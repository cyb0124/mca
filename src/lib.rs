use anyhow::{anyhow, bail, ensure, Result};
use bitstream_io::{BitRead, BitReader, BitWrite, BitWriter};
use byteorder::{BigEndian, LittleEndian, ReadBytesExt, WriteBytesExt};
use nbt::{CompoundTag, CompoundTagError, Tag};
use std::{
    io::{Cursor, Read},
    ops::{Index, IndexMut},
};

pub const CHUNKS_IN_MCA: usize = 32 * 32;
pub const BLOCKS_IN_SECTION: usize = 16 * 16 * 16;
pub const BIOMES_IN_SECTION: usize = 4 * 4 * 4;

pub struct Chunk {
    pub data: Option<CompoundTag>,
    pub timestamp: u32,
}

pub struct MCA {
    pub chunks: Box<[Chunk]>,
}

impl MCA {
    pub fn parse(data: &[u8]) -> Result<MCA> {
        let mut header = Cursor::new(data);
        let mut chunks = Vec::with_capacity(CHUNKS_IN_MCA);
        for _ in 0..CHUNKS_IN_MCA {
            let offset = header.read_uint::<BigEndian>(3)? << 12;
            if header.read_u8()? == 0 {
                chunks.push(Chunk { data: None, timestamp: 0 });
                continue;
            }
            let mut cursor = Cursor::new(data);
            cursor.set_position(offset);
            let size = cursor.read_u32::<BigEndian>()? as u64;
            ensure!(size >= 1 && cursor.read_u8()? == 2);
            let chunk = nbt::decode::read_zlib_compound_tag(&mut cursor.take(size - 1))?;
            chunks.push(Chunk { data: Some(chunk), timestamp: 0 })
        }
        for chunk in &mut chunks {
            chunk.timestamp = header.read_u32::<BigEndian>()?
        }
        Ok(MCA { chunks: chunks.into_boxed_slice() })
    }

    pub fn dump(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let mut ts = Cursor::new(&mut out);
        ts.set_position((CHUNKS_IN_MCA * 4) as _);
        for chunk in &*self.chunks {
            ts.write_u32::<BigEndian>(chunk.timestamp).unwrap()
        }
        for (i, chunk) in self.chunks.iter().enumerate() {
            let Some(chunk) = &chunk.data else { continue };
            let start = out.len();
            out.resize(start + 4, 0);
            out.write_u8(2).unwrap();
            nbt::encode::write_zlib_compound_tag(&mut out, chunk).unwrap();
            let body_len = out.len() - start - 4;
            let end = out.len().next_multiple_of(1 << 12);
            out.resize(end, 0);
            let mut cursor = Cursor::new(&mut out);
            cursor.set_position(start as _);
            cursor.write_u32::<BigEndian>(body_len as _).unwrap();
            cursor.set_position((i * 4) as _);
            cursor.write_uint::<BigEndian>((start >> 12) as _, 3).unwrap();
            cursor.write_u8(((end - start) >> 12).try_into().unwrap()).unwrap()
        }
        out
    }
}

impl Index<(usize, usize)> for MCA {
    type Output = Chunk;
    fn index(&self, (x, z): (usize, usize)) -> &Chunk { &self.chunks[z * 32 + x] }
}

impl IndexMut<(usize, usize)> for MCA {
    fn index_mut(&mut self, (x, z): (usize, usize)) -> &mut Chunk { &mut self.chunks[z * 32 + x] }
}

pub struct Section {
    pub y: i8,
    pub block_palette: Vec<CompoundTag>,
    pub block_data: Box<[usize]>,
    pub biome_palette: Vec<String>,
    pub biome_data: Box<[usize]>,
    pub block_light: Box<[u8]>,
    pub sky_light: Box<[u8]>,
}

trait TagErrorExt<T> {
    fn to(self) -> Result<T>;
}

impl<T> TagErrorExt<T> for Result<T, CompoundTagError<'_>> {
    fn to(self) -> Result<T> { self.map_err(|e| anyhow!("{e}")) }
}

fn parse_light_data(tag: &CompoundTag, key: &str) -> Result<Box<[u8]>> {
    let Ok(tag) = tag.get::<&Tag>(key) else { return Ok(vec![0; BLOCKS_IN_SECTION].into_boxed_slice()) };
    let Tag::ByteArray(data) = tag else { bail!("{key} is not byte array") };
    ensure!(data.len() * 2 == BLOCKS_IN_SECTION);
    Ok(Box::from_iter(data.iter().flat_map(|&x| {
        let x = x as u8;
        [x & 7, x >> 4]
    })))
}

fn dump_light_data(tag: &mut CompoundTag, key: &str, levels: &[u8]) {
    if levels.iter().any(|&x| x != 0) {
        tag.insert_i8_vec(key, levels.chunks_exact(2).map(|x| (x[0] | (x[1] << 4)) as i8).collect())
    }
}

impl Section {
    pub fn parse(tag: &CompoundTag) -> Result<Self> {
        let y = tag.get_i8("Y").to()?;
        let bs = tag.get_compound_tag("block_states").to()?;
        let block_palette = Vec::from_iter(bs.get_compound_tag_vec("palette").to()?.into_iter().cloned());
        let bits = usize::BITS - (block_palette.len() - 1).leading_zeros();
        let mut block_data = Vec::with_capacity(BLOCKS_IN_SECTION);
        if bits == 0 {
            block_data.resize(BLOCKS_IN_SECTION, 0)
        } else {
            let bits = bits.max(4);
            for &data in bs.get_i64_vec("data").to()? {
                let bytes = data.to_le_bytes();
                let mut reader = BitReader::endian(bytes.as_slice(), bitstream_io::LittleEndian);
                while let Ok(idx) = reader.read::<u64>(bits) {
                    block_data.push(idx as _);
                    if block_data.len() == BLOCKS_IN_SECTION {
                        break;
                    }
                }
            }
            ensure!(block_data.len() == BLOCKS_IN_SECTION)
        }
        let bs = tag.get_compound_tag("biomes").to()?;
        let biome_palette = Vec::from_iter(bs.get_str_vec("palette").to()?.into_iter().map(|x| x.to_owned()));
        let bits = usize::BITS - (biome_palette.len() - 1).leading_zeros();
        let mut biome_data = Vec::with_capacity(BIOMES_IN_SECTION);
        if bits == 0 {
            biome_data.resize(BIOMES_IN_SECTION, 0)
        } else {
            let data = bs.get_i64_vec("data").to()?;
            let mut bytes = Vec::with_capacity(data.len() * 8);
            for &data in data {
                bytes.write_i64::<LittleEndian>(data).unwrap()
            }
            let mut reader = BitReader::endian(&*bytes, bitstream_io::LittleEndian);
            while biome_data.len() != BIOMES_IN_SECTION {
                biome_data.push(reader.read::<u64>(bits)? as usize)
            }
        }
        Ok(Self {
            y,
            block_palette,
            block_data: block_data.into_boxed_slice(),
            biome_palette,
            biome_data: biome_data.into_boxed_slice(),
            block_light: parse_light_data(tag, "BlockLight")?,
            sky_light: parse_light_data(tag, "SkyLight")?,
        })
    }

    pub fn dump(&self) -> CompoundTag {
        let mut out = CompoundTag::new();
        out.insert_i8("Y", self.y);
        let mut bs = CompoundTag::new();
        bs.insert_compound_tag_vec("palette", self.block_palette.iter().cloned());
        let bits = usize::BITS - (self.block_palette.len() - 1).leading_zeros();
        if bits != 0 {
            let bits = bits.max(4);
            let mut data = Vec::new();
            let mut queue = 0;
            let mut bits_in_queue = 0;
            for &idx in &*self.block_data {
                if 64 - bits_in_queue < bits {
                    data.push(queue as i64);
                    bits_in_queue = 0
                }
                queue |= (idx as u64) << bits_in_queue;
                bits_in_queue += bits
            }
            if bits_in_queue != 0 {
                data.push(queue as i64)
            }
            bs.insert_i64_vec("data", data)
        }
        out.insert_compound_tag("block_states", bs);
        bs = CompoundTag::new();
        bs.insert_str_vec("palette", self.biome_palette.iter().cloned());
        let bits = usize::BITS - (self.biome_palette.len() - 1).leading_zeros();
        if bits != 0 {
            let mut bytes = Vec::new();
            let mut writer = BitWriter::endian(&mut bytes, bitstream_io::LittleEndian);
            for &idx in &*self.biome_data {
                writer.write(bits, idx as u64).unwrap()
            }
            writer.byte_align().unwrap();
            bytes.resize(bytes.len().next_multiple_of(8), 0);
            let mut bytes = bytes.as_slice();
            let data = Vec::from_iter(std::iter::from_fn(|| bytes.read_i64::<LittleEndian>().ok()));
            bs.insert_i64_vec("data", data)
        }
        out.insert_compound_tag("biomes", bs);
        dump_light_data(&mut out, "BlockLight", &self.block_light);
        dump_light_data(&mut out, "SkyLight", &self.sky_light);
        out
    }
}
