#![allow(dead_code)]

use std::{
    collections::BTreeMap,
    convert::TryFrom,
    fs::{File, OpenOptions},
    io::{self, ErrorKind, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
};

use fs4::FileExt;

const FILE_MAGIC: &[u8; 4] = b"DBL1";
const FILE_HEADER_LEN: u64 = 8; // 4 magic + 4 version
const RECORD_HEADER_LEN: u64 = 13; // kind + key len + value len + payload capacity
const CURRENT_VERSION: u32 = 2;
const ALLOCATION_GRANULARITY: u32 = 64;

/// Represents a contiguous value payload written in the backing file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValueLocation {
    /// Byte offset from the beginning of the file where the value is stored.
    pub value_offset: u64,
    /// Length of the value in bytes.
    pub value_length: u32,
    /// Byte offset of the record header.
    pub record_offset: u64,
    /// Bytes reserved (after the header) for key/value data, aligned for reuse.
    pub record_capacity: u32,
}

/// Basic key/value pair where the value is arbitrary bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyValuePair {
    pub key: String,
    pub value: Vec<u8>,
}

/// In-memory index that maps keys to where their values live on disk.
#[derive(Debug, Default)]
pub struct InMemoryIndex {
    pub entries: BTreeMap<String, ValueLocation>,
}

impl InMemoryIndex {
    pub fn insert(&mut self, key: String, location: ValueLocation) -> Option<ValueLocation> {
        self.entries.insert(key, location)
    }

    pub fn get(&self, key: &str) -> Option<&ValueLocation> {
        self.entries.get(key)
    }

    pub fn remove(&mut self, key: &str) -> Option<ValueLocation> {
        self.entries.remove(key)
    }
}

#[derive(Debug, Clone, Copy)]
struct FreeBlock {
    offset: u64,
    capacity: u32,
}

#[derive(Debug, Default)]
struct FreeList {
    blocks: BTreeMap<u32, Vec<FreeBlock>>,
}

impl FreeList {
    fn add(&mut self, location: ValueLocation) {
        if location.record_capacity == 0 {
            return;
        }
        let entry = self.blocks.entry(location.record_capacity).or_default();
        entry.push(FreeBlock {
            offset: location.record_offset,
            capacity: location.record_capacity,
        });
    }

    fn take(&mut self, required_payload: u32) -> Option<FreeBlock> {
        let key = {
            let mut iter = self.blocks.range(required_payload..);
            iter.next().map(|(size, _)| *size)?
        };
        let mut blocks = self.blocks.remove(&key)?;
        let block = blocks.pop()?;
        if !blocks.is_empty() {
            self.blocks.insert(key, blocks);
        }
        Some(block)
    }

    fn clear(&mut self) {
        self.blocks.clear();
    }
}

#[derive(Debug)]
struct AllocatedRegion {
    offset: u64,
    payload_capacity: u32,
    append: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LockMode {
    Shared,
    Exclusive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LockStrategy {
    Blocking,
    NonBlocking,
}

/// Captures the OS-level lock that guards the data file.
#[derive(Debug)]
pub struct FileLock {
    file: File,
    mode: LockMode,
}

impl FileLock {
    pub fn open(path: &Path, mode: LockMode) -> io::Result<Self> {
        Self::open_internal(path, mode, LockStrategy::Blocking)
    }

    pub fn try_open(path: &Path, mode: LockMode) -> io::Result<Self> {
        Self::open_internal(path, mode, LockStrategy::NonBlocking)
    }

    fn open_internal(path: &Path, mode: LockMode, strategy: LockStrategy) -> io::Result<Self> {
        let mut options = OpenOptions::new();
        options.read(true).write(true);
        if matches!(mode, LockMode::Exclusive) {
            options.create(true);
        }
        let file = options.open(path)?;
        match (mode, strategy) {
            (LockMode::Shared, LockStrategy::Blocking) => <File as FileExt>::lock_shared(&file)?,
            (LockMode::Shared, LockStrategy::NonBlocking) => {
                <File as FileExt>::try_lock_shared(&file)?
            }
            (LockMode::Exclusive, LockStrategy::Blocking) => {
                <File as FileExt>::lock_exclusive(&file)?
            }
            (LockMode::Exclusive, LockStrategy::NonBlocking) => {
                <File as FileExt>::try_lock_exclusive(&file)?
            }
        }
        Ok(Self { file, mode })
    }

    pub fn mode(&self) -> LockMode {
        self.mode
    }

    pub fn file(&self) -> &File {
        &self.file
    }

    pub fn file_mut(&mut self) -> &mut File {
        &mut self.file
    }
}

/// Metadata tracked for each data file managed by the store.
#[derive(Debug)]
pub struct FileMetadata {
    pub path: PathBuf,
    pub version: u32,
    pub lock: FileLock,
    pub index: InMemoryIndex,
}

impl FileMetadata {
    fn ensure_header(&mut self) -> io::Result<()> {
        self.version = ensure_header(self.lock.file_mut())?;
        Ok(())
    }
}

/// Main entry point for interacting with the on-disk key/value file.
#[derive(Debug)]
pub struct KeyValueStore {
    metadata: FileMetadata,
    free_list: FreeList,
}

impl KeyValueStore {
    pub fn open(path: impl Into<PathBuf>, mode: LockMode) -> io::Result<Self> {
        let path = path.into();
        let lock = FileLock::open(&path, mode)?;
        let mut metadata = FileMetadata {
            path,
            version: 0,
            lock,
            index: InMemoryIndex::default(),
        };
        metadata.ensure_header()?;
        let mut store = Self {
            metadata,
            free_list: FreeList::default(),
        };
        store.rebuild_index()?;
        Ok(store)
    }

    pub fn version(&self) -> u32 {
        self.metadata.version
    }

    pub fn contains_key(&self, key: &str) -> bool {
        self.metadata.index.get(key).is_some()
    }

    pub fn put(&mut self, key: &str, value: &[u8]) -> io::Result<()> {
        self.ensure_writable()?;
        if let Some(previous) = self.metadata.index.get(key).cloned() {
            self.free_list.add(previous);
        }
        let location = self.persist_record(RecordKind::Insert, key, Some(value))?;
        let _ = self.metadata.index.insert(key.to_string(), location);
        Ok(())
    }

    pub fn get(&mut self, key: &str) -> io::Result<Option<Vec<u8>>> {
        let location = match self.metadata.index.get(key) {
            Some(loc) => *loc,
            None => return Ok(None),
        };
        let file = self.metadata.lock.file_mut();
        file.seek(SeekFrom::Start(location.value_offset))?;
        let mut buf = vec![0u8; location.value_length as usize];
        file.read_exact(&mut buf)?;
        Ok(Some(buf))
    }

    pub fn remove(&mut self, key: &str) -> io::Result<bool> {
        self.ensure_writable()?;
        let removed = match self.metadata.index.remove(key) {
            Some(loc) => {
                self.free_list.add(loc);
                true
            }
            None => false,
        };
        if !removed {
            return Ok(false);
        }
        self.persist_record(RecordKind::Delete, key, None)?;
        Ok(true)
    }

    pub fn keys(&self) -> impl Iterator<Item = &String> + '_ {
        self.metadata.index.entries.keys()
    }

    fn ensure_writable(&self) -> io::Result<()> {
        if self.metadata.lock.mode() == LockMode::Shared {
            return Err(io::Error::new(
                ErrorKind::PermissionDenied,
                "cannot mutate store opened in shared mode",
            ));
        }
        Ok(())
    }

    fn persist_record(
        &mut self,
        kind: RecordKind,
        key: &str,
        value: Option<&[u8]>,
    ) -> io::Result<ValueLocation> {
        let key_bytes = key.as_bytes();
        let value_bytes = value.unwrap_or(&[]);
        if kind == RecordKind::Delete && !value_bytes.is_empty() {
            return Err(io::Error::new(
                ErrorKind::InvalidInput,
                "delete records cannot carry values",
            ));
        }
        let key_len = u32::try_from(key_bytes.len())
            .map_err(|_| io::Error::new(ErrorKind::InvalidInput, "key length exceeds u32::MAX"))?;
        let value_len = u32::try_from(value_bytes.len()).map_err(|_| {
            io::Error::new(ErrorKind::InvalidInput, "value length exceeds u32::MAX")
        })?;
        let payload_len = key_len
            .checked_add(value_len)
            .ok_or_else(|| io::Error::new(ErrorKind::InvalidInput, "record payload too large"))?;
        let aligned_len = align_payload(payload_len)?;
        let allow_reuse = matches!(kind, RecordKind::Insert);
        let region = self.allocate_region(aligned_len, allow_reuse)?;
        self.write_region(region, kind, key_bytes, value_bytes, key_len, value_len)
    }

    fn allocate_region(
        &mut self,
        requested_capacity: u32,
        allow_reuse: bool,
    ) -> io::Result<AllocatedRegion> {
        if allow_reuse {
            if let Some(block) = self.free_list.take(requested_capacity) {
                return Ok(AllocatedRegion {
                    offset: block.offset,
                    payload_capacity: block.capacity,
                    append: false,
                });
            }
        }
        let file = self.metadata.lock.file_mut();
        let offset = file.seek(SeekFrom::End(0))?;
        Ok(AllocatedRegion {
            offset,
            payload_capacity: requested_capacity,
            append: true,
        })
    }

    fn write_region(
        &mut self,
        region: AllocatedRegion,
        kind: RecordKind,
        key_bytes: &[u8],
        value_bytes: &[u8],
        key_len: u32,
        value_len: u32,
    ) -> io::Result<ValueLocation> {
        let payload_len = key_len
            .checked_add(value_len)
            .ok_or_else(|| io::Error::new(ErrorKind::InvalidInput, "record payload too large"))?;
        if region.payload_capacity < payload_len {
            return Err(io::Error::new(
                ErrorKind::InvalidData,
                "allocated region smaller than record",
            ));
        }

        let file = self.metadata.lock.file_mut();
        file.seek(SeekFrom::Start(region.offset))?;

        let mut header = [0u8; RECORD_HEADER_LEN as usize];
        header[0] = kind as u8;
        header[1..5].copy_from_slice(&key_len.to_le_bytes());
        header[5..9].copy_from_slice(&value_len.to_le_bytes());
        header[9..13].copy_from_slice(&region.payload_capacity.to_le_bytes());
        file.write_all(&header)?;
        file.write_all(key_bytes)?;
        if kind == RecordKind::Insert {
            file.write_all(value_bytes)?;
        }

        let padding = region.payload_capacity - payload_len;
        if padding > 0 {
            write_padding(file, padding, region.append)?;
        }

        file.flush()?;

        let value_offset = region
            .offset
            .checked_add(RECORD_HEADER_LEN)
            .and_then(|pos| pos.checked_add(u64::from(key_len)))
            .ok_or_else(|| io::Error::new(ErrorKind::InvalidData, "value offset overflow"))?;

        Ok(ValueLocation {
            value_offset,
            value_length: value_len,
            record_offset: region.offset,
            record_capacity: region.payload_capacity,
        })
    }

    fn rebuild_index(&mut self) -> io::Result<()> {
        self.metadata.index.entries.clear();
        self.free_list.clear();
        let file = self.metadata.lock.file_mut();
        let file_len = file.metadata()?.len();
        if file_len < FILE_HEADER_LEN {
            return Err(io::Error::new(
                ErrorKind::UnexpectedEof,
                "file shorter than header",
            ));
        }

        let mut cursor = FILE_HEADER_LEN;
        while cursor < file_len {
            file.seek(SeekFrom::Start(cursor))?;
            let header = match read_record_header(file) {
                Ok(h) => h,
                Err(err) if err.kind() == ErrorKind::UnexpectedEof => break,
                Err(err) => return Err(err),
            };

            let record_start = cursor;
            let payload_capacity = header.payload_capacity;
            let payload_len = header
                .key_len
                .checked_add(header.value_len)
                .ok_or_else(|| io::Error::new(ErrorKind::InvalidData, "payload length overflow"))?;
            if payload_capacity < payload_len {
                return Err(io::Error::new(
                    ErrorKind::InvalidData,
                    "payload capacity smaller than data",
                ));
            }

            let mut key_buf = vec![0u8; header.key_len as usize];
            file.read_exact(&mut key_buf)?;
            let key = String::from_utf8(key_buf).map_err(|_| {
                io::Error::new(ErrorKind::InvalidData, "stored key is not valid UTF-8")
            })?;

            let value_offset = file.stream_position()?;
            let value_end = value_offset
                .checked_add(u64::from(header.value_len))
                .ok_or_else(|| io::Error::new(ErrorKind::InvalidData, "value length overflow"))?;
            file.seek(SeekFrom::Start(value_end))?;
            let padding = payload_capacity - payload_len;
            if padding > 0 {
                let padding_end = value_end.checked_add(u64::from(padding)).ok_or_else(|| {
                    io::Error::new(ErrorKind::InvalidData, "padding length overflow")
                })?;
                file.seek(SeekFrom::Start(padding_end))?;
            }

            match header.kind {
                RecordKind::Insert => {
                    let location = ValueLocation {
                        value_offset,
                        value_length: header.value_len,
                        record_offset: record_start,
                        record_capacity: payload_capacity,
                    };
                    if let Some(previous) = self.metadata.index.insert(key, location) {
                        self.free_list.add(previous);
                    }
                }
                RecordKind::Delete => {
                    if let Some(previous) = self.metadata.index.remove(&key) {
                        self.free_list.add(previous);
                    }
                }
            }

            let record_end = record_start
                .checked_add(RECORD_HEADER_LEN)
                .and_then(|pos| pos.checked_add(u64::from(payload_capacity)))
                .ok_or_else(|| io::Error::new(ErrorKind::InvalidData, "record length overflow"))?;
            if record_end > file_len {
                return Err(io::Error::new(
                    ErrorKind::UnexpectedEof,
                    "record extends beyond end of file",
                ));
            }
            cursor = record_end;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RecordKind {
    Insert = 1,
    Delete = 2,
}

impl TryFrom<u8> for RecordKind {
    type Error = io::Error;

    fn try_from(value: u8) -> io::Result<Self> {
        match value {
            1 => Ok(Self::Insert),
            2 => Ok(Self::Delete),
            other => Err(io::Error::new(
                ErrorKind::InvalidData,
                format!("unknown record kind {other}"),
            )),
        }
    }
}

struct RecordHeader {
    kind: RecordKind,
    key_len: u32,
    value_len: u32,
    payload_capacity: u32,
}

fn read_record_header(file: &mut File) -> io::Result<RecordHeader> {
    let mut buf = [0u8; RECORD_HEADER_LEN as usize];
    file.read_exact(&mut buf)?;
    let kind = RecordKind::try_from(buf[0])?;
    let key_len = u32::from_le_bytes(buf[1..5].try_into().unwrap());
    let value_len = u32::from_le_bytes(buf[5..9].try_into().unwrap());
    let payload_capacity = u32::from_le_bytes(buf[9..13].try_into().unwrap());
    Ok(RecordHeader {
        kind,
        key_len,
        value_len,
        payload_capacity,
    })
}

fn ensure_header(file: &mut File) -> io::Result<u32> {
    let len = file.metadata()?.len();
    if len < FILE_HEADER_LEN {
        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(FILE_MAGIC)?;
        file.write_all(&CURRENT_VERSION.to_le_bytes())?;
        file.flush()?;
        return Ok(CURRENT_VERSION);
    }
    file.seek(SeekFrom::Start(0))?;
    let mut magic = [0u8; 4];
    file.read_exact(&mut magic)?;
    if &magic != FILE_MAGIC {
        return Err(io::Error::new(
            ErrorKind::InvalidData,
            "file magic mismatch",
        ));
    }
    let mut version_bytes = [0u8; 4];
    file.read_exact(&mut version_bytes)?;
    Ok(u32::from_le_bytes(version_bytes))
}

fn align_payload(len: u32) -> io::Result<u32> {
    if ALLOCATION_GRANULARITY == 0 || len == 0 {
        return Ok(len);
    }
    let remainder = len % ALLOCATION_GRANULARITY;
    if remainder == 0 {
        return Ok(len);
    }
    len.checked_add(ALLOCATION_GRANULARITY - remainder)
        .ok_or_else(|| io::Error::new(ErrorKind::InvalidInput, "aligned payload exceeds u32::MAX"))
}

fn write_padding(file: &mut File, mut padding: u32, append: bool) -> io::Result<()> {
    if padding == 0 {
        return Ok(());
    }
    if !append {
        let current = file.stream_position()?;
        let target = current
            .checked_add(u64::from(padding))
            .ok_or_else(|| io::Error::new(ErrorKind::InvalidData, "padding seek overflow"))?;
        file.seek(SeekFrom::Start(target))?;
        return Ok(());
    }

    const ZERO_PAD: [u8; 4096] = [0u8; 4096];
    while padding > 0 {
        let chunk = padding.min(ZERO_PAD.len() as u32) as usize;
        file.write_all(&ZERO_PAD[..chunk])?;
        padding -= chunk as u32;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::NamedTempFile;

    fn new_store(path: &Path) -> io::Result<KeyValueStore> {
        KeyValueStore::open(path, LockMode::Exclusive)
    }

    #[test]
    fn put_get_round_trip() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = new_store(file.path())?;
        store.put("alpha", b"beta")?;
        store.put("gamma", b"delta")?;

        let alpha = store.get("alpha")?.expect("missing alpha");
        assert_eq!(alpha, b"beta");
        let gamma = store.get("gamma")?.expect("missing gamma");
        assert_eq!(gamma, b"delta");
        Ok(())
    }

    #[test]
    fn persistence_and_reload() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        {
            let mut store = new_store(file.path())?;
            store.put("hello", b"world")?;
            store.put("rust", b"lang")?;
        }
        let mut reopened = new_store(file.path())?;
        assert_eq!(reopened.get("hello")?.as_deref(), Some(&b"world"[..]));
        assert_eq!(reopened.get("rust")?.as_deref(), Some(&b"lang"[..]));
        Ok(())
    }

    #[test]
    fn delete_removes_key() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = new_store(file.path())?;
        store.put("fruit", b"apple")?;
        assert!(store.remove("fruit")?);
        assert!(!store.contains_key("fruit"));
        assert!(store.get("fruit")?.is_none());
        assert!(!store.remove("fruit")?);
        Ok(())
    }

    #[test]
    fn exclusive_lock_blocks_second_exclusive() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let lock_one = FileLock::open(file.path(), LockMode::Exclusive)?;
        let err = FileLock::try_open(file.path(), LockMode::Exclusive)
            .expect_err("second exclusive lock should fail");
        assert_eq!(err.kind(), ErrorKind::WouldBlock);
        drop(lock_one);
        FileLock::open(file.path(), LockMode::Exclusive)?;
        Ok(())
    }

    #[test]
    fn shared_mode_prevents_writes() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        {
            let mut store = new_store(file.path())?;
            store.put("pre", b"existing")?;
        }
        let mut shared = KeyValueStore::open(file.path(), LockMode::Shared)?;
        let err = shared
            .put("new", b"data")
            .expect_err("shared put should fail");
        assert_eq!(err.kind(), ErrorKind::PermissionDenied);
        assert_eq!(shared.get("pre")?.as_deref(), Some(&b"existing"[..]));
        Ok(())
    }

    #[test]
    fn free_space_gets_reused() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = new_store(file.path())?;
        let big_value = vec![42u8; 256];
        store.put("alpha", &big_value)?;
        store.remove("alpha")?;
        let len_after_remove = fs::metadata(file.path())?.len();

        let smaller_value = vec![7u8; 64];
        store.put("beta", &smaller_value)?;
        let len_after_reuse = fs::metadata(file.path())?.len();

        assert_eq!(len_after_remove, len_after_reuse, "expected block reuse");
        assert_eq!(store.get("beta")?.as_deref(), Some(&smaller_value[..]));
        Ok(())
    }
}
