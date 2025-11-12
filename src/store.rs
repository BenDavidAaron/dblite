#![allow(dead_code)]

use std::{
    collections::BTreeMap,
    convert::TryFrom,
    fs::{self, File, OpenOptions},
    io::{self, ErrorKind, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use fs4::FileExt;

const FILE_MAGIC: &[u8; 4] = b"DBL1";
const FILE_HEADER_LEN: u64 = 8; // 4 magic + 4 version
const RECORD_HEADER_LEN: u64 = 21; // kind + key len + value len + payload capacity + expiration
const CURRENT_VERSION: u32 = 3;
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
    /// Optional UNIX timestamp in milliseconds when the key should expire.
    pub expires_at: Option<u64>,
}

impl ValueLocation {
    fn is_expired(&self, now: u64) -> bool {
        matches!(self.expires_at, Some(exp) if exp <= now)
    }
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

    pub fn path(&self) -> &Path {
        &self.metadata.path
    }

    pub fn contains_key(&mut self, key: &str) -> io::Result<bool> {
        if self.evict_if_expired(key)? {
            return Ok(false);
        }
        Ok(self.metadata.index.get(key).is_some())
    }

    pub fn put(&mut self, key: &str, value: &[u8]) -> io::Result<()> {
        self.put_with_deadline(key, value, None)
    }

    pub fn put_with_ttl(
        &mut self,
        key: &str,
        value: &[u8],
        ttl: Option<Duration>,
    ) -> io::Result<()> {
        let expires_at = ttl_to_deadline(ttl)?;
        self.put_with_deadline(key, value, expires_at)
    }

    pub fn get(&mut self, key: &str) -> io::Result<Option<Vec<u8>>> {
        if self.evict_if_expired(key)? {
            return Ok(None);
        }
        let location = match self.metadata.index.get(key) {
            Some(loc) => *loc,
            None => return Ok(None),
        };
        self.read_value_at(location).map(Some)
    }

    pub fn remove(&mut self, key: &str) -> io::Result<bool> {
        self.ensure_writable()?;
        if self.evict_if_expired(key)? {
            return Ok(false);
        }
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
        self.persist_record(RecordKind::Delete, key, None, None)?;
        Ok(true)
    }

    pub fn keys(&mut self) -> io::Result<Vec<String>> {
        self.evict_all_expired()?;
        Ok(self.metadata.index.entries.keys().cloned().collect())
    }

    pub fn compact(&mut self) -> io::Result<()> {
        self.ensure_writable()?;
        self.evict_all_expired()?;
        let entries: Vec<(String, ValueLocation)> = self
            .metadata
            .index
            .entries
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect();

        let temp_path = compaction_path(&self.metadata.path);
        if temp_path.exists() {
            fs::remove_file(&temp_path)?;
        }

        {
            let mut compacted = KeyValueStore::open(&temp_path, LockMode::Exclusive)?;
            for (key, location) in &entries {
                let value = self.read_value_at(*location)?;
                compacted.put_with_deadline(key, &value, location.expires_at)?;
            }
        }

        {
            let mut source = File::open(&temp_path)?;
            let dest = self.metadata.lock.file_mut();
            dest.set_len(0)?;
            dest.seek(SeekFrom::Start(0))?;
            io::copy(&mut source, dest)?;
            dest.flush()?;
        }

        fs::remove_file(&temp_path)?;
        self.rebuild_index()
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

    fn evict_if_expired(&mut self, key: &str) -> io::Result<bool> {
        let expires_at = match self.metadata.index.get(key) {
            Some(loc) => match loc.expires_at {
                Some(ts) => ts,
                None => return Ok(false),
            },
            None => return Ok(false),
        };
        let now = current_unix_millis()?;
        if now < expires_at {
            return Ok(false);
        }
        if let Some(loc) = self.metadata.index.remove(key) {
            self.free_list.add(loc);
        }
        Ok(true)
    }

    fn evict_all_expired(&mut self) -> io::Result<()> {
        if self.metadata.index.entries.is_empty() {
            return Ok(());
        }
        let now = current_unix_millis()?;
        let expired_keys: Vec<String> = self
            .metadata
            .index
            .entries
            .iter()
            .filter(|(_, loc)| loc.is_expired(now))
            .map(|(key, _)| key.clone())
            .collect();
        for key in expired_keys {
            if let Some(loc) = self.metadata.index.remove(&key) {
                self.free_list.add(loc);
            }
        }
        Ok(())
    }

    fn persist_record(
        &mut self,
        kind: RecordKind,
        key: &str,
        value: Option<&[u8]>,
        expires_at: Option<u64>,
    ) -> io::Result<ValueLocation> {
        let key_bytes = key.as_bytes();
        let value_bytes = value.unwrap_or(&[]);
        if kind == RecordKind::Delete && !value_bytes.is_empty() {
            return Err(io::Error::new(
                ErrorKind::InvalidInput,
                "delete records cannot carry values",
            ));
        }
        if matches!(kind, RecordKind::Delete) && expires_at.is_some() {
            return Err(io::Error::new(
                ErrorKind::InvalidInput,
                "delete records cannot specify expirations",
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
        self.write_region(region, kind, key_bytes, value_bytes, expires_at)
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
        expires_at: Option<u64>,
    ) -> io::Result<ValueLocation> {
        let key_len = u32::try_from(key_bytes.len())
            .map_err(|_| io::Error::new(ErrorKind::InvalidInput, "key length exceeds u32::MAX"))?;
        let value_len = u32::try_from(value_bytes.len()).map_err(|_| {
            io::Error::new(ErrorKind::InvalidInput, "value length exceeds u32::MAX")
        })?;
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
        header[13..21].copy_from_slice(&encode_expiration(expires_at).to_le_bytes());
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
            expires_at,
        })
    }

    fn read_value_at(&mut self, location: ValueLocation) -> io::Result<Vec<u8>> {
        let file = self.metadata.lock.file_mut();
        file.seek(SeekFrom::Start(location.value_offset))?;
        let mut buf = vec![0u8; location.value_length as usize];
        file.read_exact(&mut buf)?;
        Ok(buf)
    }

    fn put_with_deadline(
        &mut self,
        key: &str,
        value: &[u8],
        expires_at: Option<u64>,
    ) -> io::Result<()> {
        self.ensure_writable()?;
        if let Some(previous) = self.metadata.index.get(key).cloned() {
            self.free_list.add(previous);
        }
        let location = self.persist_record(RecordKind::Insert, key, Some(value), expires_at)?;
        let _ = self.metadata.index.insert(key.to_string(), location);
        Ok(())
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
        let now_snapshot = current_unix_millis()?;

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
                        expires_at: header.expires_at,
                    };
                    if location.is_expired(now_snapshot) {
                        self.free_list.add(location);
                    } else if let Some(previous) = self.metadata.index.insert(key, location) {
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
    expires_at: Option<u64>,
}

fn read_record_header(file: &mut File) -> io::Result<RecordHeader> {
    let mut buf = [0u8; RECORD_HEADER_LEN as usize];
    file.read_exact(&mut buf)?;
    let kind = RecordKind::try_from(buf[0])?;
    let key_len = u32::from_le_bytes(buf[1..5].try_into().unwrap());
    let value_len = u32::from_le_bytes(buf[5..9].try_into().unwrap());
    let payload_capacity = u32::from_le_bytes(buf[9..13].try_into().unwrap());
    let expires_raw = u64::from_le_bytes(buf[13..21].try_into().unwrap());
    Ok(RecordHeader {
        kind,
        key_len,
        value_len,
        payload_capacity,
        expires_at: decode_expiration(expires_raw),
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
    let version = u32::from_le_bytes(version_bytes);
    if version != CURRENT_VERSION {
        return Err(io::Error::new(
            ErrorKind::InvalidData,
            format!("unsupported file version {version}; expected {CURRENT_VERSION}",),
        ));
    }
    Ok(version)
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

fn encode_expiration(expires_at: Option<u64>) -> u64 {
    expires_at.unwrap_or(0)
}

fn decode_expiration(raw: u64) -> Option<u64> {
    if raw == 0 { None } else { Some(raw) }
}

fn compaction_path(path: &Path) -> PathBuf {
    let mut scratch = path.to_path_buf();
    let file_name = path
        .file_name()
        .and_then(|n| n.to_str())
        .map(|name| format!("{name}.compact"))
        .unwrap_or_else(|| "dblite.compact".to_string());
    scratch.set_file_name(file_name);
    scratch
}

fn system_time_to_unix_millis(time: SystemTime) -> io::Result<u64> {
    let duration = time
        .duration_since(UNIX_EPOCH)
        .map_err(|err| io::Error::new(ErrorKind::InvalidInput, err))?;
    u64::try_from(duration.as_millis()).map_err(|_| {
        io::Error::new(
            ErrorKind::InvalidInput,
            "timestamp exceeds u64::MAX milliseconds",
        )
    })
}

fn current_unix_millis() -> io::Result<u64> {
    system_time_to_unix_millis(SystemTime::now())
}

fn ttl_to_deadline(ttl: Option<Duration>) -> io::Result<Option<u64>> {
    match ttl {
        Some(duration) => {
            let expires_at = SystemTime::now()
                .checked_add(duration)
                .ok_or_else(|| io::Error::new(ErrorKind::InvalidInput, "ttl overflow"))?;
            Ok(Some(system_time_to_unix_millis(expires_at)?))
        }
        None => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        sync::{Arc, Barrier, mpsc},
        thread,
        time::{Duration, Instant},
    };
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
        assert!(!store.contains_key("fruit")?);
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

    #[test]
    fn ttl_expiration_removes_key() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = new_store(file.path())?;
        store.put_with_ttl("temp", b"data", Some(Duration::from_millis(50)))?;
        thread::sleep(Duration::from_millis(70));
        assert!(store.get("temp")?.is_none());
        assert!(!store.contains_key("temp")?);
        Ok(())
    }

    #[test]
    fn ttl_expiration_persists_across_restart() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        {
            let mut store = new_store(file.path())?;
            store.put_with_ttl("session", b"token", Some(Duration::from_millis(50)))?;
        }
        thread::sleep(Duration::from_millis(70));
        let mut reopened = new_store(file.path())?;
        assert!(reopened.get("session")?.is_none());
        assert!(!reopened.contains_key("session")?);
        Ok(())
    }

    #[test]
    fn manual_compaction_rewrites_file() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = new_store(file.path())?;
        store.put("keep", b"alive")?;
        store.put("drop", b"dead")?;
        let before = fs::metadata(file.path())?.len();
        store.remove("drop")?;
        store.compact()?;
        let after = fs::metadata(file.path())?.len();
        assert!(after <= before, "compaction should not grow file");
        assert_eq!(store.get("keep")?.as_deref(), Some(&b"alive"[..]));
        Ok(())
    }

    #[test]
    fn concurrent_writers_respect_os_lock() -> io::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("db.dblite");
        let primary = KeyValueStore::open(&path, LockMode::Exclusive)?;

        let barrier = Arc::new(Barrier::new(2));
        let (tx, rx) = mpsc::channel();
        let path_clone = path.clone();
        let barrier_clone = barrier.clone();

        let handle = thread::spawn(move || -> io::Result<()> {
            barrier_clone.wait();
            let start = Instant::now();
            let _secondary = KeyValueStore::open(&path_clone, LockMode::Exclusive)?;
            tx.send(start.elapsed()).expect("channel send failed");
            Ok(())
        });

        barrier.wait();
        thread::sleep(Duration::from_millis(150));
        drop(primary);

        let delay = rx
            .recv_timeout(Duration::from_secs(1))
            .expect("secondary did not report lock timing");
        assert!(
            delay >= Duration::from_millis(100),
            "secondary writer acquired lock too early: {:?}",
            delay
        );

        handle.join().expect("secondary panicked")?;
        Ok(())
    }
}
