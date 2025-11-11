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
const RECORD_HEADER_LEN: u64 = 9; // 1 kind + 4 key len + 4 value len
const CURRENT_VERSION: u32 = 1;

/// Represents a contiguous value payload written in the backing file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValueLocation {
    /// Byte offset from the beginning of the file.
    pub offset: u64,
    /// Length of the value in bytes.
    pub length: u32,
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
    pub fn insert(&mut self, key: String, location: ValueLocation) {
        self.entries.insert(key, location);
    }

    pub fn get(&self, key: &str) -> Option<&ValueLocation> {
        self.entries.get(key)
    }

    pub fn remove(&mut self, key: &str) -> Option<ValueLocation> {
        self.entries.remove(key)
    }
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
        let mut store = Self { metadata };
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
        let location = self.append_record(RecordKind::Insert, key, Some(value))?;
        self.metadata.index.insert(key.to_string(), location);
        Ok(())
    }

    pub fn get(&mut self, key: &str) -> io::Result<Option<Vec<u8>>> {
        let location = match self.metadata.index.get(key) {
            Some(loc) => *loc,
            None => return Ok(None),
        };
        let file = self.metadata.lock.file_mut();
        file.seek(SeekFrom::Start(location.offset))?;
        let mut buf = vec![0u8; location.length as usize];
        file.read_exact(&mut buf)?;
        Ok(Some(buf))
    }

    pub fn remove(&mut self, key: &str) -> io::Result<bool> {
        self.ensure_writable()?;
        if self.metadata.index.remove(key).is_none() {
            return Ok(false);
        }
        self.append_record(RecordKind::Delete, key, None)?;
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

    fn append_record(
        &mut self,
        kind: RecordKind,
        key: &str,
        value: Option<&[u8]>,
    ) -> io::Result<ValueLocation> {
        let key_bytes = key.as_bytes();
        let value_bytes = value.unwrap_or(&[]);
        let key_len = u32::try_from(key_bytes.len()).map_err(|_| {
            io::Error::new(ErrorKind::InvalidInput, "key length exceeds u32::MAX")
        })?;
        let value_len = u32::try_from(value_bytes.len()).map_err(|_| {
            io::Error::new(ErrorKind::InvalidInput, "value length exceeds u32::MAX")
        })?;

        let file = self.metadata.lock.file_mut();
        let record_start = file.seek(SeekFrom::End(0))?;

        let mut header = [0u8; RECORD_HEADER_LEN as usize];
        header[0] = kind as u8;
        header[1..5].copy_from_slice(&key_len.to_le_bytes());
        header[5..9].copy_from_slice(&value_len.to_le_bytes());

        file.write_all(&header)?;
        file.write_all(key_bytes)?;
        if kind == RecordKind::Insert {
            file.write_all(value_bytes)?;
        }
        file.flush()?;

        let value_offset = record_start + RECORD_HEADER_LEN + u64::from(key_len);
        Ok(ValueLocation {
            offset: value_offset,
            length: value_len,
        })
    }

    fn rebuild_index(&mut self) -> io::Result<()> {
        self.metadata.index.entries.clear();
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

            let mut key_buf = vec![0u8; header.key_len as usize];
            file.read_exact(&mut key_buf)?;
            let key = String::from_utf8(key_buf).map_err(|_| {
                io::Error::new(ErrorKind::InvalidData, "stored key is not valid UTF-8")
            })?;

            let value_offset = file.stream_position()?;
            match header.kind {
                RecordKind::Insert => {
                    let location = ValueLocation {
                        offset: value_offset,
                        length: header.value_len,
                    };
                    self.metadata.index.insert(key, location);
                }
                RecordKind::Delete => {
                    self.metadata.index.remove(&key);
                }
            }

            let record_end = value_offset
                .checked_add(u64::from(header.value_len))
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
}

fn read_record_header(file: &mut File) -> io::Result<RecordHeader> {
    let mut buf = [0u8; RECORD_HEADER_LEN as usize];
    file.read_exact(&mut buf)?;
    let kind = RecordKind::try_from(buf[0])?;
    let key_len = u32::from_le_bytes(buf[1..5].try_into().unwrap());
    let value_len = u32::from_le_bytes(buf[5..9].try_into().unwrap());
    Ok(RecordHeader {
        kind,
        key_len,
        value_len,
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
        return Err(io::Error::new(ErrorKind::InvalidData, "file magic mismatch"));
    }
    let mut version_bytes = [0u8; 4];
    file.read_exact(&mut version_bytes)?;
    Ok(u32::from_le_bytes(version_bytes))
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let err = shared.put("new", b"data").expect_err("shared put should fail");
        assert_eq!(err.kind(), ErrorKind::PermissionDenied);
        assert_eq!(shared.get("pre")?.as_deref(), Some(&b"existing"[..]));
        Ok(())
    }
}
