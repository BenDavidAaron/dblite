use std::collections::BTreeMap;

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
    pub(super) fn is_expired(&self, now: u64) -> bool {
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
pub(super) struct InMemoryIndex {
    pub(super) entries: BTreeMap<String, ValueLocation>,
}

impl InMemoryIndex {
    pub(super) fn insert(&mut self, key: String, location: ValueLocation) -> Option<ValueLocation> {
        self.entries.insert(key, location)
    }

    pub(super) fn get(&self, key: &str) -> Option<&ValueLocation> {
        self.entries.get(key)
    }

    pub(super) fn remove(&mut self, key: &str) -> Option<ValueLocation> {
        self.entries.remove(key)
    }
}
