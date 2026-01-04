use std::fs::File;
use std::io::{self, ErrorKind, Read};

use super::RECORD_HEADER_LEN;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RecordKind {
    Insert = 1,
    Delete = 2,
}

impl RecordKind {
    pub(super) fn from_byte(value: u8) -> io::Result<Self> {
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

pub(super) struct RecordHeader {
    pub(super) kind: RecordKind,
    pub(super) key_len: u32,
    pub(super) value_len: u32,
    pub(super) payload_capacity: u32,
    pub(super) expires_at: Option<u64>,
}

pub(super) fn read_record_header(file: &mut File) -> io::Result<RecordHeader> {
    let mut buf = [0u8; RECORD_HEADER_LEN as usize];
    file.read_exact(&mut buf)?;
    let kind = RecordKind::from_byte(buf[0])?;
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

pub(super) fn encode_expiration(expires_at: Option<u64>) -> u64 {
    expires_at.unwrap_or(0)
}

pub(super) fn decode_expiration(raw: u64) -> Option<u64> {
    if raw == 0 { None } else { Some(raw) }
}
