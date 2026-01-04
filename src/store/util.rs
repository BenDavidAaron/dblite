use std::fs::File;
use std::io::{self, ErrorKind, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::ALLOCATION_GRANULARITY;

pub(super) fn align_payload(len: u32) -> io::Result<u32> {
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

pub(super) fn write_padding(file: &mut File, mut padding: u32, append: bool) -> io::Result<()> {
    use std::io::{Seek, SeekFrom};

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

pub(super) fn compaction_path(path: &Path) -> PathBuf {
    let mut scratch = path.to_path_buf();
    let file_name = path
        .file_name()
        .and_then(|n| n.to_str())
        .map(|name| format!("{name}.compact"))
        .unwrap_or_else(|| "dblite.compact".to_string());
    scratch.set_file_name(file_name);
    scratch
}

pub(super) fn system_time_to_unix_millis(time: SystemTime) -> io::Result<u64> {
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

pub(super) fn current_unix_millis() -> io::Result<u64> {
    system_time_to_unix_millis(SystemTime::now())
}

pub(super) fn ttl_to_deadline(ttl: Option<Duration>) -> io::Result<Option<u64>> {
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
