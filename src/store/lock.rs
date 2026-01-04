use std::fs::{File, OpenOptions};
use std::io;
use std::path::Path;

use fs4::FileExt;

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
pub(super) struct FileLock {
    file: File,
    mode: LockMode,
}

impl FileLock {
    pub(super) fn open(path: &Path, mode: LockMode) -> io::Result<Self> {
        Self::open_internal(path, mode, LockStrategy::Blocking)
    }

    pub(super) fn try_open(path: &Path, mode: LockMode) -> io::Result<Self> {
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

    pub(super) fn mode(&self) -> LockMode {
        self.mode
    }

    pub(super) fn file(&self) -> &File {
        &self.file
    }

    pub(super) fn file_mut(&mut self) -> &mut File {
        &mut self.file
    }
}
