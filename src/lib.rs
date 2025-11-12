pub mod cli;
pub mod store;

pub use crate::cli::CommandResult;
use std::{
    fs::{self, OpenOptions},
    io,
    path::Path,
    time::Duration,
};
pub use store::{KeyValueStore, LockMode};

#[derive(Debug)]
pub struct Database {
    store: KeyValueStore,
}

impl Database {
    pub fn create(path: impl AsRef<Path>) -> io::Result<Self> {
        let path = path.as_ref();
        if path.exists() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!("database {:?} already exists", path),
            ));
        }
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        OpenOptions::new().write(true).create_new(true).open(path)?;
        let store = KeyValueStore::open(path, store::LockMode::Exclusive)?;
        Ok(Self { store })
    }

    pub fn open(path: impl AsRef<Path>) -> io::Result<Self> {
        let path = path.as_ref();
        if !path.exists() {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("database {:?} not found", path),
            ));
        }
        let store = KeyValueStore::open(path, store::LockMode::Exclusive)?;
        Ok(Self { store })
    }

    pub fn open_or_create(path: impl AsRef<Path>) -> io::Result<Self> {
        match Self::open(&path) {
            Ok(db) => Ok(db),
            Err(err) if err.kind() == io::ErrorKind::NotFound => Self::create(path),
            Err(err) => Err(err),
        }
    }

    pub fn set(&mut self, key: &str, value: &[u8]) -> io::Result<()> {
        self.store.put(key, value)
    }

    pub fn set_with_ttl(&mut self, key: &str, value: &[u8], ttl: Duration) -> io::Result<()> {
        self.store.put_with_ttl(key, value, Some(ttl))
    }

    pub fn get(&mut self, key: &str) -> io::Result<Option<Vec<u8>>> {
        self.store.get(key)
    }

    pub fn delete(&mut self, key: &str) -> io::Result<bool> {
        self.store.remove(key)
    }

    pub fn contains_key(&mut self, key: &str) -> io::Result<bool> {
        self.store.contains_key(key)
    }

    pub fn compact(&mut self) -> io::Result<()> {
        self.store.compact()
    }

    pub fn path(&self) -> &Path {
        self.store.path()
    }

    pub fn execute_command(&mut self, command: &str) -> io::Result<CommandResult> {
        crate::cli::execute_command(&mut self.store, command)
    }
}
