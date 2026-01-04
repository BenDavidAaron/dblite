//! # dblite
//!
//! A lightweight, embeddable key-value store inspired by SQLite.
//!
//! ## Quick Start
//!
//! ```
//! use dblite::Database;
//! use std::time::Duration;
//!
//! # fn main() -> std::io::Result<()> {
//! # let temp = tempfile::NamedTempFile::new()?;
//! // Open or create a database
//! let mut db = Database::open_or_create(temp.path())?;
//!
//! // Store a value
//! db.set("username", b"alice")?;
//!
//! // Retrieve it
//! let value = db.get("username")?;
//! assert_eq!(value, Some(b"alice".to_vec()));
//!
//! // Store with TTL (expires in 60 seconds)
//! db.set_with_ttl("session", b"token123", Duration::from_secs(60))?;
//!
//! // Delete a key
//! db.delete("username")?;
//! # Ok(())
//! # }
//! ```

#[cfg(feature = "cli")]
pub mod cli;
pub mod store;

#[cfg(feature = "cli")]
pub use crate::cli::CommandResult;
use std::{
    fs::{self, OpenOptions},
    io,
    path::Path,
    time::Duration,
};
pub use store::{KeyValueStore, LockMode};

/// A high-level database interface for key-value storage.
///
/// # Examples
///
/// ```
/// use dblite::Database;
///
/// # fn main() -> std::io::Result<()> {
/// # let temp = tempfile::NamedTempFile::new()?;
/// let mut db = Database::open_or_create(temp.path())?;
/// db.set("key", b"value")?;
/// assert_eq!(db.get("key")?, Some(b"value".to_vec()));
/// # Ok(())
/// # }
/// ```
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

    /// Opens an existing database or creates it if it doesn't exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use dblite::Database;
    ///
    /// # fn main() -> std::io::Result<()> {
    /// # let temp = tempfile::NamedTempFile::new()?;
    /// let mut db = Database::open_or_create(temp.path())?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn open_or_create(path: impl AsRef<Path>) -> io::Result<Self> {
        match Self::open(&path) {
            Ok(db) => Ok(db),
            Err(err) if err.kind() == io::ErrorKind::NotFound => Self::create(path),
            Err(err) => Err(err),
        }
    }

    /// Stores a key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use dblite::Database;
    ///
    /// # fn main() -> std::io::Result<()> {
    /// # let temp = tempfile::NamedTempFile::new()?;
    /// # let mut db = Database::open_or_create(temp.path())?;
    /// db.set("user:123", b"Alice")?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn set(&mut self, key: &str, value: &[u8]) -> io::Result<()> {
        self.store.put(key, value)
    }

    /// Stores a key-value pair with a time-to-live (TTL).
    ///
    /// # Examples
    ///
    /// ```
    /// use dblite::Database;
    /// use std::time::Duration;
    ///
    /// # fn main() -> std::io::Result<()> {
    /// # let temp = tempfile::NamedTempFile::new()?;
    /// # let mut db = Database::open_or_create(temp.path())?;
    /// // Expires in 60 seconds
    /// db.set_with_ttl("session:abc", b"token", Duration::from_secs(60))?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn set_with_ttl(&mut self, key: &str, value: &[u8], ttl: Duration) -> io::Result<()> {
        self.store.put_with_ttl(key, value, Some(ttl))
    }

    /// Retrieves a value by key.
    ///
    /// Returns `None` if the key doesn't exist or has expired.
    ///
    /// # Examples
    ///
    /// ```
    /// use dblite::Database;
    ///
    /// # fn main() -> std::io::Result<()> {
    /// # let temp = tempfile::NamedTempFile::new()?;
    /// # let mut db = Database::open_or_create(temp.path())?;
    /// db.set("greeting", b"Hello, World!")?;
    /// let value = db.get("greeting")?;
    /// assert_eq!(value, Some(b"Hello, World!".to_vec()));
    /// # Ok(())
    /// # }
    /// ```
    pub fn get(&mut self, key: &str) -> io::Result<Option<Vec<u8>>> {
        self.store.get(key)
    }

    /// Deletes a key-value pair.
    ///
    /// Returns `true` if the key was deleted, `false` if it didn't exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use dblite::Database;
    ///
    /// # fn main() -> std::io::Result<()> {
    /// # let temp = tempfile::NamedTempFile::new()?;
    /// # let mut db = Database::open_or_create(temp.path())?;
    /// db.set("temp", b"data")?;
    /// assert!(db.delete("temp")?);
    /// assert!(!db.delete("temp")?); // Already deleted
    /// # Ok(())
    /// # }
    /// ```
    pub fn delete(&mut self, key: &str) -> io::Result<bool> {
        self.store.remove(key)
    }

    /// Checks if a key exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use dblite::Database;
    ///
    /// # fn main() -> std::io::Result<()> {
    /// # let temp = tempfile::NamedTempFile::new()?;
    /// # let mut db = Database::open_or_create(temp.path())?;
    /// db.set("key", b"value")?;
    /// assert!(db.contains_key("key")?);
    /// assert!(!db.contains_key("missing")?);
    /// # Ok(())
    /// # }
    /// ```
    pub fn contains_key(&mut self, key: &str) -> io::Result<bool> {
        self.store.contains_key(key)
    }

    /// Compacts the database by removing deleted records and reclaiming disk space.
    ///
    /// # Examples
    ///
    /// ```
    /// use dblite::Database;
    ///
    /// # fn main() -> std::io::Result<()> {
    /// # let temp = tempfile::NamedTempFile::new()?;
    /// # let mut db = Database::open_or_create(temp.path())?;
    /// db.set("key1", b"value1")?;
    /// db.set("key2", b"value2")?;
    /// db.delete("key1")?;
    /// db.compact()?; // Reclaim space from deleted key1
    /// # Ok(())
    /// # }
    /// ```
    pub fn compact(&mut self) -> io::Result<()> {
        self.store.compact()
    }

    pub fn path(&self) -> &Path {
        self.store.path()
    }

    #[cfg(feature = "cli")]
    pub fn execute_command(&mut self, command: &str) -> io::Result<CommandResult> {
        crate::cli::execute_command(&mut self.store, command)
    }

    pub fn keys(&mut self) -> io::Result<Vec<String>> {
        self.store.keys()
    }
}
