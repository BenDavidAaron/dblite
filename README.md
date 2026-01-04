# dblite

A lightweight, embeddable key-value store inspired by SQLite. Simple, fast, and built for embedding into your Rust applications or using as a standalone CLI tool.

## Features

- **Simple Key-Value Storage**: Store and retrieve arbitrary data by string keys
- **File-Based Persistence**: All data stored in a single file on disk
- **ACID Guarantees**: File-level locking ensures data integrity
- **TTL Support**: Set expiration times on keys
- **Space Reuse**: Deleted records' space is automatically reused for new data
- **Compaction**: Reclaim disk space by removing deleted/expired records
- **Embeddable Library**: Use as a Rust library in your projects
- **Interactive CLI**: REPL interface with command completion

## Installation

### From Source

```bash
git clone https://github.com/yourusername/dblite.git
cd dblite
cargo build --release
```

The binary will be available at `target/release/dblite`

### Install Globally

```bash
cargo install --path .
```

## Usage

### CLI Tool

#### Starting the REPL

```bash
dblite /path/to/database.db
```

This opens an interactive shell where you can execute commands.

#### Available Commands

**SET** - Store a key-value pair
```
dblite> SET mykey "Hello, World!"
OK

dblite> SET user:123 '{"name":"Alice","age":30}'
OK
```

**SET with TTL** - Store a key with expiration time
```
dblite> SET session:abc token123 30s
OK

dblite> SET cache:data value 5m
OK
```

TTL formats: `30s` (seconds), `5m` (minutes), `2h` (hours), `1d` (days)

**GET** - Retrieve a value
```
dblite> GET mykey
Hello, World!

dblite> GET nonexistent
(nil)
```

**DEL** - Delete a key
```
dblite> DEL mykey
1

dblite> DEL nonexistent
0
```

**COMPACT** - Reclaim disk space
```
dblite> COMPACT
OK
```

Removes deleted records and optimizes file size.

**EXIT** or **QUIT** - Close the CLI
```
dblite> EXIT
bye
```

### As a Rust Library

Add to your `Cargo.toml`:

```toml
[dependencies]
dblite = "0.1"
```

#### Basic Usage

```rust
use dblite::{Database, LockMode};
use std::time::Duration;

fn main() -> std::io::Result<()> {
    // Open or create a database
    let mut db = Database::open_or_create("~/mydb.dbl")?;
    
    // Store a value
    db.set("username", b"alice")?;
    
    // Store with TTL (expires in 60 seconds)
    db.set_with_ttl("session_token", b"abc123", Duration::from_secs(60))?;
    
    // Retrieve a value
    if let Some(value) = db.get("username")? {
        println!("Username: {}", String::from_utf8_lossy(&value));
    }
    
    // Check if key exists
    if db.contains_key("username")? {
        println!("User exists!");
    }
    
    // Delete a key
    let deleted = db.delete("username")?;
    println!("Deleted: {}", deleted);
    
    // Get all keys
    let keys = db.keys()?;
    println!("Keys: {:?}", keys);
    
    // Compact the database
    db.compact()?;
    
    Ok(())
}
```

#### Advanced: Using the Store Directly

```rust
use dblite::{KeyValueStore, LockMode};
use std::time::Duration;

fn main() -> std::io::Result<()> {
    // Open with exclusive lock
    let mut store = KeyValueStore::open("data.db", LockMode::Exclusive)?;
    
    // Store data
    store.put("key", b"value")?;
    
    // Store with TTL
    store.put_with_ttl("temp", b"data", Some(Duration::from_secs(300)))?;
    
    // Retrieve
    if let Some(data) = store.get("key")? {
        println!("Got: {:?}", data);
    }
    
    // Remove
    store.remove("key")?;
    
    Ok(())
}
```

#### Read-Only Access

```rust
use dblite::{KeyValueStore, LockMode};

fn main() -> std::io::Result<()> {
    // Open in shared mode (read-only)
    let mut store = KeyValueStore::open("data.db", LockMode::Shared)?;
    
    // Read operations work
    let value = store.get("key")?;
    
    // Write operations will fail with PermissionDenied
    // store.put("key", b"value")?; // Error!
    
    Ok(())
}
```

## File Format

dblite stores data in a single file with the following structure:

- **Header**: Magic bytes (`DBL1`) + version number
- **Records**: Sequence of key-value records with metadata
  - Record type (insert/delete)
  - Key length and data
  - Value length and data
  - Capacity (for space reuse)
  - Optional expiration timestamp

The file format is designed for:
- **Efficiency**: Records are aligned for fast access
- **Durability**: All writes are flushed to disk
- **Space Reuse**: Deleted space is tracked and reused
- **Simplicity**: Single-file storage like SQLite

## Architecture

### Key Components

- **KeyValueStore**: Low-level storage engine with file I/O and indexing
- **Database**: High-level API wrapping the store
- **InMemoryIndex**: BTreeMap-based index for fast key lookups
- **FreeSpaceManager**: Tracks and reuses deleted record space
- **FileLock**: OS-level file locking for concurrent access control

### Concurrency Model

- **Exclusive Lock**: One writer, no readers (LockMode::Exclusive)
- **Shared Lock**: Multiple readers, no writers (LockMode::Shared)
- OS-level file locking prevents data corruption
- Index is rebuilt from file on open

## Performance Characteristics

- **Reads**: O(log n) via in-memory BTreeMap index
- **Writes**: O(log n) index update + O(1) append or O(n) space reuse scan
- **Deletes**: O(log n) index update + O(1) free space tracking
- **Compaction**: O(n) full file rewrite
- **Memory**: O(n) for key index (keys + metadata only, not values)

## Limitations

- **Single-file**: All data in one file (simple but not distributed)
- **In-memory index**: Keys must fit in memory
- **No transactions**: Individual operations are atomic, but no multi-key transactions
- **No query language**: Simple get/set/delete operations only
- **File-level locking**: Not optimized for high-concurrency scenarios

## Building

### Development Build

```bash
cargo build
```

### Release Build

```bash
cargo build --release
```

### Running Tests

```bash
cargo test
```

## License

This project is licensed under the **GNU Affero General Public License v3.0 or later (AGPL-3.0-or-later)**.

See the LICENSE file for details.

## Project Status

This is a hobby project created over a holiday. It's functional and tested, but not battle-tested in production environments. Please contact me know if you would like to battle test it :3
