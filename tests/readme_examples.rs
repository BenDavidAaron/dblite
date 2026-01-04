use dblite::{Database, KeyValueStore, LockMode};
use std::time::Duration;
use tempfile::NamedTempFile;

#[test]
fn readme_basic_usage() -> std::io::Result<()> {
    let temp_file = NamedTempFile::new()?;

    // Open or create a database
    let mut db = Database::open_or_create(temp_file.path())?;

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
    assert_eq!(deleted, true);

    // Get all keys
    let keys = db.keys()?;
    println!("Keys: {:?}", keys);

    // Compact the database
    db.compact()?;

    Ok(())
}

#[test]
fn readme_advanced_store_direct() -> std::io::Result<()> {
    let temp_file = NamedTempFile::new()?;

    // Open with exclusive lock
    let mut store = KeyValueStore::open(temp_file.path(), LockMode::Exclusive)?;

    // Store data
    store.put("key", b"value")?;

    // Store with TTL
    store.put_with_ttl("temp", b"data", Some(Duration::from_secs(300)))?;

    // Retrieve
    if let Some(data) = store.get("key")? {
        println!("Got: {:?}", data);
        assert_eq!(data, b"value");
    }

    // Remove
    store.remove("key")?;

    Ok(())
}

#[test]
fn readme_read_only_access() -> std::io::Result<()> {
    let temp_file = NamedTempFile::new()?;

    // First, create some data with exclusive lock
    {
        let mut store = KeyValueStore::open(temp_file.path(), LockMode::Exclusive)?;
        store.put("key", b"value")?;
    }

    // Open in shared mode (read-only)
    let mut store = KeyValueStore::open(temp_file.path(), LockMode::Shared)?;

    // Read operations work
    let value = store.get("key")?;
    assert_eq!(value, Some(b"value".to_vec()));

    // Write operations will fail with PermissionDenied
    let result = store.put("key", b"value");
    assert!(result.is_err());
    assert_eq!(
        result.unwrap_err().kind(),
        std::io::ErrorKind::PermissionDenied
    );

    Ok(())
}
