mod store;

use crate::store::{KeyValueStore, LockMode};
use std::{
    env,
    io::{self, BufRead, Write},
    path::PathBuf,
    str::FromStr,
    time::Duration,
};

fn main() -> io::Result<()> {
    let db_path = database_path_from_args();
    let mut store = KeyValueStore::open(db_path, LockMode::Exclusive)?;
    println!("dblite ready. Commands: GET <key>, SET <key> <value> [ttl_secs], DEL <key>, or EXIT");
    repl(&mut store)
}

fn database_path_from_args() -> PathBuf {
    env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| panic!("usage: dblite <path-to-db>"))
}

fn repl(store: &mut KeyValueStore) -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut lines = stdin.lock().lines();

    loop {
        print!("dblite> ");
        stdout.flush()?;

        let Some(line) = lines.next() else {
            break;
        };
        let line = line?;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        match handle_command(store, trimmed) {
            Ok(ControlFlow::Continue) => {}
            Ok(ControlFlow::Break) => break,
            Err(err) => eprintln!("ERR {}", err),
        }
    }

    println!("bye");
    Ok(())
}

enum ControlFlow {
    Continue,
    Break,
}

fn handle_command(store: &mut KeyValueStore, input: &str) -> io::Result<ControlFlow> {
    let tokens: Vec<&str> = input.split_whitespace().collect();
    if tokens.is_empty() {
        return Ok(ControlFlow::Continue);
    }
    let command = tokens[0].to_ascii_uppercase();
    match command.as_str() {
        "GET" => {
            if tokens.len() != 2 {
                println!("Usage: GET <key>");
                return Ok(ControlFlow::Continue);
            }
            let key = tokens[1];
            match store.get(key)? {
                Some(value) => println!("{}", format_value(&value)),
                None => println!("(nil)"),
            }
        }
        "SET" => {
            if tokens.len() < 3 || tokens.len() > 4 {
                println!("Usage: SET <key> <value> [ttl_secs]");
                return Ok(ControlFlow::Continue);
            }
            let key = tokens[1];
            let value = tokens[2].as_bytes();
            let ttl = if tokens.len() == 4 {
                Some(parse_ttl(tokens[3])?)
            } else {
                None
            };
            store.put_with_ttl(key, value, ttl)?;
            println!("OK");
        }
        "DEL" => {
            if tokens.len() != 2 {
                println!("Usage: DEL <key>");
                return Ok(ControlFlow::Continue);
            }
            let key = tokens[1];
            if store.remove(key)? {
                println!("(deleted)");
            } else {
                println!("(not found)");
            }
        }
        "EXIT" | "QUIT" => return Ok(ControlFlow::Break),
        _ => println!("Unknown command: {}", tokens[0]),
    }
    Ok(ControlFlow::Continue)
}

fn parse_ttl(raw: &str) -> io::Result<Duration> {
    let secs =
        u64::from_str(raw).map_err(|err| io::Error::new(io::ErrorKind::InvalidInput, err))?;
    Ok(Duration::from_secs(secs))
}

fn format_value(value: &[u8]) -> String {
    match std::str::from_utf8(value) {
        Ok(text) => text.to_string(),
        Err(_) => {
            let mut hex = String::with_capacity(value.len() * 2 + 2);
            hex.push_str("0x");
            for byte in value {
                hex.push_str(&format!("{:02x}", byte));
            }
            hex
        }
    }
}

#[cfg(test)]
mod cli_tests {
    use super::*;
    use tempfile::NamedTempFile;

    #[test]
    fn cli_set_get_del_cycle() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = KeyValueStore::open(file.path(), LockMode::Exclusive)?;

        handle_command(&mut store, "SET foo bar")?;
        assert_eq!(store.get("foo")?.as_deref(), Some(&b"bar"[..]));

        handle_command(&mut store, "GET foo")?;
        handle_command(&mut store, "DEL foo")?;
        assert!(store.get("foo")?.is_none());
        Ok(())
    }

    #[test]
    fn cli_set_with_ttl_expires() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = KeyValueStore::open(file.path(), LockMode::Exclusive)?;

        handle_command(&mut store, "SET temp value 1")?;
        std::thread::sleep(Duration::from_millis(1100));
        handle_command(&mut store, "GET temp")?;
        assert!(store.get("temp")?.is_none());
        Ok(())
    }
}
