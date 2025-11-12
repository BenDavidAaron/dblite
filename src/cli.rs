use crate::store::KeyValueStore;
use std::{io, str::FromStr, time::Duration};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommandResult {
    Output(String),
    Exit,
}

pub fn execute_command(store: &mut KeyValueStore, input: &str) -> io::Result<CommandResult> {
    let tokens = tokenize(input)?;
    if tokens.is_empty() {
        return Ok(CommandResult::Output(String::new()));
    }
    let command = tokens[0].to_ascii_uppercase();
    let response = match command.as_str() {
        "GET" => {
            if tokens.len() != 2 {
                return Ok(CommandResult::Output("Usage: GET <key>".into()));
            }
            let key = &tokens[1];
            match store.get(key)? {
                Some(value) => format_value(&value),
                None => "(nil)".into(),
            }
        }
        "SET" => {
            if tokens.len() < 3 || tokens.len() > 4 {
                return Ok(CommandResult::Output(
                    "Usage: SET <key> <value> [ttl_secs]".into(),
                ));
            }
            let key = &tokens[1];
            let value = tokens[2].as_bytes();
            if tokens.len() == 4 {
                let ttl = parse_ttl(&tokens[3])?;
                store.put_with_ttl(key, value, Some(ttl))?;
            } else {
                store.put(key, value)?;
            }
            "OK".into()
        }
        "DEL" => {
            if tokens.len() != 2 {
                return Ok(CommandResult::Output("Usage: DEL <key>".into()));
            }
            let key = &tokens[1];
            if store.remove(key)? {
                "(deleted)".into()
            } else {
                "(not found)".into()
            }
        }
        "COMPACT" => {
            store.compact()?;
            "OK (compacted)".into()
        }
        "EXIT" | "QUIT" => return Ok(CommandResult::Exit),
        _ => format!("Unknown command: {}", tokens[0]),
    };
    Ok(CommandResult::Output(response))
}

pub fn tokenize(input: &str) -> io::Result<Vec<String>> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut in_quotes: Option<char> = None;
    let mut escape = false;

    for ch in input.chars() {
        if escape {
            current.push(decode_escape(ch)?);
            escape = false;
            continue;
        }

        if ch == '\\' {
            escape = true;
            continue;
        }

        if let Some(quote) = in_quotes {
            if ch == quote {
                in_quotes = None;
            } else {
                current.push(ch);
            }
            continue;
        }

        match ch {
            '"' | '\'' => in_quotes = Some(ch),
            c if c.is_whitespace() => {
                if !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
            }
            _ => current.push(ch),
        }
    }

    if in_quotes.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "unterminated quote in command",
        ));
    }
    if escape {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "dangling escape in command",
        ));
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    Ok(tokens)
}

fn parse_ttl(raw: &str) -> io::Result<Duration> {
    let secs =
        u64::from_str(raw).map_err(|err| io::Error::new(io::ErrorKind::InvalidInput, err))?;
    Ok(Duration::from_secs(secs))
}

fn decode_escape(ch: char) -> io::Result<char> {
    Ok(match ch {
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        '0' => '\0',
        '\\' => '\\',
        '"' => '"',
        '\'' => '\'',
        other => other,
    })
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
mod tests {
    use super::*;
    use crate::store::{KeyValueStore, LockMode};
    use std::{path::Path, thread};
    use tempfile::NamedTempFile;

    fn new_store(path: &Path) -> io::Result<KeyValueStore> {
        KeyValueStore::open(path, LockMode::Exclusive)
    }

    #[test]
    fn cli_set_get_del_cycle() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = new_store(file.path())?;

        assert_eq!(output(&mut store, "SET foo bar")?, "OK");
        assert_eq!(output(&mut store, "GET foo")?, "bar");
        assert_eq!(output(&mut store, "DEL foo")?, "(deleted)");
        assert_eq!(output(&mut store, "GET foo")?, "(nil)");
        Ok(())
    }

    #[test]
    fn cli_set_with_ttl_expires() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = new_store(file.path())?;

        assert_eq!(output(&mut store, "SET temp value 1")?, "OK");
        thread::sleep(Duration::from_millis(1100));
        assert_eq!(output(&mut store, "GET temp")?, "(nil)");
        Ok(())
    }

    #[test]
    fn cli_set_with_quoted_value() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = new_store(file.path())?;

        assert_eq!(output(&mut store, "SET greeting \"hello world\"")?, "OK");
        assert_eq!(output(&mut store, "GET greeting")?, "hello world");

        assert_eq!(output(&mut store, "SET quote \"say \"hi\"\" 1")?, "OK");
        thread::sleep(Duration::from_millis(1100));
        assert_eq!(output(&mut store, "GET quote")?, "(nil)");
        Ok(())
    }

    #[test]
    fn cli_supports_single_quotes_and_escapes() -> io::Result<()> {
        let file = NamedTempFile::new()?;
        let mut store = new_store(file.path())?;

        assert_eq!(
            output(&mut store, "SET ' spaced key ' 'line 1\\nline 2'")?,
            "OK"
        );
        assert_eq!(output(&mut store, "GET ' spaced key '")?, "line 1\nline 2");

        let tokens = tokenize("GET cool\\ key")?;
        assert_eq!(tokens, vec!["GET".to_string(), "cool key".to_string()]);
        Ok(())
    }

    fn output(store: &mut KeyValueStore, cmd: &str) -> io::Result<String> {
        match execute_command(store, cmd)? {
            CommandResult::Output(msg) => Ok(msg),
            CommandResult::Exit => Ok("EXIT".into()),
        }
    }
}
