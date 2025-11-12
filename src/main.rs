use dblite::{CommandResult, Database};
use rustyline::{
    Context, Editor, Helper, Result as RustylineResult,
    completion::{Completer, Pair},
    error::ReadlineError,
    highlight::Highlighter,
    hint::Hinter,
    history::DefaultHistory,
    validate::Validator,
};
use std::{env, io, path::PathBuf};

fn main() -> io::Result<()> {
    let db_path = database_path_from_args();
    let mut db = Database::open_or_create(&db_path)?;
    println!(
        "dblite ready at {:?}. Commands: GET <key>, SET <key> <value> [ttl_secs], DEL <key>, COMPACT, EXIT",
        db.path()
    );
    repl(&mut db)
}

fn database_path_from_args() -> PathBuf {
    env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| panic!("usage: dblite <path-to-db>"))
}

fn repl(db: &mut Database) -> io::Result<()> {
    let mut editor = Editor::<ReplHelper, DefaultHistory>::new().map_err(readline_to_io)?;
    let initial_keys = db.keys().unwrap_or_default();
    editor.set_helper(Some(ReplHelper::new(initial_keys)));

    loop {
        match editor.readline("dblite> ") {
            Ok(line) => {
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    continue;
                }
                let _ = editor.add_history_entry(trimmed);
                match db.execute_command(trimmed) {
                    Ok(CommandResult::Output(output)) => {
                        if !output.is_empty() {
                            println!("{}", output);
                        }
                    }
                    Ok(CommandResult::Exit) => break,
                    Err(err) => eprintln!("ERR {}", err),
                }
                refresh_key_cache(&mut editor, db)?;
            }
            Err(ReadlineError::Interrupted) => continue,
            Err(ReadlineError::Eof) => break,
            Err(err) => return Err(readline_to_io(err)),
        }
    }

    println!("bye");
    Ok(())
}

fn refresh_key_cache(
    editor: &mut Editor<ReplHelper, DefaultHistory>,
    db: &mut Database,
) -> io::Result<()> {
    if let Some(helper) = editor.helper_mut() {
        helper.update_keys(db.keys()?);
    }
    Ok(())
}

fn readline_to_io(err: ReadlineError) -> io::Error {
    io::Error::new(io::ErrorKind::Other, err)
}

struct ReplHelper {
    keys: Vec<String>,
}

impl ReplHelper {
    fn new(keys: Vec<String>) -> Self {
        Self { keys }
    }

    fn update_keys(&mut self, keys: Vec<String>) {
        self.keys = keys;
    }
}

const COMMANDS: &[&str] = &["GET", "SET", "DEL", "COMPACT", "EXIT", "QUIT"];

impl Helper for ReplHelper {}

impl Completer for ReplHelper {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &Context<'_>,
    ) -> RustylineResult<(usize, Vec<Pair>)> {
        let (start, token_index) = current_token_info(line, pos);
        let prefix = &line[start..pos];
        let mut pairs = Vec::new();

        if token_index == 0 {
            let upper = prefix.to_ascii_uppercase();
            for &cmd in COMMANDS {
                if cmd.starts_with(&upper) {
                    pairs.push(Pair {
                        display: cmd.to_string(),
                        replacement: cmd.to_string(),
                    });
                }
            }
        } else if token_index == 1 {
            if let Some(first) = first_token(line) {
                let verb = first.to_ascii_uppercase();
                if matches!(verb.as_str(), "GET" | "SET" | "DEL") {
                    for key in &self.keys {
                        if key.starts_with(prefix) {
                            pairs.push(Pair {
                                display: key.clone(),
                                replacement: key.clone(),
                            });
                        }
                    }
                }
            }
        }

        Ok((start, pairs))
    }
}

impl Hinter for ReplHelper {
    type Hint = String;

    fn hint(&self, _line: &str, _pos: usize, _ctx: &Context<'_>) -> Option<String> {
        None
    }
}

impl Highlighter for ReplHelper {}

impl Validator for ReplHelper {}

fn first_token(line: &str) -> Option<&str> {
    line.split_whitespace().next()
}

fn current_token_info(line: &str, pos: usize) -> (usize, usize) {
    if pos > line.len() {
        return (line.len(), line.split_whitespace().count());
    }
    let before = &line[..pos];
    let mut start = 0;
    for (idx, ch) in before.char_indices().rev() {
        if ch.is_whitespace() {
            start = idx + ch.len_utf8();
            break;
        }
    }
    let token_index = if start == 0 {
        0
    } else {
        before[..start].split_whitespace().count()
    };
    (start, token_index)
}
