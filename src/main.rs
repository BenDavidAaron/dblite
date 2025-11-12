use dblite::{CommandResult, Database};
use std::{
    env,
    io::{self, BufRead, Write},
    path::PathBuf,
};

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

        match db.execute_command(trimmed) {
            Ok(CommandResult::Output(output)) => {
                if !output.is_empty() {
                    println!("{}", output);
                }
            }
            Ok(CommandResult::Exit) => break,
            Err(err) => eprintln!("ERR {}", err),
        }
    }

    println!("bye");
    Ok(())
}
