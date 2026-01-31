use dblite::Database;
use rand::Rng;
use std::collections::HashSet;
use std::io::Write as _;
use std::time::{Duration, Instant};
use tempfile::NamedTempFile;

fn random_key(rng: &mut impl Rng) -> String {
    let len = rng.gen_range(1..=64);
    (0..len)
        .map(|_| {
            let idx = rng.gen_range(0..36);
            if idx < 10 {
                (b'0' + idx) as char
            } else {
                (b'a' + idx - 10) as char
            }
        })
        .collect()
}

fn random_value(rng: &mut impl Rng) -> Vec<u8> {
    let len = rng.gen_range(1..=1_000_000);
    let mut buf = vec![0u8; len];
    rng.fill(&mut buf[..]);
    buf
}

fn pick_random_key(keys: &HashSet<String>, rng: &mut impl Rng) -> String {
    let idx = rng.gen_range(0..keys.len());
    keys.iter().nth(idx).unwrap().clone()
}

fn human_bytes(b: u64) -> String {
    const KB: u64 = 1024;
    const MB: u64 = 1024 * KB;
    const GB: u64 = 1024 * MB;
    if b >= GB {
        format!("{:.1} GB", b as f64 / GB as f64)
    } else if b >= MB {
        format!("{:.1} MB", b as f64 / MB as f64)
    } else if b >= KB {
        format!("{:.1} KB", b as f64 / KB as f64)
    } else {
        format!("{b} B")
    }
}

#[derive(Clone, Copy)]
enum Op {
    Write,
    Read,
    Delete,
    Compact,
}

#[test]
fn stress() -> std::io::Result<()> {
    let total_ops: u64 = std::env::var("STRESS_OPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(500);

    let temp_file = NamedTempFile::new()?;
    let mut db = Database::open_or_create(temp_file.path())?;
    let mut rng = rand::thread_rng();
    let mut known_keys: HashSet<String> = HashSet::new();

    let mut writes = 0u64;
    let mut reads = 0u64;
    let mut deletes = 0u64;
    let mut compacts = 0u64;
    let mut bytes_written = 0u64;
    let mut bytes_read = 0u64;

    let mut write_time = Duration::ZERO;
    let mut read_time = Duration::ZERO;
    let mut delete_time = Duration::ZERO;
    let mut compact_time = Duration::ZERO;

    let report_path = std::env::var("STRESS_REPORT")
        .unwrap_or_else(|_| "stress_report.csv".to_string());
    let mut csv = std::fs::File::create(&report_path)?;
    writeln!(csv, "ops,writes,reads,deletes,compacts,keys,bytes_written,bytes_read,write_time_us,read_time_us,delete_time_us,compact_time_us,elapsed_ms,file_size_bytes,avg_write_us,avg_read_us,avg_delete_us,avg_compact_us")?;

    let start = Instant::now();
    let mut completed = 0u64;

    while completed < total_ops {
        let op = if known_keys.is_empty() {
            Op::Write
        } else {
            let r = rng.gen_range(0..100);
            if r < 70 {
                Op::Read
            } else if r < 80 {
                Op::Write
            } else if r < 90 {
                Op::Delete
            } else {
                Op::Compact
            }
        };

        match op {
            Op::Write => {
                let key = random_key(&mut rng);
                let value = random_value(&mut rng);
                bytes_written += value.len() as u64;
                let t = Instant::now();
                db.set(&key, &value)?;
                write_time += t.elapsed();
                known_keys.insert(key);
                writes += 1;
            }
            Op::Read => {
                let key = pick_random_key(&known_keys, &mut rng);
                let t = Instant::now();
                if let Some(val) = db.get(&key)? {
                    bytes_read += val.len() as u64;
                }
                read_time += t.elapsed();
                reads += 1;
            }
            Op::Delete => {
                let key = pick_random_key(&known_keys, &mut rng);
                let t = Instant::now();
                db.delete(&key)?;
                delete_time += t.elapsed();
                known_keys.remove(&key);
                deletes += 1;
            }
            Op::Compact => {
                let t = Instant::now();
                db.compact()?;
                compact_time += t.elapsed();
                compacts += 1;
            }
        }

        completed += 1;

        if completed % 100 == 0 || completed == total_ops {
            let file_size = std::fs::metadata(temp_file.path())?.len();
            let elapsed_ms = start.elapsed().as_millis();
            eprintln!(
                "[{completed}/{total_ops}] w:{writes} r:{reads} d:{deletes} c:{compacts}  keys:{}  disk:{}",
                known_keys.len(),
                human_bytes(file_size),
            );
            let avg_write = if writes > 0 { write_time.as_micros() / writes as u128 } else { 0 };
            let avg_read = if reads > 0 { read_time.as_micros() / reads as u128 } else { 0 };
            let avg_delete = if deletes > 0 { delete_time.as_micros() / deletes as u128 } else { 0 };
            let avg_compact = if compacts > 0 { compact_time.as_micros() / compacts as u128 } else { 0 };
            writeln!(
                csv,
                "{completed},{writes},{reads},{deletes},{compacts},{},{bytes_written},{bytes_read},{},{},{},{},{elapsed_ms},{file_size},{avg_write},{avg_read},{avg_delete},{avg_compact}",
                known_keys.len(),
                write_time.as_micros(),
                read_time.as_micros(),
                delete_time.as_micros(),
                compact_time.as_micros(),
            )?;
            csv.flush()?;
        }
    }

    let elapsed = start.elapsed();

    // verify remaining keys
    let db_keys: HashSet<String> = db.keys()?.into_iter().collect();
    let missing: Vec<_> = known_keys.difference(&db_keys).collect();
    assert!(
        missing.is_empty(),
        "keys we expected but were missing from db: {:?}",
        missing,
    );

    eprintln!();
    eprintln!("=== benchmark results ({total_ops} ops in {elapsed:.1?}) ===");
    eprintln!(
        "writes:   {writes:>6}  ({:>9})  {write_time:.1?} total  ({:.1?}/op avg)",
        human_bytes(bytes_written),
        if writes > 0 { write_time / writes as u32 } else { Duration::ZERO },
    );
    eprintln!(
        "reads:    {reads:>6}  ({:>9})  {read_time:.1?} total  ({:.1?}/op avg)",
        human_bytes(bytes_read),
        if reads > 0 { read_time / reads as u32 } else { Duration::ZERO },
    );
    eprintln!(
        "deletes:  {deletes:>6}               {delete_time:.1?} total  ({:.1?}/op avg)",
        if deletes > 0 { delete_time / deletes as u32 } else { Duration::ZERO },
    );
    eprintln!(
        "compacts: {compacts:>6}               {compact_time:.1?} total  ({:.1?}/op avg)",
        if compacts > 0 { compact_time / compacts as u32 } else { Duration::ZERO },
    );
    eprintln!("keys remaining: {}", known_keys.len());

    eprintln!("report written to {report_path}");

    Ok(())
}
