//! `stream-monitor`: tail a JSONL stream (a live Claude Code transcript), append every line to an
//! MMR, cut a window every N lines, and have the Lean follower's producer mode compute the receipt.
//!
//! ```text
//! stream-monitor run   --input FILE --dir DIR --checker STREAM_CHECK [--every 100] [--follow SECS]
//! stream-monitor audit --dir DIR --lo I --hi J --root HEX
//! ```
//!
//! `run` decides nothing: the receipt is computed by `stream-check produce` (Lean) and accepted only
//! by `stream-check follow` / `verify` (Lean, `Policy.checkWindow`). What this binary adds is the
//! MMR the stream is committed to (dregg-query's, with the [`ArityBlake3`] hasher) and a
//! differential: after every window it compares the Lean producer's root with its own incremental
//! [`Frontier`] root and stops on any disagreement.
//!
//! `audit` is the third-party read: from a root obtained elsewhere ALONE (the published root, or the
//! one the Lean follower accepted), open positions `[I, J]` and check them with dregg-query's
//! `verify_range`, the Rust embodiment of `MMR.RVerifies` (correspondence documented, not proved).

use std::fs;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use dregg_query::mmr::{Mmr, verify_range};
use dregg_query::stream::{ArityBlake3, Frontier, entry_value};

fn hex(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1).cloned())
}

fn window_path(dir: &Path, k: u64) -> PathBuf {
    dir.join("windows").join(format!("w{k:06}.jsonl"))
}

struct Run {
    dir: PathBuf,
    checker: String,
    frontier: Frontier<ArityBlake3>,
    pending: Vec<Vec<u8>>,
    k: u64,
}

impl Run {
    fn flush(&mut self) -> Result<(), String> {
        if self.pending.is_empty() {
            return Ok(());
        }
        self.k += 1;
        let mut body = Vec::new();
        for l in &self.pending {
            body.extend_from_slice(l);
            body.push(b'\n');
        }
        let p = window_path(&self.dir, self.k);
        fs::write(&p, &body).map_err(|e| format!("{}: {e}", p.display()))?;
        let t = Instant::now();
        let out = Command::new(&self.checker)
            .arg("produce")
            .arg(&self.dir)
            .output()
            .map_err(|e| format!("{}: {e}", self.checker))?;
        if !out.status.success() {
            return Err(format!(
                "stream-check produce failed: {}",
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        let line = String::from_utf8_lossy(&out.stdout).trim().to_string();
        let f: Vec<&str> = line.split_whitespace().collect();
        let mine = hex(&self.frontier.root());
        if f.len() != 5 || f[3] != mine {
            return Err(format!(
                "DIFFERENTIAL: Lean producer root {:?} != Rust frontier root {mine} at window {}",
                f.get(3),
                self.k
            ));
        }
        println!(
            "window {} [{}, {}) root {} verdict {} (produce {} ms)",
            self.k,
            f[1],
            f[2],
            &mine[..16],
            f[4],
            t.elapsed().as_millis()
        );
        self.pending.clear();
        Ok(())
    }
}

fn run(args: &[String]) -> Result<(), String> {
    let input = arg(args, "--input").ok_or("--input FILE")?;
    let dir = PathBuf::from(arg(args, "--dir").ok_or("--dir DIR")?);
    let checker = arg(args, "--checker").ok_or("--checker PATH")?;
    let every: usize = arg(args, "--every")
        .map_or(Ok(100), |s| s.parse())
        .map_err(|e| format!("--every: {e}"))?;
    let follow: Option<u64> = arg(args, "--follow")
        .map(|s| s.parse())
        .transpose()
        .map_err(|e| format!("--follow: {e}"))?;
    if dir.join("receipts.jsonl").exists() {
        return Err(format!(
            "{} already has receipts; use a fresh dir",
            dir.display()
        ));
    }
    fs::create_dir_all(dir.join("windows")).map_err(|e| e.to_string())?;
    let mut st = Run {
        dir,
        checker,
        frontier: Frontier::new(ArityBlake3),
        pending: Vec::new(),
        k: 0,
    };
    let mut file = fs::File::open(&input).map_err(|e| format!("{input}: {e}"))?;
    let mut offset = 0u64;
    let mut carry: Vec<u8> = Vec::new();
    let mut idle = Instant::now();
    loop {
        file.seek(SeekFrom::Start(offset))
            .map_err(|e| e.to_string())?;
        let mut buf = Vec::new();
        file.read_to_end(&mut buf).map_err(|e| e.to_string())?;
        offset += buf.len() as u64;
        if !buf.is_empty() {
            idle = Instant::now();
        }
        carry.extend_from_slice(&buf);
        // Only complete lines are entries; a partial tail waits for its newline.
        while let Some(i) = carry.iter().position(|&b| b == b'\n') {
            let line: Vec<u8> = carry.drain(..=i).take(i).collect();
            st.frontier.push(&entry_value(&line));
            st.pending.push(line);
            if st.pending.len() == every {
                st.flush()?;
            }
        }
        match follow {
            Some(secs) if idle.elapsed() < Duration::from_secs(secs) => {
                std::thread::sleep(Duration::from_millis(250))
            }
            _ => break,
        }
    }
    st.flush()?;
    println!(
        "done: {} entries in {} windows, root {}",
        st.frontier.len(),
        st.k,
        hex(&st.frontier.root())
    );
    Ok(())
}

fn audit(args: &[String]) -> Result<(), String> {
    let dir = PathBuf::from(arg(args, "--dir").ok_or("--dir DIR")?);
    let lo: u64 = arg(args, "--lo")
        .ok_or("--lo I")?
        .parse()
        .map_err(|e| format!("{e}"))?;
    let hi: u64 = arg(args, "--hi")
        .ok_or("--hi J")?
        .parse()
        .map_err(|e| format!("{e}"))?;
    // The auditor's only trusted input: a root it got elsewhere (the published root, or the root the
    // Lean follower printed on ACCEPT). Nothing is read from the receipts.
    let root_hex =
        arg(args, "--root").ok_or("--root HEX (the published / follower-accepted root)")?;
    let mut root = [0u8; 32];
    hex::decode_to_slice(&root_hex, &mut root).map_err(|e| e.to_string())?;
    // The server side: rebuild the log from the windows and open the range.
    let mut m = Mmr::new(ArityBlake3);
    let mut k = 1;
    while window_path(&dir, k).exists() {
        let body = fs::read(window_path(&dir, k)).map_err(|e| e.to_string())?;
        // The follower's split: every newline-terminated line is an entry, empty ones included.
        let mut parts: Vec<&[u8]> = body.split(|&b| b == b'\n').collect();
        if parts.last().is_some_and(|l| l.is_empty()) {
            parts.pop();
        }
        for l in parts {
            m.push(entry_value(l));
        }
        k += 1;
    }
    let (vals, opening) = m.open_range(lo, hi);
    let wire = serde_json::to_string(&opening).map_err(|e| e.to_string())?;
    // The client side: dregg-query's `verify_range` against the root alone. It is the Rust embodiment
    // of `MMR.RVerifies` (mmr.rs documents the correspondence; it is not proved), so this is an
    // audit read, not the stream's acceptance, which is `stream-check`'s.
    let len = verify_range(&ArityBlake3, &root, lo, hi, &vals, &opening)
        .map_err(|e| format!("REFUSE: {e}"))?;
    for (j, v) in vals.iter().enumerate() {
        println!("pos {}: {}", lo as usize + j, &hex(v)[..16]);
    }
    println!(
        "VERIFIED [{lo}, {hi}] against root {}: committed length {len}, {} values, opening {} bytes",
        &root_hex[..16],
        vals.len(),
        wire.len()
    );
    // Two server attacks on the same query, both refused by the root alone.
    if vals.len() > 1 {
        let mut short = opening.clone();
        short.paths.remove(0);
        let r = verify_range(&ArityBlake3, &root, lo, hi, &vals[1..], &short);
        println!(
            "omit position {lo} (answer and path removed): {:?}",
            r.err()
        );
        let (shifted, sop) = m.open_range(lo + 1, hi + 1);
        if shifted.len() == vals.len() {
            let r = verify_range(&ArityBlake3, &root, lo, hi, &shifted, &sop);
            println!(
                "shift by one (positions {}..{} passed off as {lo}..{hi}): {:?}",
                lo + 1,
                hi + 1,
                r.err()
            );
        }
    }
    let _ = std::io::stdout().flush();
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let r = match args.get(1).map(String::as_str) {
        Some("run") => run(&args),
        Some("audit") => audit(&args),
        _ => Err("usage: stream-monitor run --input FILE --dir DIR --checker PATH [--every N] [--follow SECS] | audit --dir DIR --lo I --hi J --root HEX".into()),
    };
    if let Err(e) = r {
        eprintln!("stream-monitor: {e}");
        std::process::exit(1);
    }
}
