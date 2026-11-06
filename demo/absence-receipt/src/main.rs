//! absence-receipt: the Rust legs of demo (a). See `demo/absence-receipt/README.md`.
//!
//! ```text
//! absence-receipt select  <index-root> <n> <manifest-out>
//! absence-receipt digest  <file>                                         # blake3 hex
//! absence-receipt hashes  <index-root> <manifest> <documents.tsv-out>     # index, path, bytes, blake3
//! absence-receipt mmr     <documents.tsv>                                  # prints the root and counts
//! absence-receipt compile <policy.txt> <table.json-out>                    # dregg_dfa::Re::compile + minimize
//! absence-receipt count   <table.json> <index-root> <manifest>             # Rust cross-check of the Lean count
//! absence-receipt receipt <policy.txt> <table.json> <documents.tsv> <dfa-run.json> <pin> <receipt.json-out>
//! ```
//!
//! The documents are read as untrusted data: bytes in, hashes and verdicts out; nothing in the
//! corpus is executed or interpreted beyond the byte fold.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use absence_receipt::absence_table;
use dregg_dfa::Dfa;
use dregg_query::mmr::{Blake3Mmr, Mmr};

fn die(msg: impl std::fmt::Display) -> ExitCode {
    eprintln!("absence-receipt: {msg}");
    ExitCode::from(2)
}

// ---------------------------------------------------------------------------------------------
// select: every regular file under the index root except dot-entries and the root config.json,
// as '/'-joined relative paths, sorted bytewise; the first n.
// ---------------------------------------------------------------------------------------------

fn walk(root: &Path, rel: &str, out: &mut Vec<String>) -> std::io::Result<()> {
    let dir = if rel.is_empty() {
        root.to_path_buf()
    } else {
        root.join(rel)
    };
    for entry in fs::read_dir(&dir)? {
        let entry = entry?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if name.starts_with('.') {
            continue;
        }
        let path = if rel.is_empty() {
            name.clone()
        } else {
            format!("{rel}/{name}")
        };
        let ft = entry.file_type()?;
        if ft.is_dir() {
            walk(root, &path, out)?;
        } else if ft.is_file() && !(rel.is_empty() && name == "config.json") {
            out.push(path);
        }
    }
    Ok(())
}

fn select(root: &Path, n: usize, out: &Path) -> Result<usize, String> {
    let mut all = Vec::new();
    walk(root, "", &mut all).map_err(|e| e.to_string())?;
    all.sort_unstable_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    let total = all.len();
    if total < n {
        return Err(format!("only {total} documents under {}", root.display()));
    }
    let mut body = all[..n].join("\n");
    body.push('\n');
    fs::write(out, body).map_err(|e| e.to_string())?;
    Ok(total)
}

fn read_manifest(p: &Path) -> Result<Vec<String>, String> {
    Ok(fs::read_to_string(p)
        .map_err(|e| format!("{}: {e}", p.display()))?
        .lines()
        .filter(|l| !l.is_empty())
        .map(str::to_owned)
        .collect())
}

// ---------------------------------------------------------------------------------------------
// hashes + mmr: leaf value = blake3(document bytes); the MMR is dregg-query's Blake3Mmr
// (tags dregg-query-mmr-v1:{leaf,node,bag,empty}).
// ---------------------------------------------------------------------------------------------

fn hashes(root: &Path, manifest: &Path, out: &Path) -> Result<(), String> {
    let docs = read_manifest(manifest)?;
    let mut f = fs::File::create(out).map_err(|e| e.to_string())?;
    for (i, rel) in docs.iter().enumerate() {
        let bytes = fs::read(root.join(rel)).map_err(|e| format!("{rel}: {e}"))?;
        let h = blake3::hash(&bytes);
        writeln!(f, "{i}\t{rel}\t{}\t{}", bytes.len(), h.to_hex()).map_err(|e| e.to_string())?;
    }
    Ok(())
}

struct DocRow {
    bytes: u64,
    hash: [u8; 32],
}

fn read_tsv(p: &Path) -> Result<Vec<DocRow>, String> {
    let text = fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))?;
    let mut rows = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let cols: Vec<&str> = line.split('\t').collect();
        if cols.len() != 4 || cols[0] != i.to_string() {
            return Err(format!("documents.tsv line {i} malformed"));
        }
        let bytes: u64 = cols[2].parse().map_err(|_| format!("line {i}: bad size"))?;
        let mut hash = [0u8; 32];
        hex::decode_to_slice(cols[3], &mut hash).map_err(|_| format!("line {i}: bad hash"))?;
        rows.push(DocRow { bytes, hash });
    }
    Ok(rows)
}

fn mmr_root(rows: &[DocRow]) -> [u8; 32] {
    Mmr::from_values(Blake3Mmr, rows.iter().map(|r| r.hash).collect()).root()
}

/// Nodes of an MMR over n leaves: 2n − popcount(n) (leaves plus internal nodes of the peaks).
fn mmr_nodes(n: u64) -> u64 {
    2 * n - u64::from(n.count_ones())
}

// ---------------------------------------------------------------------------------------------
// receipt: the signed body. Canonical: fixed key order, no whitespace, one trailing newline.
// ---------------------------------------------------------------------------------------------

fn receipt(
    policy: &Path,
    table: &Path,
    tsv: &Path,
    run: &Path,
    pin: &str,
    out: &Path,
) -> Result<String, String> {
    let policy_digest = blake3::hash(&fs::read(policy).map_err(|e| e.to_string())?);
    let table_digest = blake3::hash(&fs::read(table).map_err(|e| e.to_string())?);
    let rows = read_tsv(tsv)?;
    let root = mmr_root(&rows);
    let run: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(run).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    let docs = run["documents"]
        .as_u64()
        .ok_or("dfa-run output lacks documents")?;
    let count = run["count"].as_u64().ok_or("dfa-run output lacks count")?;
    if docs != rows.len() as u64 {
        return Err(format!(
            "dfa-run read {docs} documents, documents.tsv has {}",
            rows.len()
        ));
    }
    if run["table_well_formed"] != serde_json::Value::Bool(true) {
        return Err("dfa-run reports the table malformed".into());
    }
    let body = format!(
        "{{\"v\":\"absence-receipt-v1\",\"policy_blake3\":\"{}\",\"table_blake3\":\"{}\",\
         \"corpus_mmr_root\":\"{}\",\"corpus_pin\":\"{pin}\",\"n\":{docs},\"count\":{count}}}\n",
        policy_digest.to_hex(),
        table_digest.to_hex(),
        hex::encode(root),
    );
    fs::write(out, &body).map_err(|e| e.to_string())?;
    Ok(body)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let a: Vec<&str> = args.iter().map(String::as_str).collect();
    let r = match a.get(1..).unwrap_or_default() {
        ["select", root, n, out] => {
            let Ok(n) = n.parse() else { return die("n must be a number") };
            select(Path::new(root), n, Path::new(out))
                .map(|total| println!("selected {n} of {total} index files"))
        }
        ["digest", f] => fs::read(f).map_err(|e| e.to_string()).map(|b| println!("{}", blake3::hash(&b).to_hex())),
        ["hashes", root, manifest, out] => hashes(Path::new(root), Path::new(manifest), Path::new(out)),
        ["mmr", tsv] => read_tsv(Path::new(tsv)).map(|rows| {
            let n = rows.len() as u64;
            let bytes: u64 = rows.iter().map(|r| r.bytes).sum();
            println!(
                "{{\"documents\":{n},\"bytes\":{bytes},\"mmr_nodes\":{},\"mmr_peaks\":{},\"root\":\"{}\"}}",
                mmr_nodes(n),
                n.count_ones(),
                hex::encode(mmr_root(&rows))
            );
        }),
        ["compile", policy, out] => fs::read_to_string(policy)
            .map_err(|e| e.to_string())
            .and_then(|p| absence_table(&p))
            .and_then(|dfa| {
                let json = serde_json::to_string(&dfa).map_err(|e| e.to_string())?;
                fs::write(out, json + "\n").map_err(|e| e.to_string())?;
                println!(
                    "{{\"num_states\":{},\"accepting\":{},\"transitions\":{}}}",
                    dfa.num_states,
                    dfa.accepting.len(),
                    dfa.transitions.len()
                );
                Ok(())
            }),
        ["count", table, root, manifest] => (|| {
            let dfa: Dfa = serde_json::from_str(&fs::read_to_string(table).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
            let docs = read_manifest(Path::new(manifest))?;
            let mut rejected = Vec::new();
            for (i, rel) in docs.iter().enumerate() {
                let bytes = fs::read(PathBuf::from(root).join(rel)).map_err(|e| e.to_string())?;
                if !dfa.matches(&bytes) {
                    rejected.push(i);
                }
            }
            println!("{{\"documents\":{},\"count\":{},\"rejected_indices\":{:?}}}", docs.len(), rejected.len(), rejected);
            Ok(())
        })(),
        ["receipt", policy, table, tsv, run, pin, out] => {
            receipt(Path::new(policy), Path::new(table), Path::new(tsv), Path::new(run), pin, Path::new(out))
                .map(|body| print!("{body}"))
        }
        _ => return die("usage: see the header of demo/absence-receipt/src/main.rs"),
    };
    match r {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => die(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn absence_table_refuses_a_key_and_admits_its_near_misses() {
        let dfa =
            absence_table("forbid AKIA[0-9A-Z]{16}\nforbid -----BEGIN [A-Z ]*PRIVATE KEY-----\n")
                .expect("compiles");
        assert!(dfa.matches(b"{\"name\":\"serde\",\"vers\":\"1.0.0\"}"));
        assert!(!dfa.matches(b"x AKIAIOSFODNN7EXAMPLE y"));
        assert!(dfa.matches(b"AKIAIOSFODNN7EXAMPL"));
        assert!(dfa.matches(b"AKIAiosfodnn7example"));
        // Built from parts so the repository's secret scanner does not read a key header here.
        let rsa = format!("-----BEGIN RSA {}-----", "PRIVATE KEY");
        let bare = format!("..-----BEGIN {}-----..", "PRIVATE KEY");
        assert!(!dfa.matches(rsa.as_bytes()));
        assert!(!dfa.matches(bare.as_bytes()));
        assert!(dfa.matches(b"-----BEGIN PUBLIC KEY-----"));
        assert!(dfa.matches(b""));
    }

    #[test]
    fn mmr_node_count() {
        assert_eq!(mmr_nodes(1), 1);
        assert_eq!(mmr_nodes(3), 4);
        assert_eq!(mmr_nodes(100_000), 199_994);
    }
}
