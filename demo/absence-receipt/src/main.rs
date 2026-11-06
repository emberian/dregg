//! absence-receipt: the Rust legs of demo (a). See `demo/absence-receipt/README.md`.
//!
//! ```text
//! absence-receipt select  <index-root> <n> <manifest-out>
//! absence-receipt digest  <file>                                         # blake3 hex
//! absence-receipt hashes  <index-root> <manifest> <documents.tsv-out>     # index, path, bytes, blake3
//! absence-receipt mmr     <documents.tsv>                                  # prints the root and counts
//! absence-receipt compile <policy.txt> <table.json-out>                    # INTERIM, unproved compiler
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

use dregg_dfa::{ByteClass, Dfa, Re};
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
// compile: the INTERIM policy compiler. Policy lines `forbid <pattern>`; the pattern subset is
// literal bytes, `\x` escapes, `.`, `[..]` classes with ranges, and the postfix operators
// `* + ? {n}` on one atom. The absence table is `~(any* · (P1 | P2 | ...) · any*)` through
// dregg-dfa's derivative compiler. UNPROVED: a second grammar outside Lean, kept only until
// lane B's `policyc compile --absence` emits the table.
// ---------------------------------------------------------------------------------------------

fn parse_class(p: &[u8], i: &mut usize) -> Result<ByteClass, String> {
    let mut ranges = Vec::new();
    let negate = p.get(*i) == Some(&b'^');
    if negate {
        *i += 1;
    }
    loop {
        let Some(&c) = p.get(*i) else {
            return Err("unterminated [".into());
        };
        *i += 1;
        if c == b']' {
            break;
        }
        let lo = if c == b'\\' {
            let e = *p.get(*i).ok_or("dangling \\")?;
            *i += 1;
            e
        } else {
            c
        };
        if p.get(*i) == Some(&b'-') && p.get(*i + 1).is_some_and(|&n| n != b']') {
            let hi = p[*i + 1];
            *i += 2;
            ranges.push((lo, hi));
        } else {
            ranges.push((lo, lo));
        }
    }
    let class = ByteClass::from_ranges(ranges);
    Ok(if negate { class.complement() } else { class })
}

fn parse_pattern(p: &[u8]) -> Result<Re, String> {
    let mut i = 0;
    let mut seq = Re::epsilon();
    while i < p.len() {
        let atom = match p[i] {
            b'[' => {
                i += 1;
                Re::sym(parse_class(p, &mut i)?)
            }
            b'.' => {
                i += 1;
                Re::any_byte()
            }
            b'\\' => {
                let e = *p.get(i + 1).ok_or("dangling \\")?;
                i += 2;
                Re::byte(e)
            }
            b'(' | b')' | b'|' => {
                return Err("groups and alternation are not in the interim subset".into());
            }
            c => {
                i += 1;
                Re::byte(c)
            }
        };
        let atom = match p.get(i) {
            Some(b'*') => {
                i += 1;
                atom.star()
            }
            Some(b'+') => {
                i += 1;
                atom.clone().then(atom.star())
            }
            Some(b'?') => {
                i += 1;
                atom.or(Re::epsilon())
            }
            Some(b'{') => {
                let close = p[i..]
                    .iter()
                    .position(|&c| c == b'}')
                    .ok_or("unterminated {")?
                    + i;
                let n: usize = std::str::from_utf8(&p[i + 1..close])
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .ok_or("bad {n}")?;
                i = close + 1;
                (0..n).fold(Re::epsilon(), |acc, _| acc.then(atom.clone()))
            }
            _ => atom,
        };
        seq = seq.then(atom);
    }
    Ok(seq)
}

fn policy_patterns(policy: &str) -> Result<Vec<String>, String> {
    let mut pats = Vec::new();
    for line in policy.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let rest = line
            .strip_prefix("forbid ")
            .ok_or_else(|| format!("not a forbid line: {line}"))?;
        pats.push(rest.to_owned());
    }
    if pats.is_empty() {
        return Err("policy forbids nothing".into());
    }
    Ok(pats)
}

/// Flatten nested `Alt` (or `Inter`) into its operands.
fn flatten(r: Re, alt: bool, out: &mut Vec<Re>) {
    match r {
        Re::Alt(l, rr) if alt => {
            flatten(*l, alt, out);
            flatten(*rr, alt, out);
        }
        Re::Inter(l, rr) if !alt => {
            flatten(*l, alt, out);
            flatten(*rr, alt, out);
        }
        other => out.push(other),
    }
}

fn flatten_cat(r: Re, out: &mut Vec<Re>) {
    match r {
        Re::Cat(l, rr) => {
            flatten_cat(*l, out);
            flatten_cat(*rr, out);
        }
        other => out.push(other),
    }
}

/// ACI-normal form: `Alt`/`Inter` flattened, sorted, deduplicated and right-nested; `Cat`
/// right-associated. Brzozowski's theorem bounds the derivatives only up to this similarity
/// (the Lean `Deriv/Similarity.lean` relation); `dregg_dfa::Re::or` normalizes commutativity and
/// idempotence at the top pair only, which is why `Re::compile` does not terminate on
/// `~(any* · w · any*)` (README, "What the interim compiler found").
fn norm(r: Re) -> Re {
    match r {
        Re::Alt(..) | Re::Inter(..) => {
            let alt = matches!(r, Re::Alt(..));
            let mut parts = Vec::new();
            flatten(r, alt, &mut parts);
            let mut parts: Vec<Re> = parts.into_iter().map(norm).collect();
            let mut flat = Vec::new();
            for p in parts.drain(..) {
                flatten(p, alt, &mut flat);
            }
            flat.sort();
            flat.dedup();
            if alt {
                flat.retain(|p| !matches!(p, Re::Empty));
            } else if flat.iter().any(|p| matches!(p, Re::Empty)) {
                return Re::Empty;
            }
            let Some(last) = flat.pop() else {
                return Re::Empty;
            };
            flat.into_iter().rev().fold(last, |acc, p| {
                if alt {
                    Re::Alt(Box::new(p), Box::new(acc))
                } else {
                    Re::Inter(Box::new(p), Box::new(acc))
                }
            })
        }
        Re::Cat(..) => {
            let mut parts = Vec::new();
            flatten_cat(r, &mut parts);
            let parts: Vec<Re> = parts.into_iter().map(norm).collect();
            parts
                .into_iter()
                .rev()
                .fold(Re::epsilon(), |acc, p| p.then(acc))
        }
        Re::Neg(x) => norm(*x).not(),
        Re::Star(x) => norm(*x).star(),
        leaf => leaf,
    }
}

/// Derivative determinization over ACI-normal forms: state 0 is `Re::Empty` (the dead sink),
/// state 1 the start, rows of 256 in the `dregg_dfa::Dfa` layout.
fn determinize(re: Re) -> Dfa {
    use std::collections::{BTreeSet, HashMap};
    let start = norm(re);
    let mut ids: HashMap<Re, u32> = HashMap::new();
    let mut order: Vec<Re> = vec![Re::empty()];
    ids.insert(Re::empty(), 0);
    let mut transitions: Vec<u32> = vec![0; 256];
    let mut accepting = BTreeSet::new();
    // Start is always state 1 (the crate's layout), even if it is similar to the dead state.
    order.push(start.clone());
    ids.entry(start.clone()).or_insert(1);
    transitions.extend(std::iter::repeat_n(0, 256));
    if start.nullable() {
        accepting.insert(1u32);
    }
    let mut i = 1usize;
    while i < order.len() {
        let cur = order[i].clone();
        for b in 0..=255u8 {
            let next = norm(cur.derive(b));
            let id = if let Some(&id) = ids.get(&next) {
                id
            } else {
                let id = order.len() as u32;
                ids.insert(next.clone(), id);
                if next.nullable() {
                    accepting.insert(id);
                }
                order.push(next);
                transitions.extend(std::iter::repeat_n(0, 256));
                id
            };
            transitions[i * 256 + b as usize] = id;
        }
        i += 1;
    }
    Dfa {
        num_states: order.len() as u32,
        transitions,
        start: 1,
        accepting,
    }
}

fn absence_table(policy: &str) -> Result<Dfa, String> {
    let mut union = Re::empty();
    for pat in policy_patterns(policy)? {
        union = union.or(parse_pattern(pat.as_bytes())?);
    }
    let any = Re::any_byte().star();
    Ok(minimize(&determinize(
        any.clone().then(union).then(any).not(),
    )))
}

/// Moore partition refinement, then renumber with the dead class at 0 and the start class at 1
/// (classes in order of first reach by breadth-first search from the start).
fn minimize(d: &Dfa) -> Dfa {
    use std::collections::{BTreeSet, HashMap, VecDeque};
    let n = d.num_states as usize;
    let mut class: Vec<u32> = (0..n)
        .map(|s| u32::from(d.accepting.contains(&(s as u32))))
        .collect();
    loop {
        let mut sig: HashMap<(u32, Vec<u32>), u32> = HashMap::new();
        let mut next = vec![0u32; n];
        for s in 0..n {
            let row: Vec<u32> = (0..256)
                .map(|b| class[d.transitions[s * 256 + b] as usize])
                .collect();
            let k = (class[s], row);
            let len = sig.len() as u32;
            next[s] = *sig.entry(k).or_insert(len);
        }
        let before = class.iter().collect::<BTreeSet<_>>().len();
        let after = sig.len();
        class = next;
        if after == before {
            break;
        }
    }
    // renumber: dead (class of state 0) -> 0, start class -> 1, then BFS order
    let mut map: HashMap<u32, u32> = HashMap::new();
    map.insert(class[0], 0);
    let start_class = class[d.start as usize];
    let mut reps: Vec<usize> = vec![0];
    let mut queue = VecDeque::new();
    if let std::collections::hash_map::Entry::Vacant(e) = map.entry(start_class) {
        e.insert(1);
        reps.push(d.start as usize);
    }
    queue.push_back(d.start as usize);
    let mut seen = BTreeSet::new();
    seen.insert(d.start as usize);
    while let Some(s) = queue.pop_front() {
        for b in 0..256 {
            let t = d.transitions[s * 256 + b] as usize;
            if let std::collections::hash_map::Entry::Vacant(e) = map.entry(class[t]) {
                e.insert(reps.len() as u32);
                reps.push(t);
            }
            if seen.insert(t) {
                queue.push_back(t);
            }
        }
    }
    let mut transitions = Vec::with_capacity(reps.len() * 256);
    let mut accepting = BTreeSet::new();
    for (new, &old) in reps.iter().enumerate() {
        for b in 0..256 {
            transitions.push(map[&class[d.transitions[old * 256 + b] as usize]]);
        }
        if d.accepting.contains(&(old as u32)) {
            accepting.insert(new as u32);
        }
    }
    let start = if class[d.start as usize] == class[0] {
        0
    } else {
        1
    };
    Dfa {
        num_states: reps.len() as u32,
        transitions,
        start,
        accepting,
    }
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
