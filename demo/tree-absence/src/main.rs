//! tree-cert: produce tree certificates for `tree-check verify` (the Lean checker decides).
//!
//!     tree-cert project <record.json>                         canonical CBOR, tree root, flat digest
//!     tree-cert field <record.json> <path-json> <table.json> <out-cert.json>
//!     tree-cert schema <record.json> <schema.json> <out-cert.json>
//!     tree-cert corpus <records.jsonl> <query.json> <out-cert.json>
//!     tree-cert conform <records.jsonl> [--edges] [--tmp DIR] [--jobs N]
//!     tree-cert table-contains <word> <out-table.json>       dregg-dfa fallback compiler
//!     tree-cert table-invocation [--no-backtick] <out-table.json>             query (B) / (C)
//!     tree-cert diff-invocation [--no-backtick] <table.json> <records.jsonl>  table vs regex oracle
//!     tree-cert flat-scan <file> <word>                       lines whose RAW bytes contain word
//!
//! `query.json` is `{"conjuncts": [{"path": ["input", "command"], "table": "<table.json>"}, ...]}`
//! with table paths relative to the query file. Exit 0 ok, 1 mismatch (conform), 2 bad input.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use tree_absence::cert::{corpus_cert, field_cert, schema_cert, Conjunct};
use tree_absence::json::parse;
use tree_absence::merkle::path_of_json;
use tree_absence::schema::Table;
use tree_absence::value::JVal;
use tree_absence::{project_line, tree_check_path, EDGES};

type R<T> = Result<T, String>;

fn read(p: &str) -> R<Vec<u8>> {
    std::fs::read(p).map_err(|e| format!("{p}: {e}"))
}

fn read_json(p: &Path) -> R<serde_json::Value> {
    let b = std::fs::read(p).map_err(|e| format!("{}: {e}", p.display()))?;
    serde_json::from_slice(&b).map_err(|e| format!("{}: {e}", p.display()))
}

fn record(p: &str) -> R<JVal> {
    parse(&read(p)?).ok_or_else(|| format!("{p}: not JSON in the model (Json.parse refuses it)"))
}

fn table(p: &Path) -> R<Table> {
    Table::from_json(&read_json(p)?)
}

fn write_json(p: &str, v: &serde_json::Value) -> R<()> {
    std::fs::write(p, serde_json::to_vec(v).map_err(|e| e.to_string())?).map_err(|e| format!("{p}: {e}"))
}

fn lines(p: &str) -> R<Vec<Vec<u8>>> {
    let b = read(p)?;
    let mut v: Vec<Vec<u8>> = b.split(|&c| c == b'\n').map(|l| l.to_vec()).collect();
    if v.last().is_some_and(|l| l.is_empty()) {
        v.pop();
    }
    Ok(v)
}

fn corpus(recs: &str, query: &str, out: &str) -> R<()> {
    let qj = read_json(Path::new(query))?;
    let base = Path::new(query).parent().unwrap_or(Path::new("."));
    let cs = qj.get("conjuncts").and_then(|c| c.as_array()).ok_or("query: want {\"conjuncts\": [...]}")?;
    let mut q = Vec::new();
    for c in cs {
        let path = path_of_json(c.get("path").ok_or("conjunct: path")?)?;
        let t = c.get("table").and_then(|t| t.as_str()).ok_or("conjunct: table")?;
        q.push(Conjunct { path, table: table(&base.join(t))? });
    }
    let mut records = Vec::new();
    let mut refused = Vec::new();
    for (i, l) in lines(recs)?.iter().enumerate() {
        match parse(l) {
            Some(v) => records.push(v),
            None => refused.push(i),
        }
    }
    if !refused.is_empty() {
        return Err(format!("{recs}: {} line(s) outside the model (0-based): {refused:?}", refused.len()));
    }
    let t = std::time::Instant::now();
    let o = corpus_cert(&records, &q);
    let ms = t.elapsed().as_millis();
    write_json(out, &o.cert)?;
    println!(
        "{}",
        serde_json::json!({ "n": records.len(), "count": o.count, "mmr_root": o.mmr_root,
            "refuted_at_conjunct": o.refuted_at, "matching_records": o.matching, "produce_ms": ms })
    );
    Ok(())
}

/// The Lean projection of one text: `Some(line)` or `None` when it refuses (exit 2).
fn lean_project(tc: &Path, file: &Path) -> R<Option<String>> {
    let o = Command::new(tc).arg("project").arg(file).output().map_err(|e| format!("{}: {e}", tc.display()))?;
    match o.status.code() {
        Some(0) => Ok(Some(String::from_utf8_lossy(&o.stdout).trim_end().to_string())),
        Some(2) => Ok(None),
        c => Err(format!("tree-check project: exit {c:?}")),
    }
}

fn conform(args: &[String]) -> R<bool> {
    let mut texts: Vec<Vec<u8>> = Vec::new();
    let mut tmp = PathBuf::from("corpus/conform-tmp");
    let mut jobs = 8usize;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--edges" => texts.extend(EDGES.iter().map(|e| e.to_vec())),
            "--tmp" => {
                i += 1;
                tmp = PathBuf::from(args.get(i).ok_or("--tmp DIR")?);
            }
            "--jobs" => {
                i += 1;
                jobs = args.get(i).and_then(|j| j.parse().ok()).ok_or("--jobs N")?;
            }
            f => texts.extend(lines(f)?),
        }
        i += 1;
    }
    std::fs::create_dir_all(&tmp).map_err(|e| e.to_string())?;
    let tc = tree_check_path();
    let next = AtomicUsize::new(0);
    let (acc, refu) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let bad: Mutex<Vec<(usize, String, String)>> = Mutex::new(Vec::new());
    let err: Mutex<Option<String>> = Mutex::new(None);
    std::thread::scope(|s| {
        for w in 0..jobs {
            let (texts, tmp, tc, next, acc, refu, bad, err) = (&texts, &tmp, &tc, &next, &acc, &refu, &bad, &err);
            s.spawn(move || {
                let file = tmp.join(format!("w{w}.json"));
                loop {
                    let k = next.fetch_add(1, Ordering::Relaxed);
                    let Some(t) = texts.get(k) else { break };
                    let rust = parse(t).map(|v| project_line(&v));
                    if let Err(e) = std::fs::write(&file, t) {
                        *err.lock().unwrap() = Some(e.to_string());
                        break;
                    }
                    match lean_project(tc, &file) {
                        Err(e) => {
                            *err.lock().unwrap() = Some(e);
                            break;
                        }
                        Ok(lean) if lean == rust => {
                            if lean.is_some() { acc.fetch_add(1, Ordering::Relaxed) } else { refu.fetch_add(1, Ordering::Relaxed) };
                        }
                        Ok(lean) => bad.lock().unwrap().push((
                            k,
                            rust.unwrap_or_else(|| "REFUSE".into()),
                            lean.unwrap_or_else(|| "REFUSE".into()),
                        )),
                    }
                }
                let _ = std::fs::remove_file(&file);
            });
        }
    });
    if let Some(e) = err.into_inner().unwrap() {
        return Err(e);
    }
    let mut bad = bad.into_inner().unwrap();
    bad.sort();
    for (k, r, l) in bad.iter().take(20) {
        eprintln!("RED text {k}: rust {r} / lean {l}");
    }
    println!(
        "{}",
        serde_json::json!({ "texts": texts.len(), "agree_accept": acc.load(Ordering::Relaxed),
            "agree_refuse": refu.load(Ordering::Relaxed), "mismatch": bad.len() })
    );
    Ok(bad.is_empty())
}

fn run(args: &[String]) -> R<ExitCode> {
    let a: Vec<&str> = args.iter().map(String::as_str).collect();
    match a.as_slice() {
        ["project", f] => println!("{}", project_line(&record(f)?)),
        ["field", f, p, t, out] => {
            let path = path_of_json(&serde_json::from_str(p).map_err(|e| format!("path: {e}"))?)?;
            let (v, c) = field_cert(&record(f)?, &path, &table(Path::new(t))?);
            write_json(out, &c)?;
            println!("{}", serde_json::json!({ "verdict": v.as_str(), "tree_root": c["statement"]["tree_root"] }));
        }
        ["schema", f, s, out] => {
            let (v, c) = schema_cert(&record(f)?, &record(s)?)?;
            write_json(out, &c)?;
            println!("{}", serde_json::json!({ "verdict": v, "tree_root": c["statement"]["tree_root"] }));
        }
        ["corpus", r, q, out] => corpus(r, q, out)?,
        ["conform", rest @ ..] if !rest.is_empty() => {
            return Ok(if conform(&args[1..])? { ExitCode::SUCCESS } else { ExitCode::from(1) });
        }
        ["table-contains", w, out] => {
            use dregg_dfa::Re;
            let d = Re::top().then(Re::word(w.as_bytes())).then(Re::top()).compile().minimize();
            let t = Table {
                num_states: d.num_states as usize,
                transitions: d.transitions.iter().map(|&x| x as usize).collect(),
                start: d.start as usize,
                accepting: d.accepting.iter().map(|&x| x as usize).collect(),
            };
            write_json(out, &t.to_json())?;
            println!("{} states", t.num_states);
        }
        ["table-invocation", out] | ["table-invocation", "--no-backtick", out] => {
            let bt = a.len() == 2;
            let d = tree_absence::invocation::invocation_re(bt).compile().minimize();
            let t = Table {
                num_states: d.num_states as usize,
                transitions: d.transitions.iter().map(|&x| x as usize).collect(),
                start: d.start as usize,
                accepting: d.accepting.iter().map(|&x| x as usize).collect(),
            };
            write_json(out, &t.to_json())?;
            println!("{} states", t.num_states);
        }
        ["diff-invocation", t, recs] | ["diff-invocation", "--no-backtick", t, recs] => {
            let bt = a.len() == 3;
            use tree_absence::invocation::{invocation_oracle, CASES};
            use tree_absence::merkle::{lookup, Step};
            let t = table(Path::new(t))?;
            let re = invocation_oracle(bt);
            let path = [Step::Key(b"input".to_vec()), Step::Key(b"command".to_vec())];
            let (mut n, mut hits, mut bad) = (0usize, 0usize, Vec::new());
            for (i, l) in lines(recs)?.iter().enumerate() {
                let v = parse(l).ok_or_else(|| format!("line {i}: outside the model"))?;
                let tree_absence::value::JVal::Obj(kvs) = &v else { continue };
                if tree_absence::merkle::find_key(b"name", kvs) != Some(&JVal::Str(b"Bash".to_vec())) {
                    continue;
                }
                if let Some(JVal::Str(c)) = lookup(&v, &path) {
                    n += 1;
                    let (a, b) = (t.accepts(c), re.is_match(c));
                    hits += a as usize;
                    if a != b {
                        bad.push(format!("record {i}: table {a} oracle {b}"));
                    }
                }
            }
            let mut case_bad = Vec::new();
            for (c, wb, wc) in CASES {
                let want = if bt { wb } else { wc };
                let (a, b) = (t.accepts(c.as_bytes()), re.is_match(c.as_bytes()));
                if a != *want || b != *want {
                    case_bad.push(format!("{c:?}: want {want} table {a} oracle {b}"));
                }
            }
            for m in bad.iter().chain(&case_bad) {
                eprintln!("RED {m}");
            }
            println!("{}", serde_json::json!({ "bash_commands": n, "table_accepts": hits,
                "disagree": bad.len(), "cases": CASES.len(), "cases_wrong": case_bad.len() }));
            if !(bad.is_empty() && case_bad.is_empty()) {
                return Ok(ExitCode::from(1));
            }
        }
        ["flat-scan", f, w] => {
            let hits: Vec<usize> = lines(f)?
                .iter()
                .enumerate()
                .filter(|(_, l)| l.windows(w.len()).any(|x| x == w.as_bytes()))
                .map(|(i, _)| i)
                .collect();
            println!("{}", serde_json::json!({ "word": w, "lines_hit": hits.len(), "hits": hits }));
        }
        _ => {
            eprintln!("usage: see the header of src/main.rs");
            return Ok(ExitCode::from(2));
        }
    }
    Ok(ExitCode::SUCCESS)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // Deep nesting recurses; give the parser room.
    let h = std::thread::Builder::new().stack_size(512 << 20).spawn(move || run(&args)).expect("thread");
    match h.join().expect("join") {
        Ok(c) => c,
        Err(e) => {
            eprintln!("tree-cert: {e}");
            ExitCode::from(2)
        }
    }
}
