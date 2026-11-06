//! Producer ↔ Lean checker round trips on a synthetic corpus: honest certificates are ACCEPTed by
//! `tree-check verify`, tampered ones REFUSEd (exit 1). Needs the built `tree-check`
//! (`$TREE_CHECK` or metatheory/.lake/build/bin/tree-check). Run filtered:
//! `cargo test --release -- negatives_` (never unfiltered).

use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;
use tree_absence::cert::{corpus_cert, field_cert, schema_cert, Conjunct};
use tree_absence::json::parse;
use tree_absence::merkle::{open_at, opening_json, Step};
use tree_absence::schema::Table;
use tree_absence::tree_check_path;
use tree_absence::value::JVal;

fn dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn table(name: &str) -> Table {
    let b = std::fs::read(dir().join("tables").join(name)).unwrap();
    Table::from_json(&serde_json::from_slice(&b).unwrap()).unwrap()
}

fn query() -> Vec<Conjunct> {
    vec![
        Conjunct { path: vec![Step::Key(b"name".to_vec())], table: table("bash.policyc.json") },
        Conjunct {
            path: vec![Step::Key(b"input".to_vec()), Step::Key(b"command".to_vec())],
            table: table("pkill.json"),
        },
    ]
}

fn rec(s: &[u8]) -> JVal {
    parse(s).expect("synthetic record is in the model")
}

fn records() -> Vec<JVal> {
    [
        &br#"{"name":"Read","input":{"file_path":"/x"}}"#[..],
        br#"{"name":"Bash","input":{"command":"git status"}}"#,
        // escaped control: a flat byte scan of this text for `pkill -f` finds nothing
        b"{\"name\":\"Bash\",\"input\":{\"command\":\"\\u0070kill -f node\"}}",
        br#"{"name":"Bash","input":{"command":"pkill -f node"}}"#,
        br#"{"name":"Bash","input":{"cmd":"pkill -f node"}}"#,
        br#"{"name":"Bash","input":{"command":["pkill -f node"]}}"#,
        br#"{"name":"Write","input":{"content":"pkill -f node"}}"#,
    ]
    .iter()
    .map(|s| rec(s))
    .collect()
}

/// `tree-check verify`'s exit code (0 accept, 1 refuse, 2 malformed).
fn verify(cert: &Value, tag: &str) -> i32 {
    let tmp = dir().join("target").join("neg-tests");
    std::fs::create_dir_all(&tmp).unwrap();
    let f = tmp.join(format!("{tag}.json"));
    std::fs::write(&f, serde_json::to_vec(cert).unwrap()).unwrap();
    let tc = tree_check_path();
    assert!(Path::new(&tc).exists(), "build tree-check first: {}", tc.display());
    Command::new(tc).arg("verify").arg(&f).output().unwrap().status.code().unwrap()
}

#[test]
fn negatives_honest_corpus_accepts_with_count_two() {
    let o = corpus_cert(&records(), &query());
    assert_eq!(o.count, 2);
    assert_eq!(o.matching, vec![2, 3]);
    assert_eq!(verify(&o.cert, "honest"), 0);
}

#[test]
fn negatives_tampered_count_refused() {
    for (d, tag) in [(1i64, "count-plus"), (-1, "count-minus")] {
        let mut c = corpus_cert(&records(), &query()).cert;
        let n = c["statement"]["count"].as_i64().unwrap() + d;
        c["statement"]["count"] = n.into();
        assert_eq!(verify(&c, tag), 1, "{tag}");
    }
}

#[test]
fn negatives_swapped_record_order_refused() {
    let mut c = corpus_cert(&records(), &query()).cert;
    c["receipt"]["records"].as_array_mut().unwrap().swap(0, 1);
    assert_eq!(verify(&c, "swap"), 1);
    // and the honest certificate of the swapped corpus has a different MMR root
    let mut rs = records();
    rs.swap(0, 1);
    let o = corpus_cert(&rs, &query());
    assert_ne!(o.cert["statement"]["mmr_root"], corpus_cert(&records(), &query()).cert["statement"]["mmr_root"]);
    assert_eq!(verify(&o.cert, "swap-honest"), 0);
}

#[test]
fn negatives_refutation_opening_at_wrong_path_refused() {
    let rs = records();
    let mut c = corpus_cert(&rs, &query()).cert;
    // record 0 (Read) is refuted at conjunct 0 (`name`); open `input` instead
    let wrong = opening_json(&open_at(&rs[0], &[Step::Key(b"input".to_vec())]));
    c["receipt"]["records"][0]["refute"]["opening"] = wrong;
    assert_eq!(verify(&c, "wrong-path"), 1);
    // a refutation that in fact accepts (record 3 matches) is refused too
    let mut c = corpus_cert(&rs, &query()).cert;
    let op = opening_json(&open_at(&rs[3], &query()[1].path));
    c["receipt"]["records"][3] = serde_json::json!({ "root": c["receipt"]["records"][3]["root"],
        "refute": { "j": 1, "opening": op } });
    c["statement"]["count"] = 1.into();
    assert_eq!(verify(&c, "false-refute"), 1);
}

#[test]
fn negatives_table_digest_swap_refused() {
    let mut c = corpus_cert(&records(), &query()).cert;
    let q = c["statement"]["query"].as_array_mut().unwrap();
    let (a, b) = (q[0]["table_digest"].clone(), q[1]["table_digest"].clone());
    q[0]["table_digest"] = b;
    q[1]["table_digest"] = a;
    assert_eq!(verify(&c, "table-swap"), 1);
}

#[test]
fn negatives_field_and_schema_certificates() {
    let rs = records();
    let t = table("pkill.json");
    let p = query()[1].path.clone();
    for (i, want) in [(1usize, "reject"), (2, "accept"), (4, "absent"), (5, "non_string")] {
        let (v, mut c) = field_cert(&rs[i], &p, &t);
        assert_eq!(v.as_str(), want);
        assert_eq!(verify(&c, &format!("field-{i}")), 0);
        c["statement"]["verdict"] = if want == "accept" { "reject" } else { "accept" }.into();
        assert_eq!(verify(&c, &format!("field-{i}-flip")), 1);
    }
    let schema = rec(&std::fs::read(dir().join("schema-bash-call.json")).unwrap());
    for (i, want) in [(0usize, false), (1, true), (4, false)] {
        let (v, mut c) = schema_cert(&rs[i], &schema).unwrap();
        assert_eq!(v, want, "record {i}");
        assert_eq!(verify(&c, &format!("schema-{i}")), 0);
        c["statement"]["verdict"] = (!want).into();
        assert_eq!(verify(&c, &format!("schema-{i}-flip")), 1);
    }
}

#[test]
fn negatives_flat_scan_misses_escaped_control() {
    let raw = b"{\"name\":\"Bash\",\"input\":{\"command\":\"\\u0070kill -f node\"}}";
    assert!(!raw.windows(8).any(|w| w == b"pkill -f"));
    let v = rec(raw);
    let leaf = tree_absence::merkle::lookup(&v, &query()[1].path);
    assert_eq!(leaf, Some(&JVal::Str(b"pkill -f node".to_vec())));
}

#[test]
fn negatives_invocation_tables_match_oracle_on_cases() {
    use tree_absence::invocation::{invocation_oracle, invocation_re, CASES};
    for (bt, file) in [(true, "invocation.json"), (false, "invocation-nobacktick.json")] {
        let d = invocation_re(bt).compile().minimize();
        let re = invocation_oracle(bt);
        let committed = table(file);
        for (c, wb, wc) in CASES {
            let want = if bt { *wb } else { *wc };
            assert_eq!(d.matches(c.as_bytes()), want, "{file} compiled on {c:?}");
            assert_eq!(re.is_match(c.as_bytes()), want, "{file} oracle on {c:?}");
            assert_eq!(committed.accepts(c.as_bytes()), want, "{file} committed on {c:?}");
        }
    }
}

/// A schema certificate built without the producer's schema reader (so a schema the reader
/// refuses still reaches tree-check): the run labels every node with `bits`.
fn raw_schema_cert(record: &JVal, schema: &JVal, bits: &str, verdict: bool) -> Value {
    use tree_absence::merkle::digest;
    use tree_absence::value::{encode, flat_digest, hex};
    fn run(v: &JVal, bits: &str) -> Value {
        match v {
            JVal::Arr(xs) => serde_json::json!({"q": bits, "kids": xs.iter().map(|c| run(c, bits)).collect::<Vec<_>>()}),
            JVal::Obj(kvs) => serde_json::json!({"q": bits, "kids": kvs.iter().map(|(_, c)| run(c, bits)).collect::<Vec<_>>()}),
            _ => serde_json::json!({"q": bits}),
        }
    }
    serde_json::json!({
        "statement": {"kind": "schema", "tree_root": hex(&digest(record)),
                      "schema_digest": hex(&flat_digest(schema)), "verdict": verdict},
        "receipt": {"tree": hex(&encode(record)), "schema": hex(&encode(schema)), "run": run(record, bits)},
    })
}

#[test]
fn negatives_schema_reader_repairs_agree_with_tree_check() {
    use tree_absence::schema::schema_of_jval;
    let r = rec(br#"{"name":"Bash","input":{"command":"ls"}}"#);
    // each schema is refused by the producer's reader; tree-check must refuse every certificate
    // over it, whatever verdict and run are claimed
    let refused: &[&[u8]] = &[
        br#"{"defs":[{"type":[]}],"root":0}"#,
        br#"{"defs":[{"enum":[]}],"root":0}"#,
        br#"{"defs":[{},{"allOf":[]}],"root":1}"#,
        br#"{"defs":[{},{"anyOf":[]}],"root":1}"#,
        br#"{"defs":[{"items":999}],"root":0}"#,
        br#"{"defs":[{"properties":{"name":7}}],"root":0}"#,
        br#"{"defs":[{"additionalProperties":3}],"root":0}"#,
        br#"{"defs":[{}],"root":0,"extra":1}"#,
        br#"{"defs":[{"pattern":0}],"root":0,"tables":[{"num_states":1,"transitions":[],"start":0,"accepting":[],"extra":1}]}"#,
    ];
    for (i, s) in refused.iter().enumerate() {
        let sch = rec(s);
        assert!(schema_of_jval(&sch).is_none(), "producer accepts schema {i}");
        for (bits, verdict) in [("0", false), ("1", true)] {
            let c = raw_schema_cert(&r, &sch, bits, verdict);
            assert_eq!(verify(&c, &format!("schema-refused-{i}-{bits}")), 1, "tree-check on schema {i}");
        }
    }
    // the same schemas without the defect are read by both sides
    let good = rec(br#"{"defs":[{"properties":{"name":0}}],"root":0}"#);
    let (v, c) = schema_cert(&r, &good).unwrap();
    assert!(v);
    assert_eq!(verify(&c, "schema-good"), 0);
}

#[test]
fn negatives_enum_refuses_every_non_string() {
    let sch = rec(br#"{"defs":[{"enum":["Bash"]}],"root":0}"#);
    for (i, t) in [&b"null"[..], b"true", b"1", b"1.5", b"[]", b"{}", br#"["Bash"]"#, br#""Bash""#, br#""ls""#]
        .iter()
        .enumerate()
    {
        let v = rec(t);
        let want = i == 7;
        let (got, mut c) = schema_cert(&v, &sch).unwrap();
        assert_eq!(got, want, "producer on {}", String::from_utf8_lossy(t));
        assert_eq!(verify(&c, &format!("enum-{i}")), 0, "honest enum cert {i}");
        c["statement"]["verdict"] = (!want).into();
        assert_eq!(verify(&c, &format!("enum-{i}-flip")), 1, "flipped enum cert {i}");
    }
}
