//! Certificate producers (FORMAT.md): field, schema, corpus. The corpus MMR is
//! `Cert.mrootC` (the algorithm of `Lightclient/MMR.lean`: push / peaksOf / bag).

use crate::merkle::{digest, lookup, open_at, opening_json, path_json, Digest, Opening, Step};
use crate::schema::{schema_of_jval, Table};
use crate::value::{encode, flat_digest, hex, mmr_hash, JVal};
use num_bigint::{BigInt, Sign};
use serde_json::{json, Value};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Absent,
    NonString,
    Accept,
    Reject,
}

impl Verdict {
    pub fn as_str(self) -> &'static str {
        match self {
            Verdict::Absent => "absent",
            Verdict::NonString => "non_string",
            Verdict::Accept => "accept",
            Verdict::Reject => "reject",
        }
    }
}

/// `Cert.classify`.
pub fn classify(t: &Table, o: Option<&JVal>) -> Verdict {
    match o {
        None => Verdict::Absent,
        Some(JVal::Str(s)) => {
            if t.accepts(s) {
                Verdict::Accept
            } else {
                Verdict::Reject
            }
        }
        Some(_) => Verdict::NonString,
    }
}

pub fn field_cert(record: &JVal, path: &[Step], table: &Table) -> (Verdict, Value) {
    let tv = table.to_jval();
    let verdict = classify(table, lookup(record, path));
    let cert = json!({
        "statement": {
            "kind": "field",
            "tree_root": hex(&digest(record)),
            "path": path_json(path),
            "table_digest": hex(&flat_digest(&tv)),
            "verdict": verdict.as_str(),
        },
        "receipt": { "opening": opening_json(&open_at(record, path)), "table": hex(&encode(&tv)) },
    });
    (verdict, cert)
}

pub fn schema_cert(record: &JVal, schema: &JVal) -> Result<(bool, Value), String> {
    let s = schema_of_jval(schema).ok_or("schema: outside the regular core (Cert.schemaOfJVal refuses it)")?;
    let verdict = s.valid(record, s.root);
    let cert = json!({
        "statement": {
            "kind": "schema",
            "tree_root": hex(&digest(record)),
            "schema_digest": hex(&flat_digest(schema)),
            "verdict": verdict,
        },
        "receipt": { "tree": hex(&encode(record)), "schema": hex(&encode(schema)), "run": s.run(record) },
    });
    Ok((verdict, cert))
}

/// `Cert.mrootC`: peaks as (height, hash), newest first; bagged newest-first.
pub fn mroot(leaves: &[BigInt]) -> BigInt {
    let mut peaks: Vec<(usize, BigInt)> = Vec::new(); // index 0 = head of the Lean list
    for v in leaves {
        let mut t = (0usize, mmr_hash(std::slice::from_ref(v)));
        // pushC: merge with the head while heights agree.
        while let Some((h, _)) = peaks.first() {
            if *h == t.0 {
                let (h, s) = peaks.remove(0);
                t = (h + 1, mmr_hash(&[s, t.1]));
            } else {
                break;
            }
        }
        peaks.insert(0, t);
    }
    fn bag(ps: &[(usize, BigInt)]) -> BigInt {
        match ps.split_first() {
            None => mmr_hash(&[]),
            Some(((_, h), rest)) => mmr_hash(&[h.clone(), bag(rest)]),
        }
    }
    bag(&peaks)
}

pub fn leaf_of(d: &Digest) -> BigInt {
    BigInt::from_bytes_be(Sign::Plus, d)
}

/// 32 big-endian bytes (`Instance.intToHex32`).
pub fn root_hex32(n: &BigInt) -> String {
    let (_, b) = n.to_bytes_be();
    let mut out = vec![0u8; 32usize.saturating_sub(b.len())];
    out.extend_from_slice(&b[b.len().saturating_sub(32)..]);
    hex(&out)
}

pub struct Conjunct {
    pub path: Vec<Step>,
    pub table: Table,
}

pub struct CorpusOut {
    pub cert: Value,
    pub count: usize,
    pub refuted_at: Vec<usize>,
    pub mmr_root: String,
    pub matching: Vec<usize>,
}

/// Per record: `refute` at the FIRST conjunct whose verdict is not `accept` (so a non-Bash
/// record opens only `name`), else `full`.
pub fn corpus_cert(records: &[JVal], q: &[Conjunct]) -> CorpusOut {
    let tvals: Vec<JVal> = q.iter().map(|c| c.table.to_jval()).collect();
    let mut evs = Vec::with_capacity(records.len());
    let mut leaves = Vec::with_capacity(records.len());
    let mut refuted_at = vec![0usize; q.len()];
    let mut matching = Vec::new();
    for (i, r) in records.iter().enumerate() {
        let root = digest(r);
        leaves.push(leaf_of(&root));
        let fail = q.iter().position(|c| classify(&c.table, lookup(r, &c.path)) != Verdict::Accept);
        let ev = match fail {
            Some(j) => {
                refuted_at[j] += 1;
                json!({ "root": hex(&root), "refute": { "j": j, "opening": opening_json(&open_at(r, &q[j].path)) } })
            }
            None => {
                matching.push(i);
                let ops: Vec<Opening> = q.iter().map(|c| open_at(r, &c.path)).collect();
                json!({ "root": hex(&root), "full": ops.iter().map(opening_json).collect::<Vec<_>>() })
            }
        };
        evs.push(ev);
    }
    let root = root_hex32(&mroot(&leaves));
    let cert = json!({
        "statement": {
            "kind": "corpus",
            "mmr_root": root,
            "n": records.len(),
            "query": q.iter().zip(&tvals).map(|(c, tv)| json!({
                "path": path_json(&c.path), "table_digest": hex(&flat_digest(tv)) })).collect::<Vec<_>>(),
            "count": matching.len(),
        },
        "receipt": {
            "tables": tvals.iter().map(|tv| hex(&encode(tv))).collect::<Vec<_>>(),
            "records": evs,
        },
    });
    CorpusOut { cert, count: matching.len(), refuted_at, mmr_root: root, matching }
}
