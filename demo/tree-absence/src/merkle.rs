//! Merkle frames, digests and honest path openings: mirrors of `Merkle.digest`, `Value.lookup`
//! and `Merkle.openAt` (the opening `walk_openAt` proves `walk` accepts with the true value).

use crate::value::{enc_bytes, enc_text, encode, encode_into, head, hex, node_h, JVal};
use serde_json::{json, Value};

pub type Digest = [u8; 32];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    Key(Vec<u8>),
    Idx(usize),
}

pub fn frame_leaf(v: &JVal) -> Vec<u8> {
    let mut f = Vec::new();
    head(&mut f, 4, 2);
    head(&mut f, 0, 0);
    encode_into(&mut f, v);
    f
}

pub fn frame_arr(ds: &[Digest]) -> Vec<u8> {
    let mut f = Vec::new();
    head(&mut f, 4, 2);
    head(&mut f, 0, 1);
    head(&mut f, 4, ds.len() as u64);
    for d in ds {
        enc_bytes(&mut f, d);
    }
    f
}

pub fn frame_obj(es: &[(Vec<u8>, Digest)]) -> Vec<u8> {
    let mut f = Vec::new();
    head(&mut f, 4, 2);
    head(&mut f, 0, 2);
    head(&mut f, 5, es.len() as u64);
    for (k, d) in es {
        enc_text(&mut f, k);
        enc_bytes(&mut f, d);
    }
    f
}

pub fn digest(v: &JVal) -> Digest {
    match v {
        JVal::Arr(xs) => node_h(&frame_arr(&digests(xs))),
        JVal::Obj(kvs) => node_h(&frame_obj(&digest_kvs(kvs))),
        v => node_h(&frame_leaf(v)),
    }
}

pub fn digests(xs: &[JVal]) -> Vec<Digest> {
    xs.iter().map(digest).collect()
}

pub fn digest_kvs(kvs: &[(Vec<u8>, JVal)]) -> Vec<(Vec<u8>, Digest)> {
    kvs.iter().map(|(k, v)| (k.clone(), digest(v))).collect()
}

/// `Value.findKey`: the first entry with key `k`.
pub fn find_key<'a>(k: &[u8], kvs: &'a [(Vec<u8>, JVal)]) -> Option<&'a JVal> {
    kvs.iter().find(|(k2, _)| k2.as_slice() == k).map(|(_, v)| v)
}

/// `Value.lookup`.
pub fn lookup<'a>(v: &'a JVal, p: &[Step]) -> Option<&'a JVal> {
    match (v, p.split_first()) {
        (v, None) => Some(v),
        (JVal::Arr(xs), Some((Step::Idx(i), rest))) => lookup(xs.get(*i)?, rest),
        (JVal::Obj(kvs), Some((Step::Key(k), rest))) => lookup(find_key(k, kvs)?, rest),
        _ => None,
    }
}

#[derive(Clone, Debug)]
pub enum Opening {
    Here(JVal),
    Arr(Vec<Digest>, Box<Opening>),
    Obj(Vec<(Vec<u8>, Digest)>, Box<Opening>),
    AbsentArr(Vec<Digest>),
    AbsentObj(Vec<(Vec<u8>, Digest)>),
}

/// `Merkle.openAt`.
pub fn open_at(v: &JVal, p: &[Step]) -> Opening {
    match (v, p.split_first()) {
        (v, None) => Opening::Here(v.clone()),
        (JVal::Arr(xs), Some((Step::Idx(i), rest))) => match xs.get(*i) {
            Some(c) => Opening::Arr(digests(xs), Box::new(open_at(c, rest))),
            None => Opening::AbsentArr(digests(xs)),
        },
        (JVal::Arr(xs), Some((Step::Key(_), _))) => Opening::AbsentArr(digests(xs)),
        (JVal::Obj(kvs), Some((Step::Key(k), rest))) => match find_key(k, kvs) {
            Some(c) => Opening::Obj(digest_kvs(kvs), Box::new(open_at(c, rest))),
            None => Opening::AbsentObj(digest_kvs(kvs)),
        },
        (JVal::Obj(kvs), Some((Step::Idx(_), _))) => Opening::AbsentObj(digest_kvs(kvs)),
        (v, Some(_)) => Opening::Here(v.clone()),
    }
}

fn entries_json(es: &[(Vec<u8>, Digest)]) -> Value {
    Value::Array(es.iter().map(|(k, d)| json!([hex(k), hex(d)])).collect())
}

pub fn opening_json(o: &Opening) -> Value {
    match o {
        Opening::Here(v) => json!({ "here": hex(&encode(v)) }),
        Opening::Arr(ds, rest) => json!({
            "arr": ds.iter().map(|d| hex(d)).collect::<Vec<_>>(),
            "rest": opening_json(rest),
        }),
        Opening::Obj(es, rest) => json!({ "obj": entries_json(es), "rest": opening_json(rest) }),
        Opening::AbsentArr(ds) => json!({ "absent_arr": ds.iter().map(|d| hex(d)).collect::<Vec<_>>() }),
        Opening::AbsentObj(es) => json!({ "absent_obj": entries_json(es) }),
    }
}

pub fn path_json(p: &[Step]) -> Value {
    Value::Array(
        p.iter()
            .map(|s| match s {
                Step::Key(k) => json!({ "key": hex(k) }),
                Step::Idx(i) => json!({ "idx": i }),
            })
            .collect(),
    )
}

/// A path written as a JSON array of strings (keys) and naturals (indices).
pub fn path_of_json(v: &Value) -> Result<Vec<Step>, String> {
    let a = v.as_array().ok_or("path: want a JSON array")?;
    a.iter()
        .map(|s| match s {
            Value::String(k) => Ok(Step::Key(k.as_bytes().to_vec())),
            Value::Number(n) => n
                .as_u64()
                .map(|i| Step::Idx(i as usize))
                .ok_or_else(|| "path index: want a natural".to_string()),
            _ => Err("path step: want a string or a natural".to_string()),
        })
        .collect()
}
