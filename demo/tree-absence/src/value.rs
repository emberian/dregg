//! The value model of `Dregg2.Tree.Value` and its canonical CBOR (RFC 8949 §4.2.1), byte for byte.
//!
//! `JVal` mirrors the Lean `JVal`; `encode` mirrors `Value.encode` (= `Cbor.enc ∘ toItem`). The
//! three hashes are those of FORMAT.md: node `H`, flat `F`, mmr `h`.

use num_bigint::{BigInt, Sign};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use std::cmp::Ordering;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JVal {
    Null,
    Bool(bool),
    Int(BigInt),
    /// `m · 10^e`, `e < 0`, `10 ∤ m`.
    Dec(BigInt, i64),
    Str(Vec<u8>),
    Arr(Vec<JVal>),
    /// Entries in canonical order (strictly increasing `key_cmp`).
    Obj(Vec<(Vec<u8>, JVal)>),
}

/// The shortest head for major type `m` and argument `n` (`Cbor.head`).
pub fn head(out: &mut Vec<u8>, m: u8, n: u64) {
    let ib = m << 5;
    if n < 24 {
        out.push(ib | n as u8);
    } else if n < 1 << 8 {
        out.push(ib | 24);
        out.push(n as u8);
    } else if n < 1 << 16 {
        out.push(ib | 25);
        out.extend_from_slice(&(n as u16).to_be_bytes());
    } else if n < 1 << 32 {
        out.push(ib | 26);
        out.extend_from_slice(&(n as u32).to_be_bytes());
    } else {
        out.push(ib | 27);
        out.extend_from_slice(&n.to_be_bytes());
    }
}

/// `Value.intItem`, encoded: major 0/1 within 64 bits, bignum tag 2/3 (minimal bytes) beyond.
pub fn enc_int(out: &mut Vec<u8>, n: &BigInt) {
    if n.sign() != Sign::Minus {
        match u64::try_from(n) {
            Ok(x) => head(out, 0, x),
            Err(_) => {
                let (_, b) = n.to_bytes_be();
                head(out, 6, 2);
                head(out, 2, b.len() as u64);
                out.extend_from_slice(&b);
            }
        }
    } else {
        let k: BigInt = BigInt::from(-1) - n;
        match u64::try_from(&k) {
            Ok(x) => head(out, 1, x),
            Err(_) => {
                let (_, b) = k.to_bytes_be();
                head(out, 6, 3);
                head(out, 2, b.len() as u64);
                out.extend_from_slice(&b);
            }
        }
    }
}

pub fn enc_text(out: &mut Vec<u8>, s: &[u8]) {
    head(out, 3, s.len() as u64);
    out.extend_from_slice(s);
}

pub fn enc_bytes(out: &mut Vec<u8>, s: &[u8]) {
    head(out, 2, s.len() as u64);
    out.extend_from_slice(s);
}

/// `Value.encode` (`enc (toItem v)`).
pub fn encode_into(out: &mut Vec<u8>, v: &JVal) {
    match v {
        JVal::Null => head(out, 7, 22),
        JVal::Bool(false) => head(out, 7, 20),
        JVal::Bool(true) => head(out, 7, 21),
        JVal::Int(n) => enc_int(out, n),
        JVal::Dec(m, e) => {
            head(out, 6, 4);
            head(out, 4, 2);
            enc_int(out, &BigInt::from(*e));
            enc_int(out, m);
        }
        JVal::Str(s) => enc_text(out, s),
        JVal::Arr(xs) => {
            head(out, 4, xs.len() as u64);
            for x in xs {
                encode_into(out, x);
            }
        }
        JVal::Obj(kvs) => {
            head(out, 5, kvs.len() as u64);
            for (k, x) in kvs {
                enc_text(out, k);
                encode_into(out, x);
            }
        }
    }
}

pub fn encode(v: &JVal) -> Vec<u8> {
    let mut out = Vec::new();
    encode_into(&mut out, v);
    out
}

/// The map-key order of RFC 8949 §4.2.1 (`Value.keyLt`): bytewise on the encoded keys.
pub fn key_cmp(a: &[u8], b: &[u8]) -> Ordering {
    let mut ea = Vec::with_capacity(a.len() + 9);
    let mut eb = Vec::with_capacity(b.len() + 9);
    enc_text(&mut ea, a);
    enc_text(&mut eb, b);
    ea.cmp(&eb)
}

/// Sort entries canonically; `None` on a duplicate key (`Json.mkObj`).
pub fn canonical_obj(mut kvs: Vec<(Vec<u8>, JVal)>) -> Option<JVal> {
    kvs.sort_by(|x, y| key_cmp(&x.0, &y.0));
    for w in kvs.windows(2) {
        if w[0].0 == w[1].0 {
            return None;
        }
    }
    Some(JVal::Obj(kvs))
}

pub fn shake(domain: &str, x: &[u8]) -> [u8; 32] {
    let mut h = sha3::Shake256::default();
    h.update(domain.as_bytes());
    h.update(&[0]);
    h.update(x);
    let mut out = [0u8; 32];
    h.finalize_xof().read(&mut out);
    out
}

/// Node hash `H` (`Merkle.shakeH`).
pub fn node_h(frame: &[u8]) -> [u8; 32] {
    shake("dregg.tree.node.v1", frame)
}

/// Flat digest `F (encode v)` (`Cert.flatDigest` at `Instance.flatF`).
pub fn flat_digest(v: &JVal) -> [u8; 32] {
    shake("dregg.tree.flat.v1", &encode(v))
}

/// MMR hash `h` (`Instance.mmrHash`): `int_be(SHAKE256(... ‖ enc(arr(map intItem l))))`.
pub fn mmr_hash(l: &[BigInt]) -> BigInt {
    let mut x = Vec::new();
    head(&mut x, 4, l.len() as u64);
    for n in l {
        enc_int(&mut x, n);
    }
    BigInt::from_bytes_be(Sign::Plus, &shake("dregg.tree.mmr.v1", &x))
}

pub fn hex(b: &[u8]) -> String {
    hex::encode(b)
}
