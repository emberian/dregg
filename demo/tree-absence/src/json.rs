//! The projection from JSON text bytes to the model: a step-for-step mirror of
//! `Dregg2.Tree.Json.parse` (metatheory/Dregg2/Tree/Json.lean). `tree-cert conform` checks the
//! mirror against `tree-check project` record by record; where they differ, Lean is right.
//!
//! Strict RFC 8259 over bytes; numbers exact (`mk_num`, written exponent magnitude at most
//! `EXP_CAP`); escapes decoded, surrogate pairs combined, lone surrogates refused, raw bytes below
//! 0x20 refused, decoded strings valid UTF-8; duplicate keys (after decoding) refused; entries
//! sorted by the RFC 8949 §4.2.1 key order.

use crate::value::{canonical_obj, JVal};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};

/// `Json.expCap`.
pub const EXP_CAP: u64 = 4096;

/// `Json.mkNum`: the canonical number for `m · 10^e`.
pub fn mk_num(m: BigInt, e: i64) -> JVal {
    if m.is_zero() {
        return JVal::Int(BigInt::zero());
    }
    let ten = BigInt::from(10);
    let (mut m, mut e) = (m, e);
    while e < 0 && (&m % &ten).is_zero() {
        m /= &ten;
        e += 1;
    }
    if e >= 0 {
        JVal::Int(m * num_traits::pow(ten, e as usize))
    } else {
        JVal::Dec(m, e)
    }
}

struct P<'a> {
    b: &'a [u8],
    i: usize,
}

fn is_ws(c: u8) -> bool {
    matches!(c, 0x20 | 0x09 | 0x0A | 0x0D)
}

fn hex_val(c: u8) -> Option<u32> {
    match c {
        b'0'..=b'9' => Some((c - b'0') as u32),
        b'a'..=b'f' => Some((c - b'a' + 10) as u32),
        b'A'..=b'F' => Some((c - b'A' + 10) as u32),
        _ => None,
    }
}

impl<'a> P<'a> {
    fn ws(&mut self) {
        while self.i < self.b.len() && is_ws(self.b[self.i]) {
            self.i += 1;
        }
    }
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }
    fn rest(&self) -> &'a [u8] {
        &self.b[self.i..]
    }
    fn digits(&mut self) -> &'a [u8] {
        let s = self.i;
        while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
            self.i += 1;
        }
        &self.b[s..self.i]
    }

    fn value(&mut self) -> Option<JVal> {
        self.ws();
        let r = self.rest();
        if r.starts_with(b"null") {
            self.i += 4;
            return Some(JVal::Null);
        }
        if r.starts_with(b"true") {
            self.i += 4;
            return Some(JVal::Bool(true));
        }
        if r.starts_with(b"false") {
            self.i += 5;
            return Some(JVal::Bool(false));
        }
        match self.peek() {
            Some(b'"') => {
                self.i += 1;
                self.string().map(JVal::Str)
            }
            Some(b'[') => {
                self.i += 1;
                self.ws();
                if self.peek() == Some(b']') {
                    self.i += 1;
                    return Some(JVal::Arr(vec![]));
                }
                let mut xs = Vec::new();
                loop {
                    xs.push(self.value()?);
                    self.ws();
                    match self.peek() {
                        Some(b',') => self.i += 1,
                        Some(b']') => {
                            self.i += 1;
                            return Some(JVal::Arr(xs));
                        }
                        _ => return None,
                    }
                }
            }
            Some(b'{') => {
                self.i += 1;
                self.ws();
                if self.peek() == Some(b'}') {
                    self.i += 1;
                    return Some(JVal::Obj(vec![]));
                }
                let mut kvs = Vec::new();
                loop {
                    self.ws();
                    if self.peek() != Some(b'"') {
                        return None;
                    }
                    self.i += 1;
                    let k = self.string()?;
                    self.ws();
                    if self.peek() != Some(b':') {
                        return None;
                    }
                    self.i += 1;
                    let v = self.value()?;
                    kvs.push((k, v));
                    self.ws();
                    match self.peek() {
                        Some(b',') => self.i += 1,
                        Some(b'}') => {
                            self.i += 1;
                            return canonical_obj(kvs);
                        }
                        _ => return None,
                    }
                }
            }
            _ => self.number(),
        }
    }

    fn number(&mut self) -> Option<JVal> {
        let neg = self.peek() == Some(b'-');
        if neg {
            self.i += 1;
        }
        let ids = self.digits();
        if ids.is_empty() || (ids[0] == b'0' && ids.len() > 1) {
            return None;
        }
        let mut fs: &[u8] = &[];
        if self.peek() == Some(b'.') {
            self.i += 1;
            fs = self.digits();
            if fs.is_empty() {
                return None;
            }
        }
        let mut x: i64 = 0;
        if matches!(self.peek(), Some(b'e') | Some(b'E')) {
            self.i += 1;
            let eneg = match self.peek() {
                Some(b'+') => {
                    self.i += 1;
                    false
                }
                Some(b'-') => {
                    self.i += 1;
                    true
                }
                _ => false,
            };
            let es = self.digits();
            if es.is_empty() {
                return None;
            }
            let mut v: u64 = 0;
            for d in es {
                v = v.saturating_mul(10).saturating_add((d - b'0') as u64);
            }
            if v > EXP_CAP {
                return None;
            }
            x = if eneg { -(v as i64) } else { v as i64 };
        }
        let mut all = Vec::with_capacity(ids.len() + fs.len());
        all.extend_from_slice(ids);
        all.extend_from_slice(fs);
        let mag = BigInt::parse_bytes(&all, 10)?;
        let m = if neg { -mag } else { mag };
        Some(mk_num(m, x - fs.len() as i64))
    }

    /// After the opening quote.
    fn string(&mut self) -> Option<Vec<u8>> {
        let b = self.b;
        let mut out = Vec::new();
        loop {
            let c = *b.get(self.i)?;
            match c {
                b'"' => {
                    self.i += 1;
                    break;
                }
                b'\\' => {
                    if b.get(self.i + 1) == Some(&b'u') && self.i + 6 <= b.len() {
                        let u = hex4(&b[self.i + 2..self.i + 6])?;
                        self.i += 6;
                        if (0xD800..0xDC00).contains(&u) {
                            if self.i + 6 <= b.len() && b[self.i] == b'\\' && b[self.i + 1] == b'u' {
                                let l = hex4(&b[self.i + 2..self.i + 6])?;
                                if !(0xDC00..0xE000).contains(&l) {
                                    return None;
                                }
                                self.i += 6;
                                let cp = 0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00);
                                push_cp(&mut out, cp);
                            } else {
                                return None;
                            }
                        } else if (0xDC00..0xE000).contains(&u) {
                            return None;
                        } else {
                            push_cp(&mut out, u);
                        }
                    } else {
                        let e = *b.get(self.i + 1)?;
                        let x = match e {
                            b'"' => 0x22,
                            b'\\' => 0x5C,
                            b'/' => 0x2F,
                            b'b' => 0x08,
                            b'f' => 0x0C,
                            b'n' => 0x0A,
                            b'r' => 0x0D,
                            b't' => 0x09,
                            _ => return None,
                        };
                        out.push(x);
                        self.i += 2;
                    }
                }
                c if c < 0x20 => return None,
                c => {
                    out.push(c);
                    self.i += 1;
                }
            }
        }
        // `Value.utf8Valid` is RFC 3629 well-formedness, which is what `from_utf8` checks.
        std::str::from_utf8(&out).ok()?;
        Some(out)
    }
}

fn hex4(s: &[u8]) -> Option<u32> {
    let mut v = 0;
    for &c in s {
        v = v * 16 + hex_val(c)?;
    }
    Some(v)
}

fn push_cp(out: &mut Vec<u8>, cp: u32) {
    let ch = char::from_u32(cp).expect("callers pass scalar values");
    let mut buf = [0u8; 4];
    out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
}

/// `Json.parse`: one value, optional whitespace around it, nothing after.
pub fn parse(b: &[u8]) -> Option<JVal> {
    let mut p = P { b, i: 0 };
    let v = p.value()?;
    p.ws();
    if p.i == b.len() {
        Some(v)
    } else {
        None
    }
}

/// Integer view used by the schema reader (`Cert.asNat`).
pub fn as_nat(v: &JVal) -> Option<usize> {
    match v {
        JVal::Int(n) if !n.is_negative() => usize::try_from(n).ok(),
        _ => None,
    }
}
