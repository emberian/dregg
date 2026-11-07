//! `dregg-calltree` — initiative 9: a certified HTTPS call tree.
//!
//! This library PRODUCES what `metatheory/Dregg2/Lightclient/CallTreeDeploy.lean` checks: the
//! tree hash (`treeHash`), the byte digests (`digestBytes`) and the MMR children root
//! (`CallTreeCore.mrootC`, proved equal to `MMR.mroot`). Nothing here decides acceptance: the
//! verifier CLI hands the bundle to the Lean exe `calltree-check`, whose exit code is the verdict.
//! A producer that disagreed with the Lean definitions would make honest trees REJECT, never
//! make a forged one accept.

use serde::{Deserialize, Serialize};

/// A 256-bit value as Lean reads it: big-endian, an `Int` ≥ 0. `[0;32]` is `0`.
pub type D = [u8; 32];

pub const ZERO: D = [0u8; 32];

fn u32be(n: usize) -> [u8; 4] {
    (n as u32).to_be_bytes()
}

/// `CallTreeDeploy.encInt` for a non-negative value given as big-endian bytes.
fn enc_nat(be: &[u8], out: &mut Vec<u8>) {
    let start = be.iter().position(|b| *b != 0).unwrap_or(be.len());
    let m = &be[start..];
    out.push(0);
    out.extend_from_slice(&u32be(m.len()));
    out.extend_from_slice(m);
}

/// `CallTreeDeploy.treeHash` over a list of non-negative 256-bit values.
pub fn tree_hash(xs: &[D]) -> D {
    let mut buf = b"dregg-calltree-v1".to_vec();
    buf.extend_from_slice(&u32be(xs.len()));
    for x in xs {
        enc_nat(x, &mut buf);
    }
    *blake3::hash(&buf).as_bytes()
}

/// `CallTreeDeploy.digestBytes`.
pub fn digest_bytes(tag: &str, b: &[u8]) -> D {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-calltree-bytes-v1:");
    h.update(tag.as_bytes());
    h.update(&[0]);
    h.update(b);
    *h.finalize().as_bytes()
}

fn small(k: u64) -> D {
    let mut d = ZERO;
    d[24..].copy_from_slice(&k.to_be_bytes());
    d
}

/// `CallTreeCore.mrootC`: peaks are perfect trees, `push` carries, `bag` folds youngest-first.
pub fn mroot(leaves: &[D]) -> D {
    // peaks youngest-first: (height, hash)
    let mut peaks: Vec<(u32, D)> = Vec::new();
    for v in leaves {
        let mut t = (0u32, tree_hash(&[*v]));
        // push: while the youngest peak has t's height, merge (older on the left)
        loop {
            match peaks.first() {
                Some(&(h, s)) if h == t.0 => {
                    peaks.remove(0);
                    t = (t.0 + 1, tree_hash(&[s, t.1]));
                }
                _ => break,
            }
        }
        peaks.insert(0, t);
    }
    fn bag(ps: &[(u32, D)]) -> D {
        match ps.split_first() {
            None => tree_hash(&[]),
            Some((p, rest)) => tree_hash(&[p.1, bag(rest)]),
        }
    }
    bag(&peaks)
}

/// One node of the tree as the bundle carries it (hex digests, `"0"` for zero).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Node {
    pub kind: i64,
    pub att: String,
    pub host: String,
    pub req: String,
    pub resp: String,
    pub kids: Vec<Node>,
}

pub fn hexd(d: &D) -> String {
    if *d == ZERO {
        "0".to_string()
    } else {
        hex::encode(d)
    }
}

pub fn unhexd(s: &str) -> anyhow::Result<D> {
    if s == "0" {
        return Ok(ZERO);
    }
    let v = hex::decode(s)?;
    anyhow::ensure!(v.len() == 32, "digest is not 32 bytes");
    let mut d = ZERO;
    d.copy_from_slice(&v);
    Ok(d)
}

impl Node {
    pub fn kids_root(&self) -> anyhow::Result<D> {
        let cs = self
            .kids
            .iter()
            .map(|k| k.commit())
            .collect::<anyhow::Result<Vec<_>>>()?;
        Ok(mroot(&cs))
    }
    /// `CallTreeCore.commit`.
    pub fn commit(&self) -> anyhow::Result<D> {
        anyhow::ensure!(self.kind >= 0, "negative kind");
        Ok(tree_hash(&[
            small(self.kind as u64),
            unhexd(&self.att)?,
            unhexd(&self.host)?,
            unhexd(&self.req)?,
            unhexd(&self.resp)?,
            self.kids_root()?,
        ]))
    }
}

/// One attested hop as the recorder keeps it: the node fields come from these bytes.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Evidence {
    /// hex of the bincode `tlsn` presentation.
    pub presentation: String,
}

/// A dataflow edge: `bytes` occur in the authenticated response of the hop `from` and in the
/// authenticated request of the hop `to` (both named by `att`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Edge {
    /// 0: response of `from` → request of `to`; 1: response of `from` → response of `to`.
    pub kind: u8,
    pub from: String,
    pub to: String,
    pub bytes: String,
}

/// What the recorder emits and the verifier reads. No key material: the presentations carry
/// redacted headers as `X`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Recording {
    pub root: String,
    pub tree: Node,
    pub presentations: Vec<Evidence>,
    pub edges: Vec<Edge>,
    /// The operator of the notary whose key signed these hops (recorded so a different notary is
    /// a config change; the VERIFIER's policy is what pins a key).
    pub notary_operator: String,
    pub notary_key: String,
    /// The grain anchor: the committed grain turn-cell (serde of `dregg_cell::Cell`) whose
    /// ATTESTATION slot carries the root, and the grain's receipt log.
    pub grain_cell: serde_json::Value,
    pub grain_receipts: Vec<String>,
    /// Wall time per hop (ms), measured by the recorder.
    pub hop_ms: Vec<u64>,
}
