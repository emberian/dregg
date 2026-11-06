//! Streaming receipts (initiative 11): the producer side of `lake exe stream-check`.
//!
//! The follower and the only acceptor is the Lean executable
//! (`metatheory/StreamCheck.lean`, deciding by `Dregg2.Stream.Policy.checkWindow`, the object
//! `Dregg2.Stream.Window.window_sound` / `windows_compose` are about). This module supplies what the
//! producer needs and nothing that decides acceptance:
//!
//! - [`ArityBlake3`]: an [`MmrHasher`] with the Lean model's domain separation exactly. The model
//!   (`Lightclient/MMR.lean`) separates empty / leaf / node by sponge ARITY (0 / 1 / 2) and bags
//!   with the same arity-2 call as a node; `StreamCheck.streamHash` instantiates that with
//!   `blake3("dregg-stream-v1:mmr:n" ‖ arity ‖ inputs)`. [`Blake3Mmr`](crate::mmr::Blake3Mmr) tags
//!   node and bag differently, so it computes a different root; this hasher computes the root the
//!   Lean follower computes, which is what lets the producer cross-check every receipt.
//! - [`entry_value`]: an entry's committed value, `blake3("dregg-stream-v1:entry" ‖ line)`.
//! - [`Frontier`]: the incremental peak frontier (the carry of `MMR.push`, amortized O(1) per
//!   append, O(log n) to bag). [`Mmr::root`](crate::mmr::Mmr::root) recomputes every subtree, O(n)
//!   per root; a live stream needs the frontier.

use crate::mmr::{MmrHasher, Peak, bag_peaks};

const MMR_TAG: &[u8] = b"dregg-stream-v1:mmr:n";
const ENTRY_TAG: &[u8] = b"dregg-stream-v1:entry";

/// The Lean model's arity-domain hash over blake3 (see the module docs).
#[derive(Clone, Copy, Debug, Default)]
pub struct ArityBlake3;

fn arity_hash(parts: &[&[u8; 32]]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(MMR_TAG);
    h.update(&[parts.len() as u8]);
    for p in parts {
        h.update(*p);
    }
    *h.finalize().as_bytes()
}

impl MmrHasher for ArityBlake3 {
    fn empty(&self) -> [u8; 32] {
        arity_hash(&[])
    }
    fn leaf(&self, v: &[u8; 32]) -> [u8; 32] {
        arity_hash(&[v])
    }
    fn node(&self, l: &[u8; 32], r: &[u8; 32]) -> [u8; 32] {
        arity_hash(&[l, r])
    }
    /// The model bags with `hash [peakHash, bagOfRest]`: the same arity-2 call as a node.
    fn bag(&self, peak: &[u8; 32], rest: &[u8; 32]) -> [u8; 32] {
        arity_hash(&[peak, rest])
    }
}

/// An entry's committed value: `blake3("dregg-stream-v1:entry" ‖ line)` (the line without its
/// newline).
pub fn entry_value(line: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(ENTRY_TAG);
    h.update(line);
    *h.finalize().as_bytes()
}

/// The incremental MMR frontier, oldest-first (the wire order of [`Peak`]).
#[derive(Clone, Debug)]
pub struct Frontier<H: MmrHasher> {
    hasher: H,
    peaks: Vec<Peak>,
    len: u64,
}

impl<H: MmrHasher> Frontier<H> {
    pub fn new(hasher: H) -> Self {
        Frontier {
            hasher,
            peaks: Vec::new(),
            len: 0,
        }
    }

    /// Append one value: a height-0 peak, then merge while the youngest peak has equal height
    /// (older peak on the left), exactly `MMR.push`.
    pub fn push(&mut self, v: &[u8; 32]) -> u64 {
        let mut cur = Peak {
            height: 0,
            hash: self.hasher.leaf(v),
        };
        while let Some(last) = self.peaks.last() {
            if last.height != cur.height {
                break;
            }
            let s = self.peaks.pop().expect("checked non-empty");
            cur = Peak {
                height: s.height + 1,
                hash: self.hasher.node(&s.hash, &cur.hash),
            };
        }
        self.peaks.push(cur);
        self.len += 1;
        self.len - 1
    }

    pub fn len(&self) -> u64 {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn peaks(&self) -> &[Peak] {
        &self.peaks
    }

    pub fn root(&self) -> [u8; 32] {
        bag_peaks(&self.hasher, &self.peaks)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mmr::{Blake3Mmr, Mmr, verify_range};

    fn v(i: u64) -> [u8; 32] {
        entry_value(&i.to_le_bytes())
    }

    /// The incremental frontier agrees with the recomputing reference at every length, under both
    /// hashers (peaks and root), and a range opened by the reference verifies against it.
    #[test]
    fn stream_frontier_matches_mmr() {
        for n in 0u64..=70 {
            let mut f = Frontier::new(ArityBlake3);
            let mut g = Frontier::new(Blake3Mmr);
            let mut m = Mmr::new(ArityBlake3);
            let mut mb = Mmr::new(Blake3Mmr);
            for i in 0..n {
                f.push(&v(i));
                g.push(&v(i));
                m.push(v(i));
                mb.push(v(i));
            }
            assert_eq!(f.peaks(), m.peaks().as_slice(), "peaks at n={n}");
            assert_eq!(f.root(), m.root(), "root at n={n}");
            assert_eq!(g.root(), mb.root(), "blake3mmr root at n={n}");
            if n > 0 {
                let (vals, op) = m.open_range(n / 2, n - 1);
                verify_range(&ArityBlake3, &f.root(), n / 2, n - 1, &vals, &op).unwrap();
            }
        }
    }

    /// The two hashers are different instantiations: equal logs, different roots.
    #[test]
    fn stream_hashers_differ() {
        let mut f = Frontier::new(ArityBlake3);
        let mut g = Frontier::new(Blake3Mmr);
        for i in 0..5 {
            f.push(&v(i));
            g.push(&v(i));
        }
        assert_ne!(f.root(), g.root());
    }
}
