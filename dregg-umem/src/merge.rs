//! The umem heap as a **grow-only set** — the merge-readiness bridge to
//! [`dregg_merge`].
//!
//! Laying records into a cell's `(collection, key) → value` heap only ever *adds*
//! leaves; the leaf-set is grow-only. That is exactly the shape the I-confluent
//! [`dregg_merge`] runtime merges coordination-free (`join = ∪`, commutative,
//! associative, idempotent, order-independent — the `top_iconfluent` /
//! `GrowSet::is_iconfluent_kind` polarity). So the substrate gets offchain
//! CRDT-merge over umem cells **for free**, with no new machinery: a cell's laid
//! records become a content-addressed [`GrowSet`], and two forks that each lay
//! their own records merge by set union.
//!
//! [`grow_set`] is the adapter. A record's identity is its **content** (the shared
//! `cell` id + the record's bytes), not which fork holds it, so two forks that
//! independently lay the byte-identical record produce the SAME delta and the union
//! deduplicates them (idempotence). Which fork contributed a delta is tracked by
//! the [`MergeReceipt`](dregg_merge::MergeReceipt)'s provenance, not the delta id.
//!
//! A *conserved* quantity (a single-writer register two forks wrote differently)
//! does NOT free-merge — reconciling it needs a non-monotone retraction, which the
//! gate escalates to a settling turn. That dichotomy is [`dregg_merge`]'s; this
//! module only supplies the grow-only view.

use std::collections::BTreeSet;

use dregg_merge::{Delta, GrowSet};

use dregg_cell::CellState;

use crate::{LEN_SLOT, open};

/// The content-addressed author every umem record delta carries. A record is
/// identified by its content, not its author — this fixed tag keeps two forks'
/// byte-identical records at the same delta id so the union deduplicates them.
const UMEM_AUTHOR: &str = "dregg-umem";

/// A content-addressed [`GrowSet`] view of the records laid into `state`'s heap on
/// the shared logical `cell` id: every laid collection (one with a header leaf at
/// [`LEN_SLOT`]) becomes one grow-only `Assert` delta carrying the record's bytes.
///
/// This is the CvRDT face of the umem heap's leaf-set. Two forks of a cell (a fork
/// and its parent, or two operators' copies) share one `cell` id; their `grow_set`
/// views merge by set union through the [`dregg_merge`] runtime — the offchain,
/// coordination-free write path, with a re-witnessable receipt and no chain op.
pub fn grow_set(state: &CellState, cell: &str) -> GrowSet {
    let mut gs = GrowSet::new(cell);
    for coll in laid_collections(state) {
        if let Ok(bytes) = open(state, coll) {
            gs.apply(Delta::assert(cell, bytes, UMEM_AUTHOR));
        }
    }
    gs
}

/// The distinct collections in `state`'s heap that look like a laid record — i.e.
/// carry a header leaf at [`LEN_SLOT`]. Sorted, deduplicated.
fn laid_collections(state: &CellState) -> Vec<u32> {
    state
        .heap_map
        .keys()
        .map(|(c, _)| *c)
        .collect::<BTreeSet<u32>>()
        .into_iter()
        .filter(|c| state.heap_map.contains_key(&(*c, LEN_SLOT)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{fork, lay};
    use dregg_merge::{MergeRuntime, MergeState, MergeVerdict, classify_merge};

    const CELL: &str = "umem-cell";
    const KIND: &str = "UmemCell";

    /// Two forks each lay a distinct record; the grow-only leaf-set is
    /// I-confluent, so the gate merges them FREE and the union carries both
    /// records.
    #[test]
    fn two_forks_merge_free_by_union() {
        let mut parent = CellState::new(0);
        lay(&mut parent, 1, b"shared-record");

        // Two independent forks, each laying its own new record offchain.
        let mut a = fork(&parent);
        let mut b = fork(&parent);
        lay(&mut a, 2, b"from-a");
        lay(&mut b, 3, b"from-b");

        let gs_a = grow_set(&a, CELL);
        let gs_b = grow_set(&b, CELL);

        // The gate finds the grow-only merge I-confluent.
        assert_eq!(classify_merge(&gs_a, &gs_b, KIND), MergeVerdict::Free);

        // The runtime performs it: the union carries the shared record + both new
        // ones (3 survivors), with a re-witnessable receipt.
        let mut rt = MergeRuntime::new(KIND, "a");
        let outcome = rt.merge(&gs_a, &gs_b).expect("grow-only merge is free");
        assert_eq!(
            outcome.state.survivors().count(),
            3,
            "union = shared + from-a + from-b"
        );
        assert_eq!(outcome.state.commitment(), gs_a.join(&gs_b).commitment());
    }

    /// The merge is order-independent and idempotent (the CvRDT laws), so merging
    /// the same views in either order — or twice — converges to one commitment.
    #[test]
    fn merge_is_order_independent_and_idempotent() {
        let mut a = CellState::new(0);
        lay(&mut a, 1, b"x");
        let mut b = fork(&a);
        lay(&mut a, 2, b"a-only");
        lay(&mut b, 3, b"b-only");

        let gs_a = grow_set(&a, CELL);
        let gs_b = grow_set(&b, CELL);

        let ab = gs_a.join(&gs_b);
        let ba = gs_b.join(&gs_a);
        assert_eq!(ab.commitment(), ba.commitment(), "join is commutative");
        assert_eq!(
            ab.join(&gs_a).commitment(),
            ab.commitment(),
            "join is idempotent"
        );
    }

    /// A grow-only umem leaf-set is statically I-confluent (the tier-1 gate).
    #[test]
    fn umem_leaf_set_is_iconfluent_kind() {
        assert!(GrowSet::is_iconfluent_kind());
    }
}
