//! # dregg-umem — the reusable **umem-heap convention** over a dregg cell
//!
//! A dregg [`CellState`](dregg_cell::CellState) already carries a committed
//! `(collection, key) → value` **heap**, sealed to the kernel's real
//! sorted-Poseidon2 boundary root [`dregg_cell::compute_heap_root`] (the Rust
//! shadow of the Lean `Substrate.Heap.root`, pinned by `root_binds_get`). The
//! substrate does not need a *new* store; **the cell IS the heap.** What it lacked
//! was a small, shared *convention* for using that heap as a durable, passable,
//! witnessed **execution image** — laying records into it, sealing them to the
//! boundary root, and forking / checkpointing / restoring / time-travelling over
//! that root.
//!
//! That convention was, until this crate, **re-implemented inline** in two
//! places. `starbridge-execution-lease` lays a checkpoint cursor + a state digest
//! + working-memory keys into its reserved [`EXEC_COLL`](../starbridge_execution_lease)
//! heap collection and hand-rolls the advance/mirror; `starbridge-vat` layers a
//! sleep=checkpoint / wake=restore / fork lifecycle on top of the same heap. Both
//! want the SAME four verbs over the cell heap. This crate factors them out — a
//! port of a prior imperative wrapper's record-laying + time-travel logic onto our
//! native cells, so the boundary root is the kernel's real Poseidon2 root and not a
//! stand-in.
//!
//! ## The two future consumers (this lane does not refactor them)
//!
//! - [`starbridge-execution-lease`](../starbridge_execution_lease) — its `EXEC_COLL`
//!   durable execution image is exactly a laid umem record + a boundary root; its
//!   `advance_checkpoint` / `mirror_checkpoint` are [`Checkpoint::capture`] +
//!   [`restore`] over the cell heap.
//! - [`starbridge-vat`](../starbridge_vat) — a vat *is* a Dregg Computer: **sleep =
//!   [`Checkpoint::capture`]**, **wake = [`restore`]**, **fork =
//!   [`fork`]/[`fork_into`]** of the execution-image cell. The two-axis lifecycle
//!   stays the vat's; the durable image machinery is this crate's.
//!
//! Both can depend on `dregg-umem` instead of hand-rolling. Wiring them over is a
//! deliberate follow-up — this crate lands the convention + its tests first, so the
//! swap is a mechanical, separately-reviewable change.
//!
//! ## The laying convention
//!
//! A **record** occupies one heap collection `coll`. Its canonical bytes are laid
//! as length-delimited 32-byte leaves:
//!
//! ```text
//!   leaf (coll, 0) = byte length (u64 LE in the low 8 bytes)   ← the header
//!   leaf (coll, 1) = payload bytes [0..32]
//!   leaf (coll, 2) = payload bytes [32..64]
//!   …               (the last chunk is zero-padded to 32 bytes)
//! ```
//!
//! - [`lay`] clears the collection (so a shorter re-lay leaves no stale chunk),
//!   writes the header + chunks, and reseals the boundary root. [`lay_record`] is
//!   the serde-typed form.
//! - [`open`] / [`open_record`] reassemble the record FROM the heap — fail-closed
//!   ([`UmemError`]) if the header/chunks are inconsistent or the payload does not
//!   deserialize. `lay ∘ open` round-trips.
//! - [`boundary_root`] is the cell's sealed sorted-Poseidon2 heap root — the
//!   commitment a dregg light client understands.
//! - [`binds`] is the [`root_binds_get`](dregg_cell::CellState::heap_root_membership)
//!   tooth over a record: `true` iff the record's leaves re-derive the sealed
//!   boundary root. A tampered leaf (mutated without resealing) fails it.
//!
//! The length header binds the payload injectively: a one-byte change to either the
//! length or the content moves the boundary root; the `(collection, key)` heap
//! canonicalises leaf order, so insertion order does not. (`:= 0` vacuity is
//! forbidden — the kernel's [`compute_heap_root`](dregg_cell::compute_heap_root) is
//! the openable Poseidon2 tree, not an opaque sponge.)
//!
//! ## Fork / checkpoint / restore / time-travel — see [`checkpoint`]
//!
//! [`Checkpoint::capture`] reifies the cell's heap into an honest checkpoint (root
//! computed FROM the image); [`restore`] adopts a checkpoint's image into a cell,
//! **fail-closed** ([`RestoreError`]) if the image does not reproduce its committed
//! root; [`fork`] / [`fork_into`] copy the committed image into a second cell that
//! descends from the same root and diverges independently; [`Timeline`] keeps a log
//! of checkpoint roots for [`Timeline::time_travel`].
//!
//! ## Merge-readiness — see [`merge`]
//!
//! The heap leaf-set is grow-only, so the I-confluent [`dregg_merge`] runtime
//! applies unchanged: [`merge::grow_set`] gives a content-addressed
//! [`GrowSet`](dregg_merge::GrowSet) view of a cell's laid records, and two forks'
//! record-sets merge by set union — commutative, associative, idempotent,
//! order-independent — with no coordination.

#![forbid(unsafe_code)]

pub mod checkpoint;
pub mod merge;

pub use checkpoint::{Checkpoint, RestoreError, Timeline, fork, fork_into, restore};
pub use merge::grow_set;

use serde::Serialize;
use serde::de::DeserializeOwned;

use dregg_cell::CellState;

/// The leaf slot within a record's collection holding the record's byte length (a
/// little-endian `u64` in the low 8 bytes of the 32-byte header leaf). Payload
/// chunks occupy slots `1..`.
pub const LEN_SLOT: u32 = 0;

/// Bytes of record payload carried per heap leaf (a `FieldElement` is 32 bytes).
pub const CHUNK_BYTES: usize = 32;

/// Why a umem-heap operation failed. Every variant **fails closed** — a
/// reassembly that cannot faithfully reproduce the committed record is refused,
/// never served partial.
#[derive(Debug)]
pub enum UmemError {
    /// The record's collection has no header leaf at [`LEN_SLOT`] — nothing was
    /// laid there (or the header leaf was dropped).
    MissingHeader {
        /// The heap collection that was expected to carry a laid record.
        coll: u32,
    },
    /// A payload chunk the header's declared length requires is absent from the
    /// heap — a truncated laying, refused rather than reassembled short.
    MissingChunk {
        /// The record's heap collection.
        coll: u32,
        /// The (0-based) payload chunk index that was missing.
        chunk: usize,
    },
    /// The reassembled bytes did not deserialize into the requested record type
    /// (a corrupt or type-mismatched payload) — fail closed.
    Serde(serde_json::Error),
}

impl std::fmt::Display for UmemError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UmemError::MissingHeader { coll } => write!(
                f,
                "umem heap collection {coll} has no record header leaf (nothing laid there)"
            ),
            UmemError::MissingChunk { coll, chunk } => write!(
                f,
                "umem heap collection {coll} is missing payload chunk {chunk} \
                 (a truncated record — fail-closed)"
            ),
            UmemError::Serde(e) => write!(f, "umem record did not deserialize: {e}"),
        }
    }
}

impl std::error::Error for UmemError {}

impl From<serde_json::Error> for UmemError {
    fn from(e: serde_json::Error) -> Self {
        UmemError::Serde(e)
    }
}

/// **Lay** `bytes` into heap collection `coll` as length-delimited 32-byte leaves,
/// superseding any prior record in that collection (a shorter re-lay leaves no
/// stale chunk), and **reseal the boundary root** so the cell's committed heap
/// binds the record.
///
/// The leaves land in the cell's own `(collection, key) → value` heap — the same
/// heap [`compute_heap_root`](dregg_cell::compute_heap_root) folds into the
/// canonical state commitment — so what is laid here is durable, passable, and
/// witnessed with no separate store.
pub fn lay(state: &mut CellState, coll: u32, bytes: &[u8]) {
    // Clear any prior leaves in this collection so a shrunk record leaves no stale
    // chunk behind. `heap_map` is the prover-side witness store; we reseal below.
    state.heap_map.retain(|&(c, _), _| c != coll);

    // Header leaf: the payload byte length (LE u64 in the low 8 bytes).
    let mut header = [0u8; 32];
    header[..8].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
    state.heap_map.insert((coll, LEN_SLOT), header);

    // Payload chunks at slots 1.., the last zero-padded to a full 32-byte leaf.
    for (i, chunk) in bytes.chunks(CHUNK_BYTES).enumerate() {
        let mut leaf = [0u8; 32];
        leaf[..chunk.len()].copy_from_slice(chunk);
        state.heap_map.insert((coll, 1 + i as u32), leaf);
    }

    // Reseal ONCE (cheaper than resealing per `set_heap`): `heap_root` now binds
    // the whole laid record.
    state.reseal_heap_root();
}

/// **Lay** a serde-serialisable record into heap collection `coll` (its canonical
/// JSON bytes via [`lay`]). The typed front door both future consumers use to lay
/// a working-memory value / a registry record.
pub fn lay_record<R: Serialize>(
    state: &mut CellState,
    coll: u32,
    record: &R,
) -> Result<(), UmemError> {
    let json = serde_json::to_vec(record)?;
    lay(state, coll, &json);
    Ok(())
}

/// **Open** the raw record bytes laid into heap collection `coll` — the inverse of
/// [`lay`]. Fails closed ([`UmemError`]) if the header is missing or a declared
/// payload chunk is absent.
pub fn open(state: &CellState, coll: u32) -> Result<Vec<u8>, UmemError> {
    let header = state
        .get_heap(coll, LEN_SLOT)
        .ok_or(UmemError::MissingHeader { coll })?;
    let byte_len =
        u64::from_le_bytes(header[..8].try_into().expect("32-byte leaf has 8 bytes")) as usize;
    let n_chunks = byte_len.div_ceil(CHUNK_BYTES);
    let mut bytes = Vec::with_capacity(byte_len);
    for i in 0..n_chunks {
        let leaf = state
            .get_heap(coll, 1 + i as u32)
            .ok_or(UmemError::MissingChunk { coll, chunk: i })?;
        bytes.extend_from_slice(&leaf);
    }
    bytes.truncate(byte_len);
    Ok(bytes)
}

/// **Open** and deserialize the record laid into heap collection `coll` — the
/// inverse of [`lay_record`]. Fails closed on a truncated laying or a payload that
/// does not deserialize into `R`.
pub fn open_record<R: DeserializeOwned>(state: &CellState, coll: u32) -> Result<R, UmemError> {
    let bytes = open(state, coll)?;
    serde_json::from_slice(&bytes).map_err(UmemError::from)
}

/// The cell's **committed boundary root** — the kernel's real sorted-Poseidon2
/// [`compute_heap_root`](dregg_cell::compute_heap_root) over the cell heap, kept
/// sealed by [`lay`] / [`restore`] / [`fork`]. This 32-byte commitment is what a
/// dregg light client binds; [`boundary_root_hex`] is its 64-hex form.
pub fn boundary_root(state: &CellState) -> [u8; 32] {
    state.heap_root
}

/// [`boundary_root`] as a 64-hex string.
pub fn boundary_root_hex(state: &CellState) -> String {
    hex32(&state.heap_root)
}

/// Recompute the boundary root FROM the current heap leaves (not the sealed field)
/// — `compute_heap_root` over `heap_map`. Equal to [`boundary_root`] for a sealed
/// cell; the two differ exactly when a leaf was mutated without a reseal, which is
/// what [`binds`] detects.
pub fn recompute_boundary_root(state: &CellState) -> [u8; 32] {
    dregg_cell::compute_heap_root(&state.heap_map)
}

/// The [`root_binds_get`](dregg_cell::CellState::heap_root_membership) tooth over a
/// laid record: `true` iff the record's header leaf is present AND the heap
/// re-derives its **sealed** boundary root (so every leaf, in `coll` and out, is
/// genuinely committed). A leaf tampered in the witness store without a reseal
/// flips the recomputed root away from the sealed one and this returns `false` —
/// the fail-closed boundary check a served record is checked against.
pub fn binds(state: &CellState, coll: u32) -> bool {
    state.heap_root_membership(coll, LEN_SLOT).is_some()
}

/// Lower-hex a 32-byte root (32 bytes → 64 hex chars).
pub(crate) fn hex32(b: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(64);
    for x in b {
        let _ = write!(s, "{x:02x}");
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    struct Rec {
        id: String,
        val: u64,
        blob: String,
    }
    fn rec(id: &str, val: u64) -> Rec {
        Rec {
            id: id.to_string(),
            val,
            // Longer than one 32-byte chunk, to exercise multi-chunk laying.
            blob: format!("payload-{id}-{}", "x".repeat(50)),
        }
    }

    /// `lay ∘ open` round-trips a (multi-chunk) record, and the cell's heap binds
    /// the laid record to its sealed boundary root (the `root_binds_get` tooth).
    #[test]
    fn lay_open_round_trips_a_record() {
        let mut st = CellState::new(0);
        let coll = 7;
        let r = rec("alpha", 42);
        lay_record(&mut st, coll, &r).unwrap();

        // The record reassembles exactly from the cell heap.
        let back: Rec = open_record(&st, coll).unwrap();
        assert_eq!(back, r);

        // The boundary root binds it, and is sealed (== recomputed).
        assert!(binds(&st, coll));
        assert_eq!(boundary_root(&st), recompute_boundary_root(&st));
        assert_eq!(boundary_root_hex(&st).len(), 64);
    }

    /// A re-lay of the same collection SUPERSEDES (last-write-wins) and leaves no
    /// stale chunk even when the new record is shorter.
    #[test]
    fn relay_supersedes_with_no_stale_chunk() {
        let mut st = CellState::new(0);
        let coll = 3;
        lay_record(&mut st, coll, &rec("k", 1)).unwrap(); // long (multi-chunk)
        // A far shorter record: the tail chunks of the prior laying must be gone.
        lay(&mut st, coll, b"tiny");
        assert_eq!(open(&st, coll).unwrap(), b"tiny");
        // No leaf beyond the single payload chunk survives.
        assert_eq!(st.get_heap(coll, 2), None);
        assert!(binds(&st, coll));
    }

    /// An empty payload round-trips (header len 0, no chunks).
    #[test]
    fn empty_payload_round_trips() {
        let mut st = CellState::new(0);
        lay(&mut st, 1, b"");
        assert_eq!(open(&st, 1).unwrap(), Vec::<u8>::new());
    }

    /// A tampered leaf FAILS `root_binds_get`: mutating a leaf in the witness
    /// store WITHOUT resealing flips the recomputed root off the sealed one.
    #[test]
    fn tampered_leaf_fails_root_binds_get() {
        let mut st = CellState::new(0);
        let coll = 9;
        lay_record(&mut st, coll, &rec("x", 5)).unwrap();
        assert!(binds(&st, coll), "genuine record binds");
        let sealed = boundary_root(&st);

        // Tamper a payload leaf directly in the witness store, NOT via a reseal.
        let leaf = st.heap_map.get_mut(&(coll, 1)).unwrap();
        leaf[0] ^= 0xff;

        // The sealed root is unchanged, but the heap no longer re-derives it.
        assert_eq!(
            boundary_root(&st),
            sealed,
            "sealed root untouched by the tamper"
        );
        assert_ne!(
            recompute_boundary_root(&st),
            sealed,
            "the heap diverged from its seal"
        );
        assert!(
            !binds(&st, coll),
            "root_binds_get refuses the tampered record"
        );
    }

    /// A missing chunk / missing header fails closed.
    #[test]
    fn truncated_record_fails_closed() {
        let mut st = CellState::new(0);
        let coll = 4;
        lay_record(&mut st, coll, &rec("y", 9)).unwrap();
        // Drop a required payload chunk.
        st.heap_map.remove(&(coll, 1));
        match open(&st, coll) {
            Err(UmemError::MissingChunk { coll: c, .. }) => assert_eq!(c, coll),
            other => panic!("expected MissingChunk, got {other:?}"),
        }
        // A never-laid collection has no header.
        match open(&st, 999) {
            Err(UmemError::MissingHeader { coll: 999 }) => {}
            other => panic!("expected MissingHeader, got {other:?}"),
        }
    }

    /// The boundary root is content-sensitive AND order-independent: a one-byte
    /// change moves it; laying the same records in a different collection order
    /// does not (the `(coll,key)` heap canonicalises).
    #[test]
    fn boundary_root_is_injective_and_canonical() {
        let mut a = CellState::new(0);
        lay(&mut a, 1, b"one");
        lay(&mut a, 2, b"two");

        let mut b = CellState::new(0);
        lay(&mut b, 2, b"two"); // other order
        lay(&mut b, 1, b"one");
        assert_eq!(boundary_root(&a), boundary_root(&b), "order-independent");

        let mut c = CellState::new(0);
        lay(&mut c, 1, b"one");
        lay(&mut c, 2, b"tXo"); // one byte different
        assert_ne!(
            boundary_root(&a),
            boundary_root(&c),
            "a changed byte moves the root"
        );
    }
}
