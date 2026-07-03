//! Fork / checkpoint / restore / time-travel over a cell's umem heap.
//!
//! These are the "superpowers a JSON-lines log can never give" the substrate gets
//! **for free** because the cell heap is a committed, boundary-rooted image:
//!
//! - [`Checkpoint::capture`] reifies the cell's current heap into a checkpoint,
//!   with the boundary root computed **from** the image (an honest reify — a
//!   checkpoint built this way always [`Checkpoint::verify`]s).
//! - [`restore`] adopts a checkpoint's image into a cell's heap, **fail-closed**
//!   ([`RestoreError::RootMismatch`]) if the image does not reproduce its committed
//!   root — a wake never resumes from state that is not the genuine committed
//!   boundary (the `root_binds_get` discipline).
//! - [`fork`] / [`fork_into`] copy the committed heap image into a second cell:
//!   two divergent copies that descend from one boundary root and diverge
//!   independently as either side lays more records.
//! - [`Timeline`] keeps the log of committed roots so [`Timeline::time_travel`]
//!   restores the cell to an EARLIER committed root — "my state as of yesterday".
//!
//! `starbridge-vat` maps its Dregg-Computer lifecycle straight onto these:
//! **sleep = [`Checkpoint::capture`]**, **wake = [`restore`]**, **fork =
//! [`fork_into`]** of the execution-image cell.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use dregg_cell::{CellState, FieldElement, compute_heap_root};

use crate::hex32;

/// A captured checkpoint of a cell's umem heap: a committed boundary `root` and the
/// reified heap `leaves` that produced it.
///
/// The leaves are stored as a canonical (sorted) `((collection, key), value)` list
/// — the same durable shape a JSON snapshot persists (tuple keys, unlike a map,
/// serialise cleanly), so a consumer can persist a checkpoint verbatim. The
/// commitment (`root`) is the kernel's real sorted-Poseidon2
/// [`compute_heap_root`]; [`Checkpoint::verify`] recomputes it FROM the image, so a
/// tampered image (one that no longer folds to `root`) is caught.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Checkpoint {
    /// The committed boundary root (32 bytes) the reified image folds to.
    pub root: [u8; 32],
    /// The reified heap leaves, canonical `(collection, key)` order.
    leaves: Vec<((u32, u32), FieldElement)>,
}

impl Checkpoint {
    /// Reify `state`'s current heap into a checkpoint. The `root` is computed FROM
    /// the captured leaves (`compute_heap_root`), so [`verify`](Self::verify) is
    /// always `true` for a checkpoint built this way — the honest reify.
    pub fn capture(state: &CellState) -> Checkpoint {
        let leaves: Vec<((u32, u32), FieldElement)> =
            state.heap_map.iter().map(|(k, v)| (*k, *v)).collect();
        // Compute the root over the SAME leaves we store, so root == image.
        let image: BTreeMap<(u32, u32), FieldElement> = state.heap_map.clone();
        Checkpoint {
            root: compute_heap_root(&image),
            leaves,
        }
    }

    /// Rebuild the heap map from the reified leaves.
    fn image(&self) -> BTreeMap<(u32, u32), FieldElement> {
        self.leaves.iter().copied().collect()
    }

    /// **Re-witness** this checkpoint: recompute the boundary root of the reified
    /// image and check it reproduces the committed `root`. `false` for a tampered
    /// image — the fail-closed gate [`restore`] runs before adopting.
    pub fn verify(&self) -> bool {
        compute_heap_root(&self.image()) == self.root
    }

    /// The committed boundary root (32 bytes).
    pub fn root(&self) -> [u8; 32] {
        self.root
    }

    /// The committed boundary root as a 64-hex string (the timeline key).
    pub fn root_hex(&self) -> String {
        hex32(&self.root)
    }

    /// How many heap leaves the reified image carries.
    pub fn leaf_count(&self) -> usize {
        self.leaves.len()
    }
}

/// Why a [`restore`] / [`Timeline::time_travel`] refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RestoreError {
    /// The reified image does not reproduce its committed boundary root — the
    /// fail-closed gate: a restore never adopts an image that is not the genuine
    /// committed state.
    RootMismatch {
        /// The committed root the image was supposed to reproduce (hex).
        committed: String,
        /// The root the (tampered) image actually folds to (hex).
        reified: String,
    },
    /// No checkpoint for this boundary root exists in the timeline (a time-travel
    /// to a root this cell never committed).
    UnknownRoot(String),
}

impl std::fmt::Display for RestoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RestoreError::RootMismatch { committed, reified } => write!(
                f,
                "umem checkpoint image does not reproduce its committed boundary root \
                 (committed {committed}, reified {reified}): restore refused"
            ),
            RestoreError::UnknownRoot(root) => {
                write!(
                    f,
                    "no umem checkpoint for boundary root {root} in this timeline"
                )
            }
        }
    }
}

impl std::error::Error for RestoreError {}

/// **Restore** `state`'s heap from `cp`, verifying the reified image reproduces its
/// committed root BEFORE adopting it. Fail-closed: a checkpoint whose image no
/// longer folds to its `root` is refused ([`RestoreError::RootMismatch`]) and
/// `state` is left untouched. On success the cell's heap and its sealed boundary
/// root are exactly the checkpoint's (`boundary_root(state) == cp.root`).
pub fn restore(state: &mut CellState, cp: &Checkpoint) -> Result<(), RestoreError> {
    if !cp.verify() {
        return Err(RestoreError::RootMismatch {
            committed: hex32(&cp.root),
            reified: hex32(&compute_heap_root(&cp.image())),
        });
    }
    state.heap_map = cp.image();
    state.reseal_heap_root();
    Ok(())
}

/// **Fork** the committed umem heap image out of `src` into a FRESH independent
/// cell: a second cell whose heap is a byte-identical copy of `src`'s, sealed to
/// the same boundary root, that diverges independently as either side lays more
/// records. (The fresh cell carries only the heap image — the durable umem state —
/// not `src`'s balance/fields/economics; use [`fork_into`] to transplant the image
/// into a cell that keeps its own identity.)
pub fn fork(src: &CellState) -> CellState {
    let mut forked = CellState::new(0);
    fork_into(src, &mut forked);
    forked
}

/// **Fork** the committed umem heap image out of `src` INTO an existing `dst` cell,
/// overwriting `dst`'s heap with a copy of `src`'s and resealing `dst`'s boundary
/// root. `dst` keeps its own balance / fields / economics — this transplants only
/// the durable execution image. This is the vat-fork shape: a new lease cell (its
/// own identity + rent schedule) receives the parent's running-World image.
pub fn fork_into(src: &CellState, dst: &mut CellState) {
    dst.heap_map = src.heap_map.clone();
    dst.reseal_heap_root();
}

/// A **time-travel record**: the log of committed boundary roots a cell has
/// checkpointed, oldest first. Both consumers keep one to roll a cell back to an
/// earlier committed image (a vat's sleep history; a lease's checkpoint cursor
/// history). The leaves are retained WITH each root so a restore is fully offline.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Timeline {
    checkpoints: Vec<Checkpoint>,
}

impl Timeline {
    /// A fresh, empty timeline.
    pub fn new() -> Timeline {
        Timeline::default()
    }

    /// **Checkpoint** `state`'s current heap into the timeline and return its
    /// boundary root (hex). An identical trailing root is de-duped, so a
    /// checkpoint/checkpoint of an unchanged heap does not bloat the log while
    /// still guaranteeing the root is present for a later [`time_travel`](Self::time_travel).
    pub fn checkpoint(&mut self, state: &CellState) -> String {
        let cp = Checkpoint::capture(state);
        let root_hex = cp.root_hex();
        if self.checkpoints.last().map(|c| c.root) != Some(cp.root) {
            self.checkpoints.push(cp);
        }
        root_hex
    }

    /// Every committed boundary root (hex), oldest first.
    pub fn roots(&self) -> Vec<String> {
        self.checkpoints.iter().map(Checkpoint::root_hex).collect()
    }

    /// The most recently committed boundary root (hex), if any.
    pub fn latest_root(&self) -> Option<String> {
        self.checkpoints.last().map(Checkpoint::root_hex)
    }

    /// The number of retained checkpoints.
    pub fn len(&self) -> usize {
        self.checkpoints.len()
    }

    /// Whether the timeline holds no checkpoints.
    pub fn is_empty(&self) -> bool {
        self.checkpoints.is_empty()
    }

    /// **Time-travel** `state` to an earlier committed boundary `root_hex` from
    /// this timeline. A root this timeline never committed is refused
    /// ([`RestoreError::UnknownRoot`]); a committed one is re-witnessed
    /// (fail-closed) and adopted via [`restore`].
    pub fn time_travel(&self, state: &mut CellState, root_hex: &str) -> Result<(), RestoreError> {
        let cp = self
            .checkpoints
            .iter()
            .rev()
            .find(|c| c.root_hex() == root_hex)
            .ok_or_else(|| RestoreError::UnknownRoot(root_hex.to_string()))?;
        restore(state, cp)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{boundary_root, lay, open};

    /// checkpoint → mutate → restore reproduces the committed boundary root and
    /// the exact heap state.
    #[test]
    fn checkpoint_then_restore_reproduces_the_boundary_root() {
        let mut st = CellState::new(0);
        lay(&mut st, 1, b"session-alpha");
        lay(&mut st, 2, b"counter-7");
        let cp = Checkpoint::capture(&st);
        let root = cp.root;
        assert_eq!(
            boundary_root(&st),
            root,
            "an honest capture matches the sealed root"
        );
        assert!(cp.verify());

        // Diverge: overwrite one record, add another.
        lay(&mut st, 2, b"counter-99");
        lay(&mut st, 3, b"scratch");
        assert_ne!(
            boundary_root(&st),
            root,
            "state diverged from the checkpoint"
        );

        // Restore: the heap and the boundary root are back to the checkpoint.
        restore(&mut st, &cp).unwrap();
        assert_eq!(
            boundary_root(&st),
            root,
            "restore reproduces the committed boundary root"
        );
        assert_eq!(open(&st, 1).unwrap(), b"session-alpha");
        assert_eq!(open(&st, 2).unwrap(), b"counter-7");
        assert!(open(&st, 3).is_err(), "the post-checkpoint record is gone");
    }

    /// Restore is fail-closed: a checkpoint whose reified image no longer folds to
    /// its committed root is REFUSED, leaving the live cell untouched.
    #[test]
    fn restore_refuses_a_tampered_image() {
        let mut st = CellState::new(0);
        lay(&mut st, 1, b"genuine");
        let genuine = Checkpoint::capture(&st);

        // Forge a checkpoint: keep the committed root, but tamper the image.
        let mut forged = genuine.clone();
        forged.leaves[0].1[0] ^= 0xff;
        assert!(
            !forged.verify(),
            "the forged image does not fold to the committed root"
        );

        // The live cell is mutated; the refused restore must not touch it.
        lay(&mut st, 1, b"live-state");
        let live_root = boundary_root(&st);
        let err = restore(&mut st, &forged).unwrap_err();
        assert!(matches!(err, RestoreError::RootMismatch { .. }));
        assert_eq!(
            boundary_root(&st),
            live_root,
            "live cell untouched on a refused restore"
        );
        assert_eq!(open(&st, 1).unwrap(), b"live-state");
    }

    /// Fork gives an INDEPENDENT image: the fork starts at the parent's root, then
    /// each side diverges without touching the other.
    #[test]
    fn fork_gives_an_independent_image() {
        let mut parent = CellState::new(0);
        lay(&mut parent, 1, b"shared-base");
        let root0 = boundary_root(&parent);

        let mut child = fork(&parent);
        assert_eq!(
            boundary_root(&child),
            root0,
            "the fork starts at the parent's root"
        );
        assert_eq!(open(&child, 1).unwrap(), b"shared-base");

        // Diverge: the child lays a record the parent never sees, and vice-versa.
        lay(&mut child, 2, b"child-only");
        lay(&mut parent, 3, b"parent-only");
        assert!(open(&child, 2).is_ok() && open(&child, 3).is_err());
        assert!(open(&parent, 3).is_ok() && open(&parent, 2).is_err());
        assert_ne!(
            boundary_root(&child),
            boundary_root(&parent),
            "the two images diverged"
        );
    }

    /// `fork_into` transplants only the heap image, preserving the destination
    /// cell's own identity (balance/fields).
    #[test]
    fn fork_into_keeps_the_destination_identity() {
        let mut src = CellState::new(0);
        lay(&mut src, 1, b"image");

        let mut dst = CellState::new(500); // its own balance
        dst.set_field(0, [9u8; 32]); // its own field
        fork_into(&src, &mut dst);

        assert_eq!(
            boundary_root(&dst),
            boundary_root(&src),
            "dst adopts src's image root"
        );
        assert_eq!(open(&dst, 1).unwrap(), b"image");
        assert_eq!(dst.balance(), 500, "dst keeps its own balance");
        assert_eq!(
            dst.get_field(0),
            Some(&[9u8; 32]),
            "dst keeps its own field"
        );
    }

    /// Time-travel restores an EARLIER committed root and refuses an unknown one.
    #[test]
    fn timeline_time_travel_restores_an_earlier_root() {
        let mut st = CellState::new(0);
        let mut tl = Timeline::new();

        lay(&mut st, 1, b"v-one");
        let r1 = tl.checkpoint(&st); // "yesterday": only record 1

        lay(&mut st, 2, b"v-two");
        let r2 = tl.checkpoint(&st);
        assert_ne!(r1, r2);
        assert_eq!(tl.roots(), vec![r1.clone(), r2.clone()]);
        assert_eq!(tl.latest_root(), Some(r2.clone()));

        // Roll back to yesterday: record 2 is gone.
        tl.time_travel(&mut st, &r1).unwrap();
        assert_eq!(boundary_root(&st), Checkpoint::capture(&st).root);
        assert_eq!(boundary_root_hex_of(&st), r1);
        assert!(open(&st, 2).is_err());

        // Forward again to r2.
        tl.time_travel(&mut st, &r2).unwrap();
        assert_eq!(open(&st, 2).unwrap(), b"v-two");

        // An unknown root is refused.
        assert!(matches!(
            tl.time_travel(&mut st, "00").unwrap_err(),
            RestoreError::UnknownRoot(_)
        ));
    }

    fn boundary_root_hex_of(state: &CellState) -> String {
        crate::boundary_root_hex(state)
    }
}
