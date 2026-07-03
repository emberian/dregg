//! End-to-end exercise of the umem-heap convention THROUGH the public API — the
//! way `starbridge-execution-lease` and `starbridge-vat` will call it once wired
//! over (a deliberate follow-up; this lane lands the crate + its tests).
//!
//! The four teeth the mission pins: lay+open round-trips a record; checkpoint →
//! restore reproduces the boundary root; a tampered leaf fails `root_binds_get`;
//! fork gives an independent image.

use serde::{Deserialize, Serialize};

use dregg_cell::CellState;
use dregg_umem::{
    Checkpoint, RestoreError, Timeline, binds, boundary_root, fork, grow_set, lay_record,
    open_record, recompute_boundary_root, restore,
};

/// A worked example of the kind of record a consumer lays into its durable image:
/// a chunk of running-World working memory (a step cursor + a payload blob).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct WorkingMemory {
    step: u64,
    note: String,
}

fn wm(step: u64, note: &str) -> WorkingMemory {
    WorkingMemory {
        step,
        note: note.to_string(),
    }
}

/// The lease/vat "durable execution image" collection id — an arbitrary
/// caller-chosen collection (here mirroring the spirit of the reserved EXEC
/// collection: high, unlikely to collide with app records).
const IMAGE_COLL: u32 = 0x0000_E3EC;

#[test]
fn lay_open_round_trips_and_binds() {
    let mut cell = CellState::new(0);
    let rec = wm(3, "the running World, checkpointed");
    lay_record(&mut cell, IMAGE_COLL, &rec).unwrap();

    let back: WorkingMemory = open_record(&cell, IMAGE_COLL).unwrap();
    assert_eq!(back, rec);
    assert!(binds(&cell, IMAGE_COLL));
}

#[test]
fn checkpoint_restore_reproduces_the_boundary_root() {
    let mut cell = CellState::new(0);
    lay_record(&mut cell, IMAGE_COLL, &wm(1, "asleep")).unwrap();
    let cp = Checkpoint::capture(&cell);
    let root = cp.root();

    // Wake into a divergent working state.
    lay_record(&mut cell, IMAGE_COLL, &wm(2, "awake and mutated")).unwrap();
    assert_ne!(boundary_root(&cell), root);

    // Restore (a "wake" from the committed image): the boundary root is back.
    restore(&mut cell, &cp).unwrap();
    assert_eq!(boundary_root(&cell), root);
    assert_eq!(
        open_record::<WorkingMemory>(&cell, IMAGE_COLL).unwrap(),
        wm(1, "asleep")
    );
}

#[test]
fn tampered_leaf_fails_root_binds_get() {
    let mut cell = CellState::new(0);
    lay_record(&mut cell, IMAGE_COLL, &wm(7, "genuine")).unwrap();
    let sealed = boundary_root(&cell);

    // Tamper a payload leaf in the witness store without resealing.
    cell.heap_map.get_mut(&(IMAGE_COLL, 1)).unwrap()[0] ^= 0xff;

    assert_eq!(boundary_root(&cell), sealed, "sealed root untouched");
    assert_ne!(
        recompute_boundary_root(&cell),
        sealed,
        "heap diverged from its seal"
    );
    assert!(
        !binds(&cell, IMAGE_COLL),
        "root_binds_get refuses the tampered image"
    );
}

#[test]
fn fork_gives_an_independent_image_and_merges_free() {
    let mut parent = CellState::new(0);
    lay_record(&mut parent, 1, &wm(0, "base")).unwrap();
    let root0 = boundary_root(&parent);

    let mut child = fork(&parent);
    assert_eq!(boundary_root(&child), root0);

    // Diverge independently.
    lay_record(&mut child, 2, &wm(1, "child-only")).unwrap();
    lay_record(&mut parent, 3, &wm(1, "parent-only")).unwrap();
    assert_ne!(boundary_root(&child), boundary_root(&parent));
    assert_eq!(open_record::<WorkingMemory>(&parent, 2).ok(), None);

    // The two grow-only record-sets merge free by union (merge-readiness).
    use dregg_merge::MergeState;
    let gs_p = grow_set(&parent, "img");
    let gs_c = grow_set(&child, "img");
    let merged = gs_p.join(&gs_c);
    // base + parent-only + child-only = 3 survivors.
    assert_eq!(merged.survivors().count(), 3);
}

#[test]
fn timeline_time_travels_across_committed_roots() {
    let mut cell = CellState::new(0);
    let mut tl = Timeline::new();

    lay_record(&mut cell, IMAGE_COLL, &wm(1, "t1")).unwrap();
    let r1 = tl.checkpoint(&cell);
    lay_record(&mut cell, IMAGE_COLL, &wm(2, "t2")).unwrap();
    let r2 = tl.checkpoint(&cell);

    tl.time_travel(&mut cell, &r1).unwrap();
    assert_eq!(
        open_record::<WorkingMemory>(&cell, IMAGE_COLL).unwrap(),
        wm(1, "t1")
    );
    tl.time_travel(&mut cell, &r2).unwrap();
    assert_eq!(
        open_record::<WorkingMemory>(&cell, IMAGE_COLL).unwrap(),
        wm(2, "t2")
    );

    assert!(matches!(
        tl.time_travel(&mut cell, "deadbeef").unwrap_err(),
        RestoreError::UnknownRoot(_)
    ));
}
