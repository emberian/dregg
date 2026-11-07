//! **VK-epoch nullifier-root FAITHFUL FILL — the Rust ghost mirrors the canonical Lean.**
//!
//! The R=24 rotated circuit binds the nullifier root as a FAITHFUL 8-felt group (limb 26 lane-0 ‖
//! completion limbs 68..=74, post REVOKED-ROOT flag day). These integration tests prove the Rust producers now fill all 8 lanes
//! from a genuine `CanonicalHeapTree8` node8 root (closing the vacuous zero-fill of 67..73 and the
//! lossy 1-felt `hash_bytes` at limb 26), that the cell/turn twins agree byte-for-byte, that the
//! empty default is the NATIVE empty root (not `[0u8; 32]`), and that distinct nullifier frontiers
//! publish distinct committed roots (the cross-node anti-replay property).
//!
//! Lives as an INTEGRATION test (links the green `dregg-turn` lib + public API) so it runs
//! independently of unrelated in-flight breakage in the crate's `#[cfg(test)]` unit modules.

use dregg_cell::commitment::{V9RotationContext, compute_rotated_pre_limbs};
use dregg_cell::note::Nullifier;
use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell::{Cell, Ledger};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{HeapLeaf, compute_canonical_heap_root_8, empty_heap_root_8};
use dregg_turn::rotation_witness::{
    cells_root, empty_nullifier_root_8, iroot8, produce, produce_in_ctx, wire_commit_8,
};

/// (a) A non-empty nullifier accumulator root fills ALL 8 rotated lanes — limb 26 = root lane 0,
/// limbs 68..=74 = root lanes 1..7 (NON-ZERO, closing the vacuous zero-fill).
///
/// ⚠ **(b) WAS "THE TWO PRODUCERS AGREE" AND IS NOW AN IDENTITY.** Since 2026-08-07
/// `rotation_witness::produce` DELEGATES to `produce_in_ctx` → `commitment::compute_rotated_pre_limbs`
/// — one body, not two — so the per-lane equality below compares a function with itself. It is kept
/// because the LANE POSITIONS `[26, 68..=74]` are the real content; the twin claim is retired here
/// rather than left standing as a name for something that stopped being true.
///
/// ⚑ AND THE CONTEXT USED TO BE ASYMMETRIC: `produce` was handed `empty_commitments_root_8()` while
/// the hand-built context beside it wrote `heap_root::empty_heap_root_8()` into `commitments_root`
/// — two different created-note sets, invisible only because every assertion here is scoped to the
/// nullifier lanes. `produce_in_ctx` takes the context instead of assembling one, so both sides now
/// read the same object and there is nothing left to disagree.
#[test]
fn nullifier_root_fills_all_8_lanes_at_the_emitted_positions() {
    // A non-empty accumulator root (one spent nullifier leaf) — a genuine node8 tree root, the SAME
    // representation `NullifierSet::root8` yields for a live (nf, value) map.
    let nf_root = compute_canonical_heap_root_8(vec![HeapLeaf::entry(
        BabyBear::new(1_500_000_000),
        BabyBear::new(1),
    )]);
    assert!(
        nf_root.limbs()[1..8].iter().any(|f| *f != BabyBear::ZERO),
        "the test fixture must be a NON-empty (non-zero-completion) accumulator root"
    );

    let mut ledger = Ledger::new();
    let cell = Cell::with_balance([9u8; 32], [0u8; 32], 4242);
    ledger.insert_cell(cell.clone()).unwrap();
    let receipts: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    // ONE context, built once and read by both calls — not two assemblies that agreed on the slot
    // this test happens to look at.
    let ctx = V9RotationContext {
        cells_root: cells_root(&ledger),
        nullifier_root: nf_root,
        commitments_root: dregg_turn::rotation_witness::empty_commitments_root_8(),
        revoked_root: dregg_turn::rotation_witness::empty_revoked_root_8(),
        iroot: iroot8(&receipts),
        material: Default::default(),
    };
    let w = produce_in_ctx(&cell, &ctx);
    let pre_cell = compute_rotated_pre_limbs(&cell, &ctx);

    let lanes = [26usize, 68, 69, 70, 71, 72, 73, 74];
    for (i, &pos) in lanes.iter().enumerate() {
        assert_eq!(
            w.pre_limbs[pos],
            nf_root.limbs()[i],
            "turn producer limb {pos} must carry nullifier-root lane {i}"
        );
        // ⚠ AN IDENTITY since `produce` began delegating — see the test doc. What it pins is the
        // POSITION, not an agreement between two bodies.
        assert_eq!(
            w.pre_limbs[pos], pre_cell[pos],
            "nullifier lane {i} must ride limb {pos}"
        );
    }
    // (a) The completion lanes 68..74 are NON-ZERO (the vacuity closure). Post the REVOKED-ROOT
    // flag day the nullifier completion shifted 67..73 → 68..74 (limb 67 is now a completion lane
    // of another root); the write positions track `rotation_witness::produce` /
    // `commitment::compute_rotated_pre_limbs` at `[26, 68..=74]`.
    assert!(
        (68..=74).any(|pos| w.pre_limbs[pos] != BabyBear::ZERO),
        "rotated nullifier completion limbs 68..74 must be NON-ZERO for a non-empty accumulator"
    );
}

/// (c) A non-spend turn commits the accumulator's OWN empty default, NOT `[0u8; 32]` and NOT a
/// second computation of it: the empty-frontier fill writes limbs [26,68..74] as
/// `empty_nullifier_root_8()`'s 8 felts, and limb 26 DIFFERS from the OLD lossy
/// `hash_bytes(&[0u8; 32])` — the committed value genuinely SHIFTED.
///
/// ⚑ 2026-07-31: the empty default is no longer `empty_heap_root_8()`. Both note accumulators
/// left the arity-3 `CanonicalHeapTree8` leaf for the exact tagged linked leaf
/// (`dom ‖ addr17 ‖ value4 ‖ next17`), so the empty accumulator is the lone
/// `BOT(value=0, next=TOP)` sentinel under the `FNI2` domain. That it is NOT the heap-tree empty
/// root is asserted rather than assumed, so a silent revert reds here.
#[test]
fn non_spend_turn_commits_the_accumulator_empty_default_not_zero_bytes() {
    let empty = empty_nullifier_root_8();
    assert_eq!(
        empty,
        NullifierSet::new().root8(),
        "the empty default must BE a fresh accumulator's committed root, not a re-derivation"
    );
    assert_ne!(
        empty,
        empty_heap_root_8(),
        "and it is no longer the legacy CanonicalHeapTree8 empty root"
    );

    let mut ledger = Ledger::new();
    let cell = Cell::with_balance([3u8; 32], [0u8; 32], 100);
    ledger.insert_cell(cell.clone()).unwrap();
    let w = produce(
        &cell,
        &ledger,
        &empty,
        &dregg_turn::rotation_witness::empty_commitments_root_8(),
        &empty_heap_root_8(),
        &[[1u8; 32]],
        &Default::default(),
    );
    let lanes = [26usize, 68, 69, 70, 71, 72, 73, 74];
    for (i, &pos) in lanes.iter().enumerate() {
        assert_eq!(
            w.pre_limbs[pos],
            empty.limbs()[i],
            "empty-frontier limb {pos} must carry the native empty-root lane {i}"
        );
    }
    assert_ne!(
        w.pre_limbs[26],
        dregg_circuit::poseidon2::hash_bytes(&[0u8; 32]),
        "limb 26 must NOT be the OLD lossy hash_bytes([0u8;32]) — the committed value shifted"
    );
}

/// (d) CROSS-NODE ANTI-REPLAY: two DIFFERENT nullifier sets ⇒ DIFFERENT committed roots. The
/// executor's live `NullifierSet::root8()` frontier flows into the committed `nullifier_root`, so two
/// nodes whose (nf, value) frontiers differ publish DIFFERENT 8-felt turn commits.
#[test]
fn different_nullifier_sets_yield_different_committed_roots() {
    let mut set_a = NullifierSet::new();
    set_a.insert(Nullifier([7u8; 32]), 1_000).unwrap();
    let mut set_b = NullifierSet::new();
    set_b.insert(Nullifier([9u8; 32]), 2_000).unwrap();
    let root_a = set_a.root8();
    let root_b = set_b.root8();
    assert_ne!(
        root_a, root_b,
        "distinct nullifier frontiers must have distinct node8 roots"
    );

    let mut ledger = Ledger::new();
    let cell = Cell::with_balance([4u8; 32], [0u8; 32], 500);
    ledger.insert_cell(cell.clone()).unwrap();
    let receipts: Vec<[u8; 32]> = vec![[5u8; 32]];

    let commit = |root: &dregg_circuit::Faithful8| {
        let w = produce(
            &cell,
            &ledger,
            root,
            &dregg_turn::rotation_witness::empty_commitments_root_8(),
            &empty_heap_root_8(),
            &receipts,
            &Default::default(),
        );
        wire_commit_8(&w.pre_limbs, iroot8(&receipts).limbs()[0])
    };
    assert_ne!(
        commit(&root_a),
        commit(&root_b),
        "two executors with DIFFERENT nullifier frontiers must publish DIFFERENT committed roots"
    );
}
