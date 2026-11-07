//! **WOUND #23 FALSIFIER — the present-cell-set collision that DID and no longer DOES conflate the
//! deployed consensus anchor.**
//!
//! `docs/WOUND-felt-width-boundaries-2026-07-19.md` #23: `cells_root` was a ONE-felt (~31-bit)
//! sorted-heap existence fold over the WHOLE present-cell set, riding as a bare `BabyBear` at
//! `pre[0]` inside `compute_canonical_state_commitment_v9_felt8` — the faithful 8-felt chain the
//! executor signs as `pre_state_hash` / `post_state_hash` and the federation receipt QC aggregates
//! over. The completion lanes for a wide `cells_root` (limbs 169..=175) were already in the verified
//! layout (`RotatedLayout.rotated178`'s `.cells` group) and were ZERO in both producers, filled only
//! by the createCell trace generator. So on every non-birth turn the committed boundary view of the
//! ledger was one felt: two DIFFERENT present-cell sets colliding on that fold gave ONE signed
//! anchor for two different ledgers.
//!
//! This file is the falsification, in the exact both-polarity form the felt-width campaign requires:
//! a pair of present-cell sets that COLLIDE on the old lane-0 fold and are SEPARATED by the new
//! 8-felt group. Both polarities are asserted on the DEPLOYED entry points
//! (`state_commit::consensus_state_commitment` and `absent_cell_commitment`), against a verbatim
//! reconstruction of the pre-fix producer shape (lane 0 = the narrow fold, completion lanes zero).
//!
//! ## Why the pair is a baked-in fixture and not a live grind
//!
//! Finding it is a ~2^15.5 birthday search over BabyBear (`p < 2^31`) — cheap in absolute terms but
//! not a per-CI-run cost. [`search_cells_root_lane0_collision`] is the search that produced the
//! fixture, kept `#[ignore]`d and runnable (`cargo test -p dregg-turn --release --test
//! cells_root_width_falsification -- --ignored --nocapture`) so the fixture is reproducible rather
//! than asserted. That the search terminates in ~2^16 tries with ZERO chain interaction is itself
//! the price of the wound: `CellId::derive_raw` is BLAKE3 over attacker-chosen
//! `(public_key, token_id)`, so candidate ids are ground entirely offline.
//!
//! ## What this closed, and what a SECOND commit closed after it
//!
//! The widening makes the ROOT faithful at every intermediate (no ~31-bit waist anywhere in the
//! fold, so this is not `finalSqueezeOnly_still_conflates`). It did NOT widen the tree's KEYS: a
//! leaf address was `heap_addr(CELLS_COLLECTION, hash_bytes(id))`, one felt per 32-byte `CellId`,
//! so two ids whose key folds collided gave literally the SAME leaf at ANY root width — the
//! accumulator-KEY class (kind D: #5/#9/#11/#20). The search below therefore REFUSES a candidate
//! whose key collides with the anchor cell's, so the fixture here is a genuine ROOT collision over
//! distinct leaf sets and not a disguised key collision.
//!
//! ⚑ **THAT KEY CLASS WAS CLOSED SEPARATELY ON 2026-08-01** — and it had become worse than a
//! conflation in the meantime. Once `assert_addr_unique` began *refusing* a repeated address
//! (2026-07-28, release-active) the one-felt key stopped conflating two ledgers and started
//! *aborting* the anchor: ~2^15.5 offline folds plus two ordinary cell creations permanently
//! halted every node's finality executor. `cells_root` is now the `FLI2` exact tagged-linked-leaf
//! accumulator keyed by the id's sixteen `u16` limbs (`2^256`, injective). See
//! `cells_root_key_collision_halt_tooth.rs` for the old-halts / new-survives exhibit.
//!
//! This file's own subject is UNAFFECTED by that: it prices the ROOT width against a legacy
//! narrow-fold oracle it reconstructs locally, and both polarities still hold.

use dregg_cell::commitment::{V9_NUM_PRE_LIMBS, V9RotationContext, compute_rotated_pre_limbs};
use dregg_cell::{Cell, CellId, Ledger};
use dregg_circuit::Faithful8;
use dregg_circuit::effect_vm::layout_generated::CELLS_ROOT_GROUP;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{compute_heap_root_entries, empty_heap_root};
use dregg_circuit::poseidon2::hash_bytes;
use dregg_turn::rotation_witness::{
    cells_root, empty_commitments_root_8, empty_nullifier_root_8, empty_revoked_root_8,
};
use dregg_turn::state_commit::{absent_cell_commitment, consensus_ctx, consensus_state_commitment};

/// The collection id present-cell existence leaves are keyed under — the value of the private
/// `rotation_witness::CELLS_COLLECTION`.
const CELLS_COLLECTION: u32 = 0;

/// The token domain every cell in this file lives in.
const TOKEN: [u8; 32] = [0u8; 32];

/// The anchor cell's public key (the agent leg whose own limbs are identical across both ledgers,
/// so the ONLY difference between the two anchors is the present-cell set).
const AGENT_PK: [u8; 32] = [7u8; 32];

/// **THE FIXTURE** — two filler-cell seeds whose present-cell sets `{agent, filler}` collide on the
/// PRE-FIX one-felt `cells_root` fold and are separated by the faithful 8-felt fold. Produced by
/// [`search_cells_root_lane0_collision`]; the test below re-derives and re-checks both facts, so a
/// stale fixture fails loudly rather than passing vacuously.
/// Regenerated 2026-08-01 after **27 369** offline narrow folds — no chain interaction, no proof,
/// no signature, ~1 s in a release test build. (The analytic birthday price for a full 31-bit fold
/// is ~2^15.5 ≈ 45k samples; 27k is an ordinary draw from that distribution. One sample is an
/// observation, not a claim about the fold's effective width.)
///
/// ⚠ The previous fixture (4084 / 7322, narrow root 1 976 398 739) went stale when `hash_bytes`
/// moved to the length-injective `bytes_to_lanes` preimage — the legacy oracle below keys on
/// `hash_bytes`, so ANY change to it invalidates the seeds. That is what the FIXTURE STALE
/// assertion is for; regenerate with the `#[ignore]`d search rather than weakening it.
const COLLIDING_SEEDS: (u64, u64) = (SEED_A, SEED_B);
const SEED_A: u64 = 3678;
const SEED_B: u64 = 27368;
/// The narrow-fold value both present-cell sets landed on — pinned so a fixture that silently stops
/// colliding is a loud failure rather than a passing test over a non-collision.
const COLLIDING_NARROW_ROOT: u32 = 187_521_109;

/// A cell built from a `u64` seed in the fixed token domain.
fn seeded_cell(seed: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[..8].copy_from_slice(&seed.to_le_bytes());
    Cell::new(pk, TOKEN)
}

/// The felt existence-leaf key of a cell id — `rotation_witness::cells_root`'s key derivation.
fn cell_key(id: &CellId) -> BabyBear {
    hash_bytes(id.as_bytes())
}

/// **THE PRE-FIX `cells_root` PRODUCER, verbatim.** The body `rotation_witness::cells_root` had
/// before wound #23 was closed: a 1-felt `CanonicalHeapTree` (`heap_node` arity-2 nodes, arity-2
/// leaf digests) existence fold, returning ONE `BabyBear`.
fn legacy_narrow_cells_root(ledger: &Ledger) -> BabyBear {
    let mut entries: Vec<((BabyBear, BabyBear), BabyBear)> = Vec::new();
    for (id, _) in ledger.iter() {
        entries.push((
            (BabyBear::new(CELLS_COLLECTION), cell_key(id)),
            BabyBear::ONE,
        ));
    }
    if entries.is_empty() {
        return empty_heap_root();
    }
    compute_heap_root_entries(&entries)
}

/// **THE PRE-FIX ANCHOR, reconstructed.** `compute_rotated_pre_limbs` at HEAD writes the whole
/// `cells_root` group; undoing exactly that fill (completion lanes back to ZERO, lane 0 back to the
/// narrow fold) reproduces the pre-fix limb vector bit-for-bit, because no other limb depends on
/// `cells_root`. The chain is the same deployed chip chain either way — this isolates the COMPONENT.
fn legacy_cell_anchor(cell: &Cell, ledger: &Ledger, ctx: &V9RotationContext) -> [u8; 32] {
    let mut pre = compute_rotated_pre_limbs(cell, ctx);
    for &pos in &CELLS_ROOT_GROUP[1..] {
        pre[pos] = BabyBear::ZERO;
    }
    pre[0] = legacy_narrow_cells_root(ledger);
    Faithful8::from_wire_commit_chip(&pre, ctx.iroot).to_bytes32()
}

/// The pre-fix ABSENT-agent anchor (`state_commit::absent_cell_commitment` before the fix): an
/// all-zero limb vector whose ONLY non-zero entry is the narrow fold at limb 0. This is the case the
/// wound entry called worse — the anchor IS the ~31-bit felt.
fn legacy_absent_anchor(ledger: &Ledger, iroot: BabyBear) -> [u8; 32] {
    let mut limbs = vec![BabyBear::ZERO; V9_NUM_PRE_LIMBS];
    limbs[0] = legacy_narrow_cells_root(ledger);
    Faithful8::from_wire_commit_chip(&limbs, iroot).to_bytes32()
}

/// A ledger holding the anchor cell plus one filler cell.
fn ledger_with(filler: &Cell) -> (Ledger, Cell) {
    let agent = Cell::with_balance(AGENT_PK, TOKEN, 500);
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent.clone()).expect("insert agent");
    ledger.insert_cell(filler.clone()).expect("insert filler");
    (ledger, agent)
}

fn ctx_for(ledger: &Ledger) -> V9RotationContext {
    consensus_ctx(
        ledger,
        empty_nullifier_root_8(),
        empty_commitments_root_8(),
        empty_revoked_root_8(),
    )
}

/// **THE FALSIFIER, both polarities.** Two present-cell sets that the PRE-FIX anchor conflates and
/// the POST-FIX anchor separates — on the deployed `consensus_state_commitment` entry point, for the
/// agent-present case AND the (worse) agent-absent case.
#[test]
fn lane0_colliding_cell_sets_share_the_old_anchor_and_split_the_new_one() {
    let (seed_a, seed_b) = COLLIDING_SEEDS;
    assert_ne!(
        seed_a, seed_b,
        "the fixture must be two DIFFERENT cell sets"
    );

    let filler_a = seeded_cell(seed_a);
    let filler_b = seeded_cell(seed_b);
    let (ledger_a, agent) = ledger_with(&filler_a);
    let (ledger_b, agent_b) = ledger_with(&filler_b);
    assert_eq!(
        agent.id(),
        agent_b.id(),
        "the agent leg must be IDENTICAL in both ledgers — otherwise the anchors differ for a \
         reason that has nothing to do with cells_root"
    );

    // The two sets are genuinely different, and NOT via a key collision (which the widening does
    // not and cannot fix — that is the kind-D accumulator-KEY class).
    assert_ne!(filler_a.id(), filler_b.id(), "distinct filler cells");
    assert_ne!(
        cell_key(&filler_a.id()),
        cell_key(&filler_b.id()),
        "the fixture must be a genuine ROOT collision over DISTINCT existence leaves, not a \
         `hash_bytes(CellId)` KEY collision wearing a root collision's clothes"
    );

    // ---- POLARITY 1 (the wound): the PRE-FIX fold conflates the two sets. ----
    let narrow_a = legacy_narrow_cells_root(&ledger_a);
    let narrow_b = legacy_narrow_cells_root(&ledger_b);
    assert_eq!(
        narrow_a, narrow_b,
        "FIXTURE STALE: the two present-cell sets must COLLIDE on the pre-fix 1-felt cells_root \
         fold — re-run `search_cells_root_lane0_collision` and update COLLIDING_SEEDS"
    );
    assert_eq!(
        narrow_a.as_u32(),
        COLLIDING_NARROW_ROOT,
        "FIXTURE STALE: the recorded collision value moved — the pre-fix fold or the id derivation \
         changed under this test"
    );

    let ctx_a = ctx_for(&ledger_a);
    let ctx_b = ctx_for(&ledger_b);

    let old_anchor_a = legacy_cell_anchor(&agent, &ledger_a, &ctx_a);
    let old_anchor_b = legacy_cell_anchor(&agent, &ledger_b, &ctx_b);
    assert_eq!(
        old_anchor_a, old_anchor_b,
        "WOUND #23, agent-present: the PRE-FIX consensus anchor is the SAME for two different \
         ledgers — one executor signature and one receipt QC over two states"
    );

    let old_absent_a = legacy_absent_anchor(&ledger_a, ctx_a.iroot);
    let old_absent_b = legacy_absent_anchor(&ledger_b, ctx_b.iroot);
    assert_eq!(
        old_absent_a, old_absent_b,
        "WOUND #23, agent-absent (the worse case): the PRE-FIX post-state anchor IS the narrow \
         felt, so two different ledgers share one signed post-state"
    );

    // ---- POLARITY 2 (the closure): the faithful 8-felt group separates them. ----
    let wide_a = cells_root(&ledger_a);
    let wide_b = cells_root(&ledger_b);
    assert_ne!(
        wide_a, wide_b,
        "the faithful 8-felt cells_root must SEPARATE the two sets the 1-felt fold conflated"
    );
    assert_ne!(
        wide_a.limbs()[0],
        narrow_a,
        "SANITY: lane 0 of the wide root must NOT be the old narrow root — the widening is a \
         genuine re-fold through `node8` (arity-16 nodes, arity-3 `digest8` leaves), not a lane-0 \
         broadcast or a re-hash of the narrow value (`finalSqueezeOnly_still_conflates`, #12)"
    );

    let new_anchor_a = consensus_state_commitment(&ledger_a, &agent.id(), &ctx_a);
    let new_anchor_b = consensus_state_commitment(&ledger_b, &agent.id(), &ctx_b);
    assert_ne!(
        new_anchor_a, new_anchor_b,
        "CLOSURE, agent-present: the deployed anchor must DIFFER for the two ledgers the narrow \
         fold conflated"
    );

    let new_absent_a = absent_cell_commitment(&ctx_a);
    let new_absent_b = absent_cell_commitment(&ctx_b);
    assert_ne!(
        new_absent_a, new_absent_b,
        "CLOSURE, agent-absent: the boundary-only anchor must DIFFER too — this is the case where \
         the narrow felt WAS the whole post-state"
    );

    // The fix moved the committed value: this is a receipt/consensus flag-day, not a no-op.
    assert_ne!(
        old_anchor_a, new_anchor_a,
        "the fix CHANGES pre_state_hash / post_state_hash on every turn — a receipt epoch"
    );
}

/// **ANTI-LAUNDER: the fold is wide at EVERY intermediate, not just at the top.**
///
/// Widening the carrier while the fold stays a 1-felt chain achieves nothing
/// (`finalSqueezeOnly_still_conflates`, #12) — the `iroot` sibling in the same struct is exactly
/// that shape (a left-leaning fold whose every intermediate `root: BabyBear` is ~31 bits). This test
/// witnesses the difference structurally: a cell-set change that leaves the ~31-bit lane-0 projection
/// of an INTERMEDIATE node untouched still moves the wide root, because each node carries 8 lanes.
/// Concretely: every completion lane of the root is a genuine `node8` output lane, so a set change
/// must be visible in lanes 1..7 and not only in lane 0.
#[test]
fn the_wide_cells_fold_is_eight_felts_at_every_level_not_a_wide_top_over_a_narrow_chain() {
    let (mut l1, _) = ledger_with(&seeded_cell(11));
    let (l2, _) = ledger_with(&seeded_cell(12));
    let r1 = cells_root(&l1);
    let r2 = cells_root(&l2);
    assert_ne!(r1, r2, "different cell sets, different roots");
    assert!(
        r1.limbs()[1..]
            .iter()
            .zip(r2.limbs()[1..].iter())
            .any(|(a, b)| a != b),
        "the COMPLETION lanes must carry independent information: if only lane 0 ever moved, the \
         octet would be a wide coat over a 1-felt chain"
    );

    // Growing the set moves all-but-nothing: at least half the lanes must move on a one-cell add
    // (a `node8` output lane is a chip output lane, not a padded projection).
    let before = cells_root(&l1);
    l1.insert_cell(seeded_cell(13)).expect("grow the cell set");
    let after = cells_root(&l1);
    let moved = before
        .limbs()
        .iter()
        .zip(after.limbs().iter())
        .filter(|(a, b)| a != b)
        .count();
    assert!(
        moved >= 7,
        "a one-cell set growth must move essentially every lane of a genuine node8 root; only \
         {moved}/8 moved — that is the signature of a narrow chain with a wide veneer"
    );
}

/// The producer twins agree lane-for-lane on the `cells_root` group — the same three-way discipline
/// `nullifier_root` / `commitments_root` / `revoked_root` already carry.
#[test]
fn both_producers_fill_the_cells_root_group_byte_identically() {
    let (ledger, agent) = ledger_with(&seeded_cell(21));
    let receipts: Vec<[u8; 32]> = vec![[3u8; 32]];
    let w = dregg_turn::rotation_witness::produce(
        &agent,
        &ledger,
        &empty_nullifier_root_8(),
        &empty_commitments_root_8(),
        &empty_revoked_root_8(),
        &receipts,
        &Default::default(),
    );
    let ctx = V9RotationContext {
        cells_root: cells_root(&ledger),
        nullifier_root: empty_nullifier_root_8(),
        commitments_root: empty_commitments_root_8(),
        revoked_root: empty_revoked_root_8(),
        iroot: dregg_turn::rotation_witness::iroot8(&receipts),
        material: Default::default(),
    };
    let pre_cell = compute_rotated_pre_limbs(&agent, &ctx);
    let expected = cells_root(&ledger).limbs();
    for (lane, &pos) in CELLS_ROOT_GROUP.iter().enumerate() {
        assert_eq!(
            w.pre_limbs[pos], expected[lane],
            "turn producer limb {pos} must carry cells-root lane {lane}"
        );
        assert_eq!(
            w.pre_limbs[pos], pre_cell[pos],
            "producer twins must write cells lane {lane} (limb {pos}) byte-identically"
        );
    }
    // The completion lanes are genuinely NON-ZERO — the closure of the zero-fill that WAS the wound.
    assert!(
        CELLS_ROOT_GROUP[1..]
            .iter()
            .any(|&pos| w.pre_limbs[pos] != BabyBear::ZERO),
        "the cells_root completion limbs 169..=175 must be NON-ZERO for a non-empty ledger"
    );
}

/// **THE SEARCH that produced [`COLLIDING_SEEDS`]** — a birthday grind over the PRE-FIX 1-felt
/// `cells_root` fold, entirely offline (no chain interaction, no proof, no signature): derive a
/// candidate `CellId` with `CellId::derive_raw` (BLAKE3 over attacker-chosen `(public_key,
/// token_id)`), fold the present-cell set `{agent, candidate}` through the narrow tree, and look for
/// a repeat. Candidates whose existence KEY collides with an earlier one are REJECTED: those are
/// kind-D key collisions, which no root widening fixes and which would make the fixture a lie.
///
/// `cargo test -p dregg-turn --release --test cells_root_width_falsification -- --ignored --nocapture`
#[test]
#[ignore = "birthday grind (~2^16 narrow folds) — run explicitly, in release, to regenerate the fixture"]
fn search_cells_root_lane0_collision() {
    use std::collections::HashMap;

    let agent = Cell::with_balance(AGENT_PK, TOKEN, 500);
    let agent_key = cell_key(&agent.id());
    // root felt -> (seed, existence key)
    let mut seen: HashMap<u32, (u64, u32)> = HashMap::new();
    let mut tried = 0u64;

    for seed in 0u64..(1u64 << 21) {
        let cell = seeded_cell(seed);
        let key = cell_key(&cell.id());
        if key == agent_key {
            continue; // a degenerate one-leaf set
        }
        let root = compute_heap_root_entries(&[
            ((BabyBear::new(CELLS_COLLECTION), agent_key), BabyBear::ONE),
            ((BabyBear::new(CELLS_COLLECTION), key), BabyBear::ONE),
        ]);
        tried += 1;
        if let Some(&(prev_seed, prev_key)) = seen.get(&root.as_u32()) {
            if prev_key == key.as_u32() {
                continue; // KEY collision, not a root collision — not what #23 is about
            }
            // Confirm the wide fold separates them before reporting.
            let (la, _) = ledger_with(&seeded_cell(prev_seed));
            let (lb, _) = ledger_with(&cell);
            let wide_differs = cells_root(&la) != cells_root(&lb);
            println!(
                "COLLISION after {tried} offline folds: SEED_A = {prev_seed}, SEED_B = {seed} \
                 (narrow root felt {}), wide roots differ = {wide_differs}",
                root.as_u32()
            );
            assert!(
                wide_differs,
                "a narrow-root collision the WIDE root also conflates would mean the widening is \
                 cosmetic — report it, do not paper over it"
            );
            return;
        }
        seen.insert(root.as_u32(), (seed, key.as_u32()));
    }
    panic!("no 1-felt cells_root collision in 2^21 candidates — the fold is not ~31 bits?");
}
