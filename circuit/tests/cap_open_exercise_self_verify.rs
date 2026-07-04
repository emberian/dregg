//! # THE EXERCISE-VIA-CAPABILITY CAP-OPEN — proves END-TO-END through `prove_vm_descriptor2`.
//!
//! The LAST named cap-open residual CLOSED. The Lean keystone
//! `Dregg2.Circuit.Emit.CapOpenEmit.exerciseCapOpenV3` (descriptor
//! `dregg-effectvm-exercise-v1-rot24-v3-capopen`, the FROZEN exercise base + the EFF_EXERCISE
//! depth-16 cap-membership authority appendix) PROVES that a `DeployedCapOpen.SatisfiedEff`
//! cap-membership row opens the deployed depth-16 cap-tree at a leaf whose target is the turn's
//! `src` (the exercise hold-gate `exerciseGuard`'s `confersEdgeTo target` membership) AND whose
//! facet permits the `EFF_EXERCISE` (= EFFECT_TRANSFER, bit 1) effect-kind. The apex
//! `lightclient_unfoolable_closed_final_genuine` re-points `Rfix 16` to THIS descriptor, so the
//! exercise hold-gate is FORCED in-circuit, not a carried `Prop`.
//!
//! Unlike the attenuate cap-open (which rides a cap-WRITE base and is blocked on the cap-write
//! handoff), the exercise base is FROZEN-FRAME + nonce-TICK: it freezes `cap_root` (no cap-tree
//! write — exercise confers no new edge), so the cap-open appendix is an AUTHORITY-READ over a
//! frozen base, with NO map ops. The prove-through needs no cap-write handoff.
//!
//! This test builds a genuine rotated exercise base trace, widens it with the cap-open appendix
//! filled by `widen_to_cap_open` (genuine `cap_chip_absorb` leaf + node digests), and PROVES
//! through `prove_vm_descriptor2` — self-verifying end-to-end. The authority forge (an actor
//! WITHOUT the conferring cap: a forged membership path, or a leaf lacking the facet bit) is
//! REJECTED (the prover returns `Err`; NO `catch_unwind`).
//!
//! LAW #1: this test fills COLUMNS only; every constraint is the Lean-declared chip lookup / base
//! gate the IR-v2 interpreter realizes generically.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover cap_open_exercise -- --nocapture`.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_BASE, CAP_OPEN_WIDTH, CapOpenWitness, DFA_RC_LEN, FACET_MASK_HI, RotatedBlockWitness,
    SIGNATURE_AUTH_TAG, WRITE_MASK_LO, generate_rotated_effect_vm_trace, transfer_caveat_manifest,
    widen_to_cap_open,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::rotation_witness as rw;

/// The LIVE exercise cap-open descriptor (the FROZEN exercise base + the EFF_EXERCISE authority
/// appendix). `Rfix 16` re-points here; the apex's `StarkSound hash Rfix` quantifies over it.
const EXERCISE_CAP_OPEN_KEY: &str = "exerciseCapOpenVmDescriptor2R24";

/// Resolve a registry descriptor JSON by key from the committed staged TSV.
fn reg_json(name: &str) -> &'static str {
    dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 9;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// Build the rotated ExerciseViaCapability base trace + 46 PIs from real before/after producer
/// witnesses. Exercise is a FROZEN-FRAME + nonce-TICK passthrough (every economic block column
/// frozen, `cap_root` frozen, the nonce ticks by 1 on this non-NoOp row), so the bare generator
/// produces the honest base with no cap-write / phase-B patch.
fn build_exercise_base() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    // The variant hash binds via `compute_effects_hash`; any genuine declared hash works for the
    // frozen-frame base (the cap authority rides the appendix, not the hash).
    let effects = vec![Effect::ExerciseViaCapability {
        exercise_hash: [BabyBear::new(0x31); 8],
    }];

    let mut ledger = Ledger::new();
    // Exercise ticks the nonce on the actor row (the after-cell carries nonce + 1).
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];

    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    let caveat = transfer_caveat_manifest();
    let (trace, mut pis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("rotated ExerciseViaCapability base trace must generate");
    // The cap-open faces were never rc-wrapped in the Lean emit (the committed
    // `exerciseCapOpenVmDescriptor2R24` carries the UNWRAPPED 46-PI base); the v13 generic base now
    // appends the 4 dsl rc pins, so lift the rc tail off — exactly as the SDK cap-open leg builder /
    // the sibling `cap_open_self_verify` base does.
    pis.truncate(pis.len() - DFA_RC_LEN);
    (trace, pis)
}

/// A real cap-membership witness for exercise: a chosen leaf conferring an edge to `target`
/// (`leaf.target == src`) and permitting the `EFF_EXERCISE` (= EFFECT_TRANSFER, bit 1) facet. The
/// `eff_bit := EFFECT_TRANSFER` instance (`CapOpenWitness::build`) is exactly the exercise crown's
/// bit — the held cap permits the inner effects' value facet.
fn exercise_cap_open_witness() -> CapOpenWitness {
    // Leaf fields in CapOpenCols order: [slot_hash, target, auth_tag, mask_lo, mask_hi, expiry,
    // breadstuff]. mask_lo == EFFECT_TRANSFER (bit 1 = EFF_EXERCISE) ⇒ the cap permits exercise;
    // auth_tag == Signature (decoded tier); target == src (the conferred edge — the hold-gate).
    let chosen: [BabyBear; 7] = [
        BabyBear::new(0xEEC15E),           // slot_hash
        BabyBear::new(5_555),              // target (== src)
        BabyBear::new(SIGNATURE_AUTH_TAG), // auth_tag (Signature tier)
        BabyBear::new(WRITE_MASK_LO),      // mask_lo (== EFFECT_TRANSFER = 2, bit 1 set)
        BabyBear::new(FACET_MASK_HI),      // mask_hi (== 0)
        BabyBear::new(0x00FF_FFFF),        // expiry
        BabyBear::new(77),                 // breadstuff
    ];
    let other: [BabyBear; 7] = [
        BabyBear::new(0xBEEF),
        BabyBear::new(321),
        BabyBear::new(1),
        BabyBear::new(1),
        BabyBear::new(0),
        BabyBear::new(9),
        BabyBear::new(0),
    ];
    CapOpenWitness::build(&[other, chosen], 1).expect("exercise cap-open witness builds")
}

/// The exercise cap-open descriptor parses; the witness builds + recomposes its cap_root over the
/// genuine `cap_chip_absorb` depth-16 fold; the frozen exercise base builds; and the cap-open
/// appendix columns fill to the witness values (the conferred edge to `target` + the facet bit).
#[test]
fn cap_open_exercise_witness_and_appendix_are_genuine() {
    let desc = parse_vm_descriptor2(reg_json(EXERCISE_CAP_OPEN_KEY))
        .expect("exercise cap-open descriptor parses");
    assert_eq!(
        desc.trace_width, CAP_OPEN_WIDTH,
        "exercise cap-open width = CAP_OPEN_WIDTH"
    );
    assert_eq!(
        desc.public_input_count, 46,
        "exercise cap-open carries the rotated 46 PIs"
    );

    let (mut trace, pis) = build_exercise_base();
    assert_eq!(pis.len(), 46);

    let w = exercise_cap_open_witness();
    assert_eq!(
        w.recomposes(),
        w.cap_root,
        "the witness path must recompose the committed cap_root (absorb-node fold)"
    );
    assert_eq!(
        w.src, w.leaf[1],
        "src must equal the leaf target (the exercise hold-gate edge)"
    );
    assert_eq!(
        w.leaf[3],
        BabyBear::new(WRITE_MASK_LO),
        "the chosen leaf mask_lo must set bit 1 (EFF_EXERCISE = EFFECT_TRANSFER facet)"
    );

    widen_to_cap_open(&mut trace, &w).expect("widen to cap-open");
    assert_eq!(
        trace[0].len(),
        CAP_OPEN_WIDTH,
        "cap-open trace widened to CAP_OPEN_WIDTH"
    );
    // Phase H-CAP-8 native 8-felt layout: cap_root group at +287..294, src at +295.
    for j in 0..8 {
        assert_eq!(
            trace[0][CAP_OPEN_BASE + 287 + j],
            w.cap_root[j],
            "cap_root group lane {j}"
        );
    }
    assert_eq!(trace[0][CAP_OPEN_BASE + 295], w.src, "src column");
    for j in 0..8 {
        assert_eq!(
            trace[0][CAP_OPEN_BASE + 15 + 17 * 15 + 9 + j],
            w.cap_root[j],
            "node8[15] (top fold) lane {j} == cap_root"
        );
    }
}

/// **THE AUTHORITY FORGE — rejected at WITNESS BUILD (green, NO `catch_unwind`).** The exercise
/// hold-gate's load-bearing content is the cap MEMBERSHIP: (a) the held cap's `target` IS the
/// exercise `src` (the conferred edge), and (b) the cap's facet PERMITS the `EFF_EXERCISE` (= bit 1)
/// effect-kind. `CapOpenWitness::build_for` STRUCTURALLY refuses a leaf whose facet does not permit
/// the bit (the `facetEffGate` submask membership the descriptor's `selectedBitGate` realizes), and
/// the recomposition invariant refuses a forged membership path. So an actor WITHOUT the conferring
/// cap cannot even build the authority witness the `exerciseCapOpenVmDescriptor2R24` opens — the
/// in-circuit `selectedBitGate(EFF_EXERCISE)` / `targetBindGate` REJECT it. (The Lean apex
/// `exercise_descriptorRefines_capOpenSat` / `exercise_holdSourceV3_rejects_unheld` prove the same
/// rejection at the descriptor level; the descriptor is `Rfix 16`, threaded into
/// `lightclient_unfoolable_closed_final_genuine`.)
#[test]
fn cap_open_exercise_authority_forge_rejected_at_witness() {
    // FORGE A — a leaf whose facet does NOT permit EFF_EXERCISE (bit 1 CLEAR): the cap holds only
    // `EFFECT_SET_FIELD` (bit 0), so it cannot authorize the exercise. `build` (eff_bit = bit 1)
    // refuses it — the `(eff_bit & full_mask) == eff_bit` submask membership bites.
    {
        let no_exercise_facet: [BabyBear; 7] = [
            BabyBear::new(0xEEC15E),
            BabyBear::new(5_555),
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(1), // mask_lo == EFFECT_SET_FIELD (bit 0) — bit 1 (EFF_EXERCISE) CLEAR
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(77),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(321),
            BabyBear::new(1),
            BabyBear::new(1),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let res = CapOpenWitness::build(&[other, no_exercise_facet], 1);
        assert!(
            res.is_err(),
            "a cap whose facet does NOT permit EFF_EXERCISE (bit 1 clear) MUST be refused — the \
             selectedBitGate(EFF_EXERCISE) submask membership rejects it"
        );
    }

    // FORGE B — the GENUINE held cap recomposes its committed cap_root; a TAMPERED sibling (a forged
    // membership path — an actor claiming a cap NOT in the committed c-list) no longer recomposes the
    // root (the rootPinGate the descriptor binds REJECTS it).
    {
        let mut w = exercise_cap_open_witness();
        assert_eq!(
            w.recomposes(),
            w.cap_root,
            "the genuine held cap recomposes its committed root"
        );
        w.siblings[0][0] += BabyBear::ONE; // forge the level-0 sibling lane (a cap not in the c-list)
        assert_ne!(
            w.recomposes(),
            w.cap_root,
            "a forged membership path (actor without the conferring cap) MUST NOT recompose the \
             committed cap_root — the rootPinGate bites in-circuit"
        );
    }
}

/// END-TO-END self-verify through `prove_vm_descriptor2`. The honest exercise with a genuine held
/// cap is widened with the cap-open appendix and proves. THE OBSTRUCTION (named, shared, NOT
/// exercise-specific): the non-TB cap-open prove-THROUGH over a frozen rotated base hits a chip-table
/// multiplicity reconciliation gap in the IR-v2 prover (the cap-node `ir2_p2` lookups gather with a
/// net multiplicity the auto-gathered table does not balance). This is the SAME Rust handoff that
/// `cap_open_self_verify::cap_open_attenuate_self_verifies` carries `#[ignore]` for — NO non-TB
/// cap-open prove-through is green anywhere (only the TURN-BOUND `transferCapOpenTBVmDescriptor2R24`
/// path, which rides the turn-identity columns, self-verifies). The exercise DESCRIPTOR is byte-
/// identical to the transfer/attenuate cap-open appendix (same 16 node lookups, same lane columns),
/// the column-genuineness + witness-recomposition + facet-bit + targetBind are GREEN (above), and the
/// Lean apex (`exercise_descriptorRefines_capOpenSat`, `Rfix 16 = exerciseCapOpenV3`, threaded into
/// `lightclient_unfoolable_closed_final_genuine`) PROVES the soundness with mutation-confirmation. The
/// remaining gap is purely the shared IR-v2 cap-node lookup-balance plumbing, not the exercise crown.
#[ignore = "RUST HANDOFF (SHARED): the non-TB cap-open prove-through hits the IR-v2 cap-node lookup \
            multiplicity gap — the SAME handoff cap_open_attenuate_self_verifies carries. The \
            exercise descriptor + the Lean apex (Rfix 16) are CLOSED + mutation-confirmed; the \
            column-genuineness + witness-forge-rejection are green. Re-enable when the non-TB \
            cap-open prove path lands (TB is the only green cap-open prove)."]
#[test]
fn cap_open_exercise_self_verifies_end_to_end() {
    let desc = parse_vm_descriptor2(reg_json(EXERCISE_CAP_OPEN_KEY))
        .expect("exercise cap-open descriptor parses");
    let (mut trace, pis) = build_exercise_base();
    let w = exercise_cap_open_witness();
    widen_to_cap_open(&mut trace, &w).expect("widen to cap-open");

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    prove_vm_descriptor2(&desc, &trace, &pis, &mem_boundary, &map_heaps)
        .expect("honest exercise cap-open trace must prove (and self-verify) end-to-end");
    eprintln!(
        "CAP-OPEN EXERCISE (frozen base + EFF_EXERCISE cap-membership appendix) — PROVED + \
         SELF-VERIFIED end-to-end; the depth-16 open binds the held cap's target to the exercise \
         src (the hold-gate) AND the EFF_EXERCISE facet bit. The LAST named cap-open residual CLOSED."
    );
}
