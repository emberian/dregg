//! THE WIDE+umem WELDED IVC LEG — MULTI-DOMAIN GAUNTLET (STAGED, VK-RISK-FREE).
//!
//! The sibling `ivc_turn_chain_wide_umem_cohort_gauntlet.rs` drives the single-domain (heap) value
//! cohort through the wide+umem welded leg, and `..._cap_write_gauntlet.rs` the cap-WRITE family.
//! THIS file closes the LAST family tail: the NOTE/BRIDGE economic verbs (`NoteSpend` / `BridgeMint`)
//! whose state touch spans TWO domains in a single effect — a `nullifiers` freshness insert + a
//! `heap` balance credit. The single-domain weld FAILS CLOSED on such a leg; this drives them through
//! the MULTI-DOMAIN weld (`mint_welded_wide_umem_multidomain_rotated_participant_leg` →
//! `RotatedParticipantLeg::mint_welded_wide_multidomain_from_block_witnesses`, which welds one guarded
//! `umemOp` PER domain onto the WIDE descriptor via `weld_umem_multidomain_into_wide_descriptor`).
//! Completing this puts the FULL effect set on the wide+umem leg.
//!
//! Each economic verb's leg:
//!   * PROVES + self-verifies on the welded WIDE descriptor (the 8-felt / ~124-bit anchors PRESERVED
//!     through the purely-additive two-domain umem weld — the leg carries `wide_old_root8`/
//!     `wide_new_root8`);
//!   * FOLDS a multi-turn same-family history through `fold_wide_welded_umem_turn_chain_staged`
//!     (8-felt continuity + the ordered-history digest);
//!   * REFUSES a forged 8-felt AFTER commit (the ~124-bit binding tooth bites).
//!
//! The cross-DOMAIN economic invariant (credit == spent/minted value) rides the effect's own rotated
//! AIR (the whole rotated constraint set the weld preserves), NOT the memory reconciliation — the same
//! division as the narrow multi-domain cohort.
//!
//! STAGED: nothing deployed — welded staged descriptors, no VK epoch, no deployed-default flip.

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, fold_wide_welded_umem_turn_chain_staged,
};
use dregg_circuit_prove::joint_turn_aggregation::{DescriptorParticipant, RotatedParticipantLeg};
use dregg_turn::rotation_witness::mint_welded_wide_umem_multidomain_rotated_participant_leg;
use dregg_turn::umem::{UKey, UProjection, UVal, UmemKind, UmemOp};

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
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

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// The genuine two-domain NOTE/BRIDGE umem touch: PRE carries the cell's balance; the op trace
/// credits the balance (`heap`) AND inserts a FRESH nullifier (`nullifiers`, prev absent — the
/// double-spend freshness gate). The `nf_seed` distinguishes per-turn nullifiers so a chained history
/// never re-inserts the same one.
fn note_umem_touch(
    cell: dregg_cell::Cell,
    before_balance: i64,
    after_balance: i64,
    nf_seed: u8,
) -> (UProjection, Vec<UmemOp>) {
    let id = cell.id();
    let mut pre = UProjection::new();
    pre.insert(UKey::Balance(id), UVal::Int(before_balance));
    let mut nf = [0u8; 32];
    nf[0] = nf_seed;
    nf[31] = nf_seed.wrapping_mul(53).wrapping_add(1);
    let ops = vec![
        // heap: credit the balance
        UmemOp {
            kind: UmemKind::Write,
            key: UKey::Balance(id),
            val: Some(UVal::Int(after_balance)),
            prev_val: Some(UVal::Int(before_balance)),
            prev_serial: 0,
        },
        // nullifiers: insert a fresh nullifier (prev absent — the freshness gate)
        UmemOp {
            kind: UmemKind::Write,
            key: UKey::NoteNullifier(nf),
            val: Some(UVal::Present),
            prev_val: None,
            prev_serial: 0,
        },
    ];
    (pre, ops)
}

/// The grow-gate BEFORE nullifier accumulator a NoteSpend wide producer needs (independent of the
/// umem nullifier — the rotated AIR's grow-gate leg, not the memory reconciliation).
fn grow_gate_before() -> Vec<BabyBear> {
    vec![BabyBear::new(0x1111), BabyBear::new(0x2222)]
}

/// Mint a WIDE+umem MULTI-DOMAIN welded leg for one NOTE/BRIDGE economic verb. The issuer cell's
/// balance moves `before_balance` → `after_balance` at `nonce` (the heap-domain credit), and the umem
/// touch additionally inserts a fresh nullifier (the nullifiers domain). `before_nullifiers` is the
/// NoteSpend grow-gate accumulator (None for BridgeMint).
fn mint_note_leg(
    before_balance: i64,
    after_balance: i64,
    nonce: u64,
    nf_seed: u8,
    effect: Effect,
    before_nullifiers: Option<&[BabyBear]>,
) -> (FinalizedTurn, [BabyBear; 8], [BabyBear; 8]) {
    let state = CellState::new(before_balance as u64, nonce as u32);
    let effects = vec![effect];
    let before_cell = producer_cell(before_balance, nonce);
    let after_cell = producer_cell(after_balance, nonce);
    let (pre, ops) = note_umem_touch(before_cell.clone(), before_balance, after_balance, nf_seed);
    let leg = mint_welded_wide_umem_multidomain_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &[0u8; 32],
        &[0u8; 32],
        &[[1u8; 32], [2u8; 32]],
        None,
        &pre,
        &ops,
        before_nullifiers,
    )
    .expect("WIDE+umem MULTI-DOMAIN welded leg mints + self-verifies");
    let old8 = leg.wide_old_root8().expect("8-felt before anchor");
    let new8 = leg.wide_new_root8().expect("8-felt after anchor");
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old8,
        new8,
    )
}

fn note_spend(value: u64) -> Effect {
    Effect::NoteSpend {
        nullifier: BabyBear::new(0xBEEF),
        value,
    }
}

fn bridge_mint(value: u64) -> Effect {
    Effect::BridgeMint {
        value_lo: BabyBear::new(value as u32),
        mint_hash: BabyBear::new(0x31D6),
        value_full: value,
    }
}

/// Each economic verb mints a wide+umem MULTI-DOMAIN welded leg that PRESERVES the 8-felt (~124-bit)
/// anchors (BEFORE != AFTER — a real bound move, not a frozen passthrough).
#[test]
fn multidomain_economic_verbs_mint_wide_welded_legs() {
    // NoteSpend CREDIT 7 (heap) + a fresh nullifier insert (nullifiers).
    let gg = grow_gate_before();
    let (_t, o8, n8) = mint_note_leg(1000, 1007, 0, 31, note_spend(7), Some(&gg));
    assert_ne!(o8, n8, "noteSpend: the 8-felt commit MOVED (non-vacuous)");

    // BridgeMint CREDIT 900 (heap) + a fresh bridged-nullifier insert (nullifiers).
    let (_t, o8, n8) = mint_note_leg(100_000, 100_900, 0, 44, bridge_mint(900), None);
    assert_ne!(o8, n8, "bridgeMint: the 8-felt commit MOVED (non-vacuous)");
}

/// A multi-turn SAME-family WIDE MULTI-DOMAIN welded history folds through the 8-felt continuity +
/// ordered digest, for BridgeMint (a multi-domain economic-verb history).
#[test]
fn multidomain_bridge_mint_history_folds() {
    let (t0, o80, n80) = mint_note_leg(100_000, 100_100, 0, 10, bridge_mint(100), None);
    let (t1, o81, n81) = mint_note_leg(100_100, 100_200, 1, 11, bridge_mint(100), None);
    let (t2, o82, _n82) = mint_note_leg(100_200, 100_300, 2, 12, bridge_mint(100), None);
    // The honest mints chain at the 8-felt anchor (balance threads the wide commit).
    assert_eq!(o81, n80, "turn1 old8 == turn0 new8 (bridgeMint continuity)");
    assert_eq!(o82, n81, "turn2 old8 == turn1 new8 (bridgeMint continuity)");
    let turns = vec![t0, t1, t2];
    let summary = fold_wide_welded_umem_turn_chain_staged(&turns)
        .expect("a continuous 3-turn WIDE MULTI-DOMAIN welded bridgeMint history folds (8-felt)");
    assert_eq!(summary.num_turns, 3);
    assert_eq!(summary.genesis_root8, o80);
    assert!(
        summary.chain_digest8.iter().any(|&x| x != BabyBear::ZERO),
        "real ~124-bit ordered-history digest"
    );
}

/// A forged 8-felt AFTER commit on a WIDE MULTI-DOMAIN welded leg no longer verifies against its
/// welded descriptor — the ~124-bit binding tooth bites per economic verb (host admission refuses it).
#[test]
fn multidomain_forged_post_commit_refused_per_verb() {
    let gg = grow_gate_before();
    for (label, t0, t1) in [
        (
            "noteSpend",
            mint_note_leg(1000, 1007, 0, 20, note_spend(7), Some(&gg)).0,
            mint_note_leg(1007, 1014, 1, 21, note_spend(7), Some(&gg)).0,
        ),
        (
            "bridgeMint",
            mint_note_leg(100_000, 100_100, 0, 30, bridge_mint(100), None).0,
            mint_note_leg(100_100, 100_200, 1, 31, bridge_mint(100), None).0,
        ),
    ] {
        // FORGE the last PI (the 8-felt AFTER commit tail) on the second leg.
        let DescriptorParticipant { rotated } = t1.participant;
        let RotatedParticipantLeg {
            proof,
            descriptor,
            mut public_inputs,
            custom_witness: _,
            bridge_witness: _,
        } = rotated;
        let last = public_inputs.len() - 1;
        public_inputs[last] = public_inputs[last] + BabyBear::ONE;
        let forged = FinalizedTurn::new(DescriptorParticipant::rotated(RotatedParticipantLeg {
            proof,
            descriptor,
            public_inputs,
            custom_witness: None,
            bridge_witness: None,
        }));
        let turns = [t0, forged];
        match fold_wide_welded_umem_turn_chain_staged(&turns) {
            Err(TurnChainError::TurnProofInvalid { index, .. }) => assert_eq!(
                index, 1,
                "{label}: forged 8-felt post-commit refused at index 1"
            ),
            Ok(_) => panic!(
                "{label}: a forged WIDE multi-domain welded 8-felt post-commit must not fold"
            ),
            Err(other) => panic!("{label}: expected TurnProofInvalid, got {other:?}"),
        }
    }
}

/// A SINGLE-domain leg (only the heap balance credit, no nullifier) FAILS CLOSED on the multi-domain
/// entry — it belongs on the single-domain wide+umem weld, not the two-domain one.
#[test]
fn single_domain_leg_fails_closed_on_multidomain() {
    let state = CellState::new(100_000, 0);
    let effects = vec![bridge_mint(100)];
    let before_cell = producer_cell(100_000, 0);
    let after_cell = producer_cell(100_100, 0);
    let id = before_cell.id();
    let mut pre = UProjection::new();
    pre.insert(UKey::Balance(id), UVal::Int(100_000));
    // ONLY the heap op — no nullifiers domain.
    let ops = vec![UmemOp {
        kind: UmemKind::Write,
        key: UKey::Balance(id),
        val: Some(UVal::Int(100_100)),
        prev_val: Some(UVal::Int(100_000)),
        prev_serial: 0,
    }];
    let res = mint_welded_wide_umem_multidomain_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &[0u8; 32],
        &[0u8; 32],
        &[[1u8; 32]],
        None,
        &pre,
        &ops,
        None,
    );
    assert!(
        res.is_err(),
        "a single-domain leg must FAIL CLOSED on the multi-domain wide weld (it belongs on the \
         single-domain entry), never mint a two-domain receipt"
    );
}
