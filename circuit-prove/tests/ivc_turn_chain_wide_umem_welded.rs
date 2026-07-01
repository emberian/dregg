//! WHOLE-CHAIN IVC FOLD over the WIDE WELDED ROTATED+UMEM leg (STAGED, VK-RISK-FREE) — the IVC half
//! of the genuine flip precursor the VK epoch needs.
//!
//! The sibling `ivc_turn_chain_rotated_umem_welded.rs` folds through the NARROW welded leg (1-felt /
//! 46-PI). THIS file folds through the WIDE welded leg
//! (`mint_welded_wide_umem_rotated_participant_leg` →
//! `RotatedParticipantLeg::mint_welded_wide_from_block_witnesses`): each finalized turn carries ONE
//! leaf that proves BOTH the WIDE rotated cohort semantics (the 8-felt / ~124-bit faithful commit,
//! the 16 wide commit PIs at the leg's tail) AND the universal-memory reconciliation. The chain fold
//! reads the SAME single-felt rotated `old_root`/`new_root` (PI 34/35 — intact through the additive
//! weld), AND the leg additionally carries the 8-felt `wide_old_root8`/`wide_new_root8` anchors.
//!
//! - `wide_welded_umem_chain_folds_host` — a continuous 3-turn WIDE welded history folds through
//!   `fold_wide_welded_umem_turn_chain_staged`, binding the **8-felt** (~124-bit) continuity
//!   (`prev.wide_new_root8 == next.wide_old_root8`) + the 8-felt ordered-history digest.
//! - `wide_welded_umem_broken_order_rejected` — a spliced out-of-order WIDE welded turn is refused at
//!   the 8-felt continuity tooth (`WideChainBreak`).
//! - `wide_welded_umem_forged_post_commit_refused` — a forged 8-felt AFTER commit (a last-8 PI) on a
//!   WIDE welded leg no longer verifies against its welded descriptor — host admission refuses it.
//! - `wide_welded_umem_chain_folds_recursive` — THE IN-CIRCUIT RECURSIVE WIDE FOLD
//!   (`prove_wide_welded_umem_turn_chain_recursive_staged`): the wide welded leaves re-verify
//!   IN-CIRCUIT and aggregate to ONE root whose exposed 8-felt segment is the whole-chain claim; it
//!   verifies under its honest VK anchor. `#[ignore]` (minutes).
//! - `wide_welded_umem_recursive_broken_order_rejected` — the in-circuit recursive entry refuses a
//!   spliced out-of-order WIDE welded turn at the 8-felt continuity tooth (`WideChainBreak`).
//!
//! NOTE: the wide fold binds the **8-felt** anchors because the wide form RETIRES the single-felt
//! rotated commit PIs (34/35) to zero (the 8-felt wide commit is the sole binding). The in-circuit
//! RECURSIVE wide fold (the 8-felt generalization of the single-felt chain-binding recursion) binds
//! that 8-felt continuity (`prev.wide_new_root8 == next.wide_old_root8`) lane-by-lane IN-CIRCUIT at
//! each aggregation node — the whole-history IVC over the wide+umem legs folds in-circuit, not just
//! host-side.

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, fold_wide_welded_umem_turn_chain_staged,
    prove_wide_welded_umem_turn_chain_recursive_staged, verify_wide_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn::rotation_witness::mint_welded_wide_umem_rotated_participant_leg;

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

/// Build a REAL finalized turn on the WIDE WELDED rotated+umem path: a `Transfer` DEBIT of `amount`
/// from `(balance, nonce)`. Returns the turn + its single-felt rotated `(old_root, new_root)` + the
/// 8-felt wide `(old_root8, new_root8)`.
#[allow(clippy::type_complexity)]
fn make_wide_welded_turn(
    balance: u64,
    nonce: u32,
    amount: u64,
) -> (
    FinalizedTurn,
    BabyBear,
    BabyBear,
    [BabyBear; 8],
    [BabyBear; 8],
) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let leg = mint_welded_wide_umem_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &[0u8; 32],
        &[0u8; 32],
        &[[1u8; 32], [2u8; 32]],
        None,
    )
    .expect("WIDE welded rotated+umem transfer leg mints + self-verifies");
    let old_root = leg.old_root();
    let new_root = leg.new_root();
    let old8 = leg
        .wide_old_root8()
        .expect("wide leg carries 8-felt before anchor");
    let new8 = leg
        .wide_new_root8()
        .expect("wide leg carries 8-felt after anchor");
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
        old8,
        new8,
    )
}

#[test]
fn wide_welded_umem_chain_folds_host() {
    // A continuous 3-turn WIDE welded history: each debits 7, advancing balance + nonce so the
    // 8-felt wide state-commit anchors link.
    let (t0, _o0, _n0, o80, n80) = make_wide_welded_turn(1000, 0, 7);
    let (t1, _o1, _n1, o81, n81) = make_wide_welded_turn(993, 1, 7);
    let (t2, _o2, _n2, o82, n82) = make_wide_welded_turn(986, 2, 7);
    // 8-felt (~124-bit) continuity — the wide anchors chain (the single-felt PIs are retired to 0).
    assert_eq!(
        o81, n80,
        "turn 1 wide old8 == turn 0 wide new8 (~124-bit continuity)"
    );
    assert_eq!(
        o82, n81,
        "turn 2 wide old8 == turn 1 wide new8 (~124-bit continuity)"
    );
    assert!(
        n82.iter().any(|&x| x != BabyBear::ZERO),
        "the 8-felt wide commits are real (not the retired single-felt zeros)"
    );

    let turns = vec![t0, t1, t2];

    let summary = fold_wide_welded_umem_turn_chain_staged(&turns)
        .expect("a continuous 3-turn WIDE welded rotated+umem history must fold (host, 8-felt)");
    assert_eq!(summary.num_turns, 3);
    assert_eq!(summary.genesis_root8, o80);
    assert_eq!(summary.final_root8, n82);
    assert!(
        summary.chain_digest8.iter().any(|&x| x != BabyBear::ZERO),
        "the 8-felt ordered-history digest is a real ~124-bit Poseidon2 commitment"
    );
}

#[test]
fn wide_welded_umem_broken_order_rejected() {
    let (t0, _o0, _n0, _, _) = make_wide_welded_turn(1000, 0, 7);
    let (t1, _o1, _n1, _, _) = make_wide_welded_turn(993, 1, 7);
    let (t2, _o2, _n2, _, _) = make_wide_welded_turn(986, 2, 7);
    let mut turns = vec![t0, t1, t2];

    // A foreign turn whose 8-felt old anchor does NOT continue turn 0.
    let (foreign, _fo, _fn, foreign_old8, _foreign_new8) = make_wide_welded_turn(500, 50, 3);
    let prev_new8 = turns[0]
        .participant
        .rotated
        .wide_new_root8()
        .expect("turn 0 carries the 8-felt anchor");
    assert_ne!(
        foreign_old8, prev_new8,
        "the foreign WIDE welded turn must NOT continue the chain at the 8-felt anchor"
    );
    turns[1] = foreign;

    match fold_wide_welded_umem_turn_chain_staged(&turns) {
        Err(TurnChainError::WideChainBreak { index }) => assert_eq!(index, 1),
        Ok(_) => panic!("a broken WIDE welded order must not fold"),
        Err(other) => panic!("expected WideChainBreak at index 1, got {other:?}"),
    }
}

#[test]
fn wide_welded_umem_forged_post_commit_refused() {
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    let (t0, _o0, _n0, _, n80) = make_wide_welded_turn(1000, 0, 7);
    let (t1, _o1, _n1, o81, _n81) = make_wide_welded_turn(993, 1, 7);
    assert_eq!(
        o81, n80,
        "honest WIDE welded turns chain by construction (8-felt)"
    );

    // FORGE the 8-felt AFTER commit (the leg's LAST PI) on the LAST WIDE welded leg — the genuine
    // ~124-bit binding. The wide carrier PiBinding makes the welded proof UNSAT against the tampered
    // PI vector, so host admission refuses it.
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
    let forged_leg = RotatedParticipantLeg {
        proof,
        descriptor,
        public_inputs,
        custom_witness: None,
        bridge_witness: None,
    };
    let t1_forged = FinalizedTurn::new(DescriptorParticipant::rotated(forged_leg));
    let turns = [t0, t1_forged];

    match fold_wide_welded_umem_turn_chain_staged(&turns) {
        Err(TurnChainError::TurnProofInvalid { index, .. }) => assert_eq!(index, 1),
        Ok(_) => panic!("a forged WIDE welded 8-felt post-commit must not fold"),
        Err(other) => panic!("expected TurnProofInvalid at index 1, got {other:?}"),
    }
}

/// THE FULL IN-CIRCUIT RECURSIVE WIDE FOLD: the WIDE welded (umem-bearing) descriptor leaves
/// re-verify IN-CIRCUIT and aggregate to ONE whole-chain root whose exposed 8-felt segment is the
/// whole-chain claim `[genesis_root8, final_root8, num_turns, chain_digest]`, combined up the tree
/// with the 8-felt continuity (`prev.wide_new_root8 == next.wide_old_root8`) bound IN-CIRCUIT
/// lane-by-lane. The root verifies under its honest VK anchor — the genuine end-to-end in-circuit
/// IVC fold over the rotated+umem WIDE form (staged; the only remaining deployment step is the gated
/// VK epoch).
#[test]
#[ignore = "SLOW: real in-circuit recursion fold over WIDE welded leaves (the wide leg's 8-felt \
            carriers + umem tables make the in-circuit re-verify HEAVIER than the narrow recursive \
            leaf — minutes-to-tens-of-minutes; the minimal 2-turn fold already exercises leaf + the \
            8-felt continuity combine + root + verify); run with --ignored"]
fn wide_welded_umem_chain_folds_recursive() {
    // The MINIMAL multi-turn in-circuit fold: 2 wide welded leaves + ONE aggregation combine (which
    // binds the 8-felt continuity `prev.wide_new_root8 == next.wide_old_root8` lane-by-lane
    // IN-CIRCUIT) + the root + verify — the genuine end-to-end in-circuit wide fold.
    let (t0, _o0, _n0, o80, _n80) = make_wide_welded_turn(1000, 0, 7);
    let (t1, _o1, _n1, _o81, n81) = make_wide_welded_turn(993, 1, 7);
    let turns = vec![t0, t1];

    let whole = prove_wide_welded_umem_turn_chain_recursive_staged(&turns).expect(
        "a continuous 2-turn WIDE welded history must fold recursively (in-circuit, 8-felt)",
    );
    assert_eq!(whole.num_turns, 2);
    assert_eq!(
        whole.genesis_root8, o80,
        "the in-circuit root's 8-felt genesis is the first turn's wide_old_root8"
    );
    assert_eq!(
        whole.final_root8, n81,
        "the in-circuit root's 8-felt final root is the last turn's wide_new_root8"
    );
    assert!(
        whole.chain_digest.iter().any(|&x| x != BabyBear::ZERO),
        "the tree-folded ordered-history digest is a real ~124-bit Poseidon2 commitment"
    );

    // The WIDE segment tooth: the root's exposed 8-felt segment (built by construction from the
    // real wide descriptor leaves) must equal the carried claim under the honest VK anchor.
    let vk = whole.root_vk_fingerprint();
    verify_wide_turn_chain_recursive(&whole, &vk)
        .expect("the WIDE welded whole-chain root proof must verify under its honest anchor");
}

/// THE 8-FELT CONTINUITY TOOTH (recursive entry): a WIDE welded turn whose 8-felt
/// `wide_old_root8` does not continue the previous turn's `wide_new_root8` breaks the finalized
/// order and is refused at the wide continuity check — before any recursion proving. (The same
/// tooth is ALSO bound in-circuit at each aggregation node by lane-by-lane `connect`; this is the
/// fast host-side gate that catches the splice up front.)
#[test]
fn wide_welded_umem_recursive_broken_order_rejected() {
    let (t0, _o0, _n0, _, _) = make_wide_welded_turn(1000, 0, 7);
    let (t1, _o1, _n1, _, _) = make_wide_welded_turn(993, 1, 7);
    let (t2, _o2, _n2, _, _) = make_wide_welded_turn(986, 2, 7);
    let mut turns = vec![t0, t1, t2];

    let (foreign, _fo, _fn, foreign_old8, _foreign_new8) = make_wide_welded_turn(500, 50, 3);
    let prev_new8 = turns[0]
        .participant
        .rotated
        .wide_new_root8()
        .expect("turn 0 carries the 8-felt anchor");
    assert_ne!(
        foreign_old8, prev_new8,
        "the foreign WIDE welded turn must NOT continue the chain at the 8-felt anchor"
    );
    turns[1] = foreign;

    match prove_wide_welded_umem_turn_chain_recursive_staged(&turns) {
        Err(TurnChainError::WideChainBreak { index }) => assert_eq!(index, 1),
        Ok(_) => panic!("a broken WIDE welded order must not fold recursively"),
        Err(other) => panic!("expected WideChainBreak at index 1, got {other:?}"),
    }
}
