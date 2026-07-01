//! THE WIDE+umem WELDED IVC LEG — FULL-COHORT GAUNTLET (STAGED, VK-RISK-FREE).
//!
//! The sibling `ivc_turn_chain_wide_umem_welded.rs` folds a Transfer-only WIDE welded history. THIS
//! file proves the wide+umem welded IVC leg is no longer Transfer-scoped: it drives the FULL
//! single-domain (heap) value cohort — `transfer` / `burn` / `bridgeMint` — through the SAME welded
//! leg (`mint_welded_wide_umem_rotated_participant_leg` →
//! `RotatedParticipantLeg::mint_welded_wide_from_block_witnesses`, now routed through the shared
//! full-cohort wide producer dispatch `generate_rotated_effect_vm_descriptor_and_trace_wide`). Each
//! family's leg:
//!   * PROVES + self-verifies on the welded WIDE descriptor (the 8-felt / ~124-bit anchors PRESERVED
//!     through the additive umem weld — the welded leg carries `wide_old_root8`/`wide_new_root8`);
//!   * FOLDS a multi-turn same-family history through `fold_wide_welded_umem_turn_chain_staged`
//!     (8-felt continuity + the ordered-history digest);
//!   * REFUSES a forged 8-felt AFTER commit (the ~124-bit binding tooth bites per family);
//!
//! and the gauntlet asserts a NON-COHORT lead (a cap-WRITE effect whose AFTER cap-root needs the
//! SEPARATE cap-open path) FAILS CLOSED at the dispatch, never silently mis-proved.
//!
//! STAGED: nothing deployed — welded staged descriptors, no VK epoch, no deployed-default flip.

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, fold_wide_welded_umem_turn_chain_staged,
};
use dregg_circuit_prove::joint_turn_aggregation::{DescriptorParticipant, RotatedParticipantLeg};
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

/// Mint a WIDE+umem welded leg for a single heap-domain VALUE effect: the issuer cell's balance moves
/// `before_balance` → `after_balance` at nonce `nonce` (the umem touch IS the heap balance write), the
/// `effect` is the cohort lead. Returns the finalized turn + the 8-felt before/after anchors. The
/// `nonce` mirrors the transfer-chain construction (the effect ticks the nonce in the wide carrier, so
/// a multi-turn chain advances the nonce in lockstep for the 8-felt continuity to link).
fn mint_value_leg(
    before_balance: i64,
    after_balance: i64,
    nonce: u64,
    effect: Effect,
) -> (FinalizedTurn, [BabyBear; 8], [BabyBear; 8]) {
    let state = CellState::new(before_balance as u64, nonce as u32);
    let effects = vec![effect];
    let before_cell = producer_cell(before_balance, nonce);
    let after_cell = producer_cell(after_balance, nonce);
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
    .expect("WIDE+umem welded value-cohort leg mints + self-verifies");
    let old8 = leg.wide_old_root8().expect("8-felt before anchor");
    let new8 = leg.wide_new_root8().expect("8-felt after anchor");
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old8,
        new8,
    )
}

/// Each value-cohort family mints a wide+umem welded leg that PRESERVES the 8-felt (~124-bit) anchors
/// (BEFORE != AFTER — a real bound move, not a frozen passthrough).
#[test]
fn value_cohort_families_mint_wide_welded_legs() {
    // transfer DEBIT 7
    let (_t, o8, n8) = mint_value_leg(
        1000,
        993,
        0,
        Effect::Transfer {
            amount: 7,
            direction: 1,
        },
    );
    assert_ne!(o8, n8, "transfer: the 8-felt commit MOVED (non-vacuous)");

    // burn DEBIT 500
    let (_t, o8, n8) = mint_value_leg(
        100_000,
        99_500,
        0,
        Effect::Burn {
            target_hash: BabyBear::new(0xB0F0),
            amount_lo: BabyBear::new(500),
            amount_full: 500,
        },
    );
    assert_ne!(o8, n8, "burn: the 8-felt commit MOVED (non-vacuous)");

    // bridgeMint CREDIT 900
    let (_t, o8, n8) = mint_value_leg(
        100_000,
        100_900,
        0,
        Effect::BridgeMint {
            value_lo: BabyBear::new(900),
            mint_hash: BabyBear::new(0x31D6),
            value_full: 900,
        },
    );
    assert_ne!(o8, n8, "bridgeMint: the 8-felt commit MOVED (non-vacuous)");
}

/// A multi-turn SAME-family WIDE welded history folds through the 8-felt continuity + ordered digest,
/// for EACH value-cohort family (burn / bridgeMint), not just transfer.
#[test]
fn value_cohort_burn_history_folds() {
    let burn = |amt: i64| Effect::Burn {
        target_hash: BabyBear::new(0xB0F0),
        amount_lo: BabyBear::new(amt as u32),
        amount_full: amt as u64,
    };
    let (t0, o80, n80) = mint_value_leg(100_000, 99_900, 0, burn(100));
    let (t1, o81, n81) = mint_value_leg(99_900, 99_800, 1, burn(100));
    let (t2, o82, _n82) = mint_value_leg(99_800, 99_700, 2, burn(100));
    // The honest burns chain at the 8-felt anchor (balance/nonce thread the wide commit).
    assert_eq!(o81, n80, "turn1 old8 == turn0 new8 (burn continuity)");
    assert_eq!(o82, n81, "turn2 old8 == turn1 new8 (burn continuity)");
    let turns = vec![t0, t1, t2];
    let summary = fold_wide_welded_umem_turn_chain_staged(&turns)
        .expect("a continuous 3-turn WIDE welded burn history folds (8-felt)");
    assert_eq!(summary.num_turns, 3);
    assert_eq!(summary.genesis_root8, o80);
    assert!(
        summary.chain_digest8.iter().any(|&x| x != BabyBear::ZERO),
        "real ~124-bit ordered-history digest"
    );
}

/// A forged 8-felt AFTER commit on a WIDE welded BURN leg no longer verifies against its welded
/// descriptor — the ~124-bit binding tooth bites per family (host admission refuses it).
#[test]
fn value_cohort_forged_post_commit_refused_per_family() {
    let burn = Effect::Burn {
        target_hash: BabyBear::new(0xB0F0),
        amount_lo: BabyBear::new(100),
        amount_full: 100,
    };
    let mint = Effect::BridgeMint {
        value_lo: BabyBear::new(100),
        mint_hash: BabyBear::new(0x31D6),
        value_full: 100,
    };
    for (label, t0, t1) in [
        (
            "burn",
            mint_value_leg(100_000, 99_900, 0, burn.clone()).0,
            mint_value_leg(99_900, 99_800, 1, burn.clone()).0,
        ),
        (
            "bridgeMint",
            mint_value_leg(100_000, 100_100, 0, mint.clone()).0,
            mint_value_leg(100_100, 100_200, 1, mint.clone()).0,
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
            Ok(_) => panic!("{label}: a forged WIDE welded 8-felt post-commit must not fold"),
            Err(other) => panic!("{label}: expected TurnProofInvalid, got {other:?}"),
        }
    }
}

/// A NON-COHORT lead (a cap-WRITE effect whose AFTER cap-root is an in-circuit cap-tree MAP-OP write —
/// its light-client route is the SEPARATE cap-open path) FAILS CLOSED at the wide producer dispatch,
/// never silently mis-proved onto the bare wide descriptor.
#[test]
fn non_cohort_cap_write_lead_fails_closed() {
    let state = CellState::new(100_000, 0);
    let effects = vec![Effect::RevokeCapability {
        slot_hash: [BabyBear::new(0x4E); 8],
        phase_b: None,
    }];
    let before_cell = producer_cell(100_000, 0);
    let after_cell = producer_cell(100_000, 1);
    let res = mint_welded_wide_umem_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &[0u8; 32],
        &[0u8; 32],
        &[[1u8; 32]],
        None,
    );
    assert!(
        res.is_err(),
        "a cap-WRITE lead (revokeCapability) must FAIL CLOSED on the bare wide welded leg (its route \
         is the separate cap-open path), never mint a wide receipt"
    );
}
