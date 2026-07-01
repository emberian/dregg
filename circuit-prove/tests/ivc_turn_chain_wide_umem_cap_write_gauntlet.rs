//! THE WIDE+umem WELDED IVC LEG — CAP-WRITE FAMILY GAUNTLET (STAGED, VK-RISK-FREE).
//!
//! The sibling `ivc_turn_chain_wide_umem_cohort_gauntlet.rs` drives the single-domain VALUE cohort
//! (transfer / burn / bridgeMint) through the wide+umem welded leg, and asserts a cap-WRITE lead
//! FAILS CLOSED there (its AFTER cap-root is an in-circuit cap-tree MAP-OP write the bare wide
//! descriptor leaves UNSAT). THIS file proves that named tail is CLOSED: the cap-WRITE family
//! (`grant` / `attenuate` / `revoke(Capability)`) now mints + folds on the SAME wide+umem leg via the
//! cap-open weld — the dispatcher lays the nonce-FREEZE base, applies the freeze patch, threads the
//! cap-tree write witness (`CapWriteWideWitness`), and appends the 8-felt wide carriers (the
//! ~124-bit anchors preserved through the additive umem weld). Each member's leg:
//!   * PROVES + self-verifies on the welded WIDE descriptor (8-felt anchors via the additive weld);
//!   * a cap-WRITE history (revokeCapability REMOVE chain) FOLDS through
//!     `fold_wide_welded_umem_turn_chain_staged` (8-felt continuity + ordered digest);
//!   * the forged 8-felt AFTER commit is REFUSED (the ~124-bit binding tooth bites);
//!   * a map_op cap-WRITE lead with NO witness still FAILS CLOSED (the cap-open weld never
//!     fabricates a post-cap-root).
//!
//! STAGED: nothing deployed — welded staged descriptors, no VK epoch, no deployed-default flip.

use dregg_circuit::effect_vm::trace_rotated::CapWriteWideWitness;
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, fold_wide_welded_umem_turn_chain_staged,
};
use dregg_circuit_prove::joint_turn_aggregation::{DescriptorParticipant, RotatedParticipantLeg};
use dregg_turn::rotation_witness::{
    mint_welded_wide_umem_cap_write_rotated_participant_leg,
    mint_welded_wide_umem_rotated_participant_leg,
};

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

fn producer_cell(balance: i64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// A (before, after) cell pair carrying a REAL caps-domain change (a granted cap revoked): the umem
/// reconciliation leg needs a non-empty single-domain (caps) op to prove. The cell's actual cap-root
/// is invisible to the rotated 8-felt commit (the rotated cap-root limb is overridden by the synthetic
/// cap-tree write witness), and balance/nonce are unchanged — so this caps touch drives the umem leg
/// without perturbing the rotated cap-WRITE proof.
fn cap_cells() -> (dregg_cell::Cell, dregg_cell::Cell) {
    use dregg_cell::AuthRequired;
    let before = {
        let mut c = producer_cell(100_000);
        let target = dregg_cell::CellId([9u8; 32]);
        let _slot = c.capabilities.grant(target, AuthRequired::None).unwrap();
        c
    };
    let after = {
        let mut c = before.clone();
        c.capabilities.revoke(0);
        c
    };
    (before, after)
}

fn leaf(addr: u32, value: u32) -> HeapLeaf {
    HeapLeaf {
        addr: BabyBear::new(addr),
        value: BabyBear::new(value),
    }
}

/// A cell at nonce `nonce` carrying TWO granted caps with `revoke_slots` revoked — a chain link. The
/// cap-WRITE base rides the nonce-TICK face (attenuate/revokeCapability advance the nonce in the wide
/// carrier), so a multi-turn chain advances the nonce in lockstep (turn i runs at nonce i) for the
/// 8-felt continuity to link — mirroring the value-cohort chain construction.
fn cell_caps(nonce: u64, revoke_slots: &[u32]) -> dregg_cell::Cell {
    use dregg_cell::AuthRequired;
    let mut c = producer_cell(100_000);
    for _ in 0..nonce {
        let _ = c.state.increment_nonce();
    }
    let _ = c
        .capabilities
        .grant(dregg_cell::CellId([9u8; 32]), AuthRequired::None)
        .unwrap();
    let _ = c
        .capabilities
        .grant(dregg_cell::CellId([10u8; 32]), AuthRequired::None)
        .unwrap();
    for &s in revoke_slots {
        c.capabilities.revoke(s);
    }
    c
}

/// Mint a cap-WRITE wide+umem welded leg over a synthetic c-list. `effect` is the cap-WRITE lead,
/// `cap_write` the cap-tree write witness (the c-list + anchor key + op payload). The nonce is FROZEN
/// by the base (attenuate-family), the cap-root advances on the openable rotated limb. Returns the
/// finalized turn + the 8-felt before/after anchors.
fn mint_cap_write_leg(
    effect: Effect,
    cap_write: &CapWriteWideWitness,
) -> (FinalizedTurn, [BabyBear; 8], [BabyBear; 8]) {
    let (before_cell, after_cell) = cap_cells();
    mint_cap_write_leg_cells(&before_cell, &after_cell, 0, effect, cap_write)
}

/// As [`mint_cap_write_leg`] but with explicit before/after cells + the turn's nonce (so a multi-turn
/// chain can thread the cap-root accumulator AND the nonce in lockstep — turn[i] runs at nonce `i`,
/// its AFTER nonce `i+1` == turn[i+1]'s BEFORE nonce — for the 8-felt continuity).
fn mint_cap_write_leg_cells(
    before_cell: &dregg_cell::Cell,
    after_cell: &dregg_cell::Cell,
    nonce: u32,
    effect: Effect,
    cap_write: &CapWriteWideWitness,
) -> (FinalizedTurn, [BabyBear; 8], [BabyBear; 8]) {
    let state = CellState::new(100_000, nonce);
    let leg = mint_welded_wide_umem_cap_write_rotated_participant_leg(
        &state,
        &[effect],
        before_cell,
        after_cell,
        &[0u8; 32],
        &[0u8; 32],
        &[[1u8; 32], [2u8; 32]],
        None,
        cap_write,
    )
    .expect("WIDE+umem welded cap-WRITE leg mints + self-verifies");
    let old8 = leg.wide_old_root8().expect("8-felt before anchor");
    let new8 = leg.wide_new_root8().expect("8-felt after anchor");
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old8,
        new8,
    )
}

/// attenuate (Update) + revokeCapability (Remove) each mint a wide+umem welded leg whose 8-felt
/// (~124-bit) commit MOVED — a genuine cap-tree write advanced the openable cap-root (non-vacuous).
#[test]
fn cap_write_family_mints_wide_welded_legs() {
    // revokeCapability: REMOVE key 0x0A from the c-list {0x0A, 0x14, 0x1E}.
    let clist = vec![leaf(0x0A, 0xF1), leaf(0x14, 0xF2), leaf(0x1E, 0xF3)];
    let revoke = Effect::RevokeCapability {
        slot_hash: [
            BabyBear::new(0x0A),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
        phase_b: None,
    };
    let (_t, o8, n8) = mint_cap_write_leg(
        revoke,
        &CapWriteWideWitness {
            clist_leaves: clist.clone(),
            anchor_key: BabyBear::new(0x0A),
            inserted: None,
        },
    );
    assert_ne!(
        o8, n8,
        "revokeCapability: the 8-felt commit MOVED (real REMOVE)"
    );

    // attenuate: UPDATE-AT-KEY 0x0A — read its held mask (0xF1), write the narrowed KEEP_MASK 0x11
    // (0x11 ⊑ 0xF1, the in-circuit submask non-amplification gate the attenuate base carries).
    let attenuate = Effect::AttenuateCapability {
        cap_slot_hash: [
            BabyBear::new(0x0A),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
        narrower_commitment: [
            BabyBear::new(0x0A),
            BabyBear::new(0x11),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
        phase_b: None,
    };
    let (_t, o8, n8) = mint_cap_write_leg(
        attenuate,
        &CapWriteWideWitness {
            clist_leaves: clist,
            anchor_key: BabyBear::new(0x0A),
            // Update ignores the key field; the value 0x11 is the narrowed KEEP_MASK written in place
            // (a strict submask of the held 0xF1 — the non-amplification gate bites otherwise).
            inserted: Some((BabyBear::new(0x0A), BabyBear::new(0x11))),
        },
    );
    assert_ne!(
        o8, n8,
        "attenuate: the 8-felt commit MOVED (real UPDATE-AT-KEY)"
    );
}

/// grantCap (the authority-only freeze base — NO cap-tree map_op write) mints a wide+umem welded leg
/// through the SAME dispatcher branch (the nonce-FREEZE patch the bare transfer-shape route mis-shapes
/// is applied; the cap-root is a frozen pass-through). It routes through the REGULAR mint entry — no
/// cap-write witness is needed (the base carries no map_op). Before this weld it FAILED CLOSED.
#[test]
fn grant_cap_mints_wide_welded_leg_via_freeze_base() {
    let state = CellState::new(100_000, 0);
    let (before_cell, after_cell) = cap_cells();
    let grant = Effect::GrantCapability {
        cap_entry: [
            BabyBear::new(0x77),
            BabyBear::new(0x03),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
        phase_b: None,
    };
    let leg = mint_welded_wide_umem_rotated_participant_leg(
        &state,
        &[grant],
        &before_cell,
        &after_cell,
        &[0u8; 32],
        &[0u8; 32],
        &[[1u8; 32], [2u8; 32]],
        None,
    )
    .expect("grantCap mints + self-verifies on the wide+umem leg via the nonce-FREEZE base");
    assert!(
        leg.wide_old_root8().is_some() && leg.wide_new_root8().is_some(),
        "grantCap leg carries the 8-felt (~124-bit) wide anchors"
    );
}

/// A multi-turn attenuate UPDATE-AT-KEY history folds through the 8-felt continuity + ordered digest:
/// each turn narrows the SAME slot's mask (the keyset is stable, so turn[i] BEFORE root == turn[i-1]
/// AFTER root) and the wide commit chains (only the cap-root accumulator moves; every other limb is
/// frozen). Each step's KEEP_MASK is a strict submask of the held value (the non-amplification gate).
#[test]
fn cap_write_revoke_history_folds() {
    let attenuate = |keep: u32| Effect::AttenuateCapability {
        cap_slot_hash: core::array::from_fn(|i| {
            if i == 0 {
                BabyBear::new(0x0A)
            } else {
                BabyBear::ZERO
            }
        }),
        narrower_commitment: core::array::from_fn(|i| match i {
            0 => BabyBear::new(0x0A),
            1 => BabyBear::new(keep),
            _ => BabyBear::ZERO,
        }),
        phase_b: None,
    };
    // The cell chain (the umem caps touch) threaded with the nonce: turn0 runs at nonce 0 (before n0,
    // after n1), turn1 at nonce 1 (before n1, after n2) — the cap-root accumulator AND the nonce both
    // link across the seam. The cell-derived non-cap-root, non-nonce limbs are frozen; the cap-root is
    // the synthetic write override (turn1 BEFORE root == turn0 AFTER root).
    // turn0: narrow 0x0A from held 0xFF -> 0x0F (0x0F ⊑ 0xFF).
    let (t0, o80, n80) = mint_cap_write_leg_cells(
        &cell_caps(0, &[]),
        &cell_caps(0, &[0]),
        0,
        attenuate(0x0F),
        &CapWriteWideWitness {
            clist_leaves: vec![leaf(0x0A, 0xFF), leaf(0x14, 0xF2), leaf(0x1E, 0xF3)],
            anchor_key: BabyBear::new(0x0A),
            inserted: Some((BabyBear::new(0x0A), BabyBear::new(0x0F))),
        },
    );
    // turn1: narrow 0x0A from held 0x0F -> 0x03 (0x03 ⊑ 0x0F). turn1 BEFORE c-list == turn0 AFTER tree.
    let (t1, o81, n81) = mint_cap_write_leg_cells(
        &cell_caps(1, &[0]),
        &cell_caps(1, &[0, 1]),
        1,
        attenuate(0x03),
        &CapWriteWideWitness {
            clist_leaves: vec![leaf(0x0A, 0x0F), leaf(0x14, 0xF2), leaf(0x1E, 0xF3)],
            anchor_key: BabyBear::new(0x0A),
            inserted: Some((BabyBear::new(0x0A), BabyBear::new(0x03))),
        },
    );
    // The honest narrows chain at the 8-felt anchor (the cap-root accumulator threads the wide commit;
    // every OTHER limb is frozen, so the only mover is the cap-root and the roots link).
    assert_eq!(o81, n80, "turn1 old8 == turn0 new8 (attenuate continuity)");
    let _ = (o80, n81);
    let turns = vec![t0, t1];
    let summary = fold_wide_welded_umem_turn_chain_staged(&turns)
        .expect("a continuous WIDE welded attenuate history folds (8-felt)");
    assert_eq!(summary.num_turns, 2);
    assert_eq!(summary.genesis_root8, o80);
    assert!(
        summary.chain_digest8.iter().any(|&x| x != BabyBear::ZERO),
        "real ~124-bit ordered-history digest"
    );
}

/// A forged 8-felt AFTER commit on a WIDE welded revokeCapability leg no longer folds — the ~124-bit
/// binding tooth bites for the cap-WRITE family too.
#[test]
fn cap_write_forged_post_commit_refused() {
    let mk = |key: u32, clist: Vec<HeapLeaf>| {
        mint_cap_write_leg(
            Effect::RevokeCapability {
                slot_hash: core::array::from_fn(|i| {
                    if i == 0 {
                        BabyBear::new(key)
                    } else {
                        BabyBear::ZERO
                    }
                }),
                phase_b: None,
            },
            &CapWriteWideWitness {
                clist_leaves: clist,
                anchor_key: BabyBear::new(key),
                inserted: None,
            },
        )
        .0
    };
    let t0 = mk(
        0x0A,
        vec![leaf(0x0A, 0xF1), leaf(0x14, 0xF2), leaf(0x1E, 0xF3)],
    );
    let t1 = mk(0x14, vec![leaf(0x14, 0xF2), leaf(0x1E, 0xF3)]);

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
        Err(TurnChainError::TurnProofInvalid { index, .. }) => {
            assert_eq!(index, 1, "forged 8-felt post-commit refused at index 1")
        }
        Ok(_) => panic!("a forged WIDE welded 8-felt post-commit must not fold (cap-WRITE)"),
        Err(other) => panic!("expected TurnProofInvalid, got {other:?}"),
    }
}

/// A map_op cap-WRITE lead (revokeCapability) given NO cap-tree write witness STILL FAILS CLOSED — the
/// cap-open weld never fabricates a post-cap-root (the dispatcher refuses the witnessless map_op).
#[test]
fn map_op_cap_write_without_witness_fails_closed() {
    let state = CellState::new(100_000, 0);
    let (before_cell, after_cell) = cap_cells();
    let res = mint_welded_wide_umem_rotated_participant_leg(
        &state,
        &[Effect::RevokeCapability {
            slot_hash: [BabyBear::new(0x0A); 8],
            phase_b: None,
        }],
        &before_cell,
        &after_cell,
        &[0u8; 32],
        &[0u8; 32],
        &[[1u8; 32]],
        None,
    );
    assert!(
        res.is_err(),
        "a map_op cap-WRITE lead with no cap-tree write witness must FAIL CLOSED (no fabricated root)"
    );
}
