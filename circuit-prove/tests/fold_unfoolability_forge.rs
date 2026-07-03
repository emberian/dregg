//! FOLD-UNFOOLABILITY FORGE TEETH — an adversarial probe of `lightclient_unfoolable`.
//!
//! The apex (`Dregg2.Circuit.CircuitSoundness.lightclient_unfoolable`, and the whole-chain
//! `verify_turn_chain_recursive` it models) claims: a light client that RUNS NOTHING and only
//! verifies `(pi, π)` cannot be fooled — an accepting proof implies a GENUINE kernel transition.
//! This file attacks that claim along the three census-named axes and records where the tooth
//! bites and where the apex's stated scope holds:
//!
//!   (a) NON-GENUINE STEP that satisfies the descriptor — REFUTED elsewhere already
//!       (`ivc_turn_chain_rotated::ungated_prover_with_forged_post_commit_cannot_produce_a_root`:
//!       a forged rotated post-commit has no satisfying in-circuit leaf, so no verifying root).
//!       Not re-litigated here.
//!
//!   (c) CROSS-TURN SEAM (turn N+1's BEFORE not forced == turn N's AFTER) — REFUTED in-circuit.
//!       `prove_descriptor_leaf_rotated_with_segment` sources `first_old8`/`last_new8` from the
//!       descriptor proof's own `air_public_targets` over the FULL 8-lane wide anchor
//!       (`SEG_ANCHOR_WIDTH == 8`, `ivc_turn_chain.rs:1413-1445`), and `aggregate_tree` `connect`s
//!       all 8 lanes `l[SEG_LAST_NEW+k] == r[SEG_FIRST_OLD+k]`. `broken_order_rejected` +
//!       `mixed_root_forgery_executes_A_claims_B` are the committed teeth. Not re-litigated here.
//!
//!   (b) FRESHNESS / REPLAY / LIVENESS-OF-GENESIS — THE LIVE SEAM this file makes executable.
//!       `lightclient_unfoolable` is SINGLE-TRANSITION by its own admission (CircuitSoundness.lean
//!       :412-435): it takes `pi.turn` as GIVEN and establishes authenticity of ONE step, NOT
//!       freshness or ordering vs the live head. Lifted to the fold: `prove_turn_chain_recursive`
//!       (`ivc_turn_chain.rs:1977`) does per-turn descriptor admission + INTERNAL continuity
//!       (`prev.new_root == next.old_root`) and then sets `genesis_root = root_seg.first_old8` —
//!       i.e. turn[0]'s OWN before-state. NOTHING ties that genesis to any live/committed chain
//!       head. The fold artifact carries no liveness anchor.
//!
//!       The teeth below WITNESS that seam: a chain rooted at an ARBITRARY attacker-chosen "stale"
//!       genesis folds and verifies exactly like the live-head chain, and two DIFFERENT arbitrary
//!       genesis states verify under the SAME VK fingerprint. A pure light client (one that "RAN
//!       NOTHING") therefore cannot distinguish a fresh chain from a stale/replayed/fabricated-
//!       genesis one from the fold alone. This is NOT a break of the apex — the apex honestly
//!       scopes freshness OUT — it is the executable confirmation that freshness rides the DEPLOYED
//!       CAS (`proof_verify.rs`) + nonce-monotonicity (`CrossTurnFreshness.lean`, which itself
//!       names its runTurn-sequence residual), never the fold/apex. If a future change ever wires a
//!       liveness anchor INTO the fold, the `stale_genesis` assert flips from `is_ok()` to `is_err()`.
//!
//! The fold teeth run a REAL recursion fold (minutes); they are `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test fold_unfoolability_forge -- --ignored --nocapture

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, WholeChainProof, prove_turn_chain_recursive, verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

// ============================================================================
// The audited rotated-mint fixture (copied verbatim from
// `ivc_turn_chain_rotated.rs` — the Bucket-F mint pattern). A finalized turn
// carries the mandatory rotated multi-table `Ir2BatchProof` leg over before/after
// actor cells; the chain roots are the genuine 8-felt wide commitments (PI tail).
// ============================================================================

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

fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        None,
    )
    .expect("rotated transfer leg mints + self-verifies");
    let old_root = leg.wide_old_root8().expect("deployed leg is wide-anchored")[0];
    let new_root = leg.wide_new_root8().expect("deployed leg is wide-anchored")[0];
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
    )
}

/// Build a continuous chain of `k` real finalized turns from `(start_balance, start_nonce)`,
/// each debiting `step`. The v1 sub-trace bumps the nonce by 1 per Transfer, so both balance
/// and nonce advance per turn to keep the rotated roots linked (`old_root[i+1] == new_root[i]`).
fn make_chain(
    start_balance: u64,
    start_nonce: u32,
    step: u64,
    k: usize,
) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
    let mut turns = Vec::with_capacity(k);
    let mut balance = start_balance;
    let mut nonce = start_nonce;
    let mut genesis = BabyBear::ZERO;
    let mut final_root = BabyBear::ZERO;
    #[allow(clippy::explicit_counter_loop)]
    for i in 0..k {
        let (turn, old_root, new_root) = make_turn(balance, nonce, step);
        if i == 0 {
            genesis = old_root;
        } else {
            assert_eq!(old_root, final_root, "real chain must already link");
        }
        final_root = new_root;
        turns.push(turn);
        balance -= step;
        nonce += 1;
    }
    (turns, genesis, final_root)
}

// ============================================================================
// (b) THE FRESHNESS / LIVENESS-OF-GENESIS SEAM, MADE EXECUTABLE.
// ============================================================================

/// **THE STALE-GENESIS TOOTH.** A whole-chain fold rooted at an ARBITRARY attacker-chosen
/// genesis (a "stale" balance/nonce that is NOT tied to any live committed head) folds and
/// VERIFIES exactly like a live-head chain. The fold carries no freshness anchor: a pure light
/// client verifying only `(root, vk)` cannot tell this chain apart from the current one.
///
/// This ASSERTS ACCEPT deliberately: it is a WITNESS that freshness is OUT of the fold/apex
/// (honestly scoped at `CircuitSoundness.lean:412-435`), closed only by the deployed CAS. The
/// day a liveness anchor is wired INTO the fold, this `is_ok()` flips to `is_err()`.
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn stale_genesis_chain_still_verifies_no_freshness_anchor() {
    // A live-head chain would start from the CURRENT committed (balance, nonce). The attacker
    // instead picks an arbitrary stale/fabricated genesis — here a much older balance and a
    // nonce far below the live head. The fold neither knows nor checks the live head.
    let stale_start_balance = 424_242;
    let stale_start_nonce = 0; // a replayed-from-genesis nonce the live head is long past
    let (turns, stale_genesis, stale_final) =
        make_chain(stale_start_balance, stale_start_nonce, 7, 3);
    assert_eq!(turns.len(), 3);

    let whole: WholeChainProof = prove_turn_chain_recursive(&turns)
        .expect("a continuous stale-genesis chain folds — the fold has no liveness gate");
    let vk = whole.root_vk_fingerprint();

    // The genesis the artifact exposes is exactly the attacker's stale before-state.
    assert_eq!(whole.genesis_root[0], stale_genesis);
    assert_eq!(whole.final_root[0], stale_final);

    let verdict = verify_turn_chain_recursive(&whole, &vk);
    assert!(
        verdict.is_ok(),
        "FRESHNESS SEAM (live-gap, honestly scoped): a chain rooted at an ARBITRARY stale \
         genesis verifies under the fold with NO liveness anchor — the light client that RANS \
         NOTHING cannot distinguish it from the live-head chain. Freshness rides the deployed \
         CAS, not the fold/apex. got: {verdict:?}"
    );
}

/// **THE INDISTINGUISHABILITY TOOTH.** Two chains from DIFFERENT arbitrary genesis states verify
/// under the SAME VK fingerprint (same K, same shape). So a light client cannot even use the VK to
/// tell "the live-head chain" from "a stale/fabricated-genesis chain" — the only thing that could
/// distinguish them (which genesis is the live head) is precisely the datum the fold omits.
#[test]
#[ignore = "SLOW: two real recursion folds (~minutes); run with --ignored"]
fn two_arbitrary_genesis_chains_share_vk_and_both_verify() {
    let (turns_live, _lg, _lf) = make_chain(1000, 0, 7, 2);
    let (turns_stale, _sg, _sf) = make_chain(999_999, 500, 3, 2);

    let live = prove_turn_chain_recursive(&turns_live).expect("live-head chain folds");
    let stale = prove_turn_chain_recursive(&turns_stale).expect("stale-genesis chain folds");

    let vk_live = live.root_vk_fingerprint();
    let vk_stale = stale.root_vk_fingerprint();
    assert_eq!(
        vk_live, vk_stale,
        "same-shape K=2 chains share a root VK fingerprint, so the VK cannot distinguish a \
         live-head chain from a stale-genesis one"
    );

    verify_turn_chain_recursive(&live, &vk_live).expect("live chain verifies");
    // THE SEAM: the stale chain verifies under the SAME anchor the light client trusts.
    let verdict = verify_turn_chain_recursive(&stale, &vk_live);
    assert!(
        verdict.is_ok(),
        "a stale-genesis chain verifies under the SAME VK the light client trusts for the \
         live-head chain — freshness is not in the fold. got: {verdict:?}"
    );
}
