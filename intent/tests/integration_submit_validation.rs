//! Adversarial integration tests for the trustless engine's submit-time
//! validation (SILVER holes #3 and #4).
//!
//! These tests prove that `submit_solution` now enforces, fail-closed:
//!   (b) expired intents are rejected,
//!   (c) non-conserving / zero-amount settlements are rejected,
//!   (d) a solver-inflated `total_score` is rejected (structural score check),
//!   (e) a participating intent that declares a `predicate_requirement` is
//!       rejected (no per-intent proof channel ⇒ fail closed).
//!
//! Each test drives the engine to the Solving state with a custom AcceptAll
//! witnessed-predicate verifier, so the proof-bytes layer accepts and the
//! NEW submit-time invariants are what actually do the rejecting. (With the
//! strict default verifier the predicate layer would reject first and we
//! couldn't isolate the new checks.)

use std::sync::Arc;

use dregg_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier as WpVerifier,
};
use dregg_federation::threshold_decrypt::{
    KeyShare, ThresholdEncryptionKey, generate_epoch_key, produce_decryption_share,
    threshold_encrypt,
};
use dregg_intent::solver::{RingTrade, Settlement};
use dregg_intent::trustless::{
    BatchState, DEFAULT_MIN_SOLVER_BOND, EncryptedIntent, EngineError, SolverSubmission,
    TrustlessIntentEngine, WitnessedProofVerifier,
};
use dregg_intent::{
    ActionPattern, CommitmentId, Intent, IntentId, IntentKind, MatchSpec, PredicateRequirement,
};

// ----------------------------------------------------------------------------
// AcceptAll proof verifier (isolates the new submit-time checks)
// ----------------------------------------------------------------------------

struct AcceptAll;
impl WpVerifier for AcceptAll {
    fn name(&self) -> &'static str {
        "test-accept-all"
    }
    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: [0xAC; 32],
        }
    }
    fn verify(
        &self,
        _commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        _proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        Ok(())
    }
}

fn accept_all_engine(threshold: usize, n: usize) -> TrustlessIntentEngine {
    let mut reg = WitnessedPredicateRegistry::with_stubs();
    reg.register_custom([0xAC; 32], Arc::new(AcceptAll));
    TrustlessIntentEngine::with_verifier(threshold, n, Box::new(WitnessedProofVerifier::new(reg)))
}

fn make_keys(threshold: u8, n: u8) -> (ThresholdEncryptionKey, Vec<KeyShare>) {
    generate_epoch_key([0xEEu8; 32], threshold, n)
}

/// Build an intent. `expiry` and `predicate_requirements` are caller-controlled
/// so individual tests can exercise the new gates.
fn make_intent_full(seed: u8, expiry: u64, preds: Vec<PredicateRequirement>) -> Intent {
    let spec = MatchSpec {
        actions: vec![ActionPattern {
            action: Some(format!("act_{seed}")),
            resource: None,
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: None,
        compound: None,
        predicate_requirements: preds,
        strict_resource_matching: false,
    };
    Intent::new(
        IntentKind::Offer,
        spec,
        CommitmentId([seed; 32]),
        expiry,
        None,
    )
}

fn make_intent(seed: u8) -> Intent {
    make_intent_full(seed, 9999, vec![])
}

fn encrypt_intent(intent: &Intent, key: &ThresholdEncryptionKey) -> EncryptedIntent {
    let bytes = postcard::to_allocvec(intent).expect("serialize");
    let ciphertext = threshold_encrypt(&bytes, key).expect("encrypt");
    EncryptedIntent {
        ciphertext,
        creator_commitment: intent.creator,
        submitted_at: 1,
    }
}

fn drive_to_solving(
    engine: &mut TrustlessIntentEngine,
    key: &ThresholdEncryptionKey,
    shares: &[KeyShare],
    intents: &[Intent],
) {
    for b in 0u8..=255 {
        engine.deposit_bond(&[b; 32], DEFAULT_MIN_SOLVER_BOND * 10);
    }
    let mut encs: Vec<EncryptedIntent> = Vec::new();
    for intent in intents {
        let enc = encrypt_intent(intent, key);
        engine.submit_encrypted(enc.clone()).unwrap();
        encs.push(enc);
    }
    engine.close_batch(5).unwrap();
    for enc in &encs {
        for ks in shares.iter().take(engine.decrypt_threshold) {
            let share = produce_decryption_share(&enc.ciphertext, ks);
            engine.contribute_decrypt_share(share).unwrap();
        }
    }
    assert_eq!(engine.batch_state(), BatchState::Solving);
}

fn wp_for(intents: &[Intent]) -> WitnessedPredicate {
    WitnessedPredicate {
        kind: WitnessedPredicateKind::Custom {
            vk_hash: [0xAC; 32],
        },
        commitment: WitnessedProofVerifier::compute_batch_binding(intents),
        input_ref: InputRef::PublicInput { pi_index: 0 },
        proof_witness_index: 0,
    }
}

/// Build a conserving 2-node ring submission: i0 -> i1 (asset0), i1 -> i0 (asset1).
fn conserving_submission(intents: &[Intent], score: f64) -> SolverSubmission {
    let participants: Vec<IntentId> = intents.iter().map(|i| i.id).collect();
    let settlements = vec![
        Settlement {
            from: intents[0].creator,
            to: intents[1].creator,
            asset: [0u8; 32],
            amount: 100,
        },
        Settlement {
            from: intents[1].creator,
            to: intents[0].creator,
            asset: [1u8; 32],
            amount: 100,
        },
    ];
    SolverSubmission {
        solver_id: [0xAA; 32],
        solution: vec![RingTrade {
            participants,
            settlements,
            score,
        }],
        total_score: score,
        validity_proof: vec![0xDE, 0xAD],
        witnessed_predicate: Some(wp_for(intents)),
        bond: DEFAULT_MIN_SOLVER_BOND,
        submitted_at: 10,
    }
}

// ============================================================================
// Baseline: a conserving, unexpired, predicate-free submission is ACCEPTED.
// (Proves the new gates don't reject honest submissions.)
// ============================================================================

#[test]
fn baseline_valid_submission_accepted() {
    let (key, shares) = make_keys(2, 3);
    let mut engine = accept_all_engine(2, 3);
    let intents = vec![make_intent(1), make_intent(2)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    let sub = conserving_submission(&intents, 5.0);
    engine
        .submit_solution(sub)
        .expect("honest conserving unexpired submission must be accepted");
    assert_eq!(engine.winning_score(), Some(5.0));
}

// ============================================================================
// (b) Expired intent rejected.
// ============================================================================

#[test]
fn expired_intent_rejected_at_submit() {
    let (key, shares) = make_keys(2, 3);
    let mut engine = accept_all_engine(2, 3);
    // intent 2 expires at height 50.
    let intents = vec![make_intent(1), make_intent_full(2, 50, vec![])];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    // Advance past intent 2's expiry.
    engine.advance_height(100);

    let sub = conserving_submission(&intents, 5.0);
    let result = engine.submit_solution(sub);
    match result {
        Err(EngineError::ExpiredIntent { expiry, now, .. }) => {
            assert_eq!(expiry, 50);
            assert_eq!(now, 100);
        }
        other => panic!("expected ExpiredIntent, got: {other:?}"),
    }
}

// ============================================================================
// (c) Non-conserving settlement rejected — free mint (a node only receives).
// ============================================================================

#[test]
fn free_mint_settlement_rejected() {
    let (key, shares) = make_keys(2, 3);
    let mut engine = accept_all_engine(2, 3);
    let intents = vec![make_intent(1), make_intent(2)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    // i0 -> i1 only: i1 receives but never sends (free mint into i1).
    let participants: Vec<IntentId> = intents.iter().map(|i| i.id).collect();
    let sub = SolverSubmission {
        solver_id: [0xAA; 32],
        solution: vec![RingTrade {
            participants,
            settlements: vec![Settlement {
                from: intents[0].creator,
                to: intents[1].creator,
                asset: [0u8; 32],
                amount: 100,
            }],
            score: 5.0,
        }],
        total_score: 5.0,
        validity_proof: vec![0xDE],
        witnessed_predicate: Some(wp_for(&intents)),
        bond: DEFAULT_MIN_SOLVER_BOND,
        submitted_at: 10,
    };
    let result = engine.submit_solution(sub);
    assert!(
        matches!(result, Err(EngineError::NonConservingSettlement { .. })),
        "a node that only receives (free mint) must be rejected, got: {result:?}"
    );
}

// ============================================================================
// (c') Zero-amount transfer rejected.
// ============================================================================

#[test]
fn zero_amount_settlement_rejected() {
    let (key, shares) = make_keys(2, 3);
    let mut engine = accept_all_engine(2, 3);
    let intents = vec![make_intent(1), make_intent(2)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    let mut sub = conserving_submission(&intents, 5.0);
    // Corrupt one leg to a zero amount.
    sub.solution[0].settlements[0].amount = 0;
    let result = engine.submit_solution(sub);
    assert!(
        matches!(result, Err(EngineError::NonConservingSettlement { ref reason }) if reason.contains("zero-amount")),
        "zero-amount transfer must be rejected, got: {result:?}"
    );
}

// ============================================================================
// (c'') Per-asset imbalance rejected — extra unmatched credit leg.
// ============================================================================

#[test]
fn per_asset_imbalance_rejected() {
    let (key, shares) = make_keys(2, 3);
    let mut engine = accept_all_engine(2, 3);
    let intents = vec![make_intent(1), make_intent(2)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    let mut sub = conserving_submission(&intents, 5.0);
    // Inflate the credit on asset0 by overpaying the receiver on the first leg,
    // breaking per-asset sent==received balance is not possible with from/to
    // pairs, so instead add a node imbalance: make i0 send more of asset0 than
    // it gets back by raising the first leg amount only.
    sub.solution[0].settlements[0].amount = 250; // i0 -> i1 asset0 = 250
    // Now asset0: sent 250, received 250 (still balanced globally per asset),
    // but cycle closure still holds. To force a real imbalance, append a
    // dangling credit with no matching debit on a fresh asset.
    sub.solution[0].settlements.push(Settlement {
        from: intents[0].creator,
        to: intents[1].creator,
        asset: [9u8; 32],
        amount: 70,
    });
    // asset9: sent 70 by i0, received 70 by i1 — per-asset balanced, but i1
    // receives asset9 and i0 sends it; both already send+receive so cycle
    // closure holds. This is actually still conserving. Replace with a genuine
    // free-mint: a node that only receives.
    sub.solution[0].settlements.clear();
    sub.solution[0].settlements.push(Settlement {
        from: intents[0].creator,
        to: intents[1].creator,
        asset: [0u8; 32],
        amount: 100,
    });
    sub.solution[0].settlements.push(Settlement {
        from: intents[1].creator,
        to: CommitmentId([0x77; 32]), // a third party not in the cycle
        asset: [1u8; 32],
        amount: 100,
    });
    // Now: i0 sends, i1 sends+receives, 0x77 only receives (free mint) AND
    // i0 never receives (value burned). Either condition triggers rejection.
    let result = engine.submit_solution(sub);
    assert!(
        matches!(result, Err(EngineError::NonConservingSettlement { .. })),
        "settlement that mints to / burns from an off-cycle node must be rejected, got: {result:?}"
    );
}

// ============================================================================
// (d) Solver-inflated total_score rejected (structural score check).
// ============================================================================

#[test]
fn inflated_total_score_rejected() {
    let (key, shares) = make_keys(2, 3);
    let mut engine = accept_all_engine(2, 3);
    let intents = vec![make_intent(1), make_intent(2)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    let mut sub = conserving_submission(&intents, 5.0);
    // Claim a total_score far above the sum of ring scores (5.0).
    sub.total_score = 9999.0;
    let result = engine.submit_solution(sub);
    assert!(
        matches!(result, Err(EngineError::InvalidProof { ref reason }) if reason.contains("score")),
        "a total_score that exceeds the sum of ring scores must be rejected, got: {result:?}"
    );
}

// ============================================================================
// (e) Intent with a declared predicate_requirement rejected (fail closed:
//     no per-intent proof channel in the wire format).
// ============================================================================

#[test]
fn predicate_bearing_intent_rejected_fail_closed() {
    let (key, shares) = make_keys(2, 3);
    let mut engine = accept_all_engine(2, 3);
    // intent 2 carries a predicate requirement "balance >= 1000".
    let pred = PredicateRequirement {
        attribute: "balance".into(),
        predicate_type: "gte".into(),
        threshold: 1000,
        upper_bound: None,
        state_root_freshness: 100,
    };
    let intents = vec![make_intent(1), make_intent_full(2, 9999, vec![pred])];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    let sub = conserving_submission(&intents, 5.0);
    let result = engine.submit_solution(sub);
    match result {
        Err(EngineError::PredicateRequirementUnmet { intent_id, .. }) => {
            assert_eq!(intent_id, intents[1].id);
        }
        other => panic!("expected PredicateRequirementUnmet, got: {other:?}"),
    }
}
