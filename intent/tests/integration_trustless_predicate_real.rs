//! Integration test: trustless engine rejects garbage proofs through the
//! WitnessedProofVerifier / WitnessedPredicateRegistry surface.
//!
//! # Why this test exists
//!
//! `TrustlessIntentEngine::new` installs the STRICT
//! `WitnessedProofVerifier::strict(default_builtins())` as its default verifier
//! (SILVER-DEBT T1.2 fail-open: CLOSED). A submission that omits its
//! `witnessed_predicate` is REJECTED — the prior permissive fallback that waved
//! garbage proof bytes through on the structural check alone is gone. When a
//! predicate IS present, the proof dispatches through the registry, which
//! installs `NotYetWiredVerifier` (fail-closed) for kinds without a real
//! algebra adapter.
//!
//! These tests:
//!   A. Prove that garbage-proof submissions WITHOUT a witnessed predicate are
//!      REJECTED by the strict production default (the closed-hole regression gate).
//!   B. Prove that garbage-proof submissions WITH a witnessed predicate are REJECTED
//!      by strict mode regardless of proof content.
//!   C. Prove that a fully-formed submission is accepted by a custom AcceptAll
//!      verifier only after it passes the batch-binding audience check — a
//!      manipulated binding (wrong commitment) is still rejected.
//!   D. Prove that a `RejectAll` custom verifier causes rejection even when every
//!      structural property is correct — confirming the registry is actually
//!      called (not short-circuited by the stub path).

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
use dregg_intent::{ActionPattern, CommitmentId, Intent, IntentId, IntentKind, MatchSpec};

// ============================================================================
// Shared helpers (mirrors the inline helpers in trustless.rs unit tests)
// ============================================================================

fn make_keys(threshold: u8, n: u8) -> (ThresholdEncryptionKey, Vec<KeyShare>) {
    generate_epoch_key([0xEEu8; 32], threshold, n)
}

fn make_intent(seed: u8) -> Intent {
    let spec = MatchSpec {
        actions: vec![ActionPattern {
            action: Some(format!("act_{seed}")),
            resource: None,
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: None,
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };
    Intent::new(
        IntentKind::Offer,
        spec,
        CommitmentId([seed; 32]),
        9999,
        None,
    )
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
    // Pre-fund every byte-prefix solver id used by tests.
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

fn make_structural_submission(
    solver_byte: u8,
    intents: &[Intent],
    score: f64,
    proof: Vec<u8>,
    predicate: Option<WitnessedPredicate>,
) -> SolverSubmission {
    let participants: Vec<IntentId> = intents.iter().map(|i| i.id).collect();
    let settlements: Vec<Settlement> = intents
        .iter()
        .enumerate()
        .map(|(i, intent)| Settlement {
            from: intent.creator,
            to: intents[(i + 1) % intents.len()].creator,
            asset: [i as u8; 32],
            amount: 100,
        })
        .collect();
    let ring = RingTrade {
        participants,
        settlements,
        score,
    };
    SolverSubmission {
        solver_id: [solver_byte; 32],
        solution: vec![ring],
        total_score: score,
        validity_proof: proof,
        witnessed_predicate: predicate,
        bond: DEFAULT_MIN_SOLVER_BOND,
        submitted_at: 10,
    }
}

fn witnessed_predicate_for(intents: &[Intent], kind: WitnessedPredicateKind) -> WitnessedPredicate {
    let commitment = WitnessedProofVerifier::compute_batch_binding(intents);
    WitnessedPredicate {
        kind,
        commitment,
        input_ref: InputRef::PublicInput { pi_index: 0 },
        proof_witness_index: 0,
    }
}

// ============================================================================
// Test A: Production default REJECTS a garbage proof WITHOUT a predicate.
//   (SILVER-DEBT T1.2 fail-open: CLOSED. The default `TrustlessIntentEngine::new`
//    now installs the STRICT verifier, so a predicate-less submission is rejected
//    rather than waved through on the structural check alone.)
// ============================================================================

#[test]
fn default_engine_rejects_garbage_proof_without_predicate() {
    let (key, shares) = make_keys(2, 3);
    let mut engine = TrustlessIntentEngine::new(2, 3);
    let intents = vec![make_intent(1), make_intent(2)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    // Garbage proof (still non-empty so the empty-proof guard passes).
    // No witnessed_predicate — the strict production default must reject this;
    // the garbage proof bytes are never accepted on the structural check alone.
    let garbage: Vec<u8> = (0..32u8).collect();
    let sub = make_structural_submission(0xAA, &intents, 5.0, garbage, None);

    let result = engine.submit_solution(sub);
    assert!(
        matches!(result, Err(EngineError::InvalidProof { .. })),
        "HOLE CLOSED: strict production default must REJECT a predicate-less \
         submission (garbage proof bytes never verified otherwise), got: {result:?}"
    );
}

// ============================================================================
// Test B: Strict mode rejects garbage proof even with correct structure
// ============================================================================

#[test]
fn strict_verifier_rejects_submission_without_predicate() {
    use dregg_intent::trustless::WitnessedProofVerifier;

    let reg = WitnessedPredicateRegistry::with_stubs();
    let (key, shares) = make_keys(2, 3);
    let mut engine =
        TrustlessIntentEngine::with_verifier(2, 3, Box::new(WitnessedProofVerifier::strict(reg)));
    let intents = vec![make_intent(1), make_intent(2)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    let garbage: Vec<u8> = (0..32u8).collect();
    let sub = make_structural_submission(0xAA, &intents, 5.0, garbage, None);

    // Strict verifier must reject — missing witnessed_predicate.
    let result = engine.submit_solution(sub);
    assert!(
        matches!(result, Err(EngineError::InvalidProof { .. })),
        "strict verifier must reject submission without witnessed_predicate, got: {result:?}"
    );
}

// ============================================================================
// Test C: AcceptAll custom verifier — garbage proof WITH correct binding accepted,
//         but tampered batch binding is still rejected (audience check fires first).
// ============================================================================

struct AcceptAll;
impl WpVerifier for AcceptAll {
    fn name(&self) -> &'static str {
        "test-accept-all-garbage"
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
        Ok(()) // accepts anything
    }
}

#[test]
fn accept_all_verifier_accepts_garbage_with_correct_binding() {
    let mut reg = WitnessedPredicateRegistry::with_stubs();
    reg.register_custom([0xAC; 32], Arc::new(AcceptAll));

    let (key, shares) = make_keys(2, 3);
    let mut engine =
        TrustlessIntentEngine::with_verifier(2, 3, Box::new(WitnessedProofVerifier::new(reg)));
    let intents = vec![make_intent(3), make_intent(4)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    let garbage: Vec<u8> = (0..32u8).rev().collect();
    let wp = witnessed_predicate_for(
        &intents,
        WitnessedPredicateKind::Custom {
            vk_hash: [0xAC; 32],
        },
    );
    let sub = make_structural_submission(0xBB, &intents, 3.0, garbage, Some(wp));

    engine
        .submit_solution(sub)
        .expect("AcceptAll verifier should accept garbage proof when binding is correct");
    assert_eq!(engine.winning_score(), Some(3.0));
}

#[test]
fn accept_all_verifier_rejects_tampered_batch_binding() {
    let mut reg = WitnessedPredicateRegistry::with_stubs();
    reg.register_custom([0xAC; 32], Arc::new(AcceptAll));

    let (key, shares) = make_keys(2, 3);
    let mut engine =
        TrustlessIntentEngine::with_verifier(2, 3, Box::new(WitnessedProofVerifier::new(reg)));
    let intents = vec![make_intent(5), make_intent(6)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    let garbage: Vec<u8> = vec![0xDE, 0xAD];
    let mut wp = witnessed_predicate_for(
        &intents,
        WitnessedPredicateKind::Custom {
            vk_hash: [0xAC; 32],
        },
    );
    // Tamper: overwrite the commitment so it no longer matches the batch.
    wp.commitment = [0xFF; 32];
    let sub = make_structural_submission(0xCC, &intents, 4.0, garbage, Some(wp));

    let result = engine.submit_solution(sub);
    assert!(
        matches!(result, Err(EngineError::InvalidProof { ref reason }) if reason.contains("batch binding")),
        "tampered binding must be rejected even by AcceptAll verifier, got: {result:?}"
    );
}

// ============================================================================
// Test D: RejectAll custom verifier — correct structure + correct binding still fails
// ============================================================================

struct RejectAll;
impl WpVerifier for RejectAll {
    fn name(&self) -> &'static str {
        "test-reject-all"
    }
    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: [0xDE; 32],
        }
    }
    fn verify(
        &self,
        _commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        _proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        Err(WitnessedPredicateError::Rejected {
            kind_name: "RejectAll".into(),
            reason: "adversarial verifier always rejects".into(),
        })
    }
}

#[test]
fn reject_all_verifier_is_actually_called() {
    // If the registry dispatch were short-circuited (e.g. stubs shadow custom
    // kinds), a RejectAll verifier would never be invoked and the submission
    // would spuriously succeed. This test confirms the opposite.
    let mut reg = WitnessedPredicateRegistry::with_stubs();
    reg.register_custom([0xDE; 32], Arc::new(RejectAll));

    let (key, shares) = make_keys(2, 3);
    let mut engine =
        TrustlessIntentEngine::with_verifier(2, 3, Box::new(WitnessedProofVerifier::new(reg)));
    let intents = vec![make_intent(7), make_intent(8)];
    drive_to_solving(&mut engine, &key, &shares, &intents);

    let proof_bytes = vec![0xAB, 0xCD, 0xEF];
    let wp = witnessed_predicate_for(
        &intents,
        WitnessedPredicateKind::Custom {
            vk_hash: [0xDE; 32],
        },
    );
    let sub = make_structural_submission(0xDD, &intents, 6.0, proof_bytes, Some(wp));

    let result = engine.submit_solution(sub);
    assert!(
        matches!(result, Err(EngineError::InvalidProof { ref reason }) if reason.contains("adversarial")),
        "RejectAll verifier must be reached and its rejection propagated; got: {result:?}"
    );
}
