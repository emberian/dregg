//! DeFi primitives integration tests: partial fills, value conservation, cross-state derivation.
//!
//! Tests the financial primitives that underpin the intent matching and
//! privacy-preserving transfer systems:
//! 1. Partial fills: intent with min/max, partial fill produces residual
//! 2. Commit-reveal fulfillment: commit → reveal → fulfill, front-running rejected
//! 3. Value commitments: commit values, prove conservation homomorphically
//! 4. Cross-state derivation: derive authorization from facts in two state roots

use dregg_circuit::cross_state_derivation::{
    CombiningRule, SourceInput, prove_cross_state_derivation, verify_cross_state_derivation,
};
use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;

use curve25519_dalek::scalar::Scalar;
use dregg_cell::value_commitment::{
    ConservationError, ValueCommitment, prove_conservation, verify_conservation,
};

use dregg_intent::commit_reveal_fulfillment::{
    CommitRevealFulfiller, CommitRevealFulfillmentError, FulfillmentRegistry,
};
use dregg_intent::fulfillment::FulfillOptions;
use dregg_intent::matcher::{HeldCapability, Sensitivity};
use dregg_intent::partial_fill::{CumulativeFillTracker, PartialFillError, execute_partial_fill};
use dregg_intent::{
    ActionPattern, CommitmentId, FillConstraints, Intent, IntentKind, Match, MatchSpec,
    VerificationMode,
};

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Deterministic scalar from a seed byte for testing.
fn test_scalar(seed: u8) -> Scalar {
    let mut bytes = [0u8; 64];
    bytes[0] = seed;
    bytes[1] = seed.wrapping_mul(37);
    Scalar::from_bytes_mod_order_wide(&bytes)
}

fn make_fill_intent(min: u64, max: u64, fill_or_kill: bool) -> Intent {
    let spec = MatchSpec {
        actions: vec![ActionPattern {
            action: Some("transfer".into()),
            resource: None,
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: None,
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };
    let constraints = FillConstraints {
        min_fill_amount: min,
        max_fill_amount: max,
        fill_or_kill,
        remaining_after_fill: None,
        generation: 0,
    };
    Intent::new_with_fill(
        IntentKind::Need,
        spec,
        CommitmentId([0xAA; 32]),
        u64::MAX,
        None,
        constraints,
    )
}

fn make_source_token() -> HeldCapability {
    HeldCapability {
        token_id: "tok_defi".into(),
        actions: vec!["transfer".into()],
        resource: "*".into(),
        app_id: None,
        service: None,
        user_id: None,
        features: vec![],
        oauth_provider: None,
        expiry: None,
        budget: None,
        sensitivity: Sensitivity::Normal,
    }
}

fn make_match(intent: &Intent) -> Match {
    Match {
        intent_id: intent.id,
        satisfier: CommitmentId([0xBB; 32]),
        proof: None,
        mode: VerificationMode::Trusted,
    }
}

fn make_options() -> FulfillOptions {
    FulfillOptions {
        mode: VerificationMode::Trusted,
        root_key: Some([0x42; 32]),
        ..Default::default()
    }
}

fn make_test_intent_for_commit_reveal() -> Intent {
    let spec = MatchSpec {
        actions: vec![ActionPattern {
            action: Some("read".into()),
            resource: None,
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: None,
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };
    Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None)
}

fn make_cr_source_token() -> HeldCapability {
    HeldCapability {
        token_id: "tok_cr".into(),
        actions: vec!["read".into(), "write".into()],
        resource: "*".into(),
        app_id: None,
        service: None,
        user_id: None,
        features: vec![],
        oauth_provider: None,
        expiry: Some(10000),
        budget: None,
        sensitivity: Sensitivity::Normal,
    }
}

// ─── Partial Fill Tests ──────────────────────────────────────────────────────

/// Happy path: partial fill of 40 from intent with min=10, max=100 → residual of 60.
#[test]
fn test_partial_fill_produces_residual() {
    let intent = make_fill_intent(10, 100, false);
    let matched = make_match(&intent);
    let token = make_source_token();
    let our_id = CommitmentId([0xBB; 32]);
    let options = make_options();

    let result = execute_partial_fill(&intent, &matched, &token, our_id, 40, &options);
    assert!(
        result.is_ok(),
        "Partial fill should succeed: {:?}",
        result.err()
    );

    let pf = result.unwrap();
    assert_eq!(pf.filled_amount, 40);
    assert_eq!(pf.remaining_amount, 60);
    assert!(
        pf.residual_intent.is_some(),
        "Should produce a residual intent"
    );

    let residual = pf.residual_intent.unwrap();
    let rc = residual.fill_constraints.as_ref().unwrap();
    assert_eq!(rc.max_fill_amount, 60);
    assert_eq!(rc.min_fill_amount, 20); // residual minimum is anti-griefing adjusted
    assert!(!rc.fill_or_kill);
    assert_ne!(residual.id, intent.id, "Residual must have a different ID");
}

/// Happy path: accumulate partial fills to full completion.
#[test]
fn test_partial_fill_cumulative_to_completion() {
    let intent = make_fill_intent(10, 100, false);
    let matched = make_match(&intent);
    let token = make_source_token();
    let our_id = CommitmentId([0xBB; 32]);
    let options = make_options();

    let mut tracker = CumulativeFillTracker::new(&intent).unwrap();
    assert_eq!(tracker.remaining(), 100);

    // Fill 30.
    let r1 = execute_partial_fill(&intent, &matched, &token, our_id, 30, &options).unwrap();
    assert_eq!(r1.filled_amount, 30);
    tracker.record_fill(&r1);
    assert_eq!(tracker.remaining(), 70);

    // Fill 40 from residual.
    let residual1 = r1.residual_intent.unwrap();
    let matched2 = make_match(&residual1);
    let r2 = execute_partial_fill(&residual1, &matched2, &token, our_id, 40, &options).unwrap();
    assert_eq!(r2.filled_amount, 40);
    tracker.record_fill(&r2);
    assert_eq!(tracker.remaining(), 30);

    // Fill final 30.
    let residual2 = r2.residual_intent.unwrap();
    let matched3 = make_match(&residual2);
    let r3 = execute_partial_fill(&residual2, &matched3, &token, our_id, 30, &options).unwrap();
    assert_eq!(r3.filled_amount, 30);
    assert_eq!(r3.remaining_amount, 0);
    assert!(r3.residual_intent.is_none(), "No residual after full fill");
    let complete = tracker.record_fill(&r3);
    assert!(complete, "Should be fully filled");
    assert_eq!(tracker.total_filled, 100);
    assert_eq!(tracker.fill_chain.len(), 3);
}

/// Adversarial: fill below minimum is rejected.
#[test]
fn test_partial_fill_below_minimum_rejected() {
    let intent = make_fill_intent(10, 100, false);
    let matched = make_match(&intent);
    let token = make_source_token();
    let our_id = CommitmentId([0xBB; 32]);
    let options = make_options();

    let result = execute_partial_fill(&intent, &matched, &token, our_id, 5, &options);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        PartialFillError::BelowMinimum {
            available: 5,
            minimum: 10
        }
    ));
}

/// Adversarial: fill-or-kill partial is rejected.
#[test]
fn test_partial_fill_fill_or_kill_rejected() {
    let intent = make_fill_intent(10, 100, true);
    let matched = make_match(&intent);
    let token = make_source_token();
    let our_id = CommitmentId([0xBB; 32]);
    let options = make_options();

    // Only 50 available but fill-or-kill requires 100.
    let result = execute_partial_fill(&intent, &matched, &token, our_id, 50, &options);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        PartialFillError::FillOrKillRejected {
            available: 50,
            required: 100
        }
    ));
}

// ─── Commit-Reveal Fulfillment Tests ─────────────────────────────────────────

/// Happy path: commit → wait → reveal+fulfill → success.
#[test]
fn test_commit_reveal_happy_path() {
    let our_id = CommitmentId([0xBB; 32]);
    let mut fulfiller = CommitRevealFulfiller::new(our_id);

    let intent = make_test_intent_for_commit_reveal();
    let matched = Match {
        intent_id: intent.id,
        satisfier: our_id,
        proof: None,
        mode: VerificationMode::Trusted,
    };
    let token = make_cr_source_token();
    let secret = [0xCC; 32];
    let options = FulfillOptions {
        mode: VerificationMode::Trusted,
        root_key: Some([0x42; 32]),
        ..Default::default()
    };

    // Phase 1: Commit at time 100.
    let commitment = fulfiller
        .commit_to_fulfillment(&intent.id, &secret, 100)
        .unwrap();
    assert_eq!(commitment.intent_id, intent.id);

    // Phase 2: Reveal + fulfill at time 106 (after 5-second window).
    let result = fulfiller.reveal_and_fulfill(&intent, &matched, &token, &secret, &options, 106);
    assert!(result.is_ok(), "Should succeed: {:?}", result.err());

    let fres = result.unwrap();
    assert_eq!(fres.fulfillment.intent_id, intent.id);
    assert!(fulfiller.registry.is_fulfilled(&intent.id));
}

/// Adversarial: front-running without commit is rejected.
#[test]
fn test_commit_reveal_frontrunning_rejected() {
    let our_id = CommitmentId([0xBB; 32]);
    let mut fulfiller = CommitRevealFulfiller::new(our_id);

    let intent = make_test_intent_for_commit_reveal();
    let matched = Match {
        intent_id: intent.id,
        satisfier: our_id,
        proof: None,
        mode: VerificationMode::Trusted,
    };
    let token = make_cr_source_token();
    let secret = [0xCC; 32];
    let options = FulfillOptions {
        mode: VerificationMode::Trusted,
        root_key: Some([0x42; 32]),
        ..Default::default()
    };

    // Try to reveal/fulfill WITHOUT committing first → front-running attempt.
    let result = fulfiller.reveal_and_fulfill(&intent, &matched, &token, &secret, &options, 200);
    assert_eq!(
        result.unwrap_err(),
        CommitRevealFulfillmentError::NoCommitment,
        "Front-running (no commit) should be rejected"
    );
}

/// Adversarial: reveal too early (before window elapses).
#[test]
fn test_commit_reveal_too_early_rejected() {
    let our_id = CommitmentId([0xBB; 32]);
    let mut fulfiller = CommitRevealFulfiller::new(our_id);

    let intent = make_test_intent_for_commit_reveal();
    let matched = Match {
        intent_id: intent.id,
        satisfier: our_id,
        proof: None,
        mode: VerificationMode::Trusted,
    };
    let token = make_cr_source_token();
    let secret = [0xCC; 32];
    let options = FulfillOptions {
        mode: VerificationMode::Trusted,
        root_key: Some([0x42; 32]),
        ..Default::default()
    };

    // Commit at time 100.
    fulfiller
        .commit_to_fulfillment(&intent.id, &secret, 100)
        .unwrap();

    // Try to reveal at time 103 (only 3s elapsed, need 5s).
    let result = fulfiller.reveal_and_fulfill(&intent, &matched, &token, &secret, &options, 103);
    assert!(matches!(
        result.unwrap_err(),
        CommitRevealFulfillmentError::TooEarly { .. }
    ));
}

/// Adversarial: wrong secret on reveal is rejected.
#[test]
fn test_commit_reveal_wrong_secret_rejected() {
    let mut registry = FulfillmentRegistry::new();
    let intent = make_test_intent_for_commit_reveal();
    let real_secret = [0xCC; 32];
    let wrong_secret = [0xDD; 32];

    // Commit with real secret.
    registry
        .register_commitment(intent.id, &real_secret, 100)
        .unwrap();

    // Reveal with wrong secret after window.
    let result = registry.validate_reveal(&intent.id, &wrong_secret, 106);
    assert_eq!(
        result.unwrap_err(),
        CommitRevealFulfillmentError::SecretMismatch,
        "Wrong secret should be rejected"
    );
}

/// Adversarial: second committer loses to first (priority enforcement).
#[test]
fn test_commit_reveal_priority_enforcement() {
    let mut registry = FulfillmentRegistry::new();
    let intent = make_test_intent_for_commit_reveal();
    let secret_a = [0xAA; 32];
    let secret_b = [0xBB; 32];

    // A commits at time 100.
    registry
        .register_commitment(intent.id, &secret_a, 100)
        .unwrap();
    // B commits at time 102.
    registry
        .register_commitment(intent.id, &secret_b, 102)
        .unwrap();

    // B tries to reveal at 108 (102 + 6) but A committed first.
    let result = registry.validate_reveal(&intent.id, &secret_b, 108);
    assert!(matches!(
        result.unwrap_err(),
        CommitRevealFulfillmentError::PriorityConflict {
            first_committed_at: 100
        }
    ));

    // A reveals at 106 (100 + 6) → success.
    let result = registry.validate_reveal(&intent.id, &secret_a, 106);
    assert!(result.is_ok(), "First committer should succeed");
}

// ─── Value Commitment Conservation Tests ─────────────────────────────────────

/// Happy path: inputs and outputs balance → conservation proof verifies.
#[test]
fn test_value_commitment_conservation_happy_path() {
    // Transaction: 300 + 500 → 450 + 350 (sum = 800 both sides).
    let r_in1 = test_scalar(10);
    let r_in2 = test_scalar(11);
    let r_out1 = test_scalar(12);
    let r_out2 = test_scalar(13);

    let inputs = vec![
        ValueCommitment::commit(300, &r_in1),
        ValueCommitment::commit(500, &r_in2),
    ];
    let outputs = vec![
        ValueCommitment::commit(450, &r_out1),
        ValueCommitment::commit(350, &r_out2),
    ];

    let excess_blinding = (r_in1 + r_in2) - (r_out1 + r_out2);
    let proof = prove_conservation(&inputs, &outputs, &excess_blinding, b"test-tx-happy");

    let result = verify_conservation(&inputs, &outputs, &proof, b"test-tx-happy");
    assert!(
        result.is_ok(),
        "Balanced transaction should verify: {:?}",
        result.err()
    );
}

/// Adversarial: imbalanced transaction → conservation proof fails.
#[test]
fn test_value_commitment_inflation_rejected() {
    // Transaction: input 100 → output 200 (INFLATION ATTEMPT).
    let r_in = test_scalar(20);
    let r_out = test_scalar(21);

    let inputs = vec![ValueCommitment::commit(100, &r_in)];
    let outputs = vec![ValueCommitment::commit(200, &r_out)];

    // Even using the "correct" blinding factor difference, the proof
    // must fail because the value component doesn't cancel.
    let blinding_diff = r_in - r_out;
    let proof = prove_conservation(&inputs, &outputs, &blinding_diff, b"inflate-attempt");

    let result = verify_conservation(&inputs, &outputs, &proof, b"inflate-attempt");
    assert_eq!(
        result.unwrap_err(),
        ConservationError::SignatureInvalid,
        "Imbalanced transaction should fail conservation check"
    );
}

/// Adversarial: replay proof with different message → rejected.
#[test]
fn test_value_commitment_wrong_message_rejected() {
    let r_in = test_scalar(40);
    let r_out = test_scalar(41);

    let inputs = vec![ValueCommitment::commit(500, &r_in)];
    let outputs = vec![ValueCommitment::commit(500, &r_out)];

    let excess = r_in - r_out;
    let proof = prove_conservation(&inputs, &outputs, &excess, b"correct-message");

    // Verify with different message → replay attack.
    let result = verify_conservation(&inputs, &outputs, &proof, b"attacker-message");
    assert_eq!(
        result.unwrap_err(),
        ConservationError::SignatureInvalid,
        "Wrong message should be rejected (anti-replay)"
    );
}

/// Homomorphic property: commit(a) + commit(b) == commit(a+b).
#[test]
fn test_value_commitment_homomorphic() {
    let r1 = test_scalar(50);
    let r2 = test_scalar(51);

    let c1 = ValueCommitment::commit(300, &r1);
    let c2 = ValueCommitment::commit(700, &r2);

    let sum = &c1 + &c2;
    let direct = ValueCommitment::commit(1000, &(r1 + r2));
    assert_eq!(sum.point, direct.point, "Homomorphic addition must hold");
}

/// Multi-asset conservation: each asset verified independently.
#[test]
fn test_value_commitment_multi_asset_conservation() {
    let asset_a = 1u64;
    let asset_b = 2u64;

    let r1 = test_scalar(60);
    let r2 = test_scalar(61);
    let r3 = test_scalar(62);
    let r4 = test_scalar(63);

    // Asset A: 100 in → 100 out (balanced).
    let inputs_a = vec![ValueCommitment::commit_with_asset(100, &r1, asset_a)];
    let outputs_a = vec![ValueCommitment::commit_with_asset(100, &r2, asset_a)];
    let excess_a = r1 - r2;
    let proof_a = prove_conservation(&inputs_a, &outputs_a, &excess_a, b"multi-asset");
    assert!(verify_conservation(&inputs_a, &outputs_a, &proof_a, b"multi-asset").is_ok());

    // Asset B: 200 in → 200 out (balanced).
    let inputs_b = vec![ValueCommitment::commit_with_asset(200, &r3, asset_b)];
    let outputs_b = vec![ValueCommitment::commit_with_asset(200, &r4, asset_b)];
    let excess_b = r3 - r4;
    let proof_b = prove_conservation(&inputs_b, &outputs_b, &excess_b, b"multi-asset");
    assert!(verify_conservation(&inputs_b, &outputs_b, &proof_b, b"multi-asset").is_ok());
}

// ─── Cross-State Derivation Tests ────────────────────────────────────────────

/// Helper: build a simple derivation witness.
fn make_source_witness(
    source_root: BabyBear,
    rule_id: u32,
    derived_pred: BabyBear,
    body_pred: BabyBear,
    term0: BabyBear,
    term1: BabyBear,
) -> DerivationWitness {
    let body_hash = hash_fact(body_pred, &[term0, term1, BabyBear::ZERO]);
    DerivationWitness {
        rule: CircuitRule {
            id: rule_id,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: derived_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: body_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root: source_root,
        body_fact_hashes: vec![body_hash],
        substitution: vec![term0, term1],
        derived_predicate: derived_pred,
        derived_terms: [term0, term1, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    }
}

/// Happy path: derive authorization from facts in two different state roots.
#[test]
fn test_cross_state_derivation_two_sources() {
    // Source 1: Org A's state has "has_role(alice, admin)".
    let root_a = BabyBear::new(11111);
    let alice = BabyBear::new(1000);
    let admin = BabyBear::new(2000);
    let has_role_pred = BabyBear::new(100);
    let org_a_cleared_pred = BabyBear::new(200);

    let witness_a = make_source_witness(root_a, 1, org_a_cleared_pred, has_role_pred, alice, admin);

    // Source 2: Org B's state has "resource_available(alice, file)".
    let root_b = BabyBear::new(22222);
    let file = BabyBear::new(3000);
    let resource_pred = BabyBear::new(300);
    let org_b_grants_pred = BabyBear::new(400);

    let witness_b = make_source_witness(root_b, 2, org_b_grants_pred, resource_pred, alice, file);

    let sources = vec![
        SourceInput {
            source_root: root_a,
            witness: witness_a,
            membership_proofs: vec![],
        },
        SourceInput {
            source_root: root_b,
            witness: witness_b,
            membership_proofs: vec![],
        },
    ];

    // Combining rule: derive cross_authorized(alice, admin) from both.
    let cross_auth_pred = BabyBear::new(500);
    let combining_rule = CombiningRule {
        rule_id: 99,
        head_predicate: cross_auth_pred,
        head_terms: [
            (true, BabyBear::new(0)),
            (true, BabyBear::new(1)),
            (false, BabyBear::ZERO),
            (false, BabyBear::ZERO),
        ],
        substitution: vec![alice, admin],
        derived_terms: [alice, admin, BabyBear::ZERO, BabyBear::ZERO],
    };

    let proof = prove_cross_state_derivation(&sources, &combining_rule);

    // Verify.
    let expected_final_hash = hash_fact(
        cross_auth_pred,
        &[alice, admin, BabyBear::ZERO, BabyBear::ZERO],
    );
    let result = verify_cross_state_derivation(&proof, &[root_a, root_b], expected_final_hash);
    assert!(
        result.is_ok(),
        "Cross-state derivation should verify: {:?}",
        result.err()
    );
}

/// Adversarial: wrong expected source root → rejected.
#[test]
fn test_cross_state_derivation_wrong_root_rejected() {
    let root_a = BabyBear::new(11111);
    let root_b = BabyBear::new(22222);
    let alice = BabyBear::new(1000);
    let val = BabyBear::new(2000);

    let pred_a = BabyBear::new(100);
    let pred_b = BabyBear::new(200);
    let derived_a = BabyBear::new(101);
    let derived_b = BabyBear::new(201);

    let witness_a = make_source_witness(root_a, 1, derived_a, pred_a, alice, val);
    let witness_b = make_source_witness(root_b, 2, derived_b, pred_b, alice, val);

    let sources = vec![
        SourceInput {
            source_root: root_a,
            witness: witness_a,
            membership_proofs: vec![],
        },
        SourceInput {
            source_root: root_b,
            witness: witness_b,
            membership_proofs: vec![],
        },
    ];

    let final_pred = BabyBear::new(999);
    let combining_rule = CombiningRule {
        rule_id: 50,
        head_predicate: final_pred,
        head_terms: [
            (true, BabyBear::new(0)),
            (false, BabyBear::ZERO),
            (false, BabyBear::ZERO),
            (false, BabyBear::ZERO),
        ],
        substitution: vec![alice],
        derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    };

    let proof = prove_cross_state_derivation(&sources, &combining_rule);
    let expected_final = hash_fact(
        final_pred,
        &[alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    );

    // Verify with a WRONG source root.
    let result = verify_cross_state_derivation(
        &proof,
        &[BabyBear::new(99999), root_b], // wrong root_a
        expected_final,
    );
    assert!(result.is_err(), "Wrong source root should be rejected");
    assert!(result.unwrap_err().contains("Source root 0 mismatch"));
}

/// Adversarial: tampered STARK proof → verification fails.
#[test]
fn test_cross_state_derivation_tampered_proof_rejected() {
    let root_a = BabyBear::new(11111);
    let alice = BabyBear::new(1000);
    let val = BabyBear::new(2000);
    let pred_a = BabyBear::new(100);
    let derived_a = BabyBear::new(101);

    let witness_a = make_source_witness(root_a, 1, derived_a, pred_a, alice, val);

    let sources = vec![SourceInput {
        source_root: root_a,
        witness: witness_a,
        membership_proofs: vec![],
    }];

    let final_pred = BabyBear::new(999);
    let combining_rule = CombiningRule {
        rule_id: 50,
        head_predicate: final_pred,
        head_terms: [
            (true, BabyBear::new(0)),
            (false, BabyBear::ZERO),
            (false, BabyBear::ZERO),
            (false, BabyBear::ZERO),
        ],
        substitution: vec![alice],
        derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    };

    let mut proof = prove_cross_state_derivation(&sources, &combining_rule);
    let expected_final = hash_fact(
        final_pred,
        &[alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    );

    // Tamper with the source STARK.
    proof.source_derivations[0].proof.trace_commitment[0] ^= 0xFF;

    let result = verify_cross_state_derivation(&proof, &[root_a], expected_final);
    assert!(result.is_err(), "Tampered STARK should be rejected");
    assert!(result.unwrap_err().contains("STARK verification failed"));
}
