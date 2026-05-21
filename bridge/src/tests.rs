//! End-to-end integration tests for the bridge module.
//!
//! These tests exercise the full pipeline: mint a MacaroonToken, attenuate it,
//! convert to ZK commitments, evaluate authorization, and produce a verified
//! presentation proof.

use pyana_circuit::fold_air::FoldAir;
use pyana_circuit::merkle_air::MerkleAir;
use pyana_circuit::{BabyBear, ConstraintProver, PresentationVerification};
use pyana_commit::{Fact, FactSet, FieldElement, SymbolTable, TokenState, verify_fold_chain};
use pyana_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};
use pyana_trace::{Conclusion, symbol_from_str};

use crate::authorize::{self, AuthError};
use crate::convert::macaroon_to_factset;
use crate::delta::{compute_fold_delta, further_attenuation_delta, initial_attenuation_delta};
use crate::present::{BridgePresentationBuilder, verify_presentation};

// ============================================================================
// Test helpers
// ============================================================================

fn test_root_key() -> [u8; 32] {
    let mut key = [0u8; 32];
    // Deterministic key for reproducible tests.
    key[0] = 0xDE;
    key[1] = 0xAD;
    key[2] = 0xBE;
    key[3] = 0xEF;
    key[28] = 0xCA;
    key[29] = 0xFE;
    key[30] = 0xBA;
    key[31] = 0xBE;
    key
}

fn test_federation_root() -> [u8; 32] {
    let mut root = [0u8; 32];
    root[0] = 0xFE;
    root[1] = 0xD0;
    root[2] = 0x00;
    root[3] = 0x01;
    root
}

/// Compute the BabyBear federation root that the synthetic Poseidon2 Merkle path
/// produces for a given key. This lets tests construct a builder with a matching root.
fn compute_matching_federation_root_bb(key: &[u8; 32]) -> BabyBear {
    use pyana_circuit::poseidon2;
    let issuer_hash = crate::present::bytes_to_babybear(key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(crate::present::hash_index(i, 0, key)),
            BabyBear::new(crate::present::hash_index(i, 1, key)),
            BabyBear::new(crate::present::hash_index(i, 2, key)),
        ];
        // Use Poseidon2 hashing to match prove()'s issuer membership path.
        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j == position {
                children[j as usize] = current;
            } else {
                children[j as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }
        current = poseidon2::hash_4_to_1(&children);
    }
    current
}

/// Create a builder whose federation root matches the synthetic Poseidon2 Merkle path
/// for the given key. Used by the `prove()` (real STARK) path.
fn test_builder_with_matching_root(key: [u8; 32]) -> BridgePresentationBuilder {
    let federation_root = test_federation_root();
    let matching_root_bb = compute_matching_federation_root_bb(&key);
    BridgePresentationBuilder::new_with_root_bb(key, federation_root, matching_root_bb)
}

/// Compute the LINEAR Merkle AIR federation root for testing `prove_fast()`.
fn compute_matching_federation_root_bb_linear(key: &[u8; 32]) -> BabyBear {
    let issuer_hash = crate::present::bytes_to_babybear(key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(crate::present::hash_index(i, 0, key)),
            BabyBear::new(crate::present::hash_index(i, 1, key)),
            BabyBear::new(crate::present::hash_index(i, 2, key)),
        ];
        current = MerkleAir::compute_parent(current, position, &siblings);
    }
    current
}

/// Create a builder whose federation root matches the synthetic LINEAR Merkle path
/// for the given key. Used by `prove_fast()` tests.
fn test_builder_with_matching_root_linear(key: [u8; 32]) -> BridgePresentationBuilder {
    let federation_root = test_federation_root();
    let matching_root_bb = compute_matching_federation_root_bb_linear(&key);
    BridgePresentationBuilder::new_with_root_bb(key, federation_root, matching_root_bb)
}

// ============================================================================
// End-to-end test: Full pipeline from token to ZK proof
// ============================================================================

/// The main end-to-end test. Proves the full pipeline works:
/// 1. Mint a root MacaroonToken.
/// 2. Attenuate it (restrict to app + actions).
/// 3. Attenuate again (add user confinement + expiry).
/// 4. Convert to committed states with fold deltas.
/// 5. Evaluate authorization against the final state.
/// 6. Generate a ZK presentation proof.
/// 7. Verify the proof.
#[test]
fn test_end_to_end_macaroon_to_zk_proof() {
    let root_key = test_root_key();

    // ── Step 1: Mint a root token ───────────────────────────────────────────
    let root_token = MacaroonToken::mint(root_key, b"issuer-kid-42", "pyana.dev");

    // Verify the root token works.
    let root_clearance = root_token.verify(&AuthRequest::default()).unwrap();
    assert_eq!(root_clearance.format, pyana_token::TokenFormat::Macaroon);

    // ── Step 2: First attenuation — restrict to app "dashboard" with rw ─────
    let att1 = Attenuation {
        apps: vec![("dashboard".into(), "rw".into())],
        ..Default::default()
    };
    let token1 = root_token.attenuate(&att1).unwrap();

    // Verify token1 still works for dashboard read.
    let request1 = AuthRequest {
        app_id: Some("dashboard".into()),
        action: Some("r".into()),
        now: Some(1700000000),
        ..Default::default()
    };
    let clearance1 = token1.verify(&request1).unwrap();
    assert!(!clearance1.capabilities.is_empty());

    // ── Step 3: Second attenuation — confine to user "alice" + set expiry ───
    let att2 = Attenuation {
        confine_user: Some("alice".into()),
        not_after: Some(2000000000),
        ..Default::default()
    };
    let token2 = token1.attenuate(&att2).unwrap();

    // Verify token2 works for alice on dashboard.
    let request2 = AuthRequest {
        app_id: Some("dashboard".into()),
        action: Some("r".into()),
        user_id: Some("alice".into()),
        now: Some(1700000000),
        ..Default::default()
    };
    let clearance2 = token2.verify(&request2).unwrap();
    assert!(clearance2.subject.is_some());
    assert_eq!(clearance2.subject.as_deref(), Some("alice"));

    // ── Step 4: Build presentation using the builder ────────────────────────
    let mut builder = test_builder_with_matching_root(root_key);

    // Set the root token.
    builder.set_root_token(root_token);
    assert_eq!(builder.chain_length(), 1);

    // First attenuation.
    assert!(builder.add_attenuation(&att1));
    assert_eq!(builder.chain_length(), 2);

    // Second attenuation.
    assert!(builder.add_attenuation(&att2));
    assert_eq!(builder.chain_length(), 3);

    // Verify the fold chain is consistent.
    assert!(builder.verify_chain());

    // ── Step 5: Generate the ZK presentation proof ──────────────────────────
    let auth_request = AuthRequest {
        app_id: Some("dashboard".into()),
        action: Some("r".into()),
        user_id: Some("alice".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    let proof_result = builder.prove(&auth_request);
    assert!(
        proof_result.is_ok(),
        "Proof generation should succeed: {:?}",
        proof_result.err()
    );

    let proof = proof_result.unwrap();

    // ── Step 6: Verify the proof ────────────────────────────────────────────
    assert!(proof.is_valid(), "Proof should be valid");
    assert_eq!(proof.chain_length, 3);
    assert!(proof.proof_size_bytes() > 0);

    // The trace should show Allow with the APP_ACTION rule.
    match &proof.trace.conclusion {
        Conclusion::Allow { policy_rule_id } => {
            assert_eq!(*policy_rule_id, 1); // APP_ACTION
        }
        Conclusion::Deny => panic!("Expected Allow conclusion"),
    }

    // Standalone verification.
    assert!(verify_presentation(&proof, &proof.federation_root));

    println!(
        "End-to-end proof generated successfully: {} (chain length: {})",
        proof.proof_size_display(),
        proof.chain_length
    );
}

/// Test: authorization denial produces an error (not a proof).
#[test]
fn test_end_to_end_denial() {
    let root_key = test_root_key();
    let federation_root = test_federation_root();

    let root_token = MacaroonToken::mint(root_key, b"kid-deny", "pyana.dev");

    let mut builder = BridgePresentationBuilder::new(root_key, federation_root);
    builder.set_root_token(root_token);

    // Restrict to app "dashboard".
    let att = Attenuation {
        apps: vec![("dashboard".into(), "rw".into())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    // Try to authorize for a different app — should be denied.
    let request = AuthRequest {
        app_id: Some("admin-panel".into()),
        action: Some("r".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    let result = builder.prove_fast(&request);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), AuthError::Denied);
}

/// Test: the conversion pipeline preserves token semantics.
#[test]
fn test_conversion_preserves_semantics() {
    let root_key = test_root_key();
    let token = MacaroonToken::mint(root_key, b"kid-sem", "pyana.dev");

    // Attenuate with multiple restrictions.
    let att = Attenuation {
        apps: vec![("app-1".into(), "rw".into()), ("app-2".into(), "r".into())],
        services: vec![("http".into(), "rw".into())],
        features: vec!["ai".into(), "gpu".into()],
        confine_user: Some("bob".into()),
        not_after: Some(1900000000),
        ..Default::default()
    };

    let restricted = token.attenuate(&att).unwrap();

    // Encode and decode to get a concrete MacaroonToken.
    let encoded = restricted.to_encoded().unwrap();
    let mac_restricted = MacaroonToken::from_encoded(&encoded, root_key).unwrap();

    let (mut factset, symbols) = macaroon_to_factset(&mac_restricted);

    // Should have: 2 apps + 1 service + 2 features + 1 confine_user + 1 valid_until = 7 facts.
    assert_eq!(factset.len(), 7, "Expected 7 facts, got {}", factset.len());

    // Verify all symbol resolutions work.
    assert!(symbols.resolve(FieldElement::from_symbol("app")).is_some());
    assert!(
        symbols
            .resolve(FieldElement::from_symbol("service"))
            .is_some()
    );
    assert!(
        symbols
            .resolve(FieldElement::from_symbol("feature"))
            .is_some()
    );
    assert!(
        symbols
            .resolve(FieldElement::from_symbol("confine_user"))
            .is_some()
    );
    assert!(
        symbols
            .resolve(FieldElement::from_symbol("valid_until"))
            .is_some()
    );

    // The Merkle root should be deterministic.
    let root1 = factset.root();
    let root2 = factset.root();
    assert_eq!(root1, root2);
    assert_ne!(root1, [0u8; 32]);
}

/// Test: fold delta chain verification.
#[test]
fn test_fold_chain_verification() {
    let mut symbols = SymbolTable::new();

    // State 0: unrestricted.
    let att1 = Attenuation {
        apps: vec![("my-app".into(), "rw".into())],
        ..Default::default()
    };

    let (state0, state1, delta1) = initial_attenuation_delta(&att1, &mut symbols).unwrap();

    // State 1 → State 2: add feature restriction.
    let feature_pred = symbols.intern("feature");
    let feature_val = symbols.intern("ai");
    let new_fact = Fact::unary(feature_pred, feature_val);

    let (state2, delta2) = further_attenuation_delta(&state1, &[new_fact], &symbols).unwrap();

    // Verify individual deltas.
    assert!(delta1.apply_and_verify(), "delta1 should verify");
    assert!(delta2.apply_and_verify(), "delta2 should verify");

    // Verify the chain.
    assert!(verify_fold_chain(&[delta1, delta2]));

    // The states should have increasing content.
    assert_eq!(state0.len(), 1); // just unrestricted
    assert!(state1.len() >= 1); // check fact(s)
    assert!(state2.len() >= state1.len()); // state2 has more checks
}

/// Test: authorization trace evaluation with the trace engine.
#[test]
fn test_authorization_trace_generation() {
    let mut symbols = SymbolTable::new();
    symbols.intern("app");
    symbols.intern("my-app");
    symbols.intern("read,write");

    // Create a state with an app fact.
    let mut state = TokenState::new();
    state.add_fact(Fact::binary(
        FieldElement::from_symbol("app"),
        FieldElement::from_symbol("my-app"),
        FieldElement::from_symbol("read,write"),
    ));

    let request = AuthRequest {
        app_id: Some("my-app".into()),
        action: Some("read".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    let trace = authorize::authorize_with_trace(&state, &request, &symbols).unwrap();

    // Should be allowed by the APP_ACTION rule.
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 1 });

    // Should have at least one derivation step.
    assert!(
        !trace.steps.is_empty(),
        "Trace should have derivation steps"
    );

    // Verify the trace.
    assert!(authorize::verify_authorization_trace(
        &state, &trace, &symbols
    ));
}

/// Test: circuit-level fold proof generation and verification.
#[test]
fn test_circuit_fold_proofs() {
    let root_key = test_root_key();
    let federation_root = test_federation_root();

    let root_token = MacaroonToken::mint(root_key, b"kid-circuit", "pyana.dev");

    let mut builder = BridgePresentationBuilder::new(root_key, federation_root);
    builder.set_root_token(root_token);

    let att = Attenuation {
        apps: vec![("my-app".into(), "rw".into())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    // The fold witnesses should produce valid AIR traces.
    let witnesses = builder.build_fold_witnesses();
    assert!(!witnesses.is_empty());

    for (i, witness) in witnesses.iter().enumerate() {
        let air = FoldAir::new(witness.clone());
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Fold AIR #{} should verify: {:?}",
            i,
            result.violations()
        );
    }
}

/// Test: service-scoped authorization through the full bridge.
#[test]
fn test_service_scoped_full_pipeline() {
    let root_key = test_root_key();

    let root_token = MacaroonToken::mint(root_key, b"kid-svc", "pyana.dev");

    let mut builder = test_builder_with_matching_root_linear(root_key);
    builder.set_root_token(root_token);

    // Restrict to HTTP service with read access.
    let att = Attenuation {
        services: vec![("http".into(), "rw".into())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    // Authorize an HTTP read.
    let request = AuthRequest {
        service: Some("http".into()),
        action: Some("r".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    let proof = builder.prove_fast(&request);
    assert!(
        proof.is_ok(),
        "Service-scoped proof should succeed: {:?}",
        proof.err()
    );

    let proof = proof.unwrap();
    assert!(proof.is_valid());

    // Should be allowed by the SERVICE_ACTION rule (rule ID 2).
    match &proof.trace.conclusion {
        Conclusion::Allow { policy_rule_id } => {
            assert_eq!(*policy_rule_id, 2);
        }
        Conclusion::Deny => panic!("Expected Allow"),
    }
}

/// Test: unrestricted token proof (no attenuations).
#[test]
fn test_unrestricted_token_proof() {
    let root_key = test_root_key();

    let root_token = MacaroonToken::mint(root_key, b"kid-unr", "pyana.dev");

    let mut builder = test_builder_with_matching_root_linear(root_key);
    builder.set_root_token(root_token);
    // No attenuations — the unrestricted root token should still authorize.

    let request = AuthRequest {
        action: Some("anything".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    let proof = builder.prove_fast(&request);
    assert!(
        proof.is_ok(),
        "Unrestricted proof should succeed: {:?}",
        proof.err()
    );

    let proof = proof.unwrap();
    assert!(proof.is_valid());

    // Should be allowed by the UNRESTRICTED rule (rule ID 3).
    match &proof.trace.conclusion {
        Conclusion::Allow { policy_rule_id } => {
            assert_eq!(*policy_rule_id, 3);
        }
        Conclusion::Deny => panic!("Expected Allow"),
    }
}

/// Test: multiple features in attenuation.
#[test]
fn test_multiple_features_attenuation() {
    let root_key = test_root_key();
    let federation_root = test_federation_root();

    let root_token = MacaroonToken::mint(root_key, b"kid-feat", "pyana.dev");

    let mut builder = BridgePresentationBuilder::new(root_key, federation_root);
    builder.set_root_token(root_token);

    // First attenuation: app restriction.
    let att1 = Attenuation {
        apps: vec![("my-app".into(), "rw".into())],
        ..Default::default()
    };
    assert!(builder.add_attenuation(&att1));

    // Second attenuation: add features.
    let att2 = Attenuation {
        features: vec!["ai".into(), "gpu".into(), "network".into()],
        ..Default::default()
    };
    assert!(builder.add_attenuation(&att2));

    assert_eq!(builder.chain_length(), 3);
    assert!(builder.verify_chain());
}

/// Test: the issuer membership Merkle proof verifies in the circuit.
#[test]
fn test_issuer_membership_circuit_rejects_wrong_federation_root() {
    let root_key = test_root_key();
    let federation_root = test_federation_root();

    let builder = BridgePresentationBuilder::new(root_key, federation_root);

    let issuer_hash = crate::present::bytes_to_babybear(&root_key);
    let result = builder.build_issuer_membership(issuer_hash);

    // The synthetic Merkle path won't match the arbitrary test federation root.
    assert!(
        result.is_err(),
        "Issuer membership should fail against unrelated federation root"
    );
    assert_eq!(
        result.unwrap_err(),
        crate::authorize::AuthError::IssuerNotInFederation
    );
}

/// Test: verify that the complete presentation AIR verifies end to end.
#[test]
fn test_presentation_air_full_verification() {
    let root_key = test_root_key();

    let root_token = MacaroonToken::mint(root_key, b"kid-full", "pyana.dev");

    let mut builder = test_builder_with_matching_root_linear(root_key);
    builder.set_root_token(root_token);

    let att = Attenuation {
        apps: vec![("my-app".into(), "rw".into())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    let request = AuthRequest {
        app_id: Some("my-app".into()),
        action: Some("r".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    let proof = builder.prove_fast(&request).unwrap();

    // Verify individual sub-proofs.
    assert!(!proof.circuit_proof.fold_proofs.is_empty());
    assert!(proof.circuit_proof.total_proof_size_bytes > 0);

    // The presentation-level verification should pass.
    assert_eq!(proof.verification, PresentationVerification::Valid);
}

/// Test: proof metadata is correct.
#[test]
fn test_proof_metadata() {
    let root_key = test_root_key();

    let root_token = MacaroonToken::mint(root_key, b"kid-meta", "pyana.dev");

    let mut builder = test_builder_with_matching_root_linear(root_key);
    builder.set_root_token(root_token);

    let att1 = Attenuation {
        apps: vec![("app-1".into(), "rw".into())],
        ..Default::default()
    };
    builder.add_attenuation(&att1);

    let att2 = Attenuation {
        confine_user: Some("alice".into()),
        ..Default::default()
    };
    builder.add_attenuation(&att2);

    let request = AuthRequest {
        app_id: Some("app-1".into()),
        action: Some("r".into()),
        user_id: Some("alice".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    let proof = builder.prove_fast(&request).unwrap();

    assert_eq!(proof.chain_length, 3); // root + 2 attenuations
    assert_ne!(proof.final_state_root, [0u8; 32]);
    assert!(proof.proof_size_bytes() > 0);

    // Proof size should be reasonable (mock proof, so relatively small).
    assert!(
        proof.proof_size_bytes() < 1_000_000,
        "Proof size should be under 1MB for a mock proof"
    );
}

/// Test: deterministic proof generation.
/// The same inputs should produce proofs that verify the same way.
#[test]
fn test_deterministic_verification() {
    let root_key = test_root_key();

    let build_and_prove = || {
        let root_token = MacaroonToken::mint(root_key, b"kid-det", "pyana.dev");
        let mut builder = test_builder_with_matching_root_linear(root_key);
        builder.set_root_token(root_token);

        let att = Attenuation {
            apps: vec![("det-app".into(), "rw".into())],
            ..Default::default()
        };
        builder.add_attenuation(&att);

        let request = AuthRequest {
            app_id: Some("det-app".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        builder.prove_fast(&request).unwrap()
    };

    let proof1 = build_and_prove();
    let proof2 = build_and_prove();

    // Both should be valid.
    assert!(proof1.is_valid());
    assert!(proof2.is_valid());

    // Chain lengths should match.
    assert_eq!(proof1.chain_length, proof2.chain_length);

    // Conclusions should match.
    assert_eq!(proof1.trace.conclusion, proof2.trace.conclusion);
}

// ============================================================================
// Lower-level unit tests for specific conversion steps
// ============================================================================

#[test]
fn test_fact_set_merkle_commitment() {
    let root_key = test_root_key();
    let token = MacaroonToken::mint(root_key, b"kid-merkle", "pyana.dev");

    let att = Attenuation {
        apps: vec![("app-a".into(), "r".into())],
        ..Default::default()
    };
    let restricted = token.attenuate(&att).unwrap();
    let encoded = restricted.to_encoded().unwrap();
    let mac = MacaroonToken::from_encoded(&encoded, root_key).unwrap();

    let (mut fs, _) = macaroon_to_factset(&mac);

    // Get membership proof for each fact.
    let facts: Vec<Fact> = fs.iter().copied().collect();
    let root = fs.root();

    for fact in &facts {
        let proof = fs.membership_proof(fact).unwrap();
        assert!(
            FactSet::verify_membership(&root, fact, &proof),
            "Membership proof should verify for committed fact"
        );
    }
}

#[test]
fn test_fold_delta_from_raw_states() {
    // Direct state manipulation test.
    let mut state = TokenState::new();
    state.add_fact(Fact::from_symbols("resource", &["secret-doc"]));
    state.add_fact(Fact::from_symbols("resource", &["public-doc"]));
    state.add_fact(Fact::from_symbols("can_access", &["user-1", "secret-doc"]));
    state.add_fact(Fact::from_symbols("can_access", &["user-1", "public-doc"]));

    // Remove access to secret-doc.
    let removed = vec![Fact::from_symbols("can_access", &["user-1", "secret-doc"])];

    let delta = compute_fold_delta(&state, removed, vec![("no_secret_access", &["user-1"])]);
    assert!(delta.is_some());

    let delta = delta.unwrap();
    assert!(delta.apply_and_verify());
    assert_eq!(delta.num_removed(), 1);
    assert_eq!(delta.num_added_checks(), 1);

    // Reconstruct and verify the new state.
    let new_state = delta.reconstruct_new_state(&state).unwrap();
    assert!(!new_state.contains(&Fact::from_symbols("can_access", &["user-1", "secret-doc"])));
    assert!(new_state.contains(&Fact::from_symbols("can_access", &["user-1", "public-doc"])));
}

#[test]
fn test_symbol_table_round_trip() {
    let mut symbols = SymbolTable::new();
    let names = ["app", "service", "dashboard", "http", "rw", "read", "alice"];

    for name in &names {
        symbols.intern(name);
    }

    // All names should be resolvable.
    for name in &names {
        let fe = FieldElement::from_symbol(name);
        assert_eq!(symbols.resolve(fe), Some(*name));
    }
}
