//! Per-variant tests for every `Authorization` variant: `Signature`,
//! `Proof`, `Breadstuff`, `Bearer`, `Unchecked`, `CapTpDelivered`, `Custom`.
//!
//! Layer: action-hash domain separation + executor verify path.
//!
//! Three categories per variant:
//!   1. Positive — valid auth accepted.
//!   2. Adversarial — tampered auth rejected.
//!   3. Cross-federation replay (T6) — action signed for F1 attempted
//!      against F2 must reject.
//!
//! Many positive tests require key material + a signing oracle and are
//! marked `#[ignore]` until the surface helpers exist in
//! `tests/src/main.rs`'s helper module.

use std::sync::Arc;

use dregg_cell::predicate::{
    InputRef as PredInputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError,
    WitnessedPredicateKind, WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::action::{
    Action, Authorization, BearerCapProof, CommitmentMode, DelegationMode, DelegationProofData,
    WitnessBlob, symbol,
};
use dregg_turn::{CallForest, ComputronCosts, Effect, Turn, TurnBuilder, TurnError, TurnExecutor};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn dummy_action(target: CellId, auth: Authorization) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: auth,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut public_key = [0u8; 32];
    public_key[0] = seed;
    let token_id = [0u8; 32];
    let mut cell = Cell::with_balance(public_key, token_id, balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

fn setup_two_open_cells(agent_balance: u64, target_balance: u64) -> (Ledger, CellId, CellId) {
    let mut ledger = Ledger::new();
    let mut agent = make_open_cell(1, agent_balance);
    let target = make_open_cell(2, target_balance);
    let agent_id = agent.id();
    let target_id = target.id();
    agent.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(target).unwrap();
    (ledger, agent_id, target_id)
}

struct ExpectedCustomAuthVerifier {
    vk_hash: [u8; 32],
    expected_message: Vec<u8>,
    expected_proof: Vec<u8>,
}

impl WitnessedPredicateVerifier for ExpectedCustomAuthVerifier {
    fn name(&self) -> &'static str {
        "expected-custom-auth-test-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        _commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        match input {
            PredicateInput::SigningMessage(bytes) if *bytes == self.expected_message.as_slice() => {
            }
            PredicateInput::SigningMessage(_) => {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: self.name(),
                    reason: "signing message mismatch".into(),
                });
            }
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "SigningMessage",
                    actual: "non-SigningMessage",
                });
            }
        }
        if proof_bytes != self.expected_proof {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "proof mismatch".into(),
            });
        }
        Ok(())
    }
}

fn make_custom_action(
    target: CellId,
    predicate: WitnessedPredicate,
    proof_bytes: Vec<u8>,
) -> Action {
    Action {
        target,
        method: symbol("custom_authd_op"),
        args: vec![],
        authorization: Authorization::Custom { predicate },
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index: 0,
            value: [42u8; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![WitnessBlob::proof(proof_bytes)],
    }
}

fn wrap_in_turn(agent: CellId, action: Action) -> Turn {
    let mut builder = TurnBuilder::new(agent, 0);
    builder.add_action(action);
    builder.fee(0).build()
}

// ===========================================================================
// Action::hash domain separation: every Authorization variant must hash
// distinctly so a tampering executor can't swap one for another.
// ===========================================================================

#[test]
fn action_hash_differs_across_authorization_variants() {
    let target = CellId([7u8; 32]);

    let sig = Authorization::Signature([1u8; 32], [2u8; 32]);
    let proof = Authorization::Proof {
        proof_bytes: vec![0u8; 8],
        bound_action: "act".to_string(),
        bound_resource: "res".to_string(),
    };
    let breadstuff = Authorization::Breadstuff([3u8; 32]);
    let unchecked = Authorization::Unchecked;

    let h_sig = dummy_action(target, sig).hash();
    let h_proof = dummy_action(target, proof).hash();
    let h_breadstuff = dummy_action(target, breadstuff).hash();
    let h_unchecked = dummy_action(target, unchecked).hash();

    assert_ne!(h_sig, h_proof);
    assert_ne!(h_sig, h_breadstuff);
    assert_ne!(h_sig, h_unchecked);
    assert_ne!(h_proof, h_breadstuff);
    assert_ne!(h_proof, h_unchecked);
    assert_ne!(h_breadstuff, h_unchecked);
}

#[test]
fn action_hash_tamper_signature_changes_hash() {
    let target = CellId([7u8; 32]);
    let a1 = dummy_action(target, Authorization::Signature([1u8; 32], [2u8; 32]));
    let a2 = dummy_action(target, Authorization::Signature([1u8; 32], [3u8; 32]));
    assert_ne!(a1.hash(), a2.hash(), "sig tamper must change action hash");
}

#[test]
fn action_hash_tamper_breadstuff_token_changes_hash() {
    let target = CellId([7u8; 32]);
    let a1 = dummy_action(target, Authorization::Breadstuff([1u8; 32]));
    let a2 = dummy_action(target, Authorization::Breadstuff([2u8; 32]));
    assert_ne!(a1.hash(), a2.hash());
}

#[test]
fn action_hash_tamper_proof_bytes_changes_hash() {
    let target = CellId([7u8; 32]);
    let a1 = dummy_action(
        target,
        Authorization::Proof {
            proof_bytes: vec![0u8; 8],
            bound_action: "act".to_string(),
            bound_resource: "res".to_string(),
        },
    );
    let a2 = dummy_action(
        target,
        Authorization::Proof {
            proof_bytes: vec![1u8; 8],
            bound_action: "act".to_string(),
            bound_resource: "res".to_string(),
        },
    );
    assert_ne!(a1.hash(), a2.hash());
}

#[test]
fn action_hash_tamper_proof_bound_resource_changes_hash() {
    let target = CellId([7u8; 32]);
    let a1 = dummy_action(
        target,
        Authorization::Proof {
            proof_bytes: vec![0u8; 8],
            bound_action: "act".to_string(),
            bound_resource: "res-a".to_string(),
        },
    );
    let a2 = dummy_action(
        target,
        Authorization::Proof {
            proof_bytes: vec![0u8; 8],
            bound_action: "act".to_string(),
            bound_resource: "res-b".to_string(),
        },
    );
    assert_ne!(
        a1.hash(),
        a2.hash(),
        "bound_resource is part of the prover-binding string and must be in the action hash"
    );
}

// ===========================================================================
// Bearer
// ===========================================================================

#[test]
fn action_hash_bearer_signed_delegation_differs_from_stark_delegation() {
    let target = CellId([8u8; 32]);
    let signed = Authorization::Bearer(BearerCapProof {
        target,
        permissions: dregg_cell::AuthRequired::None,
        delegation_proof: DelegationProofData::SignedDelegation {
            delegator_pk: [1u8; 32],
            signature: [0u8; 64],
            bearer_pk: [2u8; 32],
        },
        expires_at: 100,
        revocation_channel: None,
        allowed_effects: None,
    });
    let stark = Authorization::Bearer(BearerCapProof {
        target,
        permissions: dregg_cell::AuthRequired::None,
        delegation_proof: DelegationProofData::StarkDelegation {
            proof_bytes: vec![],
            root_issuer_commitment: [9u8; 32],
        },
        expires_at: 100,
        revocation_channel: None,
        allowed_effects: None,
    });
    assert_ne!(
        dummy_action(target, signed).hash(),
        dummy_action(target, stark).hash()
    );
}

// ===========================================================================
// CapTpDelivered
// ===========================================================================

#[test]
fn captp_delivered_signing_message_differs_per_turn() {
    use dregg_turn::action::Effect as Eff;
    let agent = CellId([10u8; 32]);
    let target = CellId([11u8; 32]);
    let cert_nonce = [0u8; 32];
    let effects_a = vec![Eff::Transfer {
        from: agent,
        to: target,
        amount: 10,
    }];
    let effects_b = vec![Eff::Transfer {
        from: agent,
        to: target,
        amount: 11,
    }];

    let msg_a =
        Authorization::captp_delivered_signing_message(&cert_nonce, &agent, &target, 7, &effects_a);
    let msg_b =
        Authorization::captp_delivered_signing_message(&cert_nonce, &agent, &target, 7, &effects_b);
    assert_ne!(
        msg_a, msg_b,
        "different effects must produce different message"
    );

    let msg_c =
        Authorization::captp_delivered_signing_message(&cert_nonce, &agent, &target, 8, &effects_a);
    assert_ne!(
        msg_a, msg_c,
        "different turn_nonce must produce different message"
    );
}

#[test]
fn captp_delivered_signing_message_includes_domain_separator() {
    let cert_nonce = [0u8; 32];
    let agent = CellId([1u8; 32]);
    let target = CellId([2u8; 32]);
    let msg = Authorization::captp_delivered_signing_message(&cert_nonce, &agent, &target, 0, &[]);
    assert!(
        msg.starts_with(b"dregg-captp-delivered-v1"),
        "missing domain separator"
    );
}

#[test]
fn captp_delivered_message_includes_federation_id_for_cross_federation_replay_protection() {
    let cert_nonce = [0xA5u8; 32];
    let agent = CellId([1u8; 32]);
    let target = CellId([2u8; 32]);
    let fed_a = [0x11u8; 32];
    let fed_b = [0x22u8; 32];
    let effects = vec![dregg_turn::action::Effect::SetField {
        cell: target,
        index: 0,
        value: [9u8; 32],
    }];

    let signed_for_a = Authorization::captp_delivered_signing_message_for_federation(
        &fed_a,
        &cert_nonce,
        &agent,
        &target,
        7,
        &effects,
    );
    let replayed_at_b = Authorization::captp_delivered_signing_message_for_federation(
        &fed_b,
        &cert_nonce,
        &agent,
        &target,
        7,
        &effects,
    );

    assert!(signed_for_a.starts_with(b"dregg-captp-delivered-v2"));
    assert_ne!(
        signed_for_a, replayed_at_b,
        "CapTP delivery signatures must be federation-bound"
    );
}

// ===========================================================================
// Custom (Authorization)
// ===========================================================================

#[test]
fn action_hash_custom_predicate_tamper_changes_hash() {
    use dregg_cell::InputRef;
    use dregg_cell::predicate::WitnessedPredicate;
    let target = CellId([12u8; 32]);
    let p1 = WitnessedPredicate::dfa([1u8; 32], InputRef::SigningMessage, 0);
    let p2 = WitnessedPredicate::dfa([2u8; 32], InputRef::SigningMessage, 0);
    let a1 = dummy_action(
        target,
        Authorization::Custom {
            predicate: p1.clone(),
        },
    );
    let a2 = dummy_action(
        target,
        Authorization::Custom {
            predicate: p2.clone(),
        },
    );
    assert_ne!(
        a1.hash(),
        a2.hash(),
        "tampering with the Custom predicate must change the action hash"
    );

    // Different kind, same commitment must also differ:
    let p3 = WitnessedPredicate::merkle_membership([1u8; 32], InputRef::SigningMessage, 0);
    let a3 = dummy_action(target, Authorization::Custom { predicate: p3 });
    assert_ne!(a1.hash(), a3.hash(), "tampering kind must change hash");
}

#[test]
fn auth_custom_with_valid_predicate_accepts() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(1000, 0);
    let federation_id = [0xF1u8; 32];
    let vk_hash = [0x42u8; 32];
    let proof = b"valid-custom-auth-proof".to_vec();

    let predicate = WitnessedPredicate::custom(vk_hash, [0u8; 32], PredInputRef::SigningMessage, 0);
    let action = make_custom_action(target_id, predicate.clone(), proof.clone());
    let expected_message =
        TurnExecutor::compute_custom_signing_message(&action, &predicate, 0, &federation_id, 0);

    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExpectedCustomAuthVerifier {
            vk_hash,
            expected_message,
            expected_proof: proof,
        }),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(federation_id);
    executor.set_witnessed_registry(registry);

    let result = executor.execute(&wrap_in_turn(agent_id, action), &mut ledger);
    assert!(
        result.is_committed(),
        "valid Authorization::Custom turn should commit, got {result:?}"
    );
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [42u8; 32]);
}

#[test]
fn auth_custom_with_tampered_predicate_proof_rejects() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(1000, 0);
    let federation_id = [0xF2u8; 32];
    let vk_hash = [0x55u8; 32];

    let predicate = WitnessedPredicate::custom(vk_hash, [0u8; 32], PredInputRef::SigningMessage, 0);
    let action = make_custom_action(target_id, predicate.clone(), b"tampered-proof".to_vec());
    let expected_message =
        TurnExecutor::compute_custom_signing_message(&action, &predicate, 0, &federation_id, 0);

    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExpectedCustomAuthVerifier {
            vk_hash,
            expected_message,
            expected_proof: b"valid-proof".to_vec(),
        }),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(federation_id);
    executor.set_witnessed_registry(registry);

    let result = executor.execute(&wrap_in_turn(agent_id, action), &mut ledger);
    assert!(result.is_rejected(), "tampered Custom proof must reject");
    match result.unwrap_rejected().0 {
        TurnError::InvalidAuthorization { reason } => {
            assert!(
                reason.contains("Custom auth predicate rejected")
                    && reason.contains("proof mismatch"),
                "expected proof-mismatch Custom rejection, got: {reason}"
            );
        }
        other => panic!("expected InvalidAuthorization, got {other:?}"),
    }
}

#[test]
fn auth_custom_vk_hash_mismatch_rejects() {
    let mut ledger = Ledger::new();
    let mut agent = make_open_cell(1, 1000);
    let mut target = make_open_cell(2, 0);
    let agent_id = agent.id();
    let target_id = target.id();
    let required_vk = [0xAAu8; 32];
    let action_vk = [0xBBu8; 32];
    target.permissions.set_state = AuthRequired::Custom {
        vk_hash: required_vk,
    };
    agent.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(target).unwrap();

    let proof = b"valid-proof".to_vec();
    let predicate =
        WitnessedPredicate::custom(action_vk, [0u8; 32], PredInputRef::SigningMessage, 0);
    let action = make_custom_action(target_id, predicate.clone(), proof.clone());
    let expected_message =
        TurnExecutor::compute_custom_signing_message(&action, &predicate, 0, &[0u8; 32], 0);

    let mut registry = WitnessedPredicateRegistry::empty();
    for vk_hash in [required_vk, action_vk] {
        registry.register_custom(
            vk_hash,
            Arc::new(ExpectedCustomAuthVerifier {
                vk_hash,
                expected_message: expected_message.clone(),
                expected_proof: proof.clone(),
            }),
        );
    }

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_witnessed_registry(registry);

    let result = executor.execute(&wrap_in_turn(agent_id, action), &mut ledger);
    assert!(result.is_rejected(), "Custom vk_hash mismatch must reject");
    match result.unwrap_rejected().0 {
        TurnError::PermissionDenied { required, .. } => {
            assert_eq!(
                required,
                AuthRequired::Custom {
                    vk_hash: required_vk
                }
            );
        }
        other => panic!("expected PermissionDenied, got {other:?}"),
    }
}

// ===========================================================================
// Cross-federation replay (T6)
// ===========================================================================

#[test]
fn signature_signed_for_federation_a_rejects_on_federation_b() {
    let target = CellId([7u8; 32]);
    let mut action = dummy_action(target, Authorization::Signature([1u8; 32], [2u8; 32]));
    action.effects.push(Effect::SetField {
        cell: target,
        index: 0,
        value: [3u8; 32],
    });

    let fed_a = [0xA1u8; 32];
    let fed_b = [0xB2u8; 32];
    let signed_for_a = TurnExecutor::compute_signing_message(&action, &fed_a);
    let verifier_at_b = TurnExecutor::compute_signing_message(&action, &fed_b);

    assert_ne!(
        signed_for_a, verifier_at_b,
        "Signature auth verifier recomputes a different message in another federation"
    );
}

#[test]
fn bearer_signed_for_federation_a_rejects_on_federation_b() {
    let target = CellId([8u8; 32]);
    let permissions = dregg_cell::AuthRequired::Signature;
    let bearer_pk = [0x44u8; 32];
    let expires_at = 100;
    let fed_a = [0xA1u8; 32];
    let fed_b = [0xB2u8; 32];

    let signed_for_a = TurnExecutor::compute_bearer_delegation_message(
        &target,
        &permissions,
        &bearer_pk,
        expires_at,
        &fed_a,
    );
    let verifier_at_b = TurnExecutor::compute_bearer_delegation_message(
        &target,
        &permissions,
        &bearer_pk,
        expires_at,
        &fed_b,
    );

    assert_ne!(
        signed_for_a, verifier_at_b,
        "Bearer delegation signatures must be federation-bound"
    );
}

#[test]
fn auth_custom_signed_for_federation_a_rejects_on_federation_b() {
    use dregg_cell::InputRef;
    use dregg_cell::predicate::WitnessedPredicate;

    let target = CellId([12u8; 32]);
    let predicate =
        WitnessedPredicate::custom([0x55u8; 32], [0x66u8; 32], InputRef::SigningMessage, 0);
    let action = dummy_action(
        target,
        Authorization::Custom {
            predicate: predicate.clone(),
        },
    );
    let fed_a = [0xA1u8; 32];
    let fed_b = [0xB2u8; 32];

    let signed_for_a =
        TurnExecutor::compute_custom_signing_message(&action, &predicate, 0, &fed_a, 9);
    let verifier_at_b =
        TurnExecutor::compute_custom_signing_message(&action, &predicate, 0, &fed_b, 9);

    assert_ne!(
        signed_for_a, verifier_at_b,
        "Custom SigningMessage input must be federation-bound"
    );
}

// ===========================================================================
// Compile-time exhaustiveness across the Authorization enum
// ===========================================================================

#[allow(dead_code)]
fn touch_every_authorization(a: &Authorization) -> &'static str {
    match a {
        Authorization::Signature(_, _) => "signature",
        Authorization::Proof { .. } => "proof",
        Authorization::Breadstuff(_) => "breadstuff",
        Authorization::Bearer(_) => "bearer",
        Authorization::Unchecked => "unchecked",
        Authorization::CapTpDelivered { .. } => "captp_delivered",
        Authorization::Custom { .. } => "custom",
        // 1-of-N disjunctive authorization. Soundness contract documented
        // in turn::action — `proof_index` selects the satisfying candidate.
        Authorization::OneOf { .. } => "one_of",
    }
}

#[test]
fn touch_each_variant_test() {
    let s = touch_every_authorization(&Authorization::Unchecked);
    assert_eq!(s, "unchecked");
}

// Ensure Turn type round-trips (no panic) — sanity for the harness.
#[test]
fn turn_with_each_unsigned_auth_constructs_without_panic() {
    use std::collections::HashMap;
    let target = CellId([99u8; 32]);
    for auth in [
        Authorization::Unchecked,
        Authorization::Signature([1u8; 32], [2u8; 32]),
        Authorization::Breadstuff([5u8; 32]),
    ] {
        let mut forest = CallForest::new();
        let action = dummy_action(target, auth.clone());
        forest.add_root(action);
        let _turn = Turn {
            agent: target,
            nonce: 0,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
    }
    // Touch unused Effect to keep imports tidy.
    let _ = Effect::Transfer {
        from: target,
        to: target,
        amount: 0,
    };
}
