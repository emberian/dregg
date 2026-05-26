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

use dregg_cell::CellId;
use dregg_turn::action::{Action, Authorization, DelegationMode};

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
#[ignore = "blocked on T6 / federation_id binding audit (EXECUTOR-HONESTY-AUDIT.md T6, T13): canonical signing message must include federation_id"]
fn captp_delivered_message_includes_federation_id_for_cross_federation_replay_protection() {
    panic!("blocked");
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
#[ignore = "blocked on AUTHORIZATION-CUSTOM-DESIGN: end-to-end positive — valid Auth::Custom predicate accepts (executor dispatches through WitnessedPredicateRegistry, binds InputRef::SigningMessage)"]
fn auth_custom_with_valid_predicate_accepts() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on AUTHORIZATION-CUSTOM-DESIGN: Auth::Custom predicate with tampered proof rejects"]
fn auth_custom_with_tampered_predicate_proof_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on AUTHORIZATION-CUSTOM-DESIGN: vk_hash mismatch between AuthRequired::Custom and Authorization::Custom must reject (design §10.4)"]
fn auth_custom_vk_hash_mismatch_rejects() {
    panic!("blocked");
}

// ===========================================================================
// Cross-federation replay (T6)
// ===========================================================================

#[test]
#[ignore = "blocked on federation_id binding audit (T6, EXECUTOR-HONESTY-AUDIT.md): action signed for F1 attempted against F2 must reject"]
fn signature_signed_for_federation_a_rejects_on_federation_b() {
    // Build identical Turn data, sign it with federation_id=F1, then
    // attempt to execute it on a federation whose id is F2. Per T6 the
    // canonical signing message must include federation_id; the verifier
    // must recompute and reject.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on federation_id binding audit (T6): bearer-cap delegation includes federation_id in the delegation message"]
fn bearer_signed_for_federation_a_rejects_on_federation_b() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on AUTHORIZATION-CUSTOM-DESIGN §11.5: SigningMessage input is federation-bound (federation_id is in compute_partial_signing_message)"]
fn auth_custom_signed_for_federation_a_rejects_on_federation_b() {
    panic!("blocked");
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
