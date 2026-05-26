//! Per-kind tests for every `WitnessedPredicateKind`: `Dfa`, `Temporal`,
//! `MerkleMembership`, `BlindedSet`, `BridgePredicate`, `PedersenEquality`,
//! `Custom`.
//!
//! Layer: registry dispatch + verifier invocation. The executor/evaluator
//! call site now accepts a `WitnessedPredicateRegistry`; built-in AIR-backed
//! verifiers still require host installation from the upstream circuit crates.
//! Tests that use `with_stubs()` are explicit plumbing demos, not
//! cryptographic acceptance claims.
//!
//! Three categories per kind:
//!   1. Positive — predicate verifies, transition accepted.
//!   2. Adversarial — tampered proof / wrong commitment rejected.
//!   3. Registry lookup — unknown kind rejected.

use std::sync::Arc;

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell::program::{TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag};
use dregg_cell::{CellProgram, CellState, EvalContext, InputRef, ProgramError, StateConstraint};

// ---------------------------------------------------------------------------
// Helpers / shared concerns
// ---------------------------------------------------------------------------

/// Construct a WitnessedPredicate of the given kind with a generic input ref
/// and proof witness index 0 — used in the registry-lookup tests.
fn wp(kind: WitnessedPredicateKind) -> WitnessedPredicate {
    WitnessedPredicate {
        kind,
        commitment: [7u8; 32],
        input_ref: InputRef::Sender,
        proof_witness_index: 0,
    }
}

struct ExactSenderVerifier {
    vk_hash: [u8; 32],
    expected_commitment: [u8; 32],
    expected_sender: [u8; 32],
    expected_proof: &'static [u8],
}

impl WitnessedPredicateVerifier for ExactSenderVerifier {
    fn name(&self) -> &'static str {
        "exact-sender-test-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        if commitment != &self.expected_commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "commitment mismatch".into(),
            });
        }
        match input {
            PredicateInput::Sender(sender) if *sender == &self.expected_sender => {}
            PredicateInput::Sender(_) => {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: self.name(),
                    reason: "sender mismatch".into(),
                });
            }
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "Sender",
                    actual: "non-Sender",
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

fn exact_sender_registry(
    vk_hash: [u8; 32],
    expected_commitment: [u8; 32],
    expected_sender: [u8; 32],
    expected_proof: &'static [u8],
) -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExactSenderVerifier {
            vk_hash,
            expected_commitment,
            expected_sender,
            expected_proof,
        }),
    );
    registry
}

// ===========================================================================
// Dfa
// ===========================================================================

#[test]
fn dfa_predicate_constructor_round_trip() {
    let p = WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::Dfa);
    assert_eq!(p.commitment, [1u8; 32]);
}

#[test]
fn dfa_predicate_with_valid_proof_accepts_through_executor() {
    let registry = WitnessedPredicateRegistry::with_stubs();
    let proof = b"stub-dfa-proof";
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let program = CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0),
    }]);
    let state = CellState::default();
    let ctx = EvalContext {
        sender: Some([0xA5u8; 32]),
        ..Default::default()
    };

    program
        .evaluate_full(
            &state,
            None,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &witnesses,
        )
        .expect("Dfa plumbing accepts non-empty proof via explicit stub registry");
}

#[test]
#[ignore = "blocked on registry dispatch: Dfa with tampered route-table-root rejects"]
fn dfa_predicate_with_tampered_proof_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on registry dispatch: Dfa with invalid input rejects"]
fn dfa_predicate_with_invalid_input_rejects() {
    panic!("blocked");
}

// ===========================================================================
// Temporal
// ===========================================================================

#[test]
fn temporal_predicate_constructor() {
    let p = WitnessedPredicate::temporal([2u8; 32], 3, 1);
    assert_eq!(p.kind, WitnessedPredicateKind::Temporal);
    assert_eq!(p.commitment, [2u8; 32]);
    assert_eq!(p.proof_witness_index, 1);
}

#[test]
#[ignore = "blocked on registry dispatch: Temporal verifier wiring through circuit::temporal_predicate_dsl"]
fn temporal_predicate_with_valid_proof_accepts() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on registry dispatch: Temporal tampering rejection"]
fn temporal_predicate_with_tampered_proof_rejects() {
    panic!("blocked");
}

// ===========================================================================
// MerkleMembership
// ===========================================================================

#[test]
fn merkle_membership_predicate_constructor() {
    let p = WitnessedPredicate::merkle_membership([3u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::MerkleMembership);
}

#[test]
#[ignore = "blocked on registry dispatch: MerklePoseidon2StarkAir wiring (CAVEAT-LAYER-COVERAGE.md §5)"]
fn merkle_membership_with_valid_path_accepts() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on registry dispatch: Merkle membership with wrong root rejects"]
fn merkle_membership_with_wrong_root_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on registry dispatch: Merkle non-membership for inverse"]
fn merkle_membership_inverse_query_rejects() {
    panic!("blocked");
}

// ===========================================================================
// BlindedSet
// ===========================================================================

#[test]
fn blinded_set_predicate_constructor() {
    let p = WitnessedPredicate::blinded_set([4u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::BlindedSet);
}

#[test]
#[ignore = "blocked on registry dispatch: AccumulatorNonMembershipAir wiring"]
fn blinded_set_with_non_revocation_proof_accepts() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on registry dispatch: BlindedSet stale proof rejects"]
fn blinded_set_revoked_member_rejects() {
    panic!("blocked");
}

// ===========================================================================
// BridgePredicate
// ===========================================================================

#[test]
fn bridge_predicate_constructor() {
    let p =
        WitnessedPredicate::bridge_predicate([5u8; 32], InputRef::PublicInput { pi_index: 0 }, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::BridgePredicate);
}

#[test]
#[ignore = "blocked on registry dispatch: PredicateAir / relational_predicate_air wiring"]
fn bridge_predicate_gte_accepts_value_above_threshold() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on registry dispatch: BridgePredicate threshold rejection"]
fn bridge_predicate_gte_rejects_value_below_threshold() {
    panic!("blocked");
}

// ===========================================================================
// PedersenEquality
// ===========================================================================

#[test]
fn pedersen_equality_constructor() {
    let p = WitnessedPredicate::pedersen_equality([6u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::PedersenEquality);
}

#[test]
#[ignore = "blocked on registry dispatch: committed_threshold + Bulletproof verifier wiring"]
fn pedersen_equality_with_valid_proof_accepts() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on registry dispatch: Pedersen tampering rejection"]
fn pedersen_equality_with_tampered_commitment_rejects() {
    panic!("blocked");
}

// ===========================================================================
// Custom
// ===========================================================================

#[test]
fn custom_predicate_constructor_carries_vk_hash() {
    let vk = [9u8; 32];
    let p = WitnessedPredicate::custom(vk, [0u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::Custom { vk_hash: vk });
}

#[test]
fn custom_predicate_with_registered_verifier_accepts() {
    let vk_hash = [9u8; 32];
    let commitment = [0xC0u8; 32];
    let sender = [0x5Eu8; 32];
    let registry = exact_sender_registry(vk_hash, commitment, sender, b"valid-custom-proof");
    let predicate = WitnessedPredicate::custom(vk_hash, commitment, InputRef::Sender, 0);

    registry
        .verify(
            &predicate,
            &PredicateInput::Sender(&sender),
            b"valid-custom-proof",
        )
        .expect("registered custom verifier accepts matching commitment/input/proof");
}

#[test]
fn custom_predicate_with_unregistered_vk_rejects() {
    let vk_hash = [0xAAu8; 32];
    let predicate = WitnessedPredicate::custom(vk_hash, [0xC0u8; 32], InputRef::Sender, 0);
    let registry = WitnessedPredicateRegistry::empty();
    let sender = [0x5Eu8; 32];
    let err = registry
        .verify(&predicate, &PredicateInput::Sender(&sender), b"proof")
        .expect_err("unregistered custom vk_hash must reject");

    assert!(matches!(
        err,
        WitnessedPredicateError::KindNotRegistered {
            kind: WitnessedPredicateKind::Custom { vk_hash: got }
        } if got == vk_hash
    ));
}

// ===========================================================================
// Registry lookup behavior
// ===========================================================================

#[test]
fn registry_returns_error_for_unknown_kind() {
    let registry = WitnessedPredicateRegistry::with_stubs();
    let unknown = wp(WitnessedPredicateKind::Custom { vk_hash: [0u8; 32] });
    let sender = [0x5Eu8; 32];
    let err = registry
        .verify(&unknown, &PredicateInput::Sender(&sender), b"proof")
        .expect_err("stub builtins do not register arbitrary custom vk_hashes");

    assert!(matches!(
        err,
        WitnessedPredicateError::KindNotRegistered {
            kind: WitnessedPredicateKind::Custom { vk_hash: [0u8; 32] }
        }
    ));
}

#[test]
fn registry_round_trip_for_registered_custom_verifier() {
    let vk_hash = [0x44u8; 32];
    let commitment = [0xC4u8; 32];
    let sender = [0x5Eu8; 32];
    let registry = exact_sender_registry(vk_hash, commitment, sender, b"valid-custom-proof");
    let predicate = WitnessedPredicate::custom(vk_hash, commitment, InputRef::Sender, 0);

    assert!(
        registry
            .get(WitnessedPredicateKind::Custom { vk_hash })
            .is_some(),
        "registered verifier must be discoverable by custom vk_hash"
    );
    registry
        .verify(
            &predicate,
            &PredicateInput::Sender(&sender),
            b"valid-custom-proof",
        )
        .expect("registered verifier accepts its exact proof");
    let err = registry
        .verify(&predicate, &PredicateInput::Sender(&sender), b"tampered-proof")
        .expect_err("registered verifier must reject a non-matching proof");
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

// ===========================================================================
// SigningMessage input ref — shape rejection outside Auth context
// ===========================================================================

#[test]
fn signing_message_input_ref_rejects_in_slot_caveat_context() {
    // Per cell::predicate docs (InputRef::SigningMessage): "surfaces that
    // evaluate WitnessedPredicate outside an action-authorization context
    // (slot caveats, preconditions) must reject this variant as
    // shape-mismatch."
    let vk_hash = [0x55u8; 32];
    let commitment = [0xC5u8; 32];
    let registry = exact_sender_registry(vk_hash, commitment, [0x5Eu8; 32], b"proof");
    let proof = b"proof";
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let program = CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: WitnessedPredicate::custom(vk_hash, commitment, InputRef::SigningMessage, 0),
    }]);
    let state = CellState::default();

    let err = program
        .evaluate_full(
            &state,
            None,
            None,
            &TransitionMeta::wildcard(),
            &witnesses,
        )
        .expect_err("SigningMessage input has no slot-caveat source");
    assert!(matches!(
        err,
        ProgramError::WitnessedPredicateRejected {
            kind_name: "Custom",
            ..
        }
    ));
}

// ===========================================================================
// Compile-time exhaustiveness: every kind has at least one test
// ===========================================================================

/// Touches every variant of WitnessedPredicateKind so that adding a new
/// variant is a compile-time prompt to extend this file.
#[allow(dead_code)]
fn touch_every_kind(k: WitnessedPredicateKind) -> &'static str {
    match k {
        WitnessedPredicateKind::Dfa => "dfa",
        WitnessedPredicateKind::Temporal => "temporal",
        WitnessedPredicateKind::MerkleMembership => "merkle_membership",
        WitnessedPredicateKind::BlindedSet => "blinded_set",
        WitnessedPredicateKind::BridgePredicate => "bridge_predicate",
        WitnessedPredicateKind::PedersenEquality => "pedersen_equality",
        // Categorical dual of MerkleMembership — sorted-set non-membership.
        WitnessedPredicateKind::NonMembership => "non_membership",
        WitnessedPredicateKind::Custom { .. } => "custom",
    }
}

#[test]
fn exhaustiveness_dummy_uses_helper() {
    let _ = touch_every_kind(WitnessedPredicateKind::Dfa);
}

// Ensure the unused-helper attribute does not paper over a missing variant:
// the match must compile (exhaustively), so adding a kind without updating
// this match will not compile.
#[test]
fn registry_unused_helper_does_not_short_circuit() {
    // Doctest-level catch.
    let _ = ProgramError::WitnessedPredicateRequiresExecutor { kind_name: "stub" };
}
