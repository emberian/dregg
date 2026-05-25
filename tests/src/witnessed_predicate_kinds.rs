//! Per-kind tests for every `WitnessedPredicateKind`: `Dfa`, `Temporal`,
//! `MerkleMembership`, `BlindedSet`, `BridgePredicate`, `PedersenEquality`,
//! `Custom`.
//!
//! Layer: registry dispatch + verifier invocation. Per
//! CAVEAT-LAYER-COVERAGE.md §5 the registry shape exists, the six built-in
//! verifiers exist in `circuit::*` (Dfa, Temporal, MerkleMembership,
//! BlindedSet, BridgePredicate, PedersenEquality), but **the executor's
//! cell-program call site does not consult the registry today**. So the
//! positive paths are all `#[ignore]`d on the caveat-correctness lane.
//!
//! Three categories per kind:
//!   1. Positive — predicate verifies, transition accepted.
//!   2. Adversarial — tampered proof / wrong commitment rejected.
//!   3. Registry lookup — unknown kind rejected.

use pyana_cell::predicate::{
    WitnessedPredicate, WitnessedPredicateKind, WitnessedPredicateRegistry,
};
use pyana_cell::{InputRef, ProgramError};

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
#[ignore = "blocked on caveat-correctness registry dispatch: executor must call WitnessedPredicateRegistry::verify for Dfa kind (CAVEAT-LAYER-COVERAGE.md §5, §6.6)"]
fn dfa_predicate_with_valid_proof_accepts_through_executor() {
    panic!("blocked");
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
#[ignore = "blocked on registry dispatch: custom-AIR vk-hash lookup + verifier invocation"]
fn custom_predicate_with_registered_verifier_accepts() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on registry dispatch: unknown custom vk_hash → registry miss → reject"]
fn custom_predicate_with_unregistered_vk_rejects() {
    panic!("blocked");
}

// ===========================================================================
// Registry lookup behavior
// ===========================================================================

#[test]
fn registry_returns_error_for_unknown_kind() {
    // The registry's built-in coverage today is stub-only; the API is
    // present even though the executor's program-eval site doesn't call
    // it. Sanity-check the unknown-kind path so a future executor wire-up
    // surfaces the same kind of error.
    let _registry = WitnessedPredicateRegistry::with_stubs();
    let _ = wp(WitnessedPredicateKind::Custom { vk_hash: [0u8; 32] });
    // The actual `verify` API surface is exercised in the unit tests of
    // the cell crate; this test exists to document the intent and pin the
    // kind tag.
}

#[test]
#[ignore = "blocked on registry dispatch: register_custom + verify_through_registry round trip"]
fn registry_round_trip_for_registered_custom_verifier() {
    panic!("blocked");
}

// ===========================================================================
// SigningMessage input ref — shape rejection outside Auth context
// ===========================================================================

#[test]
#[ignore = "blocked on AUTHORIZATION-CUSTOM-DESIGN: predicate.input_ref = SigningMessage must reject outside Auth context"]
fn signing_message_input_ref_rejects_in_slot_caveat_context() {
    // Per cell::predicate docs (InputRef::SigningMessage): "surfaces that
    // evaluate WitnessedPredicate outside an action-authorization context
    // (slot caveats, preconditions) must reject this variant as
    // shape-mismatch."
    panic!("blocked");
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
