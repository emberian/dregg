//! Witnessed-predicate dispatch wiring tests (Cav-Codex Block 3.5).
//!
//! Per CAVEAT-LAYER-COVERAGE.md §7 finding #5: the
//! `WitnessedPredicateRegistry` shape exists, stubs exist, real
//! verifiers exist, but "no call site dispatches through it" — every
//! `StateConstraint::Witnessed` / `Preconditions::Witnessed` evaluation
//! surfaced the legacy `WitnessedPredicateRequiresExecutor` sentinel
//! and the executor mapped it to `TurnError::ProgramViolation`.
//!
//! Block 3.5 fix: `TurnExecutor` now defaults to
//! `Some(WitnessedPredicateRegistry::default_builtins())` on every
//! constructor (`new`, `with_budget_gate`, `with_proof_verifier`), and
//! the slot-caveat program-evaluator + the precondition checker both
//! consult `self.witnessed_registry` when they encounter a witnessed
//! clause.
//!
//! These tests exercise the dispatch surface, not the proof algebra.
//!
//! **Post AIR-soundness audit (commit `ce1e2def`).** The default
//! registry now installs `NotYetWiredVerifier` for the kinds whose real
//! cryptographic verifier lives in `pyana-circuit` / `pyana-bridge`
//! (Dfa, Temporal, MerkleMembership, BlindedSet, BridgePredicate,
//! PedersenEquality) — those verifiers **reject** every proof until a
//! host installs the real adapter. NonMembership ships with the real
//! Silver-Sound `SortedNeighborNonMembershipVerifier` in this crate.
//!
//! For tests that previously relied on `default_builtins()` accepting
//! arbitrary non-empty proof bytes (the stub-verifier behavior), switch
//! to `WitnessedPredicateRegistry::with_stubs()` explicitly — that
//! constructor preserves the prior permissive shape under an honest
//! name and is kept for plumbing-only tests.

use pyana_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry,
};
use pyana_turn::ComputronCosts;
use pyana_turn::TurnExecutor;

// ─────────────────────────────────────────────────────────────────────
// Registry surface tests (default_builtins constructor)
// ─────────────────────────────────────────────────────────────────────

/// The default registry MUST reject Dfa proofs until a host installs the
/// real `pyana_circuit::dsl::circuit` adapter. Prior behavior was to
/// accept any non-empty proof bytes — a soundness loss caught by the
/// AIR audit.
#[test]
fn default_builtins_registry_rejects_dfa_until_host_wires_real_verifier() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let input = PredicateInput::Sender(&pk);
    let err = reg.verify(&wp, &input, b"non-empty-proof").unwrap_err();
    assert!(
        matches!(err, WitnessedPredicateError::Rejected { .. }),
        "Dfa default must REJECT until host installs real verifier; got {err:?}"
    );
}

#[test]
fn default_builtins_registry_rejects_merkle_membership_until_host_wires_real_verifier() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::merkle_membership([2u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let input = PredicateInput::Sender(&pk);
    let err = reg.verify(&wp, &input, b"non-empty-proof").unwrap_err();
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn default_builtins_registry_rejects_blinded_set_until_host_wires_real_verifier() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::blinded_set([3u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"non-empty-proof")
        .unwrap_err();
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn default_builtins_registry_rejects_temporal_bridge_pedersen_until_host_wires_real_verifier() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    for wp in [
        WitnessedPredicate::temporal([4u8; 32], 0, 0),
        WitnessedPredicate::bridge_predicate([5u8; 32], InputRef::PublicInput { pi_index: 0 }, 0),
        WitnessedPredicate::pedersen_equality([6u8; 32], InputRef::Slot { index: 0 }, 0),
    ] {
        let pk = [0u8; 32];
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&pk), b"non-empty-proof")
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "default-builtin {:?} must reject until host installs real verifier; got {err:?}",
            wp.kind
        );
    }
}

/// The `with_stubs()` constructor preserves the *prior* permissive
/// behavior under an explicit, honest name — for plumbing-only tests.
#[test]
fn with_stubs_registry_still_accepts_nonempty_proof_for_plumbing_tests() {
    let reg = WitnessedPredicateRegistry::with_stubs();
    let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    reg.verify(&wp, &PredicateInput::Sender(&pk), b"non-empty-proof")
        .expect("with_stubs() preserves the prior permissive behavior for plumbing tests");
}

#[test]
fn default_builtins_registry_rejects_empty_proof() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"")
        .unwrap_err();
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn default_builtins_registry_unknown_custom_not_registered() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::custom([99u8; 32], [0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"proof")
        .unwrap_err();
    assert!(matches!(
        err,
        WitnessedPredicateError::KindNotRegistered {
            kind: WitnessedPredicateKind::Custom { .. }
        }
    ));
}

// ─────────────────────────────────────────────────────────────────────
// TurnExecutor wiring: the registry is now non-None by default.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn turn_executor_new_defaults_to_default_builtins_registry() {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    assert!(
        executor.witnessed_registry.is_some(),
        "TurnExecutor::new must default-equip the witnessed registry (Block 3.5)"
    );
    let reg = executor.witnessed_registry.as_ref().unwrap();
    // Confirm a builtin is present.
    assert!(reg.get(WitnessedPredicateKind::Dfa).is_some());
    assert!(reg.get(WitnessedPredicateKind::MerkleMembership).is_some());
    assert!(reg.get(WitnessedPredicateKind::BlindedSet).is_some());
    assert!(reg.get(WitnessedPredicateKind::Temporal).is_some());
    assert!(reg.get(WitnessedPredicateKind::BridgePredicate).is_some());
    assert!(reg.get(WitnessedPredicateKind::PedersenEquality).is_some());
}

#[test]
fn turn_executor_can_swap_registry() {
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    // Custom-only registry.
    let mut custom_reg = WitnessedPredicateRegistry::empty();
    struct AcceptAll;
    impl pyana_cell::predicate::WitnessedPredicateVerifier for AcceptAll {
        fn name(&self) -> &'static str {
            "test-accept-all"
        }
        fn kind(&self) -> WitnessedPredicateKind {
            WitnessedPredicateKind::Custom {
                vk_hash: [0xAA; 32],
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
    custom_reg.register_custom([0xAA; 32], std::sync::Arc::new(AcceptAll));
    executor.set_witnessed_registry(custom_reg);

    // The default builtins are now gone.
    let reg = executor.witnessed_registry.as_ref().unwrap();
    assert!(reg.get(WitnessedPredicateKind::Dfa).is_none());
    // The custom kind dispatches.
    let wp = WitnessedPredicate::custom([0xAA; 32], [0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    reg.verify(&wp, &PredicateInput::Sender(&pk), b"any-proof-even-empty")
        .expect("custom AcceptAll verifier should accept");
}

// ─────────────────────────────────────────────────────────────────────
// Tampered witness rejects: empty proof bytes routes through the stub
// rejection path.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn tampered_empty_proof_rejects_through_executor_registry() {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let reg = executor.witnessed_registry.as_ref().unwrap();
    let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"")
        .unwrap_err();
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn unregistered_custom_yields_kind_not_registered_through_executor() {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let reg = executor.witnessed_registry.as_ref().unwrap();
    let wp = WitnessedPredicate::custom([0xFF; 32], [0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"proof")
        .unwrap_err();
    assert!(matches!(
        err,
        WitnessedPredicateError::KindNotRegistered { .. }
    ));
}
