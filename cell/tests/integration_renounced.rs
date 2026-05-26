//! Integration tests: `StateConstraint::Renounced` end-to-end through the
//! default executor-level registry.
//!
//! These tests exercise the full dispatch chain:
//!
//!   CellProgram::evaluate_full
//!     → evaluate_constraint_full (Renounced branch)
//!       → WitnessedPredicateRegistry::verify (NonMembership kind)
//!         → SortedNeighborNonMembershipVerifier
//!
//! They use [`WitnessedPredicateRegistry::default_builtins`] — the same
//! registry the executor installs — so they catch regressions in any layer
//! of the wiring, not just the crypto gadget.
//!
//! # Adversarial coverage
//!
//! - valid neighbor proof + correct commitment → accepted.
//! - candidate == lower neighbor (prover IS in the set) → rejected.
//! - forged adjacency_tag (public sentinel attack) → rejected.
//! - garbage proof bytes (not 96-byte wire format) → rejected.
//! - missing sender in ctx → `MissingContextField` (structural error, not
//!   accepted-under-negation).
//! - no registry in bundle → `SenderMembershipWitnessMissing`.

use pyana_cell::{
    CellProgram, CellState, StateConstraint,
    preconditions::EvalContext,
    predicate::{NonMembershipNeighborProof, WitnessedPredicateRegistry},
    program::{RenouncedSet, TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag},
};

// ─── Helpers ──────────────────────────────────────────────────────────────────

fn renounced_blinded(commitment: [u8; 32]) -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet { commitment },
    }])
}

fn ctx_with_sender(sender: [u8; 32]) -> EvalContext {
    EvalContext {
        sender: Some(sender),
        ..Default::default()
    }
}

/// Evaluate a Renounced program against the default-builtins registry.
fn eval_with_default_registry(
    program: &CellProgram,
    sender: [u8; 32],
    proof_bytes: &[u8],
) -> Result<(), pyana_cell::ProgramError> {
    let registry = WitnessedPredicateRegistry::default_builtins();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let state = CellState::new(0);
    let ctx = ctx_with_sender(sender);
    program.evaluate_full(
        &state,
        None,
        Some(&ctx),
        &TransitionMeta::wildcard(),
        &bundle,
    )
}

// ─── Positive case ────────────────────────────────────────────────────────────

/// A sender that is NOT in the set → Renounced accepts.
///
/// `candidate = 0x05..`, lower = 0x04.., upper = 0x06..` — the candidate
/// falls strictly between the neighbors, so non-membership holds.
#[test]
fn renounced_valid_non_membership_accepted() {
    let commitment = [0xAB; 32];
    let candidate = [0x05u8; 32];
    let proof = NonMembershipNeighborProof::new(&commitment, [0x04u8; 32], [0x06u8; 32]);
    let proof_bytes = proof.to_bytes();

    let program = renounced_blinded(commitment);
    eval_with_default_registry(&program, candidate, &proof_bytes)
        .expect("valid non-membership proof must be accepted");
}

// ─── Adversarial cases ────────────────────────────────────────────────────────

/// Prover IS in the set (candidate == lower) → Renounced rejects.
///
/// The attacker constructs a neighbor proof where `lower` equals the
/// candidate, violating `lower < candidate`. The verifier must reject.
#[test]
fn renounced_candidate_equals_lower_rejected() {
    let commitment = [0xAB; 32];
    let candidate = [0x05u8; 32];
    // lower == candidate — the prover IS at the lower boundary (i.e., in the set).
    let proof = NonMembershipNeighborProof::new(&commitment, candidate, [0x06u8; 32]);
    let proof_bytes = proof.to_bytes();

    let program = renounced_blinded(commitment);
    let err = eval_with_default_registry(&program, candidate, &proof_bytes)
        .expect_err("candidate-equals-lower must be rejected");
    assert!(
        matches!(
            err,
            pyana_cell::ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ),
        "expected WitnessedPredicateRejected(NonMembership), got: {err:?}"
    );
}

/// Prover IS in the set (candidate == upper) → Renounced rejects.
///
/// The attacker constructs a neighbor proof where `upper` equals the
/// candidate, violating `candidate < upper`. The verifier must reject.
#[test]
fn renounced_candidate_equals_upper_rejected() {
    let commitment = [0xAB; 32];
    let candidate = [0x06u8; 32];
    // upper == candidate — the prover IS at the upper boundary.
    let proof = NonMembershipNeighborProof::new(&commitment, [0x04u8; 32], candidate);
    let proof_bytes = proof.to_bytes();

    let program = renounced_blinded(commitment);
    let err = eval_with_default_registry(&program, candidate, &proof_bytes)
        .expect_err("candidate-equals-upper must be rejected");
    assert!(
        matches!(
            err,
            pyana_cell::ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ),
        "expected WitnessedPredicateRejected(NonMembership), got: {err:?}"
    );
}

/// Forged adjacency_tag → Renounced rejects.
///
/// The prior "public sentinel" attack (`AIR-SOUNDNESS-AUDIT.md` finding #2):
/// a prover picks `lower=0x00..`, `upper=0xFF..`, supplies a zero (or
/// arbitrary) tag and claims non-membership for any candidate. The
/// commitment-keyed tag introduced post-audit closes this — the verifier
/// must reject any proof whose tag does not equal
/// `BLAKE3_keyed("pyana-nonmembership-adjacency-v1", commitment||lower||upper)`.
#[test]
fn renounced_forged_adjacency_tag_rejected() {
    let commitment = [0xAB; 32];
    let candidate = [0x05u8; 32];
    // Build a proof with the right lower/upper ordering but a zeroed tag
    // (what the pre-audit sentinel would have used).
    let forged_proof = NonMembershipNeighborProof {
        lower: [0x00u8; 32],
        upper: [0xFFu8; 32],
        adjacency_tag: [0u8; 32], // wrong — not commitment-keyed
    };
    let proof_bytes = forged_proof.to_bytes();

    let program = renounced_blinded(commitment);
    let err = eval_with_default_registry(&program, candidate, &proof_bytes)
        .expect_err("forged adjacency tag must be rejected");
    assert!(
        matches!(
            err,
            pyana_cell::ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ),
        "expected WitnessedPredicateRejected(NonMembership), got: {err:?}"
    );
}

/// Garbage proof bytes (wrong length) → Renounced rejects.
///
/// The wire format is exactly 96 bytes (lower || upper || adjacency_tag).
/// Any other length must be rejected before the sorting checks run.
#[test]
fn renounced_garbage_proof_bytes_rejected() {
    let commitment = [0xAB; 32];
    let candidate = [0x05u8; 32];
    // 64 bytes of 0xAA — not a valid 96-byte neighbor proof.
    let garbage: Vec<u8> = vec![0xAAu8; 64];

    let program = renounced_blinded(commitment);
    let err = eval_with_default_registry(&program, candidate, &garbage)
        .expect_err("garbage proof bytes must be rejected");
    assert!(
        matches!(
            err,
            pyana_cell::ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ),
        "expected WitnessedPredicateRejected(NonMembership), got: {err:?}"
    );
}

/// Empty proof bytes → Renounced rejects.
#[test]
fn renounced_empty_proof_bytes_rejected() {
    let commitment = [0xAB; 32];
    let candidate = [0x05u8; 32];

    let program = renounced_blinded(commitment);
    let err = eval_with_default_registry(&program, candidate, &[])
        .expect_err("empty proof bytes must be rejected");
    assert!(
        matches!(
            err,
            pyana_cell::ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ),
        "expected WitnessedPredicateRejected(NonMembership), got: {err:?}"
    );
}

// ─── Structural sentinel cases ────────────────────────────────────────────────

/// No ctx → `MissingContextField`.
///
/// Fail-closed: if the executor doesn't supply the sender, the constraint
/// is unevaluable (structural error), NOT vacuously satisfied.
#[test]
fn renounced_no_ctx_returns_missing_context_field() {
    let commitment = [0xAB; 32];
    let proof = NonMembershipNeighborProof::new(&commitment, [0x04u8; 32], [0x06u8; 32]);
    let proof_bytes = proof.to_bytes();

    let registry = WitnessedPredicateRegistry::default_builtins();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let state = CellState::new(0);
    let program = renounced_blinded(commitment);

    // No ctx at all.
    let err = program
        .evaluate_full(&state, None, None, &TransitionMeta::wildcard(), &bundle)
        .expect_err("missing ctx must surface MissingContextField");
    assert!(
        matches!(err, pyana_cell::ProgramError::MissingContextField { .. }),
        "expected MissingContextField, got: {err:?}"
    );
}

/// Ctx without sender → `MissingContextField`.
#[test]
fn renounced_ctx_without_sender_returns_missing_context_field() {
    let commitment = [0xAB; 32];
    let proof = NonMembershipNeighborProof::new(&commitment, [0x04u8; 32], [0x06u8; 32]);
    let proof_bytes = proof.to_bytes();

    let registry = WitnessedPredicateRegistry::default_builtins();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let state = CellState::new(0);
    let bare_ctx = EvalContext::default(); // sender: None
    let program = renounced_blinded(commitment);

    let err = program
        .evaluate_full(
            &state,
            None,
            Some(&bare_ctx),
            &TransitionMeta::wildcard(),
            &bundle,
        )
        .expect_err("ctx without sender must surface MissingContextField");
    assert!(
        matches!(err, pyana_cell::ProgramError::MissingContextField { .. }),
        "expected MissingContextField, got: {err:?}"
    );
}

/// No registry in bundle → `SenderMembershipWitnessMissing`.
///
/// The program cannot evaluate without a registry; this is a fail-closed
/// sentinel (not an accept) so the executor must configure a registry.
#[test]
fn renounced_no_registry_returns_sentinel() {
    let commitment = [0xAB; 32];
    let candidate = [0x05u8; 32];
    let proof = NonMembershipNeighborProof::new(&commitment, [0x04u8; 32], [0x06u8; 32]);
    let proof_bytes = proof.to_bytes();

    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    // Registry deliberately absent.
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: None,
    };
    let state = CellState::new(0);
    let ctx = ctx_with_sender(candidate);
    let program = renounced_blinded(commitment);

    let err = program
        .evaluate_full(
            &state,
            None,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &bundle,
        )
        .expect_err("absent registry must surface SenderMembershipWitnessMissing");
    assert!(
        matches!(
            err,
            pyana_cell::ProgramError::SenderMembershipWitnessMissing
        ),
        "expected SenderMembershipWitnessMissing, got: {err:?}"
    );
}

// ─── PublicRoot variant ───────────────────────────────────────────────────────

/// `Renounced { set: PublicRoot { set_root_index } }` reads the commitment
/// from the cell's state slot rather than baking it in.
#[test]
fn renounced_public_root_reads_commitment_from_slot() {
    let commitment = [0xCC; 32];
    let candidate = [0x05u8; 32];
    let proof = NonMembershipNeighborProof::new(&commitment, [0x04u8; 32], [0x06u8; 32]);
    let proof_bytes = proof.to_bytes();

    let registry = WitnessedPredicateRegistry::default_builtins();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    // State: slot 2 holds the set root.
    let mut state = CellState::new(0);
    state.fields[2] = commitment;
    let ctx = ctx_with_sender(candidate);

    let program = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::PublicRoot { set_root_index: 2 },
    }]);
    program
        .evaluate_full(
            &state,
            None,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &bundle,
        )
        .expect(
            "PublicRoot variant must accept valid non-membership proof keyed to the slot value",
        );
}

/// PublicRoot variant: proof keyed to the WRONG commitment is rejected,
/// even if the ordering is valid, because the adjacency tag won't match.
#[test]
fn renounced_public_root_wrong_commitment_rejected() {
    let real_commitment = [0xCC; 32];
    let wrong_commitment = [0xDD; 32];
    let candidate = [0x05u8; 32];
    // Proof is keyed to the wrong commitment.
    let proof = NonMembershipNeighborProof::new(&wrong_commitment, [0x04u8; 32], [0x06u8; 32]);
    let proof_bytes = proof.to_bytes();

    let registry = WitnessedPredicateRegistry::default_builtins();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let mut state = CellState::new(0);
    state.fields[2] = real_commitment; // cell holds the real root
    let ctx = ctx_with_sender(candidate);

    let program = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::PublicRoot { set_root_index: 2 },
    }]);
    let err = program
        .evaluate_full(
            &state,
            None,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &bundle,
        )
        .expect_err("proof keyed to wrong commitment must be rejected");
    assert!(
        matches!(
            err,
            pyana_cell::ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ),
        "expected WitnessedPredicateRejected(NonMembership), got: {err:?}"
    );
}
