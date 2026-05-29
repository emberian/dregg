//! Protocol-coverage gate (Pillar 2 of the test/gates initiative, #142).
//!
//! "Verification means something" only if the gates actually exercise the
//! protocol. This file is a **compile-time forcing function**: each exhaustive
//! `match` below has one arm per variant of a core protocol enum (`Effect`,
//! `Authorization`, `StateConstraint`), so **adding a new variant breaks this
//! test's compilation until someone classifies it** — covered by a real
//! executor-invoking flow, or explicitly not-yet-covered. Silent, untested
//! protocol growth is therefore impossible.
//!
//! Honesty contract: an arm is `true` ONLY where a test in this workspace
//! actually drives that variant through `TurnExecutor::execute` /
//! `EmbeddedExecutor::submit_action` with real accept/reject assertions
//! (the coverage_* suites, the cross-app composition e2e, the per-app
//! integration suites, and the #111–#116 apply-path tests). Where coverage is
//! unconfirmed, the arm is conservatively `false` — under-claiming, never
//! over-claiming. The ratchets only shrink.
//!
//! This gate runs under `cargo test --workspace` (CI ci.yml), so it is
//! enforced, not advisory (Pillar 3).

use dregg_cell::StateConstraint;
use dregg_turn::action::{Authorization, Effect};

/// Returns `true` iff this `Effect` variant is exercised end-to-end by at
/// least one executor-invoking test in this workspace. Exhaustive by design.
fn effect_executor_coverage(e: &Effect) -> bool {
    match e {
        // ── Covered: driven through the executor by a real test ──────────
        Effect::SetField { .. } => true, // cross_app_composition_e2e, many
        Effect::Transfer { .. } => true, // bilateral/transfer suites
        Effect::GrantCapability { .. } => true, // capability/grant tests
        Effect::RevokeCapability { .. } => true, // revocation tests
        Effect::EmitEvent { .. } => true, // cross_app_composition_e2e
        Effect::IncrementNonce { .. } => true, // sdk agent_demo / runtime
        Effect::CreateCell { .. } => true, // ledger/create tests
        Effect::SetVerificationKey { .. } => true, // VK integrity tests
        Effect::SpawnWithDelegation { .. } => true, // delegation suite
        Effect::RefreshDelegation => true,          // delegation suite
        Effect::RevokeDelegation { .. } => true,    // delegation suite
        Effect::BridgeMint { .. } => true,          // bridge tests
        Effect::BridgeLock { .. } => true,          // bridge tests
        Effect::CreateObligation { .. } => true,    // #113 apply test
        Effect::FulfillObligation { .. } => true,   // #112 apply test
        Effect::SlashObligation { .. } => true,     // obligation suite
        Effect::CreateEscrow { .. } => true,        // escrow suite
        Effect::ReleaseEscrow { .. } => true,       // escrow suite
        Effect::RefundEscrow { .. } => true,        // escrow suite
        Effect::ExerciseViaCapability { .. } => true, // #111 apply test
        Effect::ExportSturdyRef { .. } => true,     // captp/#96 tests
        Effect::EnlivenRef { .. } => true,          // captp/#96 tests
        Effect::DropRef { .. } => true,             // captp gc tests
        Effect::ValidateHandoff { .. } => true,     // captp handoff tests
        Effect::CellSeal { .. } => true,            // integration_lifecycle
        Effect::CellUnseal { .. } => true,          // integration_lifecycle
        Effect::CellDestroy { .. } => true,         // integration_destroy_terminal
        Effect::Burn { .. } => true,                // integration_burn_receipt
        Effect::AttenuateCapability { .. } => true, // integration_attenuate_capability
        Effect::ReceiptArchive { .. } => true,      // integration_attestation_archive
        // coverage_queue_effects.rs:
        Effect::QueueAllocate { .. } => true,
        Effect::QueueEnqueue { .. } => true,
        Effect::QueueDequeue { .. } => true,
        Effect::QueueResize { .. } => true,
        Effect::QueueAtomicTx { .. } => true,
        Effect::QueuePipelineStep { .. } => true,
        // coverage_misc_effects.rs:
        Effect::NoteCreate { .. } => true,
        Effect::CreateSealPair { .. } => true,
        Effect::Seal { .. } => true,
        Effect::CreateCommittedEscrow { .. } => true,
        Effect::ReleaseCommittedEscrow { .. } => true,
        Effect::RefundCommittedEscrow { .. } => true,
        Effect::BridgeFinalize { .. } => true,
        Effect::BridgeCancel { .. } => true,
        Effect::Introduce { .. } => true,
        Effect::MakeSovereign { .. } => true,
        Effect::CreateCellFromFactory { .. } => true,
        Effect::SetPermissions { .. } => true,
        Effect::Refusal { .. } => true,

        Effect::Unseal { .. } => true, // coverage_misc_effects Seal->Unseal round-trip (#144 fixed)

        // ── Not yet covered: documented blockers (#142 work-list) ────────
        Effect::NoteSpend { .. } => false,    // needs the real ZK spending-proof stack
        Effect::PipelinedSend { .. } => false, // only valid inside a pipeline resolution pass
    }
}

/// `Effect` variants not yet exercised end-to-end (the #142 work-list).
const NOT_YET_COVERED: &[&str] = &["NoteSpend", "PipelinedSend"];

/// Ratchet: the number of not-yet-covered `Effect` variants may only DECREASE.
const MAX_UNCOVERED_EFFECTS: usize = 2;

#[test]
fn effect_coverage_ratchet_only_shrinks() {
    assert!(
        NOT_YET_COVERED.len() <= MAX_UNCOVERED_EFFECTS,
        "not-yet-covered Effect count {} exceeds the ratchet baseline {} — coverage regressed",
        NOT_YET_COVERED.len(),
        MAX_UNCOVERED_EFFECTS
    );
    // Touch the forcing function so adding a variant breaks the build here.
    assert!(effect_executor_coverage(&Effect::RefreshDelegation));
}

// ============================================================================
// Authorization modes
// ============================================================================

/// Returns `true` iff this `Authorization` mode is exercised end-to-end by at
/// least one executor-invoking test. Exhaustive by design.
fn authorization_executor_coverage(a: &Authorization) -> bool {
    match a {
        // Covered.
        Authorization::Signature(..) => true, // every signed turn (composition, app tests)
        Authorization::Unchecked => true,     // bare_turn helpers across suites
        Authorization::Bearer(..) => true,    // bearer-cap exercise tests
        Authorization::CapTpDelivered { .. } => true, // wire captp_delivery_tests + #122
        // Not yet confirmed covered by an executor-invoking test (#142 work-list).
        Authorization::Proof { .. } => false,
        Authorization::Breadstuff(..) => false,
        Authorization::Custom { .. } => false,
        Authorization::OneOf { .. } => false,
    }
}

const NOT_YET_COVERED_AUTH: &[&str] = &["Proof", "Breadstuff", "Custom", "OneOf"];

/// Ratchet for Authorization-mode coverage — may only shrink.
const MAX_UNCOVERED_AUTH: usize = 4;

#[test]
fn authorization_coverage_ratchet_only_shrinks() {
    assert!(
        NOT_YET_COVERED_AUTH.len() <= MAX_UNCOVERED_AUTH,
        "not-yet-covered Authorization count {} exceeds baseline {} — coverage regressed",
        NOT_YET_COVERED_AUTH.len(),
        MAX_UNCOVERED_AUTH
    );
    assert!(authorization_executor_coverage(&Authorization::Unchecked));
}

// ============================================================================
// StateConstraint (cell-program caveats)
// ============================================================================

/// Returns `true` iff this `StateConstraint` is enforced THROUGH THE EXECUTOR
/// (a `submit_action`/`execute` test where the caveat actually gates a commit)
/// — not merely unit-tested via a direct `CellProgram::evaluate` call.
/// Exhaustive by design.
fn state_constraint_executor_coverage(c: &StateConstraint) -> bool {
    match c {
        // Confirmed enforced via the executor commit path (coverage_state_constraints.rs
        // accept+reject pairs, plus Monotonic/MonotonicSequence from the app suites).
        StateConstraint::Monotonic { .. } => true,
        StateConstraint::MonotonicSequence { .. } => true,
        StateConstraint::FieldEquals { .. } => true,
        StateConstraint::FieldGte { .. } => true,
        StateConstraint::FieldLte { .. } => true,
        StateConstraint::FieldLteField { .. } => true,
        StateConstraint::SumEquals { .. } => true,
        StateConstraint::SumEqualsAcross { .. } => true,
        StateConstraint::WriteOnce { .. } => true,
        StateConstraint::Immutable { .. } => true,
        StateConstraint::StrictMonotonic { .. } => true,
        StateConstraint::BoundedBy { .. } => true,
        StateConstraint::FieldDelta { .. } => true,
        StateConstraint::FieldDeltaInRange { .. } => true,
        StateConstraint::RateLimit { .. } => true,
        StateConstraint::RateLimitBySum { .. } => true,
        StateConstraint::TemporalGate { .. } => true,
        StateConstraint::PreimageGate { .. } => true,
        StateConstraint::AllowedTransitions { .. } => true,
        StateConstraint::AnyOf { .. } => true,

        // Not yet enforced/confirmed through the executor (#142 work-list):
        StateConstraint::FieldGteHeight { .. } => false, // not attempted (height-relative)
        StateConstraint::FieldLteHeight { .. } => false, // not attempted (height-relative)
        StateConstraint::SenderAuthorized { .. } => false, // needs witness registry verifier
        StateConstraint::CapabilityUniqueness { .. } => false, // evaluator is a no-op (#143)
        StateConstraint::TemporalPredicate { .. } => false, // needs witness registry
        StateConstraint::BoundDelta { .. } => false,        // cross-cell, not wired in embedded
        StateConstraint::Witnessed { .. } => false,         // needs witness registry
        StateConstraint::Renounced { .. } => false,         // needs witness registry
        StateConstraint::Custom { .. } => false,            // needs ir/descriptor verifier
    }
}

/// `StateConstraint` variants not yet executor-enforced (the #142 work-list).
const NOT_YET_COVERED_CONSTRAINTS: &[&str] = &[
    "FieldGteHeight",
    "FieldLteHeight",
    "SenderAuthorized",
    "CapabilityUniqueness",
    "TemporalPredicate",
    "BoundDelta",
    "Witnessed",
    "Renounced",
    "Custom",
];

/// Ratchet for StateConstraint executor-enforcement coverage — may only shrink.
const MAX_UNCOVERED_CONSTRAINTS: usize = 9;

#[test]
fn state_constraint_coverage_ratchet_only_shrinks() {
    assert!(
        NOT_YET_COVERED_CONSTRAINTS.len() <= MAX_UNCOVERED_CONSTRAINTS,
        "not-yet-covered StateConstraint count {} exceeds baseline {} — coverage regressed",
        NOT_YET_COVERED_CONSTRAINTS.len(),
        MAX_UNCOVERED_CONSTRAINTS
    );
    // Touch the classifier: a covered and an uncovered variant.
    assert!(state_constraint_executor_coverage(&StateConstraint::Monotonic { index: 0 }));
    assert!(!state_constraint_executor_coverage(&StateConstraint::FieldGteHeight {
        index: 0,
        offset: 0
    }));
}
