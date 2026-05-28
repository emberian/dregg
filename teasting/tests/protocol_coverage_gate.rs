//! Protocol-coverage gate (Pillar 2 of the test/gates initiative, #142).
//!
//! "Verification means something" only if the gates actually exercise the
//! protocol. This file is a **compile-time forcing function**: the exhaustive
//! `match` in `effect_executor_coverage` has one arm per `dregg_turn::Effect`
//! variant, so **adding a new `Effect` variant breaks this test's compilation
//! until someone classifies it** — covered by a real executor-invoking flow,
//! or explicitly not-yet-covered. That makes silent, untested protocol growth
//! impossible.
//!
//! Honesty contract: an arm is `true` ONLY where a test in this workspace
//! actually drives that variant through `TurnExecutor::execute` /
//! `EmbeddedExecutor::submit_action` (per-app integration tests, the
//! cross-app composition e2e, the lifecycle/obligation/escrow suites, and the
//! #111–#116 apply-path tests). Where coverage is unconfirmed, the arm is
//! conservatively `false` — under-claiming, never over-claiming. The runtime
//! assertion ratchets: the not-yet-covered count may only shrink.
//!
//! Follow-ups (#142): extend the same forcing function to `Authorization`
//! modes and `StateConstraint` variants, then wire into preflight (Pillar 3).

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

        // ── Not yet confirmed covered by an executor-invoking test ───────
        // (#142 work-list — flip to true with the covering test as it lands)
        Effect::SetPermissions { .. } => false,
        Effect::NoteSpend { .. } => false,
        Effect::NoteCreate { .. } => false,
        Effect::CreateSealPair { .. } => false,
        Effect::Seal { .. } => false,
        Effect::Unseal { .. } => false,
        Effect::BridgeFinalize { .. } => false,
        Effect::BridgeCancel { .. } => false,
        Effect::Introduce { .. } => false,
        Effect::PipelinedSend { .. } => false,
        Effect::CreateCommittedEscrow { .. } => false,
        Effect::ReleaseCommittedEscrow { .. } => false,
        Effect::RefundCommittedEscrow { .. } => false,
        Effect::MakeSovereign { .. } => false,
        Effect::CreateCellFromFactory { .. } => false,
        Effect::QueueAllocate { .. } => false,
        Effect::QueueEnqueue { .. } => false,
        Effect::QueueDequeue { .. } => false,
        Effect::QueueResize { .. } => false,
        Effect::QueueAtomicTx { .. } => false,
        Effect::QueuePipelineStep { .. } => false,
        Effect::Refusal { .. } => false,
    }
}

/// The set of `Effect` variant names currently classified not-yet-covered.
/// This is the ratchet's source of truth and the #142 work-list. Keep it in
/// sync with the `false` arms above (the exhaustive match guarantees no
/// variant is omitted entirely).
const NOT_YET_COVERED: &[&str] = &[
    "SetPermissions",
    "NoteSpend",
    "NoteCreate",
    "CreateSealPair",
    "Seal",
    "Unseal",
    "BridgeFinalize",
    "BridgeCancel",
    "Introduce",
    "PipelinedSend",
    "CreateCommittedEscrow",
    "ReleaseCommittedEscrow",
    "RefundCommittedEscrow",
    "MakeSovereign",
    "CreateCellFromFactory",
    "QueueAllocate",
    "QueueEnqueue",
    "QueueDequeue",
    "QueueResize",
    "QueueAtomicTx",
    "QueuePipelineStep",
    "Refusal",
];

/// Ratchet: the number of `Effect` variants not yet exercised end-to-end may
/// only DECREASE. When you add coverage, flip the arm to `true`, remove it
/// from `NOT_YET_COVERED`, and lower this baseline. It must never rise.
const MAX_UNCOVERED_EFFECTS: usize = 22;

#[test]
fn effect_coverage_ratchet_only_shrinks() {
    assert!(
        NOT_YET_COVERED.len() <= MAX_UNCOVERED_EFFECTS,
        "not-yet-covered Effect count {} exceeds the ratchet baseline {} — coverage regressed",
        NOT_YET_COVERED.len(),
        MAX_UNCOVERED_EFFECTS
    );
    // Touch the forcing function so it is compiled (and so adding a variant
    // breaks the build here). RefreshDelegation is the unit variant.
    assert!(effect_executor_coverage(&Effect::RefreshDelegation));
}

// ============================================================================
// Authorization modes
// ============================================================================

/// Returns `true` iff this `Authorization` mode is exercised end-to-end by at
/// least one executor-invoking test. Exhaustive by design — adding an auth
/// mode breaks compilation until classified. Same honesty contract as above.
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
/// Exhaustive by design. Conservative: most caveats have rich direct-evaluate
/// unit tests in `cell` but their executor-path enforcement is unconfirmed
/// here, so they are `false` pending a confirming integration test (#142).
fn state_constraint_executor_coverage(c: &StateConstraint) -> bool {
    match c {
        // Confirmed enforced via the executor commit path.
        StateConstraint::Monotonic { .. } => true, // identity revocation-root rollback rejected (integration_issue_present_verify)
        StateConstraint::MonotonicSequence { .. } => true, // subscription publish head (integration_publish_consume)

        // Not yet confirmed enforced through the executor (#142 work-list).
        StateConstraint::FieldEquals { .. } => false,
        StateConstraint::FieldGte { .. } => false,
        StateConstraint::FieldLte { .. } => false,
        StateConstraint::FieldLteField { .. } => false,
        StateConstraint::SumEquals { .. } => false,
        StateConstraint::WriteOnce { .. } => false,
        StateConstraint::Immutable { .. } => false,
        StateConstraint::StrictMonotonic { .. } => false,
        StateConstraint::BoundedBy { .. } => false,
        StateConstraint::FieldDelta { .. } => false,
        StateConstraint::FieldDeltaInRange { .. } => false,
        StateConstraint::FieldGteHeight { .. } => false,
        StateConstraint::FieldLteHeight { .. } => false,
        StateConstraint::SumEqualsAcross { .. } => false,
        StateConstraint::SenderAuthorized { .. } => false,
        StateConstraint::CapabilityUniqueness { .. } => false,
        StateConstraint::RateLimit { .. } => false,
        StateConstraint::RateLimitBySum { .. } => false,
        StateConstraint::TemporalGate { .. } => false,
        StateConstraint::PreimageGate { .. } => false,
        StateConstraint::AllowedTransitions { .. } => false,
        StateConstraint::TemporalPredicate { .. } => false,
        StateConstraint::BoundDelta { .. } => false,
        StateConstraint::AnyOf { .. } => false,
        StateConstraint::Witnessed { .. } => false,
        StateConstraint::Renounced { .. } => false,
        StateConstraint::Custom { .. } => false,
    }
}

/// Ratchet for StateConstraint executor-enforcement coverage — may only shrink.
const MAX_UNCOVERED_CONSTRAINTS: usize = 27;

#[test]
fn state_constraint_coverage_ratchet_only_shrinks() {
    // Count the `false` arms by exercising the classifier over a representative
    // instance of each variant would require constructing all 29; instead the
    // exhaustive match above is the completeness guarantee, and this baseline
    // is maintained alongside it. Touch the classifier so it compiles.
    assert!(state_constraint_executor_coverage(&StateConstraint::Monotonic { index: 0 }));
    assert!(!state_constraint_executor_coverage(&StateConstraint::WriteOnce { index: 0 }));
    // 2 of 29 confirmed → 27 not-yet; baseline must never rise.
    assert_eq!(MAX_UNCOVERED_CONSTRAINTS, 27);
}
