//! # dregg-cell
//!
//! ## ⚠️ LEGACY dregg1 — pending the verified-Lean SWAP
//!
//! **This crate is the LEGACY dregg1 Rust cell-state model. It is NOT the
//! source of truth.** The verified cell / program / predicate / caveat
//! semantics live in Lean under `metatheory/Dregg2/` (`Exec/Cell.lean`,
//! `Exec/CellProgram.lean`, `Authority/Caveat.lean`, `Exec/RecordCell.lean`).
//! The Rust types here (`CellProgram`, `Permissions`, `Predicate`,
//! capability/delegation, `Nullifier`/`NoteCommitment`) are hand-written,
//! UNVERIFIED duplicates that dregg2 *replaces*. They remain because
//! `dregg-turn` (the running executor) depends on them until THE SWAP. Treat
//! the Lean as the spec; this Rust as the legacy subject-under-test. The exact
//! Rust↔Lean duplication map is in
//! `metatheory/docs/rebuild/_DREGG1-DREGG2-UNIFICATION-LEDGER.md`.
//!
//! The agent cell model: capability-secure isolated execution contexts.
//!
//! A Cell is the agent-model analog of a Mina zkApp account. It holds:
//! - Content-addressed identity (`CellId`)
//! - Mutable state with 16 generic field slots (`CellState`)
//! - Permission requirements for each action type (`Permissions`)
//! - A capability set (c-list) defining what the agent can reach (`CapabilitySet`)
//! - An optional verification key for ZK proof validation
//! - Token domain membership and delegation hierarchy

pub mod allowance;
pub mod blueprint;
pub mod capability;
pub mod cell;
pub mod commitment;
pub mod custom_effect;
pub mod delegation;
pub mod derivation;
pub mod derived;
pub mod escrow_sealed;
pub mod facet;
pub mod factory;
pub mod id;
/// First-class typed cell interfaces (CELLS-AS-SERVICE-OBJECTS): a
/// content-addressed [`interface::InterfaceDescriptor`] auto-derived from a
/// cell's method-dispatch program. A standalone, NON-committed type — the
/// service-object / `invoke()` layer lives ABOVE the effectvm/commitment, so the
/// descriptor is not folded into the cell commitment.
pub mod interface;
pub mod ledger;
pub mod lifecycle;
pub mod membrane;
pub mod migration;
pub mod note;
pub mod nullifier_set;
pub mod obligation_standing;
pub mod permissions;
pub mod preconditions;
pub mod predicate;
pub mod prepaid_lease;
pub mod program;
pub mod revocation_channel;
pub mod ring_closure;
pub mod state;
/// γ.2 unilateral binding (1-arity sibling) — plain data type used by
/// `peer_exchange` to ship per-cell self-attestations. PI / accumulator
/// logic lives in `dregg_turn::bilateral_schedule`.
pub mod unilateral;
pub mod vault;
pub mod vk_v2;

#[cfg(test)]
mod tests;

// Re-exports for convenience.
pub use allowance::{
    AllowanceError, AllowanceState, AllowanceTerms, Spend as AllowanceSpend, SpendOutcome,
    is_allowance, open_allowance, remaining_at as allowance_remaining_at, spend as spend_allowance,
};
pub use blueprint::{
    AllowanceTerms as AllowanceFactoryTerms, BlueprintError, BridgeTerms, EscrowTerms,
    ObligationTerms, StandingObligationTerms as StandingObligationFactoryTerms,
    VaultCondition as VaultFactoryCondition, VaultTerms as VaultFactoryTerms,
    allowance_cell_program, allowance_factory_descriptor, allowance_state_constraints,
    bridge_cell_program, bridge_factory_descriptor, escrow_cell_program, escrow_factory_descriptor,
    obligation_cell_program, obligation_factory_descriptor, standing_obligation_cell_program,
    standing_obligation_factory_descriptor, standing_obligation_state_constraints,
    vault_cell_program, vault_factory_descriptor, vault_state_constraints,
};
pub use capability::{
    AttenuatedCap, CapabilityCaveat, CapabilityRef, CapabilitySet, is_attenuation,
};
pub use cell::{Cell, CellConfig, CellMode, VerificationKey, VerificationKeyIntegrityError};
pub use commitment::{
    CANONICAL_CAP_ROOT_CONTEXT, CANONICAL_COMMITMENT_CONTEXT, authority_residue_bytes,
    canonical_to_babybear_pi, cap_ref_to_leaf, capability_ref_leaf_commitment,
    compute_authority_digest_8, compute_authority_digest_felt, compute_canonical_capability_root,
    compute_canonical_capability_root_8, compute_canonical_capability_root_felt,
    compute_canonical_state_commitment, digest8_to_bytes32, felt_to_bytes32,
};
pub use custom_effect::{
    CustomEffectError, CustomEffectRegistry, CustomEffectVerifier, StubCustomEffectVerifier,
};
pub use delegation::DelegatedRef;
pub use derivation::{
    DerivationEdge, DerivationNode, DerivationRecord, DerivationTree, DerivationType,
};
pub use derived::{
    Aggregate, DerivationError, DerivationSpec, bind_derivation, bound_claimed_value,
    bound_spec_digest, is_derived, verify_derivation,
};
pub use escrow_sealed::{
    Claim, EscrowError, EscrowState, EscrowTerms as SealedEscrowTerms, Leg, LegRequirement,
    LegStatus, Side as EscrowSide, deposit_leg, is_escrow, open_escrow, reclaim_leg, settle,
};
pub use facet::{
    EFFECT_ALL, EFFECT_ATTENUATE_CAPABILITY, EFFECT_BRIDGE_OPS, EFFECT_BURN, EFFECT_CAPTP_OPS,
    EFFECT_CREATE_CELL, EFFECT_DELEGATION_OPS, EFFECT_EMIT_EVENT, EFFECT_ESCROW_OPS,
    EFFECT_GRANT_CAPABILITY, EFFECT_INCREMENT_NONCE, EFFECT_INTRODUCE, EFFECT_LIFECYCLE_OPS,
    EFFECT_MINT, EFFECT_NOTE_CREATE, EFFECT_NOTE_SPEND, EFFECT_OBLIGATION_OPS, EFFECT_QUEUE_OPS,
    EFFECT_REACTIVE_OPS, EFFECT_REFUSAL, EFFECT_REVOKE_CAPABILITY, EFFECT_SEAL_OPS,
    EFFECT_SET_FIELD, EFFECT_SET_PERMISSIONS, EFFECT_SET_PROGRAM, EFFECT_SET_VERIFICATION_KEY,
    EFFECT_SOVEREIGN_OPS, EFFECT_TRANSFER, EffectContext, EffectMask, ExtendedFacet, FACET_ADMIN,
    FACET_DELEGATOR, FACET_READ_ONLY, FACET_STATE_WRITER, FACET_TRANSFER_ONLY, FacetBuilder,
    FacetConstraint, FacetViolation, is_effect_permitted, is_facet_attenuation,
};
pub use factory::{
    CapGrant, CapTarget, CapTemplate, ChildVkStrategy, FactoryCreationParams, FactoryDescriptor,
    FactoryError, FactoryRegistry, FieldConstraint, Provenance, canonical_program_vk,
};
pub use id::CellId;
pub use interface::{
    ArgsSchema, InterfaceDescriptor, InterfaceRef, MethodSig, Semantics, method_symbol,
};
pub use ledger::{
    CellStateDelta, DEFAULT_SOVEREIGN_TTL, Ledger, LedgerDelta, LedgerError, MembershipProof, Side,
    SovereignHistory, SovereignRegistration, WitnessDiff,
};
pub use lifecycle::{
    ArchivalAttestation, CellLifecycle, DeathCertificate, DeathReason, LifecycleTransitionError,
};
pub use membrane::{
    CompositionPolicy, HeldFacet, Membrane, MembraneCap, MembraneError, Presentation,
    SealedMembrane, compose_both,
};
pub use note::{Note, NoteBatcher, NoteCommitment, NoteError, Nullifier, PositionedNote};
pub use nullifier_set::{MerkleMembershipProof, NonMembershipProof, NullifierSet};
pub use obligation_standing::{
    Discharge, ObligationError as StandingObligationError,
    ObligationState as StandingObligationState, ObligationTerms as StandingObligationTerms,
    discharge, is_obligation, open_obligation,
};
pub use permissions::{Action, AuthKind, AuthRequired, Permissions};
#[allow(deprecated)]
pub use preconditions::PreconditionClause;
pub use preconditions::{
    CellStatePrecondition, EvalContext, NetworkPrecondition, Precondition, Preconditions,
    PreconditionsBuilder, TimeRange,
};
pub use predicate::{
    InputRef, NonMembershipNeighborProof, PredicateInput, WitnessProducer, WitnessProducerError,
    WitnessProducerRegistry, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier, canonical_predicate_vk,
};
pub use program::{
    CellProgram, HeapAtom, ProgramError, StateConstraint, count_ge_set_commitment, field_from_u64,
    field_from_u64_be,
};
pub use revocation_channel::{
    ChannelId, RevocationChannel, RevocationChannelError, RevocationChannelSet,
};
pub use ring_closure::{
    ClosureProofKind, RingClosureAttestation, RingClosureError, RingLegPi,
    canonical_silver_commitment,
};
pub use state::{
    CellState, FIELD_ZERO, FIELDS_ROOT_CONTEXT, FieldElement, FieldVisibility, PublicFieldView,
    STATE_SLOTS, compute_fields_root, compute_heap_root, empty_fields_root, empty_heap_root,
};
pub use unilateral::{UnilateralAttestation, UnilateralAttestationKind};
pub use vault::{
    Claim as VaultClaim, ClaimOutcome as VaultClaimOutcome, Condition as VaultCondition,
    VaultError, VaultState, VaultTerms, claim as claim_vault,
    is_claimable_at as vault_claimable_at, is_vault, open_vault,
};
pub use vk_v2::{ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2};
