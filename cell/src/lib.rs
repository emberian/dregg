//! # pyana-cell
//!
//! The agent cell model: capability-secure isolated execution contexts.
//!
//! A Cell is the agent-model analog of a Mina zkApp account. It holds:
//! - Content-addressed identity (`CellId`)
//! - Mutable state with 8 generic field slots (`CellState`)
//! - Permission requirements for each action type (`Permissions`)
//! - A capability set (c-list) defining what the agent can reach (`CapabilitySet`)
//! - An optional verification key for ZK proof validation
//! - Token domain membership and delegation hierarchy

pub mod capability;
#[cfg(feature = "crypto")]
pub mod capability_proof;
pub mod cell;
pub mod commitment;
pub mod custom_effect;
pub mod delegation;
pub mod derivation;
pub mod facet;
pub mod factory;
pub mod id;
pub mod ledger;
pub mod note;
#[cfg(feature = "crypto")]
pub mod note_bridge;
pub mod nullifier_set;
#[cfg(feature = "crypto")]
pub mod oblivious_transfer;
#[cfg(feature = "crypto")]
pub mod peer_exchange;
pub mod permissions;
pub mod preconditions;
pub mod predicate;
pub mod program;
pub mod revocation_channel;
pub mod ring_closure;
/// γ.2 unilateral binding (1-arity sibling) — plain data type used by
/// `peer_exchange` to ship per-cell self-attestations. PI / accumulator
/// logic lives in `pyana_turn::bilateral_schedule`.
pub mod unilateral;
#[cfg(feature = "crypto")]
pub mod seal;
pub mod state;
#[cfg(feature = "crypto")]
pub mod stealth;
#[cfg(feature = "crypto")]
pub mod value_commitment;
pub mod vk_v2;

#[cfg(test)]
mod tests;

// Re-exports for convenience.
pub use capability::{
    AttenuatedCap, CapabilityCaveat, CapabilityRef, CapabilitySet, is_attenuation,
};
#[cfg(feature = "crypto")]
pub use capability_proof::{
    CapabilityExerciseRequest, CapabilityExerciseResponse, CapabilityProof, CapabilityProofData,
    CapabilityProofError, PeerEffect, VerificationContext, sign_capability_proof,
};
pub use cell::{Cell, CellConfig, CellMode, VerificationKey};
pub use commitment::{
    CANONICAL_CAP_ROOT_CONTEXT, CANONICAL_COMMITMENT_CONTEXT, canonical_to_babybear_pi,
    compute_canonical_capability_root, compute_canonical_state_commitment,
};
pub use custom_effect::{
    CustomEffectError, CustomEffectRegistry, CustomEffectVerifier, StubCustomEffectVerifier,
};
pub use delegation::DelegatedRef;
pub use derivation::{
    DerivationEdge, DerivationNode, DerivationRecord, DerivationTree, DerivationType,
};
pub use facet::{
    EFFECT_ALL, EFFECT_BRIDGE_OPS, EFFECT_CAPTP_OPS, EFFECT_CREATE_CELL, EFFECT_DELEGATION_OPS,
    EFFECT_EMIT_EVENT, EFFECT_ESCROW_OPS, EFFECT_GRANT_CAPABILITY, EFFECT_INCREMENT_NONCE,
    EFFECT_INTRODUCE, EFFECT_NOTE_CREATE, EFFECT_NOTE_SPEND, EFFECT_OBLIGATION_OPS,
    EFFECT_QUEUE_OPS, EFFECT_REFUSAL, EFFECT_REVOKE_CAPABILITY, EFFECT_SEAL_OPS, EFFECT_SET_FIELD,
    EFFECT_SET_PERMISSIONS, EFFECT_SET_VERIFICATION_KEY, EFFECT_SOVEREIGN_OPS, EFFECT_TRANSFER,
    EffectContext, EffectMask, ExtendedFacet, FACET_ADMIN, FACET_DELEGATOR, FACET_READ_ONLY,
    FACET_STATE_WRITER, FACET_TRANSFER_ONLY, FacetBuilder, FacetConstraint, FacetViolation,
    is_effect_permitted, is_facet_attenuation,
};
pub use factory::{
    CapGrant, CapTarget, CapTemplate, ChildVkStrategy, FactoryCreationParams, FactoryDescriptor,
    FactoryError, FactoryRegistry, FieldConstraint, Provenance, canonical_program_vk,
};
pub use id::CellId;
pub use ledger::{
    CellStateDelta, DEFAULT_SOVEREIGN_TTL, Ledger, LedgerDelta, LedgerError, MembershipProof, Side,
    SovereignHistory, SovereignRegistration, WitnessDiff,
};
pub use note::{Note, NoteBatcher, NoteCommitment, NoteError, Nullifier, PositionedNote};
#[cfg(feature = "crypto")]
pub use note_bridge::{
    BridgeDestination, BridgeError, BridgeReceipt, BridgeState, BridgedNullifierSet, PendingBridge,
    PendingBridgeSet, PortableNoteProof, cancel_bridge, create_portable_note, finalize_bridge,
    initiate_bridge, verify_bridge_receipt, verify_portable_note,
};
pub use nullifier_set::{MerkleMembershipProof, NonMembershipProof, NullifierSet};
#[cfg(feature = "crypto")]
pub use oblivious_transfer::{
    OtError, OtReceiver, OtReceiverResponse, OtSender, OtSenderPayload, OtSenderSetup, ot_1_of_n,
};
#[cfg(feature = "crypto")]
pub use peer_exchange::{PeerCellView, PeerExchange, PeerExchangeError, PeerStateTransition};
pub use permissions::{Action, AuthKind, AuthRequired, Permissions};
pub use unilateral::{UnilateralAttestation, UnilateralAttestationKind};
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
pub use program::{CellProgram, ProgramError, StateConstraint, field_from_u64, field_from_u64_be};
pub use revocation_channel::{
    ChannelId, RevocationChannel, RevocationChannelError, RevocationChannelSet,
};
pub use ring_closure::{
    ClosureProofKind, RingClosureAttestation, RingClosureError, RingLegPi,
    canonical_silver_commitment,
};
#[cfg(feature = "crypto")]
pub use seal::{SealError, SealPair, SealedBox, SealerPublic, test_seal_pair};
pub use state::{
    CellState, FIELD_ZERO, FieldElement, FieldVisibility, PublicFieldView, STATE_SLOTS,
};
#[cfg(feature = "crypto")]
pub use stealth::{StealthAddress, StealthAnnouncement, StealthKeys, StealthMetaAddress};
#[cfg(feature = "crypto")]
pub use value_commitment::{
    BulletproofRangeProof, CommittedNote, CommittedNoteOpening, ConservationError,
    ConservationProof, FullConservationError, FullConservationProof, ValueCommitment,
    ValueCommitmentBytes, prove_conservation, prove_conservation_with_range, verify_conservation,
    verify_conservation_with_range,
};
pub use vk_v2::{ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2};
