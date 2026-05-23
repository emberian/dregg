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
pub mod cell;
pub mod delegation;
pub mod derivation;
pub mod id;
pub mod ledger;
pub mod note;
#[cfg(feature = "crypto")]
pub mod note_bridge;
pub mod nullifier_set;
#[cfg(feature = "crypto")]
pub mod oblivious_transfer;
pub mod permissions;
pub mod preconditions;
pub mod program;
pub mod revocation_channel;
#[cfg(feature = "crypto")]
pub mod seal;
pub mod state;
#[cfg(feature = "crypto")]
pub mod stealth;
#[cfg(feature = "crypto")]
pub mod value_commitment;

#[cfg(test)]
mod tests;

// Re-exports for convenience.
pub use capability::{AttenuatedCap, CapabilityRef, CapabilitySet, is_attenuation};
pub use cell::{Cell, VerificationKey};
pub use delegation::DelegatedRef;
pub use derivation::{
    DerivationEdge, DerivationNode, DerivationRecord, DerivationTree, DerivationType,
};
pub use id::CellId;
pub use ledger::{CellStateDelta, Ledger, LedgerDelta, LedgerError, MembershipProof, Side};
pub use note::{Note, NoteCommitment, NoteError, Nullifier, PositionedNote};
#[cfg(feature = "crypto")]
pub use note_bridge::{
    BridgeError, BridgeReceipt, BridgeState, BridgedNullifierSet, PendingBridge, PendingBridgeSet,
    PortableNoteProof, cancel_bridge, create_portable_note, finalize_bridge, initiate_bridge,
    verify_bridge_receipt, verify_portable_note,
};
pub use nullifier_set::{MerkleMembershipProof, NonMembershipProof, NullifierSet};
#[cfg(feature = "crypto")]
pub use oblivious_transfer::{
    OtError, OtReceiver, OtReceiverResponse, OtSender, OtSenderPayload, OtSenderSetup, ot_1_of_n,
};
pub use permissions::{Action, AuthKind, AuthRequired, Permissions};
pub use preconditions::{
    CellStatePrecondition, EvalContext, NetworkPrecondition, Preconditions, TimeRange,
};
pub use program::{CellProgram, ProgramError, StateConstraint, field_from_u64, field_from_u64_be};
pub use revocation_channel::{
    ChannelId, RevocationChannel, RevocationChannelError, RevocationChannelSet,
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
    ValueCommitmentBytes, prove_conservation, prove_conservation_with_range,
    verify_conservation, verify_conservation_with_range,
};
