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
pub mod id;
pub mod ledger;
pub mod permissions;
pub mod preconditions;
pub mod program;
pub mod state;

#[cfg(test)]
mod tests;

// Re-exports for convenience.
pub use capability::{CapabilityRef, CapabilitySet, is_attenuation};
pub use cell::{Cell, VerificationKey};
pub use id::CellId;
pub use ledger::{CellStateDelta, Ledger, LedgerDelta, LedgerError, MembershipProof, Side};
pub use permissions::{Action, AuthKind, AuthRequired, Permissions};
pub use preconditions::{
    CellStatePrecondition, EvalContext, NetworkPrecondition, Preconditions, TimeRange,
};
pub use program::{CellProgram, ProgramError, StateConstraint};
pub use state::{CellState, FieldElement, FieldVisibility, FIELD_ZERO, PublicFieldView, STATE_SLOTS};
