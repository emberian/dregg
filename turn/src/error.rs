//! Error types for turn execution failures.
//!
//! TurnError covers all the ways a turn can fail: authorization issues,
//! precondition violations, resource limits, and structural problems.

use pyana_cell::{AuthRequired, CellId};
use serde::{Deserialize, Serialize};

/// All possible failure modes when executing a turn.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TurnError {
    /// The source cell doesn't have enough computrons for a transfer.
    InsufficientBalance { cell: CellId, required: u64, available: u64 },

    /// The provided authorization doesn't satisfy the cell's permission requirements.
    PermissionDenied {
        cell: CellId,
        action: String,
        required: AuthRequired,
    },

    /// A precondition check failed.
    PreconditionFailed { description: String },

    /// The authorization was structurally invalid (e.g., bad signature format).
    InvalidAuthorization { reason: String },

    /// The target cell doesn't exist in the ledger.
    CellNotFound { id: CellId },

    /// An action tried to act on a cell it has no capability to reach.
    CapabilityNotHeld { actor: CellId, target: CellId },

    /// The turn's nonce doesn't match the expected nonce for the agent cell.
    NonceReplay { expected: u64, got: u64 },

    /// The turn's valid_until timestamp has passed.
    Expired { valid_until: i64, now: i64 },

    /// The turn exceeded its computron budget.
    BudgetExceeded { limit: u64, used: u64 },

    /// A child action tried to use delegation but the parent disallowed it.
    DelegationDenied { parent: CellId, child_target: CellId },

    /// State field index out of bounds.
    InvalidFieldIndex { cell: CellId, index: usize },

    /// A cell that was supposed to be created already exists.
    CellAlreadyExists { id: CellId },

    /// The call forest is empty (no actions to execute).
    EmptyForest,

    /// Transfer destination cell not found.
    TransferDestNotFound { id: CellId },

    /// Balance overflow on receiving cell.
    BalanceOverflow { cell: CellId },

    /// The sum of all balance_change deltas in the turn is not zero.
    /// This violates the conservation law: withdrawals must be matched by deposits.
    ExcessNotZero { excess: i64 },

    /// A balance_change would underflow the target cell's balance (withdrawal exceeds holdings).
    BalanceChangeUnderflow { cell: CellId, current: u64, delta: i64 },

    /// The cell's program rejected the state transition.
    ProgramViolation { cell: CellId, reason: String },

    /// Note conservation law violated: for a given asset type, the total value
    /// of spent notes does not equal the total value of created notes.
    NoteConservationViolation { asset_type: u64, inputs: u64, outputs: u64 },
    /// Three-party introduction denied.
    IntroductionDenied { introducer: CellId, recipient: CellId, target: CellId, reason: String },
}

impl core::fmt::Display for TurnError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TurnError::InsufficientBalance { cell, required, available } => {
                write!(
                    f,
                    "insufficient balance on cell {cell}: need {required}, have {available}"
                )
            }
            TurnError::PermissionDenied { cell, action, required } => {
                write!(
                    f,
                    "permission denied on cell {cell} for action '{action}': requires {required:?}"
                )
            }
            TurnError::PreconditionFailed { description } => {
                write!(f, "precondition failed: {description}")
            }
            TurnError::InvalidAuthorization { reason } => {
                write!(f, "invalid authorization: {reason}")
            }
            TurnError::CellNotFound { id } => {
                write!(f, "cell not found: {id}")
            }
            TurnError::CapabilityNotHeld { actor, target } => {
                write!(f, "cell {actor} has no capability to reach cell {target}")
            }
            TurnError::NonceReplay { expected, got } => {
                write!(f, "nonce replay: expected {expected}, got {got}")
            }
            TurnError::Expired { valid_until, now } => {
                write!(f, "turn expired: valid_until={valid_until}, now={now}")
            }
            TurnError::BudgetExceeded { limit, used } => {
                write!(f, "computron budget exceeded: limit={limit}, used={used}")
            }
            TurnError::DelegationDenied { parent, child_target } => {
                write!(
                    f,
                    "delegation denied: parent {parent} does not delegate to child targeting {child_target}"
                )
            }
            TurnError::InvalidFieldIndex { cell, index } => {
                write!(f, "invalid field index {index} for cell {cell}")
            }
            TurnError::CellAlreadyExists { id } => {
                write!(f, "cell already exists: {id}")
            }
            TurnError::EmptyForest => {
                write!(f, "call forest is empty")
            }
            TurnError::TransferDestNotFound { id } => {
                write!(f, "transfer destination not found: {id}")
            }
            TurnError::BalanceOverflow { cell } => {
                write!(f, "balance overflow on cell {cell}")
            }
            TurnError::ExcessNotZero { excess } => {
                write!(
                    f,
                    "excess not zero at turn end: {excess} (conservation law violated)"
                )
            }
            TurnError::BalanceChangeUnderflow { cell, current, delta } => {
                write!(
                    f,
                    "balance_change underflow on cell {cell}: balance={current}, delta={delta}"
                )
            }
            TurnError::ProgramViolation { cell, reason } => {
                write!(f, "program violation on cell {cell}: {reason}")
            }
            TurnError::NoteConservationViolation { asset_type, inputs, outputs } => {
                write!(
                    f,
                    "note conservation violated for asset {asset_type}: inputs={inputs}, outputs={outputs}"
                )
            }
            TurnError::IntroductionDenied { introducer, recipient, target, reason } => {
                write!(f, "introduction denied: {introducer} cannot introduce {recipient} to {target}: {reason}")
            }
        }
    }
}

impl std::error::Error for TurnError {}
