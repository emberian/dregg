//! Error types for turn execution failures.
//!
//! TurnError covers all the ways a turn can fail: authorization issues,
//! precondition violations, resource limits, and structural problems.

use pyana_cell::{AuthRequired, CellId, ChannelId};
use serde::{Deserialize, Serialize};

/// All possible failure modes when executing a turn.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TurnError {
    /// The source cell doesn't have enough computrons for a transfer.
    InsufficientBalance {
        cell: CellId,
        required: u64,
        available: u64,
    },

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
    DelegationDenied {
        parent: CellId,
        child_target: CellId,
    },

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

    /// CreateCell was called with a non-zero initial balance.
    CreateCellNonZeroBalance { cell: CellId, balance: u64 },

    /// The sum of all balance_change deltas in the turn is not zero.
    /// This violates the conservation law: withdrawals must be matched by deposits.
    ExcessNotZero { excess: i64 },

    /// A balance_change would underflow the target cell's balance (withdrawal exceeds holdings).
    BalanceChangeUnderflow {
        cell: CellId,
        current: u64,
        delta: i64,
    },

    /// The cell's program rejected the state transition.
    ProgramViolation { cell: CellId, reason: String },

    /// Note conservation law violated: for a given asset type, the total value
    /// of spent notes does not equal the total value of created notes.
    NoteConservationViolation {
        asset_type: u64,
        inputs: u64,
        outputs: u64,
    },
    /// Three-party introduction denied.
    IntroductionDenied {
        introducer: CellId,
        recipient: CellId,
        target: CellId,
        reason: String,
    },

    /// The silo's budget slice is exhausted (Stingray bounded counter).
    /// The turn was rejected before execution because the BudgetGate's
    /// local slice cannot cover the requested fee.
    BudgetExhausted {
        silo_id: u32,
        requested: u64,
        remaining: u64,
    },

    /// A conditional turn's condition was not satisfied by the presented proof.
    ConditionNotMet(String),

    /// The fee provided for a conditional turn is less than the required reservation deposit.
    /// Deposit = BASE_CONDITIONAL_DEPOSIT + PER_BLOCK_DEPOSIT * blocks_until_timeout.
    InsufficientConditionalDeposit { required: u64, provided: u64 },

    /// A BridgeMint effect failed verification (untrusted root, invalid proof,
    /// or double-bridge attempt).
    BridgeMintFailed { reason: String },

    /// A BridgeLock effect failed (note already locked, etc.).
    BridgeLockFailed { reason: String },

    /// A BridgeFinalize effect failed (invalid receipt, bridge not found, etc.).
    BridgeFinalizeFailed { reason: String },

    /// A BridgeCancel effect failed (timeout not reached, bridge not found, etc.).
    BridgeCancelFailed { reason: String },

    /// A delegated capability snapshot is stale (exceeded max_staleness).
    /// The delegation must be refreshed before it can be exercised.
    StaleDelegation {
        actor: CellId,
        source: CellId,
        refreshed_at: u64,
        max_staleness: u64,
        now: u64,
    },

    /// A delegated capability has been revoked via its revocation channel.
    /// The channel was tripped, meaning the capability is no longer valid.
    CapabilityRevoked {
        actor: CellId,
        channel_id: ChannelId,
        tripped_at: u64,
    },

    /// The capability slot counter overflowed (2^32 grants exhausted).
    CapabilitySlotOverflow { cell: CellId },

    /// An effect was structurally invalid (malformed data, null identifiers, etc.).
    InvalidEffect { reason: String },

    /// Committed (Pedersen) conservation check failed: the Schnorr proof over the
    /// excess commitment is invalid, indicating value is not conserved.
    CommittedConservationFailed { reason: String },

    /// A turn targets a sovereign cell but no witness was provided.
    SovereignWitnessRequired { cell: CellId },

    /// The sovereign cell witness commitment does not match the stored commitment.
    SovereignCommitmentMismatch {
        cell: CellId,
        expected: [u8; 32],
        got: [u8; 32],
    },
}

impl core::fmt::Display for TurnError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TurnError::InsufficientBalance {
                cell,
                required,
                available,
            } => {
                write!(
                    f,
                    "insufficient balance on cell {cell}: need {required}, have {available}"
                )
            }
            TurnError::PermissionDenied {
                cell,
                action,
                required,
            } => {
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
            TurnError::DelegationDenied {
                parent,
                child_target,
            } => {
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
            TurnError::CreateCellNonZeroBalance { cell, balance } => {
                write!(
                    f,
                    "CreateCell requires zero initial balance, got {balance} for cell {cell}"
                )
            }
            TurnError::ExcessNotZero { excess } => {
                write!(
                    f,
                    "excess not zero at turn end: {excess} (conservation law violated)"
                )
            }
            TurnError::BalanceChangeUnderflow {
                cell,
                current,
                delta,
            } => {
                write!(
                    f,
                    "balance_change underflow on cell {cell}: balance={current}, delta={delta}"
                )
            }
            TurnError::ProgramViolation { cell, reason } => {
                write!(f, "program violation on cell {cell}: {reason}")
            }
            TurnError::NoteConservationViolation {
                asset_type,
                inputs,
                outputs,
            } => {
                write!(
                    f,
                    "note conservation violated for asset {asset_type}: inputs={inputs}, outputs={outputs}"
                )
            }
            TurnError::IntroductionDenied {
                introducer,
                recipient,
                target,
                reason,
            } => {
                write!(
                    f,
                    "introduction denied: {introducer} cannot introduce {recipient} to {target}: {reason}"
                )
            }
            TurnError::BudgetExhausted {
                silo_id,
                requested,
                remaining,
            } => {
                write!(
                    f,
                    "budget exhausted on silo {silo_id}: requested {requested}, remaining {remaining}"
                )
            }
            TurnError::ConditionNotMet(reason) => {
                write!(f, "conditional turn condition not met: {reason}")
            }
            TurnError::InsufficientConditionalDeposit { required, provided } => {
                write!(
                    f,
                    "insufficient conditional deposit: required {required}, provided {provided}"
                )
            }
            TurnError::BridgeMintFailed { reason } => {
                write!(f, "bridge mint failed: {reason}")
            }
            TurnError::BridgeLockFailed { reason } => {
                write!(f, "bridge lock failed: {reason}")
            }
            TurnError::BridgeFinalizeFailed { reason } => {
                write!(f, "bridge finalize failed: {reason}")
            }
            TurnError::BridgeCancelFailed { reason } => {
                write!(f, "bridge cancel failed: {reason}")
            }
            TurnError::StaleDelegation {
                actor,
                source,
                refreshed_at,
                max_staleness,
                now,
            } => {
                write!(
                    f,
                    "stale delegation: actor {actor}'s delegation from {source} expired \
                     (refreshed_at={refreshed_at}, max_staleness={max_staleness}, now={now})"
                )
            }
            TurnError::CapabilityRevoked {
                actor,
                channel_id,
                tripped_at,
            } => {
                write!(
                    f,
                    "capability revoked: actor {actor}'s delegation revoked via channel \
                     {:02x}{:02x}... (tripped_at={tripped_at})",
                    channel_id[0], channel_id[1]
                )
            }
            TurnError::CapabilitySlotOverflow { cell } => {
                write!(
                    f,
                    "capability slot counter overflow on cell {cell} (2^32 grants exhausted)"
                )
            }
            TurnError::InvalidEffect { reason } => {
                write!(f, "invalid effect: {reason}")
            }
            TurnError::CommittedConservationFailed { reason } => {
                write!(f, "committed conservation failed: {reason}")
            }
            TurnError::SovereignWitnessRequired { cell } => {
                write!(
                    f,
                    "sovereign cell {cell} targeted but no witness provided in turn"
                )
            }
            TurnError::SovereignCommitmentMismatch {
                cell,
                expected,
                got,
            } => {
                write!(
                    f,
                    "sovereign commitment mismatch for cell {cell}: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    expected[0], expected[1], got[0], got[1]
                )
            }
        }
    }
}

impl std::error::Error for TurnError {}
