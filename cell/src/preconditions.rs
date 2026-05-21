use serde::{Deserialize, Serialize};

use crate::state::{CellState, FieldElement};

/// Preconditions that must hold for an action to be valid.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Preconditions {
    /// Assertions about the cell's current state.
    pub cell_state: Option<CellStatePrecondition>,
    /// Assertions about the network state.
    pub network: Option<NetworkPrecondition>,
    /// Time range during which this action is valid.
    pub valid_while: Option<TimeRange>,
}

/// Assertions about a cell's state that must be true.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellStatePrecondition {
    /// The exact nonce that must be current.
    pub nonce: Option<u64>,
    /// Minimum computron balance required.
    pub min_balance: Option<u64>,
    /// Fields that must equal specific values: (slot_index, expected_value).
    pub field_equals: Vec<(usize, FieldElement)>,
    /// Assert that the cell's proved_state flag equals this value.
    pub proved_state: Option<bool>,
}

/// Assertions about the network/ledger state.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct NetworkPrecondition {
    /// Minimum block height.
    pub min_height: Option<u64>,
    /// Maximum block height.
    pub max_height: Option<u64>,
}

/// A time range (inclusive on both ends).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TimeRange {
    /// Start of the valid time window (unix timestamp, seconds).
    pub start: i64,
    /// End of the valid time window (unix timestamp, seconds).
    pub end: i64,
}

impl TimeRange {
    /// Create a new time range.
    pub fn new(start: i64, end: i64) -> Self {
        TimeRange { start, end }
    }

    /// Check if a given timestamp falls within this range.
    pub fn contains(&self, timestamp: i64) -> bool {
        timestamp >= self.start && timestamp <= self.end
    }
}

/// Context for evaluating network/time preconditions.
#[derive(Clone, Debug)]
pub struct EvalContext {
    /// Current block height.
    pub block_height: u64,
    /// Current timestamp (unix seconds).
    pub timestamp: i64,
}

impl Preconditions {
    /// Compute a deterministic hash of these preconditions for inclusion in signing messages.
    ///
    /// Uses BLAKE3 over a canonical byte representation. Empty (default) preconditions
    /// hash to all-zeros for efficiency (no hashing needed for the common case).
    pub fn hash(&self) -> [u8; 32] {
        // Fast path: default (empty) preconditions are represented as zero hash.
        if self.cell_state.is_none() && self.network.is_none() && self.valid_while.is_none() {
            return [0u8; 32];
        }
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"preconditions-v1");
        // Cell state precondition
        if let Some(ref cs) = self.cell_state {
            hasher.update(b"\x01");
            if let Some(nonce) = cs.nonce {
                hasher.update(b"\x01");
                hasher.update(&nonce.to_le_bytes());
            } else {
                hasher.update(b"\x00");
            }
            if let Some(min_bal) = cs.min_balance {
                hasher.update(b"\x01");
                hasher.update(&min_bal.to_le_bytes());
            } else {
                hasher.update(b"\x00");
            }
            hasher.update(&(cs.field_equals.len() as u64).to_le_bytes());
            for &(index, ref value) in &cs.field_equals {
                hasher.update(&(index as u64).to_le_bytes());
                hasher.update(value);
            }
            if let Some(proved) = cs.proved_state {
                hasher.update(if proved { b"\x01" } else { b"\x00" });
            }
        } else {
            hasher.update(b"\x00");
        }
        // Network precondition
        if let Some(ref net) = self.network {
            hasher.update(b"\x01");
            hasher.update(&net.min_height.unwrap_or(0).to_le_bytes());
            hasher.update(&net.max_height.unwrap_or(u64::MAX).to_le_bytes());
        } else {
            hasher.update(b"\x00");
        }
        // Time range
        if let Some(ref tr) = self.valid_while {
            hasher.update(b"\x01");
            hasher.update(&tr.start.to_le_bytes());
            hasher.update(&tr.end.to_le_bytes());
        } else {
            hasher.update(b"\x00");
        }
        *hasher.finalize().as_bytes()
    }

    /// Evaluate all preconditions against the given cell state and context.
    /// Returns Ok(()) if all preconditions pass, or Err with a description of the failure.
    pub fn evaluate(&self, state: &CellState, ctx: &EvalContext) -> Result<(), PreconditionError> {
        if let Some(ref cell_pre) = self.cell_state {
            cell_pre.evaluate(state)?;
        }
        if let Some(ref net_pre) = self.network {
            net_pre.evaluate(ctx)?;
        }
        if let Some(ref time_range) = self.valid_while
            && !time_range.contains(ctx.timestamp)
        {
            return Err(PreconditionError::TimeOutOfRange {
                timestamp: ctx.timestamp,
                start: time_range.start,
                end: time_range.end,
            });
        }
        Ok(())
    }
}

impl CellStatePrecondition {
    /// Evaluate the cell state precondition.
    pub fn evaluate(&self, state: &CellState) -> Result<(), PreconditionError> {
        if let Some(expected_nonce) = self.nonce
            && state.nonce != expected_nonce
        {
            return Err(PreconditionError::NonceMismatch {
                expected: expected_nonce,
                actual: state.nonce,
            });
        }
        if let Some(min_bal) = self.min_balance
            && state.balance < min_bal
        {
            return Err(PreconditionError::InsufficientBalance {
                required: min_bal,
                actual: state.balance,
            });
        }
        for &(index, ref expected_value) in &self.field_equals {
            match state.get_field(index) {
                Some(actual) if actual == expected_value => {}
                Some(actual) => {
                    return Err(PreconditionError::FieldMismatch {
                        index,
                        expected: *expected_value,
                        actual: *actual,
                    });
                }
                None => {
                    return Err(PreconditionError::InvalidFieldIndex { index });
                }
            }
        }
        if let Some(expected_proved) = self.proved_state
            && state.proved_state != expected_proved
        {
            return Err(PreconditionError::ProvedStateMismatch {
                expected: expected_proved,
                actual: state.proved_state,
            });
        }
        Ok(())
    }
}

impl NetworkPrecondition {
    /// Evaluate the network precondition.
    pub fn evaluate(&self, ctx: &EvalContext) -> Result<(), PreconditionError> {
        if let Some(min_h) = self.min_height
            && ctx.block_height < min_h
        {
            return Err(PreconditionError::HeightTooLow {
                required: min_h,
                actual: ctx.block_height,
            });
        }
        if let Some(max_h) = self.max_height
            && ctx.block_height > max_h
        {
            return Err(PreconditionError::HeightTooHigh {
                max: max_h,
                actual: ctx.block_height,
            });
        }
        Ok(())
    }
}

/// Errors from precondition evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PreconditionError {
    NonceMismatch {
        expected: u64,
        actual: u64,
    },
    InsufficientBalance {
        required: u64,
        actual: u64,
    },
    FieldMismatch {
        index: usize,
        expected: FieldElement,
        actual: FieldElement,
    },
    InvalidFieldIndex {
        index: usize,
    },
    HeightTooLow {
        required: u64,
        actual: u64,
    },
    HeightTooHigh {
        max: u64,
        actual: u64,
    },
    TimeOutOfRange {
        timestamp: i64,
        start: i64,
        end: i64,
    },
    ProvedStateMismatch {
        expected: bool,
        actual: bool,
    },
}
