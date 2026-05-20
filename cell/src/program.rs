//! Cell programs: state transition logic carried by cells.
//!
//! A cell program defines valid state transitions. The executor checks the program's
//! constraints on every state-modifying action. This turns cells from "accounts with
//! permissions" into "smart contracts with privacy."
//!
//! # Use Cases
//!
//! - **Private DEX order**: Cell holds (asset, amount, price). The matching predicate
//!   is part of the cell. A filler proves they satisfy the predicate without seeing
//!   the full order details.
//! - **Sealed auction**: Cell holds committed bid. On reveal, proves bid > minimum
//!   and bid was committed before deadline.
//! - **NFT with provenance**: Cell holds ownership + history. Transfer proves valid
//!   chain without revealing full provenance to public.

use serde::{Deserialize, Serialize};

use crate::state::{CellState, FieldElement, FIELD_ZERO, STATE_SLOTS};

/// A cell program defines valid state transitions.
/// The executor checks the program's constraints on every state-modifying action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CellProgram {
    /// No program — any authorized state change is valid (current behavior).
    None,

    /// Predicate program: a set of conditions that must hold after transition.
    /// Expressed as a list of constraints over the 8 field slots.
    Predicate(Vec<StateConstraint>),

    /// Circuit program: an AIR/R1CS circuit that defines the valid state transition function.
    /// The proof in the Action's authorization MUST satisfy this circuit.
    Circuit {
        /// Hash of the circuit (for lookup/verification).
        circuit_hash: [u8; 32],
    },
}

impl Default for CellProgram {
    fn default() -> Self {
        CellProgram::None
    }
}

/// A constraint on cell state (for Predicate programs).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StateConstraint {
    /// Field at index must equal value.
    FieldEquals { index: u8, value: FieldElement },
    /// Field at index must be >= value (unsigned big-endian comparison).
    FieldGte { index: u8, value: FieldElement },
    /// Field at index must be <= value (unsigned big-endian comparison).
    FieldLte { index: u8, value: FieldElement },
    /// Sum of fields at indices must equal value (conservation law).
    /// Fields are interpreted as little-endian u64 in the first 8 bytes.
    SumEquals { indices: Vec<u8>, value: FieldElement },
    /// Field must not change from its previous value (immutable after initialization).
    Immutable { index: u8 },
    /// Custom: hash of a more complex constraint (checked by external verifier).
    Custom { constraint_hash: [u8; 32] },
}

/// Error from evaluating a cell program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramError {
    /// A state constraint was violated.
    ConstraintViolated {
        constraint: StateConstraint,
        description: String,
    },
    /// A field index in a constraint is out of bounds.
    InvalidFieldIndex { index: u8 },
    /// A circuit proof is required but was not provided.
    CircuitProofRequired { circuit_hash: [u8; 32] },
    /// Custom constraint cannot be evaluated locally.
    CustomConstraintUnevaluable { constraint_hash: [u8; 32] },
}

impl core::fmt::Display for ProgramError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProgramError::ConstraintViolated { description, .. } => {
                write!(f, "program constraint violated: {description}")
            }
            ProgramError::InvalidFieldIndex { index } => {
                write!(f, "program references invalid field index: {index}")
            }
            ProgramError::CircuitProofRequired { .. } => {
                write!(f, "circuit program requires a proof in the action authorization")
            }
            ProgramError::CustomConstraintUnevaluable { .. } => {
                write!(f, "custom constraint cannot be evaluated locally")
            }
        }
    }
}

impl std::error::Error for ProgramError {}

impl CellProgram {
    /// Evaluate the program's constraints against the new (post-transition) state.
    ///
    /// For `Immutable` constraints, `old_state` is required to compare the field
    /// value before and after the transition.
    ///
    /// Returns `Ok(())` if all constraints pass, or the first `ProgramError` on failure.
    pub fn evaluate(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
    ) -> Result<(), ProgramError> {
        match self {
            CellProgram::None => Ok(()),
            CellProgram::Predicate(constraints) => {
                for constraint in constraints {
                    evaluate_constraint(constraint, new_state, old_state)?;
                }
                Ok(())
            }
            CellProgram::Circuit { circuit_hash } => {
                // Circuit programs are not evaluated locally — they require a proof.
                // The executor must check that the action carries a valid proof
                // before reaching this point. If we get here without a proof,
                // it means the executor didn't enforce it.
                Err(ProgramError::CircuitProofRequired {
                    circuit_hash: *circuit_hash,
                })
            }
        }
    }

    /// Returns true if this program is `None` (backward-compatible no-op).
    pub fn is_none(&self) -> bool {
        matches!(self, CellProgram::None)
    }

    /// Returns true if this program requires proof authorization for state transitions.
    pub fn requires_proof(&self) -> bool {
        matches!(self, CellProgram::Circuit { .. })
    }
}

/// Evaluate a single constraint against the cell state.
fn evaluate_constraint(
    constraint: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
) -> Result<(), ProgramError> {
    match constraint {
        StateConstraint::FieldEquals { index, value } => {
            let idx = *index as usize;
            if idx >= STATE_SLOTS {
                return Err(ProgramError::InvalidFieldIndex { index: *index });
            }
            if new_state.fields[idx] != *value {
                return Err(ProgramError::ConstraintViolated {
                    constraint: constraint.clone(),
                    description: format!(
                        "field[{idx}] != expected value"
                    ),
                });
            }
            Ok(())
        }

        StateConstraint::FieldGte { index, value } => {
            let idx = *index as usize;
            if idx >= STATE_SLOTS {
                return Err(ProgramError::InvalidFieldIndex { index: *index });
            }
            if !field_gte(&new_state.fields[idx], value) {
                return Err(ProgramError::ConstraintViolated {
                    constraint: constraint.clone(),
                    description: format!(
                        "field[{idx}] < minimum value"
                    ),
                });
            }
            Ok(())
        }

        StateConstraint::FieldLte { index, value } => {
            let idx = *index as usize;
            if idx >= STATE_SLOTS {
                return Err(ProgramError::InvalidFieldIndex { index: *index });
            }
            if !field_lte(&new_state.fields[idx], value) {
                return Err(ProgramError::ConstraintViolated {
                    constraint: constraint.clone(),
                    description: format!(
                        "field[{idx}] > maximum value"
                    ),
                });
            }
            Ok(())
        }

        StateConstraint::SumEquals { indices, value } => {
            let mut sum: u64 = 0;
            for &idx in indices {
                if idx as usize >= STATE_SLOTS {
                    return Err(ProgramError::InvalidFieldIndex { index: idx });
                }
                let field_val = field_to_u64(&new_state.fields[idx as usize]);
                sum = sum.saturating_add(field_val);
            }
            let expected = field_to_u64(value);
            if sum != expected {
                return Err(ProgramError::ConstraintViolated {
                    constraint: constraint.clone(),
                    description: format!(
                        "sum of fields {:?} = {sum}, expected {expected}",
                        indices
                    ),
                });
            }
            Ok(())
        }

        StateConstraint::Immutable { index } => {
            let idx = *index as usize;
            if idx >= STATE_SLOTS {
                return Err(ProgramError::InvalidFieldIndex { index: *index });
            }
            if let Some(old) = old_state {
                if new_state.fields[idx] != old.fields[idx] {
                    return Err(ProgramError::ConstraintViolated {
                        constraint: constraint.clone(),
                        description: format!(
                            "field[{idx}] was mutated but is marked immutable"
                        ),
                    });
                }
            }
            // If no old_state provided, we cannot check immutability — allow it
            // (this handles the initialization case).
            Ok(())
        }

        StateConstraint::Custom { constraint_hash } => {
            // Custom constraints require an external verifier; we cannot evaluate locally.
            Err(ProgramError::CustomConstraintUnevaluable {
                constraint_hash: *constraint_hash,
            })
        }
    }
}

/// Interpret a field element as a little-endian u64 (first 8 bytes).
fn field_to_u64(field: &FieldElement) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[..8]);
    u64::from_le_bytes(bytes)
}

/// Compare two field elements as unsigned big-endian: a >= b.
fn field_gte(a: &FieldElement, b: &FieldElement) -> bool {
    // Compare as big-endian (most significant byte first).
    for i in (0..32).rev() {
        if a[i] > b[i] {
            return true;
        }
        if a[i] < b[i] {
            return false;
        }
    }
    true // equal
}

/// Compare two field elements as unsigned big-endian: a <= b.
fn field_lte(a: &FieldElement, b: &FieldElement) -> bool {
    field_gte(b, a)
}

/// Helper: create a FieldElement from a u64 (little-endian in first 8 bytes).
pub fn field_from_u64(val: u64) -> FieldElement {
    let mut f = FIELD_ZERO;
    f[..8].copy_from_slice(&val.to_le_bytes());
    f
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_program_backward_compat() {
        let program = CellProgram::None;
        let state = CellState::new(100);
        assert!(program.evaluate(&state, None).is_ok());
    }

    #[test]
    fn test_field_equals_pass() {
        let program = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(42),
        }]);
        let mut state = CellState::new(0);
        state.fields[0] = field_from_u64(42);
        assert!(program.evaluate(&state, None).is_ok());
    }

    #[test]
    fn test_field_equals_fail() {
        let program = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(42),
        }]);
        let mut state = CellState::new(0);
        state.fields[0] = field_from_u64(99);
        assert!(program.evaluate(&state, None).is_err());
    }

    #[test]
    fn test_predicate_program_enforced() {
        // Cell with FieldGte constraint rejects transitions that violate it.
        let program = CellProgram::Predicate(vec![StateConstraint::FieldGte {
            index: 1,
            value: field_from_u64(100),
        }]);

        // Value = 200 >= 100: passes
        let mut state = CellState::new(0);
        state.fields[1] = field_from_u64(200);
        assert!(program.evaluate(&state, None).is_ok());

        // Value = 50 < 100: fails
        state.fields[1] = field_from_u64(50);
        assert!(program.evaluate(&state, None).is_err());
    }

    #[test]
    fn test_field_lte() {
        let program = CellProgram::Predicate(vec![StateConstraint::FieldLte {
            index: 2,
            value: field_from_u64(1000),
        }]);

        let mut state = CellState::new(0);
        state.fields[2] = field_from_u64(500);
        assert!(program.evaluate(&state, None).is_ok());

        state.fields[2] = field_from_u64(1001);
        assert!(program.evaluate(&state, None).is_err());
    }

    #[test]
    fn test_immutable_field() {
        let program = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);

        let mut old_state = CellState::new(0);
        old_state.fields[3] = field_from_u64(77);

        // Same value: passes
        let mut new_state = old_state.clone();
        assert!(program.evaluate(&new_state, Some(&old_state)).is_ok());

        // Different value: fails
        new_state.fields[3] = field_from_u64(88);
        assert!(program.evaluate(&new_state, Some(&old_state)).is_err());
    }

    #[test]
    fn test_immutable_field_no_old_state() {
        // Without old state (initialization), immutable constraint passes.
        let program = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
        let mut state = CellState::new(0);
        state.fields[3] = field_from_u64(77);
        assert!(program.evaluate(&state, None).is_ok());
    }

    #[test]
    fn test_sum_conservation() {
        // SumEquals constraint enforces balance conservation across fields.
        let program = CellProgram::Predicate(vec![StateConstraint::SumEquals {
            indices: vec![0, 1, 2],
            value: field_from_u64(1000),
        }]);

        // 400 + 300 + 300 = 1000: passes
        let mut state = CellState::new(0);
        state.fields[0] = field_from_u64(400);
        state.fields[1] = field_from_u64(300);
        state.fields[2] = field_from_u64(300);
        assert!(program.evaluate(&state, None).is_ok());

        // 500 + 300 + 300 = 1100 != 1000: fails
        state.fields[0] = field_from_u64(500);
        assert!(program.evaluate(&state, None).is_err());
    }

    #[test]
    fn test_multiple_constraints_all_must_pass() {
        let program = CellProgram::Predicate(vec![
            StateConstraint::FieldGte {
                index: 0,
                value: field_from_u64(10),
            },
            StateConstraint::FieldLte {
                index: 0,
                value: field_from_u64(100),
            },
        ]);

        // 50 is in [10, 100]: passes
        let mut state = CellState::new(0);
        state.fields[0] = field_from_u64(50);
        assert!(program.evaluate(&state, None).is_ok());

        // 5 < 10: fails first constraint
        state.fields[0] = field_from_u64(5);
        assert!(program.evaluate(&state, None).is_err());

        // 200 > 100: fails second constraint
        state.fields[0] = field_from_u64(200);
        assert!(program.evaluate(&state, None).is_err());
    }

    #[test]
    fn test_invalid_field_index() {
        let program = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
            index: 99,
            value: field_from_u64(1),
        }]);
        let state = CellState::new(0);
        let err = program.evaluate(&state, None).unwrap_err();
        assert!(matches!(err, ProgramError::InvalidFieldIndex { index: 99 }));
    }

    #[test]
    fn test_circuit_program_requires_proof() {
        let program = CellProgram::Circuit {
            circuit_hash: [0xAB; 32],
        };
        let state = CellState::new(0);
        let err = program.evaluate(&state, None).unwrap_err();
        assert!(matches!(err, ProgramError::CircuitProofRequired { .. }));
    }

    #[test]
    fn test_program_default_is_none() {
        let program = CellProgram::default();
        assert!(program.is_none());
        assert!(!program.requires_proof());
    }
}
