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

use crate::state::{CellState, FIELD_ZERO, FieldElement, STATE_SLOTS};

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
    /// Fields are interpreted as big-endian u64 in the last 8 bytes.
    SumEquals {
        indices: Vec<u8>,
        value: FieldElement,
    },
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
    /// Immutable constraint cannot be verified without prior state.
    /// Fail-closed: if there is no old_state to compare against, the constraint
    /// cannot be satisfied (unless this is a fresh cell with nonce == 0).
    ImmutableCheckRequiresOldState { index: u8 },
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
                write!(
                    f,
                    "circuit program requires a proof in the action authorization"
                )
            }
            ProgramError::CustomConstraintUnevaluable { .. } => {
                write!(f, "custom constraint cannot be evaluated locally")
            }
            ProgramError::ImmutableCheckRequiresOldState { index } => {
                write!(
                    f,
                    "immutable constraint on field[{index}] cannot be verified without prior state"
                )
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
                    description: format!("field[{idx}] != expected value"),
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
                    description: format!("field[{idx}] < minimum value"),
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
                    description: format!("field[{idx}] > maximum value"),
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
                sum =
                    sum.checked_add(field_val)
                        .ok_or_else(|| ProgramError::ConstraintViolated {
                            constraint: constraint.clone(),
                            description: format!(
                                "overflow computing sum of fields {:?}: u64 addition overflowed",
                                indices
                            ),
                        })?;
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
            match old_state {
                Some(old) => {
                    if new_state.fields[idx] != old.fields[idx] {
                        return Err(ProgramError::ConstraintViolated {
                            constraint: constraint.clone(),
                            description: format!(
                                "field[{idx}] was mutated but is marked immutable"
                            ),
                        });
                    }
                }
                None => {
                    // Fail-closed: cannot verify immutability without prior state.
                    // The only legitimate case for None is cell initialization (nonce == 0),
                    // where immutable fields are being set for the first time.
                    if new_state.nonce != 0 {
                        return Err(ProgramError::ImmutableCheckRequiresOldState { index: *index });
                    }
                }
            }
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

/// Interpret a field element as a big-endian u64 (last 8 bytes).
fn field_to_u64(field: &FieldElement) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes)
}

/// Compare two field elements as unsigned big-endian: a >= b.
fn field_gte(a: &FieldElement, b: &FieldElement) -> bool {
    // Big-endian: compare from most significant byte (index 0) first.
    a >= b
}

/// Compare two field elements as unsigned big-endian: a <= b.
fn field_lte(a: &FieldElement, b: &FieldElement) -> bool {
    field_gte(b, a)
}

/// Helper: create a FieldElement from a u64 (big-endian in last 8 bytes).
///
/// The u64 value is stored at bytes [24..32] in big-endian order, with bytes [0..24]
/// zeroed. This ensures lexicographic (big-endian) comparison on the full 32-byte
/// array is equivalent to numerical comparison on the u64 value.
pub fn field_from_u64(val: u64) -> FieldElement {
    let mut f = FIELD_ZERO;
    f[24..32].copy_from_slice(&val.to_be_bytes());
    f
}

/// Alias for `field_from_u64` — explicit big-endian naming for clarity at call sites.
pub fn field_from_u64_be(val: u64) -> FieldElement {
    field_from_u64(val)
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
    fn test_immutable_field_no_old_state_initialization() {
        // Without old state, immutable constraint passes ONLY for fresh cells (nonce == 0).
        let program = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
        let mut state = CellState::new(0);
        state.fields[3] = field_from_u64(77);
        // nonce == 0: initialization path, allowed
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

    // --- Adversarial security tests ---

    #[test]
    fn test_immutable_bypass_fails_closed_when_no_old_state() {
        // CRITICAL: Calling evaluate with old_state=None on a non-fresh cell (nonce > 0)
        // must ERROR, not silently pass.
        let program = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
        let mut state = CellState::new(0);
        state.fields[3] = field_from_u64(77);
        state.nonce = 5; // Not a fresh cell — has been mutated before
        let result = program.evaluate(&state, None);
        assert!(
            result.is_err(),
            "immutable constraint must fail-closed when old_state is None and nonce > 0"
        );
        let err = result.unwrap_err();
        assert!(
            matches!(
                err,
                ProgramError::ImmutableCheckRequiresOldState { index: 3 }
            ),
            "expected ImmutableCheckRequiresOldState, got: {:?}",
            err
        );
    }

    #[test]
    fn test_field_gte_big_endian_correctness() {
        // Adversarial test: values where big-endian and little-endian orderings disagree.
        // a = [0x00, 0, ..., 0, 0xFF] — big-endian: small (MSB=0x00), little-endian: large (LSB=0xFF)
        // b = [0xFF, 0, ..., 0, 0x00] — big-endian: large (MSB=0xFF), little-endian: small (LSB=0x00)
        let mut a: FieldElement = [0u8; 32];
        a[31] = 0xFF; // LSB is large, but MSB (index 0) is 0x00
        let mut b: FieldElement = [0u8; 32];
        b[0] = 0xFF; // MSB is large, but LSB (index 31) is 0x00

        // In big-endian: a < b (because a[0]=0x00 < b[0]=0xFF)
        assert!(
            !field_gte(&a, &b),
            "field_gte(a, b) must be false: a is smaller than b in big-endian"
        );
        // And b >= a
        assert!(
            field_gte(&b, &a),
            "field_gte(b, a) must be true: b is larger than a in big-endian"
        );
        // field_lte should be the inverse
        assert!(
            field_lte(&a, &b),
            "field_lte(a, b) must be true: a <= b in big-endian"
        );
        assert!(
            !field_lte(&b, &a),
            "field_lte(b, a) must be false: b > a in big-endian"
        );
    }

    #[test]
    fn test_field_gte_equal_values() {
        let a: FieldElement = [0x42; 32];
        let b: FieldElement = [0x42; 32];
        assert!(field_gte(&a, &b), "equal values: a >= b must be true");
        assert!(field_lte(&a, &b), "equal values: a <= b must be true");
    }
}
