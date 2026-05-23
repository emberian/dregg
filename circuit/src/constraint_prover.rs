//! Constraint satisfaction prover for AIR definitions.
//!
//! Evaluates AIR constraints row-by-row on a given execution trace and checks
//! that every constraint evaluates to zero. This validates circuit logic and
//! produces a compact trace-digest proof. For full cryptographic soundness,
//! use the STARK prover in the [`crate::stark`] module.

use crate::field::BabyBear;
use std::fmt;

/// The result of a constraint evaluation.
#[derive(Clone, Debug)]
pub struct ConstraintViolation {
    /// Which row the violation occurred on.
    pub row: usize,
    /// Which constraint index was violated.
    pub constraint_idx: usize,
    /// The constraint's name/description.
    pub constraint_name: String,
    /// The non-zero value the constraint evaluated to.
    pub value: BabyBear,
}

impl fmt::Display for ConstraintViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Constraint violation at row {}: '{}' (constraint #{}) evaluated to {}",
            self.row, self.constraint_name, self.constraint_idx, self.value
        )
    }
}

/// Result of constraint satisfaction checking.
#[derive(Clone, Debug)]
pub enum ConstraintCheckResult {
    /// All constraints satisfied -- the trace is valid.
    Valid,
    /// One or more constraints were violated.
    Invalid(Vec<ConstraintViolation>),
}

impl ConstraintCheckResult {
    pub fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }

    pub fn violations(&self) -> &[ConstraintViolation] {
        match self {
            Self::Valid => &[],
            Self::Invalid(v) => v,
        }
    }
}

/// A named constraint expression that can be evaluated on trace rows.
pub struct Constraint {
    pub name: String,
    /// The constraint function takes (current_row, next_row, public_inputs) -> value.
    /// It must evaluate to zero for a valid trace.
    pub eval: ConstraintFn,
}

/// Type-erased constraint function.
/// Arguments: (current_row_values, next_row_values_or_none, public_inputs)
/// Returns: the constraint residual (must be zero for valid trace).
pub type ConstraintFn =
    Box<dyn Fn(&[BabyBear], Option<&[BabyBear]>, &[BabyBear]) -> BabyBear + Send + Sync>;

/// The trait that all AIR definitions implement.
///
/// An AIR (Algebraic Intermediate Representation) defines:
/// - The trace width (number of columns)
/// - The constraints that must hold between consecutive rows
/// - The public inputs
pub trait Air: Send + Sync {
    /// Number of columns in the execution trace.
    fn trace_width(&self) -> usize;

    /// Number of public input elements.
    fn num_public_inputs(&self) -> usize;

    /// Generate the list of constraints.
    /// Each constraint is evaluated on every pair of consecutive rows.
    fn constraints(&self) -> Vec<Constraint>;

    /// Optional: constraints that only apply to the first row.
    fn first_row_constraints(&self) -> Vec<Constraint> {
        vec![]
    }

    /// Optional: constraints that only apply to the last row.
    fn last_row_constraints(&self) -> Vec<Constraint> {
        vec![]
    }

    /// Generate the execution trace for the given witness.
    /// Returns (trace_rows, public_inputs).
    /// Each row is a Vec<BabyBear> of length trace_width().
    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>);
}

/// Constraint satisfaction prover. Evaluates all AIR constraints on the trace.
pub struct ConstraintProver;

impl ConstraintProver {
    /// Verify that the given trace satisfies all AIR constraints.
    pub fn verify(air: &dyn Air) -> ConstraintCheckResult {
        let (trace, public_inputs) = air.generate_trace();
        Self::verify_trace(air, &trace, &public_inputs)
    }

    /// Verify a pre-generated trace against the AIR constraints.
    ///
    /// This avoids redundant trace generation when the caller already has the trace.
    pub fn verify_trace(
        air: &dyn Air,
        trace: &[Vec<BabyBear>],
        public_inputs: &[BabyBear],
    ) -> ConstraintCheckResult {
        if trace.is_empty() {
            return ConstraintCheckResult::Valid;
        }

        let mut violations = Vec::new();

        // Check trace width consistency
        for (row_idx, row) in trace.iter().enumerate() {
            if row.len() != air.trace_width() {
                violations.push(ConstraintViolation {
                    row: row_idx,
                    constraint_idx: 0,
                    constraint_name: format!(
                        "trace_width (expected {}, got {})",
                        air.trace_width(),
                        row.len()
                    ),
                    value: BabyBear::ONE,
                });
            }
        }

        if !violations.is_empty() {
            return ConstraintCheckResult::Invalid(violations);
        }

        // Check first row constraints
        let first_row_constraints = air.first_row_constraints();
        for (c_idx, constraint) in first_row_constraints.iter().enumerate() {
            let next_row = if trace.len() > 1 {
                Some(trace[1].as_slice())
            } else {
                None
            };
            let value = (constraint.eval)(&trace[0], next_row, public_inputs);
            if value != BabyBear::ZERO {
                violations.push(ConstraintViolation {
                    row: 0,
                    constraint_idx: c_idx,
                    constraint_name: format!("first_row::{}", constraint.name),
                    value,
                });
            }
        }

        // Check transition constraints (row i -> row i+1)
        let constraints = air.constraints();
        for row_idx in 0..trace.len() {
            let next_row = if row_idx + 1 < trace.len() {
                Some(trace[row_idx + 1].as_slice())
            } else {
                None
            };

            for (c_idx, constraint) in constraints.iter().enumerate() {
                let value = (constraint.eval)(&trace[row_idx], next_row, public_inputs);
                if value != BabyBear::ZERO {
                    violations.push(ConstraintViolation {
                        row: row_idx,
                        constraint_idx: c_idx,
                        constraint_name: constraint.name.clone(),
                        value,
                    });
                }
            }
        }

        // Check last row constraints
        let last_row_constraints = air.last_row_constraints();
        if let Some(last_row) = trace.last() {
            for (c_idx, constraint) in last_row_constraints.iter().enumerate() {
                let value = (constraint.eval)(last_row, None, public_inputs);
                if value != BabyBear::ZERO {
                    violations.push(ConstraintViolation {
                        row: trace.len() - 1,
                        constraint_idx: c_idx,
                        constraint_name: format!("last_row::{}", constraint.name),
                        value,
                    });
                }
            }
        }

        if violations.is_empty() {
            ConstraintCheckResult::Valid
        } else {
            ConstraintCheckResult::Invalid(violations)
        }
    }

    /// Run verification and return a human-readable report.
    pub fn verify_and_report(air: &dyn Air) -> String {
        let result = Self::verify(air);
        match result {
            ConstraintCheckResult::Valid => "All constraints satisfied.".to_string(),
            ConstraintCheckResult::Invalid(violations) => {
                let mut report = format!("{} constraint violation(s):\n", violations.len());
                for v in &violations {
                    report.push_str(&format!("  - {v}\n"));
                }
                report
            }
        }
    }
}

/// A proof produced by constraint satisfaction checking.
///
/// Contains the trace digest (BLAKE3 hash of the full execution trace) and
/// public inputs. This validates that the AIR constraints are satisfied without
/// requiring full STARK proof generation. For cryptographic soundness in
/// adversarial settings, use the STARK prover.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ConstraintProof {
    /// The number of trace rows.
    pub num_rows: usize,
    /// The number of columns.
    pub num_cols: usize,
    /// The number of public inputs.
    pub num_public_inputs: usize,
    /// A BLAKE3 digest of the entire trace (for integrity).
    pub trace_digest: [u8; 32],
    /// The public inputs (visible to verifier).
    pub public_inputs: Vec<BabyBear>,
    /// Proof size in bytes (estimated for the equivalent STARK proof).
    pub simulated_proof_size_bytes: usize,
}

impl ConstraintProof {
    /// Generate a constraint proof without verifying constraints.
    ///
    /// Use when the real cryptographic check is handled by a separate STARK proof
    /// and this ConstraintProof is only needed for metadata (public inputs, size).
    pub fn generate_unchecked(air: &dyn Air) -> Self {
        let (trace, public_inputs) = air.generate_trace();
        let num_rows = trace.len();
        let num_cols = air.trace_width();

        let mut hasher = blake3::Hasher::new();
        for row in &trace {
            for elem in row {
                hasher.update(&elem.0.to_le_bytes());
            }
        }
        let trace_digest = *hasher.finalize().as_bytes();

        let log_rows = (num_rows.max(1) as f64).log2().ceil() as usize;
        let security_bits = 128;
        let fri_queries = security_bits / 2;
        let simulated_proof_size_bytes =
            num_cols * log_rows * fri_queries * 4 + public_inputs.len() * 4 + 32;

        Self {
            num_rows,
            num_cols,
            num_public_inputs: public_inputs.len(),
            trace_digest,
            public_inputs,
            simulated_proof_size_bytes,
        }
    }

    /// Generate a constraint proof from a valid trace.
    pub fn generate(air: &dyn Air) -> Option<Self> {
        let (trace, public_inputs) = air.generate_trace();
        let result = ConstraintProver::verify_trace(air, &trace, &public_inputs);
        if !result.is_valid() {
            return None;
        }
        let num_rows = trace.len();
        let num_cols = air.trace_width();

        // Compute trace digest
        let mut hasher = blake3::Hasher::new();
        for row in &trace {
            for elem in row {
                hasher.update(&elem.0.to_le_bytes());
            }
        }
        let trace_digest = *hasher.finalize().as_bytes();

        // Estimate proof size: in a real STARK, it's roughly
        // O(num_cols * log(num_rows) * security_parameter)
        let log_rows = (num_rows as f64).log2().ceil() as usize;
        let security_bits = 128;
        let fri_queries = security_bits / 2; // ~64 queries
        let simulated_proof_size_bytes = num_cols * log_rows * fri_queries * 4 // FRI layers
            + public_inputs.len() * 4 // public inputs
            + 32; // root commitment

        Some(Self {
            num_rows,
            num_cols,
            num_public_inputs: public_inputs.len(),
            trace_digest,
            public_inputs,
            simulated_proof_size_bytes,
        })
    }

    /// Verify a constraint proof (checks public input consistency).
    pub fn verify(&self, expected_public_inputs: &[BabyBear]) -> bool {
        if self.public_inputs.len() != expected_public_inputs.len() {
            return false;
        }
        self.public_inputs == expected_public_inputs
    }

    /// Human-readable proof size.
    pub fn proof_size_display(&self) -> String {
        if self.simulated_proof_size_bytes < 1024 {
            format!("{} B", self.simulated_proof_size_bytes)
        } else if self.simulated_proof_size_bytes < 1024 * 1024 {
            format!("{:.1} KiB", self.simulated_proof_size_bytes as f64 / 1024.0)
        } else {
            format!(
                "{:.1} MiB",
                self.simulated_proof_size_bytes as f64 / (1024.0 * 1024.0)
            )
        }
    }
}

// Backward-compatible type aliases for internal migration.
// These will be removed in a future version.
#[doc(hidden)]
pub type MockProof = ConstraintProof;
#[doc(hidden)]
pub type MockProver = ConstraintProver;
#[doc(hidden)]
pub type MockProofResult = ConstraintCheckResult;

#[cfg(test)]
mod tests {
    use super::*;

    /// A trivial AIR for testing: one column, constraint is col[0] * (col[0] - 1) = 0
    /// (each row must be 0 or 1).
    struct BinaryAir {
        values: Vec<BabyBear>,
    }

    impl Air for BinaryAir {
        fn trace_width(&self) -> usize {
            1
        }
        fn num_public_inputs(&self) -> usize {
            0
        }
        fn constraints(&self) -> Vec<Constraint> {
            vec![Constraint {
                name: "binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let x = row[0];
                    x * (x - BabyBear::ONE) // must be 0 or 1
                }),
            }]
        }
        fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
            let trace = self.values.iter().map(|&v| vec![v]).collect();
            (trace, vec![])
        }
    }

    #[test]
    fn constraint_prover_valid_trace() {
        let air = BinaryAir {
            values: vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::ONE, BabyBear::ZERO],
        };
        let result = ConstraintProver::verify(&air);
        assert!(result.is_valid());
    }

    #[test]
    fn constraint_prover_invalid_trace() {
        let air = BinaryAir {
            values: vec![BabyBear::ZERO, BabyBear::new(2), BabyBear::ONE],
        };
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid());
        assert_eq!(result.violations().len(), 1);
        assert_eq!(result.violations()[0].row, 1);
    }

    #[test]
    fn constraint_proof_generation() {
        let air = BinaryAir {
            values: vec![BabyBear::ONE, BabyBear::ZERO, BabyBear::ONE],
        };
        let proof = ConstraintProof::generate(&air).unwrap();
        assert_eq!(proof.num_rows, 3);
        assert_eq!(proof.num_cols, 1);
        assert!(proof.verify(&[]));
    }

    #[test]
    fn constraint_proof_fails_on_invalid() {
        let air = BinaryAir {
            values: vec![BabyBear::new(5)],
        };
        let proof = ConstraintProof::generate(&air);
        assert!(proof.is_none());
    }
}
