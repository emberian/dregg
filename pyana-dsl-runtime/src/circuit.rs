//! Runtime circuit descriptor: a generic `StarkAir` implementation driven by data.
//!
//! Instead of the proc macro generating full `impl StarkAir` code, it emits a
//! [`CircuitDescriptor`] that the generic [`DslCircuit`] interprets at runtime.

use pyana_circuit::field::BabyBear;
use pyana_circuit::stark::{BoundaryConstraint, StarkAir};

// ============================================================================
// Descriptor types
// ============================================================================

/// A complete description of an AIR circuit — trace layout, constraints, boundaries.
#[derive(Debug, Clone)]
pub struct CircuitDescriptor {
    pub name: &'static str,
    pub trace_width: usize,
    pub max_degree: usize,
    pub columns: Vec<ColumnDef>,
    pub constraints: Vec<ConstraintExpr>,
    pub boundaries: Vec<BoundaryDef>,
    pub public_input_count: usize,
}

/// Metadata for a single trace column.
#[derive(Debug, Clone)]
pub struct ColumnDef {
    pub name: &'static str,
    pub index: usize,
    pub kind: ColumnKind,
}

/// Semantic kind of a column (for documentation and potential future optimization).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ColumnKind {
    Value,
    Binary,
    Selector,
    Hash,
}

/// An algebraic constraint expression that evaluates to zero on a valid trace.
#[derive(Debug, Clone)]
pub enum ConstraintExpr {
    /// `local[a] - local[b] == 0`
    Equality { col_a: usize, col_b: usize },
    /// `local[a] * local[b] - local[output] == 0`
    Multiplication { a: usize, b: usize, output: usize },
    /// `local[col] * (local[col] - 1) == 0` (boolean check)
    Binary { col: usize },
    /// `local[col] - pi[pi_index] == 0` (typically enforced via boundary)
    PiBinding { col: usize, pi_index: usize },
    /// `next[next_col] - local[local_col] == 0`
    Transition { next_col: usize, local_col: usize },
    /// Arbitrary polynomial: sum of terms, each a coefficient times a product of columns.
    Polynomial { terms: Vec<PolyTerm> },
    /// Gated constraint: `local[selector_col] * inner == 0`
    Gated { selector_col: usize, inner: Box<ConstraintExpr> },
}

/// A single term in a polynomial constraint: `coeff * product(local[col] for col in col_indices)`.
#[derive(Debug, Clone)]
pub struct PolyTerm {
    pub coeff: BabyBear,
    /// Product of these column values. Empty = constant term (just coeff).
    pub col_indices: Vec<usize>,
}

/// A boundary constraint definition (binds a trace cell to a value at prove time).
#[derive(Debug, Clone)]
pub enum BoundaryDef {
    /// `trace[row][col] == pi[pi_index]`
    PiBinding { row: BoundaryRow, col: usize, pi_index: usize },
    /// `trace[row][col] == fixed_value`
    Fixed { row: BoundaryRow, col: usize, value: BabyBear },
}

/// Which row a boundary constraint targets.
#[derive(Debug, Clone, Copy)]
pub enum BoundaryRow {
    First,
    Last,
    /// Absolute row index.
    Index(usize),
}

// ============================================================================
// Constraint evaluation
// ============================================================================

impl ConstraintExpr {
    /// Evaluate this constraint expression given the current and next row.
    pub fn evaluate(&self, local: &[BabyBear], next: &[BabyBear], pi: &[BabyBear]) -> BabyBear {
        match self {
            Self::Equality { col_a, col_b } => local[*col_a] - local[*col_b],
            Self::Multiplication { a, b, output } => {
                local[*a] * local[*b] - local[*output]
            }
            Self::Binary { col } => {
                local[*col] * (local[*col] - BabyBear::ONE)
            }
            Self::PiBinding { col, pi_index } => local[*col] - pi[*pi_index],
            Self::Transition { next_col, local_col } => next[*next_col] - local[*local_col],
            Self::Polynomial { terms } => {
                let mut sum = BabyBear::ZERO;
                for term in terms {
                    let mut prod = term.coeff;
                    for &ci in &term.col_indices {
                        prod = prod * local[ci];
                    }
                    sum = sum + prod;
                }
                sum
            }
            Self::Gated { selector_col, inner } => {
                local[*selector_col] * inner.evaluate(local, next, pi)
            }
        }
    }
}

impl BoundaryDef {
    fn resolve_row(&self, trace_len: usize) -> usize {
        match self {
            Self::PiBinding { row, .. } | Self::Fixed { row, .. } => match row {
                BoundaryRow::First => 0,
                BoundaryRow::Last => trace_len - 1,
                BoundaryRow::Index(i) => *i,
            },
        }
    }
}

// ============================================================================
// DslCircuit: generic StarkAir driven by a descriptor
// ============================================================================

/// A circuit defined entirely by its descriptor. Implements `StarkAir` generically.
pub struct DslCircuit {
    pub descriptor: CircuitDescriptor,
}

impl DslCircuit {
    pub fn new(descriptor: CircuitDescriptor) -> Self {
        Self { descriptor }
    }
}

impl StarkAir for DslCircuit {
    fn width(&self) -> usize {
        self.descriptor.trace_width
    }

    fn constraint_degree(&self) -> usize {
        self.descriptor.max_degree
    }

    fn air_name(&self) -> &'static str {
        self.descriptor.name
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut result = BabyBear::ZERO;
        let mut alpha_power = BabyBear::ONE;
        for constraint in &self.descriptor.constraints {
            let value = constraint.evaluate(local, next, public_inputs);
            result = result + alpha_power * value;
            alpha_power = alpha_power * alpha;
        }
        result
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        self.descriptor
            .boundaries
            .iter()
            .map(|bdef| {
                let row = bdef.resolve_row(trace_len);
                match bdef {
                    BoundaryDef::PiBinding { col, pi_index, .. } => BoundaryConstraint {
                        row,
                        col: *col,
                        value: public_inputs[*pi_index],
                    },
                    BoundaryDef::Fixed { col, value, .. } => BoundaryConstraint {
                        row,
                        col: *col,
                        value: *value,
                    },
                }
            })
            .collect()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::stark::{prove, verify};

    /// Build a CircuitDescriptor equivalent to SovereignTransitionAir.
    ///
    /// Constraints:
    ///   c1: direction * (direction - 1) == 0   (Binary on col 3)
    ///   c2: new_balance - old_balance - transfer_amount + 2*direction*transfer_amount == 0
    ///       expressed as Polynomial with terms:
    ///         +1 * col[2]            (new_balance)
    ///         -1 * col[0]            (old_balance)
    ///         -1 * col[1]            (transfer_amount)
    ///         +2 * col[3] * col[1]   (2 * direction * transfer_amount)
    fn sovereign_transfer_descriptor() -> CircuitDescriptor {
        CircuitDescriptor {
            name: "pyana-sovereign-transition-v1",
            trace_width: 6,
            max_degree: 2,
            columns: vec![
                ColumnDef { name: "old_balance", index: 0, kind: ColumnKind::Value },
                ColumnDef { name: "transfer_amount", index: 1, kind: ColumnKind::Value },
                ColumnDef { name: "new_balance", index: 2, kind: ColumnKind::Value },
                ColumnDef { name: "direction", index: 3, kind: ColumnKind::Binary },
                ColumnDef { name: "pad0", index: 4, kind: ColumnKind::Value },
                ColumnDef { name: "pad1", index: 5, kind: ColumnKind::Value },
            ],
            constraints: vec![
                // c1: direction is boolean
                ConstraintExpr::Binary { col: 3 },
                // c2: balance conservation polynomial
                // new_balance - old_balance - transfer_amount + 2*direction*transfer_amount == 0
                ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm { coeff: BabyBear::ONE, col_indices: vec![2] },          // +new_balance
                        PolyTerm { coeff: BabyBear::new(pyana_circuit::field::BABYBEAR_P - 1), col_indices: vec![0] }, // -old_balance
                        PolyTerm { coeff: BabyBear::new(pyana_circuit::field::BABYBEAR_P - 1), col_indices: vec![1] }, // -transfer_amount
                        PolyTerm { coeff: BabyBear::new(2), col_indices: vec![3, 1] },    // +2*direction*transfer_amount
                    ],
                },
            ],
            boundaries: vec![],
            public_input_count: 32,
        }
    }

    #[test]
    fn dsl_circuit_matches_handwritten_air() {
        // Use the same test vectors as sovereign_transition_air tests.
        let old_balance = 1000u64;
        let transfer_amount = 100u64;
        let direction = 1u32; // outgoing => new = 900

        let new_balance = old_balance - transfer_amount;

        let row = vec![
            BabyBear::from_u64(old_balance),
            BabyBear::from_u64(transfer_amount),
            BabyBear::from_u64(new_balance),
            BabyBear::new(direction),
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];

        let dummy_next = vec![BabyBear::ZERO; 6];
        let dummy_pi = vec![BabyBear::ZERO; 32];
        let alpha = BabyBear::new(7); // arbitrary nonzero

        // Evaluate using hand-written AIR
        use pyana_circuit::sovereign_transition_air::SovereignTransitionAir;
        let hand = SovereignTransitionAir;
        let hand_result = hand.eval_constraints(&row, &dummy_next, &dummy_pi, alpha);

        // Evaluate using DslCircuit
        let dsl = DslCircuit::new(sovereign_transfer_descriptor());
        let dsl_result = dsl.eval_constraints(&row, &dummy_next, &dummy_pi, alpha);

        assert_eq!(
            hand_result, dsl_result,
            "DslCircuit and hand-written AIR must produce identical constraint evaluations"
        );

        // Both should be zero on a valid trace row.
        assert_eq!(hand_result, BabyBear::ZERO);
    }

    #[test]
    fn dsl_circuit_rejects_invalid_trace() {
        let row = vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(1000), // WRONG: should be 900
            BabyBear::ONE,            // direction = outgoing
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let dummy_next = vec![BabyBear::ZERO; 6];
        let dummy_pi = vec![BabyBear::ZERO; 32];
        let alpha = BabyBear::new(13);

        let dsl = DslCircuit::new(sovereign_transfer_descriptor());
        let result = dsl.eval_constraints(&row, &dummy_next, &dummy_pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "Invalid trace must produce nonzero constraint");
    }

    #[test]
    fn dsl_circuit_prove_and_verify() {
        use pyana_circuit::sovereign_transition_air::{
            bytes32_to_babybear, SOVEREIGN_PUBLIC_INPUTS,
        };

        let old_balance = 1000u64;
        let transfer_amount = 100u64;
        let direction = 1u32;
        let new_balance = old_balance - transfer_amount;

        // Build trace (2 rows, padded).
        let row = vec![
            BabyBear::from_u64(old_balance),
            BabyBear::from_u64(transfer_amount),
            BabyBear::from_u64(new_balance),
            BabyBear::new(direction),
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let trace = vec![row.clone(), row];

        // Build public inputs (same encoding as sovereign_transition_air).
        let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
        public_inputs.extend(bytes32_to_babybear(&[1u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[2u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[3u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[4u8; 32]));

        let dsl = DslCircuit::new(sovereign_transfer_descriptor());

        // Prove and verify using our custom STARK.
        let proof = prove(&dsl, &trace, &public_inputs);
        let result = verify(&dsl, &proof, &public_inputs);
        assert!(result.is_ok(), "DslCircuit prove/verify failed: {:?}", result.err());
    }

    #[test]
    fn dsl_circuit_incoming_transfer() {
        use pyana_circuit::sovereign_transition_air::{
            bytes32_to_babybear, SOVEREIGN_PUBLIC_INPUTS,
        };

        let old_balance = 500u64;
        let transfer_amount = 200u64;
        let direction = 0u32; // incoming => new = 700
        let new_balance = old_balance + transfer_amount;

        let row = vec![
            BabyBear::from_u64(old_balance),
            BabyBear::from_u64(transfer_amount),
            BabyBear::from_u64(new_balance),
            BabyBear::new(direction),
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let trace = vec![row.clone(), row];

        let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
        public_inputs.extend(bytes32_to_babybear(&[10u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[11u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[12u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[13u8; 32]));

        let dsl = DslCircuit::new(sovereign_transfer_descriptor());
        let proof = prove(&dsl, &trace, &public_inputs);
        let result = verify(&dsl, &proof, &public_inputs);
        assert!(result.is_ok(), "DslCircuit incoming transfer failed: {:?}", result.err());
    }
}
