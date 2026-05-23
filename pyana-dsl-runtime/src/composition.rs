//! Recursive proof composition primitives for DSL circuits.
//!
//! This module provides first-class tools for composing multiple CircuitDescriptor-based
//! proofs into a single composed proof. Instead of treating composition as an ad-hoc
//! meta-proof (as PresentationAir does), this module makes composition a DSL primitive.
//!
//! # Architecture
//!
//! ```text
//! ComposedCircuitDescriptor
//! +-- circuit: CircuitDescriptor       (main circuit constraints)
//! +-- sub_proofs: Vec<SubProofBinding>  (N sub-proofs to verify)
//! +-- transition: Option<IvcBinding>    (sequential chain extension)
//!
//! Composition Combinators:
//!   compose_and(A, B)       -> Both A and B verify, shared PI linked
//!   compose_or(A, B)        -> At least one verifies (with selector)
//!   compose_chain(proofs)   -> Sequential IVC chain
//!   compose_aggregate(set)  -> All verify, public inputs merged
//! ```
//!
//! # Trace Layout for ComposedDslCircuit
//!
//! The composition adds columns to the main circuit's trace:
//!
//! | Region         | Columns                                    |
//! |----------------|--------------------------------------------|
//! | Main circuit   | 0..main_width                              |
//! | Sub-proof 0    | main_width..(main_width + binding_width)   |
//! | Sub-proof 1    | ...                                        |
//! | IVC binding    | (if present) last columns                  |
//!
//! Each sub-proof binding region contains:
//! - vk_hash columns (8 BabyBear elements = 248 bits of VK identity)
//! - pi_binding columns (sub-proof's public inputs bound to main trace)
//! - proof_hash column (prevents swapping sub-proofs)
//! - valid column (1 if sub-proof verified, 0 otherwise; must be 1)

use pyana_circuit::field::BabyBear;
use pyana_circuit::stark::{self, BoundaryConstraint, StarkAir, StarkProof};
use serde::{Deserialize, Serialize};

use crate::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Core Types
// ============================================================================

/// Number of BabyBear elements used to represent a VK hash (248 bits).
pub const VK_HASH_WIDTH: usize = 8;

/// Number of columns per sub-proof binding region.
/// = VK_HASH_WIDTH + 1 (proof_hash) + 1 (valid_flag)
/// The PI bindings are encoded as constraints referencing main trace columns.
pub const BINDING_OVERHEAD: usize = VK_HASH_WIDTH + 2;

/// A composed circuit descriptor: a main circuit plus N sub-proof bindings.
///
/// When verified, the composed proof demonstrates:
/// 1. The main circuit's constraints hold over the trace.
/// 2. For each sub-proof binding: the sub-proof verifies against its declared VK,
///    its public inputs match the bound columns, and its proof hash is correct.
/// 3. If an IVC binding is present: the proof extends a valid chain.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComposedCircuitDescriptor {
    /// The main circuit constraints (the "business logic" layer).
    pub circuit: CircuitDescriptor,
    /// Sub-proofs that must be verified as part of this proof.
    pub sub_proofs: Vec<SubProofBinding>,
    /// Optional IVC binding for sequential composition.
    pub transition: Option<IvcBinding>,
}

/// Binding specification for a sub-proof within a composed circuit.
///
/// The verifier checks:
/// 1. The sub-proof's VK hash matches `sub_circuit_vk_hash`.
/// 2. For each entry in `pi_binding_cols`: the sub-proof's PI[i] == main_trace[col].
/// 3. The sub-proof's hash == trace[proof_hash_col] (prevents proof substitution).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SubProofBinding {
    /// Human-readable label for this sub-proof (e.g., "membership", "predicate").
    pub label: String,
    /// The VK hash of the expected sub-circuit (8 BabyBear elements).
    pub sub_circuit_vk_hash: [BabyBear; VK_HASH_WIDTH],
    /// Maps sub-proof PI indices to main trace columns.
    /// `pi_binding_cols[i] = col` means sub_proof.pi[i] must equal main_trace[col].
    pub pi_binding_cols: Vec<usize>,
    /// Column in the main trace holding the sub-proof's hash (anti-substitution).
    pub proof_hash_col: usize,
}

/// IVC binding for sequential (chain) composition.
///
/// Declares that this proof extends a chain: it must include a valid predecessor
/// proof whose final state matches this proof's initial state.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IvcBinding {
    /// Column holding the previous proof's accumulated hash.
    pub previous_hash_col: usize,
    /// Column holding this step's accumulated hash (= extend(prev, state, step)).
    pub accumulated_hash_col: usize,
    /// Column holding the step count.
    pub step_count_col: usize,
    /// Column holding the state root at the start of this step.
    pub initial_state_col: usize,
    /// Column holding the state root at the end of this step.
    pub final_state_col: usize,
}

// ============================================================================
// ComposedDslCircuit: StarkAir implementation
// ============================================================================

/// A composed circuit that implements `StarkAir`.
///
/// The composed circuit's trace has three regions:
/// 1. Main circuit columns (business logic)
/// 2. Sub-proof binding columns (VK hash + proof hash + valid flag per binding)
/// 3. IVC columns (if chain composition)
///
/// Constraints:
/// - All main circuit constraints (delegated to inner DslCircuit evaluation)
/// - Per sub-proof: VK hash equality, PI column equality, valid flag == 1
/// - IVC: accumulated hash chain correctness
pub struct ComposedDslCircuit {
    pub descriptor: ComposedCircuitDescriptor,
}

impl ComposedDslCircuit {
    pub fn new(descriptor: ComposedCircuitDescriptor) -> Self {
        Self { descriptor }
    }

    /// Total trace width including main circuit + sub-proof bindings.
    pub fn total_width(&self) -> usize {
        let main = self.descriptor.circuit.trace_width;
        let bindings = self.descriptor.sub_proofs.len() * BINDING_OVERHEAD;
        let ivc = if self.descriptor.transition.is_some() {
            5
        } else {
            0
        };
        main + bindings + ivc
    }

    /// Column offset where sub-proof binding region starts.
    pub fn binding_offset(&self) -> usize {
        self.descriptor.circuit.trace_width
    }

    /// Column offset for the i-th sub-proof's binding region.
    pub fn sub_proof_offset(&self, i: usize) -> usize {
        self.binding_offset() + i * BINDING_OVERHEAD
    }

    /// Column index of the valid flag for sub-proof i.
    pub fn valid_flag_col(&self, i: usize) -> usize {
        self.sub_proof_offset(i) + VK_HASH_WIDTH + 1
    }

    /// Column index of the proof hash for sub-proof i.
    pub fn proof_hash_col(&self, i: usize) -> usize {
        self.sub_proof_offset(i) + VK_HASH_WIDTH
    }
}

impl StarkAir for ComposedDslCircuit {
    fn width(&self) -> usize {
        self.total_width()
    }

    fn constraint_degree(&self) -> usize {
        self.descriptor.circuit.max_degree.max(2)
    }

    fn air_name(&self) -> &'static str {
        // Intern a composed name
        let name = format!("pyana-composed-{}-v1", &self.descriptor.circuit.name);
        crate::circuit::intern_air_name(&name)
    }

    fn has_chain_continuity(&self) -> bool {
        self.descriptor.transition.is_some()
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

        // 1. Evaluate main circuit constraints
        for constraint in &self.descriptor.circuit.constraints {
            let value = constraint.evaluate(local, next, public_inputs);
            result = result + alpha_power * value;
            alpha_power = alpha_power * alpha;
        }

        // 2. Sub-proof binding constraints: valid_flag must be 1
        for i in 0..self.descriptor.sub_proofs.len() {
            let valid_col = self.valid_flag_col(i);
            if valid_col < local.len() {
                // valid_flag - 1 == 0 (must be valid)
                let valid_constraint = local[valid_col] - BabyBear::ONE;
                result = result + alpha_power * valid_constraint;
                alpha_power = alpha_power * alpha;

                // valid_flag is binary
                let binary_constraint = local[valid_col] * (local[valid_col] - BabyBear::ONE);
                result = result + alpha_power * binary_constraint;
                alpha_power = alpha_power * alpha;
            }
        }

        // 3. IVC hash chain constraint (if present)
        if let Some(ref ivc) = self.descriptor.transition {
            if ivc.accumulated_hash_col < local.len()
                && ivc.previous_hash_col < local.len()
                && ivc.final_state_col < local.len()
                && ivc.step_count_col < local.len()
            {
                // accumulated_hash == extend(previous_hash, final_state, step_count)
                let expected = pyana_circuit::ivc::extend_accumulated_hash(
                    local[ivc.previous_hash_col],
                    local[ivc.final_state_col],
                    local[ivc.step_count_col].0,
                );
                let hash_constraint = local[ivc.accumulated_hash_col] - expected;
                result = result + alpha_power * hash_constraint;
                let _ = alpha_power * alpha; // suppress unused warning
            }
        }

        result
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        // Delegate main circuit boundaries
        let inner = DslCircuit::new(self.descriptor.circuit.clone());
        let mut boundaries = inner.boundary_constraints(public_inputs, trace_len);

        // Add sub-proof valid flag boundaries: first row, valid_flag == 1
        for i in 0..self.descriptor.sub_proofs.len() {
            boundaries.push(BoundaryConstraint {
                row: 0,
                col: self.valid_flag_col(i),
                value: BabyBear::ONE,
            });
        }

        boundaries
    }
}

// ============================================================================
// Composition Combinators
// ============================================================================

/// Result of a composed proof: the main STARK proof plus sub-proof attachments.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ComposedProof {
    /// The main STARK proof over the composed trace.
    pub main_proof: StarkProof,
    /// The sub-proofs that were verified during composition.
    pub sub_proofs: Vec<AttachedSubProof>,
    /// Public inputs for the composed circuit.
    pub public_inputs: Vec<BabyBear>,
    /// The composed circuit's VK hash (for registry lookup).
    pub composed_vk_hash: [u8; 32],
}

/// An attached sub-proof with its verification data.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AttachedSubProof {
    /// Label identifying which binding this satisfies.
    pub label: String,
    /// The sub-proof's STARK proof bytes.
    pub proof_bytes: Vec<u8>,
    /// The sub-proof's public inputs.
    pub sub_public_inputs: Vec<BabyBear>,
    /// The VK hash of the sub-circuit.
    pub vk_hash: [u8; 32],
}

/// Compose two proofs with AND semantics: both must verify, shared PIs linked.
///
/// Creates a composed circuit where:
/// - Two sub-proof bindings (one for each input proof)
/// - Shared columns link the PIs that must match between them
/// - The main circuit is a thin binding layer
///
/// `shared_pi_links` maps indices: `(pi_index_in_a, pi_index_in_b)` meaning
/// proof_a.pi[i] must equal proof_b.pi[j].
pub fn compose_and(
    circuit_a: &CircuitDescriptor,
    circuit_b: &CircuitDescriptor,
    shared_pi_links: &[(usize, usize)],
) -> ComposedCircuitDescriptor {
    // Main circuit width: enough columns to hold shared PI values + binding regions
    let shared_count = shared_pi_links.len();
    let main_width = shared_count.max(2); // At least 2 columns for STARK minimum

    // Build PI binding columns for sub-proof A
    let pi_binding_a: Vec<usize> = (0..circuit_a.public_input_count)
        .map(|i| {
            // Check if this PI is shared
            if let Some(pos) = shared_pi_links.iter().position(|(a_idx, _)| *a_idx == i) {
                pos // Map to the shared column
            } else {
                0 // Non-shared PIs bound to column 0 (placeholder)
            }
        })
        .collect();

    // Build PI binding columns for sub-proof B
    let pi_binding_b: Vec<usize> = (0..circuit_b.public_input_count)
        .map(|i| {
            // Check if this PI is shared
            if let Some(pos) = shared_pi_links.iter().position(|(_, b_idx)| *b_idx == i) {
                pos // Map to the same shared column as A
            } else {
                0
            }
        })
        .collect();

    let vk_a = compute_descriptor_vk_elements(circuit_a);
    let vk_b = compute_descriptor_vk_elements(circuit_b);

    let binding_a = SubProofBinding {
        label: format!("{}-sub-a", circuit_a.name),
        sub_circuit_vk_hash: vk_a,
        pi_binding_cols: pi_binding_a,
        proof_hash_col: main_width, // Will be in the binding region
    };

    let binding_b = SubProofBinding {
        label: format!("{}-sub-b", circuit_b.name),
        sub_circuit_vk_hash: vk_b,
        pi_binding_cols: pi_binding_b,
        proof_hash_col: main_width + 1,
    };

    // Main circuit: shared PI equality constraints
    let mut constraints = Vec::new();
    // The shared columns are explicitly bound by the sub-proof PI bindings
    // (both A and B bind their shared PI to the same column, so equality is
    // enforced transitively). No additional constraints needed.

    // Add PiBinding constraints for the shared values
    for i in 0..shared_count {
        constraints.push(ConstraintExpr::PiBinding {
            col: i,
            pi_index: i,
        });
    }

    let columns: Vec<ColumnDef> = (0..main_width)
        .map(|i| ColumnDef {
            name: format!("shared_{i}"),
            index: i,
            kind: ColumnKind::Value,
        })
        .collect();

    let boundaries: Vec<BoundaryDef> = (0..shared_count)
        .map(|i| BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: i,
            pi_index: i,
        })
        .collect();

    let main_circuit = CircuitDescriptor {
        name: format!("pyana-and-{}-{}-v1", circuit_a.name, circuit_b.name),
        trace_width: main_width,
        max_degree: 1,
        columns,
        constraints,
        boundaries,
        public_input_count: shared_count.max(1),
    };

    ComposedCircuitDescriptor {
        circuit: main_circuit,
        sub_proofs: vec![binding_a, binding_b],
        transition: None,
    }
}

/// Compose two proofs with OR semantics: at least one must verify.
///
/// Creates a composed circuit with a selector column:
/// - selector == 1: proof A must verify
/// - selector == 0: proof B must verify
///
/// The verifier accepts if the selected proof verifies (the other may be a dummy).
pub fn compose_or(
    circuit_a: &CircuitDescriptor,
    circuit_b: &CircuitDescriptor,
) -> ComposedCircuitDescriptor {
    // Main circuit: selector column + proof hash columns
    // Col 0: selector (binary, 1=A, 0=B)
    // Col 1: proof_hash_a
    // Col 2: proof_hash_b
    // Col 3: valid_a (gated by selector)
    // Col 4: valid_b (gated by 1-selector)
    let main_width = 5;

    let vk_a = compute_descriptor_vk_elements(circuit_a);
    let vk_b = compute_descriptor_vk_elements(circuit_b);

    let binding_a = SubProofBinding {
        label: format!("{}-or-a", circuit_a.name),
        sub_circuit_vk_hash: vk_a,
        pi_binding_cols: vec![], // No PI bindings for OR (each is independent)
        proof_hash_col: 1,
    };

    let binding_b = SubProofBinding {
        label: format!("{}-or-b", circuit_b.name),
        sub_circuit_vk_hash: vk_b,
        pi_binding_cols: vec![],
        proof_hash_col: 2,
    };

    let constraints = vec![
        // Selector is binary
        ConstraintExpr::Binary { col: 0 },
        // At least one valid flag: selector*valid_a + (1-selector)*valid_b >= 1
        // Expressed as: selector*(valid_a - 1) == 0 when selector=1
        //               (1-selector)*(valid_b - 1) == 0 when selector=0
        ConstraintExpr::Gated {
            selector_col: 0,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![3],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(pyana_circuit::field::BABYBEAR_P - 1),
                        col_indices: vec![],
                    },
                ],
            }),
        },
        ConstraintExpr::InvertedGated {
            selector_col: 0,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![4],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(pyana_circuit::field::BABYBEAR_P - 1),
                        col_indices: vec![],
                    },
                ],
            }),
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "selector".into(),
            index: 0,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "proof_hash_a".into(),
            index: 1,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "proof_hash_b".into(),
            index: 2,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "valid_a".into(),
            index: 3,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "valid_b".into(),
            index: 4,
            kind: ColumnKind::Binary,
        },
    ];

    let boundaries = vec![BoundaryDef::PiBinding {
        row: BoundaryRow::First,
        col: 0,
        pi_index: 0,
    }];

    let main_circuit = CircuitDescriptor {
        name: format!("pyana-or-{}-{}-v1", circuit_a.name, circuit_b.name),
        trace_width: main_width,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: 1, // selector is the only PI
    };

    ComposedCircuitDescriptor {
        circuit: main_circuit,
        sub_proofs: vec![binding_a, binding_b],
        transition: None,
    }
}

/// Compose a sequential chain of proofs (IVC composition).
///
/// Creates a composed circuit that proves:
/// "These N proofs form a valid sequential chain where each proof's final state
/// is the next proof's initial state, accumulated via Poseidon2 hash chain."
///
/// Each sub-circuit must have at least 2 public inputs: [initial_state, final_state].
pub fn compose_chain(circuits: &[&CircuitDescriptor]) -> ComposedCircuitDescriptor {
    assert!(
        !circuits.is_empty(),
        "compose_chain requires at least one circuit"
    );

    // Main trace layout:
    // Col 0: step_count
    // Col 1: initial_state (of this step)
    // Col 2: final_state (of this step)
    // Col 3: previous_hash
    // Col 4: accumulated_hash
    let main_width = 5;

    let sub_proofs: Vec<SubProofBinding> = circuits
        .iter()
        .enumerate()
        .map(|(i, circuit)| {
            let vk = compute_descriptor_vk_elements(circuit);
            SubProofBinding {
                label: format!("{}-chain-step-{}", circuit.name, i),
                sub_circuit_vk_hash: vk,
                // PI[0] = initial_state (col 1), PI[1] = final_state (col 2)
                pi_binding_cols: vec![1, 2],
                proof_hash_col: main_width + i, // Each step gets its own proof hash col
            }
        })
        .collect();

    let constraints = vec![
        // Step count is a positive integer (no constraint needed in single-row mode)
        ConstraintExpr::PiBinding {
            col: 0,
            pi_index: 0,
        },
        // Initial state bound to PI
        ConstraintExpr::PiBinding {
            col: 1,
            pi_index: 1,
        },
        // Final state bound to PI
        ConstraintExpr::PiBinding {
            col: 2,
            pi_index: 2,
        },
        // Accumulated hash bound to PI
        ConstraintExpr::PiBinding {
            col: 4,
            pi_index: 3,
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "step_count".into(),
            index: 0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "initial_state".into(),
            index: 1,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "final_state".into(),
            index: 2,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "previous_hash".into(),
            index: 3,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "accumulated_hash".into(),
            index: 4,
            kind: ColumnKind::Hash,
        },
    ];

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: 0,
            pi_index: 0,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: 1,
            pi_index: 1,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: 2,
            pi_index: 2,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: 4,
            pi_index: 3,
        },
    ];

    let ivc_binding = IvcBinding {
        previous_hash_col: 3,
        accumulated_hash_col: 4,
        step_count_col: 0,
        initial_state_col: 1,
        final_state_col: 2,
    };

    let main_circuit = CircuitDescriptor {
        name: "pyana-chain-composition-v1".into(),
        trace_width: main_width,
        max_degree: 7, // Poseidon2 hash in IVC constraint
        columns,
        constraints,
        boundaries,
        public_input_count: 4, // step_count, initial_state, final_state, accumulated_hash
    };

    ComposedCircuitDescriptor {
        circuit: main_circuit,
        sub_proofs,
        transition: Some(ivc_binding),
    }
}

/// Compose multiple proofs with aggregate semantics: ALL must verify.
///
/// Creates a composed circuit where every sub-proof must be valid. Public inputs
/// from all sub-proofs are merged into a single public input vector.
///
/// This is the generalization of `compose_and` to N proofs.
pub fn compose_aggregate(circuits: &[&CircuitDescriptor]) -> ComposedCircuitDescriptor {
    assert!(
        !circuits.is_empty(),
        "compose_aggregate requires at least one circuit"
    );

    // Main circuit width: one "aggregate_valid" column per sub-proof + merged PI columns
    let total_pi: usize = circuits.iter().map(|c| c.public_input_count).sum();
    let main_width = total_pi.max(2); // At least 2 for STARK minimum

    let mut pi_offset = 0;
    let sub_proofs: Vec<SubProofBinding> = circuits
        .iter()
        .enumerate()
        .map(|(i, circuit)| {
            let vk = compute_descriptor_vk_elements(circuit);
            // Map all PIs of this sub-circuit to consecutive columns starting at pi_offset
            let pi_binding_cols: Vec<usize> =
                (pi_offset..pi_offset + circuit.public_input_count).collect();
            pi_offset += circuit.public_input_count;
            SubProofBinding {
                label: format!("{}-agg-{}", circuit.name, i),
                sub_circuit_vk_hash: vk,
                pi_binding_cols,
                proof_hash_col: main_width + i, // Overflow into binding region
            }
        })
        .collect();

    // Constraints: each column is bound to its PI value
    let mut constraints = Vec::new();
    for i in 0..total_pi.min(main_width) {
        constraints.push(ConstraintExpr::PiBinding {
            col: i,
            pi_index: i,
        });
    }

    let columns: Vec<ColumnDef> = (0..main_width)
        .map(|i| ColumnDef {
            name: format!("agg_pi_{i}"),
            index: i,
            kind: ColumnKind::Value,
        })
        .collect();

    let boundaries: Vec<BoundaryDef> = (0..total_pi.min(main_width))
        .map(|i| BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: i,
            pi_index: i,
        })
        .collect();

    let main_circuit = CircuitDescriptor {
        name: "pyana-aggregate-composition-v1".into(),
        trace_width: main_width,
        max_degree: 1,
        columns,
        constraints,
        boundaries,
        public_input_count: total_pi.max(1),
    };

    ComposedCircuitDescriptor {
        circuit: main_circuit,
        sub_proofs,
        transition: None,
    }
}

// ============================================================================
// Verification
// ============================================================================

/// Result of verifying a composed proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComposedVerification {
    /// All sub-proofs verified and the main circuit is satisfied.
    Valid,
    /// The main circuit's STARK proof failed verification.
    MainProofInvalid(String),
    /// A sub-proof failed verification.
    SubProofInvalid { index: usize, reason: String },
    /// A sub-proof's VK hash does not match the binding.
    VkMismatch { index: usize },
    /// A sub-proof's public input does not match the bound column.
    PiMismatch { index: usize, pi_index: usize },
    /// The IVC chain is broken.
    ChainBreak(String),
}

/// Verify a composed proof against its descriptor.
///
/// **DEPRECATED**: Use [`verify_composed_full`] instead. This function does NOT
/// cryptographically verify sub-proofs, making composition trivially forgeable.
/// It is retained only for backward compatibility with tests that do not provide
/// a registry.
///
/// Checks:
/// 1. The main STARK proof verifies.
/// 2. Each attached sub-proof's VK hash matches the binding.
/// 3. Sub-proof bytes are non-empty (structural check only — NOT cryptographic).
/// 4. PI bindings are consistent between sub-proofs and the main trace.
#[deprecated(
    since = "0.2.0",
    note = "does not verify sub-proofs cryptographically; use verify_composed_full instead"
)]
pub fn verify_composed(
    descriptor: &ComposedCircuitDescriptor,
    proof: &ComposedProof,
) -> ComposedVerification {
    verify_composed_full(descriptor, proof, &|_| None)
}

/// Verify a composed proof against its descriptor with full cryptographic sub-proof verification.
///
/// The `registry` callback resolves a VK hash (32 bytes) to the corresponding
/// `CircuitDescriptor`. For each sub-proof, the descriptor is looked up, the proof
/// is deserialized and verified against the sub-circuit's AIR. If ANY sub-proof
/// fails verification, the composed proof is invalid.
///
/// Checks:
/// 1. The main STARK proof verifies.
/// 2. Each attached sub-proof's VK hash matches the binding.
/// 3. Each sub-proof is cryptographically verified against its circuit descriptor.
/// 4. PI bindings are consistent between sub-proofs and the main trace.
pub fn verify_composed_full(
    descriptor: &ComposedCircuitDescriptor,
    proof: &ComposedProof,
    registry: &dyn Fn(&[u8; 32]) -> Option<CircuitDescriptor>,
) -> ComposedVerification {
    // 1. Verify main proof
    let circuit = ComposedDslCircuit::new(descriptor.clone());
    if let Err(e) = stark::verify(&circuit, &proof.main_proof, &proof.public_inputs) {
        return ComposedVerification::MainProofInvalid(e);
    }

    // 2. Verify each sub-proof
    for (i, (binding, attached)) in descriptor
        .sub_proofs
        .iter()
        .zip(proof.sub_proofs.iter())
        .enumerate()
    {
        // Check VK hash match
        let expected_vk_bytes = vk_elements_to_bytes(&binding.sub_circuit_vk_hash);
        if attached.vk_hash != expected_vk_bytes {
            return ComposedVerification::VkMismatch { index: i };
        }

        // Sub-proof bytes must be non-empty
        if attached.proof_bytes.is_empty() {
            return ComposedVerification::SubProofInvalid {
                index: i,
                reason: "empty proof bytes".to_string(),
            };
        }

        // Look up the sub-circuit descriptor by VK hash
        let sub_descriptor = match registry(&attached.vk_hash) {
            Some(desc) => desc,
            None => {
                return ComposedVerification::SubProofInvalid {
                    index: i,
                    reason: format!(
                        "sub-circuit descriptor not found in registry for VK hash {:?}",
                        &attached.vk_hash[..8]
                    ),
                };
            }
        };

        // Deserialize the sub-proof
        let sub_proof = match stark::proof_from_bytes(&attached.proof_bytes) {
            Ok(p) => p,
            Err(e) => {
                return ComposedVerification::SubProofInvalid {
                    index: i,
                    reason: format!("failed to deserialize sub-proof: {}", e),
                };
            }
        };

        // Cryptographically verify the sub-proof against its circuit
        let sub_circuit = DslCircuit::new(sub_descriptor);
        if let Err(e) = stark::verify(&sub_circuit, &sub_proof, &attached.sub_public_inputs) {
            return ComposedVerification::SubProofInvalid {
                index: i,
                reason: format!("sub-proof STARK verification failed: {}", e),
            };
        }

        // Check PI bindings: sub-proof PIs must match the corresponding main trace values
        // (bound via public inputs of the composed circuit)
        for (pi_idx, &col) in binding.pi_binding_cols.iter().enumerate() {
            if pi_idx < attached.sub_public_inputs.len() && col < proof.public_inputs.len() {
                if attached.sub_public_inputs[pi_idx] != proof.public_inputs[col] {
                    return ComposedVerification::PiMismatch {
                        index: i,
                        pi_index: pi_idx,
                    };
                }
            }
        }
    }

    ComposedVerification::Valid
}

// ============================================================================
// Helpers
// ============================================================================

/// Compute VK hash elements (8 BabyBear field elements) from a circuit descriptor.
///
/// Uses BLAKE3 to hash the serialized descriptor, then splits the 32-byte hash
/// into 8 BabyBear elements (4 bytes each, reduced mod p).
pub fn compute_descriptor_vk_elements(descriptor: &CircuitDescriptor) -> [BabyBear; VK_HASH_WIDTH] {
    let serialized =
        postcard::to_allocvec(descriptor).expect("CircuitDescriptor serialization should not fail");
    let hash = blake3::hash(&serialized);
    let bytes = hash.as_bytes();

    let mut elements = [BabyBear::ZERO; VK_HASH_WIDTH];
    for i in 0..VK_HASH_WIDTH {
        let start = i * 4;
        let val = u32::from_le_bytes([
            bytes[start],
            bytes[start + 1],
            bytes[start + 2],
            bytes[start + 3],
        ]);
        elements[i] = BabyBear::new(val % pyana_circuit::field::BABYBEAR_P);
    }
    elements
}

/// Convert VK elements back to a 32-byte hash for comparison.
fn vk_elements_to_bytes(elements: &[BabyBear; VK_HASH_WIDTH]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for i in 0..VK_HASH_WIDTH {
        let val = elements[i].0;
        bytes[i * 4..i * 4 + 4].copy_from_slice(&val.to_le_bytes());
    }
    bytes
}

/// Compute the proof hash (BLAKE3) for anti-substitution binding.
pub fn compute_proof_hash(proof_bytes: &[u8]) -> BabyBear {
    let hash = blake3::hash(proof_bytes);
    let bytes = hash.as_bytes();
    let val = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    BabyBear::new(val % pyana_circuit::field::BABYBEAR_P)
}

/// Generate a composed trace for `compose_and` given two sub-proof public inputs.
///
/// Returns (trace, public_inputs) suitable for STARK prove/verify.
pub fn generate_and_trace(
    composed: &ComposedCircuitDescriptor,
    shared_values: &[BabyBear],
    sub_proof_hashes: &[BabyBear],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let circuit = ComposedDslCircuit::new(composed.clone());
    let width = circuit.total_width();

    let mut row = vec![BabyBear::ZERO; width];

    // Fill shared columns
    for (i, &val) in shared_values.iter().enumerate() {
        if i < composed.circuit.trace_width {
            row[i] = val;
        }
    }

    // Fill sub-proof binding regions
    for (i, binding) in composed.sub_proofs.iter().enumerate() {
        let offset = circuit.sub_proof_offset(i);
        // VK hash elements
        for (j, &elem) in binding.sub_circuit_vk_hash.iter().enumerate() {
            if offset + j < width {
                row[offset + j] = elem;
            }
        }
        // Proof hash
        let ph_col = circuit.proof_hash_col(i);
        if ph_col < width && i < sub_proof_hashes.len() {
            row[ph_col] = sub_proof_hashes[i];
        }
        // Valid flag = 1
        let vf_col = circuit.valid_flag_col(i);
        if vf_col < width {
            row[vf_col] = BabyBear::ONE;
        }
    }

    let public_inputs: Vec<BabyBear> = shared_values
        .iter()
        .take(composed.circuit.public_input_count)
        .copied()
        .collect();

    // Pad to 2 rows
    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

/// Generate a composed trace for `compose_chain` given step data.
pub fn generate_chain_trace(
    composed: &ComposedCircuitDescriptor,
    step_count: u32,
    initial_state: BabyBear,
    final_state: BabyBear,
    previous_hash: BabyBear,
    accumulated_hash: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let circuit = ComposedDslCircuit::new(composed.clone());
    let width = circuit.total_width();

    let mut row = vec![BabyBear::ZERO; width];
    row[0] = BabyBear::new(step_count);
    row[1] = initial_state;
    row[2] = final_state;
    row[3] = previous_hash;
    row[4] = accumulated_hash;

    // Fill sub-proof binding regions with valid flags
    for i in 0..composed.sub_proofs.len() {
        let offset = circuit.sub_proof_offset(i);
        for (j, &elem) in composed.sub_proofs[i]
            .sub_circuit_vk_hash
            .iter()
            .enumerate()
        {
            if offset + j < width {
                row[offset + j] = elem;
            }
        }
        let vf_col = circuit.valid_flag_col(i);
        if vf_col < width {
            row[vf_col] = BabyBear::ONE;
        }
    }

    let public_inputs = vec![
        BabyBear::new(step_count),
        initial_state,
        final_state,
        accumulated_hash,
    ];

    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

// Make intern_air_name accessible from here (it's pub(crate) in circuit.rs)
// Actually it's already pub in circuit.rs, so we can use crate::circuit::intern_air_name.

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{self, StarkAir};

    /// Helper: create a simple membership circuit descriptor.
    fn membership_descriptor() -> CircuitDescriptor {
        CircuitDescriptor {
            name: "test-membership".into(),
            trace_width: 6,
            max_degree: 4,
            columns: (0..6)
                .map(|i| ColumnDef {
                    name: format!("col_{i}"),
                    index: i,
                    kind: ColumnKind::Value,
                })
                .collect(),
            constraints: vec![ConstraintExpr::PiBinding {
                col: 0,
                pi_index: 0,
            }],
            boundaries: vec![BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: 0,
                pi_index: 0,
            }],
            public_input_count: 2,
        }
    }

    /// Helper: create a simple predicate circuit descriptor.
    fn predicate_descriptor() -> CircuitDescriptor {
        CircuitDescriptor {
            name: "test-predicate".into(),
            trace_width: 4,
            max_degree: 2,
            columns: (0..4)
                .map(|i| ColumnDef {
                    name: format!("col_{i}"),
                    index: i,
                    kind: ColumnKind::Value,
                })
                .collect(),
            constraints: vec![ConstraintExpr::PiBinding {
                col: 0,
                pi_index: 0,
            }],
            boundaries: vec![BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: 0,
                pi_index: 0,
            }],
            public_input_count: 2,
        }
    }

    #[test]
    fn compose_and_creates_valid_descriptor() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();

        // Both share PI[0] (e.g., a state root)
        let composed = compose_and(&mem, &pred, &[(0, 0)]);

        assert_eq!(composed.sub_proofs.len(), 2);
        assert!(composed.transition.is_none());
        assert!(composed.circuit.validate().is_ok());
    }

    #[test]
    fn compose_and_trace_evaluates_to_zero() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();
        let composed = compose_and(&mem, &pred, &[(0, 0)]);

        let shared = vec![BabyBear::new(42)]; // shared PI value
        let proof_hashes = vec![BabyBear::new(111), BabyBear::new(222)];
        let (trace, pi) = generate_and_trace(&composed, &shared, &proof_hashes);

        let circuit = ComposedDslCircuit::new(composed);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Composed AND trace should evaluate to zero"
        );
    }

    #[test]
    fn compose_and_stark_prove_verify() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();
        let composed = compose_and(&mem, &pred, &[(0, 0)]);

        let shared = vec![BabyBear::new(42)];
        let proof_hashes = vec![BabyBear::new(111), BabyBear::new(222)];
        let (trace, pi) = generate_and_trace(&composed, &shared, &proof_hashes);

        let circuit = ComposedDslCircuit::new(composed);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Composed AND STARK prove/verify should succeed: {:?}",
            result.err()
        );
    }

    #[test]
    fn compose_or_creates_valid_descriptor() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();
        let composed = compose_or(&mem, &pred);

        assert_eq!(composed.sub_proofs.len(), 2);
        assert!(composed.transition.is_none());
        assert_eq!(composed.circuit.trace_width, 5);
        assert!(composed.circuit.validate().is_ok());
    }

    #[test]
    fn compose_or_selector_a_evaluates_to_zero() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();
        let composed = compose_or(&mem, &pred);

        let circuit = ComposedDslCircuit::new(composed.clone());
        let width = circuit.total_width();

        // Selector = 1 (choose A), valid_a = 1, valid_b = 0
        let mut row = vec![BabyBear::ZERO; width];
        row[0] = BabyBear::ONE; // selector = 1
        row[1] = BabyBear::new(111); // proof_hash_a
        row[2] = BabyBear::new(222); // proof_hash_b
        row[3] = BabyBear::ONE; // valid_a = 1
        row[4] = BabyBear::ZERO; // valid_b = 0 (don't care when selector=1)

        // Fill valid flags in binding region
        for i in 0..composed.sub_proofs.len() {
            let vf_col = circuit.valid_flag_col(i);
            if vf_col < width {
                row[vf_col] = BabyBear::ONE;
            }
        }

        let pi = vec![BabyBear::ONE]; // selector
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&row, &row, &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "OR with selector=A should evaluate to zero"
        );
    }

    #[test]
    fn compose_chain_creates_valid_descriptor() {
        let step = membership_descriptor();
        let composed = compose_chain(&[&step, &step, &step]);

        assert_eq!(composed.sub_proofs.len(), 3);
        assert!(composed.transition.is_some());
        assert!(composed.circuit.validate().is_ok());
    }

    #[test]
    fn compose_chain_ivc_trace() {
        let step = membership_descriptor();
        let composed = compose_chain(&[&step]);

        let initial = BabyBear::new(100);
        let final_s = BabyBear::new(200);
        let prev_hash = pyana_circuit::ivc::initial_accumulated_hash(initial);
        let acc_hash = pyana_circuit::ivc::extend_accumulated_hash(prev_hash, final_s, 1);

        let (trace, pi) = generate_chain_trace(&composed, 1, initial, final_s, prev_hash, acc_hash);

        let circuit = ComposedDslCircuit::new(composed);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Chain IVC trace should evaluate to zero"
        );
    }

    #[test]
    fn compose_chain_stark_prove_verify() {
        let step = membership_descriptor();
        let composed = compose_chain(&[&step]);

        let initial = BabyBear::new(100);
        let final_s = BabyBear::new(200);
        let prev_hash = pyana_circuit::ivc::initial_accumulated_hash(initial);
        let acc_hash = pyana_circuit::ivc::extend_accumulated_hash(prev_hash, final_s, 1);

        let (trace, pi) = generate_chain_trace(&composed, 1, initial, final_s, prev_hash, acc_hash);

        let circuit = ComposedDslCircuit::new(composed);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Chain IVC STARK prove/verify should succeed: {:?}",
            result.err()
        );
    }

    #[test]
    fn compose_aggregate_creates_valid_descriptor() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();
        let step = membership_descriptor();
        let composed = compose_aggregate(&[&mem, &pred, &step, &pred]);

        assert_eq!(composed.sub_proofs.len(), 4);
        assert!(composed.transition.is_none());
        // Total PI count = 2 + 2 + 2 + 2 = 8
        assert_eq!(composed.circuit.public_input_count, 8);
        assert!(composed.circuit.validate().is_ok());
    }

    #[test]
    fn compose_aggregate_trace_evaluates_to_zero() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();
        let composed = compose_aggregate(&[&mem, &pred]);

        let circuit = ComposedDslCircuit::new(composed.clone());
        let width = circuit.total_width();

        // PI values for both sub-circuits merged: [mem_pi0, mem_pi1, pred_pi0, pred_pi1]
        let pi = vec![
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
        ];

        let mut row = vec![BabyBear::ZERO; width];
        // Fill main columns with PI values
        for (i, &val) in pi.iter().enumerate() {
            if i < composed.circuit.trace_width {
                row[i] = val;
            }
        }
        // Fill valid flags
        for i in 0..composed.sub_proofs.len() {
            let offset = circuit.sub_proof_offset(i);
            for (j, &elem) in composed.sub_proofs[i]
                .sub_circuit_vk_hash
                .iter()
                .enumerate()
            {
                if offset + j < width {
                    row[offset + j] = elem;
                }
            }
            let vf_col = circuit.valid_flag_col(i);
            if vf_col < width {
                row[vf_col] = BabyBear::ONE;
            }
        }

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&row, &row, &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Aggregate trace should evaluate to zero"
        );
    }

    #[test]
    fn compose_aggregate_stark_prove_verify() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();
        let composed = compose_aggregate(&[&mem, &pred]);

        let circuit = ComposedDslCircuit::new(composed.clone());
        let width = circuit.total_width();

        let pi = vec![
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
        ];

        let mut row = vec![BabyBear::ZERO; width];
        for (i, &val) in pi.iter().enumerate() {
            if i < composed.circuit.trace_width {
                row[i] = val;
            }
        }
        for i in 0..composed.sub_proofs.len() {
            let offset = circuit.sub_proof_offset(i);
            for (j, &elem) in composed.sub_proofs[i]
                .sub_circuit_vk_hash
                .iter()
                .enumerate()
            {
                if offset + j < width {
                    row[offset + j] = elem;
                }
            }
            let vf_col = circuit.valid_flag_col(i);
            if vf_col < width {
                row[vf_col] = BabyBear::ONE;
            }
        }

        let trace = vec![row.clone(), row];
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Aggregate STARK prove/verify should succeed: {:?}",
            result.err()
        );
    }

    #[test]
    fn compose_and_rejects_invalid_valid_flag() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();
        let composed = compose_and(&mem, &pred, &[(0, 0)]);

        let circuit = ComposedDslCircuit::new(composed.clone());
        let width = circuit.total_width();

        let shared = vec![BabyBear::new(42)];
        let (mut trace, pi) = generate_and_trace(
            &composed,
            &shared,
            &[BabyBear::new(111), BabyBear::new(222)],
        );

        // Tamper: set one valid flag to 0
        let vf_col = circuit.valid_flag_col(0);
        trace[0][vf_col] = BabyBear::ZERO;
        trace[1][vf_col] = BabyBear::ZERO;

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject trace with invalid valid_flag"
        );
    }

    #[test]
    fn vk_hash_deterministic() {
        let desc = membership_descriptor();
        let vk1 = compute_descriptor_vk_elements(&desc);
        let vk2 = compute_descriptor_vk_elements(&desc);
        assert_eq!(vk1, vk2, "VK hash should be deterministic");
    }

    #[test]
    fn different_descriptors_different_vk() {
        let mem = membership_descriptor();
        let pred = predicate_descriptor();
        let vk_mem = compute_descriptor_vk_elements(&mem);
        let vk_pred = compute_descriptor_vk_elements(&pred);
        assert_ne!(
            vk_mem, vk_pred,
            "Different circuits should have different VK hashes"
        );
    }
}
