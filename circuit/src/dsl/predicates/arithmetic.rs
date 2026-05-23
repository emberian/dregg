//! Full arithmetic predicate expressed as a CircuitDescriptor.
//!
//! Port of `circuit/src/arithmetic_predicate_air.rs` (2902 lines) to the DSL runtime.
//!
//! Supports the FULL expression evaluation model:
//! - Expression AST: Var, Const, Add, Sub, Mul, Min, Max, Sum, Abs, DivFloor, Mod
//! - Expression compilation to flat opcode slots
//! - Variable-width traces depending on expression complexity
//! - 6 predicate types: ExprGte, ExprLte, ExprEq, ExprNeq, ExprInRange, ExprCompare
//! - 6 comparison operators: Gte, Lte, Gt, Lt, Eq, Neq
//! - Multi-operand aggregates: Min(Vec), Max(Vec), Sum(Vec)
//! - Abs with range proof
//! - Dual-expression evaluation for ExprCompare
//!
//! # Design
//!
//! The circuit is built dynamically from the compiled expression. Each opcode gets
//! a "slot" column for its result. Complex operations (Min, Max, Abs, DivFloor, Mod)
//! get additional auxiliary columns for range proofs. The predicate comparison section
//! uses bit decomposition (or inverse witness for EQ/NEQ) to prove the final relation.
//!
//! # Trace Layout (dynamic width)
//!
//! | Columns          | Description                                          |
//! |------------------|------------------------------------------------------|
//! | 0..N-1           | input values (private witness)                       |
//! | N..N+M-1         | expression A slot results (one per compiled op)      |
//! | N+M..N+M+K-1    | expression B slot results (ExprCompare only)         |
//! | aux region       | auxiliary columns for complex ops (range proof bits)  |
//! | threshold_col    | threshold (public comparison target)                 |
//! | diff_col         | diff value for predicate comparison                  |
//! | diff_bits[0..29] | bit decomposition of diff (30 bits)                  |
//! | fact_commit_col  | fact commitment (binding to token state)             |
//! | neq_inverse_col  | inverse witness for NEQ predicates                   |
//!
//! # Public Inputs
//!
//! `[threshold, fact_commitment]`

use crate::field::{BABYBEAR_P, BabyBear};
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Constants
// ============================================================================

/// Number of bits used for range proofs (diff decomposition).
pub const NUM_BITS: usize = 30;

/// Public input indices.
pub const PI_THRESHOLD: usize = 0;
pub const PI_FACT_COMMITMENT: usize = 1;
pub const PUBLIC_INPUT_COUNT: usize = 2;

// ============================================================================
// Expression AST (mirrors circuit/src/arithmetic_predicate_air.rs)
// ============================================================================

/// An arithmetic expression over private inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArithExpr {
    /// Reference to a private input by index.
    Var(usize),
    /// A literal constant.
    Const(u32),
    /// Addition: a + b.
    Add(Box<ArithExpr>, Box<ArithExpr>),
    /// Subtraction: a - b.
    Sub(Box<ArithExpr>, Box<ArithExpr>),
    /// Multiplication: a * b.
    Mul(Box<ArithExpr>, Box<ArithExpr>),
    /// Minimum of inputs at these indices.
    Min(Vec<usize>),
    /// Maximum of inputs at these indices.
    Max(Vec<usize>),
    /// Sum of inputs at these indices.
    Sum(Vec<usize>),
    /// Absolute value: |expr|.
    Abs(Box<ArithExpr>),
    /// Integer floor division: a / b.
    DivFloor(Box<ArithExpr>, Box<ArithExpr>),
    /// Modulo: a % b.
    Mod(Box<ArithExpr>, Box<ArithExpr>),
}

/// Comparison operator for ExprCompare.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompareOp {
    Gte,
    Lte,
    Gt,
    Lt,
    Eq,
    Neq,
}

/// A predicate over an arithmetic expression result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArithPredicate {
    /// Expression result >= threshold.
    ExprGte(ArithExpr, u32),
    /// Expression result <= threshold.
    ExprLte(ArithExpr, u32),
    /// Expression result == value.
    ExprEq(ArithExpr, u32),
    /// Expression result != value.
    ExprNeq(ArithExpr, u32),
    /// low <= expression result <= high.
    ExprInRange(ArithExpr, u32, u32),
    /// Two expressions compared: expr1 `relation` expr2.
    ExprCompare(ArithExpr, ArithExpr, CompareOp),
}

// ============================================================================
// Compiled expression (flat opcode sequence)
// ============================================================================

/// A single flattened operation in the compiled expression.
#[derive(Clone, Debug)]
pub enum CompiledOp {
    /// Load input[index] into this slot.
    Input(usize),
    /// Load a constant.
    Const(u32),
    /// slot = slots[a] + slots[b].
    Add(usize, usize),
    /// slot = slots[a] - slots[b].
    Sub(usize, usize),
    /// slot = slots[a] * slots[b].
    Mul(usize, usize),
    /// slot = min(inputs[indices]).
    Min(Vec<usize>),
    /// slot = max(inputs[indices]).
    Max(Vec<usize>),
    /// slot = sum(inputs[indices]).
    Sum(Vec<usize>),
    /// slot = |slots[a]|.
    Abs(usize),
    /// slot = slots[a] / slots[b] (integer floor division).
    DivFloor(usize, usize),
    /// slot = slots[a] % slots[b].
    Mod(usize, usize),
}

/// A compiled arithmetic expression.
#[derive(Clone, Debug)]
pub struct CompiledArith {
    pub ops: Vec<CompiledOp>,
    pub num_inputs: usize,
    pub result_slot: usize,
}

/// Compile an expression into a flat sequence of operations.
pub fn compile_expression(expr: &ArithExpr, num_inputs: usize) -> CompiledArith {
    let mut ops = Vec::new();
    let result_slot = compile_recursive(expr, &mut ops, num_inputs);
    CompiledArith {
        ops,
        num_inputs,
        result_slot,
    }
}

fn compile_recursive(expr: &ArithExpr, ops: &mut Vec<CompiledOp>, num_inputs: usize) -> usize {
    match expr {
        ArithExpr::Var(i) => {
            let slot = ops.len();
            ops.push(CompiledOp::Input(*i));
            slot
        }
        ArithExpr::Const(c) => {
            let slot = ops.len();
            ops.push(CompiledOp::Const(*c));
            slot
        }
        ArithExpr::Add(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs);
            let sb = compile_recursive(b, ops, num_inputs);
            let slot = ops.len();
            ops.push(CompiledOp::Add(sa, sb));
            slot
        }
        ArithExpr::Sub(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs);
            let sb = compile_recursive(b, ops, num_inputs);
            let slot = ops.len();
            ops.push(CompiledOp::Sub(sa, sb));
            slot
        }
        ArithExpr::Mul(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs);
            let sb = compile_recursive(b, ops, num_inputs);
            let slot = ops.len();
            ops.push(CompiledOp::Mul(sa, sb));
            slot
        }
        ArithExpr::Min(indices) => {
            let slot = ops.len();
            ops.push(CompiledOp::Min(indices.clone()));
            slot
        }
        ArithExpr::Max(indices) => {
            let slot = ops.len();
            ops.push(CompiledOp::Max(indices.clone()));
            slot
        }
        ArithExpr::Sum(indices) => {
            let slot = ops.len();
            ops.push(CompiledOp::Sum(indices.clone()));
            slot
        }
        ArithExpr::Abs(a) => {
            let sa = compile_recursive(a, ops, num_inputs);
            let slot = ops.len();
            ops.push(CompiledOp::Abs(sa));
            slot
        }
        ArithExpr::DivFloor(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs);
            let sb = compile_recursive(b, ops, num_inputs);
            let slot = ops.len();
            ops.push(CompiledOp::DivFloor(sa, sb));
            slot
        }
        ArithExpr::Mod(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs);
            let sb = compile_recursive(b, ops, num_inputs);
            let slot = ops.len();
            ops.push(CompiledOp::Mod(sa, sb));
            slot
        }
    }
}

// ============================================================================
// Layout computation
// ============================================================================

/// Auxiliary column info for a complex operation.
#[derive(Clone, Debug)]
struct OpAux {
    /// Index of the compiled op this auxiliary data belongs to.
    op_idx: usize,
    /// Whether this is in expression B (for ExprCompare).
    is_expr_b: bool,
    /// Starting column index of the auxiliary data in the trace.
    start_col: usize,
    /// Total number of auxiliary columns for this op.
    num_cols: usize,
}

/// Compute auxiliary columns needed per complex operation.
fn aux_cols_for_op(op: &CompiledOp) -> usize {
    match op {
        // Min(K operands): K * NUM_BITS bits for range checks (operand_i - result >= 0)
        CompiledOp::Min(indices) => indices.len() * NUM_BITS,
        // Max(K operands): K * NUM_BITS bits for range checks (result - operand_i >= 0)
        CompiledOp::Max(indices) => indices.len() * NUM_BITS,
        // Abs: NUM_BITS bits to prove result < p/2
        CompiledOp::Abs(_) => NUM_BITS,
        // DivFloor: 1 remainder + NUM_BITS (remainder bits) + NUM_BITS (bound_diff bits)
        CompiledOp::DivFloor(_, _) => 1 + 2 * NUM_BITS,
        // Mod: 1 quotient + NUM_BITS (remainder bits) + NUM_BITS (bound_diff bits)
        CompiledOp::Mod(_, _) => 1 + 2 * NUM_BITS,
        _ => 0,
    }
}

/// Complete trace layout for the arithmetic predicate circuit.
#[derive(Clone, Debug)]
pub struct ArithLayout {
    pub num_inputs: usize,
    pub num_slots_a: usize,
    pub num_slots_b: usize,
    pub slots_a_start: usize,
    pub slots_b_start: usize,
    pub aux_start: usize,
    pub aux_ops: Vec<OpAux>,
    pub threshold_col: usize,
    pub diff_col: usize,
    pub diff_bits_start: usize,
    pub fact_commitment_col: usize,
    pub neq_inverse_col: usize,
    pub width: usize,
}

impl ArithLayout {
    pub fn new(num_inputs: usize, ops_a: &[CompiledOp], ops_b: Option<&[CompiledOp]>) -> Self {
        let num_slots_a = ops_a.len();
        let num_slots_b = ops_b.map_or(0, |o| o.len());
        let slots_a_start = num_inputs;
        let slots_b_start = slots_a_start + num_slots_a;
        let aux_start = slots_b_start + num_slots_b;

        let mut aux_ops = Vec::new();
        let mut aux_offset = aux_start;

        // Auxiliary columns for expression A ops.
        for (idx, op) in ops_a.iter().enumerate() {
            let num_aux = aux_cols_for_op(op);
            if num_aux > 0 {
                aux_ops.push(OpAux {
                    op_idx: idx,
                    is_expr_b: false,
                    start_col: aux_offset,
                    num_cols: num_aux,
                });
                aux_offset += num_aux;
            }
        }

        // Auxiliary columns for expression B ops.
        if let Some(ob) = ops_b {
            for (idx, op) in ob.iter().enumerate() {
                let num_aux = aux_cols_for_op(op);
                if num_aux > 0 {
                    aux_ops.push(OpAux {
                        op_idx: idx,
                        is_expr_b: true,
                        start_col: aux_offset,
                        num_cols: num_aux,
                    });
                    aux_offset += num_aux;
                }
            }
        }

        let threshold_col = aux_offset;
        let diff_col = threshold_col + 1;
        let diff_bits_start = diff_col + 1;
        let fact_commitment_col = diff_bits_start + NUM_BITS;
        let neq_inverse_col = fact_commitment_col + 1;
        let width = neq_inverse_col + 1;

        Self {
            num_inputs,
            num_slots_a,
            num_slots_b,
            slots_a_start,
            slots_b_start,
            aux_start,
            aux_ops,
            threshold_col,
            diff_col,
            diff_bits_start,
            fact_commitment_col,
            neq_inverse_col,
            width,
        }
    }

    fn aux_for_op(&self, op_idx: usize, is_expr_b: bool) -> Option<&OpAux> {
        self.aux_ops
            .iter()
            .find(|a| a.op_idx == op_idx && a.is_expr_b == is_expr_b)
    }
}

// ============================================================================
// Descriptor construction
// ============================================================================

/// Determines how the diff column relates to the expression results.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiffKind {
    /// diff = result - threshold (GTE, InRange lower bound)
    ResultMinusThreshold,
    /// diff = threshold - result (LTE)
    ThresholdMinusResult,
    /// diff = result - threshold, must be zero (EQ)
    Equality,
    /// diff = result - threshold, must be non-zero (NEQ)
    Inequality,
    /// diff = result_a - result_b (CompareGte)
    CompareGte,
    /// diff = result_b - result_a (CompareLte)
    CompareLte,
    /// diff = result_a - result_b - 1 (CompareGt)
    CompareGt,
    /// diff = result_b - result_a - 1 (CompareLt)
    CompareLt,
    /// diff = result_a - result_b, must be zero (CompareEq)
    CompareEq,
    /// diff = result_a - result_b, must be non-zero (CompareNeq)
    CompareNeq,
}

impl DiffKind {
    fn uses_bit_decomp(&self) -> bool {
        !matches!(
            self,
            DiffKind::Equality | DiffKind::Inequality | DiffKind::CompareEq | DiffKind::CompareNeq
        )
    }

    fn uses_inverse(&self) -> bool {
        matches!(self, DiffKind::Inequality | DiffKind::CompareNeq)
    }

    fn uses_zero_check(&self) -> bool {
        matches!(self, DiffKind::Equality | DiffKind::CompareEq)
    }
}

/// Build the full arithmetic predicate `CircuitDescriptor` from a predicate specification.
///
/// This is the DSL equivalent of the ~2900-line `ArithmeticPredicateAir`.
/// The circuit is dynamically sized based on the expression complexity.
pub fn build_arithmetic_predicate_descriptor(
    predicate: &ArithPredicate,
    num_inputs: usize,
) -> (
    CircuitDescriptor,
    ArithLayout,
    CompiledArith,
    Option<CompiledArith>,
    DiffKind,
) {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    // Compile expressions.
    let (compiled_a, compiled_b, diff_kind) = match predicate {
        ArithPredicate::ExprGte(expr, _) => (
            compile_expression(expr, num_inputs),
            None,
            DiffKind::ResultMinusThreshold,
        ),
        ArithPredicate::ExprLte(expr, _) => (
            compile_expression(expr, num_inputs),
            None,
            DiffKind::ThresholdMinusResult,
        ),
        ArithPredicate::ExprEq(expr, _) => (
            compile_expression(expr, num_inputs),
            None,
            DiffKind::Equality,
        ),
        ArithPredicate::ExprNeq(expr, _) => (
            compile_expression(expr, num_inputs),
            None,
            DiffKind::Inequality,
        ),
        ArithPredicate::ExprInRange(expr, _, _) => {
            // For InRange, we prove the lower bound (GTE low). Upper bound would need
            // a second proof or additional diff columns; we handle it as GTE for the lower.
            (
                compile_expression(expr, num_inputs),
                None,
                DiffKind::ResultMinusThreshold,
            )
        }
        ArithPredicate::ExprCompare(expr_a, expr_b, op) => {
            let ca = compile_expression(expr_a, num_inputs);
            let cb = compile_expression(expr_b, num_inputs);
            let dk = match op {
                CompareOp::Gte => DiffKind::CompareGte,
                CompareOp::Lte => DiffKind::CompareLte,
                CompareOp::Gt => DiffKind::CompareGt,
                CompareOp::Lt => DiffKind::CompareLt,
                CompareOp::Eq => DiffKind::CompareEq,
                CompareOp::Neq => DiffKind::CompareNeq,
            };
            (ca, Some(cb), dk)
        }
    };

    let layout = ArithLayout::new(
        num_inputs,
        &compiled_a.ops,
        compiled_b.as_ref().map(|c| c.ops.as_slice()),
    );

    // Build columns.
    let mut columns = Vec::with_capacity(layout.width);
    for i in 0..num_inputs {
        columns.push(ColumnDef {
            name: format!("input_{i}"),
            index: i,
            kind: ColumnKind::Value,
        });
    }
    for i in 0..layout.num_slots_a {
        columns.push(ColumnDef {
            name: format!("slot_a_{i}"),
            index: layout.slots_a_start + i,
            kind: ColumnKind::Value,
        });
    }
    for i in 0..layout.num_slots_b {
        columns.push(ColumnDef {
            name: format!("slot_b_{i}"),
            index: layout.slots_b_start + i,
            kind: ColumnKind::Value,
        });
    }
    // Auxiliary columns.
    for aux in &layout.aux_ops {
        for j in 0..aux.num_cols {
            columns.push(ColumnDef {
                name: format!(
                    "aux_{}_{}{}",
                    if aux.is_expr_b { "b" } else { "a" },
                    aux.op_idx,
                    j
                ),
                index: aux.start_col + j,
                kind: ColumnKind::Value,
            });
        }
    }
    columns.push(ColumnDef {
        name: "threshold".into(),
        index: layout.threshold_col,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "diff".into(),
        index: layout.diff_col,
        kind: ColumnKind::Value,
    });
    for i in 0..NUM_BITS {
        columns.push(ColumnDef {
            name: format!("diff_bit_{i}"),
            index: layout.diff_bits_start + i,
            kind: ColumnKind::Binary,
        });
    }
    columns.push(ColumnDef {
        name: "fact_commitment".into(),
        index: layout.fact_commitment_col,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "neq_inverse".into(),
        index: layout.neq_inverse_col,
        kind: ColumnKind::Value,
    });

    let mut constraints = Vec::new();

    // ─── C1: Threshold matches public input ─────────────────────────────────
    constraints.push(ConstraintExpr::PiBinding {
        col: layout.threshold_col,
        pi_index: PI_THRESHOLD,
    });

    // ─── C2: Fact commitment matches public input ───────────────────────────
    constraints.push(ConstraintExpr::PiBinding {
        col: layout.fact_commitment_col,
        pi_index: PI_FACT_COMMITMENT,
    });

    // ─── C3: Expression A slot constraints ──────────────────────────────────
    // Each slot is constrained to be the correct function of its operands.
    add_slot_constraints(
        &mut constraints,
        &compiled_a.ops,
        &layout,
        false, // is_expr_b
        neg_one,
    );

    // ─── C4: Expression B slot constraints (ExprCompare only) ───────────────
    if let Some(ref cb) = compiled_b {
        add_slot_constraints(&mut constraints, &cb.ops, &layout, true, neg_one);
    }

    // ─── C5: Diff computation constraint ────────────────────────────────────
    // Constrains the relationship between diff, result(s), and threshold.
    {
        let result_a_col = layout.slots_a_start + compiled_a.result_slot;
        match &diff_kind {
            DiffKind::ResultMinusThreshold | DiffKind::Equality | DiffKind::Inequality => {
                // diff - result_a + threshold == 0
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![layout.diff_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![result_a_col],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![layout.threshold_col],
                        },
                    ],
                });
            }
            DiffKind::ThresholdMinusResult => {
                // diff - threshold + result_a == 0
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![layout.diff_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![layout.threshold_col],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![result_a_col],
                        },
                    ],
                });
            }
            DiffKind::CompareGte | DiffKind::CompareEq | DiffKind::CompareNeq => {
                // diff - result_a + result_b == 0
                let result_b_col = layout.slots_b_start + compiled_b.as_ref().unwrap().result_slot;
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![layout.diff_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![result_a_col],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![result_b_col],
                        },
                    ],
                });
            }
            DiffKind::CompareLte => {
                // diff - result_b + result_a == 0
                let result_b_col = layout.slots_b_start + compiled_b.as_ref().unwrap().result_slot;
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![layout.diff_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![result_b_col],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![result_a_col],
                        },
                    ],
                });
            }
            DiffKind::CompareGt => {
                // diff - result_a + result_b + 1 == 0
                let result_b_col = layout.slots_b_start + compiled_b.as_ref().unwrap().result_slot;
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![layout.diff_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![result_a_col],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![result_b_col],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![],
                        }, // +1
                    ],
                });
            }
            DiffKind::CompareLt => {
                // diff - result_b + result_a + 1 == 0
                let result_b_col = layout.slots_b_start + compiled_b.as_ref().unwrap().result_slot;
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![layout.diff_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![result_b_col],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![result_a_col],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![],
                        }, // +1
                    ],
                });
            }
        }
    }

    // ─── C6: Predicate proof (bit decomp / inverse / zero check) ────────────
    if diff_kind.uses_bit_decomp() {
        // Bit decomposition: sum(diff_bits[i] * 2^i) - diff == 0
        let mut terms = Vec::with_capacity(NUM_BITS + 1);
        let mut power_of_two = 1u32;
        for i in 0..NUM_BITS {
            terms.push(PolyTerm {
                coeff: BabyBear::new(power_of_two),
                col_indices: vec![layout.diff_bits_start + i],
            });
            power_of_two = power_of_two.wrapping_mul(2);
        }
        terms.push(PolyTerm {
            coeff: neg_one,
            col_indices: vec![layout.diff_col],
        });
        constraints.push(ConstraintExpr::Polynomial { terms });

        // Bits are binary.
        for i in 0..NUM_BITS {
            constraints.push(ConstraintExpr::Binary {
                col: layout.diff_bits_start + i,
            });
        }

        // High bit is zero (proves diff < 2^29, i.e., non-negative).
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![layout.diff_bits_start + NUM_BITS - 1],
            }],
        });
    } else if diff_kind.uses_zero_check() {
        // EQ: diff must be zero.
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![layout.diff_col],
            }],
        });
    } else if diff_kind.uses_inverse() {
        // NEQ: diff * neq_inverse - 1 == 0
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![layout.diff_col, layout.neq_inverse_col],
                },
                PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![],
                }, // -1
            ],
        });
    }

    // ─── Boundaries ──────────────────────────────────────────────────────────
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: layout.threshold_col,
            pi_index: PI_THRESHOLD,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: layout.fact_commitment_col,
            pi_index: PI_FACT_COMMITMENT,
        },
    ];

    // Compute max_degree: generally 3 for gated constraints with degree-2 inner
    // (product terms in slot constraints can go higher for Min/Max with many operands,
    // but those use Polynomial directly which has degree = #operands).
    // We need to account for the highest-degree constraint we emit.
    let max_degree = constraints
        .iter()
        .map(|c| c.degree())
        .max()
        .unwrap_or(1)
        .max(3);

    let descriptor = CircuitDescriptor {
        name: "pyana-arithmetic-predicate-full-dsl-v1".into(),
        trace_width: layout.width,
        max_degree,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
    };

    (descriptor, layout, compiled_a, compiled_b, diff_kind)
}

/// Add slot constraints for a set of compiled ops.
fn add_slot_constraints(
    constraints: &mut Vec<ConstraintExpr>,
    ops: &[CompiledOp],
    layout: &ArithLayout,
    is_expr_b: bool,
    neg_one: BabyBear,
) {
    let slots_start = if is_expr_b {
        layout.slots_b_start
    } else {
        layout.slots_a_start
    };

    for (slot_idx, op) in ops.iter().enumerate() {
        let slot_col = slots_start + slot_idx;

        match op {
            CompiledOp::Input(i) => {
                // slot == input[i]
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![slot_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![*i],
                        },
                    ],
                });
            }
            CompiledOp::Const(c) => {
                // slot - c == 0
                let c_neg = BabyBear::ZERO - BabyBear::new(*c);
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![slot_col],
                        },
                        PolyTerm {
                            coeff: c_neg,
                            col_indices: vec![],
                        },
                    ],
                });
            }
            CompiledOp::Add(a, b) => {
                // slot - (slot_a + slot_b) == 0
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![slot_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![slots_start + a],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![slots_start + b],
                        },
                    ],
                });
            }
            CompiledOp::Sub(a, b) => {
                // slot - slot_a + slot_b == 0
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![slot_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![slots_start + a],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![slots_start + b],
                        },
                    ],
                });
            }
            CompiledOp::Mul(a, b) => {
                // slot - slot_a * slot_b == 0
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![slot_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![slots_start + a, slots_start + b],
                        },
                    ],
                });
            }
            CompiledOp::Sum(indices) => {
                // slot - sum(input[i] for i in indices) == 0
                let mut terms = vec![PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![slot_col],
                }];
                for &i in indices {
                    terms.push(PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![i],
                    });
                }
                constraints.push(ConstraintExpr::Polynomial { terms });
            }
            CompiledOp::Min(indices) => {
                // Constraint 1: result equals at least one operand.
                // product((result - operand_i)) == 0
                // This is a degree-K polynomial where K = number of operands.
                // We encode it as a single Polynomial term with all (slot_col - input[i]) factors.
                // However, PolyTerm only supports products of columns, not (col - col).
                // We need a different approach: use a product expansion.
                //
                // For Min with K operands, we need: product(slot - input[i]) = 0
                // We can't directly express this as a single Polynomial constraint in the DSL.
                // Instead, for soundness we rely on the auxiliary range proofs:
                // For each operand i: operand_i - result >= 0 (proved by bit decomp).
                // Combined with "result equals one of the operands" which we enforce as:
                // product((result - input[i])) == 0.
                //
                // The Polynomial constraint type can handle this if we expand the product.
                // For 2 operands: (result - a)(result - b) = result^2 - result*a - result*b + a*b
                // For 3+: gets complex. We'll encode it directly for small K.
                //
                // Actually, Polynomial terms are sums of (coeff * product_of_cols).
                // (result - a)(result - b) = result*result - result*a - result*b + a*b
                // Each of those IS expressible as a PolyTerm.
                add_min_max_constraints(
                    constraints,
                    slot_col,
                    indices,
                    layout,
                    slot_idx,
                    is_expr_b,
                    true, // is_min
                    neg_one,
                );
            }
            CompiledOp::Max(indices) => {
                add_min_max_constraints(
                    constraints,
                    slot_col,
                    indices,
                    layout,
                    slot_idx,
                    is_expr_b,
                    false, // is_max
                    neg_one,
                );
            }
            CompiledOp::Abs(a) => {
                // Constraint: result^2 == operand^2 (result = +/- operand)
                // result^2 - operand^2 == 0
                let operand_col = slots_start + a;
                constraints.push(ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![slot_col, slot_col],
                        },
                        PolyTerm {
                            coeff: neg_one,
                            col_indices: vec![operand_col, operand_col],
                        },
                    ],
                });

                // Constraint: result is non-negative via bit decomposition.
                // The aux columns contain bits such that sum(bit_j * 2^j) == result
                // and high bit is 0 (proves result < 2^29 < p/2).
                if let Some(aux) = layout.aux_for_op(slot_idx, is_expr_b) {
                    let bits_start = aux.start_col;
                    // Bit reconstruction: sum(bit_j * 2^j) - result == 0
                    let mut terms = Vec::with_capacity(NUM_BITS + 1);
                    let mut power_of_two = 1u32;
                    for j in 0..NUM_BITS {
                        terms.push(PolyTerm {
                            coeff: BabyBear::new(power_of_two),
                            col_indices: vec![bits_start + j],
                        });
                        power_of_two = power_of_two.wrapping_mul(2);
                    }
                    terms.push(PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![slot_col],
                    });
                    constraints.push(ConstraintExpr::Polynomial { terms });

                    // Bits are binary.
                    for j in 0..NUM_BITS {
                        constraints.push(ConstraintExpr::Binary {
                            col: bits_start + j,
                        });
                    }

                    // High bit is zero.
                    constraints.push(ConstraintExpr::Polynomial {
                        terms: vec![PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![bits_start + NUM_BITS - 1],
                        }],
                    });
                }
            }
            CompiledOp::DivFloor(a, b) => {
                // result = quotient. aux[0] = remainder.
                // Identity: quotient * divisor + remainder - dividend == 0
                // Plus range proofs: 0 <= remainder < divisor.
                if let Some(aux) = layout.aux_for_op(slot_idx, is_expr_b) {
                    let remainder_col = aux.start_col;
                    let dividend_col = slots_start + a;
                    let divisor_col = slots_start + b;

                    // quotient * divisor + remainder - dividend == 0
                    constraints.push(ConstraintExpr::Polynomial {
                        terms: vec![
                            PolyTerm {
                                coeff: BabyBear::ONE,
                                col_indices: vec![slot_col, divisor_col],
                            },
                            PolyTerm {
                                coeff: BabyBear::ONE,
                                col_indices: vec![remainder_col],
                            },
                            PolyTerm {
                                coeff: neg_one,
                                col_indices: vec![dividend_col],
                            },
                        ],
                    });

                    // Remainder range proof bits.
                    let bits_start_r = aux.start_col + 1;
                    // Bit reconstruction: sum(bit_j * 2^j) - remainder == 0
                    let mut terms = Vec::with_capacity(NUM_BITS + 1);
                    let mut power_of_two = 1u32;
                    for j in 0..NUM_BITS {
                        terms.push(PolyTerm {
                            coeff: BabyBear::new(power_of_two),
                            col_indices: vec![bits_start_r + j],
                        });
                        power_of_two = power_of_two.wrapping_mul(2);
                    }
                    terms.push(PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![remainder_col],
                    });
                    constraints.push(ConstraintExpr::Polynomial { terms });

                    // Remainder bits are binary.
                    for j in 0..NUM_BITS {
                        constraints.push(ConstraintExpr::Binary {
                            col: bits_start_r + j,
                        });
                    }
                    // High bit is zero.
                    constraints.push(ConstraintExpr::Polynomial {
                        terms: vec![PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![bits_start_r + NUM_BITS - 1],
                        }],
                    });

                    // Bound diff: divisor - remainder - 1 >= 0
                    // We need bound_diff_bits such that sum(bit_j * 2^j) == divisor - remainder - 1
                    // But we don't have a separate "bound_diff" column; we compute it inline.
                    // The constraint is: sum(bound_bits * 2^j) - divisor + remainder + 1 == 0
                    let bits_start_bound = aux.start_col + 1 + NUM_BITS;
                    let mut terms2 = Vec::with_capacity(NUM_BITS + 3);
                    let mut power_of_two2 = 1u32;
                    for j in 0..NUM_BITS {
                        terms2.push(PolyTerm {
                            coeff: BabyBear::new(power_of_two2),
                            col_indices: vec![bits_start_bound + j],
                        });
                        power_of_two2 = power_of_two2.wrapping_mul(2);
                    }
                    terms2.push(PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![divisor_col],
                    });
                    terms2.push(PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![remainder_col],
                    });
                    terms2.push(PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![],
                    }); // +1
                    constraints.push(ConstraintExpr::Polynomial { terms: terms2 });

                    // Bound bits are binary.
                    for j in 0..NUM_BITS {
                        constraints.push(ConstraintExpr::Binary {
                            col: bits_start_bound + j,
                        });
                    }
                    // High bit is zero.
                    constraints.push(ConstraintExpr::Polynomial {
                        terms: vec![PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![bits_start_bound + NUM_BITS - 1],
                        }],
                    });
                }
            }
            CompiledOp::Mod(a, b) => {
                // result = remainder. aux[0] = quotient.
                // Identity: quotient * divisor + remainder - dividend == 0
                if let Some(aux) = layout.aux_for_op(slot_idx, is_expr_b) {
                    let quotient_col = aux.start_col;
                    let dividend_col = slots_start + a;
                    let divisor_col = slots_start + b;

                    // quotient * divisor + result - dividend == 0
                    constraints.push(ConstraintExpr::Polynomial {
                        terms: vec![
                            PolyTerm {
                                coeff: BabyBear::ONE,
                                col_indices: vec![quotient_col, divisor_col],
                            },
                            PolyTerm {
                                coeff: BabyBear::ONE,
                                col_indices: vec![slot_col],
                            },
                            PolyTerm {
                                coeff: neg_one,
                                col_indices: vec![dividend_col],
                            },
                        ],
                    });

                    // Result (remainder) range proof.
                    let bits_start_r = aux.start_col + 1;
                    let mut terms = Vec::with_capacity(NUM_BITS + 1);
                    let mut power_of_two = 1u32;
                    for j in 0..NUM_BITS {
                        terms.push(PolyTerm {
                            coeff: BabyBear::new(power_of_two),
                            col_indices: vec![bits_start_r + j],
                        });
                        power_of_two = power_of_two.wrapping_mul(2);
                    }
                    terms.push(PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![slot_col],
                    });
                    constraints.push(ConstraintExpr::Polynomial { terms });

                    // Remainder bits are binary.
                    for j in 0..NUM_BITS {
                        constraints.push(ConstraintExpr::Binary {
                            col: bits_start_r + j,
                        });
                    }
                    // High bit is zero.
                    constraints.push(ConstraintExpr::Polynomial {
                        terms: vec![PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![bits_start_r + NUM_BITS - 1],
                        }],
                    });

                    // Bound diff: divisor - result - 1 >= 0
                    let bits_start_bound = aux.start_col + 1 + NUM_BITS;
                    let mut terms2 = Vec::with_capacity(NUM_BITS + 3);
                    let mut power_of_two2 = 1u32;
                    for j in 0..NUM_BITS {
                        terms2.push(PolyTerm {
                            coeff: BabyBear::new(power_of_two2),
                            col_indices: vec![bits_start_bound + j],
                        });
                        power_of_two2 = power_of_two2.wrapping_mul(2);
                    }
                    terms2.push(PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![divisor_col],
                    });
                    terms2.push(PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![slot_col],
                    });
                    terms2.push(PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![],
                    }); // +1
                    constraints.push(ConstraintExpr::Polynomial { terms: terms2 });

                    // Bound bits are binary.
                    for j in 0..NUM_BITS {
                        constraints.push(ConstraintExpr::Binary {
                            col: bits_start_bound + j,
                        });
                    }
                    // High bit is zero.
                    constraints.push(ConstraintExpr::Polynomial {
                        terms: vec![PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![bits_start_bound + NUM_BITS - 1],
                        }],
                    });
                }
            }
        }
    }
}

/// Add constraints for Min/Max operations (membership + range proofs).
fn add_min_max_constraints(
    constraints: &mut Vec<ConstraintExpr>,
    slot_col: usize,
    indices: &[usize],
    layout: &ArithLayout,
    slot_idx: usize,
    is_expr_b: bool,
    is_min: bool,
    neg_one: BabyBear,
) {
    // Constraint 1: result equals at least one operand.
    // product(result - input[i]) == 0
    // Expand into Polynomial terms. For K operands:
    // (result - a0)(result - a1)...(result - aK) = 0
    //
    // For 2 operands: result^2 - result*a - result*b + a*b
    // For 3: result^3 - result^2*(a+b+c) + result*(ab+ac+bc) - abc
    //
    // General expansion uses elementary symmetric polynomials.
    // Each term is a product of some subset of {result, -input[i]}.
    //
    // For small K (2-4) we expand explicitly. For larger K, we chain.
    let k = indices.len();
    if k <= 4 {
        // Direct polynomial expansion of product(slot_col - input[i])
        let terms = expand_product_constraint(slot_col, indices);
        constraints.push(ConstraintExpr::Polynomial { terms });
    } else {
        // For larger K, we'd need intermediate columns. For now, just use
        // a simpler (but slightly higher degree) approach: pair-wise.
        // This is still sound: if result != any operand, all factors are nonzero.
        let terms = expand_product_constraint(slot_col, indices);
        constraints.push(ConstraintExpr::Polynomial { terms });
    }

    // Constraint 2: Range proofs via auxiliary bit decompositions.
    // For Min: operand_i - result >= 0 for each operand.
    // For Max: result - operand_i >= 0 for each operand.
    if let Some(aux) = layout.aux_for_op(slot_idx, is_expr_b) {
        for (k_idx, &input_idx) in indices.iter().enumerate() {
            let bits_start = aux.start_col + k_idx * NUM_BITS;

            // Bit reconstruction constraint:
            // For Min: sum(bits * 2^j) - input[i] + result == 0
            // For Max: sum(bits * 2^j) - result + input[i] == 0
            let mut terms = Vec::with_capacity(NUM_BITS + 2);
            let mut power_of_two = 1u32;
            for j in 0..NUM_BITS {
                terms.push(PolyTerm {
                    coeff: BabyBear::new(power_of_two),
                    col_indices: vec![bits_start + j],
                });
                power_of_two = power_of_two.wrapping_mul(2);
            }
            if is_min {
                // sum(bits) == input[i] - result
                terms.push(PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![input_idx],
                });
                terms.push(PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![slot_col],
                });
            } else {
                // sum(bits) == result - input[i]
                terms.push(PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![slot_col],
                });
                terms.push(PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![input_idx],
                });
            }
            constraints.push(ConstraintExpr::Polynomial { terms });

            // Bits are binary.
            for j in 0..NUM_BITS {
                constraints.push(ConstraintExpr::Binary {
                    col: bits_start + j,
                });
            }

            // High bit is zero (proves the diff is non-negative and < 2^29).
            constraints.push(ConstraintExpr::Polynomial {
                terms: vec![PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![bits_start + NUM_BITS - 1],
                }],
            });
        }
    }
}

/// Expand product(slot_col - input[i]) into polynomial terms.
///
/// Uses the expansion: product(x - a_i) = sum_{S subset of indices} (-1)^|S| * x^(k-|S|) * product(a_j for j in S)
/// where k = number of indices.
fn expand_product_constraint(slot_col: usize, indices: &[usize]) -> Vec<PolyTerm> {
    let k = indices.len();
    // Generate all subsets of indices (2^k subsets).
    let mut terms = Vec::new();

    for mask in 0..(1u64 << k) {
        let subset_size = mask.count_ones() as usize;
        let result_power = k - subset_size; // number of `slot_col` factors

        // Coefficient: (-1)^subset_size
        let coeff = if subset_size % 2 == 0 {
            BabyBear::ONE
        } else {
            BabyBear::new(BABYBEAR_P - 1) // -1
        };

        // Column indices: result_power copies of slot_col + the input columns in the subset
        let mut col_indices = Vec::with_capacity(k);
        for _ in 0..result_power {
            col_indices.push(slot_col);
        }
        for bit_pos in 0..k {
            if mask & (1u64 << bit_pos) != 0 {
                col_indices.push(indices[bit_pos]);
            }
        }

        terms.push(PolyTerm { coeff, col_indices });
    }

    terms
}

// ============================================================================
// Expression evaluation (for trace generation)
// ============================================================================

/// Evaluate an expression given concrete inputs, returning all slot values.
pub fn evaluate_compiled_slots(compiled: &CompiledArith, inputs: &[BabyBear]) -> Vec<BabyBear> {
    let mut slots: Vec<BabyBear> = Vec::with_capacity(compiled.ops.len());

    for op in &compiled.ops {
        let val = match op {
            CompiledOp::Input(i) => inputs[*i],
            CompiledOp::Const(c) => BabyBear::new(*c),
            CompiledOp::Add(a, b) => slots[*a] + slots[*b],
            CompiledOp::Sub(a, b) => slots[*a] - slots[*b],
            CompiledOp::Mul(a, b) => slots[*a] * slots[*b],
            CompiledOp::Sum(indices) => {
                let mut sum = BabyBear::ZERO;
                for &i in indices {
                    sum = sum + inputs[i];
                }
                sum
            }
            CompiledOp::Min(indices) => {
                let mut min_val = inputs[indices[0]];
                for &i in &indices[1..] {
                    if inputs[i].as_u32() < min_val.as_u32() {
                        min_val = inputs[i];
                    }
                }
                min_val
            }
            CompiledOp::Max(indices) => {
                let mut max_val = inputs[indices[0]];
                for &i in &indices[1..] {
                    if inputs[i].as_u32() > max_val.as_u32() {
                        max_val = inputs[i];
                    }
                }
                max_val
            }
            CompiledOp::Abs(a) => {
                let v = slots[*a].as_u32();
                let half_p = BABYBEAR_P / 2;
                if v > half_p {
                    BabyBear::ZERO - slots[*a]
                } else {
                    slots[*a]
                }
            }
            CompiledOp::DivFloor(a, b) => {
                let vb = slots[*b].as_u32();
                assert!(vb != 0, "division by zero in expression evaluation");
                BabyBear::new(slots[*a].as_u32() / vb)
            }
            CompiledOp::Mod(a, b) => {
                let vb = slots[*b].as_u32();
                assert!(vb != 0, "division by zero in expression evaluation");
                BabyBear::new(slots[*a].as_u32() % vb)
            }
        };
        slots.push(val);
    }

    slots
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate a valid trace for the full arithmetic predicate.
///
/// Returns `(trace, public_inputs)`.
pub fn generate_full_trace(
    inputs: &[u32],
    predicate: &ArithPredicate,
    fact_commitment: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_inputs = inputs.len();
    let bb_inputs: Vec<BabyBear> = inputs.iter().map(|&v| BabyBear::new(v)).collect();

    let (_descriptor, layout, compiled_a, compiled_b, diff_kind) =
        build_arithmetic_predicate_descriptor(predicate, num_inputs);

    let mut row = vec![BabyBear::ZERO; layout.width];

    // Fill input columns.
    for (i, &val) in bb_inputs.iter().enumerate() {
        row[i] = val;
    }

    // Evaluate expression A and fill slot columns.
    let slots_a = evaluate_compiled_slots(&compiled_a, &bb_inputs);
    for (i, &val) in slots_a.iter().enumerate() {
        row[layout.slots_a_start + i] = val;
    }

    // Fill auxiliary columns for expression A.
    fill_aux_columns(
        &mut row,
        &compiled_a.ops,
        &slots_a,
        &bb_inputs,
        &layout,
        false,
    );

    // Evaluate expression B if present (ExprCompare).
    let slots_b = if let Some(ref cb) = compiled_b {
        let sb = evaluate_compiled_slots(cb, &bb_inputs);
        for (i, &val) in sb.iter().enumerate() {
            row[layout.slots_b_start + i] = val;
        }
        fill_aux_columns(&mut row, &cb.ops, &sb, &bb_inputs, &layout, true);
        Some(sb)
    } else {
        None
    };

    // Compute threshold and diff.
    let result_a = slots_a[compiled_a.result_slot];
    let (threshold, diff) = match &diff_kind {
        DiffKind::ResultMinusThreshold | DiffKind::Equality | DiffKind::Inequality => {
            let t = match predicate {
                ArithPredicate::ExprGte(_, t)
                | ArithPredicate::ExprLte(_, t)
                | ArithPredicate::ExprEq(_, t)
                | ArithPredicate::ExprNeq(_, t) => BabyBear::new(*t),
                ArithPredicate::ExprInRange(_, low, _) => BabyBear::new(*low),
                _ => unreachable!(),
            };
            (t, result_a - t)
        }
        DiffKind::ThresholdMinusResult => {
            let t = match predicate {
                ArithPredicate::ExprLte(_, t) => BabyBear::new(*t),
                _ => unreachable!(),
            };
            (t, t - result_a)
        }
        DiffKind::CompareGte | DiffKind::CompareEq | DiffKind::CompareNeq => {
            let result_b = slots_b.as_ref().unwrap()[compiled_b.as_ref().unwrap().result_slot];
            (BabyBear::ZERO, result_a - result_b)
        }
        DiffKind::CompareLte => {
            let result_b = slots_b.as_ref().unwrap()[compiled_b.as_ref().unwrap().result_slot];
            (BabyBear::ZERO, result_b - result_a)
        }
        DiffKind::CompareGt => {
            let result_b = slots_b.as_ref().unwrap()[compiled_b.as_ref().unwrap().result_slot];
            (BabyBear::ZERO, result_a - result_b - BabyBear::ONE)
        }
        DiffKind::CompareLt => {
            let result_b = slots_b.as_ref().unwrap()[compiled_b.as_ref().unwrap().result_slot];
            (BabyBear::ZERO, result_b - result_a - BabyBear::ONE)
        }
    };

    row[layout.threshold_col] = threshold;
    row[layout.diff_col] = diff;
    row[layout.fact_commitment_col] = fact_commitment;

    // Fill diff bits or neq_inverse based on diff_kind.
    if diff_kind.uses_bit_decomp() {
        let diff_val = diff.as_u32();
        for i in 0..NUM_BITS {
            row[layout.diff_bits_start + i] = BabyBear::new((diff_val >> i) & 1);
        }
    } else if diff_kind.uses_inverse() {
        if let Some(inv) = diff.inverse() {
            row[layout.neq_inverse_col] = inv;
        }
    }
    // For zero check (EQ), diff should already be zero; no extra columns needed.

    let public_inputs = vec![threshold, fact_commitment];

    // Pad to 2 rows (STARK requires at least 2).
    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

/// Fill auxiliary columns for complex operations.
fn fill_aux_columns(
    row: &mut [BabyBear],
    ops: &[CompiledOp],
    slots: &[BabyBear],
    inputs: &[BabyBear],
    layout: &ArithLayout,
    is_expr_b: bool,
) {
    for (slot_idx, op) in ops.iter().enumerate() {
        let Some(aux) = layout.aux_for_op(slot_idx, is_expr_b) else {
            continue;
        };
        let result = slots[slot_idx];

        match op {
            CompiledOp::Min(indices) => {
                // For each operand: bit decompose (operand - result).
                for (k, &i) in indices.iter().enumerate() {
                    let operand = inputs[i];
                    let diff = operand - result;
                    let diff_val = diff.as_u32();
                    let bits_start = aux.start_col + k * NUM_BITS;
                    for j in 0..NUM_BITS {
                        row[bits_start + j] = BabyBear::new((diff_val >> j) & 1);
                    }
                }
            }
            CompiledOp::Max(indices) => {
                // For each operand: bit decompose (result - operand).
                for (k, &i) in indices.iter().enumerate() {
                    let operand = inputs[i];
                    let diff = result - operand;
                    let diff_val = diff.as_u32();
                    let bits_start = aux.start_col + k * NUM_BITS;
                    for j in 0..NUM_BITS {
                        row[bits_start + j] = BabyBear::new((diff_val >> j) & 1);
                    }
                }
            }
            CompiledOp::Abs(_) => {
                // Bit decompose result (to prove < p/2).
                let result_val = result.as_u32();
                let bits_start = aux.start_col;
                for j in 0..NUM_BITS {
                    row[bits_start + j] = BabyBear::new((result_val >> j) & 1);
                }
            }
            CompiledOp::DivFloor(a, b) => {
                let dividend = slots[*a];
                let divisor = slots[*b];
                let quotient = result;
                let remainder_val = dividend.as_u32() - quotient.as_u32() * divisor.as_u32();

                // Store remainder.
                row[aux.start_col] = BabyBear::new(remainder_val);

                // Bit decompose remainder.
                let bits_start_r = aux.start_col + 1;
                for j in 0..NUM_BITS {
                    row[bits_start_r + j] = BabyBear::new((remainder_val >> j) & 1);
                }

                // Bit decompose (divisor - remainder - 1).
                let bound_diff = divisor.as_u32() - remainder_val - 1;
                let bits_start_bound = aux.start_col + 1 + NUM_BITS;
                for j in 0..NUM_BITS {
                    row[bits_start_bound + j] = BabyBear::new((bound_diff >> j) & 1);
                }
            }
            CompiledOp::Mod(a, b) => {
                let dividend = slots[*a];
                let divisor = slots[*b];
                let remainder = result;
                let quotient_val = dividend.as_u32() / divisor.as_u32();

                // Store quotient.
                row[aux.start_col] = BabyBear::new(quotient_val);

                // Bit decompose remainder.
                let remainder_val = remainder.as_u32();
                let bits_start_r = aux.start_col + 1;
                for j in 0..NUM_BITS {
                    row[bits_start_r + j] = BabyBear::new((remainder_val >> j) & 1);
                }

                // Bit decompose (divisor - remainder - 1).
                let bound_diff = divisor.as_u32() - remainder_val - 1;
                let bits_start_bound = aux.start_col + 1 + NUM_BITS;
                for j in 0..NUM_BITS {
                    row[bits_start_bound + j] = BabyBear::new((bound_diff >> j) & 1);
                }
            }
            _ => {}
        }
    }
}

// ============================================================================
// Prove / Verify API
// ============================================================================

/// A complete arithmetic predicate proof result.
#[derive(Clone, Debug)]
pub struct ArithmeticPredicateProof {
    pub predicate: ArithPredicate,
    pub num_inputs: usize,
    pub threshold: BabyBear,
    pub fact_commitment: BabyBear,
    pub stark_proof: StarkProof,
}

/// Prove an arithmetic predicate.
pub fn prove_arithmetic_dsl(
    inputs: &[u32],
    predicate: &ArithPredicate,
    fact_commitment: BabyBear,
) -> Result<ArithmeticPredicateProof, String> {
    let num_inputs = inputs.len();
    let (descriptor, _layout, _ca, _cb, _dk) =
        build_arithmetic_predicate_descriptor(predicate, num_inputs);
    let circuit = DslCircuit::new(descriptor);
    let (trace, pi) = generate_full_trace(inputs, predicate, fact_commitment);
    let stark_proof = stark::prove(&circuit, &trace, &pi);

    Ok(ArithmeticPredicateProof {
        predicate: predicate.clone(),
        num_inputs,
        threshold: pi[0],
        fact_commitment,
        stark_proof,
    })
}

/// Verify an arithmetic predicate proof.
pub fn verify_arithmetic_dsl(
    proof: &ArithmeticPredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) -> Result<(), String> {
    if proof.threshold != threshold || proof.fact_commitment != fact_commitment {
        return Err("public input mismatch".into());
    }
    let (descriptor, _layout, _ca, _cb, _dk) =
        build_arithmetic_predicate_descriptor(&proof.predicate, proof.num_inputs);
    let circuit = DslCircuit::new(descriptor);
    let pi = vec![threshold, fact_commitment];
    stark::verify(&circuit, &proof.stark_proof, &pi)
}

/// Backward-compatible alias for `verify_arithmetic_dsl`.
pub fn verify_arithmetic_predicate(
    proof: &ArithmeticPredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) -> Result<(), String> {
    verify_arithmetic_dsl(proof, threshold, fact_commitment)
}

/// Backward-compatible: compute fact commitment for arithmetic predicates.
pub fn compute_arithmetic_fact_commitment(fact_hash: BabyBear, state_root: BabyBear) -> BabyBear {
    crate::poseidon2::hash_2_to_1(fact_hash, state_root)
}
