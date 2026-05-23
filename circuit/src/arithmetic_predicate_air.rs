//! Arithmetic predicate AIR: proves arbitrary arithmetic expressions over private inputs.
//!
//! Extends the predicate system beyond single comparisons to support expressions like:
//! - `balance_a + balance_b >= 2000` (joint qualification)
//! - `(revenue - costs) * margin >= min_profit` (complex financial predicates)
//! - `min(a, b, c) >= threshold` (worst-case guarantees)
//! - `max(a, b) - min(a, b) <= spread` (value proximity / spread checks)
//!
//! # Design
//!
//! The `ArithmeticPredicateAir` flattens an arithmetic expression AST into a linear
//! sequence of operations. Each operation gets its own column in the trace, constrained
//! to be the correct function of its operands. The final column holds the expression
//! result, which is then range-checked against a threshold using the same
//! bit-decomposition technique as [`PredicateAir`](crate::predicate_air).
//!
//! # Trace Layout
//!
//! | Columns        | Description                                          |
//! |----------------|------------------------------------------------------|
//! | 0..N-1         | input values (private witness)                       |
//! | N..N+M-1       | intermediate computation columns (one per AST node)  |
//! | N+M-1          | expression result (also the last intermediate)       |
//! | N+M            | threshold (public comparison target)                 |
//! | N+M+1          | diff (result - threshold for GTE, etc.)              |
//! | N+M+2..N+M+33  | diff_bits[0..31] (bit decomposition of diff)         |
//! | N+M+33         | fact_commitment (binding to token state)              |
//!
//! # Limits
//!
//! Maximum 32 operations per expression (trace columns grow linearly with expression size).
//!
//! # Public Inputs
//!
//! `[threshold, fact_commitment]`

use crate::constraint_prover::{Air, Constraint};
use crate::field::BabyBear;
use crate::poseidon2;
use crate::predicate_air::PREDICATE_DIFF_BITS;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Maximum number of operations in a compiled expression.
pub const MAX_ARITHMETIC_OPS: usize = 32;

/// An arithmetic expression over private inputs.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ArithExpr {
    /// Reference to a private input by index.
    Var(usize),
    /// A literal constant.
    Const(BabyBear),

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

/// A predicate over an arithmetic expression result.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ArithPredicate {
    /// Expression result >= threshold.
    ExprGte(ArithExpr, BabyBear),
    /// Expression result <= threshold.
    ExprLte(ArithExpr, BabyBear),
    /// Expression result == value.
    ExprEq(ArithExpr, BabyBear),
    /// Expression result != value (inequality).
    /// Proved by witnessing the multiplicative inverse of (result - value).
    ExprNeq(ArithExpr, BabyBear),
    /// low <= expression result <= high.
    ExprInRange(ArithExpr, BabyBear, BabyBear),
    /// Two expressions compared: expr1 `relation` expr2.
    ExprCompare(ArithExpr, ArithExpr, CompareOp),
}

/// Comparison operator for ExprCompare.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CompareOp {
    Gte,
    Lte,
    Gt,
    Lt,
    Eq,
    Neq,
}

/// A single flattened operation in the compiled expression.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum CompiledOp {
    /// Load input[index] into this slot.
    Input(usize),
    /// Load a constant into this slot.
    Const(BabyBear),
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
    /// slot = |slots[a]| (absolute value via conditional negation).
    Abs(usize),
    /// slot = slots[a] / slots[b] (integer floor division).
    /// Also stores remainder slot index for constraint: quotient * b + remainder = a.
    DivFloor(usize, usize),
    /// slot = slots[a] % slots[b] (remainder from floor division).
    Mod(usize, usize),
}

/// A compiled arithmetic expression: flattened into a linear sequence of operations.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CompiledArith {
    /// The operations in evaluation order.
    pub ops: Vec<CompiledOp>,
    /// The number of private inputs required.
    pub num_inputs: usize,
    /// Index of the final result in the ops/slots vector.
    pub result_slot: usize,
}

impl ArithExpr {
    /// Count the number of unique input variables referenced.
    pub fn max_input_index(&self) -> Option<usize> {
        match self {
            ArithExpr::Var(i) => Some(*i),
            ArithExpr::Const(_) => None,
            ArithExpr::Add(a, b)
            | ArithExpr::Sub(a, b)
            | ArithExpr::Mul(a, b)
            | ArithExpr::DivFloor(a, b)
            | ArithExpr::Mod(a, b) => {
                let ma = a.max_input_index();
                let mb = b.max_input_index();
                match (ma, mb) {
                    (Some(a), Some(b)) => Some(a.max(b)),
                    (Some(a), None) => Some(a),
                    (None, Some(b)) => Some(b),
                    (None, None) => None,
                }
            }
            ArithExpr::Min(indices) | ArithExpr::Max(indices) | ArithExpr::Sum(indices) => {
                indices.iter().max().copied()
            }
            ArithExpr::Abs(a) => a.max_input_index(),
        }
    }

    /// Count the total number of AST nodes (operations).
    pub fn node_count(&self) -> usize {
        match self {
            ArithExpr::Var(_) | ArithExpr::Const(_) => 1,
            ArithExpr::Add(a, b)
            | ArithExpr::Sub(a, b)
            | ArithExpr::Mul(a, b)
            | ArithExpr::DivFloor(a, b)
            | ArithExpr::Mod(a, b) => 1 + a.node_count() + b.node_count(),
            ArithExpr::Min(_) | ArithExpr::Max(_) | ArithExpr::Sum(_) => 1,
            ArithExpr::Abs(a) => 1 + a.node_count(),
        }
    }
}

/// Compile an expression into a flat sequence of operations.
///
/// Returns `None` if the expression exceeds `MAX_ARITHMETIC_OPS`.
pub fn compile_expression(expr: &ArithExpr, num_inputs: usize) -> Option<CompiledArith> {
    let mut ops = Vec::new();
    let result_slot = compile_recursive(expr, &mut ops, num_inputs)?;
    if ops.len() > MAX_ARITHMETIC_OPS {
        return None;
    }
    Some(CompiledArith {
        ops,
        num_inputs,
        result_slot,
    })
}

/// Recursively compile an expression, returning the slot index of the result.
fn compile_recursive(
    expr: &ArithExpr,
    ops: &mut Vec<CompiledOp>,
    num_inputs: usize,
) -> Option<usize> {
    if ops.len() >= MAX_ARITHMETIC_OPS {
        return None;
    }
    match expr {
        ArithExpr::Var(i) => {
            if *i >= num_inputs {
                return None;
            }
            let slot = ops.len();
            ops.push(CompiledOp::Input(*i));
            Some(slot)
        }
        ArithExpr::Const(c) => {
            let slot = ops.len();
            ops.push(CompiledOp::Const(*c));
            Some(slot)
        }
        ArithExpr::Add(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs)?;
            let sb = compile_recursive(b, ops, num_inputs)?;
            let slot = ops.len();
            ops.push(CompiledOp::Add(sa, sb));
            Some(slot)
        }
        ArithExpr::Sub(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs)?;
            let sb = compile_recursive(b, ops, num_inputs)?;
            let slot = ops.len();
            ops.push(CompiledOp::Sub(sa, sb));
            Some(slot)
        }
        ArithExpr::Mul(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs)?;
            let sb = compile_recursive(b, ops, num_inputs)?;
            let slot = ops.len();
            ops.push(CompiledOp::Mul(sa, sb));
            Some(slot)
        }
        ArithExpr::Min(indices) => {
            for &i in indices {
                if i >= num_inputs {
                    return None;
                }
            }
            let slot = ops.len();
            ops.push(CompiledOp::Min(indices.clone()));
            Some(slot)
        }
        ArithExpr::Max(indices) => {
            for &i in indices {
                if i >= num_inputs {
                    return None;
                }
            }
            let slot = ops.len();
            ops.push(CompiledOp::Max(indices.clone()));
            Some(slot)
        }
        ArithExpr::Sum(indices) => {
            for &i in indices {
                if i >= num_inputs {
                    return None;
                }
            }
            let slot = ops.len();
            ops.push(CompiledOp::Sum(indices.clone()));
            Some(slot)
        }
        ArithExpr::Abs(a) => {
            let sa = compile_recursive(a, ops, num_inputs)?;
            let slot = ops.len();
            ops.push(CompiledOp::Abs(sa));
            Some(slot)
        }
        ArithExpr::DivFloor(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs)?;
            let sb = compile_recursive(b, ops, num_inputs)?;
            let slot = ops.len();
            ops.push(CompiledOp::DivFloor(sa, sb));
            Some(slot)
        }
        ArithExpr::Mod(a, b) => {
            let sa = compile_recursive(a, ops, num_inputs)?;
            let sb = compile_recursive(b, ops, num_inputs)?;
            let slot = ops.len();
            ops.push(CompiledOp::Mod(sa, sb));
            Some(slot)
        }
    }
}

/// Evaluate an arithmetic expression given concrete inputs.
///
/// Returns `None` if the expression references out-of-bounds inputs or
/// division by zero occurs.
pub fn evaluate_expression(expr: &ArithExpr, inputs: &[BabyBear]) -> Option<BabyBear> {
    match expr {
        ArithExpr::Var(i) => inputs.get(*i).copied(),
        ArithExpr::Const(c) => Some(*c),
        ArithExpr::Add(a, b) => {
            let va = evaluate_expression(a, inputs)?;
            let vb = evaluate_expression(b, inputs)?;
            Some(va + vb)
        }
        ArithExpr::Sub(a, b) => {
            let va = evaluate_expression(a, inputs)?;
            let vb = evaluate_expression(b, inputs)?;
            Some(va - vb)
        }
        ArithExpr::Mul(a, b) => {
            let va = evaluate_expression(a, inputs)?;
            let vb = evaluate_expression(b, inputs)?;
            Some(va * vb)
        }
        ArithExpr::Min(indices) => {
            if indices.is_empty() {
                return None;
            }
            let mut min_val = inputs.get(*indices.first()?)?;
            for &i in &indices[1..] {
                let v = inputs.get(i)?;
                if v.as_u32() < min_val.as_u32() {
                    min_val = v;
                }
            }
            Some(*min_val)
        }
        ArithExpr::Max(indices) => {
            if indices.is_empty() {
                return None;
            }
            let mut max_val = inputs.get(*indices.first()?)?;
            for &i in &indices[1..] {
                let v = inputs.get(i)?;
                if v.as_u32() > max_val.as_u32() {
                    max_val = v;
                }
            }
            Some(*max_val)
        }
        ArithExpr::Sum(indices) => {
            let mut sum = BabyBear::ZERO;
            for &i in indices {
                sum = sum + *inputs.get(i)?;
            }
            Some(sum)
        }
        ArithExpr::Abs(a) => {
            let va = evaluate_expression(a, inputs)?;
            // In BabyBear, "negative" means val > p/2.
            // Abs maps those to p - val.
            let v = va.as_u32();
            let half_p = crate::field::BABYBEAR_P / 2;
            if v > half_p {
                // Negative: negate it.
                Some(BabyBear::ZERO - va)
            } else {
                Some(va)
            }
        }
        ArithExpr::DivFloor(a, b) => {
            let va = evaluate_expression(a, inputs)?;
            let vb = evaluate_expression(b, inputs)?;
            if vb.as_u32() == 0 {
                return None; // Division by zero.
            }
            // Integer floor division on the u32 representations.
            Some(BabyBear::new(va.as_u32() / vb.as_u32()))
        }
        ArithExpr::Mod(a, b) => {
            let va = evaluate_expression(a, inputs)?;
            let vb = evaluate_expression(b, inputs)?;
            if vb.as_u32() == 0 {
                return None; // Division by zero.
            }
            Some(BabyBear::new(va.as_u32() % vb.as_u32()))
        }
    }
}

/// Evaluate a compiled expression against concrete slot values (for use in trace generation).
fn evaluate_compiled(compiled: &CompiledArith, inputs: &[BabyBear]) -> Option<Vec<BabyBear>> {
    let mut slots: Vec<BabyBear> = Vec::with_capacity(compiled.ops.len());

    for op in &compiled.ops {
        let val = match op {
            CompiledOp::Input(i) => *inputs.get(*i)?,
            CompiledOp::Const(c) => *c,
            CompiledOp::Add(a, b) => slots[*a] + slots[*b],
            CompiledOp::Sub(a, b) => slots[*a] - slots[*b],
            CompiledOp::Mul(a, b) => slots[*a] * slots[*b],
            CompiledOp::Min(indices) => {
                let mut min_val = *inputs.get(*indices.first()?)?;
                for &i in &indices[1..] {
                    let v = *inputs.get(i)?;
                    if v.as_u32() < min_val.as_u32() {
                        min_val = v;
                    }
                }
                min_val
            }
            CompiledOp::Max(indices) => {
                let mut max_val = *inputs.get(*indices.first()?)?;
                for &i in &indices[1..] {
                    let v = *inputs.get(i)?;
                    if v.as_u32() > max_val.as_u32() {
                        max_val = v;
                    }
                }
                max_val
            }
            CompiledOp::Sum(indices) => {
                let mut sum = BabyBear::ZERO;
                for &i in indices {
                    sum = sum + *inputs.get(i)?;
                }
                sum
            }
            CompiledOp::Abs(a) => {
                let v = slots[*a].as_u32();
                let half_p = crate::field::BABYBEAR_P / 2;
                if v > half_p {
                    BabyBear::ZERO - slots[*a]
                } else {
                    slots[*a]
                }
            }
            CompiledOp::DivFloor(a, b) => {
                let vb = slots[*b].as_u32();
                if vb == 0 {
                    return None;
                }
                BabyBear::new(slots[*a].as_u32() / vb)
            }
            CompiledOp::Mod(a, b) => {
                let vb = slots[*b].as_u32();
                if vb == 0 {
                    return None;
                }
                BabyBear::new(slots[*a].as_u32() % vb)
            }
        };
        slots.push(val);
    }

    Some(slots)
}

/// Witness for an arithmetic predicate proof.
#[derive(Clone, Debug)]
pub struct ArithmeticPredicateWitness {
    /// The private input values.
    pub inputs: Vec<BabyBear>,
    /// The arithmetic predicate to prove.
    pub predicate: ArithPredicate,
    /// Fact commitment: Poseidon2(fact_hash, state_root).
    /// Binds this proof to a specific fact in a specific token state.
    pub fact_commitment: BabyBear,
}

impl ArithmeticPredicateWitness {
    /// Check whether the predicate is satisfiable (the statement is true).
    pub fn is_satisfiable(&self) -> bool {
        match &self.predicate {
            ArithPredicate::ExprGte(expr, threshold) => {
                let Some(result) = evaluate_expression(expr, &self.inputs) else {
                    return false;
                };
                result.as_u32() >= threshold.as_u32()
            }
            ArithPredicate::ExprLte(expr, threshold) => {
                let Some(result) = evaluate_expression(expr, &self.inputs) else {
                    return false;
                };
                result.as_u32() <= threshold.as_u32()
            }
            ArithPredicate::ExprEq(expr, value) => {
                let Some(result) = evaluate_expression(expr, &self.inputs) else {
                    return false;
                };
                result == *value
            }
            ArithPredicate::ExprNeq(expr, value) => {
                let Some(result) = evaluate_expression(expr, &self.inputs) else {
                    return false;
                };
                result != *value
            }
            ArithPredicate::ExprInRange(expr, low, high) => {
                let Some(result) = evaluate_expression(expr, &self.inputs) else {
                    return false;
                };
                result.as_u32() >= low.as_u32() && result.as_u32() <= high.as_u32()
            }
            ArithPredicate::ExprCompare(expr_a, expr_b, op) => {
                let Some(result_a) = evaluate_expression(expr_a, &self.inputs) else {
                    return false;
                };
                let Some(result_b) = evaluate_expression(expr_b, &self.inputs) else {
                    return false;
                };
                match op {
                    CompareOp::Gte => result_a.as_u32() >= result_b.as_u32(),
                    CompareOp::Lte => result_a.as_u32() <= result_b.as_u32(),
                    CompareOp::Gt => result_a.as_u32() > result_b.as_u32(),
                    CompareOp::Lt => result_a.as_u32() < result_b.as_u32(),
                    CompareOp::Eq => result_a == result_b,
                    CompareOp::Neq => result_a != result_b,
                }
            }
        }
    }

    /// Get the expression from the predicate.
    fn expression(&self) -> &ArithExpr {
        match &self.predicate {
            ArithPredicate::ExprGte(expr, _)
            | ArithPredicate::ExprLte(expr, _)
            | ArithPredicate::ExprEq(expr, _)
            | ArithPredicate::ExprNeq(expr, _)
            | ArithPredicate::ExprInRange(expr, _, _) => expr,
            ArithPredicate::ExprCompare(expr, _, _) => expr,
        }
    }
}

/// The arithmetic predicate proof AIR.
///
/// Proves an arithmetic expression over private inputs satisfies a comparison predicate.
pub struct ArithmeticPredicateAir {
    pub witness: ArithmeticPredicateWitness,
    /// Compiled expression (cached for constraint generation).
    compiled: CompiledArith,
    /// For ExprCompare, the second compiled expression.
    compiled_b: Option<CompiledArith>,
}

/// Describes auxiliary columns needed to verify a single complex operation.
#[derive(Clone, Debug)]
struct OpAux {
    /// Index of the compiled op this auxiliary data belongs to.
    op_idx: usize,
    /// Starting column index of the auxiliary data in the trace.
    start_col: usize,
    /// Total number of auxiliary columns for this op.
    num_cols: usize,
}

/// Compute the number of auxiliary columns needed per complex operation.
fn aux_cols_for_op(op: &CompiledOp) -> usize {
    match op {
        // Min(K operands): K range-check proofs (K * PREDICATE_DIFF_BITS bits)
        // to verify operand_i - result >= 0 for each operand.
        CompiledOp::Min(indices) => indices.len() * PREDICATE_DIFF_BITS,
        // Max(K operands): K range-check proofs (K * PREDICATE_DIFF_BITS bits)
        // to verify result - operand_i >= 0 for each operand.
        CompiledOp::Max(indices) => indices.len() * PREDICATE_DIFF_BITS,
        // Abs(a): PREDICATE_DIFF_BITS bits for range-checking that result < p/2
        // (i.e., result is non-negative).
        CompiledOp::Abs(_) => PREDICATE_DIFF_BITS,
        // DivFloor(a, b): 1 remainder column + PREDICATE_DIFF_BITS bits for
        // remainder >= 0 + PREDICATE_DIFF_BITS bits for b - remainder - 1 >= 0.
        CompiledOp::DivFloor(_, _) => 1 + 2 * PREDICATE_DIFF_BITS,
        // Mod(a, b): 1 quotient column + PREDICATE_DIFF_BITS bits for
        // result >= 0 + PREDICATE_DIFF_BITS bits for b - result - 1 >= 0.
        CompiledOp::Mod(_, _) => 1 + 2 * PREDICATE_DIFF_BITS,
        _ => 0,
    }
}

/// Column layout helper for the arithmetic predicate AIR.
#[derive(Clone, Debug)]
struct ArithLayout {
    /// Number of private inputs.
    num_inputs: usize,
    /// Number of intermediate computation slots.
    num_slots: usize,
    /// Number of slots for the second expression (ExprCompare only).
    num_slots_b: usize,
    /// Start column for computation slots.
    slots_start: usize,
    /// Start column for second expression slots (ExprCompare only).
    slots_b_start: usize,
    /// Start column for auxiliary data.
    aux_start: usize,
    /// Auxiliary column info for each complex op.
    aux_ops: Vec<OpAux>,
    /// Total auxiliary columns.
    num_aux_cols: usize,
    /// Column for the threshold/comparison target.
    threshold_col: usize,
    /// Column for the diff value.
    diff_col: usize,
    /// Start column for diff bits.
    diff_bits_start: usize,
    /// Column for fact commitment.
    fact_commitment_col: usize,
    /// Column for NEQ inverse witness (only used for Inequality/CompareNeq).
    neq_inverse_col: usize,
    /// Total trace width.
    width: usize,
}

impl ArithLayout {
    fn new(num_inputs: usize, ops: &[CompiledOp], ops_b: Option<&[CompiledOp]>) -> Self {
        let num_slots = ops.len();
        let num_slots_b = ops_b.map_or(0, |o| o.len());
        let slots_start = num_inputs;
        let slots_b_start = slots_start + num_slots;
        let aux_start = slots_b_start + num_slots_b;

        // Compute auxiliary column allocation for ops in expression A.
        let mut aux_ops = Vec::new();
        let mut aux_offset = aux_start;
        for (idx, op) in ops.iter().enumerate() {
            let num_aux = aux_cols_for_op(op);
            if num_aux > 0 {
                aux_ops.push(OpAux {
                    op_idx: idx,
                    start_col: aux_offset,
                    num_cols: num_aux,
                });
                aux_offset += num_aux;
            }
        }
        // Also handle ops_b auxiliary columns.
        if let Some(ob) = ops_b {
            for (idx, op) in ob.iter().enumerate() {
                let num_aux = aux_cols_for_op(op);
                if num_aux > 0 {
                    // Use num_slots + idx to distinguish from ops_a indices.
                    aux_ops.push(OpAux {
                        op_idx: num_slots + idx,
                        start_col: aux_offset,
                        num_cols: num_aux,
                    });
                    aux_offset += num_aux;
                }
            }
        }

        let num_aux_cols = aux_offset - aux_start;
        let threshold_col = aux_offset;
        let diff_col = threshold_col + 1;
        let diff_bits_start = diff_col + 1;
        let fact_commitment_col = diff_bits_start + PREDICATE_DIFF_BITS;
        let neq_inverse_col = fact_commitment_col + 1;
        let width = neq_inverse_col + 1;

        Self {
            num_inputs,
            num_slots,
            num_slots_b,
            slots_start,
            slots_b_start,
            aux_start,
            aux_ops,
            num_aux_cols,
            threshold_col,
            diff_col,
            diff_bits_start,
            fact_commitment_col,
            neq_inverse_col,
            width,
        }
    }

    fn diff_bit_col(&self, i: usize) -> usize {
        self.diff_bits_start + i
    }

    /// Get the OpAux for a given slot index in expression A, or None.
    fn aux_for_op(&self, op_idx: usize) -> Option<&OpAux> {
        self.aux_ops.iter().find(|a| a.op_idx == op_idx)
    }
}

impl ArithmeticPredicateAir {
    /// Create a new arithmetic predicate AIR.
    ///
    /// Returns `None` if the expression is too large or references invalid inputs.
    pub fn new(witness: ArithmeticPredicateWitness) -> Option<Self> {
        let num_inputs = witness.inputs.len();

        let compiled = match &witness.predicate {
            ArithPredicate::ExprGte(expr, _)
            | ArithPredicate::ExprLte(expr, _)
            | ArithPredicate::ExprEq(expr, _)
            | ArithPredicate::ExprNeq(expr, _)
            | ArithPredicate::ExprInRange(expr, _, _) => compile_expression(expr, num_inputs)?,
            ArithPredicate::ExprCompare(expr_a, _, _) => compile_expression(expr_a, num_inputs)?,
        };

        let compiled_b = match &witness.predicate {
            ArithPredicate::ExprCompare(_, expr_b, _) => {
                Some(compile_expression(expr_b, num_inputs)?)
            }
            _ => None,
        };

        Some(Self {
            witness,
            compiled,
            compiled_b,
        })
    }

    fn layout(&self) -> ArithLayout {
        let ops_b = self.compiled_b.as_ref().map(|c| c.ops.as_slice());
        ArithLayout::new(self.witness.inputs.len(), &self.compiled.ops, ops_b)
    }
}

/// Fill auxiliary columns in the trace row for expression A's complex operations.
fn fill_aux_columns(
    row: &mut [BabyBear],
    ops: &[CompiledOp],
    slots: &[BabyBear],
    inputs: &[BabyBear],
    _slots_start: usize,
    layout: &ArithLayout,
) {
    for (slot_idx, op) in ops.iter().enumerate() {
        let Some(aux) = layout.aux_for_op(slot_idx) else {
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
                    let bits_start = aux.start_col + k * PREDICATE_DIFF_BITS;
                    for j in 0..PREDICATE_DIFF_BITS {
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
                    let bits_start = aux.start_col + k * PREDICATE_DIFF_BITS;
                    for j in 0..PREDICATE_DIFF_BITS {
                        row[bits_start + j] = BabyBear::new((diff_val >> j) & 1);
                    }
                }
            }
            CompiledOp::Abs(_) => {
                // Bit decompose result itself (to prove it's < p/2).
                let result_val = result.as_u32();
                let bits_start = aux.start_col;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start + j] = BabyBear::new((result_val >> j) & 1);
                }
            }
            CompiledOp::DivFloor(a, b) => {
                // remainder = dividend - quotient * divisor
                let dividend = slots[*a];
                let divisor = slots[*b];
                let quotient = result; // DivFloor result IS the quotient.
                let remainder_val = dividend.as_u32() - quotient.as_u32() * divisor.as_u32();
                let remainder = BabyBear::new(remainder_val);

                // Store remainder.
                row[aux.start_col] = remainder;

                // Bit decompose remainder (to prove >= 0).
                let bits_start_r = aux.start_col + 1;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start_r + j] = BabyBear::new((remainder_val >> j) & 1);
                }

                // Bit decompose (divisor - remainder - 1) to prove remainder < divisor.
                let bound_diff = divisor.as_u32() - remainder_val - 1;
                let bits_start_bound = aux.start_col + 1 + PREDICATE_DIFF_BITS;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start_bound + j] = BabyBear::new((bound_diff >> j) & 1);
                }
            }
            CompiledOp::Mod(a, b) => {
                // quotient = dividend / divisor (floor)
                let dividend = slots[*a];
                let divisor = slots[*b];
                let remainder = result; // Mod result IS the remainder.
                let quotient_val = dividend.as_u32() / divisor.as_u32();

                // Store quotient.
                row[aux.start_col] = BabyBear::new(quotient_val);

                // Bit decompose remainder (to prove >= 0).
                let remainder_val = remainder.as_u32();
                let bits_start_r = aux.start_col + 1;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start_r + j] = BabyBear::new((remainder_val >> j) & 1);
                }

                // Bit decompose (divisor - remainder - 1) to prove remainder < divisor.
                let bound_diff = divisor.as_u32() - remainder_val - 1;
                let bits_start_bound = aux.start_col + 1 + PREDICATE_DIFF_BITS;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start_bound + j] = BabyBear::new((bound_diff >> j) & 1);
                }
            }
            _ => {}
        }
    }
}

/// Fill auxiliary columns for expression B's complex operations.
fn fill_aux_columns_b(
    row: &mut [BabyBear],
    ops: &[CompiledOp],
    slots: &[BabyBear],
    inputs: &[BabyBear],
    _slots_start: usize,
    layout: &ArithLayout,
) {
    let num_slots_a = layout.num_slots;
    for (slot_idx, op) in ops.iter().enumerate() {
        let Some(aux) = layout.aux_for_op(num_slots_a + slot_idx) else {
            continue;
        };
        let result = slots[slot_idx];

        match op {
            CompiledOp::Min(indices) => {
                for (k, &i) in indices.iter().enumerate() {
                    let operand = inputs[i];
                    let diff = operand - result;
                    let diff_val = diff.as_u32();
                    let bits_start = aux.start_col + k * PREDICATE_DIFF_BITS;
                    for j in 0..PREDICATE_DIFF_BITS {
                        row[bits_start + j] = BabyBear::new((diff_val >> j) & 1);
                    }
                }
            }
            CompiledOp::Max(indices) => {
                for (k, &i) in indices.iter().enumerate() {
                    let operand = inputs[i];
                    let diff = result - operand;
                    let diff_val = diff.as_u32();
                    let bits_start = aux.start_col + k * PREDICATE_DIFF_BITS;
                    for j in 0..PREDICATE_DIFF_BITS {
                        row[bits_start + j] = BabyBear::new((diff_val >> j) & 1);
                    }
                }
            }
            CompiledOp::Abs(_) => {
                let result_val = result.as_u32();
                let bits_start = aux.start_col;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start + j] = BabyBear::new((result_val >> j) & 1);
                }
            }
            CompiledOp::DivFloor(a, b) => {
                let dividend = slots[*a];
                let divisor = slots[*b];
                let quotient = result;
                let remainder_val = dividend.as_u32() - quotient.as_u32() * divisor.as_u32();
                let remainder = BabyBear::new(remainder_val);
                row[aux.start_col] = remainder;
                let bits_start_r = aux.start_col + 1;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start_r + j] = BabyBear::new((remainder_val >> j) & 1);
                }
                let bound_diff = divisor.as_u32() - remainder_val - 1;
                let bits_start_bound = aux.start_col + 1 + PREDICATE_DIFF_BITS;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start_bound + j] = BabyBear::new((bound_diff >> j) & 1);
                }
            }
            CompiledOp::Mod(a, b) => {
                let dividend = slots[*a];
                let divisor = slots[*b];
                let remainder = result;
                let quotient_val = dividend.as_u32() / divisor.as_u32();
                row[aux.start_col] = BabyBear::new(quotient_val);
                let remainder_val = remainder.as_u32();
                let bits_start_r = aux.start_col + 1;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start_r + j] = BabyBear::new((remainder_val >> j) & 1);
                }
                let bound_diff = divisor.as_u32() - remainder_val - 1;
                let bits_start_bound = aux.start_col + 1 + PREDICATE_DIFF_BITS;
                for j in 0..PREDICATE_DIFF_BITS {
                    row[bits_start_bound + j] = BabyBear::new((bound_diff >> j) & 1);
                }
            }
            _ => {}
        }
    }
}

impl Air for ArithmeticPredicateAir {
    fn trace_width(&self) -> usize {
        self.layout().width
    }

    fn num_public_inputs(&self) -> usize {
        2 // [threshold, fact_commitment]
    }

    fn constraints(&self) -> Vec<Constraint> {
        let layout = self.layout();
        let compiled_ops = self.compiled.ops.clone();
        let compiled_b_ops = self.compiled_b.as_ref().map(|c| c.ops.clone());
        let _num_inputs = layout.num_inputs;
        let slots_start = layout.slots_start;
        let slots_b_start = layout.slots_b_start;
        let threshold_col = layout.threshold_col;
        let diff_col = layout.diff_col;
        let diff_bits_start = layout.diff_bits_start;
        let fact_commitment_col = layout.fact_commitment_col;

        // Determine the comparison type for diff computation.
        let predicate = self.witness.predicate.clone();

        vec![
            // Constraint 1: Threshold in trace matches public input.
            Constraint {
                name: "threshold_matches_public_input".to_string(),
                eval: Box::new(move |row, _, public_inputs| row[threshold_col] - public_inputs[0]),
            },
            // Constraint 2: Fact commitment in trace matches public input.
            Constraint {
                name: "fact_commitment_matches_public_input".to_string(),
                eval: {
                    let fc_col = fact_commitment_col;
                    Box::new(move |row, _, public_inputs| row[fc_col] - public_inputs[1])
                },
            },
            // Constraint 3: Each arithmetic operation is correctly computed.
            // For simple ops (Input, Const, Add, Sub, Mul, Sum): direct algebraic check.
            // For complex ops (Min, Max, Abs, DivFloor, Mod): algebraic identity checks
            // using auxiliary columns for range proofs.
            Constraint {
                name: "arithmetic_ops_correct".to_string(),
                eval: {
                    let ops = compiled_ops.clone();
                    let ss = slots_start;
                    let layout_clone = layout.clone();
                    Box::new(move |row, _, _| {
                        let mut error = BabyBear::ZERO;
                        for (slot_idx, op) in ops.iter().enumerate() {
                            let col = ss + slot_idx;
                            let actual = row[col];
                            match op {
                                CompiledOp::Input(i) => {
                                    error = error + (actual - row[*i]);
                                }
                                CompiledOp::Const(c) => {
                                    error = error + (actual - *c);
                                }
                                CompiledOp::Add(a, b) => {
                                    error = error + (actual - (row[ss + a] + row[ss + b]));
                                }
                                CompiledOp::Sub(a, b) => {
                                    error = error + (actual - (row[ss + a] - row[ss + b]));
                                }
                                CompiledOp::Mul(a, b) => {
                                    error = error + (actual - (row[ss + a] * row[ss + b]));
                                }
                                CompiledOp::Sum(indices) => {
                                    let mut sum = BabyBear::ZERO;
                                    for &i in indices {
                                        sum = sum + row[i];
                                    }
                                    error = error + (actual - sum);
                                }
                                CompiledOp::Min(indices) => {
                                    // Constraint: result equals at least one operand.
                                    // product((result - operand_i)) = 0
                                    let result = actual;
                                    let mut product = BabyBear::ONE;
                                    for &i in indices {
                                        product = product * (result - row[i]);
                                    }
                                    error = error + product;

                                    // Constraint: result <= each operand (via aux range check bits).
                                    // For each operand i: operand_i - result >= 0.
                                    // The bit decomposition of (operand_i - result) is in aux columns.
                                    if let Some(aux) = layout_clone.aux_for_op(slot_idx) {
                                        for (k, &i) in indices.iter().enumerate() {
                                            let diff = row[i] - result;
                                            let bits_start =
                                                aux.start_col + k * PREDICATE_DIFF_BITS;

                                            // Check bit decomposition: sum(bit_j * 2^j) = diff
                                            let mut recomposed = BabyBear::ZERO;
                                            let mut power = BabyBear::ONE;
                                            for j in 0..PREDICATE_DIFF_BITS {
                                                let bit = row[bits_start + j];
                                                recomposed = recomposed + bit * power;
                                                // bits binary check
                                                error = error + bit * (bit - BabyBear::ONE);
                                                power = power + power;
                                            }
                                            error = error + (recomposed - diff);
                                            // high bit must be 0 (non-negative)
                                            error =
                                                error + row[bits_start + PREDICATE_DIFF_BITS - 1];
                                        }
                                    }
                                }
                                CompiledOp::Max(indices) => {
                                    // Constraint: result equals at least one operand.
                                    let result = actual;
                                    let mut product = BabyBear::ONE;
                                    for &i in indices {
                                        product = product * (result - row[i]);
                                    }
                                    error = error + product;

                                    // Constraint: result >= each operand (via aux range check bits).
                                    // For each operand i: result - operand_i >= 0.
                                    if let Some(aux) = layout_clone.aux_for_op(slot_idx) {
                                        for (k, &i) in indices.iter().enumerate() {
                                            let diff = result - row[i];
                                            let bits_start =
                                                aux.start_col + k * PREDICATE_DIFF_BITS;

                                            let mut recomposed = BabyBear::ZERO;
                                            let mut power = BabyBear::ONE;
                                            for j in 0..PREDICATE_DIFF_BITS {
                                                let bit = row[bits_start + j];
                                                recomposed = recomposed + bit * power;
                                                error = error + bit * (bit - BabyBear::ONE);
                                                power = power + power;
                                            }
                                            error = error + (recomposed - diff);
                                            error =
                                                error + row[bits_start + PREDICATE_DIFF_BITS - 1];
                                        }
                                    }
                                }
                                CompiledOp::Abs(a) => {
                                    // Constraint: result^2 = operand^2 (result = +/- operand).
                                    let operand = row[ss + a];
                                    error = error + (actual * actual - operand * operand);

                                    // Constraint: result is non-negative (< p/2) via bit decomp.
                                    if let Some(aux) = layout_clone.aux_for_op(slot_idx) {
                                        let bits_start = aux.start_col;
                                        let mut recomposed = BabyBear::ZERO;
                                        let mut power = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start + j];
                                            recomposed = recomposed + bit * power;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power = power + power;
                                        }
                                        // Bit decomposition equals result (proves result < 2^31)
                                        error = error + (recomposed - actual);
                                        // High bit is 0 (proves result < 2^30 < p/2)
                                        error = error + row[bits_start + PREDICATE_DIFF_BITS - 1];
                                    }
                                }
                                CompiledOp::DivFloor(a, b) => {
                                    // result = quotient, slots[a] = dividend, slots[b] = divisor.
                                    // Constraint: quotient * divisor + remainder = dividend.
                                    // Also: 0 <= remainder < divisor.
                                    if let Some(aux) = layout_clone.aux_for_op(slot_idx) {
                                        let remainder_col = aux.start_col;
                                        let remainder = row[remainder_col];
                                        let dividend = row[ss + a];
                                        let divisor = row[ss + b];
                                        let quotient = actual;

                                        // Division identity: q * b + r = a
                                        error = error + (quotient * divisor + remainder - dividend);

                                        // remainder >= 0: bit decomposition of remainder
                                        let bits_start_r = aux.start_col + 1;
                                        let mut recomposed = BabyBear::ZERO;
                                        let mut power = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start_r + j];
                                            recomposed = recomposed + bit * power;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power = power + power;
                                        }
                                        error = error + (recomposed - remainder);
                                        error = error + row[bits_start_r + PREDICATE_DIFF_BITS - 1];

                                        // remainder < divisor: bit decomp of (divisor - remainder - 1)
                                        let bits_start_bound =
                                            aux.start_col + 1 + PREDICATE_DIFF_BITS;
                                        let bound_diff = divisor - remainder - BabyBear::ONE;
                                        let mut recomposed2 = BabyBear::ZERO;
                                        let mut power2 = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start_bound + j];
                                            recomposed2 = recomposed2 + bit * power2;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power2 = power2 + power2;
                                        }
                                        error = error + (recomposed2 - bound_diff);
                                        error =
                                            error + row[bits_start_bound + PREDICATE_DIFF_BITS - 1];
                                    }
                                }
                                CompiledOp::Mod(a, b) => {
                                    // result = remainder, slots[a] = dividend, slots[b] = divisor.
                                    // Constraint: quotient * divisor + result = dividend.
                                    // Also: 0 <= result < divisor.
                                    if let Some(aux) = layout_clone.aux_for_op(slot_idx) {
                                        let quotient_col = aux.start_col;
                                        let quotient = row[quotient_col];
                                        let dividend = row[ss + a];
                                        let divisor = row[ss + b];
                                        let remainder = actual;

                                        // Division identity: q * b + r = a
                                        error = error + (quotient * divisor + remainder - dividend);

                                        // result >= 0: bit decomposition of result
                                        let bits_start_r = aux.start_col + 1;
                                        let mut recomposed = BabyBear::ZERO;
                                        let mut power = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start_r + j];
                                            recomposed = recomposed + bit * power;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power = power + power;
                                        }
                                        error = error + (recomposed - remainder);
                                        error = error + row[bits_start_r + PREDICATE_DIFF_BITS - 1];

                                        // result < divisor: bit decomp of (divisor - result - 1)
                                        let bits_start_bound =
                                            aux.start_col + 1 + PREDICATE_DIFF_BITS;
                                        let bound_diff = divisor - remainder - BabyBear::ONE;
                                        let mut recomposed2 = BabyBear::ZERO;
                                        let mut power2 = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start_bound + j];
                                            recomposed2 = recomposed2 + bit * power2;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power2 = power2 + power2;
                                        }
                                        error = error + (recomposed2 - bound_diff);
                                        error =
                                            error + row[bits_start_bound + PREDICATE_DIFF_BITS - 1];
                                    }
                                }
                            }
                        }
                        error
                    })
                },
            },
            // Constraint 4: Second expression operations correct (ExprCompare only).
            Constraint {
                name: "arithmetic_ops_b_correct".to_string(),
                eval: {
                    let ops_b = compiled_b_ops.clone();
                    let sb = slots_b_start;
                    let layout_clone = layout.clone();
                    let num_slots_a = layout.num_slots;
                    Box::new(move |row, _, _| {
                        let Some(ops) = &ops_b else {
                            return BabyBear::ZERO;
                        };
                        let mut error = BabyBear::ZERO;
                        for (slot_idx, op) in ops.iter().enumerate() {
                            let col = sb + slot_idx;
                            let actual = row[col];
                            match op {
                                CompiledOp::Input(i) => {
                                    error = error + (actual - row[*i]);
                                }
                                CompiledOp::Const(c) => {
                                    error = error + (actual - *c);
                                }
                                CompiledOp::Add(a, b) => {
                                    error = error + (actual - (row[sb + a] + row[sb + b]));
                                }
                                CompiledOp::Sub(a, b) => {
                                    error = error + (actual - (row[sb + a] - row[sb + b]));
                                }
                                CompiledOp::Mul(a, b) => {
                                    error = error + (actual - (row[sb + a] * row[sb + b]));
                                }
                                CompiledOp::Sum(indices) => {
                                    let mut sum = BabyBear::ZERO;
                                    for &i in indices {
                                        sum = sum + row[i];
                                    }
                                    error = error + (actual - sum);
                                }
                                CompiledOp::Min(indices) => {
                                    let result = actual;
                                    let mut product = BabyBear::ONE;
                                    for &i in indices {
                                        product = product * (result - row[i]);
                                    }
                                    error = error + product;

                                    // Aux index for ops_b uses num_slots_a + slot_idx.
                                    if let Some(aux) =
                                        layout_clone.aux_for_op(num_slots_a + slot_idx)
                                    {
                                        for (k, &i) in indices.iter().enumerate() {
                                            let diff = row[i] - result;
                                            let bits_start =
                                                aux.start_col + k * PREDICATE_DIFF_BITS;
                                            let mut recomposed = BabyBear::ZERO;
                                            let mut power = BabyBear::ONE;
                                            for j in 0..PREDICATE_DIFF_BITS {
                                                let bit = row[bits_start + j];
                                                recomposed = recomposed + bit * power;
                                                error = error + bit * (bit - BabyBear::ONE);
                                                power = power + power;
                                            }
                                            error = error + (recomposed - diff);
                                            error =
                                                error + row[bits_start + PREDICATE_DIFF_BITS - 1];
                                        }
                                    }
                                }
                                CompiledOp::Max(indices) => {
                                    let result = actual;
                                    let mut product = BabyBear::ONE;
                                    for &i in indices {
                                        product = product * (result - row[i]);
                                    }
                                    error = error + product;

                                    if let Some(aux) =
                                        layout_clone.aux_for_op(num_slots_a + slot_idx)
                                    {
                                        for (k, &i) in indices.iter().enumerate() {
                                            let diff = result - row[i];
                                            let bits_start =
                                                aux.start_col + k * PREDICATE_DIFF_BITS;
                                            let mut recomposed = BabyBear::ZERO;
                                            let mut power = BabyBear::ONE;
                                            for j in 0..PREDICATE_DIFF_BITS {
                                                let bit = row[bits_start + j];
                                                recomposed = recomposed + bit * power;
                                                error = error + bit * (bit - BabyBear::ONE);
                                                power = power + power;
                                            }
                                            error = error + (recomposed - diff);
                                            error =
                                                error + row[bits_start + PREDICATE_DIFF_BITS - 1];
                                        }
                                    }
                                }
                                CompiledOp::Abs(a) => {
                                    let operand = row[sb + a];
                                    error = error + (actual * actual - operand * operand);
                                    if let Some(aux) =
                                        layout_clone.aux_for_op(num_slots_a + slot_idx)
                                    {
                                        let bits_start = aux.start_col;
                                        let mut recomposed = BabyBear::ZERO;
                                        let mut power = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start + j];
                                            recomposed = recomposed + bit * power;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power = power + power;
                                        }
                                        error = error + (recomposed - actual);
                                        error = error + row[bits_start + PREDICATE_DIFF_BITS - 1];
                                    }
                                }
                                CompiledOp::DivFloor(a, b) => {
                                    if let Some(aux) =
                                        layout_clone.aux_for_op(num_slots_a + slot_idx)
                                    {
                                        let remainder_col = aux.start_col;
                                        let remainder = row[remainder_col];
                                        let dividend = row[sb + a];
                                        let divisor = row[sb + b];
                                        let quotient = actual;
                                        error = error + (quotient * divisor + remainder - dividend);
                                        let bits_start_r = aux.start_col + 1;
                                        let mut recomposed = BabyBear::ZERO;
                                        let mut power = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start_r + j];
                                            recomposed = recomposed + bit * power;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power = power + power;
                                        }
                                        error = error + (recomposed - remainder);
                                        error = error + row[bits_start_r + PREDICATE_DIFF_BITS - 1];
                                        let bits_start_bound =
                                            aux.start_col + 1 + PREDICATE_DIFF_BITS;
                                        let bound_diff = divisor - remainder - BabyBear::ONE;
                                        let mut recomposed2 = BabyBear::ZERO;
                                        let mut power2 = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start_bound + j];
                                            recomposed2 = recomposed2 + bit * power2;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power2 = power2 + power2;
                                        }
                                        error = error + (recomposed2 - bound_diff);
                                        error =
                                            error + row[bits_start_bound + PREDICATE_DIFF_BITS - 1];
                                    }
                                }
                                CompiledOp::Mod(a, b) => {
                                    if let Some(aux) =
                                        layout_clone.aux_for_op(num_slots_a + slot_idx)
                                    {
                                        let quotient_col = aux.start_col;
                                        let quotient = row[quotient_col];
                                        let dividend = row[sb + a];
                                        let divisor = row[sb + b];
                                        let remainder = actual;
                                        error = error + (quotient * divisor + remainder - dividend);
                                        let bits_start_r = aux.start_col + 1;
                                        let mut recomposed = BabyBear::ZERO;
                                        let mut power = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start_r + j];
                                            recomposed = recomposed + bit * power;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power = power + power;
                                        }
                                        error = error + (recomposed - remainder);
                                        error = error + row[bits_start_r + PREDICATE_DIFF_BITS - 1];
                                        let bits_start_bound =
                                            aux.start_col + 1 + PREDICATE_DIFF_BITS;
                                        let bound_diff = divisor - remainder - BabyBear::ONE;
                                        let mut recomposed2 = BabyBear::ZERO;
                                        let mut power2 = BabyBear::ONE;
                                        for j in 0..PREDICATE_DIFF_BITS {
                                            let bit = row[bits_start_bound + j];
                                            recomposed2 = recomposed2 + bit * power2;
                                            error = error + bit * (bit - BabyBear::ONE);
                                            power2 = power2 + power2;
                                        }
                                        error = error + (recomposed2 - bound_diff);
                                        error =
                                            error + row[bits_start_bound + PREDICATE_DIFF_BITS - 1];
                                    }
                                }
                            }
                        }
                        error
                    })
                },
            },
            // Constraint 5: Diff is correctly computed based on predicate type.
            Constraint {
                name: "diff_correct".to_string(),
                eval: {
                    let pred = predicate.clone();
                    let dc = diff_col;
                    let ss = slots_start;
                    let sb = slots_b_start;
                    let compiled_a = self.compiled.clone();
                    let compiled_b_ref = self.compiled_b.clone();
                    Box::new(move |row, _, _| {
                        let diff = row[dc];
                        let result_a = row[ss + compiled_a.result_slot];
                        match &pred {
                            ArithPredicate::ExprGte(_, _) => {
                                // diff = result - threshold
                                let threshold = row[threshold_col];
                                diff - (result_a - threshold)
                            }
                            ArithPredicate::ExprLte(_, _) => {
                                // diff = threshold - result
                                let threshold = row[threshold_col];
                                diff - (threshold - result_a)
                            }
                            ArithPredicate::ExprEq(_, _) | ArithPredicate::ExprNeq(_, _) => {
                                // diff = result - threshold (must be zero for Eq, non-zero for Neq)
                                let threshold = row[threshold_col];
                                diff - (result_a - threshold)
                            }
                            ArithPredicate::ExprInRange(_, _, _) => {
                                // For InRange, we prove the lower bound (GTE).
                                // The upper bound is handled by a second AIR instance.
                                let threshold = row[threshold_col];
                                diff - (result_a - threshold)
                            }
                            ArithPredicate::ExprCompare(_, _, op) => {
                                let compiled_b = compiled_b_ref.as_ref().unwrap();
                                let result_b = row[sb + compiled_b.result_slot];
                                match op {
                                    CompareOp::Gte => diff - (result_a - result_b),
                                    CompareOp::Lte => diff - (result_b - result_a),
                                    CompareOp::Gt => diff - (result_a - result_b - BabyBear::ONE),
                                    CompareOp::Lt => diff - (result_b - result_a - BabyBear::ONE),
                                    CompareOp::Eq | CompareOp::Neq => diff - (result_a - result_b),
                                }
                            }
                        }
                    })
                },
            },
            // Constraint 6: Bit decomposition or inverse check.
            Constraint {
                name: "bit_decomposition_correct".to_string(),
                eval: {
                    let pred = predicate.clone();
                    let dc = diff_col;
                    let dbs = diff_bits_start;
                    let neq_inv_col = layout.neq_inverse_col;
                    Box::new(move |row, _, _| {
                        // For ExprEq, diff must be zero (no bit decomp needed).
                        if matches!(&pred, ArithPredicate::ExprEq(_, _)) {
                            return row[dc];
                        }
                        if matches!(&pred, ArithPredicate::ExprCompare(_, _, CompareOp::Eq)) {
                            return row[dc];
                        }
                        // For ExprNeq / CompareNeq: diff * inverse == 1.
                        if matches!(&pred, ArithPredicate::ExprNeq(_, _)) {
                            let neq_inverse = row[neq_inv_col];
                            return row[dc] * neq_inverse - BabyBear::ONE;
                        }
                        if matches!(&pred, ArithPredicate::ExprCompare(_, _, CompareOp::Neq)) {
                            let neq_inverse = row[neq_inv_col];
                            return row[dc] * neq_inverse - BabyBear::ONE;
                        }

                        let diff = row[dc];
                        let mut recomposed = BabyBear::ZERO;
                        let mut power_of_two = BabyBear::ONE;
                        for i in 0..PREDICATE_DIFF_BITS {
                            let bit = row[dbs + i];
                            recomposed = recomposed + bit * power_of_two;
                            power_of_two = power_of_two + power_of_two;
                        }
                        recomposed - diff
                    })
                },
            },
            // Constraint 7: All bits are binary (0 or 1).
            // Skipped for EQ (diff must be zero) and NEQ (uses inverse).
            Constraint {
                name: "bits_binary".to_string(),
                eval: {
                    let pred = predicate.clone();
                    let dbs = diff_bits_start;
                    Box::new(move |row, _, _| {
                        if matches!(
                            &pred,
                            ArithPredicate::ExprEq(_, _) | ArithPredicate::ExprNeq(_, _)
                        ) {
                            return BabyBear::ZERO;
                        }
                        if matches!(
                            &pred,
                            ArithPredicate::ExprCompare(_, _, CompareOp::Eq | CompareOp::Neq)
                        ) {
                            return BabyBear::ZERO;
                        }
                        let mut result = BabyBear::ZERO;
                        for i in 0..PREDICATE_DIFF_BITS {
                            let bit = row[dbs + i];
                            result = result + bit * (bit - BabyBear::ONE);
                        }
                        result
                    })
                },
            },
            // Constraint 8: High bit is 0 (diff < 2^30 < p/2, proving non-negative).
            // Skipped for EQ and NEQ.
            Constraint {
                name: "high_bit_zero".to_string(),
                eval: {
                    let pred = predicate.clone();
                    let dbs = diff_bits_start;
                    Box::new(move |row, _, _| {
                        if matches!(
                            &pred,
                            ArithPredicate::ExprEq(_, _) | ArithPredicate::ExprNeq(_, _)
                        ) {
                            return BabyBear::ZERO;
                        }
                        if matches!(
                            &pred,
                            ArithPredicate::ExprCompare(_, _, CompareOp::Eq | CompareOp::Neq)
                        ) {
                            return BabyBear::ZERO;
                        }
                        row[dbs + PREDICATE_DIFF_BITS - 1]
                    })
                },
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let layout = self.layout();
        let mut row = vec![BabyBear::ZERO; layout.width];

        // Fill input columns.
        for (i, &val) in self.witness.inputs.iter().enumerate() {
            row[i] = val;
        }

        // Evaluate compiled expression A and fill slot columns.
        let slots_a = evaluate_compiled(&self.compiled, &self.witness.inputs)
            .expect("compiled expression evaluation should succeed for satisfiable witness");
        for (i, &val) in slots_a.iter().enumerate() {
            row[layout.slots_start + i] = val;
        }

        // Fill auxiliary columns for expression A's complex operations.
        fill_aux_columns(
            &mut row,
            &self.compiled.ops,
            &slots_a,
            &self.witness.inputs,
            layout.slots_start,
            &layout,
        );

        // Evaluate compiled expression B if present (ExprCompare).
        if let Some(compiled_b) = &self.compiled_b {
            let slots_b = evaluate_compiled(compiled_b, &self.witness.inputs)
                .expect("compiled expression B evaluation should succeed");
            for (i, &val) in slots_b.iter().enumerate() {
                row[layout.slots_b_start + i] = val;
            }

            // Fill auxiliary columns for expression B's complex operations.
            fill_aux_columns_b(
                &mut row,
                &compiled_b.ops,
                &slots_b,
                &self.witness.inputs,
                layout.slots_b_start,
                &layout,
            );
        }

        // Compute the expression result.
        let result_a = slots_a[self.compiled.result_slot];

        // Determine threshold and diff based on predicate type.
        let (threshold, diff) = match &self.witness.predicate {
            ArithPredicate::ExprGte(_, t) => (*t, result_a - *t),
            ArithPredicate::ExprLte(_, t) => (*t, *t - result_a),
            ArithPredicate::ExprEq(_, v) => {
                (*v, result_a - *v) // Should be zero.
            }
            ArithPredicate::ExprNeq(_, v) => {
                (*v, result_a - *v) // Must be non-zero.
            }
            ArithPredicate::ExprInRange(_, low, _high) => {
                // Prove lower bound (GTE low).
                (*low, result_a - *low)
            }
            ArithPredicate::ExprCompare(_, _, op) => {
                let compiled_b = self.compiled_b.as_ref().unwrap();
                let slots_b = evaluate_compiled(compiled_b, &self.witness.inputs).unwrap();
                let result_b = slots_b[compiled_b.result_slot];
                let diff = match op {
                    CompareOp::Gte => result_a - result_b,
                    CompareOp::Lte => result_b - result_a,
                    CompareOp::Gt => result_a - result_b - BabyBear::ONE,
                    CompareOp::Lt => result_b - result_a - BabyBear::ONE,
                    CompareOp::Eq => result_a - result_b,
                    CompareOp::Neq => result_a - result_b,
                };
                // For ExprCompare, threshold public input is zero (not used for comparison).
                (BabyBear::ZERO, diff)
            }
        };

        row[layout.threshold_col] = threshold;
        row[layout.diff_col] = diff;
        row[layout.fact_commitment_col] = self.witness.fact_commitment;

        // Determine if this is an equality or inequality check.
        let is_eq = matches!(&self.witness.predicate, ArithPredicate::ExprEq(_, _))
            || matches!(
                &self.witness.predicate,
                ArithPredicate::ExprCompare(_, _, CompareOp::Eq)
            );
        let is_neq = matches!(&self.witness.predicate, ArithPredicate::ExprNeq(_, _))
            || matches!(
                &self.witness.predicate,
                ArithPredicate::ExprCompare(_, _, CompareOp::Neq)
            );

        if is_neq {
            // For NEQ: witness the inverse of diff. diff * inv == 1 proves diff != 0.
            if let Some(inv) = diff.inverse() {
                row[layout.neq_inverse_col] = inv;
            }
            // No bit decomposition needed for NEQ.
        } else if !is_eq {
            let diff_val = diff.as_u32();
            for i in 0..PREDICATE_DIFF_BITS {
                let bit = (diff_val >> i) & 1;
                row[layout.diff_bit_col(i)] = BabyBear::new(bit);
            }
        }

        let public_inputs = vec![threshold, self.witness.fact_commitment];
        (vec![row], public_inputs)
    }
}

/// A complete arithmetic predicate proof result.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ArithmeticPredicateProof {
    /// The threshold (public input).
    pub threshold: BabyBear,
    /// The fact commitment (public input).
    pub fact_commitment: BabyBear,
    /// The STARK proof (FRI-based, cryptographically sound).
    pub stark_proof: StarkProof,
    /// Compiled expression A ops (needed for verifier constraint reconstruction).
    pub compiled_ops: Vec<CompiledOp>,
    /// Result slot index for expression A.
    pub result_slot: usize,
    /// Compiled expression B ops (for ExprCompare predicates).
    pub compiled_ops_b: Option<Vec<CompiledOp>>,
    /// Result slot index for expression B (ExprCompare only).
    pub result_slot_b: Option<usize>,
    /// Number of private inputs (determines layout).
    pub num_inputs: usize,
    /// The kind of diff computation used.
    pub diff_kind: DiffKind,
}

/// Describes how the diff column is computed, for verifier reconstruction.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum DiffKind {
    /// diff = result - threshold (GTE / InRange lower bound)
    ResultMinusThreshold,
    /// diff = threshold - result (LTE)
    ThresholdMinusResult,
    /// diff = result - threshold, must be zero (ExprEq)
    Equality,
    /// diff = result - threshold, must be non-zero (ExprNeq)
    /// Proved via inverse witness: diff * inv == 1.
    Inequality,
    /// diff = result_a - result_b (ExprCompare GTE)
    CompareGte,
    /// diff = result_b - result_a (ExprCompare LTE)
    CompareLte,
    /// diff = result_a - result_b - 1 (ExprCompare GT)
    CompareGt,
    /// diff = result_b - result_a - 1 (ExprCompare LT)
    CompareLt,
    /// diff = result_a - result_b, must be zero (ExprCompare EQ)
    CompareEq,
    /// diff = result_a - result_b, must be non-zero (ExprCompare NEQ)
    /// Proved via inverse witness: diff * inv == 1.
    CompareNeq,
}

/// StarkAir wrapper for arithmetic predicates.
///
/// Contains all information needed to evaluate the full constraint set,
/// including arithmetic operation correctness, diff computation, bit decomposition,
/// and public input binding.
struct ArithmeticPredicateStarkAir {
    width: usize,
    /// Compiled ops for expression A.
    compiled_ops: Vec<CompiledOp>,
    /// Result slot index for expression A.
    result_slot: usize,
    /// Compiled ops for expression B (ExprCompare only).
    compiled_ops_b: Option<Vec<CompiledOp>>,
    /// Result slot index for expression B.
    result_slot_b: Option<usize>,
    /// Number of private inputs.
    num_inputs: usize,
    /// How the diff column is computed.
    diff_kind: DiffKind,
}

impl ArithmeticPredicateStarkAir {
    /// Reconstruct the layout from the stored parameters.
    fn layout(&self) -> ArithLayout {
        let ops_b = self.compiled_ops_b.as_deref();
        ArithLayout::new(self.num_inputs, &self.compiled_ops, ops_b)
    }
}

/// Evaluate all arithmetic operation constraints for a set of compiled ops,
/// given the trace row and the starting column for those slots.
/// Returns the accumulated constraint error.
fn eval_ops_constraints(
    ops: &[CompiledOp],
    local: &[BabyBear],
    slots_start: usize,
    layout: &ArithLayout,
    op_idx_offset: usize,
) -> BabyBear {
    let mut error = BabyBear::ZERO;
    for (slot_idx, op) in ops.iter().enumerate() {
        let col = slots_start + slot_idx;
        let actual = local[col];
        match op {
            CompiledOp::Input(i) => {
                error = error + (actual - local[*i]);
            }
            CompiledOp::Const(c) => {
                error = error + (actual - *c);
            }
            CompiledOp::Add(a, b) => {
                error = error + (actual - (local[slots_start + a] + local[slots_start + b]));
            }
            CompiledOp::Sub(a, b) => {
                error = error + (actual - (local[slots_start + a] - local[slots_start + b]));
            }
            CompiledOp::Mul(a, b) => {
                error = error + (actual - (local[slots_start + a] * local[slots_start + b]));
            }
            CompiledOp::Sum(indices) => {
                let mut sum = BabyBear::ZERO;
                for &i in indices {
                    sum = sum + local[i];
                }
                error = error + (actual - sum);
            }
            CompiledOp::Min(indices) => {
                // result equals at least one operand
                let result = actual;
                let mut product = BabyBear::ONE;
                for &i in indices {
                    product = product * (result - local[i]);
                }
                error = error + product;

                // result <= each operand (via aux range check bits)
                if let Some(aux) = layout.aux_for_op(op_idx_offset + slot_idx) {
                    for (k, &i) in indices.iter().enumerate() {
                        let diff = local[i] - result;
                        let bits_start = aux.start_col + k * PREDICATE_DIFF_BITS;
                        let mut recomposed = BabyBear::ZERO;
                        let mut power = BabyBear::ONE;
                        for j in 0..PREDICATE_DIFF_BITS {
                            let bit = local[bits_start + j];
                            recomposed = recomposed + bit * power;
                            error = error + bit * (bit - BabyBear::ONE);
                            power = power + power;
                        }
                        error = error + (recomposed - diff);
                        error = error + local[bits_start + PREDICATE_DIFF_BITS - 1];
                    }
                }
            }
            CompiledOp::Max(indices) => {
                // result equals at least one operand
                let result = actual;
                let mut product = BabyBear::ONE;
                for &i in indices {
                    product = product * (result - local[i]);
                }
                error = error + product;

                // result >= each operand (via aux range check bits)
                if let Some(aux) = layout.aux_for_op(op_idx_offset + slot_idx) {
                    for (k, &i) in indices.iter().enumerate() {
                        let diff = result - local[i];
                        let bits_start = aux.start_col + k * PREDICATE_DIFF_BITS;
                        let mut recomposed = BabyBear::ZERO;
                        let mut power = BabyBear::ONE;
                        for j in 0..PREDICATE_DIFF_BITS {
                            let bit = local[bits_start + j];
                            recomposed = recomposed + bit * power;
                            error = error + bit * (bit - BabyBear::ONE);
                            power = power + power;
                        }
                        error = error + (recomposed - diff);
                        error = error + local[bits_start + PREDICATE_DIFF_BITS - 1];
                    }
                }
            }
            CompiledOp::Abs(a) => {
                // result^2 = operand^2
                let operand = local[slots_start + a];
                error = error + (actual * actual - operand * operand);

                // result is non-negative via bit decomp
                if let Some(aux) = layout.aux_for_op(op_idx_offset + slot_idx) {
                    let bits_start = aux.start_col;
                    let mut recomposed = BabyBear::ZERO;
                    let mut power = BabyBear::ONE;
                    for j in 0..PREDICATE_DIFF_BITS {
                        let bit = local[bits_start + j];
                        recomposed = recomposed + bit * power;
                        error = error + bit * (bit - BabyBear::ONE);
                        power = power + power;
                    }
                    error = error + (recomposed - actual);
                    error = error + local[bits_start + PREDICATE_DIFF_BITS - 1];
                }
            }
            CompiledOp::DivFloor(a, b) => {
                if let Some(aux) = layout.aux_for_op(op_idx_offset + slot_idx) {
                    let remainder_col = aux.start_col;
                    let remainder = local[remainder_col];
                    let dividend = local[slots_start + a];
                    let divisor = local[slots_start + b];
                    let quotient = actual;

                    // q * b + r = a
                    error = error + (quotient * divisor + remainder - dividend);

                    // remainder >= 0: bit decomposition
                    let bits_start_r = aux.start_col + 1;
                    let mut recomposed = BabyBear::ZERO;
                    let mut power = BabyBear::ONE;
                    for j in 0..PREDICATE_DIFF_BITS {
                        let bit = local[bits_start_r + j];
                        recomposed = recomposed + bit * power;
                        error = error + bit * (bit - BabyBear::ONE);
                        power = power + power;
                    }
                    error = error + (recomposed - remainder);
                    error = error + local[bits_start_r + PREDICATE_DIFF_BITS - 1];

                    // remainder < divisor: bit decomp of (divisor - remainder - 1)
                    let bits_start_bound = aux.start_col + 1 + PREDICATE_DIFF_BITS;
                    let bound_diff = divisor - remainder - BabyBear::ONE;
                    let mut recomposed2 = BabyBear::ZERO;
                    let mut power2 = BabyBear::ONE;
                    for j in 0..PREDICATE_DIFF_BITS {
                        let bit = local[bits_start_bound + j];
                        recomposed2 = recomposed2 + bit * power2;
                        error = error + bit * (bit - BabyBear::ONE);
                        power2 = power2 + power2;
                    }
                    error = error + (recomposed2 - bound_diff);
                    error = error + local[bits_start_bound + PREDICATE_DIFF_BITS - 1];
                }
            }
            CompiledOp::Mod(a, b) => {
                if let Some(aux) = layout.aux_for_op(op_idx_offset + slot_idx) {
                    let quotient_col = aux.start_col;
                    let quotient = local[quotient_col];
                    let dividend = local[slots_start + a];
                    let divisor = local[slots_start + b];
                    let remainder = actual;

                    // q * b + r = a
                    error = error + (quotient * divisor + remainder - dividend);

                    // result >= 0: bit decomposition
                    let bits_start_r = aux.start_col + 1;
                    let mut recomposed = BabyBear::ZERO;
                    let mut power = BabyBear::ONE;
                    for j in 0..PREDICATE_DIFF_BITS {
                        let bit = local[bits_start_r + j];
                        recomposed = recomposed + bit * power;
                        error = error + bit * (bit - BabyBear::ONE);
                        power = power + power;
                    }
                    error = error + (recomposed - remainder);
                    error = error + local[bits_start_r + PREDICATE_DIFF_BITS - 1];

                    // result < divisor: bit decomp of (divisor - result - 1)
                    let bits_start_bound = aux.start_col + 1 + PREDICATE_DIFF_BITS;
                    let bound_diff = divisor - remainder - BabyBear::ONE;
                    let mut recomposed2 = BabyBear::ZERO;
                    let mut power2 = BabyBear::ONE;
                    for j in 0..PREDICATE_DIFF_BITS {
                        let bit = local[bits_start_bound + j];
                        recomposed2 = recomposed2 + bit * power2;
                        error = error + bit * (bit - BabyBear::ONE);
                        power2 = power2 + power2;
                    }
                    error = error + (recomposed2 - bound_diff);
                    error = error + local[bits_start_bound + PREDICATE_DIFF_BITS - 1];
                }
            }
        }
    }
    error
}

impl StarkAir for ArithmeticPredicateStarkAir {
    fn width(&self) -> usize {
        self.width
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-arithmetic-predicate-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let layout = self.layout();
        let threshold_col = layout.threshold_col;
        let diff_col = layout.diff_col;
        let diff_bits_start = layout.diff_bits_start;
        let fact_commitment_col = layout.fact_commitment_col;

        let mut result = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;

        // Constraint 1: Threshold matches public input.
        let c1 = local[threshold_col] - public_inputs[0];
        result = result + alpha_pow * c1;
        alpha_pow = alpha_pow * alpha;

        // Constraint 2: Fact commitment matches public input.
        let c2 = local[fact_commitment_col] - public_inputs[1];
        result = result + alpha_pow * c2;
        alpha_pow = alpha_pow * alpha;

        // Constraint 3: Arithmetic operation correctness (expression A).
        let c3 = eval_ops_constraints(&self.compiled_ops, local, layout.slots_start, &layout, 0);
        result = result + alpha_pow * c3;
        alpha_pow = alpha_pow * alpha;

        // Constraint 4: Arithmetic operation correctness (expression B, ExprCompare only).
        let c4 = if let Some(ops_b) = &self.compiled_ops_b {
            eval_ops_constraints(
                ops_b,
                local,
                layout.slots_b_start,
                &layout,
                layout.num_slots,
            )
        } else {
            BabyBear::ZERO
        };
        result = result + alpha_pow * c4;
        alpha_pow = alpha_pow * alpha;

        // Constraint 5: Diff is correctly computed based on predicate type.
        let result_a = local[layout.slots_start + self.result_slot];
        let c5 = match &self.diff_kind {
            DiffKind::ResultMinusThreshold => local[diff_col] - (result_a - local[threshold_col]),
            DiffKind::ThresholdMinusResult => local[diff_col] - (local[threshold_col] - result_a),
            DiffKind::Equality | DiffKind::Inequality => {
                local[diff_col] - (result_a - local[threshold_col])
            }
            DiffKind::CompareGte => {
                let result_b = local[layout.slots_b_start + self.result_slot_b.unwrap_or(0)];
                local[diff_col] - (result_a - result_b)
            }
            DiffKind::CompareLte => {
                let result_b = local[layout.slots_b_start + self.result_slot_b.unwrap_or(0)];
                local[diff_col] - (result_b - result_a)
            }
            DiffKind::CompareGt => {
                let result_b = local[layout.slots_b_start + self.result_slot_b.unwrap_or(0)];
                local[diff_col] - (result_a - result_b - BabyBear::ONE)
            }
            DiffKind::CompareLt => {
                let result_b = local[layout.slots_b_start + self.result_slot_b.unwrap_or(0)];
                local[diff_col] - (result_b - result_a - BabyBear::ONE)
            }
            DiffKind::CompareEq | DiffKind::CompareNeq => {
                let result_b = local[layout.slots_b_start + self.result_slot_b.unwrap_or(0)];
                local[diff_col] - (result_a - result_b)
            }
        };
        result = result + alpha_pow * c5;
        alpha_pow = alpha_pow * alpha;

        // Constraint 6: Bit decomposition or inverse check.
        let is_eq = matches!(self.diff_kind, DiffKind::Equality | DiffKind::CompareEq);
        let is_neq = matches!(self.diff_kind, DiffKind::Inequality | DiffKind::CompareNeq);
        let c6 = if is_eq {
            // For equality predicates, diff must be zero directly.
            local[diff_col]
        } else if is_neq {
            // For inequality predicates, diff * inverse == 1 (proves diff != 0).
            let neq_inverse = local[layout.neq_inverse_col];
            local[diff_col] * neq_inverse - BabyBear::ONE
        } else {
            let mut recomposed = BabyBear::ZERO;
            let mut power_of_two = BabyBear::ONE;
            for i in 0..PREDICATE_DIFF_BITS {
                let bit = local[diff_bits_start + i];
                recomposed = recomposed + bit * power_of_two;
                power_of_two = power_of_two + power_of_two;
            }
            recomposed - local[diff_col]
        };
        result = result + alpha_pow * c6;
        alpha_pow = alpha_pow * alpha;

        // Constraint 7: All diff bits are binary (0 or 1).
        // Skipped for EQ (diff must be zero) and NEQ (uses inverse instead of bit decomp).
        let c7 = if is_eq || is_neq {
            BabyBear::ZERO
        } else {
            let mut bits_error = BabyBear::ZERO;
            for i in 0..PREDICATE_DIFF_BITS {
                let bit = local[diff_bits_start + i];
                bits_error = bits_error + bit * (bit - BabyBear::ONE);
            }
            bits_error
        };
        result = result + alpha_pow * c7;
        alpha_pow = alpha_pow * alpha;

        // Constraint 8: High bit is zero (proves diff is non-negative, i.e., diff < 2^(BITS-1)).
        // Skipped for EQ and NEQ.
        let c8 = if is_eq || is_neq {
            BabyBear::ZERO
        } else {
            local[diff_bits_start + PREDICATE_DIFF_BITS - 1]
        };
        result = result + alpha_pow * c8;

        result
    }

    fn boundary_constraints(
        &self,
        _public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        vec![]
    }
}

/// Determine the DiffKind from a predicate.
fn diff_kind_from_predicate(predicate: &ArithPredicate) -> DiffKind {
    match predicate {
        ArithPredicate::ExprGte(_, _) => DiffKind::ResultMinusThreshold,
        ArithPredicate::ExprLte(_, _) => DiffKind::ThresholdMinusResult,
        ArithPredicate::ExprEq(_, _) => DiffKind::Equality,
        ArithPredicate::ExprNeq(_, _) => DiffKind::Inequality,
        ArithPredicate::ExprInRange(_, _, _) => DiffKind::ResultMinusThreshold,
        ArithPredicate::ExprCompare(_, _, op) => match op {
            CompareOp::Gte => DiffKind::CompareGte,
            CompareOp::Lte => DiffKind::CompareLte,
            CompareOp::Gt => DiffKind::CompareGt,
            CompareOp::Lt => DiffKind::CompareLt,
            CompareOp::Eq => DiffKind::CompareEq,
            CompareOp::Neq => DiffKind::CompareNeq,
        },
    }
}

/// Generate an arithmetic predicate proof from a witness.
///
/// Returns `None` if the predicate is not satisfiable (the statement is false),
/// the expression is too large, or proof generation fails.
pub fn prove_arithmetic_predicate(
    witness: ArithmeticPredicateWitness,
) -> Option<ArithmeticPredicateProof> {
    if !witness.is_satisfiable() {
        return None;
    }

    let fact_commitment = witness.fact_commitment;
    let num_inputs = witness.inputs.len();
    let diff_kind = diff_kind_from_predicate(&witness.predicate);

    let air = ArithmeticPredicateAir::new(witness)?;

    let compiled_ops = air.compiled.ops.clone();
    let result_slot = air.compiled.result_slot;
    let compiled_ops_b = air.compiled_b.as_ref().map(|c| c.ops.clone());
    let result_slot_b = air.compiled_b.as_ref().map(|c| c.result_slot);

    // Generate trace and get public inputs.
    let (mut trace, public_inputs) = air.generate_trace();
    let threshold = public_inputs[0];
    let width = air.trace_width();

    // STARK prover requires trace length >= 2 and power-of-two.
    while trace.len() < 2 || !trace.len().is_power_of_two() {
        trace.push(trace[0].clone());
    }

    let stark_air = ArithmeticPredicateStarkAir {
        width,
        compiled_ops: compiled_ops.clone(),
        result_slot,
        compiled_ops_b: compiled_ops_b.clone(),
        result_slot_b,
        num_inputs,
        diff_kind: diff_kind.clone(),
    };
    let stark_proof = stark::prove(&stark_air, &trace, &public_inputs);

    Some(ArithmeticPredicateProof {
        threshold,
        fact_commitment,
        stark_proof,
        compiled_ops,
        result_slot,
        compiled_ops_b,
        result_slot_b,
        num_inputs,
        diff_kind,
    })
}

/// Verify an arithmetic predicate proof against expected public inputs.
pub fn verify_arithmetic_predicate(
    proof: &ArithmeticPredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) -> bool {
    if proof.threshold != threshold || proof.fact_commitment != fact_commitment {
        return false;
    }
    let public_inputs = vec![threshold, fact_commitment];
    // Reconstruct the AIR with ops from the proof for full constraint verification.
    let stark_air = ArithmeticPredicateStarkAir {
        width: proof.stark_proof.num_cols,
        compiled_ops: proof.compiled_ops.clone(),
        result_slot: proof.result_slot,
        compiled_ops_b: proof.compiled_ops_b.clone(),
        result_slot_b: proof.result_slot_b,
        num_inputs: proof.num_inputs,
        diff_kind: proof.diff_kind.clone(),
    };
    stark::verify(&stark_air, &proof.stark_proof, &public_inputs).is_ok()
}

/// Compute the fact commitment for binding proven values to a token state.
///
/// `fact_commitment = Poseidon2(fact_hash, state_root)`
pub fn compute_arithmetic_fact_commitment(fact_hash: BabyBear, state_root: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(fact_hash, state_root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;
    use crate::poseidon2;

    /// Helper: create a fact commitment for testing.
    fn test_commitment(values: &[BabyBear]) -> BabyBear {
        let fact_hash = poseidon2::hash_fact(BabyBear::new(200), values);
        let state_root = BabyBear::new(88888);
        compute_arithmetic_fact_commitment(fact_hash, state_root)
    }

    // =========================================================================
    // Expression evaluation tests
    // =========================================================================

    #[test]
    fn test_eval_add() {
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));
        let inputs = vec![BabyBear::new(60), BabyBear::new(50)];
        let result = evaluate_expression(&expr, &inputs).unwrap();
        assert_eq!(result.as_u32(), 110);
    }

    #[test]
    fn test_eval_sub() {
        let expr = ArithExpr::Sub(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));
        let inputs = vec![BabyBear::new(500), BabyBear::new(300)];
        let result = evaluate_expression(&expr, &inputs).unwrap();
        assert_eq!(result.as_u32(), 200);
    }

    #[test]
    fn test_eval_mul() {
        let expr = ArithExpr::Mul(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));
        let inputs = vec![BabyBear::new(20), BabyBear::new(60)];
        let result = evaluate_expression(&expr, &inputs).unwrap();
        assert_eq!(result.as_u32(), 1200);
    }

    #[test]
    fn test_eval_min() {
        let expr = ArithExpr::Min(vec![0, 1, 2]);
        let inputs = vec![BabyBear::new(15), BabyBear::new(10), BabyBear::new(20)];
        let result = evaluate_expression(&expr, &inputs).unwrap();
        assert_eq!(result.as_u32(), 10);
    }

    #[test]
    fn test_eval_max() {
        let expr = ArithExpr::Max(vec![0, 1, 2]);
        let inputs = vec![BabyBear::new(15), BabyBear::new(10), BabyBear::new(20)];
        let result = evaluate_expression(&expr, &inputs).unwrap();
        assert_eq!(result.as_u32(), 20);
    }

    #[test]
    fn test_eval_sum() {
        let expr = ArithExpr::Sum(vec![0, 1, 2]);
        let inputs = vec![BabyBear::new(10), BabyBear::new(20), BabyBear::new(30)];
        let result = evaluate_expression(&expr, &inputs).unwrap();
        assert_eq!(result.as_u32(), 60);
    }

    #[test]
    fn test_eval_div_floor() {
        let expr = ArithExpr::DivFloor(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));
        let inputs = vec![BabyBear::new(100), BabyBear::new(7)];
        let result = evaluate_expression(&expr, &inputs).unwrap();
        assert_eq!(result.as_u32(), 14); // 100 / 7 = 14
    }

    #[test]
    fn test_eval_mod() {
        let expr = ArithExpr::Mod(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));
        let inputs = vec![BabyBear::new(100), BabyBear::new(7)];
        let result = evaluate_expression(&expr, &inputs).unwrap();
        assert_eq!(result.as_u32(), 2); // 100 % 7 = 2
    }

    #[test]
    fn test_eval_const() {
        let expr = ArithExpr::Add(
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(BabyBear::new(42))),
        );
        let inputs = vec![BabyBear::new(8)];
        let result = evaluate_expression(&expr, &inputs).unwrap();
        assert_eq!(result.as_u32(), 50);
    }

    // =========================================================================
    // AIR constraint verification tests
    // =========================================================================

    #[test]
    fn test_add_gte_passes() {
        // Prove: a + b >= 100 where a=60, b=50 (sum=110 >= 100)
        let inputs = vec![BabyBear::new(60), BabyBear::new(50)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(100)),
            fact_commitment: commitment,
        };

        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "a + b >= 100 with a=60, b=50 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_add_gte_fails() {
        // Prove: a + b >= 100 where a=30, b=20 (sum=50 < 100)
        let inputs = vec![BabyBear::new(30), BabyBear::new(20)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(100)),
            fact_commitment: commitment,
        };

        assert!(
            !witness.is_satisfiable(),
            "50 >= 100 should not be satisfiable"
        );
    }

    #[test]
    fn test_mul_gte_passes() {
        // Prove: a * b >= 1000 where a=20, b=60 (product=1200 >= 1000)
        let inputs = vec![BabyBear::new(20), BabyBear::new(60)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Mul(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(1000)),
            fact_commitment: commitment,
        };

        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "a * b >= 1000 with a=20, b=60 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_min_gte_passes() {
        // Prove: min(a, b, c) >= 10 where values are 15, 10, 20 (min=10 >= 10)
        let inputs = vec![BabyBear::new(15), BabyBear::new(10), BabyBear::new(20)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Min(vec![0, 1, 2]);

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(10)),
            fact_commitment: commitment,
        };

        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "min(15,10,20) >= 10 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_spread_check_lte_passes() {
        // Prove: max(a, b) - min(a, b) <= 5 (spread check)
        // a=12, b=14 => max=14, min=12, spread=2 <= 5
        let inputs = vec![BabyBear::new(12), BabyBear::new(14)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Sub(
            Box::new(ArithExpr::Max(vec![0, 1])),
            Box::new(ArithExpr::Min(vec![0, 1])),
        );

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprLte(expr, BabyBear::new(5)),
            fact_commitment: commitment,
        };

        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "max(12,14) - min(12,14) <= 5 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_profitability_passes() {
        // Prove: (revenue - costs) >= 0 where revenue=500, costs=300
        let inputs = vec![BabyBear::new(500), BabyBear::new(300)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Sub(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(0)),
            fact_commitment: commitment,
        };

        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "(500 - 300) >= 0 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_expr_eq_passes() {
        // Prove: a + b == 100 where a=60, b=40
        let inputs = vec![BabyBear::new(60), BabyBear::new(40)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprEq(expr, BabyBear::new(100)),
            fact_commitment: commitment,
        };

        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "60 + 40 == 100 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_expr_eq_fails() {
        // Prove: a + b == 100 where a=60, b=50 (sum=110 != 100)
        let inputs = vec![BabyBear::new(60), BabyBear::new(50)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprEq(expr, BabyBear::new(100)),
            fact_commitment: commitment,
        };

        assert!(
            !witness.is_satisfiable(),
            "110 == 100 should not be satisfiable"
        );
    }

    #[test]
    fn test_expr_compare_gte_passes() {
        // Prove: (a + b) >= (c + d) where a=30, b=40, c=20, d=15
        // 70 >= 35
        let inputs = vec![
            BabyBear::new(30),
            BabyBear::new(40),
            BabyBear::new(20),
            BabyBear::new(15),
        ];
        let commitment = test_commitment(&inputs);
        let expr_a = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));
        let expr_b = ArithExpr::Add(Box::new(ArithExpr::Var(2)), Box::new(ArithExpr::Var(3)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprCompare(expr_a, expr_b, CompareOp::Gte),
            fact_commitment: commitment,
        };

        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "(30+40) >= (20+15) should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_expr_compare_lt_passes() {
        // Prove: a < b where a=10, b=20
        let inputs = vec![BabyBear::new(10), BabyBear::new(20)];
        let commitment = test_commitment(&inputs);
        let expr_a = ArithExpr::Var(0);
        let expr_b = ArithExpr::Var(1);

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprCompare(expr_a, expr_b, CompareOp::Lt),
            fact_commitment: commitment,
        };

        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "10 < 20 should pass: {:?}",
            result.violations()
        );
    }

    // =========================================================================
    // Prove/verify integration tests
    // =========================================================================

    #[test]
    fn test_prove_and_verify_add_gte() {
        // Prove: a + b >= 100 where a=60, b=50
        let inputs = vec![BabyBear::new(60), BabyBear::new(50)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(100)),
            fact_commitment: commitment,
        };

        let proof = prove_arithmetic_predicate(witness).expect("should produce proof");
        assert!(verify_arithmetic_predicate(
            &proof,
            BabyBear::new(100),
            commitment
        ));
    }

    #[test]
    fn test_prove_returns_none_for_false_statement() {
        // Prove: a + b >= 200 where a=60, b=50 (sum=110 < 200)
        let inputs = vec![BabyBear::new(60), BabyBear::new(50)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(200)),
            fact_commitment: commitment,
        };

        let proof = prove_arithmetic_predicate(witness);
        assert!(proof.is_none(), "Cannot prove false statement");
    }

    #[test]
    fn test_verify_fails_with_wrong_threshold() {
        let inputs = vec![BabyBear::new(60), BabyBear::new(50)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(100)),
            fact_commitment: commitment,
        };

        let proof = prove_arithmetic_predicate(witness).expect("should produce proof");
        // Verify with wrong threshold.
        assert!(!verify_arithmetic_predicate(
            &proof,
            BabyBear::new(50),
            commitment
        ));
    }

    #[test]
    fn test_verify_fails_with_wrong_commitment() {
        let inputs = vec![BabyBear::new(60), BabyBear::new(50)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(100)),
            fact_commitment: commitment,
        };

        let proof = prove_arithmetic_predicate(witness).expect("should produce proof");
        let wrong_commitment = BabyBear::new(12345);
        assert!(!verify_arithmetic_predicate(
            &proof,
            BabyBear::new(100),
            wrong_commitment
        ));
    }

    // =========================================================================
    // Compilation tests
    // =========================================================================

    #[test]
    fn test_compile_simple_add() {
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));
        let compiled = compile_expression(&expr, 2).unwrap();
        assert_eq!(compiled.ops.len(), 3); // Input(0), Input(1), Add(0,1)
        assert_eq!(compiled.result_slot, 2);
    }

    #[test]
    fn test_compile_nested() {
        // (a + b) * c
        let expr = ArithExpr::Mul(
            Box::new(ArithExpr::Add(
                Box::new(ArithExpr::Var(0)),
                Box::new(ArithExpr::Var(1)),
            )),
            Box::new(ArithExpr::Var(2)),
        );
        let compiled = compile_expression(&expr, 3).unwrap();
        // Input(0), Input(1), Add(0,1), Input(2), Mul(2,3)
        assert_eq!(compiled.ops.len(), 5);
        assert_eq!(compiled.result_slot, 4);
    }

    #[test]
    fn test_compile_rejects_invalid_input() {
        // Var(5) but only 2 inputs.
        let expr = ArithExpr::Var(5);
        let result = compile_expression(&expr, 2);
        assert!(result.is_none());
    }

    #[test]
    fn test_expression_size_limit() {
        // Build a deeply nested expression that exceeds MAX_ARITHMETIC_OPS.
        let mut expr = ArithExpr::Var(0);
        for _ in 0..35 {
            expr = ArithExpr::Add(Box::new(expr), Box::new(ArithExpr::Const(BabyBear::ONE)));
        }
        let result = compile_expression(&expr, 1);
        assert!(
            result.is_none(),
            "Should reject expression exceeding 32 ops"
        );
    }

    // =========================================================================
    // Complex scenario tests
    // =========================================================================

    #[test]
    fn test_sum_aggregate_gte() {
        // Prove: sum(a, b, c, d) >= 100 where values are 20, 30, 25, 35 (sum=110)
        let inputs = vec![
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(25),
            BabyBear::new(35),
        ];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Sum(vec![0, 1, 2, 3]);

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(100)),
            fact_commitment: commitment,
        };

        let proof = prove_arithmetic_predicate(witness).expect("should produce proof");
        assert!(verify_arithmetic_predicate(
            &proof,
            BabyBear::new(100),
            commitment
        ));
    }

    #[test]
    fn test_complex_expression_revenue_margin() {
        // Prove: (revenue - costs) * margin >= min_profit
        // revenue=1000, costs=400, margin=3 => (600) * 3 = 1800 >= 1500
        let inputs = vec![
            BabyBear::new(1000), // revenue
            BabyBear::new(400),  // costs
            BabyBear::new(3),    // margin multiplier
        ];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Mul(
            Box::new(ArithExpr::Sub(
                Box::new(ArithExpr::Var(0)),
                Box::new(ArithExpr::Var(1)),
            )),
            Box::new(ArithExpr::Var(2)),
        );

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(1500)),
            fact_commitment: commitment,
        };

        let air = ArithmeticPredicateAir::new(witness.clone()).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "(1000-400)*3 >= 1500 should pass: {:?}",
            result.violations()
        );

        let proof = prove_arithmetic_predicate(witness).expect("should produce proof");
        assert!(verify_arithmetic_predicate(
            &proof,
            BabyBear::new(1500),
            commitment
        ));
    }

    #[test]
    fn test_in_range_predicate() {
        // Prove: 50 <= (a + b) <= 200 where a=60, b=50 (sum=110)
        let inputs = vec![BabyBear::new(60), BabyBear::new(50)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprInRange(expr, BabyBear::new(50), BabyBear::new(200)),
            fact_commitment: commitment,
        };

        assert!(witness.is_satisfiable());

        // The AIR proves the lower bound. For full InRange, you'd need two AIR instances.
        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "50 <= (60+50) <= 200 lower bound should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_max_minus_min_spread_full_proof() {
        // Full prove/verify: max(a,b) - min(a,b) <= 5
        // a=100, b=103 => spread = 3 <= 5
        let inputs = vec![BabyBear::new(100), BabyBear::new(103)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Sub(
            Box::new(ArithExpr::Max(vec![0, 1])),
            Box::new(ArithExpr::Min(vec![0, 1])),
        );

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprLte(expr, BabyBear::new(5)),
            fact_commitment: commitment,
        };

        let proof = prove_arithmetic_predicate(witness).expect("should produce proof");
        assert!(verify_arithmetic_predicate(
            &proof,
            BabyBear::new(5),
            commitment
        ));
    }

    #[test]
    fn test_div_floor_in_expression() {
        // Prove: (total / count) >= 50 where total=500, count=8 (62 >= 50)
        let inputs = vec![BabyBear::new(500), BabyBear::new(8)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::DivFloor(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprGte(expr, BabyBear::new(50)),
            fact_commitment: commitment,
        };

        assert!(witness.is_satisfiable());
        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "500/8 >= 50 should pass: {:?}",
            result.violations()
        );
    }

    // =========================================================================
    // ExprNeq tests (inequality predicate)
    // =========================================================================

    #[test]
    fn test_expr_neq_passes() {
        // Prove: a != 42 where a = 100
        let inputs = vec![BabyBear::new(100)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Var(0);

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprNeq(expr, BabyBear::new(42)),
            fact_commitment: commitment,
        };

        assert!(witness.is_satisfiable());
        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "100 != 42 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_expr_neq_fails_when_equal() {
        // Prove: a != 42 where a = 42 (should fail)
        let inputs = vec![BabyBear::new(42)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Var(0);

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprNeq(expr, BabyBear::new(42)),
            fact_commitment: commitment,
        };

        assert!(
            !witness.is_satisfiable(),
            "42 != 42 should not be satisfiable"
        );
    }

    #[test]
    fn test_expr_neq_expression_passes() {
        // Prove: (a + b) != 100 where a=30, b=40 (sum=70 != 100)
        let inputs = vec![BabyBear::new(30), BabyBear::new(40)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprNeq(expr, BabyBear::new(100)),
            fact_commitment: commitment,
        };

        assert!(witness.is_satisfiable());
        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "(30 + 40) != 100 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_prove_verify_expr_neq() {
        // Full prove/verify: a != 0 where a = 7
        let inputs = vec![BabyBear::new(7)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Var(0);

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprNeq(expr, BabyBear::new(0)),
            fact_commitment: commitment,
        };

        let proof = prove_arithmetic_predicate(witness).expect("should produce proof");
        assert!(verify_arithmetic_predicate(
            &proof,
            BabyBear::new(0),
            commitment
        ));
    }

    #[test]
    fn test_prove_neq_returns_none_when_equal() {
        // Prove: a != 7 where a = 7 (should fail)
        let inputs = vec![BabyBear::new(7)];
        let commitment = test_commitment(&inputs);
        let expr = ArithExpr::Var(0);

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprNeq(expr, BabyBear::new(7)),
            fact_commitment: commitment,
        };

        let proof = prove_arithmetic_predicate(witness);
        assert!(proof.is_none(), "Cannot prove 7 != 7");
    }

    #[test]
    fn test_expr_compare_neq_passes() {
        // Prove: a != b where a=10, b=20
        let inputs = vec![BabyBear::new(10), BabyBear::new(20)];
        let commitment = test_commitment(&inputs);
        let expr_a = ArithExpr::Var(0);
        let expr_b = ArithExpr::Var(1);

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprCompare(expr_a, expr_b, CompareOp::Neq),
            fact_commitment: commitment,
        };

        assert!(witness.is_satisfiable());
        let air = ArithmeticPredicateAir::new(witness).unwrap();
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "10 != 20 (ExprCompare) should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_expr_compare_neq_fails_when_equal() {
        // Prove: a != b where a=42, b=42 (should fail)
        let inputs = vec![BabyBear::new(42), BabyBear::new(42)];
        let commitment = test_commitment(&inputs);
        let expr_a = ArithExpr::Var(0);
        let expr_b = ArithExpr::Var(1);

        let witness = ArithmeticPredicateWitness {
            inputs,
            predicate: ArithPredicate::ExprCompare(expr_a, expr_b, CompareOp::Neq),
            fact_commitment: commitment,
        };

        assert!(
            !witness.is_satisfiable(),
            "42 != 42 (ExprCompare) should not be satisfiable"
        );
    }
}
