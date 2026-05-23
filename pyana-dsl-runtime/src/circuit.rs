//! Runtime circuit descriptor: a generic `StarkAir` implementation driven by data.
//!
//! Instead of the proc macro generating full `impl StarkAir` code, it emits a
//! [`CircuitDescriptor`] that the generic [`DslCircuit`] interprets at runtime.
//!
//! # Smart Contract Runtime
//!
//! The `DslCircuit` + `CircuitDescriptor` serves as the smart contract runtime:
//! user-defined cell programs are submitted as serialized `CircuitDescriptor`s at
//! deploy time, validated for safety, and then executed/verified at runtime via
//! the [`CellProgram`] and [`ProgramRegistry`] types.

use std::collections::HashMap;
use std::sync::Mutex;

use pyana_circuit::field::BabyBear;
use pyana_circuit::stark::{self, BoundaryConstraint, StarkAir};
use serde::{Deserialize, Serialize};

// ============================================================================
// Descriptor types
// ============================================================================

/// A complete description of an AIR circuit — trace layout, constraints, boundaries.
///
/// This is the core type for user-defined cell programs. It is serializable for
/// deployment and can be validated for safety before accepting into a registry.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitDescriptor {
    pub name: String,
    pub trace_width: usize,
    pub max_degree: usize,
    pub columns: Vec<ColumnDef>,
    pub constraints: Vec<ConstraintExpr>,
    pub boundaries: Vec<BoundaryDef>,
    pub public_input_count: usize,
}

/// Metadata for a single trace column.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ColumnDef {
    pub name: String,
    pub index: usize,
    pub kind: ColumnKind,
}

/// Semantic kind of a column (for documentation and potential future optimization).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ColumnKind {
    Value,
    Binary,
    Selector,
    Hash,
}

/// An algebraic constraint expression that evaluates to zero on a valid trace.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
    Gated {
        selector_col: usize,
        inner: Box<ConstraintExpr>,
    },

    /// Constraint active when selector_col == 0 (inverted gating)
    /// `(1 - local[selector_col]) * inner == 0`
    InvertedGated {
        selector_col: usize,
        inner: Box<ConstraintExpr>,
    },

    /// Squared constraint: `inner^2 == 0` (equivalent to `inner == 0` for soundness,
    /// but produces different numerical values when composed with alpha powers).
    Squared { inner: Box<ConstraintExpr> },

    /// Constrain col_output == Poseidon2_hash_fact(col_inputs[0], col_inputs[1..])
    /// The first input column is the predicate, the rest are terms.
    /// The evaluator computes hash_fact(predicate, &terms) and checks equality.
    /// For general-purpose hashing (sponge), use hash_many via Polynomial encoding.
    Hash {
        output_col: usize,
        input_cols: Vec<usize>,
    },

    /// When selector_col != 0, require value_col != 0.
    /// Implemented as: selector * (value * inverse - 1) == 0
    /// Needs an auxiliary inverse column (prover fills with value^{-1}, or 0 if value==0).
    ConditionalNonzero {
        selector_col: usize,
        value_col: usize,
        inverse_col: usize,
    },

    /// Require sum(flag_cols) >= 1 (at least one flag is active).
    /// Implemented as: (1 - flag_0) * (1 - flag_1) * ... * (1 - flag_n) == 0
    /// (product is zero iff at least one flag is 1).
    AtLeastOne { flag_cols: Vec<usize> },

    /// Constrain output_col == Poseidon2_hash_2_to_1(input_col_a, input_col_b).
    /// Uses the 2-to-1 compression function with arity tag 2.
    Hash2to1 {
        output_col: usize,
        input_col_a: usize,
        input_col_b: usize,
    },

    /// Constrain output_col == Poseidon2_hash_4_to_1([col_0, col_1, col_2, col_3]).
    /// Uses the 4-to-1 compression function with arity tag 4.
    Hash4to1 {
        output_col: usize,
        input_cols: [usize; 4],
    },
    // NOTE: SelectiveWrite was removed -- it used a non-algebraic Rust if/else branch
    // which is unsound in a STARK (constraints must be evaluatable as polynomials over
    // the entire domain). Users should instead use a Gated constraint with an explicit
    // binary indicator column set to 1 at the target row and 0 elsewhere:
    //   indicator * (next[target_col] - local[source_col]) == 0
    // This is algebraic and soundly verifiable.
}

/// A single term in a polynomial constraint: `coeff * product(local[col] for col in col_indices)`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolyTerm {
    pub coeff: BabyBear,
    /// Product of these column values. Empty = constant term (just coeff).
    pub col_indices: Vec<usize>,
}

/// A boundary constraint definition (binds a trace cell to a value at prove time).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BoundaryDef {
    /// `trace[row][col] == pi[pi_index]`
    PiBinding {
        row: BoundaryRow,
        col: usize,
        pi_index: usize,
    },
    /// `trace[row][col] == fixed_value`
    Fixed {
        row: BoundaryRow,
        col: usize,
        value: BabyBear,
    },
}

/// Which row a boundary constraint targets.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
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
            Self::Multiplication { a, b, output } => local[*a] * local[*b] - local[*output],
            Self::Binary { col } => local[*col] * (local[*col] - BabyBear::ONE),
            Self::PiBinding { col, pi_index } => local[*col] - pi[*pi_index],
            Self::Transition {
                next_col,
                local_col,
            } => next[*next_col] - local[*local_col],
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
            Self::Gated {
                selector_col,
                inner,
            } => local[*selector_col] * inner.evaluate(local, next, pi),
            Self::InvertedGated {
                selector_col,
                inner,
            } => (BabyBear::ONE - local[*selector_col]) * inner.evaluate(local, next, pi),
            Self::Squared { inner } => {
                let v = inner.evaluate(local, next, pi);
                v * v
            }
            Self::Hash {
                output_col,
                input_cols,
            } => {
                // First input is the predicate, rest are terms.
                let predicate = local[input_cols[0]];
                let terms: Vec<BabyBear> = input_cols[1..].iter().map(|&c| local[c]).collect();
                let expected = pyana_circuit::poseidon2::hash_fact(predicate, &terms);
                expected - local[*output_col]
            }
            Self::ConditionalNonzero {
                selector_col,
                value_col,
                inverse_col,
            } => {
                // selector * (value * inverse - 1) == 0
                // When selector=0: constraint is trivially 0.
                // When selector!=0: requires value*inverse=1, i.e. value!=0.
                local[*selector_col] * (local[*value_col] * local[*inverse_col] - BabyBear::ONE)
            }
            Self::AtLeastOne { flag_cols } => {
                // (1-f0)*(1-f1)*...*(1-fn) == 0 iff at least one fi=1
                let mut product = BabyBear::ONE;
                for &col in flag_cols {
                    product = product * (BabyBear::ONE - local[col]);
                }
                product
            }
            Self::Hash2to1 {
                output_col,
                input_col_a,
                input_col_b,
            } => {
                let expected =
                    pyana_circuit::poseidon2::hash_2_to_1(local[*input_col_a], local[*input_col_b]);
                expected - local[*output_col]
            }
            Self::Hash4to1 {
                output_col,
                input_cols,
            } => {
                let children = [
                    local[input_cols[0]],
                    local[input_cols[1]],
                    local[input_cols[2]],
                    local[input_cols[3]],
                ];
                let expected = pyana_circuit::poseidon2::hash_4_to_1(&children);
                expected - local[*output_col]
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

/// Global cache for leaked air name strings. Ensures each unique name is leaked at most once,
/// preventing unbounded memory growth when multiple `DslCircuit` instances share the same name.
static AIR_NAME_CACHE: Mutex<Option<HashMap<String, &'static str>>> = Mutex::new(None);

/// Intern a string as `&'static str`, reusing a previously leaked copy if available.
pub(crate) fn intern_air_name(name: &str) -> &'static str {
    let mut guard = AIR_NAME_CACHE.lock().unwrap_or_else(|e| e.into_inner());
    let cache = guard.get_or_insert_with(HashMap::new);
    if let Some(&existing) = cache.get(name) {
        return existing;
    }
    let leaked: &'static str = Box::leak(name.to_owned().into_boxed_str());
    cache.insert(name.to_owned(), leaked);
    leaked
}

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
        // Use the global intern cache so each unique name is leaked at most once.
        intern_air_name(&self.descriptor.name)
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
// Program Validation
// ============================================================================

/// Maximum allowed trace width for deployed programs (columns).
pub const MAX_TRACE_WIDTH: usize = 1024;

/// Maximum allowed constraint degree for deployed programs.
pub const MAX_CONSTRAINT_DEGREE: usize = 8;

/// Maximum number of public inputs for deployed programs.
pub const MAX_PUBLIC_INPUTS: usize = 64;

/// Errors returned when validating a program descriptor for deployment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProgramValidationError {
    /// Trace width exceeds the maximum allowed (1024 columns).
    TooWide { width: usize },
    /// Constraint degree exceeds the maximum allowed (8).
    DegreeTooHigh { degree: usize },
    /// A constraint references a column index that exceeds trace_width.
    ColumnOutOfBounds {
        constraint_index: usize,
        col: usize,
        trace_width: usize,
    },
    /// Too many public inputs declared.
    TooManyPublicInputs { count: usize },
    /// A boundary constraint references an out-of-bounds column.
    BoundaryColumnOutOfBounds {
        boundary_index: usize,
        col: usize,
        trace_width: usize,
    },
    /// A boundary constraint references a public input index out of range.
    BoundaryPiOutOfBounds {
        boundary_index: usize,
        pi_index: usize,
        pi_count: usize,
    },
    /// Program name is empty or too long.
    InvalidName,
    /// Trace width is zero.
    ZeroWidth,
    /// A constraint's algebraic degree exceeds max_degree.
    ConstraintDegreeExceeded {
        constraint_index: usize,
        degree: usize,
        max_degree: usize,
    },
    /// A PiBinding constraint references an out-of-bounds public input index.
    PiBindingOutOfBounds {
        constraint_index: usize,
        pi_index: usize,
        pi_count: usize,
    },
}

impl std::fmt::Display for ProgramValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooWide { width } => {
                write!(f, "trace width {width} exceeds max {MAX_TRACE_WIDTH}")
            }
            Self::DegreeTooHigh { degree } => write!(
                f,
                "constraint degree {degree} exceeds max {MAX_CONSTRAINT_DEGREE}"
            ),
            Self::ColumnOutOfBounds {
                constraint_index,
                col,
                trace_width,
            } => {
                write!(
                    f,
                    "constraint {constraint_index} references column {col} but trace_width is {trace_width}"
                )
            }
            Self::TooManyPublicInputs { count } => write!(
                f,
                "public_input_count {count} exceeds max {MAX_PUBLIC_INPUTS}"
            ),
            Self::BoundaryColumnOutOfBounds {
                boundary_index,
                col,
                trace_width,
            } => {
                write!(
                    f,
                    "boundary {boundary_index} references column {col} but trace_width is {trace_width}"
                )
            }
            Self::BoundaryPiOutOfBounds {
                boundary_index,
                pi_index,
                pi_count,
            } => {
                write!(
                    f,
                    "boundary {boundary_index} references pi[{pi_index}] but public_input_count is {pi_count}"
                )
            }
            Self::InvalidName => write!(f, "program name is empty or exceeds 256 bytes"),
            Self::ZeroWidth => write!(f, "trace width must be at least 1"),
            Self::ConstraintDegreeExceeded {
                constraint_index,
                degree,
                max_degree,
            } => {
                write!(
                    f,
                    "constraint {constraint_index} has degree {degree} which exceeds max_degree {max_degree}"
                )
            }
            Self::PiBindingOutOfBounds {
                constraint_index,
                pi_index,
                pi_count,
            } => {
                write!(
                    f,
                    "constraint {constraint_index} PiBinding references pi[{pi_index}] but public_input_count is {pi_count}"
                )
            }
        }
    }
}

impl std::error::Error for ProgramValidationError {}

impl ConstraintExpr {
    /// Compute the algebraic degree of this constraint expression.
    ///
    /// Each column reference contributes degree 1. Multiplication of sub-expressions
    /// adds their degrees. Gating adds 1 (selector * inner).
    pub fn degree(&self) -> usize {
        match self {
            Self::Equality { .. } => 1,
            Self::Multiplication { .. } => 2,
            Self::Binary { .. } => 2,
            Self::PiBinding { .. } => 1,
            Self::Transition { .. } => 1,
            Self::Polynomial { terms } => {
                terms.iter().map(|t| t.col_indices.len()).max().unwrap_or(0)
            }
            Self::Gated { inner, .. } => 1 + inner.degree(),
            Self::InvertedGated { inner, .. } => 1 + inner.degree(),
            Self::Squared { inner } => 2 * inner.degree(),
            Self::Hash { input_cols, .. } => {
                // Hash is degree 1 per column reference in the constraint check,
                // but the hash computation itself is opaque (non-algebraic helper).
                // The constraint is: hash(inputs) - output, which is degree 1.
                input_cols.len().max(1)
            }
            Self::ConditionalNonzero { .. } => {
                // selector * (value * inverse - 1): degree 3
                3
            }
            Self::AtLeastOne { flag_cols } => {
                // (1 - f0) * (1 - f1) * ... * (1 - fn): degree = n
                flag_cols.len()
            }
            Self::Hash2to1 { .. } => {
                // hash_2_to_1(a, b) - output: the hash is opaque, constraint is degree 1.
                1
            }
            Self::Hash4to1 { .. } => {
                // hash_4_to_1([a,b,c,d]) - output: the hash is opaque, constraint is degree 1.
                1
            }
        }
    }

    /// Return the maximum column index referenced by this constraint expression.
    fn max_column_index(&self) -> Option<usize> {
        match self {
            Self::Equality { col_a, col_b } => Some((*col_a).max(*col_b)),
            Self::Multiplication { a, b, output } => Some((*a).max(*b).max(*output)),
            Self::Binary { col } => Some(*col),
            Self::PiBinding { col, .. } => Some(*col),
            Self::Transition {
                next_col,
                local_col,
            } => Some((*next_col).max(*local_col)),
            Self::Polynomial { terms } => terms
                .iter()
                .flat_map(|t| t.col_indices.iter().copied())
                .max(),
            Self::Gated {
                selector_col,
                inner,
            } => {
                let inner_max = inner.max_column_index().unwrap_or(0);
                Some((*selector_col).max(inner_max))
            }
            Self::InvertedGated {
                selector_col,
                inner,
            } => {
                let inner_max = inner.max_column_index().unwrap_or(0);
                Some((*selector_col).max(inner_max))
            }
            Self::Squared { inner } => inner.max_column_index(),
            Self::Hash {
                output_col,
                input_cols,
            } => {
                let max_input = input_cols.iter().copied().max().unwrap_or(0);
                Some((*output_col).max(max_input))
            }
            Self::ConditionalNonzero {
                selector_col,
                value_col,
                inverse_col,
            } => Some((*selector_col).max(*value_col).max(*inverse_col)),
            Self::AtLeastOne { flag_cols } => flag_cols.iter().copied().max(),
            Self::Hash2to1 {
                output_col,
                input_col_a,
                input_col_b,
            } => Some((*output_col).max(*input_col_a).max(*input_col_b)),
            Self::Hash4to1 {
                output_col,
                input_cols,
            } => {
                let max_input = input_cols.iter().copied().max().unwrap_or(0);
                Some((*output_col).max(max_input))
            }
        }
    }
}

/// Recursively check that all PiBinding references within a constraint expression
/// are within the declared `pi_count`. Returns `Ok(())` if all references are valid,
/// or `Err(pi_index)` with the first out-of-bounds pi_index found.
fn check_pi_bounds_recursive(expr: &ConstraintExpr, pi_count: usize) -> Result<(), usize> {
    match expr {
        ConstraintExpr::PiBinding { pi_index, .. } => {
            if *pi_index >= pi_count {
                return Err(*pi_index);
            }
        }
        ConstraintExpr::Gated { inner, .. } => {
            check_pi_bounds_recursive(inner, pi_count)?;
        }
        ConstraintExpr::InvertedGated { inner, .. } => {
            check_pi_bounds_recursive(inner, pi_count)?;
        }
        ConstraintExpr::Squared { inner } => {
            check_pi_bounds_recursive(inner, pi_count)?;
        }
        _ => {}
    }
    Ok(())
}

impl CircuitDescriptor {
    /// Validate that this program is safe to deploy as a cell program.
    ///
    /// Checks:
    /// - Trace width within bounds (max 1024 columns)
    /// - Constraint degree within bounds (max 8)
    /// - No column index out of bounds in constraints
    /// - Public input count reasonable (max 64)
    /// - Boundary constraints reference valid rows/columns
    /// - Program name is non-empty and not too long
    pub fn validate(&self) -> Result<(), ProgramValidationError> {
        // Name validation
        if self.name.is_empty() || self.name.len() > 256 {
            return Err(ProgramValidationError::InvalidName);
        }

        // Trace width bounds
        if self.trace_width == 0 {
            return Err(ProgramValidationError::ZeroWidth);
        }
        if self.trace_width > MAX_TRACE_WIDTH {
            return Err(ProgramValidationError::TooWide {
                width: self.trace_width,
            });
        }

        // Constraint degree bounds
        if self.max_degree > MAX_CONSTRAINT_DEGREE {
            return Err(ProgramValidationError::DegreeTooHigh {
                degree: self.max_degree,
            });
        }

        // Public input count
        if self.public_input_count > MAX_PUBLIC_INPUTS {
            return Err(ProgramValidationError::TooManyPublicInputs {
                count: self.public_input_count,
            });
        }

        // Validate column indices, degree, and PiBinding bounds in constraints
        for (i, constraint) in self.constraints.iter().enumerate() {
            if let Some(max_col) = constraint.max_column_index() {
                if max_col >= self.trace_width {
                    return Err(ProgramValidationError::ColumnOutOfBounds {
                        constraint_index: i,
                        col: max_col,
                        trace_width: self.trace_width,
                    });
                }
            }

            // Check that the constraint's algebraic degree does not exceed max_degree
            let deg = constraint.degree();
            if deg > self.max_degree {
                return Err(ProgramValidationError::ConstraintDegreeExceeded {
                    constraint_index: i,
                    degree: deg,
                    max_degree: self.max_degree,
                });
            }

            // Check PiBinding references are within public_input_count (recursively)
            if let Err(pi_index) = check_pi_bounds_recursive(constraint, self.public_input_count) {
                return Err(ProgramValidationError::PiBindingOutOfBounds {
                    constraint_index: i,
                    pi_index,
                    pi_count: self.public_input_count,
                });
            }
        }

        // Validate boundary constraints
        for (i, bc) in self.boundaries.iter().enumerate() {
            match bc {
                BoundaryDef::PiBinding { col, pi_index, .. } => {
                    if *col >= self.trace_width {
                        return Err(ProgramValidationError::BoundaryColumnOutOfBounds {
                            boundary_index: i,
                            col: *col,
                            trace_width: self.trace_width,
                        });
                    }
                    if *pi_index >= self.public_input_count {
                        return Err(ProgramValidationError::BoundaryPiOutOfBounds {
                            boundary_index: i,
                            pi_index: *pi_index,
                            pi_count: self.public_input_count,
                        });
                    }
                }
                BoundaryDef::Fixed { col, .. } => {
                    if *col >= self.trace_width {
                        return Err(ProgramValidationError::BoundaryColumnOutOfBounds {
                            boundary_index: i,
                            col: *col,
                            trace_width: self.trace_width,
                        });
                    }
                }
            }
        }

        Ok(())
    }
}

// ============================================================================
// Program Errors
// ============================================================================

/// Errors that can occur during program deployment, proof generation, or verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProgramError {
    /// The program descriptor failed validation.
    ValidationFailed(ProgramValidationError),
    /// The requested program (by VK hash) is not in the registry.
    UnknownProgram,
    /// Proof deserialization failed.
    InvalidProof(String),
    /// Proof verification failed.
    VerificationFailed(String),
    /// Witness is missing required column data.
    MissingWitness { column: String },
    /// Witness column has wrong length.
    WitnessLengthMismatch {
        column: String,
        expected: usize,
        got: usize,
    },
    /// Trace length must be a power of two and >= 2.
    InvalidTraceLength { len: usize },
}

impl std::fmt::Display for ProgramError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ValidationFailed(e) => write!(f, "program validation failed: {e}"),
            Self::UnknownProgram => write!(f, "unknown program (VK hash not found in registry)"),
            Self::InvalidProof(msg) => write!(f, "invalid proof: {msg}"),
            Self::VerificationFailed(msg) => write!(f, "verification failed: {msg}"),
            Self::MissingWitness { column } => write!(f, "witness missing column: {column}"),
            Self::WitnessLengthMismatch {
                column,
                expected,
                got,
            } => {
                write!(
                    f,
                    "witness column '{column}' has length {got}, expected {expected}"
                )
            }
            Self::InvalidTraceLength { len } => {
                write!(f, "trace length {len} must be a power of two and >= 2")
            }
        }
    }
}

impl std::error::Error for ProgramError {}

impl From<ProgramValidationError> for ProgramError {
    fn from(e: ProgramValidationError) -> Self {
        Self::ValidationFailed(e)
    }
}

// ============================================================================
// Cell Program: deployable circuit descriptor
// ============================================================================

/// A deployable cell program (serialized circuit descriptor).
///
/// Users submit cell programs as serialized `CircuitDescriptor`s. The descriptor
/// defines valid state transitions for a sovereign cell. The `vk_hash` is derived
/// deterministically from the descriptor and serves as the program's identity.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CellProgram {
    /// The circuit descriptor (defines valid transitions).
    pub descriptor: CircuitDescriptor,
    /// Program version (for upgrade/migration tracking).
    pub version: u32,
    /// The verification key hash (derived from the descriptor).
    pub vk_hash: [u8; 32],
}

impl CellProgram {
    /// Create a new CellProgram from a descriptor, computing the VK hash.
    pub fn new(descriptor: CircuitDescriptor, version: u32) -> Self {
        let vk_hash = Self::compute_vk_hash(&descriptor);
        Self {
            descriptor,
            version,
            vk_hash,
        }
    }

    /// Compute the verification key hash from the descriptor.
    ///
    /// This is a deterministic hash of the serialized descriptor, serving as the
    /// program's unique identity. Two programs with identical descriptors produce
    /// the same VK hash.
    pub fn compute_vk_hash(descriptor: &CircuitDescriptor) -> [u8; 32] {
        let serialized = postcard::to_allocvec(descriptor)
            .expect("CircuitDescriptor serialization should not fail");
        *blake3::hash(&serialized).as_bytes()
    }

    /// Verify that the stored vk_hash matches the descriptor.
    ///
    /// Call this after deserialization to detect tampering.
    pub fn verify_integrity(&self) -> bool {
        self.vk_hash == Self::compute_vk_hash(&self.descriptor)
    }

    /// Verify that a STARK proof demonstrates a valid state transition under this program.
    ///
    /// The public inputs should encode the old and new state commitments so that
    /// the AIR constraints bind the proof to a specific transition.
    pub fn verify_transition(
        &self,
        public_inputs: &[BabyBear],
        proof_bytes: &[u8],
    ) -> Result<(), ProgramError> {
        let circuit = DslCircuit {
            descriptor: self.descriptor.clone(),
        };
        let proof =
            stark::proof_from_bytes(proof_bytes).map_err(|e| ProgramError::InvalidProof(e))?;
        stark::verify(&circuit, &proof, public_inputs)
            .map_err(|e| ProgramError::VerificationFailed(e))
    }

    /// Generate an execution trace for this program from provided witness values.
    ///
    /// The witness maps column names to their values for each row. The trace length
    /// must be a power of two and >= 2.
    pub fn generate_trace(
        &self,
        witness_values: &HashMap<String, Vec<BabyBear>>,
        num_rows: usize,
    ) -> Result<Vec<Vec<BabyBear>>, ProgramError> {
        // Validate trace length
        if num_rows < 2 || !num_rows.is_power_of_two() {
            return Err(ProgramError::InvalidTraceLength { len: num_rows });
        }

        let mut trace = Vec::with_capacity(num_rows);

        for row_idx in 0..num_rows {
            let mut row = vec![BabyBear::ZERO; self.descriptor.trace_width];
            for col_def in &self.descriptor.columns {
                if let Some(values) = witness_values.get(&col_def.name) {
                    if values.len() != num_rows {
                        return Err(ProgramError::WitnessLengthMismatch {
                            column: col_def.name.clone(),
                            expected: num_rows,
                            got: values.len(),
                        });
                    }
                    row[col_def.index] = values[row_idx];
                }
                // Columns not in witness default to ZERO (padding columns)
            }
            trace.push(row);
        }

        Ok(trace)
    }

    /// Prove a state transition under this program.
    ///
    /// Given witness values for all columns, generates a trace and produces a
    /// STARK proof. The public inputs are provided separately and typically encode
    /// old/new state commitments.
    pub fn prove_transition(
        &self,
        witness_values: &HashMap<String, Vec<BabyBear>>,
        num_rows: usize,
        public_inputs: &[BabyBear],
    ) -> Result<Vec<u8>, ProgramError> {
        let trace = self.generate_trace(witness_values, num_rows)?;
        let circuit = DslCircuit {
            descriptor: self.descriptor.clone(),
        };
        let proof = stark::prove(&circuit, &trace, public_inputs);
        Ok(stark::proof_to_bytes(&proof))
    }
}

// ============================================================================
// Program Registry: VK → program lookup
// ============================================================================

/// Registry mapping verification key hashes to deployed programs.
///
/// This serves as the "code store" for the smart contract runtime. Programs are
/// validated before deployment and can be looked up by their VK hash for
/// verification of proof-carrying turns.
#[derive(Debug, Clone, Default)]
pub struct ProgramRegistry {
    programs: HashMap<[u8; 32], CellProgram>,
}

impl ProgramRegistry {
    /// Create an empty program registry.
    pub fn new() -> Self {
        Self {
            programs: HashMap::new(),
        }
    }

    /// Deploy a program to the registry after validation.
    ///
    /// Returns the VK hash on success. Rejects programs that fail validation.
    /// If a program with the same VK hash already exists, this is a no-op
    /// (idempotent deployment).
    pub fn deploy(&mut self, program: CellProgram) -> Result<[u8; 32], ProgramError> {
        // Validate the descriptor
        program.descriptor.validate()?;

        // Verify the VK hash is correctly computed
        let computed_vk = CellProgram::compute_vk_hash(&program.descriptor);
        if computed_vk != program.vk_hash {
            return Err(ProgramError::InvalidProof(
                "VK hash does not match descriptor".to_string(),
            ));
        }

        let vk_hash = program.vk_hash;
        self.programs.insert(vk_hash, program);
        Ok(vk_hash)
    }

    /// Look up a deployed program by its VK hash.
    pub fn get(&self, vk_hash: &[u8; 32]) -> Option<&CellProgram> {
        self.programs.get(vk_hash)
    }

    /// Check if a program is deployed.
    pub fn contains(&self, vk_hash: &[u8; 32]) -> bool {
        self.programs.contains_key(vk_hash)
    }

    /// Number of deployed programs.
    pub fn len(&self) -> usize {
        self.programs.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.programs.is_empty()
    }

    /// Verify a proof-carrying transition against a deployed program.
    ///
    /// This is the primary entry point for the executor: given a VK hash from a
    /// sovereign cell, look up the program and verify the proof.
    pub fn verify_with_program(
        &self,
        vk_hash: &[u8; 32],
        public_inputs: &[BabyBear],
        proof_bytes: &[u8],
    ) -> Result<(), ProgramError> {
        let program = self.get(vk_hash).ok_or(ProgramError::UnknownProgram)?;
        program.verify_transition(public_inputs, proof_bytes)
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
            name: "pyana-sovereign-transition-v1".to_string(),
            trace_width: 6,
            max_degree: 2,
            columns: vec![
                ColumnDef {
                    name: "old_balance".to_string(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "transfer_amount".to_string(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "new_balance".to_string(),
                    index: 2,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "direction".to_string(),
                    index: 3,
                    kind: ColumnKind::Binary,
                },
                ColumnDef {
                    name: "pad0".to_string(),
                    index: 4,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "pad1".to_string(),
                    index: 5,
                    kind: ColumnKind::Value,
                },
            ],
            constraints: vec![
                // c1: direction is boolean
                ConstraintExpr::Binary { col: 3 },
                // c2: balance conservation polynomial
                // new_balance - old_balance - transfer_amount + 2*direction*transfer_amount == 0
                ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![2],
                        }, // +new_balance
                        PolyTerm {
                            coeff: BabyBear::new(pyana_circuit::field::BABYBEAR_P - 1),
                            col_indices: vec![0],
                        }, // -old_balance
                        PolyTerm {
                            coeff: BabyBear::new(pyana_circuit::field::BABYBEAR_P - 1),
                            col_indices: vec![1],
                        }, // -transfer_amount
                        PolyTerm {
                            coeff: BabyBear::new(2),
                            col_indices: vec![3, 1],
                        }, // +2*direction*transfer_amount
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
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Invalid trace must produce nonzero constraint"
        );
    }

    #[test]
    fn dsl_circuit_prove_and_verify() {
        use pyana_circuit::sovereign_transition_air::{
            SOVEREIGN_PUBLIC_INPUTS, bytes32_to_babybear,
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
        assert!(
            result.is_ok(),
            "DslCircuit prove/verify failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn dsl_circuit_incoming_transfer() {
        use pyana_circuit::sovereign_transition_air::{
            SOVEREIGN_PUBLIC_INPUTS, bytes32_to_babybear,
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
        assert!(
            result.is_ok(),
            "DslCircuit incoming transfer failed: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Smart Contract Runtime Tests
    // ========================================================================

    #[test]
    fn deploy_program_and_get_vk_hash() {
        let descriptor = sovereign_transfer_descriptor();
        let program = CellProgram::new(descriptor.clone(), 1);

        // VK hash is deterministic
        let expected_vk = CellProgram::compute_vk_hash(&descriptor);
        assert_eq!(program.vk_hash, expected_vk);
        assert!(program.verify_integrity());

        // Deploy to registry
        let mut registry = ProgramRegistry::new();
        let vk_hash = registry.deploy(program).unwrap();
        assert_eq!(vk_hash, expected_vk);
        assert_eq!(registry.len(), 1);
        assert!(registry.contains(&vk_hash));

        // Retrieve
        let retrieved = registry.get(&vk_hash).unwrap();
        assert_eq!(retrieved.version, 1);
        assert_eq!(retrieved.descriptor.name, "pyana-sovereign-transition-v1");
    }

    #[test]
    fn prove_and_verify_via_registry() {
        use pyana_circuit::sovereign_transition_air::{
            SOVEREIGN_PUBLIC_INPUTS, bytes32_to_babybear,
        };

        let descriptor = sovereign_transfer_descriptor();
        let program = CellProgram::new(descriptor, 1);

        let mut registry = ProgramRegistry::new();
        let vk_hash = registry.deploy(program.clone()).unwrap();

        // Build witness
        let old_balance = 1000u64;
        let transfer_amount = 100u64;
        let direction = 1u32; // outgoing
        let new_balance = old_balance - transfer_amount;
        let num_rows = 2;

        let mut witness = HashMap::new();
        witness.insert(
            "old_balance".to_string(),
            vec![BabyBear::from_u64(old_balance); num_rows],
        );
        witness.insert(
            "transfer_amount".to_string(),
            vec![BabyBear::from_u64(transfer_amount); num_rows],
        );
        witness.insert(
            "new_balance".to_string(),
            vec![BabyBear::from_u64(new_balance); num_rows],
        );
        witness.insert(
            "direction".to_string(),
            vec![BabyBear::new(direction); num_rows],
        );

        // Build public inputs
        let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
        public_inputs.extend(bytes32_to_babybear(&[1u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[2u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[3u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[4u8; 32]));

        // Prove
        let proof_bytes = program
            .prove_transition(&witness, num_rows, &public_inputs)
            .unwrap();
        assert!(!proof_bytes.is_empty());

        // Verify via registry
        let result = registry.verify_with_program(&vk_hash, &public_inputs, &proof_bytes);
        assert!(
            result.is_ok(),
            "Registry verification failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn invalid_program_too_wide_rejected() {
        let mut descriptor = sovereign_transfer_descriptor();
        descriptor.trace_width = MAX_TRACE_WIDTH + 1;

        let program = CellProgram::new(descriptor, 1);
        let mut registry = ProgramRegistry::new();
        let result = registry.deploy(program);
        assert!(result.is_err());
        match result.unwrap_err() {
            ProgramError::ValidationFailed(ProgramValidationError::TooWide { width }) => {
                assert_eq!(width, MAX_TRACE_WIDTH + 1);
            }
            other => panic!("Expected TooWide error, got: {:?}", other),
        }
    }

    #[test]
    fn invalid_program_degree_too_high_rejected() {
        let mut descriptor = sovereign_transfer_descriptor();
        descriptor.max_degree = MAX_CONSTRAINT_DEGREE + 1;

        let program = CellProgram::new(descriptor, 1);
        let mut registry = ProgramRegistry::new();
        let result = registry.deploy(program);
        assert!(result.is_err());
        match result.unwrap_err() {
            ProgramError::ValidationFailed(ProgramValidationError::DegreeTooHigh { degree }) => {
                assert_eq!(degree, MAX_CONSTRAINT_DEGREE + 1);
            }
            other => panic!("Expected DegreeTooHigh error, got: {:?}", other),
        }
    }

    #[test]
    fn invalid_program_column_out_of_bounds_rejected() {
        let mut descriptor = sovereign_transfer_descriptor();
        // Add a constraint referencing column 99 in a 6-wide trace
        descriptor
            .constraints
            .push(ConstraintExpr::Binary { col: 99 });

        let program = CellProgram::new(descriptor, 1);
        let mut registry = ProgramRegistry::new();
        let result = registry.deploy(program);
        assert!(result.is_err());
        match result.unwrap_err() {
            ProgramError::ValidationFailed(ProgramValidationError::ColumnOutOfBounds {
                col,
                ..
            }) => {
                assert_eq!(col, 99);
            }
            other => panic!("Expected ColumnOutOfBounds error, got: {:?}", other),
        }
    }

    #[test]
    fn invalid_program_too_many_public_inputs_rejected() {
        let mut descriptor = sovereign_transfer_descriptor();
        descriptor.public_input_count = MAX_PUBLIC_INPUTS + 1;

        let program = CellProgram::new(descriptor, 1);
        let mut registry = ProgramRegistry::new();
        let result = registry.deploy(program);
        assert!(result.is_err());
        match result.unwrap_err() {
            ProgramError::ValidationFailed(ProgramValidationError::TooManyPublicInputs {
                count,
            }) => {
                assert_eq!(count, MAX_PUBLIC_INPUTS + 1);
            }
            other => panic!("Expected TooManyPublicInputs error, got: {:?}", other),
        }
    }

    #[test]
    fn wrong_vk_hash_verification_fails() {
        use pyana_circuit::sovereign_transition_air::{
            SOVEREIGN_PUBLIC_INPUTS, bytes32_to_babybear,
        };

        let descriptor = sovereign_transfer_descriptor();
        let program = CellProgram::new(descriptor, 1);

        let mut registry = ProgramRegistry::new();
        let _vk_hash = registry.deploy(program).unwrap();

        // Try to verify with a wrong VK hash
        let wrong_vk = [0xFFu8; 32];
        let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
        public_inputs.extend(bytes32_to_babybear(&[1u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[2u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[3u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[4u8; 32]));

        let result = registry.verify_with_program(&wrong_vk, &public_inputs, &[0u8; 10]);
        assert_eq!(result.unwrap_err(), ProgramError::UnknownProgram);
    }

    #[test]
    fn valid_proof_under_correct_program_passes() {
        use pyana_circuit::sovereign_transition_air::{
            SOVEREIGN_PUBLIC_INPUTS, bytes32_to_babybear,
        };

        let descriptor = sovereign_transfer_descriptor();
        let program = CellProgram::new(descriptor, 1);

        let mut registry = ProgramRegistry::new();
        let vk_hash = registry.deploy(program.clone()).unwrap();

        // Generate a valid proof
        let old_balance = 500u64;
        let transfer_amount = 200u64;
        let direction = 0u32; // incoming => new = 700
        let new_balance = old_balance + transfer_amount;
        let num_rows = 2;

        let mut witness = HashMap::new();
        witness.insert(
            "old_balance".to_string(),
            vec![BabyBear::from_u64(old_balance); num_rows],
        );
        witness.insert(
            "transfer_amount".to_string(),
            vec![BabyBear::from_u64(transfer_amount); num_rows],
        );
        witness.insert(
            "new_balance".to_string(),
            vec![BabyBear::from_u64(new_balance); num_rows],
        );
        witness.insert(
            "direction".to_string(),
            vec![BabyBear::new(direction); num_rows],
        );

        let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
        public_inputs.extend(bytes32_to_babybear(&[10u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[11u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[12u8; 32]));
        public_inputs.extend(bytes32_to_babybear(&[13u8; 32]));

        let proof_bytes = program
            .prove_transition(&witness, num_rows, &public_inputs)
            .unwrap();

        // Verify via registry — should pass
        let result = registry.verify_with_program(&vk_hash, &public_inputs, &proof_bytes);
        assert!(result.is_ok(), "Valid proof rejected: {:?}", result.err());
    }

    #[test]
    fn descriptor_serialization_roundtrip() {
        let descriptor = sovereign_transfer_descriptor();
        let serialized = postcard::to_allocvec(&descriptor).unwrap();
        let deserialized: CircuitDescriptor = postcard::from_bytes(&serialized).unwrap();

        assert_eq!(deserialized.name, descriptor.name);
        assert_eq!(deserialized.trace_width, descriptor.trace_width);
        assert_eq!(deserialized.max_degree, descriptor.max_degree);
        assert_eq!(deserialized.columns.len(), descriptor.columns.len());
        assert_eq!(deserialized.constraints.len(), descriptor.constraints.len());
        assert_eq!(
            deserialized.public_input_count,
            descriptor.public_input_count
        );

        // VK hash should be identical after roundtrip
        let vk_before = CellProgram::compute_vk_hash(&descriptor);
        let vk_after = CellProgram::compute_vk_hash(&deserialized);
        assert_eq!(vk_before, vk_after);
    }

    #[test]
    fn cell_program_serialization_roundtrip() {
        let descriptor = sovereign_transfer_descriptor();
        let program = CellProgram::new(descriptor, 1);

        let serialized = postcard::to_allocvec(&program).unwrap();
        let deserialized: CellProgram = postcard::from_bytes(&serialized).unwrap();

        assert_eq!(deserialized.vk_hash, program.vk_hash);
        assert_eq!(deserialized.version, program.version);
        assert!(deserialized.verify_integrity());
    }

    #[test]
    fn validation_boundary_out_of_bounds() {
        let mut descriptor = sovereign_transfer_descriptor();
        descriptor.boundaries.push(BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: 100, // out of bounds for trace_width=6
            value: BabyBear::ONE,
        });

        let result = descriptor.validate();
        assert!(result.is_err());
        match result.unwrap_err() {
            ProgramValidationError::BoundaryColumnOutOfBounds { col, .. } => {
                assert_eq!(col, 100);
            }
            other => panic!("Expected BoundaryColumnOutOfBounds, got: {:?}", other),
        }
    }

    #[test]
    fn validation_boundary_pi_out_of_bounds() {
        let mut descriptor = sovereign_transfer_descriptor();
        descriptor.boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: 0,
            pi_index: 999, // out of bounds for public_input_count=32
        });

        let result = descriptor.validate();
        assert!(result.is_err());
        match result.unwrap_err() {
            ProgramValidationError::BoundaryPiOutOfBounds { pi_index, .. } => {
                assert_eq!(pi_index, 999);
            }
            other => panic!("Expected BoundaryPiOutOfBounds, got: {:?}", other),
        }
    }

    #[test]
    fn witness_length_mismatch_error() {
        let descriptor = sovereign_transfer_descriptor();
        let program = CellProgram::new(descriptor, 1);

        let mut witness = HashMap::new();
        // Provide 3 values for a 2-row trace
        witness.insert("old_balance".to_string(), vec![BabyBear::ONE; 3]);

        let result = program.generate_trace(&witness, 2);
        assert!(result.is_err());
        match result.unwrap_err() {
            ProgramError::WitnessLengthMismatch {
                column,
                expected,
                got,
            } => {
                assert_eq!(column, "old_balance");
                assert_eq!(expected, 2);
                assert_eq!(got, 3);
            }
            other => panic!("Expected WitnessLengthMismatch, got: {:?}", other),
        }
    }

    #[test]
    fn invalid_trace_length_error() {
        let descriptor = sovereign_transfer_descriptor();
        let program = CellProgram::new(descriptor, 1);

        // Non-power-of-two
        let result = program.generate_trace(&HashMap::new(), 3);
        assert!(matches!(
            result,
            Err(ProgramError::InvalidTraceLength { len: 3 })
        ));

        // Too small
        let result = program.generate_trace(&HashMap::new(), 1);
        assert!(matches!(
            result,
            Err(ProgramError::InvalidTraceLength { len: 1 })
        ));
    }

    #[test]
    fn idempotent_deployment() {
        let descriptor = sovereign_transfer_descriptor();
        let program = CellProgram::new(descriptor, 1);
        let vk_hash = program.vk_hash;

        let mut registry = ProgramRegistry::new();
        let h1 = registry.deploy(program.clone()).unwrap();
        let h2 = registry.deploy(program).unwrap();
        assert_eq!(h1, h2);
        assert_eq!(h1, vk_hash);
        assert_eq!(registry.len(), 1);
    }

    #[test]
    fn tampered_vk_hash_rejected() {
        let descriptor = sovereign_transfer_descriptor();
        let mut program = CellProgram::new(descriptor, 1);
        // Tamper with the VK hash
        program.vk_hash[0] ^= 0xFF;

        let mut registry = ProgramRegistry::new();
        let result = registry.deploy(program);
        assert!(result.is_err());
        match result.unwrap_err() {
            ProgramError::InvalidProof(msg) => {
                assert!(msg.contains("VK hash does not match"));
            }
            other => panic!("Expected InvalidProof, got: {:?}", other),
        }
    }
}
