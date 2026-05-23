//! Programmable predicate compilation pipeline.
//!
//! Turns a predicate specification into the appropriate AIR proof(s).
//! This implements Stage 1 of the programmable predicates compilation pipeline
//! from `docs/programmable-predicates.md`:
//!
//! ```text
//! PredicateProgram
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  Program Analyzer   │  Determine which built-ins are needed
//! └─────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  AIR Selector       │  Map each built-in to its specialized AIR
//! └─────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  Witness Generator  │  Fill traces from private state
//! └─────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  Proof Compositor   │  Compose sub-proofs into a single proof
//! └─────────────────────┘
//!     │
//!     ▼
//! PredicateProof (verifiable by anyone)
//! ```
//!
//! # Overview
//!
//! A `PredicateProgram` is a structured expression tree over leaf predicates
//! (range checks, membership, temporal continuity, relational comparisons,
//! committed thresholds) composed with boolean operators (AND, OR, NOT, Threshold).
//!
//! The compiler analyzes the program, maps each leaf to its specialized AIR,
//! and determines whether the program can be flattened into a single
//! `CompoundPredicateAir` or requires multi-AIR composition.
//!
//! # Compilation Strategy
//!
//! - **Single range leaf**: Dispatches directly to `PredicateAir`.
//! - **Multiple range leaves combined with AND/OR/Threshold**: Flattens into
//!   `CompoundPredicateAir` (up to 8 sub-predicates).
//! - **Temporal leaves**: Each becomes an independent `TemporalPredicateAir`.
//! - **Mixed AIR types or nested compositions**: Multi-AIR composition with
//!   a boolean formula over sub-proofs.

use std::collections::HashMap;

use crate::committed_threshold::{
    CommittedThresholdProof, CommittedThresholdWitness, compute_threshold_commitment,
    prove_committed_threshold as prove_committed_threshold_air,
    verify_committed_threshold as verify_committed_threshold_air,
};
use crate::compound_predicate_air::{
    BooleanFormula, CompoundPredicateProof, MAX_COMPOUND_PREDICATES, prove_compound_predicate,
    verify_compound_predicate,
};
use crate::field::BabyBear;
use crate::poseidon2;
use crate::predicate_air::{
    PredicateProof, PredicateType, PredicateWitness, compute_fact_commitment, prove_predicate,
    verify_predicate,
};
use crate::relational_predicate_air::{
    RelationType, RelationalPredicateProof, RelationalPredicateWitness, compute_value_commitment,
    prove_relational as prove_relational_air, verify_relational as verify_relational_air,
};
#[cfg(feature = "plonky3")]
use crate::temporal_predicate_dsl::p3_temporal::{
    P3TemporalPredicateProof, prove_temporal_predicate_p3, verify_temporal_predicate_p3,
};
use crate::temporal_predicate_dsl::{
    TemporalPredicateProof, prove_temporal_predicate, verify_temporal_predicate,
};

// =============================================================================
// Program Representation
// =============================================================================

/// A predicate expression tree — the "program" that gets compiled to AIR proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PredicateExpr {
    // ─── Leaf predicates (dispatch to specific AIRs) ───
    /// Range comparison: `attribute <op> threshold`.
    /// Dispatches to `PredicateAir`.
    Range {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
    },

    /// Set membership: `attribute IN committed_set`.
    /// Dispatches to `MerklePoseidon2StarkAir`.
    Membership {
        attribute: String,
        set_commitment: BabyBear,
    },

    /// Temporal continuity: `attribute <op> threshold for min_blocks consecutive steps`.
    /// Dispatches to `TemporalPredicateAir`.
    Temporal {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
        min_blocks: u64,
    },

    /// Relational comparison between two parties' committed values.
    /// Dispatches to `RelationalPredicateAir`.
    Relational {
        my_attribute: String,
        their_commitment: BabyBear,
        relation: RelationType,
    },

    /// Private threshold comparison where the threshold is committed.
    /// Dispatches to `CommittedThresholdAir`.
    CommittedThreshold {
        attribute: String,
        threshold_commitment: BabyBear,
    },

    /// Arithmetic predicate: an expression over multiple inputs satisfies a comparison.
    /// Dispatches to `ArithmeticPredicateAir`.
    ///
    /// Example: `balance_a + balance_b >= 2000`
    Arithmetic {
        /// The attribute names that serve as inputs to the expression.
        inputs: Vec<String>,
        /// The arithmetic expression over the inputs (Var(0), Var(1), etc.).
        expression: crate::arithmetic_predicate_air::ArithExpr,
        /// The predicate to prove about the expression result.
        predicate: crate::arithmetic_predicate_air::ArithPredicate,
    },

    /// Non-membership: `attribute NOT IN property_set`.
    /// Dispatches to `AccumulatorNonMembershipAir` (generalized from non-revocation).
    ///
    /// This is the sound way to express `NOT(Membership { ... })` -- instead of
    /// trying to negate a proof (which is unsound), we use the polynomial-evaluation
    /// accumulator to directly prove non-membership.
    NonMembership {
        /// The attribute whose hash must NOT appear in the set.
        attribute: String,
        /// Identifier for the property set (domain-separated).
        set_id: BabyBear,
    },

    // ─── Negation extensions (no new AIR needed) ───
    /// Inequality: prove `attribute != value`.
    /// Compiles to `ArithmeticPredicateAir` with `ExprNeq`.
    Neq { attribute: String, value: u64 },

    /// Range exclusion: prove `value NOT IN [low, high]`.
    /// Strategy: compiles to `Or(Lt(low), Gt(high))` using existing range predicates.
    NotInRange {
        attribute: String,
        low: u64,
        high: u64,
    },

    /// Threshold below: prove that FEWER than `max_k` of the given predicates hold.
    /// Purely compositional: during proving, count how many sub-predicates succeed,
    /// reject (produce no proof) if count >= max_k. Verifier checks fewer than max_k proofs.
    ThresholdBelow {
        max_k: usize,
        predicates: Vec<PredicateExpr>,
    },

    // ─── Composition operators ───
    /// All sub-predicates must hold.
    And(Vec<PredicateExpr>),

    /// At least one sub-predicate must hold.
    Or(Vec<PredicateExpr>),

    /// The negation of a sub-predicate.
    Not(Box<PredicateExpr>),

    /// At least `k` of the given predicates must hold.
    Threshold {
        k: usize,
        predicates: Vec<PredicateExpr>,
    },
}

/// A predicate program: an expression tree with resource limits.
#[derive(Clone, Debug)]
pub struct PredicateProgram {
    /// The predicate expression to evaluate and prove.
    pub expr: PredicateExpr,
    /// Maximum nesting depth (for resource limiting).
    pub max_depth: usize,
}

impl PredicateProgram {
    /// Create a new predicate program with the given expression and depth limit.
    pub fn new(expr: PredicateExpr, max_depth: usize) -> Self {
        Self { expr, max_depth }
    }

    /// Create a predicate program with the default depth limit (8).
    pub fn with_default_depth(expr: PredicateExpr) -> Self {
        Self { expr, max_depth: 8 }
    }
}

// =============================================================================
// Compilation Output
// =============================================================================

/// The type of AIR that a leaf predicate compiles to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AirType {
    /// `PredicateAir` — single range/comparison check.
    Range,
    /// `CompoundPredicateAir` — boolean combination of range checks.
    Compound,
    /// `TemporalPredicateAir` — predicate held over N steps.
    Temporal,
    /// `RelationalPredicateAir` — two-party value comparison.
    Relational,
    /// `CommittedThresholdAir` — value >= committed threshold.
    CommittedThreshold,
    /// `MerklePoseidon2StarkAir` — set membership proof.
    Membership,
    /// `ArithmeticPredicateAir` — arithmetic expression over multiple inputs.
    Arithmetic,
    /// `AccumulatorNonMembershipAir` — accumulator-based non-membership proof.
    NonMembership,
}

/// Specification of what witness data is needed for a particular compiled sub-proof.
#[derive(Clone, Debug, PartialEq)]
pub enum WitnessSpec {
    /// Single range predicate: needs (attribute_name, predicate_type, threshold).
    Range {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
    },
    /// Temporal predicate: needs values at each step + state roots.
    Temporal {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
        min_blocks: u64,
    },
    /// Relational: needs my value + their commitment.
    Relational {
        my_attribute: String,
        their_commitment: BabyBear,
        relation: RelationType,
    },
    /// Committed threshold: needs my value + threshold + blinding.
    CommittedThreshold {
        attribute: String,
        threshold_commitment: BabyBear,
    },
    /// Membership: needs value + Merkle path.
    Membership {
        attribute: String,
        set_commitment: BabyBear,
    },
    /// Arithmetic: needs multiple attribute values + expression + predicate.
    Arithmetic {
        inputs: Vec<String>,
        expression: crate::arithmetic_predicate_air::ArithExpr,
        predicate: crate::arithmetic_predicate_air::ArithPredicate,
    },
    /// Non-membership: needs element hash + set parameters.
    NonMembership { attribute: String, set_id: BabyBear },
}

/// The compiled form of a predicate program — a plan for proof generation.
#[derive(Clone, Debug, PartialEq)]
pub enum CompiledPredicate {
    /// A single leaf that maps to one AIR instance.
    Single {
        air_type: AirType,
        witness_spec: WitnessSpec,
    },
    /// A compound predicate that uses `CompoundPredicateAir` to prove
    /// a boolean formula over multiple range sub-predicates in one proof.
    CompoundRange {
        /// The individual range sub-predicates (flattened from the expression tree).
        sub_predicates: Vec<WitnessSpec>,
        /// The boolean formula combining them.
        formula: BooleanFormula,
    },
    /// A multi-AIR composition: multiple independent sub-proofs combined
    /// by a boolean formula. This is used when the program mixes AIR types
    /// (e.g., range + temporal) that cannot be flattened into one AIR.
    Composite {
        sub_proofs: Vec<CompiledPredicate>,
        formula: CompositeFormula,
    },
}

/// Boolean formula for multi-AIR composition (over sub-proof results).
#[derive(Clone, Debug, PartialEq)]
pub enum CompositeFormula {
    /// All sub-proofs must verify.
    And,
    /// At least one sub-proof must verify.
    Or,
    /// At least `k` sub-proofs must verify.
    Threshold(usize),
    /// Fewer than `k` sub-proofs verify (the inverse of Threshold).
    ThresholdBelow(usize),
    /// Negate the single sub-proof's result.
    Not,
}

// =============================================================================
// Compilation Errors
// =============================================================================

/// Errors that can occur during predicate compilation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// The program exceeds the maximum allowed nesting depth.
    DepthExceeded { max: usize, actual: usize },
    /// The program has too many leaves for a compound AIR (> MAX_COMPOUND_PREDICATES).
    TooManyPredicates { max: usize, actual: usize },
    /// The program is empty (no predicates to prove).
    EmptyProgram,
    /// A NOT operator was applied to a non-single predicate (unsupported in current AIR).
    UnsupportedNot,
    /// Threshold `k` is zero or exceeds the number of predicates.
    InvalidThreshold { k: usize, n: usize },
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DepthExceeded { max, actual } => {
                write!(f, "program depth {actual} exceeds maximum {max}")
            }
            Self::TooManyPredicates { max, actual } => {
                write!(f, "program has {actual} predicates, maximum is {max}")
            }
            Self::EmptyProgram => write!(f, "empty predicate program"),
            Self::UnsupportedNot => {
                write!(
                    f,
                    "NOT is not supported: requires MPC-in-the-head proof of non-satisfaction (not yet implemented). Use comparison flipping (GTE -> LT) instead."
                )
            }
            Self::InvalidThreshold { k, n } => {
                write!(f, "threshold k={k} is invalid for {n} predicates")
            }
        }
    }
}

// =============================================================================
// Compiler
// =============================================================================

/// Compile a predicate program into a proof plan.
///
/// The compiler:
/// 1. Validates depth/size limits.
/// 2. Flattens nested AND/OR into `CompoundPredicateAir` where possible
///    (when all leaves are range predicates and count <= MAX_COMPOUND_PREDICATES).
/// 3. Identifies which AIRs are needed.
/// 4. Returns a compilation plan (`CompiledPredicate`).
pub fn compile_predicate(program: &PredicateProgram) -> Result<CompiledPredicate, CompileError> {
    // Validate depth.
    let actual_depth = compute_depth(&program.expr);
    if actual_depth > program.max_depth {
        return Err(CompileError::DepthExceeded {
            max: program.max_depth,
            actual: actual_depth,
        });
    }

    compile_expr(&program.expr)
}

/// Compute the nesting depth of an expression.
fn compute_depth(expr: &PredicateExpr) -> usize {
    match expr {
        // Leaves have depth 1.
        PredicateExpr::Range { .. }
        | PredicateExpr::Membership { .. }
        | PredicateExpr::NonMembership { .. }
        | PredicateExpr::Temporal { .. }
        | PredicateExpr::Relational { .. }
        | PredicateExpr::CommittedThreshold { .. }
        | PredicateExpr::Arithmetic { .. }
        | PredicateExpr::Neq { .. }
        | PredicateExpr::NotInRange { .. } => 1,

        // Composition operators have depth = 1 + max(children).
        PredicateExpr::And(children) | PredicateExpr::Or(children) => {
            1 + children.iter().map(compute_depth).max().unwrap_or(0)
        }
        PredicateExpr::Not(inner) => 1 + compute_depth(inner),
        PredicateExpr::Threshold { predicates, .. }
        | PredicateExpr::ThresholdBelow {
            max_k: _,
            predicates,
        } => 1 + predicates.iter().map(compute_depth).max().unwrap_or(0),
    }
}

/// Compile a single expression node.
fn compile_expr(expr: &PredicateExpr) -> Result<CompiledPredicate, CompileError> {
    match expr {
        // ─── Leaf nodes ───
        PredicateExpr::Range {
            attribute,
            predicate_type,
            threshold,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Range,
            witness_spec: WitnessSpec::Range {
                attribute: attribute.clone(),
                predicate_type: *predicate_type,
                threshold: *threshold,
            },
        }),

        PredicateExpr::Membership {
            attribute,
            set_commitment,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Membership,
            witness_spec: WitnessSpec::Membership {
                attribute: attribute.clone(),
                set_commitment: *set_commitment,
            },
        }),

        PredicateExpr::Temporal {
            attribute,
            predicate_type,
            threshold,
            min_blocks,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Temporal,
            witness_spec: WitnessSpec::Temporal {
                attribute: attribute.clone(),
                predicate_type: *predicate_type,
                threshold: *threshold,
                min_blocks: *min_blocks,
            },
        }),

        PredicateExpr::Relational {
            my_attribute,
            their_commitment,
            relation,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Relational,
            witness_spec: WitnessSpec::Relational {
                my_attribute: my_attribute.clone(),
                their_commitment: *their_commitment,
                relation: *relation,
            },
        }),

        PredicateExpr::CommittedThreshold {
            attribute,
            threshold_commitment,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::CommittedThreshold,
            witness_spec: WitnessSpec::CommittedThreshold {
                attribute: attribute.clone(),
                threshold_commitment: *threshold_commitment,
            },
        }),

        PredicateExpr::Arithmetic {
            inputs,
            expression,
            predicate,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Arithmetic,
            witness_spec: WitnessSpec::Arithmetic {
                inputs: inputs.clone(),
                expression: expression.clone(),
                predicate: predicate.clone(),
            },
        }),

        PredicateExpr::NonMembership { attribute, set_id } => Ok(CompiledPredicate::Single {
            air_type: AirType::NonMembership,
            witness_spec: WitnessSpec::NonMembership {
                attribute: attribute.clone(),
                set_id: *set_id,
            },
        }),

        // ─── Negation extensions ───
        PredicateExpr::Neq { attribute, value } => {
            // Compile as ArithmeticPredicateAir with ExprNeq.
            use crate::arithmetic_predicate_air::{ArithExpr, ArithPredicate};
            Ok(CompiledPredicate::Single {
                air_type: AirType::Arithmetic,
                witness_spec: WitnessSpec::Arithmetic {
                    inputs: vec![attribute.clone()],
                    expression: ArithExpr::Var(0),
                    predicate: ArithPredicate::ExprNeq(
                        ArithExpr::Var(0),
                        BabyBear::new(*value as u32),
                    ),
                },
            })
        }

        PredicateExpr::NotInRange {
            attribute,
            low,
            high,
        } => {
            // Compile to Or(Lt(low), Gt(high)) — value < low OR value > high.
            // This means value is outside [low, high].
            let lt_low = PredicateExpr::Range {
                attribute: attribute.clone(),
                predicate_type: PredicateType::Lt,
                threshold: *low,
            };
            let gt_high = PredicateExpr::Range {
                attribute: attribute.clone(),
                predicate_type: PredicateType::Gt,
                threshold: *high,
            };
            compile_expr(&PredicateExpr::Or(vec![lt_low, gt_high]))
        }

        PredicateExpr::ThresholdBelow { max_k, predicates } => {
            if predicates.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            if *max_k == 0 || *max_k > predicates.len() {
                return Err(CompileError::InvalidThreshold {
                    k: *max_k,
                    n: predicates.len(),
                });
            }
            // ThresholdBelow { max_k, predicates } means "fewer than max_k hold".
            // Equivalently: at most (max_k - 1) hold.
            // We compile this as a Composite with a ThresholdBelow formula.
            let sub_proofs: Vec<CompiledPredicate> = predicates
                .iter()
                .map(compile_expr)
                .collect::<Result<Vec<_>, _>>()?;

            Ok(CompiledPredicate::Composite {
                sub_proofs,
                formula: CompositeFormula::ThresholdBelow(*max_k),
            })
        }

        // ─── AND composition ───
        PredicateExpr::And(children) => {
            if children.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            compile_boolean_composition(children, CompositeFormulaKind::And)
        }

        // ─── OR composition ───
        PredicateExpr::Or(children) => {
            if children.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            compile_boolean_composition(children, CompositeFormulaKind::Or)
        }

        // ─── NOT ───
        PredicateExpr::Not(inner) => {
            // Special case: NOT(Membership { ... }) compiles to NonMembership.
            //
            // This is the ONE case where NOT can be soundly implemented: we use the
            // polynomial-evaluation accumulator to directly prove non-membership,
            // rather than trying to negate an existential proof.
            if let PredicateExpr::Membership {
                attribute,
                set_commitment,
            } = inner.as_ref()
            {
                return Ok(CompiledPredicate::Single {
                    air_type: AirType::NonMembership,
                    witness_spec: WitnessSpec::NonMembership {
                        attribute: attribute.clone(),
                        set_id: *set_commitment,
                    },
                });
            }

            // SOUNDNESS FIX: General NOT cannot be soundly implemented in the current
            // proof system.
            //
            // The previous implementation accepted NOT(P) when the prover "failed to
            // generate a proof for P." This is UNSOUND: a malicious prover can claim
            // NOT(P) for ANY P by simply omitting the inner proof (producing empty
            // sub_proofs). The verifier would then accept based on the absence of proof.
            //
            // Correct NOT requires either:
            // 1. MPC-in-the-head proof of non-satisfaction
            // 2. A proper algebraic NOT gate (requires proving the complement)
            // 3. Flipping the comparison (GTE -> LT) at the expression level before
            //    compilation (caller's responsibility)
            //
            // Only NOT(Membership(...)) is supported (compiles to NonMembership above).
            // All other NOT forms are rejected at compile time.
            Err(CompileError::UnsupportedNot)
        }

        // ─── Threshold ───
        PredicateExpr::Threshold { k, predicates } => {
            if predicates.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            if *k == 0 || *k > predicates.len() {
                return Err(CompileError::InvalidThreshold {
                    k: *k,
                    n: predicates.len(),
                });
            }
            compile_boolean_composition(predicates, CompositeFormulaKind::Threshold(*k))
        }
    }
}

/// Internal enum for tracking which boolean composition to build.
#[derive(Clone, Debug)]
enum CompositeFormulaKind {
    And,
    Or,
    Threshold(usize),
}

/// Compile a boolean composition (AND, OR, Threshold) of child expressions.
///
/// If ALL children are range predicates and the total count fits in a single
/// `CompoundPredicateAir`, this flattens into a `CompoundRange` compilation.
/// Otherwise, it produces a `Composite` with independently compiled sub-proofs.
fn compile_boolean_composition(
    children: &[PredicateExpr],
    kind: CompositeFormulaKind,
) -> Result<CompiledPredicate, CompileError> {
    // Check if all children are range-type leaves (can flatten into CompoundPredicateAir).
    let all_range = children
        .iter()
        .all(|c| matches!(c, PredicateExpr::Range { .. }));

    if all_range && children.len() <= MAX_COMPOUND_PREDICATES {
        // Flatten into a single CompoundPredicateAir.
        let sub_predicates: Vec<WitnessSpec> = children
            .iter()
            .map(|c| match c {
                PredicateExpr::Range {
                    attribute,
                    predicate_type,
                    threshold,
                } => WitnessSpec::Range {
                    attribute: attribute.clone(),
                    predicate_type: *predicate_type,
                    threshold: *threshold,
                },
                _ => unreachable!("checked all_range above"),
            })
            .collect();

        let indices: Vec<usize> = (0..sub_predicates.len()).collect();
        let formula = match kind {
            CompositeFormulaKind::And => BooleanFormula::And(indices),
            CompositeFormulaKind::Or => BooleanFormula::Or(indices),
            CompositeFormulaKind::Threshold(k) => BooleanFormula::Threshold(k, indices),
        };

        Ok(CompiledPredicate::CompoundRange {
            sub_predicates,
            formula,
        })
    } else {
        // Mixed AIR types or too many predicates: compile each child independently.
        let sub_proofs: Vec<CompiledPredicate> = children
            .iter()
            .map(compile_expr)
            .collect::<Result<Vec<_>, _>>()?;

        let formula = match kind {
            CompositeFormulaKind::And => CompositeFormula::And,
            CompositeFormulaKind::Or => CompositeFormula::Or,
            CompositeFormulaKind::Threshold(k) => CompositeFormula::Threshold(k),
        };

        Ok(CompiledPredicate::Composite {
            sub_proofs,
            formula,
        })
    }
}

// =============================================================================
// NOR Helper
// =============================================================================

/// Compile a NOR ("none of these hold") predicate expression.
///
/// For predicate-based NOR: flips each range predicate's comparison direction,
/// then compiles as AND of flipped predicates:
/// - `Gte` becomes `Lt`
/// - `Lte` becomes `Gt`
/// - `Gt` becomes `Lte`
/// - `Lt` becomes `Gte`
/// - `Neq` becomes an `ExprEq` (via Arithmetic)
///
/// This is sound because "none hold" = "all are false" = "all negations are true".
///
/// For non-range predicates in the input, they are wrapped in ThresholdBelow(1, [p])
/// which means "zero of [p] hold".
///
/// Returns a `PredicateExpr` that can be fed to `compile_predicate`.
pub fn compile_nor(predicates: &[PredicateExpr]) -> PredicateExpr {
    let flipped: Vec<PredicateExpr> = predicates.iter().map(|p| flip_predicate(p)).collect();
    PredicateExpr::And(flipped)
}

/// Flip a single predicate to its negation.
///
/// For range predicates, this flips the comparison direction.
/// For other predicate types, wraps in ThresholdBelow(1, ...) meaning "zero hold".
fn flip_predicate(pred: &PredicateExpr) -> PredicateExpr {
    match pred {
        PredicateExpr::Range {
            attribute,
            predicate_type,
            threshold,
        } => {
            let flipped_type = match predicate_type {
                PredicateType::Gte => PredicateType::Lt,
                PredicateType::Lte => PredicateType::Gt,
                PredicateType::Gt => PredicateType::Lte,
                PredicateType::Lt => PredicateType::Gte,
                PredicateType::Neq => {
                    // NEQ flipped = EQ. Use Arithmetic with ExprEq.
                    return PredicateExpr::Arithmetic {
                        inputs: vec![attribute.clone()],
                        expression: crate::arithmetic_predicate_air::ArithExpr::Var(0),
                        predicate: crate::arithmetic_predicate_air::ArithPredicate::ExprEq(
                            crate::arithmetic_predicate_air::ArithExpr::Var(0),
                            BabyBear::new(*threshold as u32),
                        ),
                    };
                }
                PredicateType::InRangeLow | PredicateType::InRangeHigh => {
                    // These are internal types; treat as unsupported by wrapping.
                    return PredicateExpr::ThresholdBelow {
                        max_k: 1,
                        predicates: vec![pred.clone()],
                    };
                }
            };
            PredicateExpr::Range {
                attribute: attribute.clone(),
                predicate_type: flipped_type,
                threshold: *threshold,
            }
        }
        PredicateExpr::Neq { attribute, value } => {
            // NEQ flipped = EQ. Compile as Arithmetic ExprEq.
            PredicateExpr::Arithmetic {
                inputs: vec![attribute.clone()],
                expression: crate::arithmetic_predicate_air::ArithExpr::Var(0),
                predicate: crate::arithmetic_predicate_air::ArithPredicate::ExprEq(
                    crate::arithmetic_predicate_air::ArithExpr::Var(0),
                    BabyBear::new(*value as u32),
                ),
            }
        }
        PredicateExpr::NotInRange {
            attribute,
            low,
            high,
        } => {
            // NOT(NotInRange) = InRange. Use a Range with InRangeLow + AND + InRangeHigh.
            PredicateExpr::And(vec![
                PredicateExpr::Range {
                    attribute: attribute.clone(),
                    predicate_type: PredicateType::Gte,
                    threshold: *low,
                },
                PredicateExpr::Range {
                    attribute: attribute.clone(),
                    predicate_type: PredicateType::Lte,
                    threshold: *high,
                },
            ])
        }
        // For other complex predicates, wrap in ThresholdBelow(1) meaning "zero hold".
        _ => PredicateExpr::ThresholdBelow {
            max_k: 1,
            predicates: vec![pred.clone()],
        },
    }
}

// =============================================================================
// Proof Execution
// =============================================================================

/// Errors that can occur during proof generation.
#[derive(Clone, Debug)]
pub enum ProveError {
    /// A required attribute value is missing from the private state.
    MissingAttribute(String),
    /// The predicate is not satisfiable with the given private state.
    NotSatisfiable(String),
    /// Proof generation failed (AIR constraint violation or internal error).
    ProofGenerationFailed(String),
    /// Temporal proof requires historical values not provided.
    MissingTemporalData { attribute: String, needed: u64 },
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingAttribute(name) => write!(f, "missing attribute: {name}"),
            Self::NotSatisfiable(msg) => write!(f, "not satisfiable: {msg}"),
            Self::ProofGenerationFailed(msg) => write!(f, "proof generation failed: {msg}"),
            Self::MissingTemporalData { attribute, needed } => {
                write!(
                    f,
                    "temporal proof for '{attribute}' needs {needed} historical values"
                )
            }
        }
    }
}

/// The output of proving a predicate program: a collection of sub-proofs
/// with the boolean formula governing their composition.
#[derive(Clone, Debug)]
pub struct ProgramProof {
    /// The sub-proofs generated by the proving pipeline.
    pub sub_proofs: Vec<SubProof>,
    /// The composition structure matching the compiled predicate.
    pub structure: ProofStructure,
}

/// A single sub-proof within a program proof.
#[derive(Clone, Debug)]
pub enum SubProof {
    /// A single-predicate range proof.
    Range(PredicateProof),
    /// A compound range proof (multiple range checks in one AIR).
    Compound(CompoundPredicateProof),
    /// A temporal predicate proof (legacy custom STARK, missing transition constraints).
    Temporal(TemporalPredicateProof),
    /// A Plonky3-based temporal predicate proof with correct transition constraints.
    /// Only available with the `plonky3` feature enabled.
    #[cfg(feature = "plonky3")]
    TemporalP3(P3TemporalPredicateProof),
    /// An arithmetic predicate proof (expression over multiple inputs).
    Arithmetic(crate::arithmetic_predicate_air::ArithmeticPredicateProof),
    /// A relational predicate proof (two-party value comparison).
    Relational(RelationalPredicateProof),
    /// A committed-threshold predicate proof (value >= hidden threshold).
    CommittedThreshold(CommittedThresholdProof),
    /// A non-membership proof (element NOT in set, via accumulator).
    NonMembership(crate::non_membership::NonMembershipProof),
}

/// The structure of a program proof (mirrors the compiled predicate shape).
#[derive(Clone, Debug)]
pub enum ProofStructure {
    /// Single proof — just verify the sub-proof directly.
    Single,
    /// Compound range — one CompoundPredicateAir proof covers everything.
    CompoundRange,
    /// Composite — multiple sub-proofs composed with a formula.
    Composite(CompositeFormula),
}

/// Extended private state for proof generation.
///
/// Maps attribute names to their private values. For temporal predicates,
/// historical values and state roots are also provided. For relational and
/// committed-threshold predicates, counterparty values received via sealed
/// channels are included.
#[derive(Clone, Debug, Default)]
pub struct PrivateState {
    /// Current attribute values: attribute_name -> value.
    pub values: HashMap<String, u64>,
    /// Historical values for temporal predicates: attribute_name -> (values, state_roots).
    pub temporal_history: HashMap<String, (Vec<u64>, Vec<BabyBear>)>,
    /// Fact hashes for each attribute (for computing fact commitments).
    pub fact_hashes: HashMap<String, BabyBear>,
    /// Counterparty values for relational predicates, keyed by their commitment.
    /// Each entry: (their_value, their_blinding) received via OT or sealed channel.
    /// The prover also needs their own blinding for the commitment.
    pub relational_context: HashMap<String, RelationalContext>,
    /// Committed thresholds received from verifiers, keyed by the threshold commitment.
    /// Each entry: (threshold, blinding) as provided by the verifier via secure channel.
    pub committed_thresholds: HashMap<String, CommittedThresholdContext>,
    /// Non-membership contexts keyed by attribute name.
    /// Each entry provides the set elements needed to generate the accumulator witness.
    pub non_membership_context: HashMap<String, NonMembershipContext>,
}

/// Context needed to prove a relational predicate.
///
/// The prover (comparison service) must know both values and their blinding factors.
#[derive(Clone, Debug)]
pub struct RelationalContext {
    /// The prover's own blinding factor for their commitment.
    pub my_blinding: BabyBear,
    /// The counterparty's value (received via sealed channel).
    pub their_value: u64,
    /// The counterparty's blinding factor (received via sealed channel).
    pub their_blinding: BabyBear,
}

/// Context needed to prove a committed-threshold predicate.
///
/// The verifier sends the threshold and blinding to the prover via a secure channel.
#[derive(Clone, Debug)]
pub struct CommittedThresholdContext {
    /// The verifier's secret threshold.
    pub threshold: u64,
    /// The verifier's blinding randomness.
    pub blinding: BabyBear,
}

/// Context needed to prove a non-membership predicate.
///
/// The prover needs the set elements to generate the accumulator witness.
/// In production, this would come from a federation's published exclusion set.
#[derive(Clone, Debug)]
pub struct NonMembershipContext {
    /// Human-readable set name (e.g., "suspended_users", "blacklist").
    pub set_name: String,
    /// The elements in the exclusion set.
    pub set_elements: Vec<BabyBear>,
}

/// Prove a compiled predicate program against private state.
///
/// # Arguments
///
/// * `compiled` - The compiled predicate (output of `compile_predicate`).
/// * `private_state` - The prover's private attribute values.
/// * `state_root` - The Poseidon2 root of the current token state.
///
/// # Returns
///
/// A `ProgramProof` that can be verified by anyone knowing the public inputs,
/// or a `ProveError` if the predicate cannot be proven.
pub fn prove_program(
    compiled: &CompiledPredicate,
    private_state: &PrivateState,
    state_root: BabyBear,
) -> Result<ProgramProof, ProveError> {
    match compiled {
        CompiledPredicate::Single { witness_spec, .. } => {
            prove_single(witness_spec, private_state, state_root)
        }
        CompiledPredicate::CompoundRange {
            sub_predicates,
            formula,
        } => prove_compound_range(sub_predicates, formula, private_state, state_root),
        CompiledPredicate::Composite {
            sub_proofs,
            formula,
        } => prove_composite(sub_proofs, formula, private_state, state_root),
    }
}

/// Prove a single leaf predicate.
fn prove_single(
    witness_spec: &WitnessSpec,
    private_state: &PrivateState,
    state_root: BabyBear,
) -> Result<ProgramProof, ProveError> {
    match witness_spec {
        WitnessSpec::Range {
            attribute,
            predicate_type,
            threshold,
        } => {
            let value = private_state
                .values
                .get(attribute)
                .ok_or_else(|| ProveError::MissingAttribute(attribute.clone()))?;

            let fact_hash = private_state
                .fact_hashes
                .get(attribute)
                .copied()
                .unwrap_or_else(|| compute_attribute_fact_hash(attribute, *value));

            let fact_commitment = compute_fact_commitment(fact_hash, state_root);

            let witness = PredicateWitness {
                private_value: BabyBear::new(*value as u32),
                threshold: BabyBear::new(*threshold as u32),
                predicate_type: *predicate_type,
                fact_commitment,
                blinding: None,
                fact_hash: Some(fact_hash),
                state_root: Some(state_root),
            };

            let proof = prove_predicate(witness).ok_or_else(|| {
                ProveError::NotSatisfiable(format!(
                    "{attribute}: value {value} does not satisfy {predicate_type:?} {threshold}"
                ))
            })?;

            Ok(ProgramProof {
                sub_proofs: vec![SubProof::Range(proof)],
                structure: ProofStructure::Single,
            })
        }

        WitnessSpec::Temporal {
            attribute,
            predicate_type,
            threshold,
            min_blocks,
        } => {
            let (values, roots) =
                private_state
                    .temporal_history
                    .get(attribute)
                    .ok_or_else(|| ProveError::MissingTemporalData {
                        attribute: attribute.clone(),
                        needed: *min_blocks,
                    })?;

            if (values.len() as u64) < *min_blocks {
                return Err(ProveError::MissingTemporalData {
                    attribute: attribute.clone(),
                    needed: *min_blocks,
                });
            }

            let values_bb: Vec<BabyBear> =
                values.iter().map(|v| BabyBear::new(*v as u32)).collect();
            let threshold_bb = BabyBear::new(*threshold as u32);

            // Use Plonky3-based prover when available (correct transition constraints).
            #[cfg(feature = "plonky3")]
            {
                let proof =
                    prove_temporal_predicate_p3(&values_bb, roots, *predicate_type, threshold_bb)
                        .ok_or_else(|| {
                        ProveError::NotSatisfiable(format!(
                            "{attribute}: temporal predicate not satisfied across all steps"
                        ))
                    })?;

                Ok(ProgramProof {
                    sub_proofs: vec![SubProof::TemporalP3(proof)],
                    structure: ProofStructure::Single,
                })
            }

            // Fallback: legacy custom STARK prover (omits transition constraints).
            #[cfg(not(feature = "plonky3"))]
            {
                let proof =
                    prove_temporal_predicate(&values_bb, roots, *predicate_type, threshold_bb)
                        .ok_or_else(|| {
                            ProveError::NotSatisfiable(format!(
                                "{attribute}: temporal predicate not satisfied across all steps"
                            ))
                        })?;

                Ok(ProgramProof {
                    sub_proofs: vec![SubProof::Temporal(proof)],
                    structure: ProofStructure::Single,
                })
            }
        }

        // Membership is recognized but proof generation is deferred to Phase 2.
        WitnessSpec::Membership { attribute, .. } => {
            Err(ProveError::ProofGenerationFailed(format!(
                "AIR type for '{}' (Membership) not yet supported in program prover",
                attribute
            )))
        }

        WitnessSpec::Relational {
            my_attribute,
            their_commitment,
            relation,
        } => {
            let my_value = private_state
                .values
                .get(my_attribute)
                .ok_or_else(|| ProveError::MissingAttribute(my_attribute.clone()))?;

            let ctx = private_state
                .relational_context
                .get(my_attribute)
                .ok_or_else(|| {
                    ProveError::ProofGenerationFailed(format!(
                        "relational predicate for '{}' requires counterparty context \
                         (their_value + blindings received via sealed channel)",
                        my_attribute
                    ))
                })?;

            let my_value_bb = BabyBear::new(*my_value as u32);
            let their_value_bb = BabyBear::new(ctx.their_value as u32);

            // Verify the counterparty's commitment matches what was declared.
            let expected_their_commitment =
                compute_value_commitment(their_value_bb, ctx.their_blinding);
            if expected_their_commitment != *their_commitment {
                return Err(ProveError::ProofGenerationFailed(format!(
                    "relational predicate for '{}': counterparty commitment mismatch \
                     (declared {} but context computes {})",
                    my_attribute,
                    their_commitment.as_u32(),
                    expected_their_commitment.as_u32()
                )));
            }

            let witness = RelationalPredicateWitness {
                value_a: my_value_bb,
                blinding_a: ctx.my_blinding,
                value_b: their_value_bb,
                blinding_b: ctx.their_blinding,
                relation: *relation,
            };

            let proof = prove_relational_air(witness).ok_or_else(|| {
                ProveError::NotSatisfiable(format!(
                    "{}: relational predicate {:?} not satisfiable (my_value={}, their_value={})",
                    my_attribute, relation, my_value, ctx.their_value
                ))
            })?;

            Ok(ProgramProof {
                sub_proofs: vec![SubProof::Relational(proof)],
                structure: ProofStructure::Single,
            })
        }

        WitnessSpec::CommittedThreshold {
            attribute,
            threshold_commitment,
        } => {
            let value = private_state
                .values
                .get(attribute)
                .ok_or_else(|| ProveError::MissingAttribute(attribute.clone()))?;

            let ctx = private_state
                .committed_thresholds
                .get(attribute)
                .ok_or_else(|| {
                    ProveError::ProofGenerationFailed(format!(
                        "committed-threshold predicate for '{}' requires verifier context \
                         (threshold + blinding received via secure channel)",
                        attribute
                    ))
                })?;

            let threshold_bb = BabyBear::new(ctx.threshold as u32);
            let blinding_bb = ctx.blinding;

            // Verify the threshold commitment matches what was declared.
            let expected_commitment = compute_threshold_commitment(threshold_bb, blinding_bb);
            if expected_commitment != *threshold_commitment {
                return Err(ProveError::ProofGenerationFailed(format!(
                    "committed-threshold for '{}': threshold commitment mismatch \
                     (declared {} but context computes {})",
                    attribute,
                    threshold_commitment.as_u32(),
                    expected_commitment.as_u32()
                )));
            }

            let fact_hash = private_state
                .fact_hashes
                .get(attribute)
                .copied()
                .unwrap_or_else(|| compute_attribute_fact_hash(attribute, *value));

            let fact_commitment = compute_fact_commitment(fact_hash, state_root);

            let witness = CommittedThresholdWitness {
                private_value: BabyBear::new(*value as u32),
                threshold: threshold_bb,
                blinding: blinding_bb,
                fact_commitment,
            };

            let proof = prove_committed_threshold_air(witness).ok_or_else(|| {
                ProveError::NotSatisfiable(format!(
                    "{}: committed-threshold not satisfiable (value={}, threshold={})",
                    attribute, value, ctx.threshold
                ))
            })?;

            Ok(ProgramProof {
                sub_proofs: vec![SubProof::CommittedThreshold(proof)],
                structure: ProofStructure::Single,
            })
        }
        WitnessSpec::Arithmetic {
            inputs,
            expression: _,
            predicate,
        } => {
            use crate::arithmetic_predicate_air::{
                ArithmeticPredicateWitness, compute_arithmetic_fact_commitment,
                prove_arithmetic_predicate,
            };

            let input_values: Vec<BabyBear> = inputs
                .iter()
                .map(|attr| {
                    let value = private_state
                        .values
                        .get(attr)
                        .ok_or_else(|| ProveError::MissingAttribute(attr.clone()))?;
                    Ok(BabyBear::new(*value as u32))
                })
                .collect::<Result<Vec<_>, ProveError>>()?;

            let fact_hashes: Vec<BabyBear> = inputs
                .iter()
                .map(|attr| {
                    private_state
                        .fact_hashes
                        .get(attr)
                        .copied()
                        .unwrap_or_else(|| {
                            let value = private_state.values.get(attr).copied().unwrap_or(0);
                            compute_attribute_fact_hash(attr, value)
                        })
                })
                .collect();

            let fact_commitments: Vec<BabyBear> = fact_hashes
                .iter()
                .map(|&fh| compute_arithmetic_fact_commitment(fh, state_root))
                .collect();
            let aggregate_commitment = poseidon2::hash_many(&fact_commitments);

            let witness = ArithmeticPredicateWitness {
                inputs: input_values,
                predicate: predicate.clone(),
                fact_commitment: aggregate_commitment,
            };

            let proof = prove_arithmetic_predicate(witness).ok_or_else(|| {
                ProveError::NotSatisfiable(format!(
                    "arithmetic predicate over {:?} is not satisfiable",
                    inputs
                ))
            })?;

            Ok(ProgramProof {
                sub_proofs: vec![SubProof::Arithmetic(proof)],
                structure: ProofStructure::Single,
            })
        }

        WitnessSpec::NonMembership { attribute, set_id } => {
            use crate::non_membership::{NonMembershipProver, SetIdentifier};

            // The non-membership context provides the set elements and set identity.
            let nm_ctx = private_state
                .non_membership_context
                .get(attribute)
                .ok_or_else(|| {
                    ProveError::ProofGenerationFailed(format!(
                        "non-membership predicate for '{}' requires set context \
                         (set_elements provided via non_membership_context)",
                        attribute
                    ))
                })?;

            let set_identifier = SetIdentifier::from_raw(&nm_ctx.set_name, *set_id);

            let prover = NonMembershipProver::with_set_id(&nm_ctx.set_elements, set_identifier);

            // The element to prove non-membership for is the attribute's hash.
            let element_hash = private_state
                .fact_hashes
                .get(attribute)
                .copied()
                .unwrap_or_else(|| {
                    let value = private_state.values.get(attribute).copied().unwrap_or(0);
                    compute_attribute_fact_hash(attribute, value)
                });

            let nm_proof = prover
                .prove_non_membership(&[element_hash])
                .ok_or_else(|| {
                    ProveError::NotSatisfiable(format!(
                        "{}: element IS in the {} set (non-membership cannot be proven)",
                        attribute, nm_ctx.set_name
                    ))
                })?;

            Ok(ProgramProof {
                sub_proofs: vec![SubProof::NonMembership(nm_proof)],
                structure: ProofStructure::Single,
            })
        }
    }
}

/// Prove a compound range program (flattened into CompoundPredicateAir).
fn prove_compound_range(
    sub_predicates: &[WitnessSpec],
    formula: &BooleanFormula,
    private_state: &PrivateState,
    state_root: BabyBear,
) -> Result<ProgramProof, ProveError> {
    // Build the predicate tuples for the compound AIR.
    let mut predicates: Vec<(BabyBear, PredicateType, BabyBear)> =
        Vec::with_capacity(sub_predicates.len());
    let mut commitments: Vec<BabyBear> = Vec::with_capacity(sub_predicates.len());

    for spec in sub_predicates {
        match spec {
            WitnessSpec::Range {
                attribute,
                predicate_type,
                threshold,
            } => {
                let value = private_state
                    .values
                    .get(attribute)
                    .ok_or_else(|| ProveError::MissingAttribute(attribute.clone()))?;

                let fact_hash = private_state
                    .fact_hashes
                    .get(attribute)
                    .copied()
                    .unwrap_or_else(|| compute_attribute_fact_hash(attribute, *value));

                let fact_commitment = compute_fact_commitment(fact_hash, state_root);

                predicates.push((
                    BabyBear::new(*value as u32),
                    *predicate_type,
                    BabyBear::new(*threshold as u32),
                ));
                commitments.push(fact_commitment);
            }
            _ => {
                return Err(ProveError::ProofGenerationFailed(
                    "compound range received non-range witness spec".to_string(),
                ));
            }
        }
    }

    let proof =
        prove_compound_predicate(&predicates, formula.clone(), &commitments).ok_or_else(|| {
            ProveError::NotSatisfiable(
                "compound predicate not satisfiable with given values".to_string(),
            )
        })?;

    Ok(ProgramProof {
        sub_proofs: vec![SubProof::Compound(proof)],
        structure: ProofStructure::CompoundRange,
    })
}

/// Prove a composite program (multiple AIR types combined).
fn prove_composite(
    sub_compilations: &[CompiledPredicate],
    formula: &CompositeFormula,
    private_state: &PrivateState,
    state_root: BabyBear,
) -> Result<ProgramProof, ProveError> {
    // For AND: all sub-proofs must succeed.
    // For OR: at least one must succeed.
    // For Threshold(k): at least k must succeed.
    // For NOT: the single sub-proof must FAIL (we invert the semantics).

    let mut all_sub_proofs: Vec<SubProof> = Vec::new();

    match formula {
        CompositeFormula::And => {
            // All must succeed.
            for sub in sub_compilations {
                let sub_result = prove_program(sub, private_state, state_root)?;
                all_sub_proofs.extend(sub_result.sub_proofs);
            }
        }
        CompositeFormula::Or => {
            // At least one must succeed. Try each; collect the first success.
            let mut found_success = false;
            for sub in sub_compilations {
                match prove_program(sub, private_state, state_root) {
                    Ok(sub_result) => {
                        all_sub_proofs.extend(sub_result.sub_proofs);
                        found_success = true;
                        break;
                    }
                    Err(_) => continue,
                }
            }
            if !found_success {
                return Err(ProveError::NotSatisfiable(
                    "no disjunct is satisfiable".to_string(),
                ));
            }
        }
        CompositeFormula::Threshold(k) => {
            // At least k must succeed.
            let mut successes = 0;
            for sub in sub_compilations {
                match prove_program(sub, private_state, state_root) {
                    Ok(sub_result) => {
                        all_sub_proofs.extend(sub_result.sub_proofs);
                        successes += 1;
                    }
                    Err(_) => continue,
                }
            }
            if successes < *k {
                return Err(ProveError::NotSatisfiable(format!(
                    "only {successes} of {k} required predicates satisfied"
                )));
            }
        }
        CompositeFormula::ThresholdBelow(max_k) => {
            // Fewer than max_k must succeed.
            // The prover counts how many sub-predicates are satisfiable. If the
            // count is >= max_k, the ThresholdBelow statement is FALSE and we
            // cannot produce a proof. If count < max_k, the statement is TRUE.
            let mut successes = 0;
            for sub in sub_compilations {
                match prove_program(sub, private_state, state_root) {
                    Ok(sub_result) => {
                        all_sub_proofs.extend(sub_result.sub_proofs);
                        successes += 1;
                    }
                    Err(_) => continue,
                }
            }
            if successes >= *max_k {
                return Err(ProveError::NotSatisfiable(format!(
                    "{successes} predicates satisfied, but ThresholdBelow requires fewer than {max_k}"
                )));
            }
            // The proof contains the (successes < max_k) satisfied sub-proofs.
            // The verifier will count them and confirm count < max_k.
        }
        CompositeFormula::Not => {
            // SOUNDNESS: NOT is rejected at compile time. If this code path is
            // reached via direct construction (bypassing the compiler), refuse to
            // produce a proof to prevent the empty-sub_proofs attack.
            return Err(ProveError::ProofGenerationFailed(
                "NOT is not supported: requires MPC-in-the-head proof of non-satisfaction. \
                 Use comparison flipping (GTE -> LT) at the expression level instead."
                    .to_string(),
            ));
        }
    }

    Ok(ProgramProof {
        sub_proofs: all_sub_proofs,
        structure: ProofStructure::Composite(formula.clone()),
    })
}

// =============================================================================
// Verification
// =============================================================================

/// Verify a program proof against expected public commitments.
///
/// The verifier provides:
/// - The compiled predicate (they know the program structure).
/// - The program proof to verify.
/// - Expected fact commitments for each attribute.
///
/// Returns `true` if the proof is valid for the given commitments.
pub fn verify_program(
    proof: &ProgramProof,
    compiled: &CompiledPredicate,
    expected_commitments: &HashMap<String, BabyBear>,
    state_root: BabyBear,
) -> bool {
    match (&proof.structure, compiled) {
        (ProofStructure::Single, CompiledPredicate::Single { witness_spec, .. }) => {
            verify_single_proof(
                &proof.sub_proofs,
                witness_spec,
                expected_commitments,
                state_root,
            )
        }
        (
            ProofStructure::CompoundRange,
            CompiledPredicate::CompoundRange {
                sub_predicates,
                formula,
            },
        ) => verify_compound_range_proof(
            &proof.sub_proofs,
            sub_predicates,
            formula,
            expected_commitments,
            state_root,
        ),
        (
            ProofStructure::Composite(_),
            CompiledPredicate::Composite {
                sub_proofs: compiled_subs,
                formula,
            },
        ) => verify_composite_proof(
            &proof.sub_proofs,
            compiled_subs,
            formula,
            expected_commitments,
            state_root,
        ),
        _ => false, // Structure mismatch.
    }
}

/// Verify a single range or temporal sub-proof.
fn verify_single_proof(
    sub_proofs: &[SubProof],
    witness_spec: &WitnessSpec,
    expected_commitments: &HashMap<String, BabyBear>,
    _state_root: BabyBear,
) -> bool {
    if sub_proofs.len() != 1 {
        return false;
    }

    match (&sub_proofs[0], witness_spec) {
        (
            SubProof::Range(proof),
            WitnessSpec::Range {
                attribute,
                threshold,
                ..
            },
        ) => {
            let expected_commitment = expected_commitments.get(attribute).copied().unwrap_or({
                // If no explicit commitment provided, we cannot verify.
                BabyBear::ZERO
            });
            verify_predicate(proof, BabyBear::new(*threshold as u32), expected_commitment)
        }

        (
            SubProof::Temporal(proof),
            WitnessSpec::Temporal {
                threshold,
                min_blocks,
                ..
            },
        ) => {
            // Verify the temporal STARK proof with full cryptographic verification.
            // The verifier checks that:
            // 1. The proof covers at least min_blocks steps
            // 2. The threshold matches
            // 3. The STARK proof itself is valid (bit decomposition, accumulator, etc.)
            proof.num_steps as u64 >= *min_blocks
                && proof.threshold == BabyBear::new(*threshold as u32)
                && verify_temporal_predicate(
                    proof,
                    BabyBear::new(*threshold as u32),
                    proof.num_steps,
                    proof.initial_state_root,
                    proof.final_state_root,
                )
        }

        // Plonky3-based temporal proof with correct transition constraints.
        #[cfg(feature = "plonky3")]
        (
            SubProof::TemporalP3(proof),
            WitnessSpec::Temporal {
                threshold,
                min_blocks,
                ..
            },
        ) => {
            // Verify the Plonky3 temporal STARK proof. This proof correctly
            // enforces transition constraints (accumulator increment) making it
            // impossible for a malicious prover to skip or duplicate steps.
            proof.num_steps as u64 >= *min_blocks
                && proof.threshold == BabyBear::new(*threshold as u32)
                && verify_temporal_predicate_p3(
                    proof,
                    BabyBear::new(*threshold as u32),
                    proof.num_steps,
                    proof.initial_state_root,
                    proof.final_state_root,
                )
        }

        (SubProof::Arithmetic(proof), WitnessSpec::Arithmetic { inputs, .. }) => {
            use crate::arithmetic_predicate_air::verify_arithmetic_predicate;

            // Recompute the aggregate fact commitment from expected per-attribute commitments.
            let fact_commitments: Vec<BabyBear> = inputs
                .iter()
                .map(|attr| {
                    expected_commitments
                        .get(attr)
                        .copied()
                        .unwrap_or(BabyBear::ZERO)
                })
                .collect();
            let aggregate_commitment = poseidon2::hash_many(&fact_commitments);

            verify_arithmetic_predicate(proof, proof.threshold, aggregate_commitment)
        }

        (
            SubProof::Relational(proof),
            WitnessSpec::Relational {
                my_attribute,
                their_commitment,
                ..
            },
        ) => {
            // For relational predicates, the verifier knows both commitments:
            // - commitment_a (prover's): from expected_commitments keyed by my_attribute
            // - commitment_b (counterparty's): from the WitnessSpec (their_commitment)
            let my_commitment = expected_commitments
                .get(my_attribute)
                .copied()
                .unwrap_or(BabyBear::ZERO);
            verify_relational_air(proof, my_commitment, *their_commitment)
        }

        (
            SubProof::CommittedThreshold(proof),
            WitnessSpec::CommittedThreshold {
                attribute,
                threshold_commitment,
            },
        ) => {
            // For committed-threshold predicates, the verifier provides:
            // - threshold_commitment: from the WitnessSpec (published by verifier)
            // - fact_commitment: from expected_commitments keyed by attribute
            let fact_commitment = expected_commitments
                .get(attribute)
                .copied()
                .unwrap_or(BabyBear::ZERO);
            verify_committed_threshold_air(proof, *threshold_commitment, fact_commitment)
        }

        (SubProof::NonMembership(proof), WitnessSpec::NonMembership { .. }) => {
            // For non-membership predicates, verify the accumulator STARK proof.
            // The verifier trusts the accumulator and alpha from the proof
            // (in production, these would be cross-checked against a federation's
            // published set commitment).
            crate::non_membership::verify_non_membership_proof(proof).is_ok()
        }

        _ => false,
    }
}

/// Verify a compound range proof.
fn verify_compound_range_proof(
    sub_proofs: &[SubProof],
    sub_predicates: &[WitnessSpec],
    formula: &BooleanFormula,
    expected_commitments: &HashMap<String, BabyBear>,
    _state_root: BabyBear,
) -> bool {
    if sub_proofs.len() != 1 {
        return false;
    }

    let compound_proof = match &sub_proofs[0] {
        SubProof::Compound(p) => p,
        _ => return false,
    };

    // Reconstruct expected commitments for the compound proof.
    let mut expected: Vec<BabyBear> = Vec::with_capacity(sub_predicates.len());
    for spec in sub_predicates {
        match spec {
            WitnessSpec::Range {
                attribute,
                threshold: _,
                ..
            } => {
                let commitment = expected_commitments
                    .get(attribute)
                    .copied()
                    .unwrap_or(BabyBear::ZERO);
                expected.push(commitment);
            }
            _ => return false,
        }
    }

    verify_compound_predicate(compound_proof, &expected, formula)
}

/// Verify a composite proof.
fn verify_composite_proof(
    sub_proofs: &[SubProof],
    compiled_subs: &[CompiledPredicate],
    formula: &CompositeFormula,
    expected_commitments: &HashMap<String, BabyBear>,
    state_root: BabyBear,
) -> bool {
    match formula {
        CompositeFormula::And => {
            // For AND composite: all sub-proofs must be present and verify.
            // We verify each sub-proof against its corresponding compiled predicate.
            let mut proof_idx = 0;
            for compiled_sub in compiled_subs {
                let sub_proof_count = count_expected_sub_proofs(compiled_sub);
                if proof_idx + sub_proof_count > sub_proofs.len() {
                    return false;
                }
                let sub_slice = &sub_proofs[proof_idx..proof_idx + sub_proof_count];
                let sub_program_proof = ProgramProof {
                    sub_proofs: sub_slice.to_vec(),
                    structure: infer_structure(compiled_sub),
                };
                if !verify_program(
                    &sub_program_proof,
                    compiled_sub,
                    expected_commitments,
                    state_root,
                ) {
                    return false;
                }
                proof_idx += sub_proof_count;
            }
            true
        }
        CompositeFormula::Or => {
            // For OR: at least one sub-proof must verify.
            if sub_proofs.is_empty() {
                return false;
            }
            // We try verifying the provided sub-proofs against each compiled sub.
            for compiled_sub in compiled_subs {
                let sub_proof_count = count_expected_sub_proofs(compiled_sub);
                if sub_proof_count <= sub_proofs.len() {
                    let sub_slice = &sub_proofs[..sub_proof_count];
                    let sub_program_proof = ProgramProof {
                        sub_proofs: sub_slice.to_vec(),
                        structure: infer_structure(compiled_sub),
                    };
                    if verify_program(
                        &sub_program_proof,
                        compiled_sub,
                        expected_commitments,
                        state_root,
                    ) {
                        return true;
                    }
                }
            }
            false
        }
        CompositeFormula::Threshold(k) => {
            // For Threshold(k): at least k sub-proofs must verify.
            // The prover provides exactly the proofs for the k satisfied branches.
            // We count how many compiled subs can be verified with the provided proofs.
            let mut verified = 0;
            let mut proof_idx = 0;
            for compiled_sub in compiled_subs {
                let sub_proof_count = count_expected_sub_proofs(compiled_sub);
                if proof_idx + sub_proof_count > sub_proofs.len() {
                    break;
                }
                let sub_slice = &sub_proofs[proof_idx..proof_idx + sub_proof_count];
                let sub_program_proof = ProgramProof {
                    sub_proofs: sub_slice.to_vec(),
                    structure: infer_structure(compiled_sub),
                };
                if verify_program(
                    &sub_program_proof,
                    compiled_sub,
                    expected_commitments,
                    state_root,
                ) {
                    verified += 1;
                    proof_idx += sub_proof_count;
                }
            }
            verified >= *k
        }
        CompositeFormula::ThresholdBelow(max_k) => {
            // For ThresholdBelow(max_k): fewer than max_k sub-proofs verify.
            // The prover provides the sub-proofs that DID succeed. The verifier
            // verifies each one and confirms the total count is < max_k.
            let mut verified = 0;
            let mut proof_idx = 0;
            for compiled_sub in compiled_subs {
                let sub_proof_count = count_expected_sub_proofs(compiled_sub);
                if proof_idx + sub_proof_count > sub_proofs.len() {
                    break;
                }
                let sub_slice = &sub_proofs[proof_idx..proof_idx + sub_proof_count];
                let sub_program_proof = ProgramProof {
                    sub_proofs: sub_slice.to_vec(),
                    structure: infer_structure(compiled_sub),
                };
                if verify_program(
                    &sub_program_proof,
                    compiled_sub,
                    expected_commitments,
                    state_root,
                ) {
                    verified += 1;
                    proof_idx += sub_proof_count;
                }
            }
            verified < *max_k
        }
        CompositeFormula::Not => {
            // SOUNDNESS FIX: NOT verification previously accepted empty sub_proofs,
            // which allowed a malicious prover to claim NOT(P) for ANY P by simply
            // omitting the proof. NOT is now always rejected.
            false
        }
    }
}

/// Count how many sub-proof items a compiled predicate generates.
fn count_expected_sub_proofs(compiled: &CompiledPredicate) -> usize {
    match compiled {
        CompiledPredicate::Single { .. } => 1,
        CompiledPredicate::CompoundRange { .. } => 1,
        CompiledPredicate::Composite { sub_proofs, .. } => {
            sub_proofs.iter().map(count_expected_sub_proofs).sum()
        }
    }
}

/// Infer the proof structure from a compiled predicate.
fn infer_structure(compiled: &CompiledPredicate) -> ProofStructure {
    match compiled {
        CompiledPredicate::Single { .. } => ProofStructure::Single,
        CompiledPredicate::CompoundRange { .. } => ProofStructure::CompoundRange,
        CompiledPredicate::Composite { formula, .. } => ProofStructure::Composite(formula.clone()),
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Compute a default fact hash for an attribute/value pair.
///
/// This is a convenience for testing and simple cases. In production, the fact hash
/// would come from the committed token state's Merkle tree.
fn compute_attribute_fact_hash(attribute: &str, value: u64) -> BabyBear {
    let attr_bytes = blake3::hash(attribute.as_bytes());
    let attr_bb = poseidon2::hash_many(&BabyBear::encode_hash(attr_bytes.as_bytes()));
    let value_bb = BabyBear::new(value as u32);
    poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO])
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a default private state with given attribute values.
    fn make_state(attrs: &[(&str, u64)]) -> PrivateState {
        let mut state = PrivateState::default();
        for &(name, value) in attrs {
            state.values.insert(name.to_string(), value);
        }
        state
    }

    /// Helper: create expected commitments matching the private state.
    fn make_commitments(attrs: &[(&str, u64)], state_root: BabyBear) -> HashMap<String, BabyBear> {
        let mut map = HashMap::new();
        for &(name, value) in attrs {
            let fact_hash = compute_attribute_fact_hash(name, value);
            let commitment = compute_fact_commitment(fact_hash, state_root);
            map.insert(name.to_string(), commitment);
        }
        map
    }

    // =========================================================================
    // Compilation tests
    // =========================================================================

    #[test]
    fn test_compile_single_range() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1000,
        });

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::Single {
                air_type,
                witness_spec,
            } => {
                assert_eq!(*air_type, AirType::Range);
                match witness_spec {
                    WitnessSpec::Range {
                        attribute,
                        predicate_type,
                        threshold,
                    } => {
                        assert_eq!(attribute, "balance");
                        assert_eq!(*predicate_type, PredicateType::Gte);
                        assert_eq!(*threshold, 1000);
                    }
                    _ => panic!("expected Range witness spec"),
                }
            }
            _ => panic!("expected Single compiled predicate"),
        }
    }

    #[test]
    fn test_compile_and_two_ranges_flattens_to_compound() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![
            PredicateExpr::Range {
                attribute: "age".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 18,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::CompoundRange {
                sub_predicates,
                formula,
            } => {
                assert_eq!(sub_predicates.len(), 2);
                assert_eq!(*formula, BooleanFormula::And(vec![0, 1]));
            }
            _ => panic!("expected CompoundRange, got {:?}", compiled),
        }
    }

    #[test]
    fn test_compile_or_ranges_flattens_to_compound() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::Or(vec![
            PredicateExpr::Range {
                attribute: "tier".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 3,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 10000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::CompoundRange { formula, .. } => {
                assert_eq!(*formula, BooleanFormula::Or(vec![0, 1]));
            }
            _ => panic!("expected CompoundRange"),
        }
    }

    #[test]
    fn test_compile_mixed_types_produces_composite() {
        // AND(range, temporal) cannot flatten because temporal uses a different AIR.
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
            },
            PredicateExpr::Temporal {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
                min_blocks: 30,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::Composite {
                sub_proofs,
                formula,
            } => {
                assert_eq!(sub_proofs.len(), 2);
                assert!(matches!(formula, CompositeFormula::And));
            }
            _ => panic!("expected Composite"),
        }
    }

    #[test]
    fn test_compile_nested_or_and_produces_composite() {
        // OR(AND(range, range), temporal) -> Composite because of mixed types.
        let program = PredicateProgram::with_default_depth(PredicateExpr::Or(vec![
            PredicateExpr::And(vec![
                PredicateExpr::Range {
                    attribute: "age".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 18,
                },
                PredicateExpr::Range {
                    attribute: "balance".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 500,
                },
            ]),
            PredicateExpr::Temporal {
                attribute: "reputation".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 50,
                min_blocks: 10,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::Composite {
                sub_proofs,
                formula,
            } => {
                assert_eq!(sub_proofs.len(), 2);
                assert!(matches!(formula, CompositeFormula::Or));
                // First sub-proof should be CompoundRange (AND of two ranges).
                assert!(matches!(
                    &sub_proofs[0],
                    CompiledPredicate::CompoundRange { .. }
                ));
                // Second should be Single(Temporal).
                assert!(matches!(
                    &sub_proofs[1],
                    CompiledPredicate::Single {
                        air_type: AirType::Temporal,
                        ..
                    }
                ));
            }
            _ => panic!("expected Composite"),
        }
    }

    #[test]
    fn test_compile_depth_exceeded() {
        // Create a deeply nested program.
        let mut expr = PredicateExpr::Range {
            attribute: "x".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1,
        };
        for _ in 0..5 {
            expr = PredicateExpr::And(vec![expr]);
        }
        // Depth is 6 (5 levels of And + 1 leaf).
        let program = PredicateProgram::new(expr, 3); // max_depth = 3
        let result = compile_predicate(&program);
        assert!(matches!(
            result,
            Err(CompileError::DepthExceeded { max: 3, .. })
        ));
    }

    #[test]
    fn test_compile_empty_and_fails() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![]));
        let result = compile_predicate(&program);
        assert_eq!(result, Err(CompileError::EmptyProgram));
    }

    #[test]
    fn test_compile_threshold_invalid_k() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::Threshold {
            k: 0,
            predicates: vec![PredicateExpr::Range {
                attribute: "x".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1,
            }],
        });
        let result = compile_predicate(&program);
        assert_eq!(result, Err(CompileError::InvalidThreshold { k: 0, n: 1 }));
    }

    #[test]
    fn test_compile_threshold_k_exceeds_n() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::Threshold {
            k: 3,
            predicates: vec![
                PredicateExpr::Range {
                    attribute: "a".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 1,
                },
                PredicateExpr::Range {
                    attribute: "b".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 1,
                },
            ],
        });
        let result = compile_predicate(&program);
        assert_eq!(result, Err(CompileError::InvalidThreshold { k: 3, n: 2 }));
    }

    // =========================================================================
    // Prove + verify roundtrip tests
    // =========================================================================

    #[test]
    fn test_prove_verify_single_range() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1000,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("balance", 5000)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("balance", 5000)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_single_range_unsatisfiable() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 10000,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("balance", 500)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_prove_verify_compound_and() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![
            PredicateExpr::Range {
                attribute: "age".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 18,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 25), ("balance", 5000)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("age", 25), ("balance", 5000)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_compound_and_one_fails() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![
            PredicateExpr::Range {
                attribute: "age".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 18,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 10000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 25), ("balance", 500)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_prove_verify_compound_or() {
        let state_root = BabyBear::new(99999);
        // OR(age >= 21, balance >= 10000) -- only age passes.
        let program = PredicateProgram::with_default_depth(PredicateExpr::Or(vec![
            PredicateExpr::Range {
                attribute: "age".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 21,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 10000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 25), ("balance", 500)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("age", 25), ("balance", 500)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_verify_threshold() {
        let state_root = BabyBear::new(99999);
        // At least 2 of (a >= 10, b >= 20, c >= 30): a=15 pass, b=25 pass, c=5 fail.
        let program = PredicateProgram::with_default_depth(PredicateExpr::Threshold {
            k: 2,
            predicates: vec![
                PredicateExpr::Range {
                    attribute: "a".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 10,
                },
                PredicateExpr::Range {
                    attribute: "b".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 20,
                },
                PredicateExpr::Range {
                    attribute: "c".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 30,
                },
            ],
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("a", 15), ("b", 25), ("c", 5)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("a", 15), ("b", 25), ("c", 5)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_verify_composite_or_with_temporal() {
        let state_root = BabyBear::new(99999);
        // OR(AND(age >= 18, balance >= 500), temporal(balance >= 1000 for 5 blocks))
        // We satisfy the first branch (AND).
        let program = PredicateProgram::with_default_depth(PredicateExpr::Or(vec![
            PredicateExpr::And(vec![
                PredicateExpr::Range {
                    attribute: "age".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 18,
                },
                PredicateExpr::Range {
                    attribute: "balance".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 500,
                },
            ]),
            PredicateExpr::Temporal {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
                min_blocks: 5,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 25), ("balance", 5000)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        // For OR composite, verification should pass with the first branch's proofs.
        let commitments = make_commitments(&[("age", 25), ("balance", 5000)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_verify_temporal() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Temporal {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 100,
            min_blocks: 5,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Provide temporal history.
        let mut private_state = PrivateState::default();
        private_state.values.insert("balance".to_string(), 200);
        let values: Vec<u64> = vec![200, 150, 300, 100, 500];
        let roots: Vec<BabyBear> = (0..5).map(|i| BabyBear::new(1000 + i)).collect();
        private_state
            .temporal_history
            .insert("balance".to_string(), (values, roots));

        let proof = prove_program(&compiled, &private_state, state_root).unwrap();
        assert!(matches!(proof.structure, ProofStructure::Single));
        assert_eq!(proof.sub_proofs.len(), 1);
        #[cfg(feature = "plonky3")]
        assert!(matches!(&proof.sub_proofs[0], SubProof::TemporalP3(_)));
        #[cfg(not(feature = "plonky3"))]
        assert!(matches!(&proof.sub_proofs[0], SubProof::Temporal(_)));
    }

    #[test]
    fn test_prove_temporal_insufficient_history() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Temporal {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 100,
            min_blocks: 10,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Only provide 5 steps when 10 are needed.
        let mut private_state = PrivateState::default();
        let values: Vec<u64> = vec![200, 150, 300, 100, 500];
        let roots: Vec<BabyBear> = (0..5).map(|i| BabyBear::new(1000 + i)).collect();
        private_state
            .temporal_history
            .insert("balance".to_string(), (values, roots));

        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(
            result,
            Err(ProveError::MissingTemporalData { .. })
        ));
    }

    #[test]
    fn test_prove_missing_attribute() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "nonexistent".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("balance", 5000)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::MissingAttribute(_))));
    }

    #[test]
    fn test_verify_fails_with_wrong_commitment() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1000,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("balance", 5000)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        // Use wrong commitments.
        let mut wrong_commitments = HashMap::new();
        wrong_commitments.insert("balance".to_string(), BabyBear::new(12345));
        assert!(!verify_program(
            &proof,
            &compiled,
            &wrong_commitments,
            state_root
        ));
    }

    // =========================================================================
    // Relational predicate prove + verify tests
    // =========================================================================

    #[test]
    fn test_prove_verify_relational_greater_than() {
        use crate::relational_predicate_air::{RelationType, compute_value_commitment};

        let state_root = BabyBear::new(99999);
        let my_value: u64 = 5000;
        let their_value: u64 = 3000;
        let my_blinding = BabyBear::new(111);
        let their_blinding = BabyBear::new(222);

        // Compute the counterparty's commitment (this would be published).
        let their_commitment =
            compute_value_commitment(BabyBear::new(their_value as u32), their_blinding);

        let program = PredicateProgram::with_default_depth(PredicateExpr::Relational {
            my_attribute: "bid".to_string(),
            their_commitment,
            relation: RelationType::GreaterThan,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Build private state with relational context.
        let mut private_state = PrivateState::default();
        private_state.values.insert("bid".to_string(), my_value);
        private_state.relational_context.insert(
            "bid".to_string(),
            RelationalContext {
                my_blinding,
                their_value,
                their_blinding,
            },
        );

        let proof = prove_program(&compiled, &private_state, state_root).unwrap();
        assert_eq!(proof.sub_proofs.len(), 1);
        assert!(matches!(&proof.sub_proofs[0], SubProof::Relational(_)));

        // Verify: the verifier knows my_commitment (from my published commitment)
        // and their_commitment (from the program).
        let my_commitment = compute_value_commitment(BabyBear::new(my_value as u32), my_blinding);
        let mut expected_commitments = HashMap::new();
        expected_commitments.insert("bid".to_string(), my_commitment);

        assert!(verify_program(
            &proof,
            &compiled,
            &expected_commitments,
            state_root
        ));
    }

    #[test]
    fn test_prove_relational_unsatisfiable() {
        use crate::relational_predicate_air::{RelationType, compute_value_commitment};

        let state_root = BabyBear::new(99999);
        let my_value: u64 = 1000; // Less than their value
        let their_value: u64 = 3000;
        let my_blinding = BabyBear::new(111);
        let their_blinding = BabyBear::new(222);

        let their_commitment =
            compute_value_commitment(BabyBear::new(their_value as u32), their_blinding);

        let program = PredicateProgram::with_default_depth(PredicateExpr::Relational {
            my_attribute: "bid".to_string(),
            their_commitment,
            relation: RelationType::GreaterThan,
        });

        let compiled = compile_predicate(&program).unwrap();

        let mut private_state = PrivateState::default();
        private_state.values.insert("bid".to_string(), my_value);
        private_state.relational_context.insert(
            "bid".to_string(),
            RelationalContext {
                my_blinding,
                their_value,
                their_blinding,
            },
        );

        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_prove_relational_missing_context() {
        use crate::relational_predicate_air::{RelationType, compute_value_commitment};

        let state_root = BabyBear::new(99999);
        let their_commitment = compute_value_commitment(BabyBear::new(3000), BabyBear::new(222));

        let program = PredicateProgram::with_default_depth(PredicateExpr::Relational {
            my_attribute: "bid".to_string(),
            their_commitment,
            relation: RelationType::GreaterThan,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Provide the value but NO relational context.
        let mut private_state = PrivateState::default();
        private_state.values.insert("bid".to_string(), 5000);

        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::ProofGenerationFailed(_))));
    }

    // =========================================================================
    // Committed-threshold predicate prove + verify tests
    // =========================================================================

    #[test]
    fn test_prove_verify_committed_threshold() {
        use crate::committed_threshold::compute_threshold_commitment;

        let state_root = BabyBear::new(99999);
        let my_value: u64 = 750;
        let threshold: u64 = 700;
        let blinding = BabyBear::new(12345);

        let threshold_commitment =
            compute_threshold_commitment(BabyBear::new(threshold as u32), blinding);

        let program = PredicateProgram::with_default_depth(PredicateExpr::CommittedThreshold {
            attribute: "credit_score".to_string(),
            threshold_commitment,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Build private state with committed-threshold context.
        let mut private_state = PrivateState::default();
        private_state
            .values
            .insert("credit_score".to_string(), my_value);
        private_state.committed_thresholds.insert(
            "credit_score".to_string(),
            CommittedThresholdContext {
                threshold,
                blinding,
            },
        );

        let proof = prove_program(&compiled, &private_state, state_root).unwrap();
        assert_eq!(proof.sub_proofs.len(), 1);
        assert!(matches!(
            &proof.sub_proofs[0],
            SubProof::CommittedThreshold(_)
        ));

        // Verify: the verifier's expected commitment is the fact_commitment for the attribute.
        let fact_hash = compute_attribute_fact_hash("credit_score", my_value);
        let fact_commitment = compute_fact_commitment(fact_hash, state_root);
        let mut expected_commitments = HashMap::new();
        expected_commitments.insert("credit_score".to_string(), fact_commitment);

        assert!(verify_program(
            &proof,
            &compiled,
            &expected_commitments,
            state_root
        ));
    }

    #[test]
    fn test_prove_committed_threshold_unsatisfiable() {
        use crate::committed_threshold::compute_threshold_commitment;

        let state_root = BabyBear::new(99999);
        let my_value: u64 = 500; // Below threshold
        let threshold: u64 = 700;
        let blinding = BabyBear::new(12345);

        let threshold_commitment =
            compute_threshold_commitment(BabyBear::new(threshold as u32), blinding);

        let program = PredicateProgram::with_default_depth(PredicateExpr::CommittedThreshold {
            attribute: "credit_score".to_string(),
            threshold_commitment,
        });

        let compiled = compile_predicate(&program).unwrap();

        let mut private_state = PrivateState::default();
        private_state
            .values
            .insert("credit_score".to_string(), my_value);
        private_state.committed_thresholds.insert(
            "credit_score".to_string(),
            CommittedThresholdContext {
                threshold,
                blinding,
            },
        );

        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_prove_committed_threshold_missing_context() {
        use crate::committed_threshold::compute_threshold_commitment;

        let state_root = BabyBear::new(99999);
        let threshold_commitment =
            compute_threshold_commitment(BabyBear::new(700), BabyBear::new(12345));

        let program = PredicateProgram::with_default_depth(PredicateExpr::CommittedThreshold {
            attribute: "credit_score".to_string(),
            threshold_commitment,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Provide the value but NO committed-threshold context.
        let mut private_state = PrivateState::default();
        private_state.values.insert("credit_score".to_string(), 750);

        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::ProofGenerationFailed(_))));
    }

    #[test]
    fn test_prove_verify_composite_relational_and_range() {
        use crate::relational_predicate_air::{RelationType, compute_value_commitment};

        let state_root = BabyBear::new(99999);
        let my_bid: u64 = 5000;
        let their_bid: u64 = 3000;
        let my_blinding = BabyBear::new(333);
        let their_blinding = BabyBear::new(444);

        let their_commitment =
            compute_value_commitment(BabyBear::new(their_bid as u32), their_blinding);

        // AND(my_bid > their_bid, reputation >= 50)
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![
            PredicateExpr::Relational {
                my_attribute: "bid".to_string(),
                their_commitment,
                relation: RelationType::GreaterThan,
            },
            PredicateExpr::Range {
                attribute: "reputation".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 50,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        // Should produce a Composite (mixed AIR types).
        assert!(matches!(compiled, CompiledPredicate::Composite { .. }));

        let mut private_state = PrivateState::default();
        private_state.values.insert("bid".to_string(), my_bid);
        private_state.values.insert("reputation".to_string(), 85);
        private_state.relational_context.insert(
            "bid".to_string(),
            RelationalContext {
                my_blinding,
                their_value: their_bid,
                their_blinding,
            },
        );

        let proof = prove_program(&compiled, &private_state, state_root).unwrap();
        assert_eq!(proof.sub_proofs.len(), 2);
        assert!(matches!(&proof.sub_proofs[0], SubProof::Relational(_)));
        assert!(matches!(&proof.sub_proofs[1], SubProof::Range(_)));
    }

    // =========================================================================
    // Negation extension tests
    // =========================================================================

    #[test]
    fn test_compile_neq() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::Neq {
            attribute: "status".to_string(),
            value: 0,
        });

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::Single {
                air_type,
                witness_spec,
            } => {
                assert_eq!(*air_type, AirType::Arithmetic);
                match witness_spec {
                    WitnessSpec::Arithmetic {
                        inputs, predicate, ..
                    } => {
                        assert_eq!(inputs.len(), 1);
                        assert_eq!(inputs[0], "status");
                        assert!(matches!(
                            predicate,
                            crate::arithmetic_predicate_air::ArithPredicate::ExprNeq(_, _)
                        ));
                    }
                    _ => panic!("expected Arithmetic witness spec"),
                }
            }
            _ => panic!("expected Single compiled predicate"),
        }
    }

    #[test]
    fn test_prove_verify_neq() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Neq {
            attribute: "status".to_string(),
            value: 0,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("status", 5)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        // Build expected commitments for the arithmetic predicate.
        use crate::arithmetic_predicate_air::compute_arithmetic_fact_commitment;
        let fact_hash = compute_attribute_fact_hash("status", 5);
        let fact_commitment = compute_arithmetic_fact_commitment(fact_hash, state_root);
        let mut commitments = HashMap::new();
        commitments.insert("status".to_string(), fact_commitment);

        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_neq_fails_when_equal() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Neq {
            attribute: "status".to_string(),
            value: 5,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("status", 5)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_compile_not_in_range() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::NotInRange {
            attribute: "age".to_string(),
            low: 18,
            high: 65,
        });

        let compiled = compile_predicate(&program).unwrap();
        // Should compile to CompoundRange with Or(Lt(18), Gt(65))
        match &compiled {
            CompiledPredicate::CompoundRange {
                sub_predicates,
                formula,
            } => {
                assert_eq!(sub_predicates.len(), 2);
                assert_eq!(*formula, BooleanFormula::Or(vec![0, 1]));
            }
            _ => panic!("expected CompoundRange, got {:?}", compiled),
        }
    }

    #[test]
    fn test_prove_verify_not_in_range_below() {
        // value=10, not in [18, 65] -> passes because 10 < 18
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::NotInRange {
            attribute: "age".to_string(),
            low: 18,
            high: 65,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 10)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("age", 10)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_verify_not_in_range_above() {
        // value=70, not in [18, 65] -> passes because 70 > 65
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::NotInRange {
            attribute: "age".to_string(),
            low: 18,
            high: 65,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 70)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("age", 70)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_not_in_range_fails_when_inside() {
        // value=30, not in [18, 65] -> fails because 30 is in [18, 65]
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::NotInRange {
            attribute: "age".to_string(),
            low: 18,
            high: 65,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 30)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_compile_threshold_below() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::ThresholdBelow {
            max_k: 2,
            predicates: vec![
                PredicateExpr::Range {
                    attribute: "a".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 10,
                },
                PredicateExpr::Range {
                    attribute: "b".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 20,
                },
                PredicateExpr::Range {
                    attribute: "c".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 30,
                },
            ],
        });

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::Composite {
                sub_proofs,
                formula,
            } => {
                assert_eq!(sub_proofs.len(), 3);
                assert_eq!(*formula, CompositeFormula::ThresholdBelow(2));
            }
            _ => panic!("expected Composite, got {:?}", compiled),
        }
    }

    #[test]
    fn test_prove_verify_threshold_below_succeeds() {
        // ThresholdBelow(2): fewer than 2 predicates hold.
        // a=15 (pass a>=10), b=10 (fail b>=20), c=5 (fail c>=30)
        // Only 1 passes, which is < 2, so ThresholdBelow succeeds.
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::ThresholdBelow {
            max_k: 2,
            predicates: vec![
                PredicateExpr::Range {
                    attribute: "a".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 10,
                },
                PredicateExpr::Range {
                    attribute: "b".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 20,
                },
                PredicateExpr::Range {
                    attribute: "c".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 30,
                },
            ],
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("a", 15), ("b", 10), ("c", 5)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("a", 15), ("b", 10), ("c", 5)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_threshold_below_fails_when_too_many_pass() {
        // ThresholdBelow(2): fewer than 2 predicates hold.
        // a=15 (pass a>=10), b=25 (pass b>=20), c=5 (fail c>=30)
        // 2 pass, which is NOT < 2, so ThresholdBelow fails.
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::ThresholdBelow {
            max_k: 2,
            predicates: vec![
                PredicateExpr::Range {
                    attribute: "a".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 10,
                },
                PredicateExpr::Range {
                    attribute: "b".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 20,
                },
                PredicateExpr::Range {
                    attribute: "c".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 30,
                },
            ],
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("a", 15), ("b", 25), ("c", 5)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_compile_nor_all_range() {
        // NOR(a >= 10, b >= 20) = AND(a < 10, b < 20)
        let predicates = vec![
            PredicateExpr::Range {
                attribute: "a".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 10,
            },
            PredicateExpr::Range {
                attribute: "b".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 20,
            },
        ];

        let nor_expr = compile_nor(&predicates);

        // Should be And(Lt(10), Lt(20))
        match &nor_expr {
            PredicateExpr::And(children) => {
                assert_eq!(children.len(), 2);
                match &children[0] {
                    PredicateExpr::Range {
                        attribute,
                        predicate_type,
                        threshold,
                    } => {
                        assert_eq!(attribute, "a");
                        assert_eq!(*predicate_type, PredicateType::Lt);
                        assert_eq!(*threshold, 10);
                    }
                    _ => panic!("expected Range"),
                }
                match &children[1] {
                    PredicateExpr::Range {
                        attribute,
                        predicate_type,
                        threshold,
                    } => {
                        assert_eq!(attribute, "b");
                        assert_eq!(*predicate_type, PredicateType::Lt);
                        assert_eq!(*threshold, 20);
                    }
                    _ => panic!("expected Range"),
                }
            }
            _ => panic!("expected And"),
        }
    }

    #[test]
    fn test_prove_verify_nor() {
        // NOR(a >= 100, b >= 200): neither holds for a=50, b=100
        let state_root = BabyBear::new(99999);
        let predicates = vec![
            PredicateExpr::Range {
                attribute: "a".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 100,
            },
            PredicateExpr::Range {
                attribute: "b".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 200,
            },
        ];

        let nor_expr = compile_nor(&predicates);
        let program = PredicateProgram::with_default_depth(nor_expr);
        let compiled = compile_predicate(&program).unwrap();

        let private_state = make_state(&[("a", 50), ("b", 100)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("a", 50), ("b", 100)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_nor_fails_when_one_holds() {
        // NOR(a >= 100, b >= 200): fails because a=150 >= 100
        let state_root = BabyBear::new(99999);
        let predicates = vec![
            PredicateExpr::Range {
                attribute: "a".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 100,
            },
            PredicateExpr::Range {
                attribute: "b".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 200,
            },
        ];

        let nor_expr = compile_nor(&predicates);
        let program = PredicateProgram::with_default_depth(nor_expr);
        let compiled = compile_predicate(&program).unwrap();

        let private_state = make_state(&[("a", 150), ("b", 100)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_compile_nor_with_neq() {
        // NOR(value != 0) should flip to value == 0
        let predicates = vec![PredicateExpr::Neq {
            attribute: "status".to_string(),
            value: 0,
        }];

        let nor_expr = compile_nor(&predicates);
        match &nor_expr {
            PredicateExpr::And(children) => {
                assert_eq!(children.len(), 1);
                match &children[0] {
                    PredicateExpr::Arithmetic { predicate, .. } => {
                        assert!(matches!(
                            predicate,
                            crate::arithmetic_predicate_air::ArithPredicate::ExprEq(_, _)
                        ));
                    }
                    _ => panic!("expected Arithmetic with ExprEq"),
                }
            }
            _ => panic!("expected And"),
        }
    }

    // =========================================================================
    // NOT(Membership) -> NonMembership compilation tests
    // =========================================================================

    #[test]
    fn test_compile_not_membership_becomes_non_membership() {
        // NOT(Membership { attribute, set_commitment }) should compile to NonMembership.
        let set_commitment = BabyBear::new(0x1234);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Not(Box::new(
            PredicateExpr::Membership {
                attribute: "user_id".to_string(),
                set_commitment,
            },
        )));

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::Single {
                air_type,
                witness_spec,
            } => {
                assert_eq!(*air_type, AirType::NonMembership);
                match witness_spec {
                    WitnessSpec::NonMembership { attribute, set_id } => {
                        assert_eq!(attribute, "user_id");
                        assert_eq!(*set_id, set_commitment);
                    }
                    _ => panic!("expected NonMembership witness spec"),
                }
            }
            _ => panic!("expected Single compiled predicate, got {:?}", compiled),
        }
    }

    #[test]
    fn test_compile_not_range_still_rejected() {
        // NOT(Range { ... }) should still produce UnsupportedNot.
        let program = PredicateProgram::with_default_depth(PredicateExpr::Not(Box::new(
            PredicateExpr::Range {
                attribute: "age".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 18,
            },
        )));

        let result = compile_predicate(&program);
        assert_eq!(result, Err(CompileError::UnsupportedNot));
    }

    #[test]
    fn test_prove_verify_non_membership_via_program() {
        use crate::non_membership::SetIdentifier;
        use crate::poseidon2::hash_many;

        let state_root = BabyBear::new(99999);

        // Create a "suspended users" set.
        let suspended_set: Vec<BabyBear> = (1..=5)
            .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xBEEF)]))
            .collect();

        // The set_id doubles as the set_commitment in this integration.
        let set_id_value = BabyBear::new(0xAAAA);

        // Build a NonMembership predicate directly.
        let program = PredicateProgram::with_default_depth(PredicateExpr::NonMembership {
            attribute: "credential".to_string(),
            set_id: set_id_value,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Build private state with non-membership context.
        let mut private_state = PrivateState::default();
        private_state.values.insert("credential".to_string(), 9999);

        // The fact hash for the credential must NOT be in the suspended set.
        let cred_fact_hash = compute_attribute_fact_hash("credential", 9999);
        assert!(!suspended_set.contains(&cred_fact_hash));

        private_state.non_membership_context.insert(
            "credential".to_string(),
            NonMembershipContext {
                set_name: "suspended".to_string(),
                set_elements: suspended_set.clone(),
            },
        );

        let proof = prove_program(&compiled, &private_state, state_root).unwrap();
        assert_eq!(proof.sub_proofs.len(), 1);
        assert!(matches!(&proof.sub_proofs[0], SubProof::NonMembership(_)));

        // Verify.
        let commitments = HashMap::new(); // NonMembership doesn't use fact commitments for verification.
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_non_membership_fails_when_in_set() {
        use crate::poseidon2::hash_many;

        let state_root = BabyBear::new(99999);
        let set_id_value = BabyBear::new(0xBBBB);

        let program = PredicateProgram::with_default_depth(PredicateExpr::NonMembership {
            attribute: "credential".to_string(),
            set_id: set_id_value,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Make the credential's fact hash equal to one of the set elements.
        let cred_fact_hash = compute_attribute_fact_hash("credential", 42);

        // Build set that INCLUDES the credential hash.
        let suspended_set = vec![
            BabyBear::new(111),
            cred_fact_hash, // The credential IS in the set.
            BabyBear::new(333),
        ];

        let mut private_state = PrivateState::default();
        private_state.values.insert("credential".to_string(), 42);
        private_state.non_membership_context.insert(
            "credential".to_string(),
            NonMembershipContext {
                set_name: "suspended".to_string(),
                set_elements: suspended_set,
            },
        );

        let result = prove_program(&compiled, &private_state, state_root);
        assert!(
            matches!(result, Err(ProveError::NotSatisfiable(_))),
            "Should fail when element IS in set: {:?}",
            result
        );
    }
}
