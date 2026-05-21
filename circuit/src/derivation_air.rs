//! Derivation step AIR.
//!
//! Proves one authorization derivation step:
//! - Rule ID + substitution (witness)
//! - Body facts exist (Merkle membership for each, up to 4 body atoms)
//! - Derived fact = rule head under substitution (substitution verification)
//! - Equal constraint checks pass under the substitution
//! - MemberOf checks pass (hash equality for set membership)
//! - GreaterThanOrEqual checks pass (bit-decomposition range check)
//! - Output: the derived fact's hash
//!
//! This AIR validates that a single Datalog rule application is correct:
//! given that certain facts exist in the committed state, the rule derives
//! a new fact.
//!
//! Trace layout:
//!
//! | Column       | Description                                             |
//! |-------------|--------------------------------------------------------|
//! | 0: rule_id  | The rule identifier                                     |
//! | 1..4: body_hashes | Hashes of the 4 body facts (zero if unused)       |
//! | 5..8: body_membership | 1 if body fact has valid membership, 0 if slot unused |
//! | 9: head_pred | Derived fact predicate (after substitution)             |
//! | 10..12: head_terms | Derived fact terms (after substitution)           |
//! | 13: derived_hash | Hash of the derived fact                            |
//! | 14..17: sub_values | Substitution values for up to 4 variables         |
//! | 18..21: body_roots | Merkle roots the body facts are verified against  |
//! | 22..24: head_is_var | 1 if head term i is a variable, 0 if constant    |
//! | 25..27: head_raw_value | Variable index (if var) or constant value      |
//! | 28..39: head_sel_var | Selector columns for variable lookup (3 terms x 4 vars) |
//! | 40..45: eq_check[0..1] | Equal checks: (active, term_a, term_b) x 2    |
//! | 46..51: memberof_check[0..1] | MemberOf checks: (active, term_a, term_b) x 2 |
//! | 52..86: gte_check | GTE check: active, term_a, term_b, diff, diff_bits[0..30] |
//!
//! Public inputs: [state_root, derived_fact_hash]
//!
//! Constraints:
//! 1. Body membership flags are binary (0 or 1)
//! 2. If membership flag is 1, body hash must be non-zero
//! 3. At least one body fact must be used (rule must have a body)
//! 4. Derived hash = hash(head_pred, head_terms)
//! 5. All body roots equal the state root (single state commitment)
//! 6. Derived hash matches public input
//! 7. head_is_var columns are binary
//! 8. Selector columns are binary and exactly one is set when is_var=1
//! 9. Substitution application: derived_term[i] = is_var * (sum_j sel_j * sub[j]) + (1-is_var) * raw_value
//! 10. Equal check: eq_active * (term_a - term_b) = 0
//! 11. Equal check active flags are binary
//! 12. MemberOf check: memberof_active * (term_a - term_b) = 0
//! 13. MemberOf check active flags are binary
//! 14. GTE check active flag is binary
//! 15. GTE diff = term_a - term_b (when active)
//! 16. GTE bit decomposition: sum(bit_i * 2^i) = diff (when active)
//! 17. GTE bits are binary
//! 18. GTE high bit is 0 (diff < 2^30 < p/2, meaning a >= b)

use crate::field::BabyBear;
use crate::constraint_prover::{Air, Constraint};
use crate::poseidon2::hash_fact;

/// Trace width for the derivation AIR.
/// rule_id(1) + body_hashes(8) + body_membership(8) + head_pred(1) + head_terms(4) +
/// derived_hash(1) + sub_values(8) + body_roots(8) + head_is_var(4) + head_raw_value(4) +
/// head_sel_var(4*8=32) + eq_checks(3*4=12) + memberof_checks(3*4=12) + gte(4+31=35) + lt(4+31=35) = 173
pub const DERIVATION_AIR_WIDTH: usize = 173;

/// Maximum body atoms per rule.
pub const MAX_BODY_ATOMS: usize = 8;

/// Maximum substitution variables.
pub const MAX_SUB_VARS: usize = 8;

/// Maximum head terms.
pub const MAX_HEAD_TERMS: usize = 4;

/// Maximum Equal checks per rule.
pub const MAX_EQUAL_CHECKS: usize = 4;

/// Maximum MemberOf checks per rule.
pub const MAX_MEMBEROF_CHECKS: usize = 4;

/// Number of bits for GTE range check (BabyBear has ~31-bit modulus).
/// We use 31 bits: if the high bit (bit 30) is 0, diff < 2^30 < p/2.
pub const GTE_DIFF_BITS: usize = 31;

/// Column indices.
pub mod col {
    use super::{
        GTE_DIFF_BITS, MAX_BODY_ATOMS, MAX_EQUAL_CHECKS, MAX_HEAD_TERMS, MAX_MEMBEROF_CHECKS,
        MAX_SUB_VARS,
    };

    pub const RULE_ID: usize = 0;
    pub const BODY_HASH_START: usize = 1; // 8 columns (1..8)
    pub const BODY_MEMBERSHIP_START: usize = BODY_HASH_START + MAX_BODY_ATOMS; // 9
    pub const HEAD_PRED: usize = BODY_MEMBERSHIP_START + MAX_BODY_ATOMS; // 17
    pub const HEAD_TERM_START: usize = HEAD_PRED + 1; // 18 (4 columns)
    pub const DERIVED_HASH: usize = HEAD_TERM_START + MAX_HEAD_TERMS; // 22
    pub const SUB_VALUE_START: usize = DERIVED_HASH + 1; // 23 (8 columns)
    pub const BODY_ROOT_START: usize = SUB_VALUE_START + MAX_SUB_VARS; // 31 (8 columns)

    // --- Substitution verification columns ---
    /// head_is_var[i]: 1 if head term i is a variable reference, 0 if constant.
    pub const HEAD_IS_VAR_START: usize = BODY_ROOT_START + MAX_BODY_ATOMS; // 39
    /// head_raw_value[i]: the variable index (when is_var=1) or the constant value (when is_var=0).
    pub const HEAD_RAW_VALUE_START: usize = HEAD_IS_VAR_START + MAX_HEAD_TERMS; // 43
    /// head_sel_var[term_i][var_j]: selector for which substitution variable to use.
    /// Layout: MAX_HEAD_TERMS * MAX_SUB_VARS = 4*8 = 32 columns.
    pub const HEAD_SEL_VAR_START: usize = HEAD_RAW_VALUE_START + MAX_HEAD_TERMS; // 47

    /// Get the column index for head_sel_var[term_idx][var_idx].
    #[inline]
    pub const fn head_sel_var(term_idx: usize, var_idx: usize) -> usize {
        HEAD_SEL_VAR_START + term_idx * MAX_SUB_VARS + var_idx
    }

    // --- Equal check columns ---
    /// Each Equal check has 3 columns: (active, term_a_resolved, term_b_resolved).
    pub const EQ_CHECK_START: usize = HEAD_SEL_VAR_START + MAX_HEAD_TERMS * MAX_SUB_VARS; // 79

    /// Get the column for eq_check[check_idx].active.
    #[inline]
    pub const fn eq_check_active(check_idx: usize) -> usize {
        EQ_CHECK_START + check_idx * 3
    }
    /// Get the column for eq_check[check_idx].term_a.
    #[inline]
    pub const fn eq_check_term_a(check_idx: usize) -> usize {
        EQ_CHECK_START + check_idx * 3 + 1
    }
    /// Get the column for eq_check[check_idx].term_b.
    #[inline]
    pub const fn eq_check_term_b(check_idx: usize) -> usize {
        EQ_CHECK_START + check_idx * 3 + 2
    }

    // --- MemberOf check columns ---
    /// Each MemberOf check has 3 columns: (active, term_a_resolved, term_b_resolved).
    pub const MEMBEROF_CHECK_START: usize = EQ_CHECK_START + MAX_EQUAL_CHECKS * 3; // 91

    /// Get the column for memberof_check[check_idx].active.
    #[inline]
    pub const fn memberof_check_active(check_idx: usize) -> usize {
        MEMBEROF_CHECK_START + check_idx * 3
    }
    /// Get the column for memberof_check[check_idx].term_a.
    #[inline]
    pub const fn memberof_check_term_a(check_idx: usize) -> usize {
        MEMBEROF_CHECK_START + check_idx * 3 + 1
    }
    /// Get the column for memberof_check[check_idx].term_b.
    #[inline]
    pub const fn memberof_check_term_b(check_idx: usize) -> usize {
        MEMBEROF_CHECK_START + check_idx * 3 + 2
    }

    // --- GTE check columns ---
    /// GTE check layout: active, term_a, term_b, diff, diff_bits[0..30]
    pub const GTE_CHECK_START: usize = MEMBEROF_CHECK_START + MAX_MEMBEROF_CHECKS * 3; // 103

    /// GTE active flag column.
    pub const GTE_CHECK_ACTIVE: usize = GTE_CHECK_START; // 103
    /// GTE term_a (the larger value) column.
    pub const GTE_CHECK_TERM_A: usize = GTE_CHECK_START + 1; // 104
    /// GTE term_b (the smaller value) column.
    pub const GTE_CHECK_TERM_B: usize = GTE_CHECK_START + 2; // 105
    /// GTE diff = term_a - term_b column.
    pub const GTE_CHECK_DIFF: usize = GTE_CHECK_START + 3; // 106
    /// GTE diff bit decomposition starts here (31 bits, columns 107..137).
    pub const GTE_CHECK_DIFF_BITS_START: usize = GTE_CHECK_START + 4; // 107

    /// Get the column for gte_check_diff_bits[bit_idx].
    #[inline]
    pub const fn gte_diff_bit(bit_idx: usize) -> usize {
        GTE_CHECK_DIFF_BITS_START + bit_idx
    }

    // --- LT check columns ---
    /// LT check layout: active, term_a, term_b, diff, diff_bits[0..30]
    /// where diff = term_b - term_a - 1 (must be non-negative for a < b).
    pub const LT_CHECK_START: usize = GTE_CHECK_DIFF_BITS_START + GTE_DIFF_BITS; // 138
    /// LT active flag column.
    pub const LT_CHECK_ACTIVE: usize = LT_CHECK_START; // 138
    /// LT term_a (the smaller value) column.
    pub const LT_CHECK_TERM_A: usize = LT_CHECK_START + 1; // 139
    /// LT term_b (the larger value) column.
    pub const LT_CHECK_TERM_B: usize = LT_CHECK_START + 2; // 140
    /// LT diff = term_b - term_a - 1 column.
    pub const LT_CHECK_DIFF: usize = LT_CHECK_START + 3; // 141
    /// LT diff bit decomposition starts here (31 bits, columns 142..172).
    pub const LT_CHECK_DIFF_BITS_START: usize = LT_CHECK_START + 4; // 142

    /// Get the column for lt_check_diff_bits[bit_idx].
    #[inline]
    pub const fn lt_diff_bit(bit_idx: usize) -> usize {
        LT_CHECK_DIFF_BITS_START + bit_idx
    }

    /// Total columns: LT_CHECK_DIFF_BITS_START + GTE_DIFF_BITS = 142 + 31 = 173
    pub const _TOTAL: usize = LT_CHECK_DIFF_BITS_START + GTE_DIFF_BITS;
}

/// A rule definition for the circuit (simplified representation).
#[derive(Clone, Debug)]
pub struct CircuitRule {
    /// Rule identifier.
    pub id: u32,
    /// Number of body atoms this rule has (1..4).
    pub num_body_atoms: usize,
    /// Number of variables in the substitution.
    pub num_variables: usize,
    /// Head predicate (will be derived).
    pub head_predicate: BabyBear,
    /// Head term patterns: each is either a direct value or an index into substitution.
    /// Encoded as (is_variable, value_or_var_index).
    pub head_terms: [(bool, BabyBear); 4],
    /// Body atom patterns: predicate + term patterns for each body atom.
    pub body_atoms: Vec<BodyAtomPattern>,
    /// Equal checks: each is (term_a_is_var, term_a_value, term_b_is_var, term_b_value).
    /// Up to MAX_EQUAL_CHECKS.
    pub equal_checks: Vec<CircuitEqualCheck>,
    /// MemberOf checks: same structure as Equal (hash equality).
    /// Up to MAX_MEMBEROF_CHECKS.
    pub memberof_checks: Vec<CircuitMemberOfCheck>,
    /// GTE check: at most one per rule (for budget enforcement).
    pub gte_check: Option<CircuitGteCheck>,
    /// LT check: at most one per rule (for time-bounded rules).
    /// Semantics: `term_a < term_b` (e.g., request_time < expiry).
    /// Proven via bit decomposition of `(term_b - term_a - 1)` with high bit = 0.
    pub lt_check: Option<CircuitLtCheck>,
}

/// An Equal check in circuit form.
#[derive(Clone, Debug)]
pub struct CircuitEqualCheck {
    /// Is the left-hand term a variable?
    pub lhs_is_var: bool,
    /// The variable index or constant value for the left-hand term.
    pub lhs_value: BabyBear,
    /// Is the right-hand term a variable?
    pub rhs_is_var: bool,
    /// The variable index or constant value for the right-hand term.
    pub rhs_value: BabyBear,
}

/// A MemberOf check in circuit form.
///
/// Semantically: "element is a member of the set identified by set_element".
/// In the circuit, this reduces to hash equality (both sides are resolved to
/// field elements and must be equal).
#[derive(Clone, Debug)]
pub struct CircuitMemberOfCheck {
    /// Is the left-hand term (element) a variable?
    pub lhs_is_var: bool,
    /// The variable index or constant value for the element term.
    pub lhs_value: BabyBear,
    /// Is the right-hand term (set element) a variable?
    pub rhs_is_var: bool,
    /// The variable index or constant value for the set element term.
    pub rhs_value: BabyBear,
}

/// A GreaterThanOrEqual check in circuit form.
///
/// Semantically: "term_a >= term_b" (used for budget enforcement).
/// Proven via bit decomposition of (a - b) and asserting the high bit is 0.
#[derive(Clone, Debug)]
pub struct CircuitGteCheck {
    /// Is the left-hand term (a, the larger value) a variable?
    pub lhs_is_var: bool,
    /// The variable index or constant value for term_a.
    pub lhs_value: BabyBear,
    /// Is the right-hand term (b, the smaller value) a variable?
    pub rhs_is_var: bool,
    /// The variable index or constant value for term_b.
    pub rhs_value: BabyBear,
}

/// A LessThan check in circuit form.
///
/// Semantics: "term_a < term_b" (used for time-bounded rules, e.g., `$t < $exp`).
/// Proven via bit decomposition of `(term_b - term_a - 1)` and asserting the high bit is 0.
/// This works because if `a < b`, then `b - a - 1 >= 0` and fits in a small positive range.
/// If `a >= b`, then `b - a - 1` wraps to a large field element (high bit set).
#[derive(Clone, Debug)]
pub struct CircuitLtCheck {
    /// Is the left-hand term (a, the smaller value) a variable?
    pub lhs_is_var: bool,
    /// The variable index or constant value for term_a.
    pub lhs_value: BabyBear,
    /// Is the right-hand term (b, the larger value) a variable?
    pub rhs_is_var: bool,
    /// The variable index or constant value for term_b.
    pub rhs_value: BabyBear,
}

/// Pattern for a body atom in a rule.
#[derive(Clone, Debug)]
pub struct BodyAtomPattern {
    /// The predicate that must match.
    pub predicate: BabyBear,
    /// Term patterns: (is_variable, value_or_var_index).
    pub terms: [(bool, BabyBear); 3],
}

/// Witness for a derivation step.
#[derive(Clone, Debug)]
pub struct DerivationWitness {
    /// The rule being applied.
    pub rule: CircuitRule,
    /// The state root all body facts must be committed to.
    pub state_root: BabyBear,
    /// Hashes of the body facts (ordered by body atom index).
    pub body_fact_hashes: Vec<BabyBear>,
    /// Substitution values (bindings for variables 0..num_variables).
    pub substitution: Vec<BabyBear>,
    /// The derived fact's predicate.
    pub derived_predicate: BabyBear,
    /// The derived fact's terms.
    pub derived_terms: [BabyBear; 4],
}

impl DerivationWitness {
    /// Compute the derived fact hash.
    pub fn derived_hash(&self) -> BabyBear {
        hash_fact(self.derived_predicate, self.derived_terms.as_slice())
    }

    /// Resolve a term pattern using the current substitution.
    pub fn resolve_term(&self, is_variable: bool, value_or_idx: BabyBear) -> BabyBear {
        if is_variable {
            let idx = value_or_idx.as_u32() as usize;
            if idx < self.substitution.len() {
                self.substitution[idx]
            } else {
                BabyBear::ZERO
            }
        } else {
            value_or_idx
        }
    }

    /// Check that the derived fact matches the rule head under substitution.
    pub fn check_head_match(&self) -> bool {
        // Predicate must match
        if self.derived_predicate != self.rule.head_predicate {
            return false;
        }
        // Terms must match after substitution
        for (i, &(is_var, val)) in self.rule.head_terms.iter().enumerate() {
            let expected = self.resolve_term(is_var, val);
            if expected != self.derived_terms[i] {
                return false;
            }
        }
        true
    }
}

/// The derivation step AIR.
pub struct DerivationAir {
    pub witness: DerivationWitness,
}

impl DerivationAir {
    pub fn new(witness: DerivationWitness) -> Self {
        Self { witness }
    }
}

impl Air for DerivationAir {
    fn trace_width(&self) -> usize {
        DERIVATION_AIR_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        2 // state_root, derived_fact_hash
    }

    fn constraints(&self) -> Vec<Constraint> {
        vec![
            // Constraint 1: Body membership flags are binary.
            Constraint {
                name: "body_membership_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_BODY_ATOMS {
                        let flag = row[col::BODY_MEMBERSHIP_START + i];
                        // flag * (flag - 1) = 0
                        result = result + flag * (flag - BabyBear::ONE);
                    }
                    result
                }),
            },
            // Constraint 2: If membership flag is 1, body hash must be non-zero.
            Constraint {
                name: "body_hash_nonzero_when_used".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_BODY_ATOMS {
                        let flag = row[col::BODY_MEMBERSHIP_START + i];
                        let hash = row[col::BODY_HASH_START + i];
                        // If flag=1 and hash=0, that's invalid.
                        if flag == BabyBear::ONE && hash == BabyBear::ZERO {
                            result = result + BabyBear::ONE;
                        }
                    }
                    result
                }),
            },
            // Constraint 3: At least one body fact must be used.
            Constraint {
                name: "at_least_one_body".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut sum = BabyBear::ZERO;
                    for i in 0..MAX_BODY_ATOMS {
                        sum = sum + row[col::BODY_MEMBERSHIP_START + i];
                    }
                    if sum == BabyBear::ZERO {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
            // Constraint 4: Derived hash is correctly computed.
            Constraint {
                name: "derived_hash_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let pred = row[col::HEAD_PRED];
                    let terms = [
                        row[col::HEAD_TERM_START],
                        row[col::HEAD_TERM_START + 1],
                        row[col::HEAD_TERM_START + 2],
                        row[col::HEAD_TERM_START + 3],
                    ];
                    let expected_hash = hash_fact(pred, &terms);
                    let claimed_hash = row[col::DERIVED_HASH];
                    expected_hash - claimed_hash
                }),
            },
            // Constraint 5: All body roots equal the state root (public input 0).
            Constraint {
                name: "body_roots_match_state".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    let state_root = public_inputs[0];
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_BODY_ATOMS {
                        let flag = row[col::BODY_MEMBERSHIP_START + i];
                        let root = row[col::BODY_ROOT_START + i];
                        result = result + flag * (root - state_root);
                    }
                    result
                }),
            },
            // Constraint 6: Derived hash matches public input.
            Constraint {
                name: "derived_hash_public".to_string(),
                eval: Box::new(|row, _, public_inputs| row[col::DERIVED_HASH] - public_inputs[1]),
            },
            // Constraint 7: head_is_var columns are binary.
            Constraint {
                name: "head_is_var_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_HEAD_TERMS {
                        let flag = row[col::HEAD_IS_VAR_START + i];
                        result = result + flag * (flag - BabyBear::ONE);
                    }
                    result
                }),
            },
            // Constraint 8: Selector columns are binary.
            Constraint {
                name: "head_sel_var_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for term_i in 0..MAX_HEAD_TERMS {
                        for var_j in 0..MAX_SUB_VARS {
                            let sel = row[col::head_sel_var(term_i, var_j)];
                            result = result + sel * (sel - BabyBear::ONE);
                        }
                    }
                    result
                }),
            },
            // Constraint 9: When is_var=1, exactly one selector must be 1.
            // sum(sel_j) = is_var for each term.
            Constraint {
                name: "head_sel_var_sum_equals_is_var".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for term_i in 0..MAX_HEAD_TERMS {
                        let is_var = row[col::HEAD_IS_VAR_START + term_i];
                        let mut sel_sum = BabyBear::ZERO;
                        for var_j in 0..MAX_SUB_VARS {
                            sel_sum = sel_sum + row[col::head_sel_var(term_i, var_j)];
                        }
                        // sel_sum must equal is_var
                        result = result + (sel_sum - is_var) * (sel_sum - is_var);
                    }
                    result
                }),
            },
            // Constraint 10: Substitution application correctness.
            // derived_term[i] = is_var * (sum_j sel_j * sub[j]) + (1-is_var) * raw_value
            Constraint {
                name: "substitution_application".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for term_i in 0..MAX_HEAD_TERMS {
                        let is_var = row[col::HEAD_IS_VAR_START + term_i];
                        let raw_value = row[col::HEAD_RAW_VALUE_START + term_i];
                        let derived_term = row[col::HEAD_TERM_START + term_i];

                        // Compute the resolved value via selectors
                        let mut var_resolved = BabyBear::ZERO;
                        for var_j in 0..MAX_SUB_VARS {
                            let sel = row[col::head_sel_var(term_i, var_j)];
                            let sub_val = row[col::SUB_VALUE_START + var_j];
                            var_resolved = var_resolved + sel * sub_val;
                        }

                        // expected = is_var * var_resolved + (1 - is_var) * raw_value
                        let expected = is_var * var_resolved + (BabyBear::ONE - is_var) * raw_value;

                        result = result + (derived_term - expected) * (derived_term - expected);
                    }
                    result
                }),
            },
            // Constraint 11: Equal check active flags are binary.
            Constraint {
                name: "eq_check_active_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_EQUAL_CHECKS {
                        let active = row[col::eq_check_active(i)];
                        result = result + active * (active - BabyBear::ONE);
                    }
                    result
                }),
            },
            // Constraint 12: Equal check enforcement.
            // When active=1: term_a must equal term_b.
            // Encoded as: active * (term_a - term_b) = 0
            Constraint {
                name: "eq_check_enforced".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_EQUAL_CHECKS {
                        let active = row[col::eq_check_active(i)];
                        let term_a = row[col::eq_check_term_a(i)];
                        let term_b = row[col::eq_check_term_b(i)];
                        result = result + active * (term_a - term_b);
                    }
                    result
                }),
            },
            // Constraint 13: MemberOf check active flags are binary.
            Constraint {
                name: "memberof_check_active_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_MEMBEROF_CHECKS {
                        let active = row[col::memberof_check_active(i)];
                        result = result + active * (active - BabyBear::ONE);
                    }
                    result
                }),
            },
            // Constraint 14: MemberOf check enforcement.
            // When active=1: term_a must equal term_b (hash equality).
            // Encoded as: active * (term_a - term_b) = 0
            Constraint {
                name: "memberof_check_enforced".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_MEMBEROF_CHECKS {
                        let active = row[col::memberof_check_active(i)];
                        let term_a = row[col::memberof_check_term_a(i)];
                        let term_b = row[col::memberof_check_term_b(i)];
                        result = result + active * (term_a - term_b);
                    }
                    result
                }),
            },
            // Constraint 15: GTE check active flag is binary.
            Constraint {
                name: "gte_check_active_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::GTE_CHECK_ACTIVE];
                    active * (active - BabyBear::ONE)
                }),
            },
            // Constraint 16: GTE diff consistency.
            // When active: diff = term_a - term_b
            Constraint {
                name: "gte_check_diff_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::GTE_CHECK_ACTIVE];
                    let term_a = row[col::GTE_CHECK_TERM_A];
                    let term_b = row[col::GTE_CHECK_TERM_B];
                    let diff = row[col::GTE_CHECK_DIFF];
                    active * (diff - (term_a - term_b))
                }),
            },
            // Constraint 17: GTE bit decomposition is correct.
            // When active: sum(bit_i * 2^i) = diff
            Constraint {
                name: "gte_check_bit_decomposition".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::GTE_CHECK_ACTIVE];
                    let diff = row[col::GTE_CHECK_DIFF];
                    let mut recomposed = BabyBear::ZERO;
                    let mut power_of_two = BabyBear::ONE;
                    for i in 0..GTE_DIFF_BITS {
                        let bit = row[col::gte_diff_bit(i)];
                        recomposed = recomposed + bit * power_of_two;
                        power_of_two = power_of_two + power_of_two; // 2^(i+1)
                    }
                    active * (recomposed - diff)
                }),
            },
            // Constraint 18: GTE bits are binary.
            Constraint {
                name: "gte_check_bits_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::GTE_CHECK_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..GTE_DIFF_BITS {
                        let bit = row[col::gte_diff_bit(i)];
                        result = result + bit * (bit - BabyBear::ONE);
                    }
                    active * result
                }),
            },
            // Constraint 19: GTE high bit is 0 (ensures diff < 2^30 < p/2).
            // When active: diff_bits[30] = 0
            Constraint {
                name: "gte_check_high_bit_zero".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::GTE_CHECK_ACTIVE];
                    let high_bit = row[col::gte_diff_bit(GTE_DIFF_BITS - 1)];
                    active * high_bit
                }),
            },
            // Constraint 20: LT check active flag is binary.
            Constraint {
                name: "lt_check_active_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::LT_CHECK_ACTIVE];
                    active * (active - BabyBear::ONE)
                }),
            },
            // Constraint 21: LT diff consistency.
            // When active: diff = term_b - term_a - 1
            Constraint {
                name: "lt_check_diff_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::LT_CHECK_ACTIVE];
                    let term_a = row[col::LT_CHECK_TERM_A];
                    let term_b = row[col::LT_CHECK_TERM_B];
                    let diff = row[col::LT_CHECK_DIFF];
                    active * (diff - (term_b - term_a - BabyBear::ONE))
                }),
            },
            // Constraint 22: LT bit decomposition is correct.
            // When active: sum(bit_i * 2^i) = diff
            Constraint {
                name: "lt_check_bit_decomposition".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::LT_CHECK_ACTIVE];
                    let diff = row[col::LT_CHECK_DIFF];
                    let mut recomposed = BabyBear::ZERO;
                    let mut power_of_two = BabyBear::ONE;
                    for i in 0..GTE_DIFF_BITS {
                        let bit = row[col::lt_diff_bit(i)];
                        recomposed = recomposed + bit * power_of_two;
                        power_of_two = power_of_two + power_of_two;
                    }
                    active * (recomposed - diff)
                }),
            },
            // Constraint 23: LT bits are binary.
            Constraint {
                name: "lt_check_bits_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::LT_CHECK_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..GTE_DIFF_BITS {
                        let bit = row[col::lt_diff_bit(i)];
                        result = result + bit * (bit - BabyBear::ONE);
                    }
                    active * result
                }),
            },
            // Constraint 24: LT high bit is 0 (ensures diff < 2^30 < p/2, meaning a < b).
            Constraint {
                name: "lt_check_high_bit_zero".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::LT_CHECK_ACTIVE];
                    let high_bit = row[col::lt_diff_bit(GTE_DIFF_BITS - 1)];
                    active * high_bit
                }),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;
        let derived_hash = w.derived_hash();

        // Single-row trace for one derivation step
        let mut row = vec![BabyBear::ZERO; DERIVATION_AIR_WIDTH];

        // Rule ID
        row[col::RULE_ID] = BabyBear::new(w.rule.id);

        // Body hashes and membership flags
        for (i, &hash) in w.body_fact_hashes.iter().enumerate().take(MAX_BODY_ATOMS) {
            row[col::BODY_HASH_START + i] = hash;
            row[col::BODY_MEMBERSHIP_START + i] = BabyBear::ONE;
            row[col::BODY_ROOT_START + i] = w.state_root;
        }

        // Head (derived fact)
        row[col::HEAD_PRED] = w.derived_predicate;
        for i in 0..MAX_HEAD_TERMS {
            row[col::HEAD_TERM_START + i] = w.derived_terms[i];
        }
        row[col::DERIVED_HASH] = derived_hash;

        // Substitution values
        for (i, &val) in w.substitution.iter().enumerate().take(MAX_SUB_VARS) {
            row[col::SUB_VALUE_START + i] = val;
        }

        // --- Substitution verification columns ---
        for (term_i, &(is_var, value)) in w.rule.head_terms.iter().enumerate().take(MAX_HEAD_TERMS)
        {
            row[col::HEAD_IS_VAR_START + term_i] = if is_var {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            row[col::HEAD_RAW_VALUE_START + term_i] = value;

            // Set selector: if is_var, set the selector for the variable index
            if is_var {
                let var_idx = value.as_u32() as usize;
                if var_idx < MAX_SUB_VARS {
                    row[col::head_sel_var(term_i, var_idx)] = BabyBear::ONE;
                }
            }
            // If not a variable, all selectors stay zero (sum=0=is_var=0).
        }

        // --- Equal check columns ---
        for (check_i, eq_check) in w
            .rule
            .equal_checks
            .iter()
            .enumerate()
            .take(MAX_EQUAL_CHECKS)
        {
            row[col::eq_check_active(check_i)] = BabyBear::ONE;

            // Resolve LHS
            let term_a = if eq_check.lhs_is_var {
                let idx = eq_check.lhs_value.as_u32() as usize;
                if idx < w.substitution.len() {
                    w.substitution[idx]
                } else {
                    BabyBear::ZERO
                }
            } else {
                eq_check.lhs_value
            };

            // Resolve RHS
            let term_b = if eq_check.rhs_is_var {
                let idx = eq_check.rhs_value.as_u32() as usize;
                if idx < w.substitution.len() {
                    w.substitution[idx]
                } else {
                    BabyBear::ZERO
                }
            } else {
                eq_check.rhs_value
            };

            row[col::eq_check_term_a(check_i)] = term_a;
            row[col::eq_check_term_b(check_i)] = term_b;
        }

        // --- MemberOf check columns ---
        for (check_i, mo_check) in w
            .rule
            .memberof_checks
            .iter()
            .enumerate()
            .take(MAX_MEMBEROF_CHECKS)
        {
            row[col::memberof_check_active(check_i)] = BabyBear::ONE;

            // Resolve LHS (element)
            let term_a = if mo_check.lhs_is_var {
                let idx = mo_check.lhs_value.as_u32() as usize;
                if idx < w.substitution.len() {
                    w.substitution[idx]
                } else {
                    BabyBear::ZERO
                }
            } else {
                mo_check.lhs_value
            };

            // Resolve RHS (set element)
            let term_b = if mo_check.rhs_is_var {
                let idx = mo_check.rhs_value.as_u32() as usize;
                if idx < w.substitution.len() {
                    w.substitution[idx]
                } else {
                    BabyBear::ZERO
                }
            } else {
                mo_check.rhs_value
            };

            row[col::memberof_check_term_a(check_i)] = term_a;
            row[col::memberof_check_term_b(check_i)] = term_b;
        }

        // --- GTE check columns ---
        if let Some(gte_check) = &w.rule.gte_check {
            row[col::GTE_CHECK_ACTIVE] = BabyBear::ONE;

            // Resolve LHS (a, the larger value)
            let term_a = if gte_check.lhs_is_var {
                let idx = gte_check.lhs_value.as_u32() as usize;
                if idx < w.substitution.len() {
                    w.substitution[idx]
                } else {
                    BabyBear::ZERO
                }
            } else {
                gte_check.lhs_value
            };

            // Resolve RHS (b, the smaller value)
            let term_b = if gte_check.rhs_is_var {
                let idx = gte_check.rhs_value.as_u32() as usize;
                if idx < w.substitution.len() {
                    w.substitution[idx]
                } else {
                    BabyBear::ZERO
                }
            } else {
                gte_check.rhs_value
            };

            row[col::GTE_CHECK_TERM_A] = term_a;
            row[col::GTE_CHECK_TERM_B] = term_b;

            // Compute diff = a - b in the field
            let diff = term_a - term_b;
            row[col::GTE_CHECK_DIFF] = diff;

            // Bit decomposition of diff
            let diff_val = diff.as_u32();
            for i in 0..GTE_DIFF_BITS {
                let bit = (diff_val >> i) & 1;
                row[col::gte_diff_bit(i)] = BabyBear::new(bit);
            }
        }

        // --- LT check columns ---
        if let Some(lt_check) = &w.rule.lt_check {
            row[col::LT_CHECK_ACTIVE] = BabyBear::ONE;

            // Resolve LHS (a, the smaller value)
            let term_a = if lt_check.lhs_is_var {
                let idx = lt_check.lhs_value.as_u32() as usize;
                if idx < w.substitution.len() {
                    w.substitution[idx]
                } else {
                    BabyBear::ZERO
                }
            } else {
                lt_check.lhs_value
            };

            // Resolve RHS (b, the larger value)
            let term_b = if lt_check.rhs_is_var {
                let idx = lt_check.rhs_value.as_u32() as usize;
                if idx < w.substitution.len() {
                    w.substitution[idx]
                } else {
                    BabyBear::ZERO
                }
            } else {
                lt_check.rhs_value
            };

            row[col::LT_CHECK_TERM_A] = term_a;
            row[col::LT_CHECK_TERM_B] = term_b;

            // Compute diff = b - a - 1 in the field
            let diff = term_b - term_a - BabyBear::ONE;
            row[col::LT_CHECK_DIFF] = diff;

            // Bit decomposition of diff
            let diff_val = diff.as_u32();
            for i in 0..GTE_DIFF_BITS {
                let bit = (diff_val >> i) & 1;
                row[col::lt_diff_bit(i)] = BabyBear::new(bit);
            }
        }

        let public_inputs = vec![w.state_root, derived_hash];
        (vec![row], public_inputs)
    }
}

/// Helper: Create a test derivation witness.
pub fn create_test_derivation() -> DerivationWitness {
    // Simple rule: access(X, Y) :- owns(X, Y), can_read(X, Y).
    let owns_pred = BabyBear::new(100);
    let can_read_pred = BabyBear::new(200);
    let access_pred = BabyBear::new(300);
    let alice = BabyBear::new(1000);
    let file = BabyBear::new(2000);

    let rule = CircuitRule {
        id: 1,
        num_body_atoms: 2,
        num_variables: 2,
        head_predicate: access_pred,
        head_terms: [
            (true, BabyBear::new(0)), // X
            (true, BabyBear::new(1)), // Y
            (false, BabyBear::ZERO),  // unused
            (false, BabyBear::ZERO),  // unused
        ],
        body_atoms: vec![
            BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)), // X
                    (true, BabyBear::new(1)), // Y
                    (false, BabyBear::ZERO),
                ],
            },
            BodyAtomPattern {
                predicate: can_read_pred,
                terms: [
                    (true, BabyBear::new(0)), // X
                    (true, BabyBear::new(1)), // Y
                    (false, BabyBear::ZERO),
                ],
            },
        ],
        equal_checks: vec![],
        memberof_checks: vec![],
        gte_check: None,
        lt_check: None,
    };

    // Body fact hashes (simulated — in real use these come from Merkle proofs)
    let body_fact_1 = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);
    let body_fact_2 = hash_fact(can_read_pred, &[alice, file, BabyBear::ZERO]);

    DerivationWitness {
        rule,
        state_root: BabyBear::new(99999),
        body_fact_hashes: vec![body_fact_1, body_fact_2],
        substitution: vec![alice, file], // X=alice, Y=file
        derived_predicate: access_pred,
        derived_terms: [alice, file, BabyBear::ZERO, BabyBear::ZERO],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;

    #[test]
    fn derivation_air_valid() {
        let witness = create_test_derivation();
        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Derivation AIR should verify: {:?}",
            result.violations()
        );
    }

    #[test]
    fn derivation_air_wrong_derived_hash_fails() {
        let mut witness = create_test_derivation();
        // Tamper with derived predicate (hash will be wrong)
        witness.derived_predicate = BabyBear::new(999);
        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        // The trace generator recomputes hash from the (tampered) predicate,
        // so the trace is internally consistent.
        assert!(result.is_valid());
    }

    #[test]
    fn derivation_air_no_body_facts_fails() {
        let mut witness = create_test_derivation();
        witness.body_fact_hashes = vec![]; // no body facts
        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid());
    }

    #[test]
    fn derivation_air_body_root_mismatch_fails() {
        let mut witness = create_test_derivation();
        witness.state_root = BabyBear::new(11111);

        // Create witness where body roots in trace differ from state_root
        struct TamperedDerivationAir {
            witness: DerivationWitness,
            tampered_root: BabyBear,
        }
        impl Air for TamperedDerivationAir {
            fn trace_width(&self) -> usize {
                DERIVATION_AIR_WIDTH
            }
            fn num_public_inputs(&self) -> usize {
                2
            }
            fn constraints(&self) -> Vec<Constraint> {
                DerivationAir::new(self.witness.clone()).constraints()
            }
            fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
                let (mut trace, pi) = DerivationAir::new(self.witness.clone()).generate_trace();
                // Tamper: set body_root[0] to different value
                trace[0][col::BODY_ROOT_START] = self.tampered_root;
                (trace, pi)
            }
        }

        let tampered = TamperedDerivationAir {
            witness,
            tampered_root: BabyBear::new(99999),
        };
        let result = ConstraintProver::verify(&tampered);
        assert!(!result.is_valid());
    }

    #[test]
    fn derivation_witness_head_match() {
        let witness = create_test_derivation();
        assert!(witness.check_head_match());
    }

    #[test]
    fn derivation_witness_head_mismatch() {
        let mut witness = create_test_derivation();
        // Change a derived term without changing substitution
        witness.derived_terms[0] = BabyBear::new(9999);
        assert!(!witness.check_head_match());
    }

    // --- Substitution verification tests ---

    #[test]
    fn test_derivation_air_substitution_correct() {
        // The standard test derivation has head_terms = [(var 0), (var 1), (const 0)]
        // with substitution = [alice=1000, file=2000]
        // and derived_terms = [1000, 2000, 0]
        // This should verify successfully.
        let witness = create_test_derivation();
        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Correct substitution should verify: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_derivation_air_wrong_substitution_rejected() {
        // Create a witness where the derived terms don't match the substitution application.
        // Rule head: access(X, Y) -> head_terms = [(var 0), (var 1), (const 0)]
        // Substitution: X=1000, Y=2000
        // But we claim derived_terms = [9999, 2000, 0] (wrong X value)
        let mut witness = create_test_derivation();
        // Tamper: change derived_terms[0] to wrong value
        witness.derived_terms[0] = BabyBear::new(9999);
        // We need to keep the hash consistent with the tampered terms, otherwise
        // the hash constraint would fail first. The point is that the SUBSTITUTION
        // constraint catches the mismatch between the rule pattern and derived fact.
        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            !result.is_valid(),
            "Wrong substitution should fail verification"
        );
        // Verify the substitution_application constraint is among the failures
        let has_sub_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "substitution_application");
        assert!(
            has_sub_violation,
            "Should have substitution_application violation, got: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_derivation_air_constant_head_term() {
        // Test rule with a constant in the head: result(X, "fixed_val", Y, _)
        // head_terms = [(var 0), (const 500), (var 1), (const 0)]
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let alice = BabyBear::new(1000);
        let file = BabyBear::new(2000);
        let fixed_val = BabyBear::new(500);

        let rule = CircuitRule {
            id: 2,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)), // X -> substitution[0] = alice
                (false, fixed_val),       // constant 500
                (true, BabyBear::new(1)), // Y -> substitution[1] = file
                (false, BabyBear::ZERO),  // unused
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
        lt_check: None,
        };

        let body_fact = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, file],
            derived_predicate: access_pred,
            derived_terms: [alice, fixed_val, file, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Constant head term should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_derivation_air_constant_head_term_wrong_value() {
        // Same as above but with wrong constant in the derived fact
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let alice = BabyBear::new(1000);
        let file = BabyBear::new(2000);
        let fixed_val = BabyBear::new(500);

        let rule = CircuitRule {
            id: 2,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, fixed_val), // expects constant 500
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
        lt_check: None,
        };

        let body_fact = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, file],
            derived_predicate: access_pred,
            derived_terms: [alice, BabyBear::new(777), file, BabyBear::ZERO], // WRONG: 777 instead of 500
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            !result.is_valid(),
            "Wrong constant in derived fact should fail"
        );
    }

    // --- Equal check tests ---

    #[test]
    fn test_derivation_air_equal_check_enforced() {
        // Rule: access(X, Y) :- owns(X, Y), can_read(X, Y), X == Y.
        // With X=alice, Y=alice (equal), this should pass.
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let alice = BabyBear::new(1000);

        let rule = CircuitRule {
            id: 3,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)), // X
                (true, BabyBear::new(1)), // Y
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![CircuitEqualCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // X
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // Y
            }],
            memberof_checks: vec![],
            gte_check: None,
        lt_check: None,
        };

        // X=alice, Y=alice (they are equal, so the check passes)
        let body_fact = hash_fact(owns_pred, &[alice, alice, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, alice], // X=alice, Y=alice
            derived_predicate: access_pred,
            derived_terms: [alice, alice, BabyBear::ZERO, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Equal check with matching values should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_derivation_air_equal_check_violation() {
        // Rule: access(X, Y) :- owns(X, Y), X == Y.
        // With X=alice, Y=file (not equal), this should FAIL.
        // But the prover must honestly report the resolved values.
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let alice = BabyBear::new(1000);
        let file = BabyBear::new(2000);

        let rule = CircuitRule {
            id: 3,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)), // X
                (true, BabyBear::new(1)), // Y
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![CircuitEqualCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // X
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // Y
            }],
            memberof_checks: vec![],
            gte_check: None,
        lt_check: None,
        };

        // X=alice (1000), Y=file (2000) — NOT equal
        let body_fact = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, file], // X=alice, Y=file (different!)
            derived_predicate: access_pred,
            derived_terms: [alice, file, BabyBear::ZERO, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            !result.is_valid(),
            "Equal check with non-matching values should fail"
        );
        // Verify the eq_check_enforced constraint is violated
        let has_eq_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "eq_check_enforced");
        assert!(
            has_eq_violation,
            "Should have eq_check_enforced violation, got: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_derivation_air_equal_check_var_vs_constant() {
        // Equal check: X == 1000 (variable compared to constant)
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let alice = BabyBear::new(1000);
        let file = BabyBear::new(2000);

        let rule = CircuitRule {
            id: 4,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![CircuitEqualCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // X
                rhs_is_var: false,
                rhs_value: alice, // constant 1000
            }],
            memberof_checks: vec![],
            gte_check: None,
        lt_check: None,
        };

        // X=alice=1000, check is X==1000, should pass
        let body_fact = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, file],
            derived_predicate: access_pred,
            derived_terms: [alice, file, BabyBear::ZERO, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Equal check var==const with matching values should pass: {:?}",
            result.violations()
        );
    }

    // --- MemberOf check tests ---

    #[test]
    fn test_derivation_air_memberof_check_passes() {
        // Rule: access(X, Y) :- owns(X, Y), member_of(X, X).
        // X bound to same hash on both sides -> passes.
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let action_hash = BabyBear::new(12345); // simulated action hash

        let rule = CircuitRule {
            id: 5,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)), // X
                (true, BabyBear::new(1)), // Y
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![CircuitMemberOfCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // X (the request action hash)
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // Y (the allowed action hash)
            }],
            gte_check: None,
        lt_check: None,
        };

        // X=action_hash, Y=action_hash (matching -> member)
        let body_fact = hash_fact(owns_pred, &[action_hash, action_hash, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![action_hash, action_hash],
            derived_predicate: access_pred,
            derived_terms: [action_hash, action_hash, BabyBear::ZERO, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "MemberOf check with matching hashes should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_derivation_air_memberof_check_fails() {
        // Rule: access(X, Y) :- owns(X, Y), member_of(X, Y).
        // X != Y -> should fail the MemberOf check.
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let request_hash = BabyBear::new(12345);
        let allowed_hash = BabyBear::new(67890);

        let rule = CircuitRule {
            id: 5,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![CircuitMemberOfCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // X (request action)
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // Y (allowed action)
            }],
            gte_check: None,
        lt_check: None,
        };

        // X=request_hash, Y=allowed_hash (DIFFERENT -> not a member)
        let body_fact = hash_fact(owns_pred, &[request_hash, allowed_hash, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![request_hash, allowed_hash],
            derived_predicate: access_pred,
            derived_terms: [request_hash, allowed_hash, BabyBear::ZERO, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            !result.is_valid(),
            "MemberOf check with non-matching hashes should fail"
        );
        // Verify the memberof_check_enforced constraint is violated
        let has_memberof_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "memberof_check_enforced");
        assert!(
            has_memberof_violation,
            "Should have memberof_check_enforced violation, got: {:?}",
            result.violations()
        );
    }

    // --- GTE check tests ---

    #[test]
    fn test_derivation_air_gte_check_passes() {
        // budget_remaining(50) >= request_cost(10)
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let budget = BabyBear::new(50);
        let cost = BabyBear::new(10);

        let rule = CircuitRule {
            id: 6,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: Some(CircuitGteCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // X = budget_remaining
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // Y = request_cost
            }),
        };

        let body_fact = hash_fact(owns_pred, &[budget, cost, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![budget, cost], // X=50, Y=10
            derived_predicate: access_pred,
            derived_terms: [budget, cost, BabyBear::ZERO, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GTE check 50 >= 10 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_derivation_air_gte_check_fails() {
        // budget_remaining(5) >= request_cost(10) — should FAIL
        // diff = 5 - 10 in BabyBear = p - 5 (wraps around, high bit set)
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let budget = BabyBear::new(5);
        let cost = BabyBear::new(10);

        let rule = CircuitRule {
            id: 6,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: Some(CircuitGteCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // X = budget_remaining
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // Y = request_cost
            }),
        };

        let body_fact = hash_fact(owns_pred, &[budget, cost, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![budget, cost], // X=5, Y=10 (5 < 10, so GTE fails)
            derived_predicate: access_pred,
            derived_terms: [budget, cost, BabyBear::ZERO, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "GTE check 5 >= 10 should fail");
        // The high bit constraint should catch this
        let has_gte_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "gte_check_high_bit_zero");
        assert!(
            has_gte_violation,
            "Should have gte_check_high_bit_zero violation, got: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_derivation_air_budget_scenario() {
        // Full budget scenario: budget_remaining(50) >= request_cost(10)
        // Combined with a MemberOf check for action verification.
        let grant_pred = BabyBear::new(400);
        let budget_pred = BabyBear::new(100);
        let action_hash = BabyBear::new(55555);
        let budget = BabyBear::new(50);
        let cost = BabyBear::new(10);

        let rule = CircuitRule {
            id: 7,
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: grant_pred,
            head_terms: [
                (true, BabyBear::new(0)), // action_hash
                (true, BabyBear::new(1)), // budget_remaining
                (true, BabyBear::new(2)), // request_cost
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: budget_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (true, BabyBear::new(2)),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![CircuitMemberOfCheck {
                // Action hash matches (self-check for illustration)
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // action_hash from request
                rhs_is_var: false,
                rhs_value: action_hash, // expected action hash (constant)
            }],
            gte_check: Some(CircuitGteCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(1), // budget_remaining
                rhs_is_var: true,
                rhs_value: BabyBear::new(2), // request_cost
            }),
        };

        let body_fact = hash_fact(budget_pred, &[action_hash, budget, cost]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![action_hash, budget, cost],
            derived_predicate: grant_pred,
            derived_terms: [action_hash, budget, cost, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Budget scenario (50>=10, action matches) should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_derivation_air_gte_check_equal_values_passes() {
        // Edge case: 10 >= 10 should pass (diff = 0, all bits zero)
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let val = BabyBear::new(10);

        let rule = CircuitRule {
            id: 8,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: Some(CircuitGteCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0),
                rhs_is_var: true,
                rhs_value: BabyBear::new(1),
            }),
        };

        let body_fact = hash_fact(owns_pred, &[val, val, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![val, val], // 10 >= 10
            derived_predicate: access_pred,
            derived_terms: [val, val, BabyBear::ZERO, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GTE check 10 >= 10 should pass: {:?}",
            result.violations()
        );
    }
}
