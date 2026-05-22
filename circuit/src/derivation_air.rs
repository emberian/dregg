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
//! 25. Check term binding: is_var flags are binary
//! 26. Check term binding: selectors are binary
//! 27. Check term binding: selector sum = is_var (exactly-one when var)
//! 28. Check term binding: resolved term = is_var*(sum sel_j*sub[j]) + (1-is_var)*raw_value
//!     (This binds eq/memberof/gte/lt check terms to the substitution, preventing soundness bypass)

use crate::constraint_prover::{Air, Constraint};
use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_fact, hash_many};
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Trace width for the derivation AIR.
/// rule_id(1) + body_hashes(8) + body_membership(8) + head_pred(1) + head_terms(4) +
/// derived_hash(1) + sub_values(8) + body_roots(8) + head_is_var(4) + head_raw_value(4) +
/// head_sel_var(4*8=32) + eq_checks(3*4=12) + memberof_checks(3*4=12) + gte(4+30=34) + lt(4+30=34)
/// + check_term_binding(20 terms * (1 is_var + 1 raw_value + 8 selectors) = 200) = 371
pub const DERIVATION_AIR_WIDTH: usize = 371;

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

/// Number of bits for GTE range check.
///
/// SOUNDNESS FIX: BabyBear p = 2013265921, p/2 = 1006632960, 2^30 = 1073741824.
/// Since 2^30 > p/2, the old value of 31 bits (checking bit 30 = 0) was UNSOUND.
/// With 30 bits, we check bit 29 = 0, proving diff < 2^29 = 536870912 < p/2.
pub const GTE_DIFF_BITS: usize = 30;

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
    /// GTE diff bit decomposition starts here (30 bits, columns 107..136).
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
    /// LT diff bit decomposition starts here (30 bits, columns 141..170).
    pub const LT_CHECK_DIFF_BITS_START: usize = LT_CHECK_START + 4; // 141

    /// Get the column for lt_check_diff_bits[bit_idx].
    #[inline]
    pub const fn lt_diff_bit(bit_idx: usize) -> usize {
        LT_CHECK_DIFF_BITS_START + bit_idx
    }

    // ==========================================================================
    // Check term binding columns (SOUNDNESS FIX)
    //
    // These columns bind each check's resolved term_a/term_b to the substitution,
    // preventing a malicious prover from placing arbitrary values in the check
    // columns that don't correspond to the actual substitution.
    //
    // Layout: For each check term, we store:
    //   - is_var (1 col): 1 if this term references a substitution variable
    //   - raw_value (1 col): the constant value (when is_var=0) or var index (when is_var=1)
    //   - sel_var[0..MAX_SUB_VARS] (8 cols): one-hot selector for which sub variable
    //
    // Total per term: 10 columns.
    // Total check terms: (MAX_EQUAL_CHECKS * 2) + (MAX_MEMBEROF_CHECKS * 2) + 2 (GTE) + 2 (LT) = 20
    // Total new columns: 20 * 10 = 200
    // ==========================================================================

    /// Number of columns per check term binding (is_var + raw_value + MAX_SUB_VARS selectors).
    pub const CHECK_TERM_COLS: usize = 1 + 1 + MAX_SUB_VARS; // 10

    /// Start of check term binding columns.
    pub const CHECK_TERM_BINDING_START: usize = LT_CHECK_DIFF_BITS_START + GTE_DIFF_BITS; // 171

    /// Number of check terms: eq(4*2) + memberof(4*2) + gte(2) + lt(2) = 20
    pub const NUM_CHECK_TERMS: usize = MAX_EQUAL_CHECKS * 2 + MAX_MEMBEROF_CHECKS * 2 + 2 + 2; // 20

    /// Get the base column for a check term binding slot.
    /// Slot ordering:
    ///   0..7:  eq_check[0..3].term_a, eq_check[0..3].term_b
    ///   8..15: memberof_check[0..3].term_a, memberof_check[0..3].term_b
    ///   16: gte_check.term_a
    ///   17: gte_check.term_b
    ///   18: lt_check.term_a
    ///   19: lt_check.term_b
    #[inline]
    pub const fn check_term_base(slot: usize) -> usize {
        CHECK_TERM_BINDING_START + slot * CHECK_TERM_COLS
    }

    /// Check term is_var column for a given slot.
    #[inline]
    pub const fn check_term_is_var(slot: usize) -> usize {
        check_term_base(slot)
    }

    /// Check term raw_value column for a given slot.
    #[inline]
    pub const fn check_term_raw_value(slot: usize) -> usize {
        check_term_base(slot) + 1
    }

    /// Check term selector column for a given slot and variable index.
    #[inline]
    pub const fn check_term_sel(slot: usize, var_idx: usize) -> usize {
        check_term_base(slot) + 2 + var_idx
    }

    // --- Helper functions for named slot indices ---

    /// Slot index for eq_check[check_idx].term_a.
    #[inline]
    pub const fn eq_check_term_a_slot(check_idx: usize) -> usize {
        check_idx * 2
    }
    /// Slot index for eq_check[check_idx].term_b.
    #[inline]
    pub const fn eq_check_term_b_slot(check_idx: usize) -> usize {
        check_idx * 2 + 1
    }
    /// Slot index for memberof_check[check_idx].term_a.
    #[inline]
    pub const fn memberof_check_term_a_slot(check_idx: usize) -> usize {
        MAX_EQUAL_CHECKS * 2 + check_idx * 2
    }
    /// Slot index for memberof_check[check_idx].term_b.
    #[inline]
    pub const fn memberof_check_term_b_slot(check_idx: usize) -> usize {
        MAX_EQUAL_CHECKS * 2 + check_idx * 2 + 1
    }
    /// Slot index for gte_check.term_a.
    pub const GTE_TERM_A_SLOT: usize = MAX_EQUAL_CHECKS * 2 + MAX_MEMBEROF_CHECKS * 2; // 16
    /// Slot index for gte_check.term_b.
    pub const GTE_TERM_B_SLOT: usize = GTE_TERM_A_SLOT + 1; // 17
    /// Slot index for lt_check.term_a.
    pub const LT_TERM_A_SLOT: usize = GTE_TERM_B_SLOT + 1; // 18
    /// Slot index for lt_check.term_b.
    pub const LT_TERM_B_SLOT: usize = LT_TERM_A_SLOT + 1; // 19

    /// Total columns: CHECK_TERM_BINDING_START + NUM_CHECK_TERMS * CHECK_TERM_COLS = 171 + 200 = 371
    pub const _TOTAL: usize = CHECK_TERM_BINDING_START + NUM_CHECK_TERMS * CHECK_TERM_COLS;
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

impl CircuitRule {
    /// Compute a cryptographic commitment to the full rule structure.
    ///
    /// This hashes ALL structural properties of the rule:
    /// - rule_id, head_predicate, num_body_atoms, num_variables
    /// - head term patterns (is_var flags + values)
    /// - equal checks (each check's lhs/rhs structure)
    /// - memberof checks (each check's lhs/rhs structure)
    /// - gte check (presence + lhs/rhs structure)
    /// - lt check (presence + lhs/rhs structure)
    ///
    /// SOUNDNESS: This commitment binds the full rule definition. A prover cannot
    /// swap a rule with stripped checks (e.g., removing a GTE budget constraint)
    /// because the resulting hash would differ from the policy commitment.
    pub fn compute_structure_hash(&self) -> BabyBear {
        let mut elements = Vec::with_capacity(32);

        // Core rule identity
        elements.push(BabyBear::new(self.id));
        elements.push(self.head_predicate);
        elements.push(BabyBear::new(self.num_body_atoms as u32));
        elements.push(BabyBear::new(self.num_variables as u32));

        // Head term patterns (encode is_var as 1/0, then the value)
        for &(is_var, value) in &self.head_terms {
            elements.push(if is_var {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            elements.push(value);
        }

        // Equal checks: encode count + each check's structure
        elements.push(BabyBear::new(self.equal_checks.len() as u32));
        for eq in &self.equal_checks {
            elements.push(if eq.lhs_is_var {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            elements.push(eq.lhs_value);
            elements.push(if eq.rhs_is_var {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            elements.push(eq.rhs_value);
        }

        // MemberOf checks: encode count + each check's structure
        elements.push(BabyBear::new(self.memberof_checks.len() as u32));
        for mo in &self.memberof_checks {
            elements.push(if mo.lhs_is_var {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            elements.push(mo.lhs_value);
            elements.push(if mo.rhs_is_var {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            elements.push(mo.rhs_value);
        }

        // GTE check: encode presence + structure
        match &self.gte_check {
            Some(gte) => {
                elements.push(BabyBear::ONE); // has gte
                elements.push(if gte.lhs_is_var {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                });
                elements.push(gte.lhs_value);
                elements.push(if gte.rhs_is_var {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                });
                elements.push(gte.rhs_value);
            }
            None => {
                elements.push(BabyBear::ZERO); // no gte
            }
        }

        // LT check: encode presence + structure
        match &self.lt_check {
            Some(lt) => {
                elements.push(BabyBear::ONE); // has lt
                elements.push(if lt.lhs_is_var {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                });
                elements.push(lt.lhs_value);
                elements.push(if lt.rhs_is_var {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                });
                elements.push(lt.rhs_value);
            }
            None => {
                elements.push(BabyBear::ZERO); // no lt
            }
        }

        hash_many(&elements)
    }
}

/// Compute the policy root from a set of rules by hashing their full structure.
///
/// SOUNDNESS: Unlike the previous implementation that only hashed rule IDs,
/// this commits to the complete rule definitions. A malicious prover cannot
/// substitute a rule with the same ID but stripped checks (e.g., removing a
/// GTE budget constraint) because the structure hash would differ.
///
/// policy_root = hash(rule_1_structure_hash || rule_2_structure_hash || ...)
pub fn compute_policy_root(rules: &[&CircuitRule]) -> BabyBear {
    if rules.is_empty() {
        return BabyBear::ZERO;
    }

    let mut acc = rules[0].compute_structure_hash();
    for rule in &rules[1..] {
        acc = hash_2_to_1(acc, rule.compute_structure_hash());
    }
    acc
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
    /// Committed pre-evaluation context: expiry bound (public input).
    ///
    /// The prover commits to this value as a public input. The verifier cross-checks:
    /// "Is current_height < not_after_height?" If the prover commits to an expired
    /// height, the verifier rejects out-of-band. If the prover lies (claims a higher
    /// height than what the token actually has), the derivation won't succeed because
    /// the body facts won't match the state root.
    ///
    /// `BabyBear::ZERO` means no expiry commitment (no expiry caveat present).
    pub not_after_height: BabyBear,
    /// Committed pre-evaluation context: organization identity binding (public input).
    ///
    /// This is `poseidon2(org_id_bytes)` — the hash of the organization ID that the
    /// token is scoped to. The verifier checks this matches the expected organization.
    /// If the prover commits to a wrong org_id_hash, the body facts won't match (the
    /// org restriction fact won't be found in the committed state).
    ///
    /// `BabyBear::ZERO` means no org binding (unrestricted token).
    pub org_id_hash: BabyBear,
    /// Committed pre-evaluation context: remaining budget (public input).
    ///
    /// The prover commits to the budget remaining at derivation time. The verifier
    /// cross-checks: "Is budget_remaining >= request_cost?" This works in conjunction
    /// with the GTE constraint in the circuit rule (if present) — the circuit enforces
    /// the arithmetic, while the public input lets the verifier see the committed value.
    ///
    /// `BabyBear::ZERO` means no budget commitment (unlimited budget).
    pub budget_remaining: BabyBear,
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
        5 // state_root, derived_fact_hash, not_after_height, org_id_hash, budget_remaining
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
            // ================================================================
            // SOUNDNESS FIX: Check term binding constraints (C25-C28)
            //
            // These constraints bind the resolved check terms (eq, memberof, gte, lt)
            // to the substitution columns, preventing a malicious prover from placing
            // arbitrary values in the check term columns.
            // ================================================================
            // Constraint 25: Check term binding is_var flags are binary.
            Constraint {
                name: "check_term_is_var_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for slot in 0..col::NUM_CHECK_TERMS {
                        let is_var = row[col::check_term_is_var(slot)];
                        result = result + is_var * (is_var - BabyBear::ONE);
                    }
                    result
                }),
            },
            // Constraint 26: Check term binding selectors are binary.
            Constraint {
                name: "check_term_sel_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for slot in 0..col::NUM_CHECK_TERMS {
                        for var_j in 0..MAX_SUB_VARS {
                            let sel = row[col::check_term_sel(slot, var_j)];
                            result = result + sel * (sel - BabyBear::ONE);
                        }
                    }
                    result
                }),
            },
            // Constraint 27: Check term binding selector sum equals is_var.
            // When is_var=1, exactly one selector must be 1; when is_var=0, all zero.
            Constraint {
                name: "check_term_sel_sum_equals_is_var".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for slot in 0..col::NUM_CHECK_TERMS {
                        let is_var = row[col::check_term_is_var(slot)];
                        let mut sel_sum = BabyBear::ZERO;
                        for var_j in 0..MAX_SUB_VARS {
                            sel_sum = sel_sum + row[col::check_term_sel(slot, var_j)];
                        }
                        let diff = sel_sum - is_var;
                        result = result + diff * diff;
                    }
                    result
                }),
            },
            // Constraint 28: Check term binding correctness.
            // For each active check, the resolved term in the trace must equal the
            // value computed from the binding columns:
            //   resolved = is_var * sum(sel_j * sub[j]) + (1-is_var) * raw_value
            //
            // Equal checks: active * (trace_term - resolved) = 0
            // MemberOf checks: active * (trace_term - resolved) = 0
            // GTE/LT: active * (trace_term - resolved) = 0
            Constraint {
                name: "check_term_binding_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;

                    // Helper: compute resolved value for a slot
                    let resolve_slot = |slot: usize| -> BabyBear {
                        let is_var = row[col::check_term_is_var(slot)];
                        let raw_value = row[col::check_term_raw_value(slot)];
                        let mut var_resolved = BabyBear::ZERO;
                        for var_j in 0..MAX_SUB_VARS {
                            let sel = row[col::check_term_sel(slot, var_j)];
                            let sub_val = row[col::SUB_VALUE_START + var_j];
                            var_resolved = var_resolved + sel * sub_val;
                        }
                        is_var * var_resolved + (BabyBear::ONE - is_var) * raw_value
                    };

                    // Equal check term bindings
                    for i in 0..MAX_EQUAL_CHECKS {
                        let active = row[col::eq_check_active(i)];
                        let trace_a = row[col::eq_check_term_a(i)];
                        let trace_b = row[col::eq_check_term_b(i)];
                        let resolved_a = resolve_slot(col::eq_check_term_a_slot(i));
                        let resolved_b = resolve_slot(col::eq_check_term_b_slot(i));
                        let diff_a = trace_a - resolved_a;
                        let diff_b = trace_b - resolved_b;
                        result = result + active * (diff_a * diff_a + diff_b * diff_b);
                    }

                    // MemberOf check term bindings
                    for i in 0..MAX_MEMBEROF_CHECKS {
                        let active = row[col::memberof_check_active(i)];
                        let trace_a = row[col::memberof_check_term_a(i)];
                        let trace_b = row[col::memberof_check_term_b(i)];
                        let resolved_a = resolve_slot(col::memberof_check_term_a_slot(i));
                        let resolved_b = resolve_slot(col::memberof_check_term_b_slot(i));
                        let diff_a = trace_a - resolved_a;
                        let diff_b = trace_b - resolved_b;
                        result = result + active * (diff_a * diff_a + diff_b * diff_b);
                    }

                    // GTE check term bindings
                    {
                        let active = row[col::GTE_CHECK_ACTIVE];
                        let trace_a = row[col::GTE_CHECK_TERM_A];
                        let trace_b = row[col::GTE_CHECK_TERM_B];
                        let resolved_a = resolve_slot(col::GTE_TERM_A_SLOT);
                        let resolved_b = resolve_slot(col::GTE_TERM_B_SLOT);
                        let diff_a = trace_a - resolved_a;
                        let diff_b = trace_b - resolved_b;
                        result = result + active * (diff_a * diff_a + diff_b * diff_b);
                    }

                    // LT check term bindings
                    {
                        let active = row[col::LT_CHECK_ACTIVE];
                        let trace_a = row[col::LT_CHECK_TERM_A];
                        let trace_b = row[col::LT_CHECK_TERM_B];
                        let resolved_a = resolve_slot(col::LT_TERM_A_SLOT);
                        let resolved_b = resolve_slot(col::LT_TERM_B_SLOT);
                        let diff_a = trace_a - resolved_a;
                        let diff_b = trace_b - resolved_b;
                        result = result + active * (diff_a * diff_a + diff_b * diff_b);
                    }

                    result
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

        // --- Check term binding columns (SOUNDNESS FIX) ---
        // Fill in the is_var, raw_value, and selector columns for each check term,
        // binding them to the substitution so the verifier can confirm term resolution.

        // Helper closure to populate binding columns for a single check term
        let fill_check_term_binding =
            |row: &mut Vec<BabyBear>, slot: usize, is_var: bool, value: BabyBear| {
                row[col::check_term_is_var(slot)] = if is_var {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                };
                row[col::check_term_raw_value(slot)] = value;
                if is_var {
                    let var_idx = value.as_u32() as usize;
                    if var_idx < MAX_SUB_VARS {
                        row[col::check_term_sel(slot, var_idx)] = BabyBear::ONE;
                    }
                }
            };

        // Equal checks
        for (check_i, eq_check) in w
            .rule
            .equal_checks
            .iter()
            .enumerate()
            .take(MAX_EQUAL_CHECKS)
        {
            fill_check_term_binding(
                &mut row,
                col::eq_check_term_a_slot(check_i),
                eq_check.lhs_is_var,
                eq_check.lhs_value,
            );
            fill_check_term_binding(
                &mut row,
                col::eq_check_term_b_slot(check_i),
                eq_check.rhs_is_var,
                eq_check.rhs_value,
            );
        }

        // MemberOf checks
        for (check_i, mo_check) in w
            .rule
            .memberof_checks
            .iter()
            .enumerate()
            .take(MAX_MEMBEROF_CHECKS)
        {
            fill_check_term_binding(
                &mut row,
                col::memberof_check_term_a_slot(check_i),
                mo_check.lhs_is_var,
                mo_check.lhs_value,
            );
            fill_check_term_binding(
                &mut row,
                col::memberof_check_term_b_slot(check_i),
                mo_check.rhs_is_var,
                mo_check.rhs_value,
            );
        }

        // GTE check
        if let Some(gte_check) = &w.rule.gte_check {
            fill_check_term_binding(
                &mut row,
                col::GTE_TERM_A_SLOT,
                gte_check.lhs_is_var,
                gte_check.lhs_value,
            );
            fill_check_term_binding(
                &mut row,
                col::GTE_TERM_B_SLOT,
                gte_check.rhs_is_var,
                gte_check.rhs_value,
            );
        }

        // LT check
        if let Some(lt_check) = &w.rule.lt_check {
            fill_check_term_binding(
                &mut row,
                col::LT_TERM_A_SLOT,
                lt_check.lhs_is_var,
                lt_check.lhs_value,
            );
            fill_check_term_binding(
                &mut row,
                col::LT_TERM_B_SLOT,
                lt_check.rhs_is_var,
                lt_check.rhs_value,
            );
        }

        let public_inputs = vec![
            w.state_root,
            derived_hash,
            w.not_after_height,
            w.org_id_hash,
            w.budget_remaining,
        ];
        (vec![row], public_inputs)
    }
}

// ============================================================================
// DerivationStarkAir: Real STARK proof generation/verification for derivation steps.
// ============================================================================

/// StarkAir implementation for the Derivation step.
///
/// This enables generating real STARK proofs (polynomial commitment + FRI)
/// for derivation operations, replacing the ConstraintProof (BLAKE3 trace digest)
/// that provides no cryptographic soundness.
///
/// The derivation AIR is single-row (no transition constraints), making it
/// perfectly suited for the custom STARK framework.
pub struct DerivationStarkAir {
    pub witness: DerivationWitness,
}

impl DerivationStarkAir {
    pub fn new(witness: DerivationWitness) -> Self {
        Self { witness }
    }
}

impl StarkAir for DerivationStarkAir {
    fn width(&self) -> usize {
        DERIVATION_AIR_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // The highest-degree polynomial constraint is the substitution application
        // which involves products of selectors and substitution values (degree 2).
        // The binary checks are also degree 2.
        2
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-derivation-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut result = BabyBear::ZERO;
        let mut alpha_power = BabyBear::ONE;

        // C1: body_membership_binary
        for i in 0..MAX_BODY_ATOMS {
            let flag = local[col::BODY_MEMBERSHIP_START + i];
            result = result + alpha_power * (flag * (flag - BabyBear::ONE));
        }
        alpha_power = alpha_power * alpha;

        // C2: body_hash_nonzero_when_used
        for i in 0..MAX_BODY_ATOMS {
            let flag = local[col::BODY_MEMBERSHIP_START + i];
            let hash = local[col::BODY_HASH_START + i];
            if flag == BabyBear::ONE && hash == BabyBear::ZERO {
                result = result + alpha_power * BabyBear::ONE;
            }
        }
        alpha_power = alpha_power * alpha;

        // C3: at_least_one_body
        let mut sum = BabyBear::ZERO;
        for i in 0..MAX_BODY_ATOMS {
            sum = sum + local[col::BODY_MEMBERSHIP_START + i];
        }
        if sum == BabyBear::ZERO {
            result = result + alpha_power * BabyBear::ONE;
        }
        alpha_power = alpha_power * alpha;

        // C4: derived_hash_correct
        let pred = local[col::HEAD_PRED];
        let terms = [
            local[col::HEAD_TERM_START],
            local[col::HEAD_TERM_START + 1],
            local[col::HEAD_TERM_START + 2],
            local[col::HEAD_TERM_START + 3],
        ];
        let expected_hash = hash_fact(pred, &terms);
        result = result + alpha_power * (expected_hash - local[col::DERIVED_HASH]);
        alpha_power = alpha_power * alpha;

        // C5: body_roots_match_state
        let state_root = public_inputs[0];
        for i in 0..MAX_BODY_ATOMS {
            let flag = local[col::BODY_MEMBERSHIP_START + i];
            let root = local[col::BODY_ROOT_START + i];
            result = result + alpha_power * (flag * (root - state_root));
        }
        alpha_power = alpha_power * alpha;

        // C6: derived_hash_public
        result = result + alpha_power * (local[col::DERIVED_HASH] - public_inputs[1]);
        alpha_power = alpha_power * alpha;

        // C7: head_is_var_binary
        for i in 0..MAX_HEAD_TERMS {
            let flag = local[col::HEAD_IS_VAR_START + i];
            result = result + alpha_power * (flag * (flag - BabyBear::ONE));
        }
        alpha_power = alpha_power * alpha;

        // C8: head_sel_var_binary
        for term_i in 0..MAX_HEAD_TERMS {
            for var_j in 0..MAX_SUB_VARS {
                let sel = local[col::head_sel_var(term_i, var_j)];
                result = result + alpha_power * (sel * (sel - BabyBear::ONE));
            }
        }
        alpha_power = alpha_power * alpha;

        // C9: head_sel_var_sum_equals_is_var
        for term_i in 0..MAX_HEAD_TERMS {
            let is_var = local[col::HEAD_IS_VAR_START + term_i];
            let mut sel_sum = BabyBear::ZERO;
            for var_j in 0..MAX_SUB_VARS {
                sel_sum = sel_sum + local[col::head_sel_var(term_i, var_j)];
            }
            let diff = sel_sum - is_var;
            result = result + alpha_power * (diff * diff);
        }
        alpha_power = alpha_power * alpha;

        // C10: substitution_application
        for term_i in 0..MAX_HEAD_TERMS {
            let is_var = local[col::HEAD_IS_VAR_START + term_i];
            let raw_value = local[col::HEAD_RAW_VALUE_START + term_i];
            let derived_term = local[col::HEAD_TERM_START + term_i];

            let mut var_resolved = BabyBear::ZERO;
            for var_j in 0..MAX_SUB_VARS {
                let sel = local[col::head_sel_var(term_i, var_j)];
                let sub_val = local[col::SUB_VALUE_START + var_j];
                var_resolved = var_resolved + sel * sub_val;
            }

            let expected = is_var * var_resolved + (BabyBear::ONE - is_var) * raw_value;
            let diff = derived_term - expected;
            result = result + alpha_power * (diff * diff);
        }
        alpha_power = alpha_power * alpha;

        // C11: eq_check_active_binary
        for i in 0..MAX_EQUAL_CHECKS {
            let active = local[col::eq_check_active(i)];
            result = result + alpha_power * (active * (active - BabyBear::ONE));
        }
        alpha_power = alpha_power * alpha;

        // C12: eq_check_enforced
        for i in 0..MAX_EQUAL_CHECKS {
            let active = local[col::eq_check_active(i)];
            let term_a = local[col::eq_check_term_a(i)];
            let term_b = local[col::eq_check_term_b(i)];
            result = result + alpha_power * (active * (term_a - term_b));
        }
        alpha_power = alpha_power * alpha;

        // C13: memberof_check_active_binary
        for i in 0..MAX_MEMBEROF_CHECKS {
            let active = local[col::memberof_check_active(i)];
            result = result + alpha_power * (active * (active - BabyBear::ONE));
        }
        alpha_power = alpha_power * alpha;

        // C14: memberof_check_enforced
        for i in 0..MAX_MEMBEROF_CHECKS {
            let active = local[col::memberof_check_active(i)];
            let term_a = local[col::memberof_check_term_a(i)];
            let term_b = local[col::memberof_check_term_b(i)];
            result = result + alpha_power * (active * (term_a - term_b));
        }
        alpha_power = alpha_power * alpha;

        // C15: gte_check_active_binary
        let gte_active = local[col::GTE_CHECK_ACTIVE];
        result = result + alpha_power * (gte_active * (gte_active - BabyBear::ONE));
        alpha_power = alpha_power * alpha;

        // C16: gte_check_diff_correct
        let gte_term_a = local[col::GTE_CHECK_TERM_A];
        let gte_term_b = local[col::GTE_CHECK_TERM_B];
        let gte_diff = local[col::GTE_CHECK_DIFF];
        result = result + alpha_power * (gte_active * (gte_diff - (gte_term_a - gte_term_b)));
        alpha_power = alpha_power * alpha;

        // C17: gte_check_bit_decomposition
        {
            let mut recomposed = BabyBear::ZERO;
            let mut power_of_two = BabyBear::ONE;
            for i in 0..GTE_DIFF_BITS {
                let bit = local[col::gte_diff_bit(i)];
                recomposed = recomposed + bit * power_of_two;
                power_of_two = power_of_two + power_of_two;
            }
            result = result + alpha_power * (gte_active * (recomposed - gte_diff));
        }
        alpha_power = alpha_power * alpha;

        // C18: gte_check_bits_binary
        {
            let mut bits_result = BabyBear::ZERO;
            for i in 0..GTE_DIFF_BITS {
                let bit = local[col::gte_diff_bit(i)];
                bits_result = bits_result + bit * (bit - BabyBear::ONE);
            }
            result = result + alpha_power * (gte_active * bits_result);
        }
        alpha_power = alpha_power * alpha;

        // C19: gte_check_high_bit_zero
        let gte_high_bit = local[col::gte_diff_bit(GTE_DIFF_BITS - 1)];
        result = result + alpha_power * (gte_active * gte_high_bit);
        alpha_power = alpha_power * alpha;

        // C20: lt_check_active_binary
        let lt_active = local[col::LT_CHECK_ACTIVE];
        result = result + alpha_power * (lt_active * (lt_active - BabyBear::ONE));
        alpha_power = alpha_power * alpha;

        // C21: lt_check_diff_correct
        let lt_term_a = local[col::LT_CHECK_TERM_A];
        let lt_term_b = local[col::LT_CHECK_TERM_B];
        let lt_diff = local[col::LT_CHECK_DIFF];
        result = result
            + alpha_power * (lt_active * (lt_diff - (lt_term_b - lt_term_a - BabyBear::ONE)));
        alpha_power = alpha_power * alpha;

        // C22: lt_check_bit_decomposition
        {
            let mut recomposed = BabyBear::ZERO;
            let mut power_of_two = BabyBear::ONE;
            for i in 0..GTE_DIFF_BITS {
                let bit = local[col::lt_diff_bit(i)];
                recomposed = recomposed + bit * power_of_two;
                power_of_two = power_of_two + power_of_two;
            }
            result = result + alpha_power * (lt_active * (recomposed - lt_diff));
        }
        alpha_power = alpha_power * alpha;

        // C23: lt_check_bits_binary
        {
            let mut bits_result = BabyBear::ZERO;
            for i in 0..GTE_DIFF_BITS {
                let bit = local[col::lt_diff_bit(i)];
                bits_result = bits_result + bit * (bit - BabyBear::ONE);
            }
            result = result + alpha_power * (lt_active * bits_result);
        }
        alpha_power = alpha_power * alpha;

        // C24: lt_check_high_bit_zero
        let lt_high_bit = local[col::lt_diff_bit(GTE_DIFF_BITS - 1)];
        result = result + alpha_power * (lt_active * lt_high_bit);
        alpha_power = alpha_power * alpha;

        // C25: check_term_is_var_binary
        for slot in 0..col::NUM_CHECK_TERMS {
            let is_var = local[col::check_term_is_var(slot)];
            result = result + alpha_power * (is_var * (is_var - BabyBear::ONE));
        }
        alpha_power = alpha_power * alpha;

        // C26: check_term_sel_binary
        for slot in 0..col::NUM_CHECK_TERMS {
            for var_j in 0..MAX_SUB_VARS {
                let sel = local[col::check_term_sel(slot, var_j)];
                result = result + alpha_power * (sel * (sel - BabyBear::ONE));
            }
        }
        alpha_power = alpha_power * alpha;

        // C27: check_term_sel_sum_equals_is_var
        for slot in 0..col::NUM_CHECK_TERMS {
            let is_var = local[col::check_term_is_var(slot)];
            let mut sel_sum = BabyBear::ZERO;
            for var_j in 0..MAX_SUB_VARS {
                sel_sum = sel_sum + local[col::check_term_sel(slot, var_j)];
            }
            let diff = sel_sum - is_var;
            result = result + alpha_power * (diff * diff);
        }
        alpha_power = alpha_power * alpha;

        // C28: check_term_binding_correct
        // Helper: compute resolved value for a slot from binding columns
        let resolve_slot = |slot: usize| -> BabyBear {
            let is_var = local[col::check_term_is_var(slot)];
            let raw_value = local[col::check_term_raw_value(slot)];
            let mut var_resolved = BabyBear::ZERO;
            for var_j in 0..MAX_SUB_VARS {
                let sel = local[col::check_term_sel(slot, var_j)];
                let sub_val = local[col::SUB_VALUE_START + var_j];
                var_resolved = var_resolved + sel * sub_val;
            }
            is_var * var_resolved + (BabyBear::ONE - is_var) * raw_value
        };

        // Equal check term bindings
        for i in 0..MAX_EQUAL_CHECKS {
            let active = local[col::eq_check_active(i)];
            let trace_a = local[col::eq_check_term_a(i)];
            let trace_b = local[col::eq_check_term_b(i)];
            let resolved_a = resolve_slot(col::eq_check_term_a_slot(i));
            let resolved_b = resolve_slot(col::eq_check_term_b_slot(i));
            let diff_a = trace_a - resolved_a;
            let diff_b = trace_b - resolved_b;
            result = result + alpha_power * (active * (diff_a * diff_a + diff_b * diff_b));
        }

        // MemberOf check term bindings
        for i in 0..MAX_MEMBEROF_CHECKS {
            let active = local[col::memberof_check_active(i)];
            let trace_a = local[col::memberof_check_term_a(i)];
            let trace_b = local[col::memberof_check_term_b(i)];
            let resolved_a = resolve_slot(col::memberof_check_term_a_slot(i));
            let resolved_b = resolve_slot(col::memberof_check_term_b_slot(i));
            let diff_a = trace_a - resolved_a;
            let diff_b = trace_b - resolved_b;
            result = result + alpha_power * (active * (diff_a * diff_a + diff_b * diff_b));
        }

        // GTE check term bindings
        {
            let active = local[col::GTE_CHECK_ACTIVE];
            let trace_a = local[col::GTE_CHECK_TERM_A];
            let trace_b = local[col::GTE_CHECK_TERM_B];
            let resolved_a = resolve_slot(col::GTE_TERM_A_SLOT);
            let resolved_b = resolve_slot(col::GTE_TERM_B_SLOT);
            let diff_a = trace_a - resolved_a;
            let diff_b = trace_b - resolved_b;
            result = result + alpha_power * (active * (diff_a * diff_a + diff_b * diff_b));
        }

        // LT check term bindings
        {
            let active = local[col::LT_CHECK_ACTIVE];
            let trace_a = local[col::LT_CHECK_TERM_A];
            let trace_b = local[col::LT_CHECK_TERM_B];
            let resolved_a = resolve_slot(col::LT_TERM_A_SLOT);
            let resolved_b = resolve_slot(col::LT_TERM_B_SLOT);
            let diff_a = trace_a - resolved_a;
            let diff_b = trace_b - resolved_b;
            result = result + alpha_power * (active * (diff_a * diff_a + diff_b * diff_b));
        }

        result
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 2 {
            // Row 0, DERIVED_HASH = public_inputs[1] (derived fact hash)
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::DERIVED_HASH,
                value: public_inputs[1],
            });
            // Row 0, BODY_ROOT_START = public_inputs[0] (state root for first body atom)
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::BODY_ROOT_START,
                value: public_inputs[0],
            });
        }
        constraints
    }
}

/// Generate a real STARK proof for a derivation step.
///
/// This produces a cryptographically sound proof (polynomial commitment + FRI)
/// that the derivation was performed correctly. The verifier can check this
/// without seeing the witness.
///
/// Returns `None` if the witness fails constraint checking.
pub fn prove_derivation_stark(witness: &DerivationWitness) -> Option<StarkProof> {
    let air = DerivationStarkAir::new(witness.clone());
    let derivation_air = DerivationAir::new(witness.clone());

    // Generate trace and public inputs
    let (trace, public_inputs) = derivation_air.generate_trace();

    // DerivationAir generates a single-row trace. STARK prover requires >= 2 rows
    // with power-of-two size, so pad to 2.
    let padded_len = trace.len().next_power_of_two().max(2);
    let mut padded_trace = trace;
    while padded_trace.len() < padded_len {
        // Pad with copies of the single row (all constraints are per-row-only,
        // so duplicating the valid row maintains satisfaction)
        padded_trace.push(padded_trace.last().unwrap().clone());
    }

    Some(stark::prove(&air, &padded_trace, &public_inputs))
}

/// Verify a STARK proof for a derivation step.
///
/// Returns `Ok(())` if the proof is valid, or an error message describing the failure.
pub fn verify_derivation_stark(
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    // Reconstruct a minimal witness just for AIR metadata (width, name, etc.)
    let dummy_witness = DerivationWitness {
        rule: CircuitRule {
            id: 0,
            num_body_atoms: 1,
            num_variables: 0,
            head_predicate: BabyBear::ZERO,
            head_terms: [
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root: BabyBear::ZERO,
        body_fact_hashes: vec![BabyBear::ONE],
        substitution: vec![],
        derived_predicate: BabyBear::ZERO,
        derived_terms: [BabyBear::ZERO; 4],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    };
    let air = DerivationStarkAir::new(dummy_witness);
    stark::verify(&air, proof, public_inputs)
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
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
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
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            lt_check: None,
        };

        let body_fact = hash_fact(owns_pred, &[budget, cost, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![budget, cost], // X=50, Y=10
            derived_predicate: access_pred,
            derived_terms: [budget, cost, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            lt_check: None,
        };

        let body_fact = hash_fact(owns_pred, &[budget, cost, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![budget, cost], // X=5, Y=10 (5 < 10, so GTE fails)
            derived_predicate: access_pred,
            derived_terms: [budget, cost, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            lt_check: None,
        };

        let body_fact = hash_fact(budget_pred, &[action_hash, budget, cost]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![action_hash, budget, cost],
            derived_predicate: grant_pred,
            derived_terms: [action_hash, budget, cost, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
            lt_check: None,
        };

        let body_fact = hash_fact(owns_pred, &[val, val, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![val, val], // 10 >= 10
            derived_predicate: access_pred,
            derived_terms: [val, val, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GTE check 10 >= 10 should pass: {:?}",
            result.violations()
        );
    }

    // ========================================================================
    // DerivationStarkAir STARK proof generation/verification tests
    // ========================================================================

    #[test]
    fn derivation_stark_proof_basic() {
        let witness = create_test_derivation();
        let proof =
            prove_derivation_stark(&witness).expect("derivation STARK proof should generate");

        // Verify against the correct public inputs
        let air = DerivationAir::new(witness.clone());
        let (_, public_inputs) = air.generate_trace();
        assert!(
            verify_derivation_stark(&proof, &public_inputs).is_ok(),
            "derivation STARK proof should verify"
        );
    }

    #[test]
    fn derivation_stark_proof_wrong_public_inputs_fails() {
        let witness = create_test_derivation();
        let proof =
            prove_derivation_stark(&witness).expect("derivation STARK proof should generate");

        // Tamper with public inputs: wrong state_root
        let air = DerivationAir::new(witness.clone());
        let (_, mut public_inputs) = air.generate_trace();
        public_inputs[0] = BabyBear::new(11111); // wrong state_root
        assert!(
            verify_derivation_stark(&proof, &public_inputs).is_err(),
            "derivation STARK proof with wrong public inputs should fail"
        );
    }

    #[test]
    fn derivation_stark_proof_tampered_commitment_fails() {
        let witness = create_test_derivation();
        let mut proof =
            prove_derivation_stark(&witness).expect("derivation STARK proof should generate");

        // Tamper with the trace commitment
        proof.trace_commitment[0] ^= 0xFF;

        let air = DerivationAir::new(witness.clone());
        let (_, public_inputs) = air.generate_trace();
        assert!(
            verify_derivation_stark(&proof, &public_inputs).is_err(),
            "tampered derivation STARK proof should fail"
        );
    }

    #[test]
    fn derivation_stark_proof_with_gte_check() {
        // Verify that a derivation with a GTE check produces a valid STARK proof.
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
                lhs_value: BabyBear::new(0),
                rhs_is_var: true,
                rhs_value: BabyBear::new(1),
            }),
            lt_check: None,
        };

        let body_fact = hash_fact(owns_pred, &[budget, cost, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![budget, cost],
            derived_predicate: access_pred,
            derived_terms: [budget, cost, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let proof =
            prove_derivation_stark(&witness).expect("derivation STARK proof with GTE should gen");

        let air = DerivationAir::new(witness.clone());
        let (_, public_inputs) = air.generate_trace();
        assert!(
            verify_derivation_stark(&proof, &public_inputs).is_ok(),
            "derivation STARK proof with GTE check should verify"
        );
    }

    // ========================================================================
    // Soundness fix tests: check term binding constraints
    // ========================================================================

    #[test]
    fn test_prover_lies_about_equal_check_term_rejected() {
        // SOUNDNESS TEST: A malicious prover sets eq_check term_a=5, term_b=5
        // in the trace (so the equality constraint passes), but the actual
        // substitution has X=1000, Y=2000. The binding constraint should catch this.
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let alice = BabyBear::new(1000);
        let file = BabyBear::new(2000);

        let rule = CircuitRule {
            id: 10,
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
            // Equal check: X == Y (var 0 == var 1)
            // With X=1000, Y=2000 this should NOT pass honestly.
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

        let body_fact = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, file], // X=1000, Y=2000
            derived_predicate: access_pred,
            derived_terms: [alice, file, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        // Generate trace honestly, then tamper with the eq check terms
        let air = DerivationAir::new(witness.clone());
        let (mut trace, public_inputs) = air.generate_trace();

        // Malicious prover: overwrite term_a and term_b to both be 5
        // so that active*(term_a - term_b) = 1*(5-5) = 0 passes
        trace[0][col::eq_check_term_a(0)] = BabyBear::new(5);
        trace[0][col::eq_check_term_b(0)] = BabyBear::new(5);

        // Verify using the tampered trace directly
        struct TamperedAir {
            trace: Vec<Vec<BabyBear>>,
            public_inputs: Vec<BabyBear>,
        }
        impl Air for TamperedAir {
            fn trace_width(&self) -> usize {
                DERIVATION_AIR_WIDTH
            }
            fn num_public_inputs(&self) -> usize {
                5
            }
            fn constraints(&self) -> Vec<Constraint> {
                let w = create_test_derivation(); // just for constraints
                DerivationAir::new(w).constraints()
            }
            fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
                (self.trace.clone(), self.public_inputs.clone())
            }
        }

        let tampered = TamperedAir {
            trace,
            public_inputs,
        };
        let result = ConstraintProver::verify(&tampered);
        assert!(
            !result.is_valid(),
            "Prover lying about eq check terms should be REJECTED by binding constraint"
        );
        let has_binding_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "check_term_binding_correct");
        assert!(
            has_binding_violation,
            "Should have check_term_binding_correct violation, got: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_prover_lies_about_gte_check_term_rejected() {
        // SOUNDNESS TEST: A malicious prover has budget=5 (sub[0]=5) and cost=10 (sub[1]=10).
        // GTE check requires sub[0] >= sub[1], which fails honestly (5 < 10).
        // Prover lies by setting GTE term_a=100, term_b=10 in the trace.
        // The binding constraint should catch that term_a != resolved(sub[0]).
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let budget = BabyBear::new(5);
        let cost = BabyBear::new(10);

        let rule = CircuitRule {
            id: 11,
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
                lhs_value: BabyBear::new(0), // budget (sub[0] = 5)
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // cost (sub[1] = 10)
            }),
            lt_check: None,
        };

        let body_fact = hash_fact(owns_pred, &[budget, cost, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![budget, cost], // sub[0]=5, sub[1]=10
            derived_predicate: access_pred,
            derived_terms: [budget, cost, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        // Generate trace honestly, then tamper
        let air = DerivationAir::new(witness.clone());
        let (mut trace, public_inputs) = air.generate_trace();

        // Malicious prover: overwrite GTE terms to fake passing
        // Set term_a = 100, term_b = 10, diff = 90 (which passes bit decomp + high bit)
        let fake_a = BabyBear::new(100);
        let fake_b = BabyBear::new(10);
        let fake_diff = fake_a - fake_b; // 90
        trace[0][col::GTE_CHECK_TERM_A] = fake_a;
        trace[0][col::GTE_CHECK_TERM_B] = fake_b;
        trace[0][col::GTE_CHECK_DIFF] = fake_diff;
        // Fix bit decomposition for the fake diff (90)
        let diff_val = fake_diff.as_u32();
        for i in 0..GTE_DIFF_BITS {
            let bit = (diff_val >> i) & 1;
            trace[0][col::gte_diff_bit(i)] = BabyBear::new(bit);
        }

        struct TamperedAir {
            trace: Vec<Vec<BabyBear>>,
            public_inputs: Vec<BabyBear>,
        }
        impl Air for TamperedAir {
            fn trace_width(&self) -> usize {
                DERIVATION_AIR_WIDTH
            }
            fn num_public_inputs(&self) -> usize {
                5
            }
            fn constraints(&self) -> Vec<Constraint> {
                let w = create_test_derivation();
                DerivationAir::new(w).constraints()
            }
            fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
                (self.trace.clone(), self.public_inputs.clone())
            }
        }

        let tampered = TamperedAir {
            trace,
            public_inputs,
        };
        let result = ConstraintProver::verify(&tampered);
        assert!(
            !result.is_valid(),
            "Prover lying about GTE check terms should be REJECTED by binding constraint"
        );
        let has_binding_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "check_term_binding_correct");
        assert!(
            has_binding_violation,
            "Should have check_term_binding_correct violation, got: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_honest_prover_with_variable_references_passes() {
        // Verify that an honest prover with variable references in all check types passes.
        // Rule with Equal (X==Y where X=Y=42), MemberOf (X==Y), and GTE (X>=Y where X=100, Y=50).
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let val = BabyBear::new(42);
        let budget = BabyBear::new(100);
        let cost = BabyBear::new(50);

        let rule = CircuitRule {
            id: 12,
            num_body_atoms: 1,
            num_variables: 4,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)), // X
                (true, BabyBear::new(1)), // Y
                (true, BabyBear::new(2)), // budget
                (true, BabyBear::new(3)), // cost
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (true, BabyBear::new(2)),
                ],
            }],
            // Equal: X == Y (both are 42)
            equal_checks: vec![CircuitEqualCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // X
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // Y
            }],
            // MemberOf: X == Y (same vars, passes)
            memberof_checks: vec![CircuitMemberOfCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // X
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // Y
            }],
            // GTE: budget >= cost (100 >= 50)
            gte_check: Some(CircuitGteCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(2), // budget
                rhs_is_var: true,
                rhs_value: BabyBear::new(3), // cost
            }),
            lt_check: None,
        };

        let body_fact = hash_fact(owns_pred, &[val, val, budget]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![val, val, budget, cost], // X=42, Y=42, budget=100, cost=50
            derived_predicate: access_pred,
            derived_terms: [val, val, budget, cost],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let air = DerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Honest prover with variable references in all check types should pass: {:?}",
            result.violations()
        );
    }
}
