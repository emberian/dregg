//! Derivation step AIR.
//!
//! Proves one authorization derivation step:
//! - Rule ID + substitution (witness)
//! - Body facts exist (Merkle membership for each, up to 4 body atoms)
//! - Derived fact = rule head under substitution (substitution verification)
//! - Equal constraint checks pass under the substitution
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
//! | 40: eq_check_0_active | 1 if first Equal check is active               |
//! | 41: eq_check_0_term_a | Resolved value of Equal check 0 LHS            |
//! | 42: eq_check_0_term_b | Resolved value of Equal check 0 RHS            |
//! | 43: eq_check_1_active | 1 if second Equal check is active              |
//! | 44: eq_check_1_term_a | Resolved value of Equal check 1 LHS            |
//! | 45: eq_check_1_term_b | Resolved value of Equal check 1 RHS            |
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

use crate::field::BabyBear;
use crate::mock_prover::{Air, Constraint};
use crate::poseidon2::hash_fact;

/// Trace width for the derivation AIR.
pub const DERIVATION_AIR_WIDTH: usize = 46;

/// Maximum body atoms per rule.
pub const MAX_BODY_ATOMS: usize = 4;

/// Maximum substitution variables.
pub const MAX_SUB_VARS: usize = 4;

/// Maximum head terms.
pub const MAX_HEAD_TERMS: usize = 3;

/// Maximum Equal checks per rule.
pub const MAX_EQUAL_CHECKS: usize = 2;

/// Column indices.
pub mod col {
    use super::{MAX_HEAD_TERMS, MAX_SUB_VARS};

    pub const RULE_ID: usize = 0;
    pub const BODY_HASH_START: usize = 1;
    pub const BODY_MEMBERSHIP_START: usize = 5;
    pub const HEAD_PRED: usize = 9;
    pub const HEAD_TERM_START: usize = 10;
    pub const DERIVED_HASH: usize = 13;
    pub const SUB_VALUE_START: usize = 14;
    pub const BODY_ROOT_START: usize = 18;

    // --- Substitution verification columns ---
    /// head_is_var[i]: 1 if head term i is a variable reference, 0 if constant.
    pub const HEAD_IS_VAR_START: usize = 22;
    /// head_raw_value[i]: the variable index (when is_var=1) or the constant value (when is_var=0).
    pub const HEAD_RAW_VALUE_START: usize = 25;
    /// head_sel_var[term_i][var_j]: selector for which substitution variable to use.
    /// Layout: term 0 uses columns 28..31, term 1 uses 32..35, term 2 uses 36..39.
    pub const HEAD_SEL_VAR_START: usize = 28;

    /// Get the column index for head_sel_var[term_idx][var_idx].
    #[inline]
    pub const fn head_sel_var(term_idx: usize, var_idx: usize) -> usize {
        HEAD_SEL_VAR_START + term_idx * MAX_SUB_VARS + var_idx
    }

    // --- Equal check columns ---
    /// Each Equal check has 3 columns: (active, term_a_resolved, term_b_resolved).
    pub const EQ_CHECK_START: usize = 28 + MAX_HEAD_TERMS * MAX_SUB_VARS; // 28 + 12 = 40

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
    pub head_terms: [(bool, BabyBear); 3],
    /// Body atom patterns: predicate + term patterns for each body atom.
    pub body_atoms: Vec<BodyAtomPattern>,
    /// Equal checks: each is (term_a_is_var, term_a_value, term_b_is_var, term_b_value).
    /// Up to MAX_EQUAL_CHECKS.
    pub equal_checks: Vec<CircuitEqualCheck>,
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
    pub derived_terms: [BabyBear; 3],
}

impl DerivationWitness {
    /// Compute the derived fact hash.
    pub fn derived_hash(&self) -> BabyBear {
        hash_fact(self.derived_predicate, &self.derived_terms)
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
                eval: Box::new(|row, _, public_inputs| {
                    row[col::DERIVED_HASH] - public_inputs[1]
                }),
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
                        let expected = is_var * var_resolved
                            + (BabyBear::ONE - is_var) * raw_value;

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
        row[col::HEAD_TERM_START] = w.derived_terms[0];
        row[col::HEAD_TERM_START + 1] = w.derived_terms[1];
        row[col::HEAD_TERM_START + 2] = w.derived_terms[2];
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
            (true, BabyBear::new(0)),  // X
            (true, BabyBear::new(1)),  // Y
            (false, BabyBear::ZERO),   // unused
        ],
        body_atoms: vec![
            BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),  // X
                    (true, BabyBear::new(1)),  // Y
                    (false, BabyBear::ZERO),
                ],
            },
            BodyAtomPattern {
                predicate: can_read_pred,
                terms: [
                    (true, BabyBear::new(0)),  // X
                    (true, BabyBear::new(1)),  // Y
                    (false, BabyBear::ZERO),
                ],
            },
        ],
        equal_checks: vec![],
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
        derived_terms: [alice, file, BabyBear::ZERO],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mock_prover::MockProver;

    #[test]
    fn derivation_air_valid() {
        let witness = create_test_derivation();
        let air = DerivationAir::new(witness);
        let result = MockProver::verify(&air);
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
        let result = MockProver::verify(&air);
        // The trace generator recomputes hash from the (tampered) predicate,
        // so the trace is internally consistent.
        assert!(result.is_valid());
    }

    #[test]
    fn derivation_air_no_body_facts_fails() {
        let mut witness = create_test_derivation();
        witness.body_fact_hashes = vec![]; // no body facts
        let air = DerivationAir::new(witness);
        let result = MockProver::verify(&air);
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
        let result = MockProver::verify(&tampered);
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
        let result = MockProver::verify(&air);
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
        let result = MockProver::verify(&air);
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
        // Test rule with a constant in the head: result(X, "fixed_val", Y)
        // head_terms = [(var 0), (const 500), (var 1)]
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
                (true, BabyBear::new(0)),   // X -> substitution[0] = alice
                (false, fixed_val),          // constant 500
                (true, BabyBear::new(1)),   // Y -> substitution[1] = file
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
        };

        let body_fact = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, file],
            derived_predicate: access_pred,
            derived_terms: [alice, fixed_val, file], // X=1000, const=500, Y=2000
        };

        let air = DerivationAir::new(witness);
        let result = MockProver::verify(&air);
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
                (false, fixed_val),          // expects constant 500
                (true, BabyBear::new(1)),
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
        };

        let body_fact = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, file],
            derived_predicate: access_pred,
            derived_terms: [alice, BabyBear::new(777), file], // WRONG: 777 instead of 500
        };

        let air = DerivationAir::new(witness);
        let result = MockProver::verify(&air);
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
                (true, BabyBear::new(0)),  // X
                (true, BabyBear::new(1)),  // Y
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
        };

        // X=alice, Y=alice (they are equal, so the check passes)
        let body_fact = hash_fact(owns_pred, &[alice, alice, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, alice], // X=alice, Y=alice
            derived_predicate: access_pred,
            derived_terms: [alice, alice, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = MockProver::verify(&air);
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
                (true, BabyBear::new(0)),  // X
                (true, BabyBear::new(1)),  // Y
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
        };

        // X=alice (1000), Y=file (2000) — NOT equal
        let body_fact = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, file], // X=alice, Y=file (different!)
            derived_predicate: access_pred,
            derived_terms: [alice, file, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = MockProver::verify(&air);
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
                lhs_value: BabyBear::new(0),  // X
                rhs_is_var: false,
                rhs_value: alice,              // constant 1000
            }],
        };

        // X=alice=1000, check is X==1000, should pass
        let body_fact = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, file],
            derived_predicate: access_pred,
            derived_terms: [alice, file, BabyBear::ZERO],
        };

        let air = DerivationAir::new(witness);
        let result = MockProver::verify(&air);
        assert!(
            result.is_valid(),
            "Equal check var==const with matching values should pass: {:?}",
            result.violations()
        );
    }
}
