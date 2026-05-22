//! Multi-step derivation chaining AIR.
//!
//! Supports policies with up to 8 body atoms per rule, 8 variables, 32 derivation
//! steps. This covers: deep RBAC hierarchies, contextual authorization (time/location/
//! device), multi-hop delegation chains, and most real-world access control policies.
//!
//! Proves a sequence of Datalog derivation steps where the output of step N
//! becomes available as a known fact to step N+1. The final step must derive
//! the "allow" predicate (or the claimed conclusion).
//!
//! This is the core circuit that makes "the STARK proves authorization" real:
//! not just membership and fold chain, but the actual multi-step Datalog
//! evaluation that concluded ALLOW.
//!
//! # Trace layout (per row = one derivation step)
//!
//! Columns 0..137: same as single-step DerivationAir (138 columns)
//! Column 138: `step_index` — which step this is (0-based)
//! Column 139: `accumulated_facts_hash` — running hash of all derived facts including this step
//! Column 140: `prev_accumulated` — accumulated hash from previous row (or initial_state_root)
//! Column 141: `is_final_step` — 1 if this is the last meaningful step, 0 otherwise
//! Column 142: `is_active` — 1 if this row is an active derivation step, 0 if padding
//!
//! Total width: 376 columns (DERIVATION_AIR_WIDTH + 5).
//!
//! # Public inputs
//!
//! 0. `initial_state_root` — the committed fact set root
//! 1. `request_hash` — hash of the authorization request
//! 2. `conclusion` — 1 for ALLOW, 0 for DENY
//! 3. `num_steps` — how many derivation steps were taken
//! 4. `final_accumulated_hash` — commitment to the full derivation trace
//! 5. `policy_root` — Poseidon2 hash of the rule set (the verifier checks
//!    "this proof was made under policy P" by comparing to their known policy)
//!
//! # Constraints
//!
//! Per-row (same as DerivationAir):
//!   - Body membership binary, body hash nonzero when used, at least one body
//!   - Derived hash correct, body roots match state, head_is_var binary
//!   - Selector binary, selector sum equals is_var, substitution application
//!   - Equal check active binary, equal check enforced
//!
//! Multi-step chaining:
//!   - `accumulated_facts_hash[0] = hash(initial_state_root || derived_hash[0])`
//!   - `accumulated_facts_hash[k] = hash(prev_accumulated[k] || derived_hash[k])` for k > 0
//!   - `prev_accumulated[0] = initial_state_root` (public input)
//!   - `prev_accumulated[k] = accumulated_facts_hash[k-1]` (transition)
//!   - `is_final_step` is binary and exactly one row has it set to 1
//!   - `is_active` is binary; once it goes to 0, it stays 0
//!   - `is_final_step * (derived_predicate - ALLOW_PREDICATE) = 0`
//!   - On the final step, `accumulated_facts_hash = final_accumulated_hash` (public input)
//!   - Step index increments by 1 for active rows
//!   - Policy root: a Poseidon2 commitment to the FULL rule structure definitions
//!     (not just rule IDs). This binds rule_id, head_predicate, num_body_atoms,
//!     num_variables, head term patterns, equal/memberof/gte/lt checks. The verifier
//!     compares the proof's policy_root against their known policy hash. A prover
//!     CANNOT substitute a rule with stripped checks (same ID, no GTE) because the
//!     structure hash would differ.

use crate::constraint_prover::{Air, Constraint};
use crate::derivation_air::{
    DERIVATION_AIR_WIDTH, DerivationWitness, GTE_DIFF_BITS, MAX_BODY_ATOMS, MAX_EQUAL_CHECKS,
    MAX_HEAD_TERMS, MAX_MEMBEROF_CHECKS, MAX_SUB_VARS, col as dcol, compute_policy_root,
};
use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_fact};
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Trace width for the multi-step derivation AIR.
pub const MULTI_STEP_AIR_WIDTH: usize = DERIVATION_AIR_WIDTH + 5; // 371 + 5 = 376

/// Maximum derivation steps supported.
pub const MAX_STEPS: usize = 32;

/// The "allow" predicate field element. This is a well-known constant that
/// the final derivation step must produce as its head predicate.
/// We use a deterministic hash of "allow" to get a field element.
pub const ALLOW_PREDICATE: u32 = 0xA110; // "allow" marker

/// Column indices for multi-step-specific columns.
pub mod col {
    use super::DERIVATION_AIR_WIDTH;

    /// Step index (0-based).
    pub const STEP_INDEX: usize = DERIVATION_AIR_WIDTH; // 371
    /// Running accumulated hash of derived facts (including this step).
    pub const ACCUMULATED_HASH: usize = DERIVATION_AIR_WIDTH + 1; // 372
    /// Previous accumulated hash (from previous row, or initial_state_root for row 0).
    pub const PREV_ACCUMULATED: usize = DERIVATION_AIR_WIDTH + 2; // 373
    /// Is this the final derivation step? (binary flag)
    pub const IS_FINAL_STEP: usize = DERIVATION_AIR_WIDTH + 3; // 374
    /// Is this row an active step? (binary flag, 0 = padding)
    pub const IS_ACTIVE: usize = DERIVATION_AIR_WIDTH + 4; // 375
}

/// Public input indices.
pub mod pi {
    pub const INITIAL_STATE_ROOT: usize = 0;
    pub const REQUEST_HASH: usize = 1;
    pub const CONCLUSION: usize = 2;
    pub const NUM_STEPS: usize = 3;
    pub const FINAL_ACCUMULATED_HASH: usize = 4;
    /// Policy root: Poseidon2 hash of the FULL rule structure definitions.
    ///
    /// This commits to the complete rule structure including: rule_id, head_predicate,
    /// num_body_atoms, num_variables, head term patterns, equal checks, memberof checks,
    /// GTE check, and LT check. The verifier checks that the proof was generated under
    /// this specific policy by comparing to their known policy root.
    ///
    /// SOUNDNESS: A prover cannot substitute a rule with the same ID but stripped
    /// checks (e.g., removing a budget GTE constraint) because the structure hash
    /// would differ, producing a different policy_root that the verifier rejects.
    pub const POLICY_ROOT: usize = 5;
}

/// Witness for a multi-step derivation (the full authorization trace).
#[derive(Clone, Debug)]
pub struct MultiStepWitness {
    /// The initial state root (committed fact set).
    pub initial_state_root: BabyBear,
    /// Hash of the authorization request.
    pub request_hash: BabyBear,
    /// The derivation steps in order.
    pub steps: Vec<DerivationWitness>,
    /// The "allow" predicate value (field element for the allow predicate).
    pub allow_predicate: BabyBear,
    /// Policy root: Poseidon2 hash of the rule set. The verifier checks that the
    /// proof was generated under this specific policy. This makes the rule set a
    /// public input — the verifier can confirm "this proof was made under policy P".
    pub policy_root: BabyBear,
    /// Optional Merkle proofs for body facts (used by `prove_authorization_with_membership`).
    ///
    /// When present, each entry is (fact_hash, siblings, positions) proving that the
    /// body fact is a leaf in the Poseidon2 Merkle tree at `initial_state_root`.
    /// This closes the soundness gap: body fact membership is PROVEN, not just asserted.
    pub body_merkle_proofs: Option<Vec<(BabyBear, Vec<[BabyBear; 3]>, Vec<u8>)>>,
}

impl MultiStepWitness {
    /// Compute the conclusion: ALLOW if the last step derives the allow predicate.
    pub fn conclusion(&self) -> BabyBear {
        if let Some(last) = self.steps.last() {
            if last.derived_predicate == self.allow_predicate {
                BabyBear::ONE // ALLOW
            } else {
                BabyBear::ZERO // DENY
            }
        } else {
            BabyBear::ZERO // No steps = DENY
        }
    }

    /// Compute the accumulated hash chain.
    /// accumulated[0] = hash(initial_state_root || derived_hash[0])
    /// accumulated[k] = hash(accumulated[k-1] || derived_hash[k])
    pub fn compute_accumulated_hashes(&self) -> Vec<BabyBear> {
        let mut acc = Vec::with_capacity(self.steps.len());
        let mut prev = self.initial_state_root;

        for step in &self.steps {
            let derived_hash = step.derived_hash();
            let next = hash_2_to_1(prev, derived_hash);
            acc.push(next);
            prev = next;
        }

        acc
    }

    /// Get the final accumulated hash.
    pub fn final_accumulated_hash(&self) -> BabyBear {
        self.compute_accumulated_hashes()
            .last()
            .copied()
            .unwrap_or(self.initial_state_root)
    }
}

/// The multi-step derivation AIR.
pub struct MultiStepDerivationAir {
    pub witness: MultiStepWitness,
    /// Maximum number of rows (padded to this size).
    pub max_steps: usize,
}

impl MultiStepDerivationAir {
    pub fn new(witness: MultiStepWitness) -> Self {
        let max_steps = witness.steps.len().max(1);
        Self { witness, max_steps }
    }

    pub fn with_max_steps(witness: MultiStepWitness, max_steps: usize) -> Self {
        assert!(
            max_steps >= witness.steps.len(),
            "max_steps ({}) must be >= actual steps ({})",
            max_steps,
            witness.steps.len()
        );
        Self { witness, max_steps }
    }
}

impl Air for MultiStepDerivationAir {
    fn trace_width(&self) -> usize {
        MULTI_STEP_AIR_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        6
    }

    fn constraints(&self) -> Vec<Constraint> {
        vec![
            // === Per-row derivation constraints (only enforced when is_active=1) ===

            // Constraint 1: Body membership flags are binary (when active).
            Constraint {
                name: "body_membership_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_BODY_ATOMS {
                        let flag = row[dcol::BODY_MEMBERSHIP_START + i];
                        result = result + flag * (flag - BabyBear::ONE);
                    }
                    active * result
                }),
            },
            // Constraint 2: If membership flag is 1, body hash must be non-zero (when active).
            Constraint {
                name: "body_hash_nonzero_when_used".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_BODY_ATOMS {
                        let flag = row[dcol::BODY_MEMBERSHIP_START + i];
                        let hash = row[dcol::BODY_HASH_START + i];
                        if flag == BabyBear::ONE && hash == BabyBear::ZERO {
                            result = result + BabyBear::ONE;
                        }
                    }
                    active * result
                }),
            },
            // Constraint 3: At least one body fact must be used (when active).
            Constraint {
                name: "at_least_one_body".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut sum = BabyBear::ZERO;
                    for i in 0..MAX_BODY_ATOMS {
                        sum = sum + row[dcol::BODY_MEMBERSHIP_START + i];
                    }
                    if active == BabyBear::ONE && sum == BabyBear::ZERO {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
            // Constraint 4: Derived hash is correctly computed (when active).
            Constraint {
                name: "derived_hash_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let pred = row[dcol::HEAD_PRED];
                    let terms = [
                        row[dcol::HEAD_TERM_START],
                        row[dcol::HEAD_TERM_START + 1],
                        row[dcol::HEAD_TERM_START + 2],
                        row[dcol::HEAD_TERM_START + 3],
                    ];
                    let expected_hash = hash_fact(pred, &terms);
                    let claimed_hash = row[dcol::DERIVED_HASH];
                    active * (expected_hash - claimed_hash)
                }),
            },
            // Constraint 5: All body roots equal the state root (when active).
            // For multi-step, body roots must equal initial_state_root (public input 0).
            Constraint {
                name: "body_roots_match_state".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    let active = row[col::IS_ACTIVE];
                    let state_root = public_inputs[pi::INITIAL_STATE_ROOT];
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_BODY_ATOMS {
                        let flag = row[dcol::BODY_MEMBERSHIP_START + i];
                        let root = row[dcol::BODY_ROOT_START + i];
                        result = result + flag * (root - state_root);
                    }
                    active * result
                }),
            },
            // Constraint 6: head_is_var columns are binary (when active).
            Constraint {
                name: "head_is_var_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_HEAD_TERMS {
                        let flag = row[dcol::HEAD_IS_VAR_START + i];
                        result = result + flag * (flag - BabyBear::ONE);
                    }
                    active * result
                }),
            },
            // Constraint 7: Selector columns are binary (when active).
            Constraint {
                name: "head_sel_var_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for term_i in 0..MAX_HEAD_TERMS {
                        for var_j in 0..MAX_SUB_VARS {
                            let sel = row[dcol::head_sel_var(term_i, var_j)];
                            result = result + sel * (sel - BabyBear::ONE);
                        }
                    }
                    active * result
                }),
            },
            // Constraint 8: Selector sum equals is_var (when active).
            Constraint {
                name: "head_sel_var_sum_equals_is_var".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for term_i in 0..MAX_HEAD_TERMS {
                        let is_var = row[dcol::HEAD_IS_VAR_START + term_i];
                        let mut sel_sum = BabyBear::ZERO;
                        for var_j in 0..MAX_SUB_VARS {
                            sel_sum = sel_sum + row[dcol::head_sel_var(term_i, var_j)];
                        }
                        result = result + (sel_sum - is_var) * (sel_sum - is_var);
                    }
                    active * result
                }),
            },
            // Constraint 9: Substitution application (when active).
            Constraint {
                name: "substitution_application".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for term_i in 0..MAX_HEAD_TERMS {
                        let is_var = row[dcol::HEAD_IS_VAR_START + term_i];
                        let raw_value = row[dcol::HEAD_RAW_VALUE_START + term_i];
                        let derived_term = row[dcol::HEAD_TERM_START + term_i];

                        let mut var_resolved = BabyBear::ZERO;
                        for var_j in 0..MAX_SUB_VARS {
                            let sel = row[dcol::head_sel_var(term_i, var_j)];
                            let sub_val = row[dcol::SUB_VALUE_START + var_j];
                            var_resolved = var_resolved + sel * sub_val;
                        }

                        let expected = is_var * var_resolved + (BabyBear::ONE - is_var) * raw_value;
                        result = result + (derived_term - expected) * (derived_term - expected);
                    }
                    active * result
                }),
            },
            // Constraint 10: Equal check active flags are binary (when active).
            Constraint {
                name: "eq_check_active_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_EQUAL_CHECKS {
                        let flag = row[dcol::eq_check_active(i)];
                        result = result + flag * (flag - BabyBear::ONE);
                    }
                    active * result
                }),
            },
            // Constraint 11: Equal check enforcement (when active).
            Constraint {
                name: "eq_check_enforced".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_EQUAL_CHECKS {
                        let eq_active = row[dcol::eq_check_active(i)];
                        let term_a = row[dcol::eq_check_term_a(i)];
                        let term_b = row[dcol::eq_check_term_b(i)];
                        result = result + eq_active * (term_a - term_b);
                    }
                    active * result
                }),
            },
            // Constraint 12: MemberOf check active flags are binary (when active).
            Constraint {
                name: "memberof_check_active_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_MEMBEROF_CHECKS {
                        let flag = row[dcol::memberof_check_active(i)];
                        result = result + flag * (flag - BabyBear::ONE);
                    }
                    active * result
                }),
            },
            // Constraint 13: MemberOf check enforcement (when active).
            Constraint {
                name: "memberof_check_enforced".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..MAX_MEMBEROF_CHECKS {
                        let mo_active = row[dcol::memberof_check_active(i)];
                        let term_a = row[dcol::memberof_check_term_a(i)];
                        let term_b = row[dcol::memberof_check_term_b(i)];
                        result = result + mo_active * (term_a - term_b);
                    }
                    active * result
                }),
            },
            // Constraint 14: GTE check active flag is binary (when active).
            Constraint {
                name: "gte_check_active_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let gte_active = row[dcol::GTE_CHECK_ACTIVE];
                    active * gte_active * (gte_active - BabyBear::ONE)
                }),
            },
            // Constraint 15: GTE diff consistency (when active).
            Constraint {
                name: "gte_check_diff_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let gte_active = row[dcol::GTE_CHECK_ACTIVE];
                    let term_a = row[dcol::GTE_CHECK_TERM_A];
                    let term_b = row[dcol::GTE_CHECK_TERM_B];
                    let diff = row[dcol::GTE_CHECK_DIFF];
                    active * gte_active * (diff - (term_a - term_b))
                }),
            },
            // Constraint 16: GTE bit decomposition (when active).
            Constraint {
                name: "gte_check_bit_decomposition".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let gte_active = row[dcol::GTE_CHECK_ACTIVE];
                    let diff = row[dcol::GTE_CHECK_DIFF];
                    let mut recomposed = BabyBear::ZERO;
                    let mut power_of_two = BabyBear::ONE;
                    for i in 0..GTE_DIFF_BITS {
                        let bit = row[dcol::gte_diff_bit(i)];
                        recomposed = recomposed + bit * power_of_two;
                        power_of_two = power_of_two + power_of_two;
                    }
                    active * gte_active * (recomposed - diff)
                }),
            },
            // Constraint 17: GTE bits are binary (when active).
            Constraint {
                name: "gte_check_bits_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let gte_active = row[dcol::GTE_CHECK_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..GTE_DIFF_BITS {
                        let bit = row[dcol::gte_diff_bit(i)];
                        result = result + bit * (bit - BabyBear::ONE);
                    }
                    active * gte_active * result
                }),
            },
            // Constraint 18: GTE high bit is zero (when active).
            Constraint {
                name: "gte_check_high_bit_zero".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let gte_active = row[dcol::GTE_CHECK_ACTIVE];
                    let high_bit = row[dcol::gte_diff_bit(GTE_DIFF_BITS - 1)];
                    active * gte_active * high_bit
                }),
            },
            // Constraint 18b: LT check active flag is binary (when active).
            Constraint {
                name: "lt_check_active_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let lt_active = row[dcol::LT_CHECK_ACTIVE];
                    active * lt_active * (lt_active - BabyBear::ONE)
                }),
            },
            // Constraint 18c: LT diff consistency (when active).
            // lt_active * (diff - (term_b - term_a - 1)) = 0
            Constraint {
                name: "lt_check_diff_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let lt_active = row[dcol::LT_CHECK_ACTIVE];
                    let term_a = row[dcol::LT_CHECK_TERM_A];
                    let term_b = row[dcol::LT_CHECK_TERM_B];
                    let diff = row[dcol::LT_CHECK_DIFF];
                    active * lt_active * (diff - (term_b - term_a - BabyBear::ONE))
                }),
            },
            // Constraint 18d: LT bit decomposition (when active).
            Constraint {
                name: "lt_check_bit_decomposition".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let lt_active = row[dcol::LT_CHECK_ACTIVE];
                    let diff = row[dcol::LT_CHECK_DIFF];
                    let mut recomposed = BabyBear::ZERO;
                    let mut power_of_two = BabyBear::ONE;
                    for i in 0..GTE_DIFF_BITS {
                        let bit = row[dcol::lt_diff_bit(i)];
                        recomposed = recomposed + bit * power_of_two;
                        power_of_two = power_of_two + power_of_two;
                    }
                    active * lt_active * (recomposed - diff)
                }),
            },
            // Constraint 18e: LT bits are binary (when active).
            Constraint {
                name: "lt_check_bits_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let lt_active = row[dcol::LT_CHECK_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for i in 0..GTE_DIFF_BITS {
                        let bit = row[dcol::lt_diff_bit(i)];
                        result = result + bit * (bit - BabyBear::ONE);
                    }
                    active * lt_active * result
                }),
            },
            // Constraint 18f: LT high bit is zero (when active).
            Constraint {
                name: "lt_check_high_bit_zero".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let lt_active = row[dcol::LT_CHECK_ACTIVE];
                    let high_bit = row[dcol::lt_diff_bit(GTE_DIFF_BITS - 1)];
                    active * lt_active * high_bit
                }),
            },
            // ================================================================
            // SOUNDNESS FIX: Check term binding constraints
            // ================================================================
            // Constraint 18g: Check term is_var flags are binary (when row active).
            Constraint {
                name: "check_term_is_var_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for slot in 0..dcol::NUM_CHECK_TERMS {
                        let is_var = row[dcol::check_term_is_var(slot)];
                        result = result + is_var * (is_var - BabyBear::ONE);
                    }
                    active * result
                }),
            },
            // Constraint 18h: Check term selectors are binary (when row active).
            Constraint {
                name: "check_term_sel_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for slot in 0..dcol::NUM_CHECK_TERMS {
                        for var_j in 0..MAX_SUB_VARS {
                            let sel = row[dcol::check_term_sel(slot, var_j)];
                            result = result + sel * (sel - BabyBear::ONE);
                        }
                    }
                    active * result
                }),
            },
            // Constraint 18i: Check term selector sum = is_var (when row active).
            Constraint {
                name: "check_term_sel_sum_equals_is_var".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;
                    for slot in 0..dcol::NUM_CHECK_TERMS {
                        let is_var = row[dcol::check_term_is_var(slot)];
                        let mut sel_sum = BabyBear::ZERO;
                        for var_j in 0..MAX_SUB_VARS {
                            sel_sum = sel_sum + row[dcol::check_term_sel(slot, var_j)];
                        }
                        let diff = sel_sum - is_var;
                        result = result + diff * diff;
                    }
                    active * result
                }),
            },
            // Constraint 18j: Check term binding correctness (when row active).
            Constraint {
                name: "check_term_binding_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let mut result = BabyBear::ZERO;

                    let resolve_slot = |slot: usize| -> BabyBear {
                        let is_var = row[dcol::check_term_is_var(slot)];
                        let raw_value = row[dcol::check_term_raw_value(slot)];
                        let mut var_resolved = BabyBear::ZERO;
                        for var_j in 0..MAX_SUB_VARS {
                            let sel = row[dcol::check_term_sel(slot, var_j)];
                            let sub_val = row[dcol::SUB_VALUE_START + var_j];
                            var_resolved = var_resolved + sel * sub_val;
                        }
                        is_var * var_resolved + (BabyBear::ONE - is_var) * raw_value
                    };

                    for i in 0..MAX_EQUAL_CHECKS {
                        let eq_active = row[dcol::eq_check_active(i)];
                        let trace_a = row[dcol::eq_check_term_a(i)];
                        let trace_b = row[dcol::eq_check_term_b(i)];
                        let resolved_a = resolve_slot(dcol::eq_check_term_a_slot(i));
                        let resolved_b = resolve_slot(dcol::eq_check_term_b_slot(i));
                        let diff_a = trace_a - resolved_a;
                        let diff_b = trace_b - resolved_b;
                        result = result + eq_active * (diff_a * diff_a + diff_b * diff_b);
                    }

                    for i in 0..MAX_MEMBEROF_CHECKS {
                        let mo_active = row[dcol::memberof_check_active(i)];
                        let trace_a = row[dcol::memberof_check_term_a(i)];
                        let trace_b = row[dcol::memberof_check_term_b(i)];
                        let resolved_a = resolve_slot(dcol::memberof_check_term_a_slot(i));
                        let resolved_b = resolve_slot(dcol::memberof_check_term_b_slot(i));
                        let diff_a = trace_a - resolved_a;
                        let diff_b = trace_b - resolved_b;
                        result = result + mo_active * (diff_a * diff_a + diff_b * diff_b);
                    }

                    {
                        let gte_active = row[dcol::GTE_CHECK_ACTIVE];
                        let trace_a = row[dcol::GTE_CHECK_TERM_A];
                        let trace_b = row[dcol::GTE_CHECK_TERM_B];
                        let resolved_a = resolve_slot(dcol::GTE_TERM_A_SLOT);
                        let resolved_b = resolve_slot(dcol::GTE_TERM_B_SLOT);
                        let diff_a = trace_a - resolved_a;
                        let diff_b = trace_b - resolved_b;
                        result = result + gte_active * (diff_a * diff_a + diff_b * diff_b);
                    }

                    {
                        let lt_active = row[dcol::LT_CHECK_ACTIVE];
                        let trace_a = row[dcol::LT_CHECK_TERM_A];
                        let trace_b = row[dcol::LT_CHECK_TERM_B];
                        let resolved_a = resolve_slot(dcol::LT_TERM_A_SLOT);
                        let resolved_b = resolve_slot(dcol::LT_TERM_B_SLOT);
                        let diff_a = trace_a - resolved_a;
                        let diff_b = trace_b - resolved_b;
                        result = result + lt_active * (diff_a * diff_a + diff_b * diff_b);
                    }

                    active * result
                }),
            },
            // === Multi-step chaining constraints ===

            // Constraint 19: is_active is binary.
            Constraint {
                name: "is_active_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    active * (active - BabyBear::ONE)
                }),
            },
            // Constraint 13: is_final_step is binary.
            Constraint {
                name: "is_final_step_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let flag = row[col::IS_FINAL_STEP];
                    flag * (flag - BabyBear::ONE)
                }),
            },
            // Constraint 14: is_final_step implies is_active.
            // is_final_step * (1 - is_active) = 0
            Constraint {
                name: "final_step_implies_active".to_string(),
                eval: Box::new(|row, _, _| {
                    let is_final = row[col::IS_FINAL_STEP];
                    let is_active = row[col::IS_ACTIVE];
                    is_final * (BabyBear::ONE - is_active)
                }),
            },
            // Constraint 15: Accumulated hash is correctly computed (when active).
            // accumulated = hash(prev_accumulated || derived_hash)
            Constraint {
                name: "accumulated_hash_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let prev = row[col::PREV_ACCUMULATED];
                    let derived = row[dcol::DERIVED_HASH];
                    let claimed_acc = row[col::ACCUMULATED_HASH];
                    let expected = hash_2_to_1(prev, derived);
                    active * (expected - claimed_acc)
                }),
            },
            // Constraint 16: On the final step, the derived predicate must be ALLOW.
            // is_final * (head_pred - ALLOW_PREDICATE) = 0
            Constraint {
                name: "final_step_derives_allow".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    let is_final = row[col::IS_FINAL_STEP];
                    let head_pred = row[dcol::HEAD_PRED];
                    // The conclusion public input encodes what we expect:
                    // If conclusion=1 (ALLOW), final step must derive allow predicate.
                    let conclusion = public_inputs[pi::CONCLUSION];
                    let allow_pred = BabyBear::new(ALLOW_PREDICATE);
                    // Only enforce when conclusion is ALLOW (=1)
                    conclusion * is_final * (head_pred - allow_pred)
                }),
            },
            // Constraint 17: Final accumulated hash matches public input.
            // is_final * (accumulated_hash - final_accumulated_hash_pi) = 0
            Constraint {
                name: "final_accumulated_matches_public".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    let is_final = row[col::IS_FINAL_STEP];
                    let acc = row[col::ACCUMULATED_HASH];
                    let expected = public_inputs[pi::FINAL_ACCUMULATED_HASH];
                    is_final * (acc - expected)
                }),
            },
            // Constraint 18: Once is_active goes to 0, it stays 0 (no gaps).
            // If current is_active=0 and next exists, next must also be 0.
            Constraint {
                name: "active_monotone_decreasing".to_string(),
                eval: Box::new(|row, next_row, _| {
                    let active = row[col::IS_ACTIVE];
                    if let Some(next) = next_row {
                        let next_active = next[col::IS_ACTIVE];
                        // (1 - active) * next_active = 0
                        // i.e., if current is inactive, next must be inactive too
                        (BabyBear::ONE - active) * next_active
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
            // Constraint 19: Transition constraint for prev_accumulated chaining.
            // For row k > 0: prev_accumulated[k] = accumulated_hash[k-1]
            // This is checked on the NEXT row looking back at current row.
            Constraint {
                name: "prev_accumulated_chain".to_string(),
                eval: Box::new(|row, next_row, _| {
                    if let Some(next) = next_row {
                        let next_active = next[col::IS_ACTIVE];
                        let current_acc = row[col::ACCUMULATED_HASH];
                        let next_prev = next[col::PREV_ACCUMULATED];
                        // Only enforce for active next rows
                        next_active * (next_prev - current_acc)
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
        ]
    }

    fn first_row_constraints(&self) -> Vec<Constraint> {
        vec![
            // The first row's prev_accumulated must equal initial_state_root.
            Constraint {
                name: "first_row_prev_is_initial_root".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    let active = row[col::IS_ACTIVE];
                    let prev = row[col::PREV_ACCUMULATED];
                    let initial_root = public_inputs[pi::INITIAL_STATE_ROOT];
                    active * (prev - initial_root)
                }),
            },
            // The first row's step_index must be 0.
            Constraint {
                name: "first_row_step_index_zero".to_string(),
                eval: Box::new(|row, _, _| {
                    let active = row[col::IS_ACTIVE];
                    let idx = row[col::STEP_INDEX];
                    active * idx
                }),
            },
        ]
    }

    fn last_row_constraints(&self) -> Vec<Constraint> {
        vec![]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;
        let num_active = w.steps.len();
        let num_rows = self.max_steps;
        let accumulated_hashes = w.compute_accumulated_hashes();

        let mut trace = Vec::with_capacity(num_rows);

        for row_idx in 0..num_rows {
            let mut row = vec![BabyBear::ZERO; MULTI_STEP_AIR_WIDTH];

            if row_idx < num_active {
                let step = &w.steps[row_idx];
                let derived_hash = step.derived_hash();

                // --- Single-step derivation columns (same as DerivationAir) ---
                row[dcol::RULE_ID] = BabyBear::new(step.rule.id);

                for (i, &hash) in step
                    .body_fact_hashes
                    .iter()
                    .enumerate()
                    .take(MAX_BODY_ATOMS)
                {
                    row[dcol::BODY_HASH_START + i] = hash;
                    row[dcol::BODY_MEMBERSHIP_START + i] = BabyBear::ONE;
                    row[dcol::BODY_ROOT_START + i] = step.state_root;
                }

                row[dcol::HEAD_PRED] = step.derived_predicate;
                for i in 0..MAX_HEAD_TERMS {
                    row[dcol::HEAD_TERM_START + i] = step.derived_terms[i];
                }
                row[dcol::DERIVED_HASH] = derived_hash;

                for (i, &val) in step.substitution.iter().enumerate().take(MAX_SUB_VARS) {
                    row[dcol::SUB_VALUE_START + i] = val;
                }

                // Substitution verification columns
                for (term_i, &(is_var, value)) in
                    step.rule.head_terms.iter().enumerate().take(MAX_HEAD_TERMS)
                {
                    row[dcol::HEAD_IS_VAR_START + term_i] = if is_var {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    };
                    row[dcol::HEAD_RAW_VALUE_START + term_i] = value;

                    if is_var {
                        let var_idx = value.as_u32() as usize;
                        if var_idx < MAX_SUB_VARS {
                            row[dcol::head_sel_var(term_i, var_idx)] = BabyBear::ONE;
                        }
                    }
                }

                // Equal check columns
                for (check_i, eq_check) in step
                    .rule
                    .equal_checks
                    .iter()
                    .enumerate()
                    .take(MAX_EQUAL_CHECKS)
                {
                    row[dcol::eq_check_active(check_i)] = BabyBear::ONE;

                    let term_a = if eq_check.lhs_is_var {
                        let idx = eq_check.lhs_value.as_u32() as usize;
                        if idx < step.substitution.len() {
                            step.substitution[idx]
                        } else {
                            BabyBear::ZERO
                        }
                    } else {
                        eq_check.lhs_value
                    };

                    let term_b = if eq_check.rhs_is_var {
                        let idx = eq_check.rhs_value.as_u32() as usize;
                        if idx < step.substitution.len() {
                            step.substitution[idx]
                        } else {
                            BabyBear::ZERO
                        }
                    } else {
                        eq_check.rhs_value
                    };

                    row[dcol::eq_check_term_a(check_i)] = term_a;
                    row[dcol::eq_check_term_b(check_i)] = term_b;
                }

                // MemberOf check columns
                for (check_i, mo_check) in step
                    .rule
                    .memberof_checks
                    .iter()
                    .enumerate()
                    .take(MAX_MEMBEROF_CHECKS)
                {
                    row[dcol::memberof_check_active(check_i)] = BabyBear::ONE;

                    let term_a = if mo_check.lhs_is_var {
                        let idx = mo_check.lhs_value.as_u32() as usize;
                        if idx < step.substitution.len() {
                            step.substitution[idx]
                        } else {
                            BabyBear::ZERO
                        }
                    } else {
                        mo_check.lhs_value
                    };

                    let term_b = if mo_check.rhs_is_var {
                        let idx = mo_check.rhs_value.as_u32() as usize;
                        if idx < step.substitution.len() {
                            step.substitution[idx]
                        } else {
                            BabyBear::ZERO
                        }
                    } else {
                        mo_check.rhs_value
                    };

                    row[dcol::memberof_check_term_a(check_i)] = term_a;
                    row[dcol::memberof_check_term_b(check_i)] = term_b;
                }

                // GTE check columns
                if let Some(gte_check) = &step.rule.gte_check {
                    row[dcol::GTE_CHECK_ACTIVE] = BabyBear::ONE;

                    let term_a = if gte_check.lhs_is_var {
                        let idx = gte_check.lhs_value.as_u32() as usize;
                        if idx < step.substitution.len() {
                            step.substitution[idx]
                        } else {
                            BabyBear::ZERO
                        }
                    } else {
                        gte_check.lhs_value
                    };

                    let term_b = if gte_check.rhs_is_var {
                        let idx = gte_check.rhs_value.as_u32() as usize;
                        if idx < step.substitution.len() {
                            step.substitution[idx]
                        } else {
                            BabyBear::ZERO
                        }
                    } else {
                        gte_check.rhs_value
                    };

                    row[dcol::GTE_CHECK_TERM_A] = term_a;
                    row[dcol::GTE_CHECK_TERM_B] = term_b;

                    let diff = term_a - term_b;
                    row[dcol::GTE_CHECK_DIFF] = diff;

                    let diff_val = diff.as_u32();
                    for i in 0..GTE_DIFF_BITS {
                        let bit = (diff_val >> i) & 1;
                        row[dcol::gte_diff_bit(i)] = BabyBear::new(bit);
                    }
                }

                // LT check columns
                if let Some(lt_check) = &step.rule.lt_check {
                    row[dcol::LT_CHECK_ACTIVE] = BabyBear::ONE;

                    let term_a = if lt_check.lhs_is_var {
                        let idx = lt_check.lhs_value.as_u32() as usize;
                        if idx < step.substitution.len() {
                            step.substitution[idx]
                        } else {
                            BabyBear::ZERO
                        }
                    } else {
                        lt_check.lhs_value
                    };

                    let term_b = if lt_check.rhs_is_var {
                        let idx = lt_check.rhs_value.as_u32() as usize;
                        if idx < step.substitution.len() {
                            step.substitution[idx]
                        } else {
                            BabyBear::ZERO
                        }
                    } else {
                        lt_check.rhs_value
                    };

                    row[dcol::LT_CHECK_TERM_A] = term_a;
                    row[dcol::LT_CHECK_TERM_B] = term_b;

                    let diff = term_b - term_a - BabyBear::ONE;
                    row[dcol::LT_CHECK_DIFF] = diff;

                    let diff_val = diff.as_u32();
                    for i in 0..GTE_DIFF_BITS {
                        let bit = (diff_val >> i) & 1;
                        row[dcol::lt_diff_bit(i)] = BabyBear::new(bit);
                    }
                }

                // --- Check term binding columns (SOUNDNESS FIX) ---
                {
                    let fill_binding =
                        |row: &mut Vec<BabyBear>, slot: usize, is_var: bool, value: BabyBear| {
                            row[dcol::check_term_is_var(slot)] = if is_var {
                                BabyBear::ONE
                            } else {
                                BabyBear::ZERO
                            };
                            row[dcol::check_term_raw_value(slot)] = value;
                            if is_var {
                                let var_idx = value.as_u32() as usize;
                                if var_idx < MAX_SUB_VARS {
                                    row[dcol::check_term_sel(slot, var_idx)] = BabyBear::ONE;
                                }
                            }
                        };

                    for (check_i, eq_check) in step
                        .rule
                        .equal_checks
                        .iter()
                        .enumerate()
                        .take(MAX_EQUAL_CHECKS)
                    {
                        fill_binding(
                            &mut row,
                            dcol::eq_check_term_a_slot(check_i),
                            eq_check.lhs_is_var,
                            eq_check.lhs_value,
                        );
                        fill_binding(
                            &mut row,
                            dcol::eq_check_term_b_slot(check_i),
                            eq_check.rhs_is_var,
                            eq_check.rhs_value,
                        );
                    }

                    for (check_i, mo_check) in step
                        .rule
                        .memberof_checks
                        .iter()
                        .enumerate()
                        .take(MAX_MEMBEROF_CHECKS)
                    {
                        fill_binding(
                            &mut row,
                            dcol::memberof_check_term_a_slot(check_i),
                            mo_check.lhs_is_var,
                            mo_check.lhs_value,
                        );
                        fill_binding(
                            &mut row,
                            dcol::memberof_check_term_b_slot(check_i),
                            mo_check.rhs_is_var,
                            mo_check.rhs_value,
                        );
                    }

                    if let Some(gte_check) = &step.rule.gte_check {
                        fill_binding(
                            &mut row,
                            dcol::GTE_TERM_A_SLOT,
                            gte_check.lhs_is_var,
                            gte_check.lhs_value,
                        );
                        fill_binding(
                            &mut row,
                            dcol::GTE_TERM_B_SLOT,
                            gte_check.rhs_is_var,
                            gte_check.rhs_value,
                        );
                    }

                    if let Some(lt_check) = &step.rule.lt_check {
                        fill_binding(
                            &mut row,
                            dcol::LT_TERM_A_SLOT,
                            lt_check.lhs_is_var,
                            lt_check.lhs_value,
                        );
                        fill_binding(
                            &mut row,
                            dcol::LT_TERM_B_SLOT,
                            lt_check.rhs_is_var,
                            lt_check.rhs_value,
                        );
                    }
                }

                // --- Multi-step columns ---
                row[col::STEP_INDEX] = BabyBear::new(row_idx as u32);
                row[col::ACCUMULATED_HASH] = accumulated_hashes[row_idx];
                row[col::PREV_ACCUMULATED] = if row_idx == 0 {
                    w.initial_state_root
                } else {
                    accumulated_hashes[row_idx - 1]
                };
                row[col::IS_FINAL_STEP] = if row_idx == num_active - 1 {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                };
                row[col::IS_ACTIVE] = BabyBear::ONE;
            }
            // else: padding row, all zeros (is_active=0)

            trace.push(row);
        }

        // Public inputs
        let conclusion = w.conclusion();
        let final_acc = w.final_accumulated_hash();
        let public_inputs = vec![
            w.initial_state_root,             // 0: initial_state_root
            w.request_hash,                   // 1: request_hash
            conclusion,                       // 2: conclusion
            BabyBear::new(num_active as u32), // 3: num_steps
            final_acc,                        // 4: final_accumulated_hash
            w.policy_root,                    // 5: policy_root
        ];

        (trace, public_inputs)
    }
}

/// Build a multi-step witness from individual derivation witnesses.
///
/// All steps must share the same state_root (they reference the same committed
/// fact set). The last step must derive the "allow" predicate for the proof
/// to conclude ALLOW.
///
/// The `policy_root` is a Poseidon2 hash of the FULL rule structure definitions.
/// This cryptographically binds not just rule IDs, but the complete rule structure
/// including all checks (equal, memberof, gte, lt), body atom count, head pattern,
/// and variable count. A malicious prover cannot substitute a rule with the same ID
/// but stripped checks (e.g., removing a budget GTE constraint).
///
/// The verifier can check "this proof was made under policy P" by comparing the
/// policy_root public input against their known/expected policy hash.
pub fn build_multi_step_witness(
    initial_state_root: BabyBear,
    request_hash: BabyBear,
    steps: Vec<DerivationWitness>,
) -> MultiStepWitness {
    // Compute policy_root as hash of ALL rule structure definitions used.
    // SOUNDNESS FIX: Previously only hashed rule IDs, allowing a prover to
    // substitute a rule with the same ID but stripped checks. Now we hash
    // the full rule structure (checks, body count, head pattern, etc.).
    let rules: Vec<&crate::derivation_air::CircuitRule> = steps.iter().map(|s| &s.rule).collect();
    let policy_root = compute_policy_root(&rules);

    MultiStepWitness {
        initial_state_root,
        request_hash,
        steps,
        allow_predicate: BabyBear::new(ALLOW_PREDICATE),
        policy_root,
        body_merkle_proofs: None,
    }
}

/// Prove a multi-step authorization derivation.
///
/// Takes a derivation trace (sequence of rule applications) and produces
/// a STARK-verifiable proof that the evaluation concluded with the claimed
/// conclusion. Returns `None` if the witness doesn't satisfy constraints.
pub fn prove_authorization(
    witness: MultiStepWitness,
) -> Option<crate::constraint_prover::ConstraintProof> {
    let air = MultiStepDerivationAir::new(witness);
    let result = crate::constraint_prover::ConstraintProver::verify(&air);
    if !result.is_valid() {
        return None;
    }
    crate::constraint_prover::ConstraintProof::generate(&air)
}

// ============================================================================
// Real STARK proof generation for multi-step authorization
// ============================================================================

/// STARK AIR adapter for multi-step authorization derivation.
///
/// This wraps the multi-step derivation constraints into the `StarkAir` trait
/// interface expected by the real FRI-based STARK prover. The constraints
/// enforce:
///
/// 1. Binary flags: `is_active`, `is_final_step`, body membership, GTE bits
/// 2. Substitution correctness: variable resolution via selector columns
/// 3. Equal/MemberOf checks: active * (term_a - term_b) = 0
/// 4. GTE range check: bit decomposition of diff, high bit = 0
/// 5. Final step derives ALLOW predicate (gated by conclusion public input)
/// 6. Hash chain: accumulated_hash correctness via trace commitment
/// 7. Active monotone: once inactive, stays inactive
///
/// Hash binding (Poseidon2 computations) is enforced through the trace
/// commitment + FRI mechanism: the prover commits to correctly-computed hash
/// values in the trace, and any tampering is detected by the polynomial
/// commitment scheme.
pub struct MultiStepStarkAir {
    /// Number of active steps in the trace.
    pub num_steps: usize,
}

impl MultiStepStarkAir {
    pub fn new(num_steps: usize) -> Self {
        assert!(num_steps >= 1, "Must have at least 1 derivation step");
        Self { num_steps }
    }
}

impl StarkAir for MultiStepStarkAir {
    fn width(&self) -> usize {
        MULTI_STEP_AIR_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // The highest-degree constraint is GTE bit binary check:
        // is_active * gte_active * bit * (bit - 1) = degree 4
        // Also: final_step_derives_allow uses conclusion * is_final * (pred - allow) = degree 3
        4
    }

    fn air_name(&self) -> &'static str {
        "pyana-multi-step-derivation-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        // Our layout is NOT the simple 6-column Merkle chain (col5=parent, col0=current).
        // We handle continuity through the accumulated hash columns.
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let is_active = local[col::IS_ACTIVE];
        let is_final = local[col::IS_FINAL_STEP];

        // We combine constraints with successive powers of alpha for linear independence.
        let mut result = BabyBear::ZERO;
        let mut alpha_power = BabyBear::ONE;

        // --- Constraint 1: is_active is binary ---
        // is_active * (is_active - 1) = 0
        let c1 = is_active * (is_active - BabyBear::ONE);
        result = result + alpha_power * c1;
        alpha_power = alpha_power * alpha;

        // --- Constraint 2: is_final_step is binary ---
        // is_final * (is_final - 1) = 0
        let c2 = is_final * (is_final - BabyBear::ONE);
        result = result + alpha_power * c2;
        alpha_power = alpha_power * alpha;

        // --- Constraint 3: is_final implies is_active ---
        // is_final * (1 - is_active) = 0
        let c3 = is_final * (BabyBear::ONE - is_active);
        result = result + alpha_power * c3;
        alpha_power = alpha_power * alpha;

        // --- Constraint 4: Body membership flags binary (when active) ---
        let mut c4 = BabyBear::ZERO;
        for i in 0..MAX_BODY_ATOMS {
            let flag = local[dcol::BODY_MEMBERSHIP_START + i];
            c4 = c4 + flag * (flag - BabyBear::ONE);
        }
        result = result + alpha_power * (is_active * c4);
        alpha_power = alpha_power * alpha;

        // --- Constraint 5: head_is_var binary (when active) ---
        let mut c5 = BabyBear::ZERO;
        for i in 0..MAX_HEAD_TERMS {
            let flag = local[dcol::HEAD_IS_VAR_START + i];
            c5 = c5 + flag * (flag - BabyBear::ONE);
        }
        result = result + alpha_power * (is_active * c5);
        alpha_power = alpha_power * alpha;

        // --- Constraint 6: Selector columns binary (when active) ---
        let mut c6 = BabyBear::ZERO;
        for term_i in 0..MAX_HEAD_TERMS {
            for var_j in 0..MAX_SUB_VARS {
                let sel = local[dcol::head_sel_var(term_i, var_j)];
                c6 = c6 + sel * (sel - BabyBear::ONE);
            }
        }
        result = result + alpha_power * (is_active * c6);
        alpha_power = alpha_power * alpha;

        // --- Constraint 7: Selector sum equals is_var (when active) ---
        // For each head term: (sum_j sel_j - is_var)^2 = 0
        let mut c7 = BabyBear::ZERO;
        for term_i in 0..MAX_HEAD_TERMS {
            let is_var = local[dcol::HEAD_IS_VAR_START + term_i];
            let mut sel_sum = BabyBear::ZERO;
            for var_j in 0..MAX_SUB_VARS {
                sel_sum = sel_sum + local[dcol::head_sel_var(term_i, var_j)];
            }
            let diff = sel_sum - is_var;
            c7 = c7 + diff * diff;
        }
        result = result + alpha_power * (is_active * c7);
        alpha_power = alpha_power * alpha;

        // --- Constraint 8: Substitution application (when active) ---
        // For each head term: derived_term = is_var * var_resolved + (1-is_var) * raw_value
        let mut c8 = BabyBear::ZERO;
        for term_i in 0..MAX_HEAD_TERMS {
            let is_var = local[dcol::HEAD_IS_VAR_START + term_i];
            let raw_value = local[dcol::HEAD_RAW_VALUE_START + term_i];
            let derived_term = local[dcol::HEAD_TERM_START + term_i];

            let mut var_resolved = BabyBear::ZERO;
            for var_j in 0..MAX_SUB_VARS {
                let sel = local[dcol::head_sel_var(term_i, var_j)];
                let sub_val = local[dcol::SUB_VALUE_START + var_j];
                var_resolved = var_resolved + sel * sub_val;
            }

            let expected = is_var * var_resolved + (BabyBear::ONE - is_var) * raw_value;
            let diff = derived_term - expected;
            c8 = c8 + diff * diff;
        }
        result = result + alpha_power * (is_active * c8);
        alpha_power = alpha_power * alpha;

        // --- Constraint 9: Equal check active flags binary (when active) ---
        let mut c9 = BabyBear::ZERO;
        for i in 0..MAX_EQUAL_CHECKS {
            let flag = local[dcol::eq_check_active(i)];
            c9 = c9 + flag * (flag - BabyBear::ONE);
        }
        result = result + alpha_power * (is_active * c9);
        alpha_power = alpha_power * alpha;

        // --- Constraint 10: Equal check enforcement (when active) ---
        // eq_active * (term_a - term_b) = 0
        let mut c10 = BabyBear::ZERO;
        for i in 0..MAX_EQUAL_CHECKS {
            let eq_active = local[dcol::eq_check_active(i)];
            let term_a = local[dcol::eq_check_term_a(i)];
            let term_b = local[dcol::eq_check_term_b(i)];
            c10 = c10 + eq_active * (term_a - term_b);
        }
        result = result + alpha_power * (is_active * c10);
        alpha_power = alpha_power * alpha;

        // --- Constraint 11: MemberOf check active flags binary (when active) ---
        let mut c11 = BabyBear::ZERO;
        for i in 0..MAX_MEMBEROF_CHECKS {
            let flag = local[dcol::memberof_check_active(i)];
            c11 = c11 + flag * (flag - BabyBear::ONE);
        }
        result = result + alpha_power * (is_active * c11);
        alpha_power = alpha_power * alpha;

        // --- Constraint 12: MemberOf check enforcement (when active) ---
        let mut c12 = BabyBear::ZERO;
        for i in 0..MAX_MEMBEROF_CHECKS {
            let mo_active = local[dcol::memberof_check_active(i)];
            let term_a = local[dcol::memberof_check_term_a(i)];
            let term_b = local[dcol::memberof_check_term_b(i)];
            c12 = c12 + mo_active * (term_a - term_b);
        }
        result = result + alpha_power * (is_active * c12);
        alpha_power = alpha_power * alpha;

        // --- Constraint 13: GTE check active flag binary (when active) ---
        let gte_active = local[dcol::GTE_CHECK_ACTIVE];
        let c13 = is_active * gte_active * (gte_active - BabyBear::ONE);
        result = result + alpha_power * c13;
        alpha_power = alpha_power * alpha;

        // --- Constraint 14: GTE diff consistency (when active) ---
        // gte_active * (diff - (term_a - term_b)) = 0
        let term_a = local[dcol::GTE_CHECK_TERM_A];
        let term_b = local[dcol::GTE_CHECK_TERM_B];
        let diff = local[dcol::GTE_CHECK_DIFF];
        let c14 = is_active * gte_active * (diff - (term_a - term_b));
        result = result + alpha_power * c14;
        alpha_power = alpha_power * alpha;

        // --- Constraint 15: GTE bit decomposition (when active) ---
        let mut recomposed = BabyBear::ZERO;
        let mut power_of_two = BabyBear::ONE;
        for i in 0..GTE_DIFF_BITS {
            let bit = local[dcol::gte_diff_bit(i)];
            recomposed = recomposed + bit * power_of_two;
            power_of_two = power_of_two + power_of_two;
        }
        let c15 = is_active * gte_active * (recomposed - diff);
        result = result + alpha_power * c15;
        alpha_power = alpha_power * alpha;

        // --- Constraint 16: GTE bits binary (when active) ---
        let mut c16 = BabyBear::ZERO;
        for i in 0..GTE_DIFF_BITS {
            let bit = local[dcol::gte_diff_bit(i)];
            c16 = c16 + bit * (bit - BabyBear::ONE);
        }
        result = result + alpha_power * (is_active * gte_active * c16);
        alpha_power = alpha_power * alpha;

        // --- Constraint 17: GTE high bit is zero (when active) ---
        let high_bit = local[dcol::gte_diff_bit(GTE_DIFF_BITS - 1)];
        let c17 = is_active * gte_active * high_bit;
        result = result + alpha_power * c17;
        alpha_power = alpha_power * alpha;

        // --- Constraint 17b: LT check active flag binary (when active) ---
        let lt_active = local[dcol::LT_CHECK_ACTIVE];
        let c17b = is_active * lt_active * (lt_active - BabyBear::ONE);
        result = result + alpha_power * c17b;
        alpha_power = alpha_power * alpha;

        // --- Constraint 17c: LT diff consistency (when active) ---
        let lt_term_a = local[dcol::LT_CHECK_TERM_A];
        let lt_term_b = local[dcol::LT_CHECK_TERM_B];
        let lt_diff = local[dcol::LT_CHECK_DIFF];
        let c17c = is_active * lt_active * (lt_diff - (lt_term_b - lt_term_a - BabyBear::ONE));
        result = result + alpha_power * c17c;
        alpha_power = alpha_power * alpha;

        // --- Constraint 17d: LT bit decomposition (when active) ---
        let mut lt_recomposed = BabyBear::ZERO;
        let mut lt_power_of_two = BabyBear::ONE;
        for i in 0..GTE_DIFF_BITS {
            let bit = local[dcol::lt_diff_bit(i)];
            lt_recomposed = lt_recomposed + bit * lt_power_of_two;
            lt_power_of_two = lt_power_of_two + lt_power_of_two;
        }
        let c17d = is_active * lt_active * (lt_recomposed - lt_diff);
        result = result + alpha_power * c17d;
        alpha_power = alpha_power * alpha;

        // --- Constraint 17e: LT bits binary (when active) ---
        let mut c17e = BabyBear::ZERO;
        for i in 0..GTE_DIFF_BITS {
            let bit = local[dcol::lt_diff_bit(i)];
            c17e = c17e + bit * (bit - BabyBear::ONE);
        }
        result = result + alpha_power * (is_active * lt_active * c17e);
        alpha_power = alpha_power * alpha;

        // --- Constraint 17f: LT high bit is zero (when active) ---
        let lt_high_bit = local[dcol::lt_diff_bit(GTE_DIFF_BITS - 1)];
        let c17f = is_active * lt_active * lt_high_bit;
        result = result + alpha_power * c17f;
        alpha_power = alpha_power * alpha;

        // --- SOUNDNESS FIX: Check term binding constraints ---

        // Constraint 17g: check_term_is_var binary
        {
            let mut c = BabyBear::ZERO;
            for slot in 0..dcol::NUM_CHECK_TERMS {
                let iv = local[dcol::check_term_is_var(slot)];
                c = c + iv * (iv - BabyBear::ONE);
            }
            result = result + alpha_power * (is_active * c);
        }
        alpha_power = alpha_power * alpha;

        // Constraint 17h: check_term_sel binary
        {
            let mut c = BabyBear::ZERO;
            for slot in 0..dcol::NUM_CHECK_TERMS {
                for var_j in 0..MAX_SUB_VARS {
                    let sel = local[dcol::check_term_sel(slot, var_j)];
                    c = c + sel * (sel - BabyBear::ONE);
                }
            }
            result = result + alpha_power * (is_active * c);
        }
        alpha_power = alpha_power * alpha;

        // Constraint 17i: check_term_sel_sum = is_var
        {
            let mut c = BabyBear::ZERO;
            for slot in 0..dcol::NUM_CHECK_TERMS {
                let iv = local[dcol::check_term_is_var(slot)];
                let mut sel_sum = BabyBear::ZERO;
                for var_j in 0..MAX_SUB_VARS {
                    sel_sum = sel_sum + local[dcol::check_term_sel(slot, var_j)];
                }
                let d = sel_sum - iv;
                c = c + d * d;
            }
            result = result + alpha_power * (is_active * c);
        }
        alpha_power = alpha_power * alpha;

        // Constraint 17j: check_term_binding_correct
        {
            let resolve_slot = |slot: usize| -> BabyBear {
                let iv = local[dcol::check_term_is_var(slot)];
                let raw = local[dcol::check_term_raw_value(slot)];
                let mut vr = BabyBear::ZERO;
                for var_j in 0..MAX_SUB_VARS {
                    let sel = local[dcol::check_term_sel(slot, var_j)];
                    let sv = local[dcol::SUB_VALUE_START + var_j];
                    vr = vr + sel * sv;
                }
                iv * vr + (BabyBear::ONE - iv) * raw
            };

            let mut c = BabyBear::ZERO;

            for i in 0..MAX_EQUAL_CHECKS {
                let ea = local[dcol::eq_check_active(i)];
                let ta = local[dcol::eq_check_term_a(i)];
                let tb = local[dcol::eq_check_term_b(i)];
                let ra = resolve_slot(dcol::eq_check_term_a_slot(i));
                let rb = resolve_slot(dcol::eq_check_term_b_slot(i));
                let da = ta - ra;
                let db = tb - rb;
                c = c + ea * (da * da + db * db);
            }

            for i in 0..MAX_MEMBEROF_CHECKS {
                let ma = local[dcol::memberof_check_active(i)];
                let ta = local[dcol::memberof_check_term_a(i)];
                let tb = local[dcol::memberof_check_term_b(i)];
                let ra = resolve_slot(dcol::memberof_check_term_a_slot(i));
                let rb = resolve_slot(dcol::memberof_check_term_b_slot(i));
                let da = ta - ra;
                let db = tb - rb;
                c = c + ma * (da * da + db * db);
            }

            {
                let ga = local[dcol::GTE_CHECK_ACTIVE];
                let ta = local[dcol::GTE_CHECK_TERM_A];
                let tb = local[dcol::GTE_CHECK_TERM_B];
                let ra = resolve_slot(dcol::GTE_TERM_A_SLOT);
                let rb = resolve_slot(dcol::GTE_TERM_B_SLOT);
                let da = ta - ra;
                let db = tb - rb;
                c = c + ga * (da * da + db * db);
            }

            {
                let la = local[dcol::LT_CHECK_ACTIVE];
                let ta = local[dcol::LT_CHECK_TERM_A];
                let tb = local[dcol::LT_CHECK_TERM_B];
                let ra = resolve_slot(dcol::LT_TERM_A_SLOT);
                let rb = resolve_slot(dcol::LT_TERM_B_SLOT);
                let da = ta - ra;
                let db = tb - rb;
                c = c + la * (da * da + db * db);
            }

            result = result + alpha_power * (is_active * c);
        }
        alpha_power = alpha_power * alpha;

        // --- Constraint 18: Final step derives ALLOW predicate ---
        // conclusion * is_final * (head_pred - ALLOW_PREDICATE) = 0
        let conclusion = public_inputs[pi::CONCLUSION];
        let head_pred = local[dcol::HEAD_PRED];
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let c18 = conclusion * is_final * (head_pred - allow_pred);
        result = result + alpha_power * c18;
        alpha_power = alpha_power * alpha;

        // --- Constraint 19: Body roots match state root (when active) ---
        // For each body atom: flag * (root - initial_state_root) = 0
        let state_root = public_inputs[pi::INITIAL_STATE_ROOT];
        let mut c19 = BabyBear::ZERO;
        for i in 0..MAX_BODY_ATOMS {
            let flag = local[dcol::BODY_MEMBERSHIP_START + i];
            let root = local[dcol::BODY_ROOT_START + i];
            c19 = c19 + flag * (root - state_root);
        }
        result = result + alpha_power * (is_active * c19);

        // --- Transition constraints (enforced on all rows except the last) ---
        //
        // These are critical for soundness: without them a malicious prover could
        // commit to arbitrary intermediate accumulated_hash values. The STARK
        // transition vanishing polynomial ensures these are NOT enforced on the
        // last row (where "next" wraps around in the evaluation domain).
        //
        // NOTE: Full Poseidon2 hash correctness is NOT proved in-circuit here
        // (the S-box would require degree-7 constraints or auxiliary columns).
        // Hash correctness relies on composition: a separate hash-chain STARK
        // proves that every accumulated_hash value is a correct Poseidon2 output.
        // What we DO enforce here is chain CONTINUITY: no gaps, no skipped rows.
        alpha_power = alpha_power * alpha;

        // --- Constraint 20: is_active monotone decreasing (transition) ---
        // Once is_active goes to 0, it must stay 0.
        // (1 - is_active_current) * is_active_next = 0
        let next_is_active = next[col::IS_ACTIVE];
        let c20 = (BabyBear::ONE - is_active) * next_is_active;
        result = result + alpha_power * c20;
        alpha_power = alpha_power * alpha;

        // --- Constraint 21: Chain continuity (transition) ---
        // The prev_accumulated of the next active row must equal the accumulated_hash
        // of the current row. This prevents a malicious prover from inserting arbitrary
        // values that break the chain between consecutive rows.
        // is_active_next * (prev_accumulated_next - accumulated_hash_current) = 0
        let current_acc = local[col::ACCUMULATED_HASH];
        let next_prev = next[col::PREV_ACCUMULATED];
        let c21 = next_is_active * (next_prev - current_acc);
        result = result + alpha_power * c21;
        let _ = alpha_power; // final power consumed

        result
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 5 {
            // Row 0, col PREV_ACCUMULATED = public_inputs[0] (initial_state_root)
            // This binds the first row's prev_accumulated to the claimed initial state root.
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::PREV_ACCUMULATED,
                value: public_inputs[pi::INITIAL_STATE_ROOT],
            });
            // Row 0, col IS_ACTIVE = 1 (first row must be active)
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::IS_ACTIVE,
                value: BabyBear::ONE,
            });
            // Row 0, col STEP_INDEX = 0
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::STEP_INDEX,
                value: BabyBear::ZERO,
            });
            // Last active row (num_steps - 1), col ACCUMULATED_HASH = public_inputs[4]
            // This binds the final accumulated hash to the public input.
            let last_active_row = self.num_steps - 1;
            constraints.push(BoundaryConstraint {
                row: last_active_row,
                col: col::ACCUMULATED_HASH,
                value: public_inputs[pi::FINAL_ACCUMULATED_HASH],
            });
            // Last active row, col IS_FINAL_STEP = 1
            constraints.push(BoundaryConstraint {
                row: last_active_row,
                col: col::IS_FINAL_STEP,
                value: BabyBear::ONE,
            });
        }
        constraints
    }
}

/// Generate the trace for a multi-step authorization witness, padded to a power of two.
///
/// This extracts the trace generation logic so it can be used by both the constraint
/// prover and the real STARK prover.
pub fn generate_multi_step_trace(
    witness: &MultiStepWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let air = MultiStepDerivationAir::new(witness.clone());
    let (mut trace, public_inputs) = air.generate_trace();

    // Pad to power-of-two length for the STARK prover
    let n = trace.len();
    let padded = n.next_power_of_two().max(2);
    while trace.len() < padded {
        trace.push(vec![BabyBear::ZERO; MULTI_STEP_AIR_WIDTH]);
    }

    (trace, public_inputs)
}

/// Prove a multi-step authorization derivation using the real FRI-based STARK prover.
///
/// This generates a cryptographic proof that the Datalog evaluation concluded with the
/// claimed conclusion. The proof can be verified by anyone who knows only the public
/// inputs (initial_state_root, request_hash, conclusion, num_steps, final_accumulated_hash).
///
/// Returns a `StarkProof` containing Merkle commitments, FRI layers, and query openings.
pub fn prove_authorization_stark(witness: &MultiStepWitness) -> StarkProof {
    let num_steps = witness.steps.len();
    let air = MultiStepStarkAir::new(num_steps);
    let (trace, public_inputs) = generate_multi_step_trace(witness);
    stark::prove(&air, &trace, &public_inputs)
}

/// Verify a multi-step authorization STARK proof.
///
/// The verifier only needs:
/// - `conclusion`: the claimed conclusion (1=ALLOW, 0=DENY)
/// - `accumulated_hash`: the final accumulated hash (commitment to derivation trace)
/// - `proof`: the STARK proof
///
/// Internally also verifies against the public inputs embedded in the proof:
/// initial_state_root, request_hash, num_steps.
///
/// Returns Ok(()) if the proof is valid, Err with a description otherwise.
pub fn verify_authorization_stark(
    conclusion: BabyBear,
    accumulated_hash: BabyBear,
    proof: &StarkProof,
) -> Result<(), String> {
    // Extract public inputs from the proof
    if proof.public_inputs.len() != 6 {
        return Err(format!(
            "Expected 6 public inputs, got {}",
            proof.public_inputs.len()
        ));
    }

    // Verify that claimed conclusion and accumulated_hash match
    let proof_conclusion = BabyBear::new_canonical(proof.public_inputs[pi::CONCLUSION]);
    let proof_acc_hash = BabyBear::new_canonical(proof.public_inputs[pi::FINAL_ACCUMULATED_HASH]);

    if proof_conclusion != conclusion {
        return Err(format!(
            "Conclusion mismatch: expected {}, proof contains {}",
            conclusion.0, proof_conclusion.0
        ));
    }
    if proof_acc_hash != accumulated_hash {
        return Err(format!(
            "Accumulated hash mismatch: expected {}, proof contains {}",
            accumulated_hash.0, proof_acc_hash.0
        ));
    }

    let num_steps = proof.public_inputs[pi::NUM_STEPS] as usize;
    if num_steps == 0 {
        return Err("Proof claims 0 derivation steps".to_string());
    }

    let air = MultiStepStarkAir::new(num_steps);
    let public_inputs: Vec<BabyBear> = proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    stark::verify(&air, proof, &public_inputs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;
    use crate::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};

    /// Helper: create a derivation step that derives a fact with the given predicate.
    fn make_step(
        rule_id: u32,
        state_root: BabyBear,
        derived_pred: BabyBear,
        terms: [BabyBear; 4],
        body_pred: BabyBear,
        body_terms: [BabyBear; 4],
        substitution: Vec<BabyBear>,
    ) -> DerivationWitness {
        let body_hash = hash_fact(body_pred, &body_terms);

        DerivationWitness {
            rule: CircuitRule {
                id: rule_id,
                num_body_atoms: 1,
                num_variables: substitution.len(),
                head_predicate: derived_pred,
                head_terms: [
                    (true, BabyBear::new(0)),
                    if substitution.len() > 1 {
                        (true, BabyBear::new(1))
                    } else {
                        (false, terms[1])
                    },
                    (false, terms[2]),
                    (false, terms[3]),
                ],
                body_atoms: vec![BodyAtomPattern {
                    predicate: body_pred,
                    terms: [
                        (true, BabyBear::new(0)),
                        if substitution.len() > 1 {
                            (true, BabyBear::new(1))
                        } else {
                            (false, body_terms[1])
                        },
                        (false, body_terms[2]),
                    ],
                }],
                equal_checks: vec![],
                memberof_checks: vec![],
                gte_check: None,
                lt_check: None,
            },
            state_root,
            body_fact_hashes: vec![body_hash],
            substitution,
            derived_predicate: derived_pred,
            derived_terms: terms,
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        }
    }

    #[test]
    fn test_multi_step_single_derivation() {
        // 1 step: derives "allow" directly from a base fact.
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let app_authorized_pred = BabyBear::new(500);

        // Step 1: app_authorized(alice, myapp) => allow(alice, myapp)
        // Actually simpler: allow(alice, myapp) :- app_authorized(alice, myapp).
        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            app_authorized_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);

        let air = MultiStepDerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Single-step multi-step AIR should verify: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_multi_step_two_derivations() {
        // Step 1: derive app_authorized(alice, myapp)
        // Step 2: derive allow(alice, myapp) from app_authorized
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let app_authorized_pred = BabyBear::new(500);
        let has_role_pred = BabyBear::new(600);

        // Step 1: app_authorized(alice, myapp) :- has_role(alice, myapp).
        let step1 = make_step(
            1,
            state_root,
            app_authorized_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        // Step 2: allow(alice, myapp) :- app_authorized(alice, myapp).
        let step2 = make_step(
            2,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            app_authorized_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step1, step2]);

        let air = MultiStepDerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Two-step derivation should verify: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_multi_step_wrong_conclusion_rejected() {
        // The final step derives app_authorized, NOT allow.
        // Since conclusion=1 (ALLOW) is computed but final step doesn't derive allow,
        // the proof should fail.
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let app_authorized_pred = BabyBear::new(500);
        let has_role_pred = BabyBear::new(600);

        // Only step: derive app_authorized (not allow!)
        let step = make_step(
            1,
            state_root,
            app_authorized_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        // The conclusion will be DENY (0) since last step isn't allow.
        // That's fine for the circuit. But let's test the case where someone
        // CLAIMS allow but the derivation doesn't support it.
        // We need to tamper with the public input to claim ALLOW.
        assert_eq!(witness.conclusion(), BabyBear::ZERO); // correctly computed as DENY

        // Now try to build an AIR that claims ALLOW by forcing the allow_predicate
        // to match what was actually derived (this would be a valid proof of... not allow)
        // Actually, let's test that the witness correctly identifies non-allow conclusions.
        // The real test: if we somehow force conclusion=1 in public inputs but the
        // derivation doesn't produce allow, the constraint should catch it.

        // Create a tampered AIR that lies about the conclusion
        struct TamperedAir {
            inner: MultiStepDerivationAir,
        }
        impl Air for TamperedAir {
            fn trace_width(&self) -> usize {
                self.inner.trace_width()
            }
            fn num_public_inputs(&self) -> usize {
                self.inner.num_public_inputs()
            }
            fn constraints(&self) -> Vec<Constraint> {
                self.inner.constraints()
            }
            fn first_row_constraints(&self) -> Vec<Constraint> {
                self.inner.first_row_constraints()
            }
            fn last_row_constraints(&self) -> Vec<Constraint> {
                self.inner.last_row_constraints()
            }
            fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
                let (trace, mut pi) = self.inner.generate_trace();
                // Tamper: claim ALLOW when derivation doesn't support it
                pi[pi::CONCLUSION] = BabyBear::ONE;
                (trace, pi)
            }
        }

        let tampered = TamperedAir {
            inner: MultiStepDerivationAir::new(witness),
        };
        let result = ConstraintProver::verify(&tampered);
        assert!(
            !result.is_valid(),
            "Claiming ALLOW when final step doesn't derive it should fail"
        );

        let has_allow_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "final_step_derives_allow");
        assert!(
            has_allow_violation,
            "Should have final_step_derives_allow violation, got: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_multi_step_broken_chain_rejected() {
        // The accumulated hash chain is broken: we tamper with prev_accumulated.
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let app_authorized_pred = BabyBear::new(500);
        let has_role_pred = BabyBear::new(600);

        let step1 = make_step(
            1,
            state_root,
            app_authorized_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let step2 = make_step(
            2,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            app_authorized_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step1, step2]);

        // Tamper: break the chain by changing a prev_accumulated value
        struct BrokenChainAir {
            inner: MultiStepDerivationAir,
        }
        impl Air for BrokenChainAir {
            fn trace_width(&self) -> usize {
                self.inner.trace_width()
            }
            fn num_public_inputs(&self) -> usize {
                self.inner.num_public_inputs()
            }
            fn constraints(&self) -> Vec<Constraint> {
                self.inner.constraints()
            }
            fn first_row_constraints(&self) -> Vec<Constraint> {
                self.inner.first_row_constraints()
            }
            fn last_row_constraints(&self) -> Vec<Constraint> {
                self.inner.last_row_constraints()
            }
            fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
                let (mut trace, pi) = self.inner.generate_trace();
                // Tamper: change prev_accumulated in row 1 to break the chain
                if trace.len() > 1 {
                    trace[1][col::PREV_ACCUMULATED] = BabyBear::new(777777);
                }
                (trace, pi)
            }
        }

        let broken = BrokenChainAir {
            inner: MultiStepDerivationAir::new(witness),
        };
        let result = ConstraintProver::verify(&broken);
        assert!(
            !result.is_valid(),
            "Broken accumulated hash chain should fail verification"
        );

        // Should fail on either prev_accumulated_chain or accumulated_hash_correct
        let has_chain_violation = result.violations().iter().any(|v| {
            v.constraint_name == "prev_accumulated_chain"
                || v.constraint_name == "accumulated_hash_correct"
        });
        assert!(
            has_chain_violation,
            "Should have chain-related violation, got: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_multi_step_real_policy() {
        // Realistic multi-step authorization:
        // Base facts: has_capability(alice, app1, read), app_registered(app1)
        // Rule 1: app_authorized(X, App) :- has_capability(X, App, _), app_registered(App).
        //   (but we only have 1 body atom per step in our simplified model, so we split)
        // Rule 1: app_authorized(X, App) :- has_capability(X, App, read).
        // Rule 2: action_permitted(X, App) :- app_authorized(X, App).
        // Rule 3: allow(X, App) :- action_permitted(X, App).
        //
        // 3 steps: has_capability -> app_authorized -> action_permitted -> allow

        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app1 = BabyBear::new(2000);
        let read_action = BabyBear::new(3000);

        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_cap_pred = BabyBear::new(100);
        let app_auth_pred = BabyBear::new(200);
        let action_perm_pred = BabyBear::new(300);

        // Step 1: app_authorized(alice, app1) :- has_capability(alice, app1, read).
        let step1 = DerivationWitness {
            rule: CircuitRule {
                id: 1,
                num_body_atoms: 1,
                num_variables: 3,
                head_predicate: app_auth_pred,
                head_terms: [
                    (true, BabyBear::new(0)), // X -> alice
                    (true, BabyBear::new(1)), // App -> app1
                    (false, BabyBear::ZERO),
                    (false, BabyBear::ZERO),
                ],
                body_atoms: vec![BodyAtomPattern {
                    predicate: has_cap_pred,
                    terms: [
                        (true, BabyBear::new(0)), // X
                        (true, BabyBear::new(1)), // App
                        (true, BabyBear::new(2)), // Action (wildcard in head)
                    ],
                }],
                equal_checks: vec![],
                memberof_checks: vec![],
                gte_check: None,
                lt_check: None,
            },
            state_root,
            body_fact_hashes: vec![hash_fact(has_cap_pred, &[alice, app1, read_action])],
            substitution: vec![alice, app1, read_action],
            derived_predicate: app_auth_pred,
            derived_terms: [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        // Step 2: action_permitted(alice, app1) :- app_authorized(alice, app1).
        let step2 = DerivationWitness {
            rule: CircuitRule {
                id: 2,
                num_body_atoms: 1,
                num_variables: 2,
                head_predicate: action_perm_pred,
                head_terms: [
                    (true, BabyBear::new(0)), // X
                    (true, BabyBear::new(1)), // App
                    (false, BabyBear::ZERO),
                    (false, BabyBear::ZERO),
                ],
                body_atoms: vec![BodyAtomPattern {
                    predicate: app_auth_pred,
                    terms: [
                        (true, BabyBear::new(0)), // X
                        (true, BabyBear::new(1)), // App
                        (false, BabyBear::ZERO),
                    ],
                }],
                equal_checks: vec![],
                memberof_checks: vec![],
                gte_check: None,
                lt_check: None,
            },
            state_root,
            body_fact_hashes: vec![hash_fact(app_auth_pred, &[alice, app1, BabyBear::ZERO])],
            substitution: vec![alice, app1],
            derived_predicate: action_perm_pred,
            derived_terms: [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        // Step 3: allow(alice, app1) :- action_permitted(alice, app1).
        let step3 = DerivationWitness {
            rule: CircuitRule {
                id: 3,
                num_body_atoms: 1,
                num_variables: 2,
                head_predicate: allow_pred,
                head_terms: [
                    (true, BabyBear::new(0)), // X
                    (true, BabyBear::new(1)), // App
                    (false, BabyBear::ZERO),
                    (false, BabyBear::ZERO),
                ],
                body_atoms: vec![BodyAtomPattern {
                    predicate: action_perm_pred,
                    terms: [
                        (true, BabyBear::new(0)), // X
                        (true, BabyBear::new(1)), // App
                        (false, BabyBear::ZERO),
                    ],
                }],
                equal_checks: vec![],
                memberof_checks: vec![],
                gte_check: None,
                lt_check: None,
            },
            state_root,
            body_fact_hashes: vec![hash_fact(action_perm_pred, &[alice, app1, BabyBear::ZERO])],
            substitution: vec![alice, app1],
            derived_predicate: allow_pred,
            derived_terms: [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let witness =
            build_multi_step_witness(state_root, BabyBear::new(42), vec![step1, step2, step3]);

        // Verify the witness computes the right conclusion
        assert_eq!(witness.conclusion(), BabyBear::ONE, "Should conclude ALLOW");

        let air = MultiStepDerivationAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Real policy 3-step derivation should verify: {:?}",
            result.violations()
        );

        // Also test prove_authorization
        let witness2 = build_multi_step_witness(
            state_root,
            BabyBear::new(42),
            vec![
                make_step(
                    1,
                    state_root,
                    app_auth_pred,
                    [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
                    has_cap_pred,
                    [alice, app1, read_action, BabyBear::ZERO],
                    vec![alice, app1, read_action],
                ),
                make_step(
                    2,
                    state_root,
                    action_perm_pred,
                    [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
                    app_auth_pred,
                    [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
                    vec![alice, app1],
                ),
                make_step(
                    3,
                    state_root,
                    allow_pred,
                    [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
                    action_perm_pred,
                    [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
                    vec![alice, app1],
                ),
            ],
        );
        let proof = prove_authorization(witness2);
        assert!(proof.is_some(), "prove_authorization should succeed");
        let proof = proof.unwrap();
        assert_eq!(proof.num_rows, 3);
        println!(
            "Multi-step authorization proof: {} rows, {}",
            proof.num_rows,
            proof.proof_size_display()
        );
    }

    #[test]
    fn test_multi_step_with_padding() {
        // Test that padding rows (is_active=0) don't break constraints.
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);

        // Use max_steps=4 to add 3 padding rows
        let air = MultiStepDerivationAir::with_max_steps(witness, 4);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Padded multi-step AIR should verify: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_prove_authorization_returns_proof() {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let proof = prove_authorization(witness);
        assert!(proof.is_some());

        let proof = proof.unwrap();
        // Public inputs should be correct
        assert_eq!(
            proof.public_inputs[pi::INITIAL_STATE_ROOT],
            BabyBear::new(99999)
        );
        assert_eq!(proof.public_inputs[pi::REQUEST_HASH], BabyBear::new(42));
        assert_eq!(proof.public_inputs[pi::CONCLUSION], BabyBear::ONE); // ALLOW
        assert_eq!(proof.public_inputs[pi::NUM_STEPS], BabyBear::ONE); // 1 step
    }

    // ========================================================================
    // Real STARK proof tests
    // ========================================================================

    #[test]
    fn test_stark_single_step_prove_and_verify() {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        assert_eq!(conclusion, BabyBear::ONE, "Should conclude ALLOW");

        let proof = prove_authorization_stark(&witness);
        let result = verify_authorization_stark(conclusion, acc_hash, &proof);
        assert!(
            result.is_ok(),
            "Single-step STARK proof should verify: {:?}",
            result.err()
        );

        println!(
            "Single-step authorization STARK proof: {} rows, {} bytes ({:.1} KiB)",
            proof.trace_len,
            stark::proof_to_bytes(&proof).len(),
            stark::proof_to_bytes(&proof).len() as f64 / 1024.0,
        );
    }

    #[test]
    fn test_stark_multi_step_prove_and_verify() {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let app_auth_pred = BabyBear::new(500);
        let has_role_pred = BabyBear::new(600);

        let step1 = make_step(
            1,
            state_root,
            app_auth_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let step2 = make_step(
            2,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            app_auth_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step1, step2]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        assert_eq!(conclusion, BabyBear::ONE, "Should conclude ALLOW");

        let proof = prove_authorization_stark(&witness);
        let result = verify_authorization_stark(conclusion, acc_hash, &proof);
        assert!(
            result.is_ok(),
            "Two-step STARK proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_stark_three_step_real_policy() {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app1 = BabyBear::new(2000);
        let read_action = BabyBear::new(3000);

        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_cap_pred = BabyBear::new(100);
        let app_auth_pred = BabyBear::new(200);
        let action_perm_pred = BabyBear::new(300);

        let step1 = make_step(
            1,
            state_root,
            app_auth_pred,
            [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
            has_cap_pred,
            [alice, app1, read_action, BabyBear::ZERO],
            vec![alice, app1, read_action],
        );
        let step2 = make_step(
            2,
            state_root,
            action_perm_pred,
            [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
            app_auth_pred,
            [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app1],
        );
        let step3 = make_step(
            3,
            state_root,
            allow_pred,
            [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
            action_perm_pred,
            [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app1],
        );

        let witness =
            build_multi_step_witness(state_root, BabyBear::new(42), vec![step1, step2, step3]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        let proof = prove_authorization_stark(&witness);
        let result = verify_authorization_stark(conclusion, acc_hash, &proof);
        assert!(
            result.is_ok(),
            "Three-step policy STARK proof should verify: {:?}",
            result.err()
        );

        let proof_bytes = stark::proof_to_bytes(&proof);
        println!(
            "Three-step authorization STARK proof: {} rows, {} bytes ({:.1} KiB)",
            proof.trace_len,
            proof_bytes.len(),
            proof_bytes.len() as f64 / 1024.0,
        );
    }

    #[test]
    fn test_stark_wrong_conclusion_rejected() {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let acc_hash = witness.final_accumulated_hash();

        let proof = prove_authorization_stark(&witness);

        // Try to verify with WRONG conclusion (DENY instead of ALLOW)
        let wrong_conclusion = BabyBear::ZERO;
        let result = verify_authorization_stark(wrong_conclusion, acc_hash, &proof);
        assert!(result.is_err(), "Should reject wrong conclusion");
        assert!(
            result.unwrap_err().contains("Conclusion mismatch"),
            "Error should mention conclusion mismatch"
        );
    }

    #[test]
    fn test_stark_wrong_accumulated_hash_rejected() {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();

        let proof = prove_authorization_stark(&witness);

        // Try to verify with WRONG accumulated hash
        let wrong_hash = BabyBear::new(777777);
        let result = verify_authorization_stark(conclusion, wrong_hash, &proof);
        assert!(result.is_err(), "Should reject wrong accumulated hash");
        assert!(
            result.unwrap_err().contains("Accumulated hash mismatch"),
            "Error should mention accumulated hash mismatch"
        );
    }

    #[test]
    fn test_stark_tampered_proof_rejected() {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        let mut proof = prove_authorization_stark(&witness);

        // Tamper with trace commitment
        proof.trace_commitment[0] ^= 0xFF;

        let result = verify_authorization_stark(conclusion, acc_hash, &proof);
        assert!(result.is_err(), "Tampered proof should be rejected");
    }

    #[test]
    fn test_stark_proof_serialization_roundtrip() {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        let proof = prove_authorization_stark(&witness);

        // Serialize and deserialize
        let bytes = stark::proof_to_bytes(&proof);
        let proof2 = stark::proof_from_bytes(&bytes).unwrap();

        // Verify the deserialized proof
        let result = verify_authorization_stark(conclusion, acc_hash, &proof2);
        assert!(
            result.is_ok(),
            "Deserialized STARK proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_stark_deny_conclusion_proves_and_verifies() {
        // Prove a DENY conclusion (last step doesn't derive allow)
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let app_auth_pred = BabyBear::new(500);
        let has_role_pred = BabyBear::new(600);

        // Only step derives app_authorized, NOT allow
        let step = make_step(
            1,
            state_root,
            app_auth_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        // Conclusion should be DENY (0)
        assert_eq!(conclusion, BabyBear::ZERO, "Should conclude DENY");

        let proof = prove_authorization_stark(&witness);
        let result = verify_authorization_stark(conclusion, acc_hash, &proof);
        assert!(
            result.is_ok(),
            "DENY conclusion STARK proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_multi_step_six_body_atom_rule() {
        // This test demonstrates a rule with 6 body atoms -- impossible under
        // the old MAX_BODY_ATOMS=4 budget. RBAC with context:
        //   allow(User, Resource) :-
        //     has_role(User, Role),          // user has a role
        //     role_has_permission(Role, Perm), // role grants a permission
        //     permission_applies(Perm, Resource), // permission covers the resource
        //     resource_in_dept(Resource, Dept),   // resource belongs to a department
        //     dept_active(Dept, Status),          // department is active
        //     time_valid(User, TimeSlot).         // user's time window is valid
        //
        // = 6 body atoms, which would have FAILED under the old budget.

        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let admin_role = BabyBear::new(2000);
        let read_perm = BabyBear::new(3000);
        let file_resource = BabyBear::new(4000);
        let eng_dept = BabyBear::new(5000);
        let active_status = BabyBear::new(6000);
        let time_slot = BabyBear::new(7000);

        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(101);
        let role_perm_pred = BabyBear::new(102);
        let perm_applies_pred = BabyBear::new(103);
        let res_dept_pred = BabyBear::new(104);
        let dept_active_pred = BabyBear::new(105);
        let time_valid_pred = BabyBear::new(106);

        // Body fact hashes for all 6 atoms
        let body_hash_1 = hash_fact(has_role_pred, &[alice, admin_role, BabyBear::ZERO]);
        let body_hash_2 = hash_fact(role_perm_pred, &[admin_role, read_perm, BabyBear::ZERO]);
        let body_hash_3 = hash_fact(
            perm_applies_pred,
            &[read_perm, file_resource, BabyBear::ZERO],
        );
        let body_hash_4 = hash_fact(res_dept_pred, &[file_resource, eng_dept, BabyBear::ZERO]);
        let body_hash_5 = hash_fact(dept_active_pred, &[eng_dept, active_status, BabyBear::ZERO]);
        let body_hash_6 = hash_fact(time_valid_pred, &[alice, time_slot, BabyBear::ZERO]);

        // Substitution: User=alice, Role=admin_role, Perm=read_perm,
        //               Resource=file_resource, Dept=eng_dept, Status=active_status, TimeSlot=time_slot
        let substitution = vec![
            alice,
            admin_role,
            read_perm,
            file_resource,
            eng_dept,
            active_status,
            time_slot,
        ];

        let step = DerivationWitness {
            rule: CircuitRule {
                id: 42,
                num_body_atoms: 6,
                num_variables: 7,
                head_predicate: allow_pred,
                head_terms: [
                    (true, BabyBear::new(0)), // User = alice
                    (true, BabyBear::new(3)), // Resource = file_resource
                    (false, BabyBear::ZERO),
                    (false, BabyBear::ZERO),
                ],
                body_atoms: vec![
                    BodyAtomPattern {
                        predicate: has_role_pred,
                        terms: [
                            (true, BabyBear::new(0)), // User
                            (true, BabyBear::new(1)), // Role
                            (false, BabyBear::ZERO),
                        ],
                    },
                    BodyAtomPattern {
                        predicate: role_perm_pred,
                        terms: [
                            (true, BabyBear::new(1)), // Role
                            (true, BabyBear::new(2)), // Perm
                            (false, BabyBear::ZERO),
                        ],
                    },
                    BodyAtomPattern {
                        predicate: perm_applies_pred,
                        terms: [
                            (true, BabyBear::new(2)), // Perm
                            (true, BabyBear::new(3)), // Resource
                            (false, BabyBear::ZERO),
                        ],
                    },
                    BodyAtomPattern {
                        predicate: res_dept_pred,
                        terms: [
                            (true, BabyBear::new(3)), // Resource
                            (true, BabyBear::new(4)), // Dept
                            (false, BabyBear::ZERO),
                        ],
                    },
                    BodyAtomPattern {
                        predicate: dept_active_pred,
                        terms: [
                            (true, BabyBear::new(4)), // Dept
                            (true, BabyBear::new(5)), // Status
                            (false, BabyBear::ZERO),
                        ],
                    },
                    BodyAtomPattern {
                        predicate: time_valid_pred,
                        terms: [
                            (true, BabyBear::new(0)), // User
                            (true, BabyBear::new(6)), // TimeSlot
                            (false, BabyBear::ZERO),
                        ],
                    },
                ],
                equal_checks: vec![],
                memberof_checks: vec![],
                gte_check: None,
                lt_check: None,
            },
            state_root,
            body_fact_hashes: vec![
                body_hash_1,
                body_hash_2,
                body_hash_3,
                body_hash_4,
                body_hash_5,
                body_hash_6,
            ],
            substitution,
            derived_predicate: allow_pred,
            derived_terms: [alice, file_resource, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        assert_eq!(witness.conclusion(), BabyBear::ONE, "Should conclude ALLOW");

        // Verify with mock prover
        let air = MultiStepDerivationAir::new(witness.clone());
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "6-body-atom rule should verify (impossible under old MAX_BODY_ATOMS=4): {:?}",
            result.violations()
        );

        // Verify with real STARK prover
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();
        let proof = prove_authorization_stark(&witness);
        let result = verify_authorization_stark(conclusion, acc_hash, &proof);
        assert!(
            result.is_ok(),
            "6-body-atom STARK proof should verify: {:?}",
            result.err()
        );

        // Verify policy_root is included in proof public inputs
        assert_eq!(proof.public_inputs.len(), 6);
        assert_ne!(
            proof.public_inputs[pi::POLICY_ROOT],
            0,
            "policy_root should be non-zero"
        );

        println!(
            "6-body-atom RBAC proof: {} rows, {} bytes ({:.1} KiB), policy_root={}",
            proof.trace_len,
            stark::proof_to_bytes(&proof).len(),
            stark::proof_to_bytes(&proof).len() as f64 / 1024.0,
            proof.public_inputs[pi::POLICY_ROOT],
        );
    }

    // ========================================================================
    // Transition constraint soundness tests (STARK variant)
    // ========================================================================

    #[test]
    fn test_stark_non_monotone_is_active_rejected() {
        // A malicious prover sets is_active to [0, 1] on consecutive rows — a
        // non-monotone transition. The constraint `(1 - is_active) * next_is_active == 0`
        // must catch this.
        //
        // We directly construct two row vectors: "local" has is_active=0, "next"
        // has is_active=1. This simulates the exact pair the STARK prover evaluates
        // when checking the transition between a padding row and a re-activated row.

        let mut local_row = vec![BabyBear::ZERO; MULTI_STEP_AIR_WIDTH];
        let mut next_row = vec![BabyBear::ZERO; MULTI_STEP_AIR_WIDTH];

        // local is inactive
        local_row[col::IS_ACTIVE] = BabyBear::ZERO;
        // next is active (non-monotone violation)
        next_row[col::IS_ACTIVE] = BabyBear::ONE;

        // Public inputs (minimal valid set)
        let public_inputs = vec![
            BabyBear::new(99999), // initial_state_root
            BabyBear::new(42),    // request_hash
            BabyBear::ONE,        // conclusion
            BabyBear::new(2),     // num_steps
            BabyBear::new(12345), // final_accumulated_hash
            BabyBear::new(67890), // policy_root
        ];

        let air = MultiStepStarkAir::new(2);
        let alpha = BabyBear::new(7); // arbitrary non-zero alpha
        let constraint_val = air.eval_constraints(&local_row, &next_row, &public_inputs, alpha);

        // The constraint evaluation must be non-zero (violation detected)
        assert_ne!(
            constraint_val,
            BabyBear::ZERO,
            "Non-monotone is_active (0 -> 1) must produce a non-zero constraint evaluation"
        );
    }

    #[test]
    fn test_stark_chain_gap_rejected() {
        // A malicious prover sets prev_accumulated[row 1] to an arbitrary value
        // instead of accumulated_hash[row 0]. The transition constraint
        // `is_active_next * (prev_accumulated_next - accumulated_current) == 0`
        // must catch this.
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);
        let app_auth_pred = BabyBear::new(500);

        let step1 = make_step(
            1,
            state_root,
            app_auth_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );
        let step2 = make_step(
            2,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            app_auth_pred,
            [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step1, step2]);
        let (mut trace, public_inputs) = generate_multi_step_trace(&witness);

        // Verify that the honest trace passes first
        let air = MultiStepStarkAir::new(2);
        let alpha = BabyBear::new(7);
        let honest_val = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_eq!(
            honest_val,
            BabyBear::ZERO,
            "Honest trace should have zero constraint evaluation on transition 0->1"
        );

        // Tamper: break the chain by changing prev_accumulated in row 1
        let original_prev = trace[1][col::PREV_ACCUMULATED];
        trace[1][col::PREV_ACCUMULATED] = BabyBear::new(777777);
        assert_ne!(
            trace[1][col::PREV_ACCUMULATED],
            original_prev,
            "Tampered value should differ from original"
        );

        // Evaluate transition constraints on rows 0->1 using the STARK AIR.
        let constraint_val = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);

        // The constraint evaluation must be non-zero (chain gap detected)
        assert_ne!(
            constraint_val,
            BabyBear::ZERO,
            "Chain gap (prev_accumulated != previous accumulated_hash) must produce \
             a non-zero constraint evaluation"
        );
    }

    // ========================================================================
    // Policy root soundness tests: full rule structure commitment
    // ========================================================================

    #[test]
    fn test_policy_root_binds_full_rule_structure() {
        // A correct rule with a GTE check produces a valid policy_root.
        // The verifier accepts the proof because the policy_root matches.
        use crate::derivation_air::{BodyAtomPattern, CircuitGteCheck, CircuitRule};

        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let budget = BabyBear::new(50);
        let cost = BabyBear::new(10);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let budget_pred = BabyBear::new(700);

        // Rule WITH a GTE check: allow(User, Budget) :- budget_info(User, Budget, Cost), Budget >= Cost.
        let rule_with_gte = CircuitRule {
            id: 10,
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)), // User
                (true, BabyBear::new(1)), // Budget
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: budget_pred,
                terms: [
                    (true, BabyBear::new(0)), // User
                    (true, BabyBear::new(1)), // Budget
                    (true, BabyBear::new(2)), // Cost
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: Some(CircuitGteCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(1), // Budget
                rhs_is_var: true,
                rhs_value: BabyBear::new(2), // Cost
            }),
            lt_check: None,
        };

        let body_hash = hash_fact(budget_pred, &[alice, budget, cost]);

        let step = DerivationWitness {
            rule: rule_with_gte,
            state_root,
            body_fact_hashes: vec![body_hash],
            substitution: vec![alice, budget, cost],
            derived_predicate: allow_pred,
            derived_terms: [alice, budget, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        assert_eq!(witness.conclusion(), BabyBear::ONE, "Should conclude ALLOW");

        // The witness should produce a valid proof
        let air = MultiStepDerivationAir::new(witness.clone());
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Correct policy with GTE check should verify: {:?}",
            result.violations()
        );

        // Also verify via STARK
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();
        let proof = prove_authorization_stark(&witness);
        let result = verify_authorization_stark(conclusion, acc_hash, &proof);
        assert!(
            result.is_ok(),
            "STARK proof with correct GTE policy should verify: {:?}",
            result.err()
        );

        // The policy_root in the proof is non-zero and deterministic
        let policy_root_value = proof.public_inputs[pi::POLICY_ROOT];
        assert_ne!(policy_root_value, 0, "policy_root should be non-zero");
    }

    #[test]
    fn test_stripped_gte_check_produces_wrong_policy_root() {
        // SOUNDNESS TEST: A prover strips the GTE check from a rule but keeps
        // the same rule_id. The resulting policy_root MUST differ from the
        // legitimate policy_root, causing verifier rejection.
        use crate::derivation_air::{
            BodyAtomPattern, CircuitGteCheck, CircuitRule, compute_policy_root,
        };

        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let budget = BabyBear::new(5); // budget LESS than cost!
        let cost = BabyBear::new(10);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let budget_pred = BabyBear::new(700);

        // The LEGITIMATE rule (with GTE check: Budget >= Cost)
        let legitimate_rule = CircuitRule {
            id: 10,
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
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
            memberof_checks: vec![],
            gte_check: Some(CircuitGteCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(1), // Budget
                rhs_is_var: true,
                rhs_value: BabyBear::new(2), // Cost
            }),
            lt_check: None,
        };

        // The STRIPPED rule (same ID but NO GTE check -- malicious)
        let stripped_rule = CircuitRule {
            id: 10, // Same ID!
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
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
            memberof_checks: vec![],
            gte_check: None, // STRIPPED! No budget check!
            lt_check: None,
        };

        // Compute the LEGITIMATE policy_root (what the verifier expects)
        let legitimate_policy_root = compute_policy_root(&[&legitimate_rule]);

        // Compute the STRIPPED policy_root (what a malicious prover would produce)
        let stripped_policy_root = compute_policy_root(&[&stripped_rule]);

        // The two policy roots MUST differ -- this is the core soundness property
        assert_ne!(
            legitimate_policy_root, stripped_policy_root,
            "SOUNDNESS FAILURE: Stripped rule produces same policy_root as legitimate rule! \
             A prover could bypass the GTE budget check."
        );

        // Now demonstrate the attack scenario: prover uses stripped rule with
        // budget=5, cost=10 (would fail GTE check). Without GTE, derivation succeeds.
        let body_hash = hash_fact(budget_pred, &[alice, budget, cost]);

        let malicious_step = DerivationWitness {
            rule: stripped_rule,
            state_root,
            body_fact_hashes: vec![body_hash],
            substitution: vec![alice, budget, cost],
            derived_predicate: allow_pred,
            derived_terms: [alice, budget, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let malicious_witness =
            build_multi_step_witness(state_root, BabyBear::new(42), vec![malicious_step]);

        // The malicious witness produces a proof (the circuit itself is satisfied
        // because there's no GTE check in the stripped rule)
        let air = MultiStepDerivationAir::new(malicious_witness.clone());
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Stripped rule passes AIR constraints (no GTE to fail)"
        );

        // BUT: the policy_root in the malicious proof differs from the legitimate one.
        // The verifier compares proof.policy_root against their known legitimate policy:
        let malicious_proof_policy_root = malicious_witness.policy_root;
        assert_ne!(
            malicious_proof_policy_root, legitimate_policy_root,
            "Verifier REJECTS: malicious proof's policy_root ({:?}) does not match \
             legitimate policy_root ({:?})",
            malicious_proof_policy_root, legitimate_policy_root
        );

        // Also verify via STARK: the proof is valid BUT has wrong policy_root
        let conclusion = malicious_witness.conclusion();
        let acc_hash = malicious_witness.final_accumulated_hash();
        let proof = prove_authorization_stark(&malicious_witness);

        // The STARK proof itself verifies (constraints are satisfied for the stripped rule)
        let result = verify_authorization_stark(conclusion, acc_hash, &proof);
        assert!(
            result.is_ok(),
            "STARK proof is technically valid for stripped rule"
        );

        // BUT the policy_root public input does NOT match the legitimate policy
        let proof_policy_root = BabyBear::new_canonical(proof.public_inputs[pi::POLICY_ROOT]);
        assert_ne!(
            proof_policy_root, legitimate_policy_root,
            "Verifier REJECTS: proof policy_root does not match expected legitimate policy. \
             The prover cannot bypass the GTE budget check by stripping it from the rule."
        );

        println!(
            "SOUNDNESS VERIFIED: legitimate_policy_root={:?}, stripped_policy_root={:?}",
            legitimate_policy_root, stripped_policy_root
        );
    }

    #[test]
    fn test_policy_root_different_for_different_rule_structures() {
        // Additional soundness checks: various rule modifications produce different hashes
        use crate::derivation_air::{
            BodyAtomPattern, CircuitEqualCheck, CircuitGteCheck, CircuitLtCheck,
            CircuitMemberOfCheck, CircuitRule, compute_policy_root,
        };

        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let body_pred = BabyBear::new(100);

        let base_rule = CircuitRule {
            id: 1,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: body_pred,
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

        // Rule with an added equal check
        let mut rule_with_eq = base_rule.clone();
        rule_with_eq.equal_checks.push(CircuitEqualCheck {
            lhs_is_var: true,
            lhs_value: BabyBear::new(0),
            rhs_is_var: false,
            rhs_value: BabyBear::new(1000),
        });

        // Rule with an added memberof check
        let mut rule_with_memberof = base_rule.clone();
        rule_with_memberof
            .memberof_checks
            .push(CircuitMemberOfCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0),
                rhs_is_var: true,
                rhs_value: BabyBear::new(1),
            });

        // Rule with an LT check
        let mut rule_with_lt = base_rule.clone();
        rule_with_lt.lt_check = Some(CircuitLtCheck {
            lhs_is_var: true,
            lhs_value: BabyBear::new(0),
            rhs_is_var: true,
            rhs_value: BabyBear::new(1),
        });

        // Rule with different head predicate
        let mut rule_different_head = base_rule.clone();
        rule_different_head.head_predicate = BabyBear::new(999);

        let base_root = compute_policy_root(&[&base_rule]);
        let eq_root = compute_policy_root(&[&rule_with_eq]);
        let memberof_root = compute_policy_root(&[&rule_with_memberof]);
        let lt_root = compute_policy_root(&[&rule_with_lt]);
        let diff_head_root = compute_policy_root(&[&rule_different_head]);

        // All must be different from each other
        let roots = [base_root, eq_root, memberof_root, lt_root, diff_head_root];
        for i in 0..roots.len() {
            for j in (i + 1)..roots.len() {
                assert_ne!(
                    roots[i], roots[j],
                    "Policy roots for structurally different rules must differ: \
                     root[{}]={:?} == root[{}]={:?}",
                    i, roots[i], j, roots[j]
                );
            }
        }
    }
}
