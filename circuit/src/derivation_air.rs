//! Derivation step types, constants, witnesses, and backward-compatible prove/verify.
//!
//! The full AIR constraint logic has moved to [`crate::dsl::derivation`]. This module
//! retains the type definitions and constants so that existing `use crate::derivation_air::*`
//! imports continue to work.

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_fact, hash_many};
use crate::stark::StarkProof;

/// Trace width for the derivation AIR.
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
pub const GTE_DIFF_BITS: usize = 30;

/// Column indices.
pub mod col {
    use super::{
        GTE_DIFF_BITS, MAX_BODY_ATOMS, MAX_EQUAL_CHECKS, MAX_HEAD_TERMS, MAX_MEMBEROF_CHECKS,
        MAX_SUB_VARS,
    };

    pub const RULE_ID: usize = 0;
    pub const BODY_HASH_START: usize = 1;
    pub const BODY_MEMBERSHIP_START: usize = BODY_HASH_START + MAX_BODY_ATOMS;
    pub const HEAD_PRED: usize = BODY_MEMBERSHIP_START + MAX_BODY_ATOMS;
    pub const HEAD_TERM_START: usize = HEAD_PRED + 1;
    pub const DERIVED_HASH: usize = HEAD_TERM_START + MAX_HEAD_TERMS;
    pub const SUB_VALUE_START: usize = DERIVED_HASH + 1;
    pub const BODY_ROOT_START: usize = SUB_VALUE_START + MAX_SUB_VARS;

    pub const HEAD_IS_VAR_START: usize = BODY_ROOT_START + MAX_BODY_ATOMS;
    pub const HEAD_RAW_VALUE_START: usize = HEAD_IS_VAR_START + MAX_HEAD_TERMS;
    pub const HEAD_SEL_VAR_START: usize = HEAD_RAW_VALUE_START + MAX_HEAD_TERMS;

    #[inline]
    pub const fn head_sel_var(term_idx: usize, var_idx: usize) -> usize {
        HEAD_SEL_VAR_START + term_idx * MAX_SUB_VARS + var_idx
    }

    pub const EQ_CHECK_START: usize = HEAD_SEL_VAR_START + MAX_HEAD_TERMS * MAX_SUB_VARS;

    #[inline]
    pub const fn eq_check_active(check_idx: usize) -> usize {
        EQ_CHECK_START + check_idx * 3
    }
    #[inline]
    pub const fn eq_check_term_a(check_idx: usize) -> usize {
        EQ_CHECK_START + check_idx * 3 + 1
    }
    #[inline]
    pub const fn eq_check_term_b(check_idx: usize) -> usize {
        EQ_CHECK_START + check_idx * 3 + 2
    }

    pub const MEMBEROF_CHECK_START: usize = EQ_CHECK_START + MAX_EQUAL_CHECKS * 3;

    #[inline]
    pub const fn memberof_check_active(check_idx: usize) -> usize {
        MEMBEROF_CHECK_START + check_idx * 3
    }
    #[inline]
    pub const fn memberof_check_term_a(check_idx: usize) -> usize {
        MEMBEROF_CHECK_START + check_idx * 3 + 1
    }
    #[inline]
    pub const fn memberof_check_term_b(check_idx: usize) -> usize {
        MEMBEROF_CHECK_START + check_idx * 3 + 2
    }

    pub const GTE_CHECK_START: usize = MEMBEROF_CHECK_START + MAX_MEMBEROF_CHECKS * 3;
    pub const GTE_CHECK_ACTIVE: usize = GTE_CHECK_START;
    pub const GTE_CHECK_TERM_A: usize = GTE_CHECK_START + 1;
    pub const GTE_CHECK_TERM_B: usize = GTE_CHECK_START + 2;
    pub const GTE_CHECK_DIFF: usize = GTE_CHECK_START + 3;
    pub const GTE_CHECK_DIFF_BITS_START: usize = GTE_CHECK_START + 4;

    #[inline]
    pub const fn gte_diff_bit(bit_idx: usize) -> usize {
        GTE_CHECK_DIFF_BITS_START + bit_idx
    }

    pub const LT_CHECK_START: usize = GTE_CHECK_DIFF_BITS_START + GTE_DIFF_BITS;
    pub const LT_CHECK_ACTIVE: usize = LT_CHECK_START;
    pub const LT_CHECK_TERM_A: usize = LT_CHECK_START + 1;
    pub const LT_CHECK_TERM_B: usize = LT_CHECK_START + 2;
    pub const LT_CHECK_DIFF: usize = LT_CHECK_START + 3;
    pub const LT_CHECK_DIFF_BITS_START: usize = LT_CHECK_START + 4;

    #[inline]
    pub const fn lt_diff_bit(bit_idx: usize) -> usize {
        LT_CHECK_DIFF_BITS_START + bit_idx
    }

    pub const CHECK_TERM_COLS: usize = 1 + 1 + MAX_SUB_VARS;
    pub const CHECK_TERM_BINDING_START: usize = LT_CHECK_DIFF_BITS_START + GTE_DIFF_BITS;
    pub const NUM_CHECK_TERMS: usize = MAX_EQUAL_CHECKS * 2 + MAX_MEMBEROF_CHECKS * 2 + 2 + 2;

    #[inline]
    pub const fn check_term_base(slot: usize) -> usize {
        CHECK_TERM_BINDING_START + slot * CHECK_TERM_COLS
    }

    #[inline]
    pub const fn check_term_is_var(slot: usize) -> usize {
        check_term_base(slot)
    }

    #[inline]
    pub const fn check_term_raw_value(slot: usize) -> usize {
        check_term_base(slot) + 1
    }

    #[inline]
    pub const fn check_term_sel(slot: usize, var_idx: usize) -> usize {
        check_term_base(slot) + 2 + var_idx
    }

    #[inline]
    pub const fn eq_check_term_a_slot(check_idx: usize) -> usize {
        check_idx * 2
    }
    #[inline]
    pub const fn eq_check_term_b_slot(check_idx: usize) -> usize {
        check_idx * 2 + 1
    }
    #[inline]
    pub const fn memberof_check_term_a_slot(check_idx: usize) -> usize {
        MAX_EQUAL_CHECKS * 2 + check_idx * 2
    }
    #[inline]
    pub const fn memberof_check_term_b_slot(check_idx: usize) -> usize {
        MAX_EQUAL_CHECKS * 2 + check_idx * 2 + 1
    }

    pub const GTE_TERM_A_SLOT: usize = MAX_EQUAL_CHECKS * 2 + MAX_MEMBEROF_CHECKS * 2;
    pub const GTE_TERM_B_SLOT: usize = GTE_TERM_A_SLOT + 1;
    pub const LT_TERM_A_SLOT: usize = GTE_TERM_B_SLOT + 1;
    pub const LT_TERM_B_SLOT: usize = LT_TERM_A_SLOT + 1;

    pub const _TOTAL: usize = CHECK_TERM_BINDING_START + NUM_CHECK_TERMS * CHECK_TERM_COLS;
}

/// A rule definition for the circuit.
#[derive(Clone, Debug)]
pub struct CircuitRule {
    pub id: u32,
    pub num_body_atoms: usize,
    pub num_variables: usize,
    pub head_predicate: BabyBear,
    pub head_terms: [(bool, BabyBear); 4],
    pub body_atoms: Vec<BodyAtomPattern>,
    pub equal_checks: Vec<CircuitEqualCheck>,
    pub memberof_checks: Vec<CircuitMemberOfCheck>,
    pub gte_check: Option<CircuitGteCheck>,
    pub lt_check: Option<CircuitLtCheck>,
}

impl CircuitRule {
    pub fn compute_structure_hash(&self) -> BabyBear {
        let mut elements = Vec::with_capacity(32);
        elements.push(BabyBear::new(self.id));
        elements.push(self.head_predicate);
        elements.push(BabyBear::new(self.num_body_atoms as u32));
        elements.push(BabyBear::new(self.num_variables as u32));
        for &(is_var, value) in &self.head_terms {
            elements.push(if is_var {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            elements.push(value);
        }
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
        match &self.gte_check {
            Some(gte) => {
                elements.push(BabyBear::ONE);
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
            None => elements.push(BabyBear::ZERO),
        }
        match &self.lt_check {
            Some(lt) => {
                elements.push(BabyBear::ONE);
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
            None => elements.push(BabyBear::ZERO),
        }
        hash_many(&elements)
    }
}

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

#[derive(Clone, Debug)]
pub struct CircuitEqualCheck {
    pub lhs_is_var: bool,
    pub lhs_value: BabyBear,
    pub rhs_is_var: bool,
    pub rhs_value: BabyBear,
}

#[derive(Clone, Debug)]
pub struct CircuitMemberOfCheck {
    pub lhs_is_var: bool,
    pub lhs_value: BabyBear,
    pub rhs_is_var: bool,
    pub rhs_value: BabyBear,
}

#[derive(Clone, Debug)]
pub struct CircuitGteCheck {
    pub lhs_is_var: bool,
    pub lhs_value: BabyBear,
    pub rhs_is_var: bool,
    pub rhs_value: BabyBear,
}

#[derive(Clone, Debug)]
pub struct CircuitLtCheck {
    pub lhs_is_var: bool,
    pub lhs_value: BabyBear,
    pub rhs_is_var: bool,
    pub rhs_value: BabyBear,
}

#[derive(Clone, Debug)]
pub struct BodyAtomPattern {
    pub predicate: BabyBear,
    pub terms: [(bool, BabyBear); 3],
}

#[derive(Clone, Debug)]
pub struct DerivationWitness {
    pub rule: CircuitRule,
    pub state_root: BabyBear,
    pub body_fact_hashes: Vec<BabyBear>,
    pub substitution: Vec<BabyBear>,
    pub derived_predicate: BabyBear,
    pub derived_terms: [BabyBear; 4],
    pub not_after_height: BabyBear,
    pub org_id_hash: BabyBear,
    pub budget_remaining: BabyBear,
}

impl DerivationWitness {
    pub fn derived_hash(&self) -> BabyBear {
        hash_fact(self.derived_predicate, self.derived_terms.as_slice())
    }

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

    pub fn check_head_match(&self) -> bool {
        if self.derived_predicate != self.rule.head_predicate {
            return false;
        }
        for (i, &(is_var, val)) in self.rule.head_terms.iter().enumerate() {
            let expected = self.resolve_term(is_var, val);
            if expected != self.derived_terms[i] {
                return false;
            }
        }
        true
    }
}

/// Legacy derivation AIR struct.
pub struct DerivationAir {
    pub witness: DerivationWitness,
}

impl DerivationAir {
    pub fn new(witness: DerivationWitness) -> Self {
        Self { witness }
    }
}

/// Legacy StarkAir struct for derivation.
pub struct DerivationStarkAir {
    pub witness: DerivationWitness,
}

impl DerivationStarkAir {
    pub fn new(witness: DerivationWitness) -> Self {
        Self { witness }
    }
}

/// Prove a derivation step (delegates to DSL).
pub fn prove_derivation_stark(witness: &DerivationWitness) -> Option<StarkProof> {
    crate::dsl::derivation::prove_derivation_dsl(witness)
}

/// Verify a derivation STARK proof (delegates to DSL).
pub fn verify_derivation_stark(
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    crate::dsl::derivation::verify_derivation_dsl(proof, public_inputs)
}

/// Helper: create a test derivation witness.
pub fn create_test_derivation() -> DerivationWitness {
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
            (true, BabyBear::new(0)),
            (true, BabyBear::new(1)),
            (false, BabyBear::ZERO),
            (false, BabyBear::ZERO),
        ],
        body_atoms: vec![
            BodyAtomPattern {
                predicate: owns_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            },
            BodyAtomPattern {
                predicate: can_read_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            },
        ],
        equal_checks: vec![],
        memberof_checks: vec![],
        gte_check: None,
        lt_check: None,
    };

    let body_fact_1 = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);
    let body_fact_2 = hash_fact(can_read_pred, &[alice, file, BabyBear::ZERO]);

    DerivationWitness {
        rule,
        state_root: BabyBear::new(99999),
        body_fact_hashes: vec![body_fact_1, body_fact_2],
        substitution: vec![alice, file],
        derived_predicate: access_pred,
        derived_terms: [alice, file, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    }
}
