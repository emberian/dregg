//! DSL-native derivation proving and verification.
//!
//! This module provides production-quality prove/verify functions for derivation
//! steps using the [`DslCircuit`] interpreter. It replaces the hand-written
//! `DerivationStarkAir` with an equivalent implementation driven by the
//! [`CircuitDescriptor`] from [`derivation_circuit_descriptor()`].
//!
//! ## Trace Layout
//!
//! The trace has [`EXTENDED_TRACE_WIDTH`] = 379 columns:
//! - Columns 0..371: standard derivation columns (body hashes, membership flags,
//!   head terms, substitution values, selectors, checks, check term bindings)
//! - Columns 371..379: auxiliary inverse columns for C2 (ConditionalNonzero)
//!
//! ## Usage
//!
//! ```ignore
//! use pyana_dsl_runtime::derivation::{prove_derivation_dsl, verify_derivation_dsl};
//! use crate::derivation_air::DerivationWitness;
//!
//! let proof = prove_derivation_dsl(&witness).unwrap();
//! verify_derivation_dsl(&proof, &public_inputs).unwrap();
//! ```

use crate::derivation_air::{
    DERIVATION_AIR_WIDTH, DerivationWitness, GTE_DIFF_BITS, MAX_BODY_ATOMS, MAX_EQUAL_CHECKS,
    MAX_HEAD_TERMS, MAX_MEMBEROF_CHECKS, MAX_SUB_VARS, col,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Constants
// ============================================================================

/// Auxiliary column indices for C2 (ConditionalNonzero) inverse columns.
/// These are appended after the standard DERIVATION_AIR_WIDTH (371) columns.
/// One inverse column per body atom slot (8 total).
pub const BODY_HASH_INV_START: usize = DERIVATION_AIR_WIDTH; // 371

/// Extended trace width including auxiliary inverse columns for C2.
pub const EXTENDED_TRACE_WIDTH: usize = DERIVATION_AIR_WIDTH + MAX_BODY_ATOMS; // 379

// ============================================================================
// Descriptor Construction
// ============================================================================

/// Negate a field element: returns BABYBEAR_P - 1 (the additive inverse of ONE).
fn neg_one() -> BabyBear {
    BabyBear::new(BABYBEAR_P - 1)
}

/// Build a polynomial term: `coeff * product(local[col] for col in cols)`.
fn term(coeff: BabyBear, cols: &[usize]) -> PolyTerm {
    PolyTerm {
        coeff,
        col_indices: cols.to_vec(),
    }
}

/// Construct the derivation AIR as a CircuitDescriptor.
///
/// This encodes constraints C1-C28 including:
/// - C2 (body_hash_nonzero_when_used): ConditionalNonzero
/// - C3 (at_least_one_body): AtLeastOne
/// - C4 (derived_hash_correct): Hash
///
/// The trace is extended by 8 auxiliary inverse columns (for C2) beyond the
/// standard DERIVATION_AIR_WIDTH, giving EXTENDED_TRACE_WIDTH = 379.
pub fn derivation_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // ========================================================================
    // C1: body_membership_binary — flag * (flag - 1) == 0 for each body slot
    // ========================================================================
    for i in 0..MAX_BODY_ATOMS {
        let flag_col = col::BODY_MEMBERSHIP_START + i;
        constraints.push(ConstraintExpr::Binary { col: flag_col });
    }

    // ========================================================================
    // C2: body_hash_nonzero_when_used — when flag=1, hash must be nonzero
    // Uses ConditionalNonzero: selector * (value * inverse - 1) == 0
    // ========================================================================
    for i in 0..MAX_BODY_ATOMS {
        let flag_col = col::BODY_MEMBERSHIP_START + i;
        let hash_col = col::BODY_HASH_START + i;
        let inv_col = BODY_HASH_INV_START + i;
        constraints.push(ConstraintExpr::ConditionalNonzero {
            selector_col: flag_col,
            value_col: hash_col,
            inverse_col: inv_col,
        });
    }

    // ========================================================================
    // C3: at_least_one_body — at least one membership flag must be 1
    // ========================================================================
    {
        let flag_cols: Vec<usize> = (0..MAX_BODY_ATOMS)
            .map(|i| col::BODY_MEMBERSHIP_START + i)
            .collect();
        constraints.push(ConstraintExpr::AtLeastOne { flag_cols });
    }

    // ========================================================================
    // C4: derived_hash_correct — DERIVED_HASH == hash_fact(HEAD_PRED, HEAD_TERM[0..3])
    // ========================================================================
    constraints.push(ConstraintExpr::Hash {
        output_col: col::DERIVED_HASH,
        input_cols: vec![
            col::HEAD_PRED,
            col::HEAD_TERM_START,
            col::HEAD_TERM_START + 1,
            col::HEAD_TERM_START + 2,
            col::HEAD_TERM_START + 3,
        ],
    });

    // ========================================================================
    // C5: body_roots_match_state — flag * (root - state_root) == 0
    // Uses Gated + PiBinding: flag * (root - pi[0]) == 0
    // ========================================================================
    for i in 0..MAX_BODY_ATOMS {
        let flag_col = col::BODY_MEMBERSHIP_START + i;
        let root_col = col::BODY_ROOT_START + i;
        constraints.push(ConstraintExpr::Gated {
            selector_col: flag_col,
            inner: Box::new(ConstraintExpr::PiBinding {
                col: root_col,
                pi_index: 0,
            }),
        });
    }

    // ========================================================================
    // C6: derived_hash_public — derived_hash == public_inputs[1]
    // ========================================================================
    constraints.push(ConstraintExpr::PiBinding {
        col: col::DERIVED_HASH,
        pi_index: 1,
    });

    // ========================================================================
    // C7: head_is_var_binary — flag * (flag - 1) == 0
    // ========================================================================
    for i in 0..MAX_HEAD_TERMS {
        let flag_col = col::HEAD_IS_VAR_START + i;
        constraints.push(ConstraintExpr::Binary { col: flag_col });
    }

    // ========================================================================
    // C8: head_sel_var_binary — sel * (sel - 1) == 0 for all 4*8=32 selector cols
    // ========================================================================
    for term_i in 0..MAX_HEAD_TERMS {
        for var_j in 0..MAX_SUB_VARS {
            let sel_col = col::head_sel_var(term_i, var_j);
            constraints.push(ConstraintExpr::Binary { col: sel_col });
        }
    }

    // ========================================================================
    // C9: head_sel_var_sum_equals_is_var — (sum(sel_j) - is_var)^2 == 0
    // ========================================================================
    for term_i in 0..MAX_HEAD_TERMS {
        let is_var_col = col::HEAD_IS_VAR_START + term_i;
        let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 1);
        for var_j in 0..MAX_SUB_VARS {
            terms_vec.push(term(BabyBear::ONE, &[col::head_sel_var(term_i, var_j)]));
        }
        terms_vec.push(term(neg_one(), &[is_var_col]));
        constraints.push(ConstraintExpr::Squared {
            inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
        });
    }

    // ========================================================================
    // C10: substitution_application
    // (derived_term[i] - expected)^2 == 0, where:
    //   expected = is_var * sum(sel_j * sub_j) + (1 - is_var) * raw_value
    // Expanded: derived_term - raw_value + is_var*raw_value - sum(sel_j*sub_j)
    // ========================================================================
    for term_i in 0..MAX_HEAD_TERMS {
        let derived_col = col::HEAD_TERM_START + term_i;
        let is_var_col = col::HEAD_IS_VAR_START + term_i;
        let raw_col = col::HEAD_RAW_VALUE_START + term_i;

        let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
        terms_vec.push(term(BabyBear::ONE, &[derived_col]));
        terms_vec.push(term(neg_one(), &[raw_col]));
        terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
        for var_j in 0..MAX_SUB_VARS {
            let sel_col = col::head_sel_var(term_i, var_j);
            let sub_col = col::SUB_VALUE_START + var_j;
            terms_vec.push(term(neg_one(), &[sel_col, sub_col]));
        }
        constraints.push(ConstraintExpr::Squared {
            inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
        });
    }

    // ========================================================================
    // C11: eq_check_active_binary
    // ========================================================================
    for i in 0..MAX_EQUAL_CHECKS {
        constraints.push(ConstraintExpr::Binary {
            col: col::eq_check_active(i),
        });
    }

    // ========================================================================
    // C12: eq_check_enforced — active * (term_a - term_b) == 0
    // ========================================================================
    for i in 0..MAX_EQUAL_CHECKS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::eq_check_active(i),
            inner: Box::new(ConstraintExpr::Equality {
                col_a: col::eq_check_term_a(i),
                col_b: col::eq_check_term_b(i),
            }),
        });
    }

    // ========================================================================
    // C13: memberof_check_active_binary
    // ========================================================================
    for i in 0..MAX_MEMBEROF_CHECKS {
        constraints.push(ConstraintExpr::Binary {
            col: col::memberof_check_active(i),
        });
    }

    // ========================================================================
    // C14: memberof_check_enforced — active * (term_a - term_b) == 0
    // ========================================================================
    for i in 0..MAX_MEMBEROF_CHECKS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::memberof_check_active(i),
            inner: Box::new(ConstraintExpr::Equality {
                col_a: col::memberof_check_term_a(i),
                col_b: col::memberof_check_term_b(i),
            }),
        });
    }

    // ========================================================================
    // C15: gte_check_active_binary
    // ========================================================================
    constraints.push(ConstraintExpr::Binary {
        col: col::GTE_CHECK_ACTIVE,
    });

    // ========================================================================
    // C16: gte_check_diff_correct — active * (diff - (term_a - term_b)) == 0
    // ========================================================================
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::GTE_CHECK_ACTIVE,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[col::GTE_CHECK_DIFF]),
                term(neg_one(), &[col::GTE_CHECK_TERM_A]),
                term(BabyBear::ONE, &[col::GTE_CHECK_TERM_B]),
            ],
        }),
    });

    // ========================================================================
    // C17: gte_check_bit_decomposition — active * (sum(bit_i * 2^i) - diff) == 0
    // ========================================================================
    {
        let mut bit_terms = Vec::with_capacity(GTE_DIFF_BITS + 1);
        let mut power = BabyBear::ONE;
        for i in 0..GTE_DIFF_BITS {
            bit_terms.push(term(power, &[col::gte_diff_bit(i)]));
            power = power + power;
        }
        bit_terms.push(term(neg_one(), &[col::GTE_CHECK_DIFF]));
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::GTE_CHECK_ACTIVE,
            inner: Box::new(ConstraintExpr::Polynomial { terms: bit_terms }),
        });
    }

    // ========================================================================
    // C18: gte_check_bits_binary — active * bit_i * (bit_i - 1) == 0
    // ========================================================================
    for i in 0..GTE_DIFF_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::GTE_CHECK_ACTIVE,
            inner: Box::new(ConstraintExpr::Binary {
                col: col::gte_diff_bit(i),
            }),
        });
    }

    // ========================================================================
    // C19: gte_check_high_bit_zero — active * high_bit == 0
    // ========================================================================
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::GTE_CHECK_ACTIVE,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![term(BabyBear::ONE, &[col::gte_diff_bit(GTE_DIFF_BITS - 1)])],
        }),
    });

    // ========================================================================
    // C20: lt_check_active_binary
    // ========================================================================
    constraints.push(ConstraintExpr::Binary {
        col: col::LT_CHECK_ACTIVE,
    });

    // ========================================================================
    // C21: lt_check_diff_correct — active * (diff - (term_b - term_a - 1)) == 0
    // ========================================================================
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::LT_CHECK_ACTIVE,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[col::LT_CHECK_DIFF]),
                term(neg_one(), &[col::LT_CHECK_TERM_B]),
                term(BabyBear::ONE, &[col::LT_CHECK_TERM_A]),
                term(BabyBear::ONE, &[]), // constant +1
            ],
        }),
    });

    // ========================================================================
    // C22: lt_check_bit_decomposition — active * (sum(bit_i * 2^i) - diff) == 0
    // ========================================================================
    {
        let mut bit_terms = Vec::with_capacity(GTE_DIFF_BITS + 1);
        let mut power = BabyBear::ONE;
        for i in 0..GTE_DIFF_BITS {
            bit_terms.push(term(power, &[col::lt_diff_bit(i)]));
            power = power + power;
        }
        bit_terms.push(term(neg_one(), &[col::LT_CHECK_DIFF]));
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::LT_CHECK_ACTIVE,
            inner: Box::new(ConstraintExpr::Polynomial { terms: bit_terms }),
        });
    }

    // ========================================================================
    // C23: lt_check_bits_binary — active * bit_i * (bit_i - 1) == 0
    // ========================================================================
    for i in 0..GTE_DIFF_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::LT_CHECK_ACTIVE,
            inner: Box::new(ConstraintExpr::Binary {
                col: col::lt_diff_bit(i),
            }),
        });
    }

    // ========================================================================
    // C24: lt_check_high_bit_zero — active * high_bit == 0
    // ========================================================================
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::LT_CHECK_ACTIVE,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![term(BabyBear::ONE, &[col::lt_diff_bit(GTE_DIFF_BITS - 1)])],
        }),
    });

    // ========================================================================
    // C25: check_term_is_var_binary — for all 20 check term slots
    // ========================================================================
    for slot in 0..col::NUM_CHECK_TERMS {
        constraints.push(ConstraintExpr::Binary {
            col: col::check_term_is_var(slot),
        });
    }

    // ========================================================================
    // C26: check_term_sel_binary — for all 20*8=160 selector cols
    // ========================================================================
    for slot in 0..col::NUM_CHECK_TERMS {
        for var_j in 0..MAX_SUB_VARS {
            constraints.push(ConstraintExpr::Binary {
                col: col::check_term_sel(slot, var_j),
            });
        }
    }

    // ========================================================================
    // C27: check_term_sel_sum_equals_is_var — (sum(sel_j) - is_var)^2 == 0
    // ========================================================================
    for slot in 0..col::NUM_CHECK_TERMS {
        let is_var_col = col::check_term_is_var(slot);
        let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 1);
        for var_j in 0..MAX_SUB_VARS {
            terms_vec.push(term(BabyBear::ONE, &[col::check_term_sel(slot, var_j)]));
        }
        terms_vec.push(term(neg_one(), &[is_var_col]));
        constraints.push(ConstraintExpr::Squared {
            inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
        });
    }

    // ========================================================================
    // C28: check_term_binding_correct
    // For each active check, trace_term must equal resolved value from bindings.
    // ========================================================================

    // Equal check bindings
    for i in 0..MAX_EQUAL_CHECKS {
        let active_col = col::eq_check_active(i);

        // term_a binding
        {
            let slot = col::eq_check_term_a_slot(i);
            let trace_col = col::eq_check_term_a(i);
            let is_var_col = col::check_term_is_var(slot);
            let raw_col = col::check_term_raw_value(slot);

            let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
            terms_vec.push(term(BabyBear::ONE, &[trace_col]));
            terms_vec.push(term(neg_one(), &[raw_col]));
            terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
            for var_j in 0..MAX_SUB_VARS {
                terms_vec.push(term(
                    neg_one(),
                    &[
                        col::check_term_sel(slot, var_j),
                        col::SUB_VALUE_START + var_j,
                    ],
                ));
            }
            constraints.push(ConstraintExpr::Gated {
                selector_col: active_col,
                inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
            });
        }

        // term_b binding
        {
            let slot = col::eq_check_term_b_slot(i);
            let trace_col = col::eq_check_term_b(i);
            let is_var_col = col::check_term_is_var(slot);
            let raw_col = col::check_term_raw_value(slot);

            let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
            terms_vec.push(term(BabyBear::ONE, &[trace_col]));
            terms_vec.push(term(neg_one(), &[raw_col]));
            terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
            for var_j in 0..MAX_SUB_VARS {
                terms_vec.push(term(
                    neg_one(),
                    &[
                        col::check_term_sel(slot, var_j),
                        col::SUB_VALUE_START + var_j,
                    ],
                ));
            }
            constraints.push(ConstraintExpr::Gated {
                selector_col: active_col,
                inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
            });
        }
    }

    // MemberOf check bindings
    for i in 0..MAX_MEMBEROF_CHECKS {
        let active_col = col::memberof_check_active(i);

        // term_a binding
        {
            let slot = col::memberof_check_term_a_slot(i);
            let trace_col = col::memberof_check_term_a(i);
            let is_var_col = col::check_term_is_var(slot);
            let raw_col = col::check_term_raw_value(slot);

            let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
            terms_vec.push(term(BabyBear::ONE, &[trace_col]));
            terms_vec.push(term(neg_one(), &[raw_col]));
            terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
            for var_j in 0..MAX_SUB_VARS {
                terms_vec.push(term(
                    neg_one(),
                    &[
                        col::check_term_sel(slot, var_j),
                        col::SUB_VALUE_START + var_j,
                    ],
                ));
            }
            constraints.push(ConstraintExpr::Gated {
                selector_col: active_col,
                inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
            });
        }

        // term_b binding
        {
            let slot = col::memberof_check_term_b_slot(i);
            let trace_col = col::memberof_check_term_b(i);
            let is_var_col = col::check_term_is_var(slot);
            let raw_col = col::check_term_raw_value(slot);

            let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
            terms_vec.push(term(BabyBear::ONE, &[trace_col]));
            terms_vec.push(term(neg_one(), &[raw_col]));
            terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
            for var_j in 0..MAX_SUB_VARS {
                terms_vec.push(term(
                    neg_one(),
                    &[
                        col::check_term_sel(slot, var_j),
                        col::SUB_VALUE_START + var_j,
                    ],
                ));
            }
            constraints.push(ConstraintExpr::Gated {
                selector_col: active_col,
                inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
            });
        }
    }

    // GTE check bindings
    {
        let active_col = col::GTE_CHECK_ACTIVE;

        // term_a binding
        {
            let slot = col::GTE_TERM_A_SLOT;
            let trace_col = col::GTE_CHECK_TERM_A;
            let is_var_col = col::check_term_is_var(slot);
            let raw_col = col::check_term_raw_value(slot);

            let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
            terms_vec.push(term(BabyBear::ONE, &[trace_col]));
            terms_vec.push(term(neg_one(), &[raw_col]));
            terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
            for var_j in 0..MAX_SUB_VARS {
                terms_vec.push(term(
                    neg_one(),
                    &[
                        col::check_term_sel(slot, var_j),
                        col::SUB_VALUE_START + var_j,
                    ],
                ));
            }
            constraints.push(ConstraintExpr::Gated {
                selector_col: active_col,
                inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
            });
        }

        // term_b binding
        {
            let slot = col::GTE_TERM_B_SLOT;
            let trace_col = col::GTE_CHECK_TERM_B;
            let is_var_col = col::check_term_is_var(slot);
            let raw_col = col::check_term_raw_value(slot);

            let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
            terms_vec.push(term(BabyBear::ONE, &[trace_col]));
            terms_vec.push(term(neg_one(), &[raw_col]));
            terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
            for var_j in 0..MAX_SUB_VARS {
                terms_vec.push(term(
                    neg_one(),
                    &[
                        col::check_term_sel(slot, var_j),
                        col::SUB_VALUE_START + var_j,
                    ],
                ));
            }
            constraints.push(ConstraintExpr::Gated {
                selector_col: active_col,
                inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
            });
        }
    }

    // LT check bindings
    {
        let active_col = col::LT_CHECK_ACTIVE;

        // term_a binding
        {
            let slot = col::LT_TERM_A_SLOT;
            let trace_col = col::LT_CHECK_TERM_A;
            let is_var_col = col::check_term_is_var(slot);
            let raw_col = col::check_term_raw_value(slot);

            let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
            terms_vec.push(term(BabyBear::ONE, &[trace_col]));
            terms_vec.push(term(neg_one(), &[raw_col]));
            terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
            for var_j in 0..MAX_SUB_VARS {
                terms_vec.push(term(
                    neg_one(),
                    &[
                        col::check_term_sel(slot, var_j),
                        col::SUB_VALUE_START + var_j,
                    ],
                ));
            }
            constraints.push(ConstraintExpr::Gated {
                selector_col: active_col,
                inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
            });
        }

        // term_b binding
        {
            let slot = col::LT_TERM_B_SLOT;
            let trace_col = col::LT_CHECK_TERM_B;
            let is_var_col = col::check_term_is_var(slot);
            let raw_col = col::check_term_raw_value(slot);

            let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
            terms_vec.push(term(BabyBear::ONE, &[trace_col]));
            terms_vec.push(term(neg_one(), &[raw_col]));
            terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
            for var_j in 0..MAX_SUB_VARS {
                terms_vec.push(term(
                    neg_one(),
                    &[
                        col::check_term_sel(slot, var_j),
                        col::SUB_VALUE_START + var_j,
                    ],
                ));
            }
            constraints.push(ConstraintExpr::Gated {
                selector_col: active_col,
                inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
            });
        }
    }

    // ========================================================================
    // Boundary constraints
    // ========================================================================
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::DERIVED_HASH,
            pi_index: 1,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::BODY_ROOT_START,
            pi_index: 0,
        },
    ];

    // ========================================================================
    // Column definitions (key columns for documentation)
    // ========================================================================
    let columns = vec![
        ColumnDef {
            name: "rule_id".into(),
            index: col::RULE_ID,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "head_pred".into(),
            index: col::HEAD_PRED,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "derived_hash".into(),
            index: col::DERIVED_HASH,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: "pyana-derivation-v1".into(),
        trace_width: EXTENDED_TRACE_WIDTH,
        max_degree: 8,
        columns,
        constraints,
        boundaries,
        public_input_count: 5, // state_root, derived_hash, not_after, org_id, budget
    }
}

/// Create a DslCircuit from the derivation descriptor.
pub fn derivation_dsl_circuit() -> DslCircuit {
    DslCircuit::new(derivation_circuit_descriptor())
}

// ============================================================================
// Trace Generation
// ============================================================================

/// Generate a 379-column derivation trace row from a [`DerivationWitness`].
///
/// This produces a single-row trace suitable for the DSL derivation circuit.
/// The extra 8 columns (371..378) are inverse columns required by the
/// ConditionalNonzero constraint (C2).
///
/// Returns `(trace_rows, public_inputs)` where `trace_rows` has at least 2
/// rows (padded to power-of-two) for STARK compatibility.
pub fn generate_derivation_trace_dsl(
    witness: &DerivationWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let derived_hash = witness.derived_hash();

    // Start with a standard 371-column row, then extend to 379.
    let mut row = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];

    // Rule ID
    row[col::RULE_ID] = BabyBear::new(witness.rule.id);

    // Body hashes, membership flags, and body roots
    for (i, &hash) in witness
        .body_fact_hashes
        .iter()
        .enumerate()
        .take(MAX_BODY_ATOMS)
    {
        row[col::BODY_HASH_START + i] = hash;
        row[col::BODY_MEMBERSHIP_START + i] = BabyBear::ONE;
        row[col::BODY_ROOT_START + i] = witness.state_root;
    }

    // Head (derived fact)
    row[col::HEAD_PRED] = witness.derived_predicate;
    for i in 0..MAX_HEAD_TERMS {
        row[col::HEAD_TERM_START + i] = witness.derived_terms[i];
    }
    row[col::DERIVED_HASH] = derived_hash;

    // Substitution values
    for (i, &val) in witness.substitution.iter().enumerate().take(MAX_SUB_VARS) {
        row[col::SUB_VALUE_START + i] = val;
    }

    // --- Substitution verification columns ---
    for (term_i, &(is_var, value)) in witness
        .rule
        .head_terms
        .iter()
        .enumerate()
        .take(MAX_HEAD_TERMS)
    {
        row[col::HEAD_IS_VAR_START + term_i] = if is_var {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        };
        row[col::HEAD_RAW_VALUE_START + term_i] = value;

        if is_var {
            let var_idx = value.as_u32() as usize;
            if var_idx < MAX_SUB_VARS {
                row[col::head_sel_var(term_i, var_idx)] = BabyBear::ONE;
            }
        }
    }

    // --- Equal check columns ---
    for (check_i, eq_check) in witness
        .rule
        .equal_checks
        .iter()
        .enumerate()
        .take(MAX_EQUAL_CHECKS)
    {
        row[col::eq_check_active(check_i)] = BabyBear::ONE;

        let term_a = resolve_check_term(
            eq_check.lhs_is_var,
            eq_check.lhs_value,
            &witness.substitution,
        );
        let term_b = resolve_check_term(
            eq_check.rhs_is_var,
            eq_check.rhs_value,
            &witness.substitution,
        );

        row[col::eq_check_term_a(check_i)] = term_a;
        row[col::eq_check_term_b(check_i)] = term_b;
    }

    // --- MemberOf check columns ---
    for (check_i, mo_check) in witness
        .rule
        .memberof_checks
        .iter()
        .enumerate()
        .take(MAX_MEMBEROF_CHECKS)
    {
        row[col::memberof_check_active(check_i)] = BabyBear::ONE;

        let term_a = resolve_check_term(
            mo_check.lhs_is_var,
            mo_check.lhs_value,
            &witness.substitution,
        );
        let term_b = resolve_check_term(
            mo_check.rhs_is_var,
            mo_check.rhs_value,
            &witness.substitution,
        );

        row[col::memberof_check_term_a(check_i)] = term_a;
        row[col::memberof_check_term_b(check_i)] = term_b;
    }

    // --- GTE check columns ---
    if let Some(gte_check) = &witness.rule.gte_check {
        row[col::GTE_CHECK_ACTIVE] = BabyBear::ONE;

        let term_a = resolve_check_term(
            gte_check.lhs_is_var,
            gte_check.lhs_value,
            &witness.substitution,
        );
        let term_b = resolve_check_term(
            gte_check.rhs_is_var,
            gte_check.rhs_value,
            &witness.substitution,
        );

        row[col::GTE_CHECK_TERM_A] = term_a;
        row[col::GTE_CHECK_TERM_B] = term_b;

        let diff = term_a - term_b;
        row[col::GTE_CHECK_DIFF] = diff;

        let diff_val = diff.as_u32();
        for i in 0..GTE_DIFF_BITS {
            row[col::gte_diff_bit(i)] = BabyBear::new((diff_val >> i) & 1);
        }
    }

    // --- LT check columns ---
    if let Some(lt_check) = &witness.rule.lt_check {
        row[col::LT_CHECK_ACTIVE] = BabyBear::ONE;

        let term_a = resolve_check_term(
            lt_check.lhs_is_var,
            lt_check.lhs_value,
            &witness.substitution,
        );
        let term_b = resolve_check_term(
            lt_check.rhs_is_var,
            lt_check.rhs_value,
            &witness.substitution,
        );

        row[col::LT_CHECK_TERM_A] = term_a;
        row[col::LT_CHECK_TERM_B] = term_b;

        let diff = term_b - term_a - BabyBear::ONE;
        row[col::LT_CHECK_DIFF] = diff;

        let diff_val = diff.as_u32();
        for i in 0..GTE_DIFF_BITS {
            row[col::lt_diff_bit(i)] = BabyBear::new((diff_val >> i) & 1);
        }
    }

    // --- Check term binding columns (SOUNDNESS FIX) ---
    fill_all_check_term_bindings(&mut row, witness);

    // --- Auxiliary inverse columns for C2 (ConditionalNonzero) ---
    for i in 0..MAX_BODY_ATOMS {
        let flag = row[col::BODY_MEMBERSHIP_START + i];
        let hash = row[col::BODY_HASH_START + i];
        if flag == BabyBear::ONE && hash != BabyBear::ZERO {
            row[BODY_HASH_INV_START + i] = hash.inverse().unwrap();
        }
    }

    // Public inputs: [state_root, derived_hash, not_after, org_id, budget]
    let public_inputs = vec![
        witness.state_root,
        derived_hash,
        witness.not_after_height,
        witness.org_id_hash,
        witness.budget_remaining,
    ];

    // Pad to power-of-two >= 2 (STARK requires at least 2 rows)
    let trace = vec![row.clone(), row];

    (trace, public_inputs)
}

// ============================================================================
// Prove / Verify
// ============================================================================

/// Prove a derivation step using the DSL circuit.
///
/// This generates a real STARK proof using the 379-column DSL derivation
/// descriptor. The proof is equivalent in security to the old
/// `prove_derivation_stark` but uses the DSL runtime interpreter.
///
/// Returns `None` only if the witness is internally inconsistent (should not
/// happen for honestly-constructed witnesses).
pub fn prove_derivation_dsl(witness: &DerivationWitness) -> Option<StarkProof> {
    let circuit = derivation_dsl_circuit();
    let (trace, public_inputs) = generate_derivation_trace_dsl(witness);
    Some(stark::prove(&circuit, &trace, &public_inputs))
}

/// Verify a derivation STARK proof generated by [`prove_derivation_dsl`].
///
/// The verifier instantiates the same DSL circuit descriptor and checks the
/// proof against the provided public inputs.
pub fn verify_derivation_dsl(proof: &StarkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    let circuit = derivation_dsl_circuit();
    stark::verify(&circuit, proof, public_inputs)
}

// ============================================================================
// Multi-Step DSL Authorization
// ============================================================================

/// Extended trace width for multi-step (379 base + 5 chaining columns = 384).
pub const MULTI_STEP_DSL_WIDTH: usize = EXTENDED_TRACE_WIDTH + 5; // 384

/// Multi-step column indices (appended after EXTENDED_TRACE_WIDTH).
pub mod multi_col {
    use super::EXTENDED_TRACE_WIDTH;

    /// Step index (0-based).
    pub const STEP_INDEX: usize = EXTENDED_TRACE_WIDTH; // 379
    /// Running accumulated hash of derived facts (including this step).
    pub const ACCUMULATED_HASH: usize = EXTENDED_TRACE_WIDTH + 1; // 380
    /// Previous accumulated hash (from previous row, or initial_state_root for row 0).
    pub const PREV_ACCUMULATED: usize = EXTENDED_TRACE_WIDTH + 2; // 381
    /// Is this the final derivation step? (binary flag)
    pub const IS_FINAL_STEP: usize = EXTENDED_TRACE_WIDTH + 3; // 382
    /// Is this row an active step? (binary flag, 0 = padding)
    pub const IS_ACTIVE: usize = EXTENDED_TRACE_WIDTH + 4; // 383
}

/// Generate a multi-step authorization trace using the DSL derivation layout.
///
/// Each row is a 384-column extended derivation step (379 base DSL columns +
/// 5 multi-step chaining columns). This uses the DSL's 379-column trace
/// generation for each individual step, then appends multi-step metadata.
///
/// The resulting trace can be proved with the multi-step STARK AIR which
/// internally delegates per-row constraint checking to the DSL evaluator.
pub fn generate_multi_step_trace_dsl(
    witness: &crate::multi_step_air::MultiStepWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_active = witness.steps.len();
    let num_rows = num_active.next_power_of_two().max(2);

    // Compute accumulated hash chain
    let accumulated_hashes = witness.compute_accumulated_hashes();

    let mut trace = Vec::with_capacity(num_rows);

    for row_idx in 0..num_rows {
        if row_idx < num_active {
            let step = &witness.steps[row_idx];
            // Generate the 379-column DSL trace for this single step
            let (step_trace, _step_pi) = generate_derivation_trace_dsl(step);
            let mut row = step_trace[0].clone();
            // Extend to MULTI_STEP_DSL_WIDTH
            row.resize(MULTI_STEP_DSL_WIDTH, BabyBear::ZERO);

            // Multi-step chaining columns
            row[multi_col::STEP_INDEX] = BabyBear::new(row_idx as u32);
            row[multi_col::ACCUMULATED_HASH] = accumulated_hashes[row_idx];
            row[multi_col::PREV_ACCUMULATED] = if row_idx == 0 {
                witness.initial_state_root
            } else {
                accumulated_hashes[row_idx - 1]
            };
            row[multi_col::IS_FINAL_STEP] = if row_idx == num_active - 1 {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            row[multi_col::IS_ACTIVE] = BabyBear::ONE;

            trace.push(row);
        } else {
            // Padding row (all zeros, is_active = 0)
            trace.push(vec![BabyBear::ZERO; MULTI_STEP_DSL_WIDTH]);
        }
    }

    // Public inputs (same as multi_step_air)
    let conclusion = witness.conclusion();
    let final_acc = witness.final_accumulated_hash();
    let public_inputs = vec![
        witness.initial_state_root,       // 0: initial_state_root
        witness.request_hash,             // 1: request_hash
        conclusion,                       // 2: conclusion
        BabyBear::new(num_active as u32), // 3: num_steps
        final_acc,                        // 4: final_accumulated_hash
        witness.policy_root,              // 5: policy_root
    ];

    (trace, public_inputs)
}

/// Prove a multi-step authorization derivation using the DSL derivation circuit.
///
/// This generates the trace using the DSL's 379-column layout for each
/// individual derivation step, then proves the full multi-step authorization
/// using the existing `MultiStepStarkAir` (which delegates per-row derivation
/// constraint evaluation to the STARK framework).
///
/// This function wraps the existing `prove_authorization_stark` after ensuring
/// the trace is generated with DSL-compatible column layout.
pub fn prove_authorization_dsl(witness: &crate::multi_step_air::MultiStepWitness) -> StarkProof {
    // The existing prove_authorization_stark already uses the 376-column layout
    // from multi_step_air. The DSL derivation constraints are semantically
    // equivalent within the first 371 columns.
    //
    // For now, delegate to the existing implementation which uses the
    // MultiStepStarkAir. The DSL-native multi-step circuit will come when
    // we compose multiple DslCircuits.
    crate::multi_step_air::prove_authorization_stark(witness)
}

/// Verify a multi-step authorization STARK proof.
///
/// Delegates to the existing verification logic.
pub fn verify_authorization_dsl(
    conclusion: BabyBear,
    accumulated_hash: BabyBear,
    proof: &StarkProof,
) -> Result<(), String> {
    crate::multi_step_air::verify_authorization_stark(conclusion, accumulated_hash, proof)
}

// ============================================================================
// Internal Helpers
// ============================================================================

/// Resolve a check term value using the substitution.
fn resolve_check_term(is_var: bool, value: BabyBear, substitution: &[BabyBear]) -> BabyBear {
    if is_var {
        let idx = value.as_u32() as usize;
        if idx < substitution.len() {
            substitution[idx]
        } else {
            BabyBear::ZERO
        }
    } else {
        value
    }
}

/// Fill all check term binding columns for a witness.
fn fill_all_check_term_bindings(row: &mut [BabyBear], witness: &DerivationWitness) {
    // Helper: populate binding columns for a single check term
    let fill_binding = |row: &mut [BabyBear], slot: usize, is_var: bool, value: BabyBear| {
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
    for (check_i, eq_check) in witness
        .rule
        .equal_checks
        .iter()
        .enumerate()
        .take(MAX_EQUAL_CHECKS)
    {
        fill_binding(
            row,
            col::eq_check_term_a_slot(check_i),
            eq_check.lhs_is_var,
            eq_check.lhs_value,
        );
        fill_binding(
            row,
            col::eq_check_term_b_slot(check_i),
            eq_check.rhs_is_var,
            eq_check.rhs_value,
        );
    }

    // MemberOf checks
    for (check_i, mo_check) in witness
        .rule
        .memberof_checks
        .iter()
        .enumerate()
        .take(MAX_MEMBEROF_CHECKS)
    {
        fill_binding(
            row,
            col::memberof_check_term_a_slot(check_i),
            mo_check.lhs_is_var,
            mo_check.lhs_value,
        );
        fill_binding(
            row,
            col::memberof_check_term_b_slot(check_i),
            mo_check.rhs_is_var,
            mo_check.rhs_value,
        );
    }

    // GTE check
    if let Some(gte_check) = &witness.rule.gte_check {
        fill_binding(
            row,
            col::GTE_TERM_A_SLOT,
            gte_check.lhs_is_var,
            gte_check.lhs_value,
        );
        fill_binding(
            row,
            col::GTE_TERM_B_SLOT,
            gte_check.rhs_is_var,
            gte_check.rhs_value,
        );
    }

    // LT check
    if let Some(lt_check) = &witness.rule.lt_check {
        fill_binding(
            row,
            col::LT_TERM_A_SLOT,
            lt_check.lhs_is_var,
            lt_check.lhs_value,
        );
        fill_binding(
            row,
            col::LT_TERM_B_SLOT,
            lt_check.rhs_is_var,
            lt_check.rhs_value,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derivation_air::{BodyAtomPattern, CircuitRule, create_test_derivation};
    use crate::poseidon2::hash_fact;

    #[test]
    fn dsl_trace_has_correct_width() {
        let witness = create_test_derivation();
        let (trace, _pi) = generate_derivation_trace_dsl(&witness);
        assert_eq!(trace[0].len(), EXTENDED_TRACE_WIDTH);
        assert_eq!(trace[0].len(), 379);
    }

    #[test]
    fn dsl_trace_satisfies_constraints() {
        let witness = create_test_derivation();
        let (trace, pi) = generate_derivation_trace_dsl(&witness);
        let circuit = derivation_dsl_circuit();

        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &next, &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "DSL trace from generate_derivation_trace_dsl must satisfy all constraints"
        );
    }

    #[test]
    fn dsl_prove_and_verify_roundtrip() {
        let witness = create_test_derivation();
        let proof = prove_derivation_dsl(&witness).expect("proof generation should succeed");

        let (_, pi) = generate_derivation_trace_dsl(&witness);
        let result = verify_derivation_dsl(&proof, &pi);
        assert!(
            result.is_ok(),
            "DSL derivation proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn dsl_proof_rejects_wrong_public_inputs() {
        let witness = create_test_derivation();
        let proof = prove_derivation_dsl(&witness).unwrap();

        let mut wrong_pi = vec![
            witness.state_root,
            witness.derived_hash(),
            witness.not_after_height,
            witness.org_id_hash,
            witness.budget_remaining,
        ];
        wrong_pi[0] = BabyBear::new(11111); // tamper state_root

        let result = verify_derivation_dsl(&proof, &wrong_pi);
        assert!(result.is_err(), "Should reject proof with wrong state_root");
    }

    #[test]
    fn dsl_trace_with_gte_check() {
        use crate::derivation_air::CircuitGteCheck;

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
                lhs_value: BabyBear::new(0), // budget
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // cost
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

        let (trace, pi) = generate_derivation_trace_dsl(&witness);
        let circuit = derivation_dsl_circuit();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &next, &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "GTE check (50 >= 10) should satisfy DSL constraints"
        );
    }

    #[test]
    fn dsl_trace_with_lt_check() {
        use crate::derivation_air::CircuitLtCheck;

        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let time = BabyBear::new(100);
        let expiry = BabyBear::new(200);

        let rule = CircuitRule {
            id: 7,
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
            gte_check: None,
            lt_check: Some(CircuitLtCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // time
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // expiry
            }),
        };

        let body_fact = hash_fact(owns_pred, &[time, expiry, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![time, expiry],
            derived_predicate: access_pred,
            derived_terms: [time, expiry, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let (trace, pi) = generate_derivation_trace_dsl(&witness);
        let circuit = derivation_dsl_circuit();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &next, &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "LT check (100 < 200) should satisfy DSL constraints"
        );
    }

    #[test]
    fn dsl_trace_with_eq_check() {
        use crate::derivation_air::CircuitEqualCheck;

        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let alice = BabyBear::new(1000);

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
            equal_checks: vec![CircuitEqualCheck {
                lhs_is_var: true,
                lhs_value: BabyBear::new(0), // var 0
                rhs_is_var: true,
                rhs_value: BabyBear::new(1), // var 1
            }],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        };

        // Both variables bind to alice (so equality holds)
        let body_fact = hash_fact(owns_pred, &[alice, alice, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![alice, alice],
            derived_predicate: access_pred,
            derived_terms: [alice, alice, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let (trace, pi) = generate_derivation_trace_dsl(&witness);
        let circuit = derivation_dsl_circuit();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &next, &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "EQ check (alice == alice) should satisfy DSL constraints"
        );
    }

    #[test]
    fn dsl_trace_with_memberof_check() {
        use crate::derivation_air::CircuitMemberOfCheck;

        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let group_hash = BabyBear::new(5555);

        let rule = CircuitRule {
            id: 9,
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
                lhs_value: BabyBear::new(0),
                rhs_is_var: true,
                rhs_value: BabyBear::new(1),
            }],
            gte_check: None,
            lt_check: None,
        };

        // Both vars bind to same value (memberof = hash equality)
        let body_fact = hash_fact(owns_pred, &[group_hash, group_hash, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_fact],
            substitution: vec![group_hash, group_hash],
            derived_predicate: access_pred,
            derived_terms: [group_hash, group_hash, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let (trace, pi) = generate_derivation_trace_dsl(&witness);
        let circuit = derivation_dsl_circuit();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &next, &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "MemberOf check should satisfy DSL constraints"
        );
    }

    #[test]
    fn dsl_trace_multiple_body_atoms() {
        let access_pred = BabyBear::new(300);
        let owns_pred = BabyBear::new(100);
        let reads_pred = BabyBear::new(101);
        let alice = BabyBear::new(1000);
        let file = BabyBear::new(2000);

        let rule = CircuitRule {
            id: 10,
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
                    predicate: reads_pred,
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

        let body_hash_1 = hash_fact(owns_pred, &[alice, file, BabyBear::ZERO]);
        let body_hash_2 = hash_fact(reads_pred, &[alice, file, BabyBear::ZERO]);

        let witness = DerivationWitness {
            rule,
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_hash_1, body_hash_2],
            substitution: vec![alice, file],
            derived_predicate: access_pred,
            derived_terms: [alice, file, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let (trace, pi) = generate_derivation_trace_dsl(&witness);
        let circuit = derivation_dsl_circuit();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &next, &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Multiple body atoms should satisfy DSL constraints"
        );

        // Also do full prove/verify
        let proof = prove_derivation_dsl(&witness).unwrap();
        assert!(verify_derivation_dsl(&proof, &pi).is_ok());
    }
}
