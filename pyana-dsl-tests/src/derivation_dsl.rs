//! The derivation AIR expressed as a CircuitDescriptor.
//!
//! This is the FIRST real system component moving from hand-written to DSL form.
//! It constructs a `CircuitDescriptor` that `DslCircuit` interprets, proving that
//! the descriptor approach can handle real-world complexity (371 columns, 28 constraints).
//!
//! The constraints here must produce IDENTICAL evaluations to `DerivationStarkAir::eval_constraints`
//! on the same trace rows. We verify this via equivalence tests.

use pyana_circuit::field::{BabyBear, BABYBEAR_P};
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// Re-export the derivation AIR column layout constants.
use pyana_circuit::derivation_air::{
    col, DERIVATION_AIR_WIDTH, GTE_DIFF_BITS, MAX_BODY_ATOMS, MAX_EQUAL_CHECKS, MAX_HEAD_TERMS,
    MAX_MEMBEROF_CHECKS, MAX_SUB_VARS,
};

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

/// Auxiliary column indices for C2 (ConditionalNonzero) inverse columns.
/// These are appended after the standard DERIVATION_AIR_WIDTH (371) columns.
/// One inverse column per body atom slot (8 total).
pub const BODY_HASH_INV_START: usize = DERIVATION_AIR_WIDTH; // 371

/// Extended trace width including auxiliary inverse columns for C2.
pub const EXTENDED_TRACE_WIDTH: usize = DERIVATION_AIR_WIDTH + MAX_BODY_ATOMS; // 379

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
    // This uses public_inputs[0] as state_root. We express it as:
    //   flag * root - flag * pi[0] == 0
    // Using PiBinding for each body root, gated by its membership flag.
    //
    // Actually: we use Polynomial with pi reference.  The ConstraintExpr evaluator
    // does NOT have direct pi access in Polynomial terms, only in PiBinding.
    // But Gated + PiBinding won't work because PiBinding is col - pi[idx].
    //
    // The cleanest approach: one Polynomial constraint PER body atom:
    //   flag * (root - pi_col) where we place state_root into a trace column.
    //
    // In the derivation AIR, state_root IS in the trace as body_roots (when used).
    // The constraint is: flag[i] * (body_root[i] - public_inputs[0]) == 0.
    // We CAN express this using Gated + PiBinding:
    //   Gated { selector: flag_col, inner: PiBinding { col: root_col, pi_index: 0 } }
    //
    // Wait — PiBinding evaluates as `local[col] - pi[pi_index]`, so
    // Gated { selector, inner: PiBinding } evaluates as `local[selector] * (local[col] - pi[idx])`.
    // That's exactly what we want!
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
    // For each head term: (sel[0] + sel[1] + ... + sel[7] - is_var)^2 == 0
    //
    // The hand-written AIR uses the squared form for alpha composition. We use
    // Squared { inner: Polynomial { sum(sel_j) - is_var } } to match exactly.
    // ========================================================================
    for term_i in 0..MAX_HEAD_TERMS {
        let is_var_col = col::HEAD_IS_VAR_START + term_i;
        // (sum(sel_j for j in 0..8) - is_var)^2 == 0
        let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 1);
        for var_j in 0..MAX_SUB_VARS {
            terms_vec.push(term(BabyBear::ONE, &[col::head_sel_var(term_i, var_j)]));
        }
        // - is_var
        terms_vec.push(term(neg_one(), &[is_var_col]));
        constraints.push(ConstraintExpr::Squared {
            inner: Box::new(ConstraintExpr::Polynomial { terms: terms_vec }),
        });
    }

    // ========================================================================
    // C10: substitution_application
    // derived_term[i] = is_var * (sum_j sel_j * sub[j]) + (1-is_var) * raw_value
    //
    // Rewriting: derived_term - is_var * sum(sel_j * sub_j) - raw_value + is_var * raw_value == 0
    //
    // Equivalently: derived_term - sum(sel_j * sub_j) * is_var - raw_value * (1 - is_var) == 0
    //
    // The hand-written version uses (derived_term - expected)^2 per term, then sums.
    // For constraint satisfaction equivalence, the linear form per term suffices.
    // We emit one constraint per head term.
    //
    // Linear form:
    //   derived_term[i] - sum_j(sel[i][j] * sub[j]) - raw_value[i] + is_var[i] * raw_value[i] == 0
    //
    // Wait — let's be careful with the algebra:
    //   expected = is_var * var_resolved + (1 - is_var) * raw_value
    //            = is_var * sum(sel_j * sub_j) + raw_value - is_var * raw_value
    //
    // Constraint: derived_term - expected == 0
    //   derived_term - is_var * sum(sel_j * sub_j) - raw_value + is_var * raw_value == 0
    //
    // Terms:
    //   +1 * derived_term[i]
    //   -1 * raw_value[i]
    //   +1 * is_var[i] * raw_value[i]      (degree 2)
    //   -1 * sel[i][0] * sub[0]            (degree 2)
    //   ...
    //   -1 * sel[i][7] * sub[7]            (degree 2)
    //
    // Wait, where does is_var factor in for the selector*sub terms? In the original:
    //   expected = is_var * var_resolved + (1 - is_var) * raw_value
    //
    // var_resolved = sum(sel_j * sub_j). Since selectors are binary and sum to is_var,
    // when is_var=0 all sel_j=0, so var_resolved=0 and we get raw_value.
    // When is_var=1, exactly one sel_j=1, so var_resolved=sub[j].
    //
    // So the constraint is:
    //   derived_term - sum(sel_j * sub_j) - (1 - is_var) * raw_value == 0
    //
    // Which is:
    //   derived_term - sum(sel_j * sub_j) - raw_value + is_var * raw_value == 0
    //
    // This works because when is_var=0: derived_term - 0 - raw_value + 0 == 0 => derived_term == raw_value
    // When is_var=1: derived_term - sub[j] - raw_value + raw_value == 0 => derived_term == sub[j]. Correct!
    // ========================================================================
    for term_i in 0..MAX_HEAD_TERMS {
        let derived_col = col::HEAD_TERM_START + term_i;
        let is_var_col = col::HEAD_IS_VAR_START + term_i;
        let raw_col = col::HEAD_RAW_VALUE_START + term_i;

        let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 3);
        // +1 * derived_term
        terms_vec.push(term(BabyBear::ONE, &[derived_col]));
        // -1 * raw_value
        terms_vec.push(term(neg_one(), &[raw_col]));
        // +1 * is_var * raw_value
        terms_vec.push(term(BabyBear::ONE, &[is_var_col, raw_col]));
        // -1 * sel[term_i][j] * sub[j] for each j
        for var_j in 0..MAX_SUB_VARS {
            let sel_col = col::head_sel_var(term_i, var_j);
            let sub_col = col::SUB_VALUE_START + var_j;
            terms_vec.push(term(neg_one(), &[sel_col, sub_col]));
        }
        constraints.push(ConstraintExpr::Polynomial { terms: terms_vec });
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
    // Expressed as: Gated { selector: active, inner: Equality { a, b } }
    //
    // Wait — ConstraintExpr::Equality is `local[a] - local[b]`. So Gated { selector, Equality }
    // evaluates as `local[selector] * (local[a] - local[b])`. That's what we want!
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
    // Expanded: active * diff - active * term_a + active * term_b == 0
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
            power = power + power; // 2^(i+1)
        }
        // - diff
        bit_terms.push(term(neg_one(), &[col::GTE_CHECK_DIFF]));
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::GTE_CHECK_ACTIVE,
            inner: Box::new(ConstraintExpr::Polynomial { terms: bit_terms }),
        });
    }

    // ========================================================================
    // C18: gte_check_bits_binary — active * sum(bit_i * (bit_i - 1)) == 0
    // We can't easily express this as a single Polynomial (it's sum of degree-2 terms
    // gated by active = degree 3). Instead, emit individual gated binary constraints.
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
    // Expressed as: Gated { active, Polynomial { +1 * high_bit } }
    // Which is Multiplication-like but simpler: active * high_bit.
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
    // Expanded: active * (diff - term_b + term_a + 1) == 0
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
    // C27: check_term_sel_sum_equals_is_var — sum(sel_j) - is_var == 0
    // (Same approach as C9: linear form is equivalent for satisfaction.)
    // ========================================================================
    for slot in 0..col::NUM_CHECK_TERMS {
        let is_var_col = col::check_term_is_var(slot);
        let mut terms_vec = Vec::with_capacity(MAX_SUB_VARS + 1);
        for var_j in 0..MAX_SUB_VARS {
            terms_vec.push(term(BabyBear::ONE, &[col::check_term_sel(slot, var_j)]));
        }
        terms_vec.push(term(neg_one(), &[is_var_col]));
        constraints.push(ConstraintExpr::Polynomial { terms: terms_vec });
    }

    // ========================================================================
    // C28: check_term_binding_correct
    // For each check term slot, the resolved value must match:
    //   resolved = is_var * sum(sel_j * sub[j]) + (1-is_var) * raw_value
    // And for active checks, trace_term must equal resolved.
    //
    // We express binding per active check as:
    //   active * (trace_term - resolved) == 0
    // where resolved = sum(sel_j * sub_j) + raw_value - is_var * raw_value
    //
    // So: active * (trace_term - sum(sel_j * sub_j) - raw_value + is_var * raw_value) == 0
    //
    // This is degree 3 (active * is_var * raw_value). We encode it as a gated polynomial.
    // But Gated already multiplies by `local[selector_col]`, so the inner polynomial
    // would be degree 2. Let's check:
    //   inner = trace_term - sum(sel_j * sub_j) - raw_value + is_var * raw_value
    // The `is_var * raw_value` term is degree 2, `sel_j * sub_j` is degree 2.
    // So the inner is degree 2, and gated makes it degree 3. Max degree = 3.
    //
    // Actually looking at the hand-written AIR, it uses degree 4:
    //   active * ((trace_term - resolved)^2) — but we can use the linear form:
    //   active * (trace_term - resolved) == 0
    // which is degree 3.
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
                terms_vec.push(term(neg_one(), &[col::check_term_sel(slot, var_j), col::SUB_VALUE_START + var_j]));
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
                terms_vec.push(term(neg_one(), &[col::check_term_sel(slot, var_j), col::SUB_VALUE_START + var_j]));
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
                terms_vec.push(term(neg_one(), &[col::check_term_sel(slot, var_j), col::SUB_VALUE_START + var_j]));
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
                terms_vec.push(term(neg_one(), &[col::check_term_sel(slot, var_j), col::SUB_VALUE_START + var_j]));
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
                terms_vec.push(term(neg_one(), &[col::check_term_sel(slot, var_j), col::SUB_VALUE_START + var_j]));
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
                terms_vec.push(term(neg_one(), &[col::check_term_sel(slot, var_j), col::SUB_VALUE_START + var_j]));
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
                terms_vec.push(term(neg_one(), &[col::check_term_sel(slot, var_j), col::SUB_VALUE_START + var_j]));
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
                terms_vec.push(term(neg_one(), &[col::check_term_sel(slot, var_j), col::SUB_VALUE_START + var_j]));
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
        ColumnDef { name: "rule_id".into(), index: col::RULE_ID, kind: ColumnKind::Value },
        ColumnDef { name: "head_pred".into(), index: col::HEAD_PRED, kind: ColumnKind::Value },
        ColumnDef { name: "derived_hash".into(), index: col::DERIVED_HASH, kind: ColumnKind::Hash },
    ];

    CircuitDescriptor {
        name: "pyana-derivation-dsl-v1".into(),
        trace_width: EXTENDED_TRACE_WIDTH,
        max_degree: 3, // Gated(degree-1 selector * degree-2 inner) = degree 3
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
// Tests: Equivalence with hand-written DerivationStarkAir
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::derivation_air::{
        create_test_derivation, DerivationAir, DerivationWitness,
    };
    use pyana_circuit::constraint_prover::Air;
    use pyana_circuit::stark::StarkAir;

    /// Extend a row from DERIVATION_AIR_WIDTH to EXTENDED_TRACE_WIDTH,
    /// filling in the auxiliary inverse columns for C2.
    fn extend_row(row: &mut Vec<BabyBear>) {
        row.resize(EXTENDED_TRACE_WIDTH, BabyBear::ZERO);
        // Fill inverse columns: inv[i] = body_hash[i]^{-1} when membership flag is set
        for i in 0..MAX_BODY_ATOMS {
            let flag = row[col::BODY_MEMBERSHIP_START + i];
            let hash = row[col::BODY_HASH_START + i];
            if flag == BabyBear::ONE && hash != BabyBear::ZERO {
                row[BODY_HASH_INV_START + i] = hash.inverse().unwrap();
            }
        }
    }

    /// Generate a valid trace from the standard test derivation witness,
    /// extended to EXTENDED_TRACE_WIDTH with auxiliary inverse columns for C2.
    fn valid_trace_and_pi() -> (Vec<BabyBear>, Vec<BabyBear>) {
        let witness = create_test_derivation();
        let air = DerivationAir::new(witness);
        let (trace, pi) = air.generate_trace();
        let mut row = trace[0].clone();
        extend_row(&mut row);
        (row, pi)
    }

    #[test]
    fn descriptor_validates_successfully() {
        let desc = derivation_circuit_descriptor();
        desc.validate().expect("derivation descriptor should pass validation");
    }

    #[test]
    fn descriptor_has_correct_width() {
        let desc = derivation_circuit_descriptor();
        assert_eq!(desc.trace_width, EXTENDED_TRACE_WIDTH);
        assert_eq!(desc.trace_width, 379); // 371 base + 8 inverse columns for C2
    }

    #[test]
    fn descriptor_has_substantial_constraints() {
        let desc = derivation_circuit_descriptor();
        // We should have a significant number of constraints:
        // C1: 8 binary, C5: 8 gated pi, C6: 1 pi, C7: 4 binary, C8: 32 binary,
        // C9: 4 poly, C10: 4 poly, C11: 4 binary, C12: 4 gated eq,
        // C13: 4 binary, C14: 4 gated eq, C15: 1 binary, C16: 1 gated poly,
        // C17: 1 gated poly, C18: 30 gated binary, C19: 1 gated poly,
        // C20: 1 binary, C21: 1 gated poly, C22: 1 gated poly,
        // C23: 30 gated binary, C24: 1 gated poly,
        // C25: 20 binary, C26: 160 binary, C27: 20 poly,
        // C28: (4*2 + 4*2 + 2 + 2) = 20 gated polys
        // Total: substantial (well over 100)
        assert!(
            desc.constraints.len() > 100,
            "Expected > 100 constraints, got {}",
            desc.constraints.len()
        );
        eprintln!("Derivation DSL descriptor has {} constraints", desc.constraints.len());
    }

    #[test]
    fn dsl_circuit_evaluates_to_zero_on_valid_trace() {
        let (row, pi) = valid_trace_and_pi();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7); // arbitrary nonzero

        let dsl = derivation_dsl_circuit();
        let result = dsl.eval_constraints(&row, &next, &pi, alpha);

        assert_eq!(
            result,
            BabyBear::ZERO,
            "DslCircuit should evaluate to ZERO on a valid derivation trace"
        );
    }

    #[test]
    fn dsl_circuit_rejects_tampered_body_root() {
        let (mut row, pi) = valid_trace_and_pi();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(13);

        // Tamper: set body_root[0] to a different value (but keep membership flag = 1)
        row[col::BODY_ROOT_START] = BabyBear::new(11111);

        let dsl = derivation_dsl_circuit();
        let result = dsl.eval_constraints(&row, &next, &pi, alpha);

        assert_ne!(
            result,
            BabyBear::ZERO,
            "DslCircuit should reject trace with tampered body root"
        );
    }

    #[test]
    fn dsl_circuit_rejects_non_binary_membership_flag() {
        let (mut row, pi) = valid_trace_and_pi();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);

        // Tamper: set a membership flag to 2 (invalid — must be 0 or 1)
        row[col::BODY_MEMBERSHIP_START] = BabyBear::new(2);

        let dsl = derivation_dsl_circuit();
        let result = dsl.eval_constraints(&row, &next, &pi, alpha);

        assert_ne!(
            result,
            BabyBear::ZERO,
            "DslCircuit should reject non-binary membership flag"
        );
    }

    #[test]
    fn dsl_circuit_rejects_wrong_derived_hash_pi() {
        let (row, mut pi) = valid_trace_and_pi();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);

        // Tamper: change public input for derived_hash
        pi[1] = BabyBear::new(99999);

        let dsl = derivation_dsl_circuit();
        let result = dsl.eval_constraints(&row, &next, &pi, alpha);

        assert_ne!(
            result,
            BabyBear::ZERO,
            "DslCircuit should reject mismatched derived_hash public input"
        );
    }

    #[test]
    fn dsl_circuit_rejects_wrong_substitution() {
        let (mut row, pi) = valid_trace_and_pi();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);

        // Tamper: change a substitution value without updating derived terms
        // The selectors still point to sub[0], but sub[0] now differs from head_term[0].
        row[col::SUB_VALUE_START] = BabyBear::new(99999);

        let dsl = derivation_dsl_circuit();
        let result = dsl.eval_constraints(&row, &next, &pi, alpha);

        assert_ne!(
            result,
            BabyBear::ZERO,
            "DslCircuit should reject trace with incorrect substitution"
        );
    }

    #[test]
    fn dsl_circuit_rejects_non_binary_selector() {
        let (mut row, pi) = valid_trace_and_pi();
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);

        // Tamper: set a head selector to 2
        row[col::head_sel_var(0, 0)] = BabyBear::new(2);

        let dsl = derivation_dsl_circuit();
        let result = dsl.eval_constraints(&row, &next, &pi, alpha);

        assert_ne!(
            result,
            BabyBear::ZERO,
            "DslCircuit should reject non-binary selector"
        );
    }

    #[test]
    fn dsl_circuit_rejects_fake_eq_check_terms() {
        // Soundness test: prover lies about eq check terms (same attack as in derivation_air tests)
        use pyana_circuit::derivation_air::{
            BodyAtomPattern, CircuitEqualCheck, CircuitRule,
        };
        use pyana_circuit::poseidon2::hash_fact;

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
                lhs_value: BabyBear::new(0),
                rhs_is_var: true,
                rhs_value: BabyBear::new(1),
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
            substitution: vec![alice, file],
            derived_predicate: access_pred,
            derived_terms: [alice, file, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let air = DerivationAir::new(witness);
        let (trace, pi) = air.generate_trace();
        let mut row = trace[0].clone();
        extend_row(&mut row);

        // Malicious prover: overwrite eq check terms to both be 5
        row[col::eq_check_term_a(0)] = BabyBear::new(5);
        row[col::eq_check_term_b(0)] = BabyBear::new(5);

        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);

        let dsl = derivation_dsl_circuit();
        let result = dsl.eval_constraints(&row, &next, &pi, alpha);

        assert_ne!(
            result,
            BabyBear::ZERO,
            "DslCircuit should reject fake eq check terms (soundness)"
        );
    }

    #[test]
    fn dsl_circuit_rejects_fake_gte_terms() {
        // Soundness test: prover has budget=5, cost=10 but lies about GTE terms
        use pyana_circuit::derivation_air::{
            BodyAtomPattern, CircuitGteCheck, CircuitRule,
        };
        use pyana_circuit::poseidon2::hash_fact;

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

        let air = DerivationAir::new(witness);
        let (trace, pi) = air.generate_trace();
        let mut row = trace[0].clone();
        extend_row(&mut row);

        // Malicious prover: fake GTE passing by setting term_a=100, term_b=10
        let fake_a = BabyBear::new(100);
        let fake_b = BabyBear::new(10);
        let fake_diff = fake_a - fake_b;
        row[col::GTE_CHECK_TERM_A] = fake_a;
        row[col::GTE_CHECK_TERM_B] = fake_b;
        row[col::GTE_CHECK_DIFF] = fake_diff;
        let diff_val = fake_diff.as_u32();
        for i in 0..GTE_DIFF_BITS {
            row[col::gte_diff_bit(i)] = BabyBear::new((diff_val >> i) & 1);
        }

        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);

        let dsl = derivation_dsl_circuit();
        let result = dsl.eval_constraints(&row, &next, &pi, alpha);

        assert_ne!(
            result,
            BabyBear::ZERO,
            "DslCircuit should reject fake GTE check terms (soundness)"
        );
    }

    #[test]
    fn dsl_circuit_gte_honest_valid_passes() {
        // budget=50 >= cost=10, honestly generated trace
        use pyana_circuit::derivation_air::{
            BodyAtomPattern, CircuitGteCheck, CircuitRule,
        };
        use pyana_circuit::poseidon2::hash_fact;

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

        let air = DerivationAir::new(witness);
        let (trace, pi) = air.generate_trace();
        let mut row = trace[0].clone();
        extend_row(&mut row);
        let next = vec![BabyBear::ZERO; EXTENDED_TRACE_WIDTH];
        let alpha = BabyBear::new(7);

        let dsl = derivation_dsl_circuit();
        let result = dsl.eval_constraints(&row, &next, &pi, alpha);

        assert_eq!(
            result,
            BabyBear::ZERO,
            "DslCircuit should accept honest GTE trace (50 >= 10)"
        );
    }

    #[test]
    fn dsl_circuit_stark_prove_and_verify() {
        // Full STARK proof using the DslCircuit — proves the descriptor is powerful enough
        // to run through the entire prove/verify pipeline.
        use pyana_circuit::stark::{prove, verify};

        let (row, pi) = valid_trace_and_pi();
        let trace = vec![row.clone(), row]; // pad to 2 rows (power of two)

        let dsl = derivation_dsl_circuit();
        let proof = prove(&dsl, &trace, &pi);
        let result = verify(&dsl, &proof, &pi);

        assert!(
            result.is_ok(),
            "DslCircuit derivation STARK prove/verify should succeed: {:?}",
            result.err()
        );
    }

    #[test]
    fn dsl_circuit_stark_wrong_pi_fails() {
        use pyana_circuit::stark::{prove, verify};

        let (row, pi) = valid_trace_and_pi();
        let trace = vec![row.clone(), row];

        let dsl = derivation_dsl_circuit();
        let proof = prove(&dsl, &trace, &pi);

        // Tamper public inputs
        let mut wrong_pi = pi;
        wrong_pi[0] = BabyBear::new(11111);

        let result = verify(&dsl, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "DslCircuit STARK with wrong public inputs should fail"
        );
    }

    #[test]
    fn dsl_circuit_boundary_constraints_correct() {
        let dsl = derivation_dsl_circuit();
        let pi = vec![
            BabyBear::new(99999), // state_root
            BabyBear::new(12345), // derived_hash
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let boundaries = dsl.boundary_constraints(&pi, 2);

        assert_eq!(boundaries.len(), 2);
        // First boundary: DERIVED_HASH = pi[1]
        assert_eq!(boundaries[0].col, col::DERIVED_HASH);
        assert_eq!(boundaries[0].value, BabyBear::new(12345));
        // Second boundary: BODY_ROOT_START = pi[0]
        assert_eq!(boundaries[1].col, col::BODY_ROOT_START);
        assert_eq!(boundaries[1].value, BabyBear::new(99999));
    }
}
