//! Cross-backend differential test entry point.
//!
//! For each canonical predicate × each curated input case, drive every
//! backend's verifier and assert they all agree on accept/reject. Skipped
//! backends (Midnight, SP1) are linted for emit well-formedness but do
//! not contribute to the consensus vote.

use pyana_dsl_differential::agreement::AgreementMatrix;
use pyana_dsl_differential::harness::run_case;
use pyana_dsl_differential::predicates::{all_specs, lookup};

/// Per-predicate param-name lists used by the Datalog evaluator and the
/// lint passes. These mirror the parameter names declared in
/// `pyana-dsl-differential/src/predicates.rs` `#[pyana_caveat]` bodies.
fn param_names_for(predicate: &str) -> &'static [&'static str] {
    match predicate {
        "diff_not_after" => &["token_expiry", "current_time"],
        "diff_minimum_balance" => &["balance", "threshold"],
        "diff_exact_equal_u64" => &["expected", "actual"],
        "diff_distinct_u64" => &["a", "b"],
        "diff_exact_equal_bytes" => &["expected", "actual"],
        "diff_distinct_bytes" => &["a", "b"],
        "diff_conjunction" => &["balance", "threshold", "sender", "receiver"],
        "diff_window" => &["low", "mid", "high"],
        "diff_set_member" => &["allowed", "candidate"],
        "diff_set_member_and_floor" => &["allowed", "candidate", "floor"],
        "diff_triple_equal" => &["a", "b", "c"],
        _ => &[],
    }
}

#[test]
fn cross_backend_differential() {
    let mut matrix = AgreementMatrix::new();
    let mut total_cases = 0usize;

    for spec in all_specs() {
        let handles = match lookup(spec.name) {
            Some(h) => h,
            None => panic!("no backend handles for predicate `{}`", spec.name),
        };
        let cases = (spec.cases)();
        let names = param_names_for(spec.name);
        for case in &cases {
            total_cases += 1;
            let row = run_case(spec.name, case, &handles, names);
            matrix.push(row);
        }
    }

    eprintln!("Ran {total_cases} differential cases across 7 backends");
    eprintln!("{}", matrix.summary());

    matrix.assert_all_agree();
}
