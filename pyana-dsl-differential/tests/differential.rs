//! Cross-backend differential test entry point.
//!
//! For each canonical predicate × each curated input case, drive every
//! backend's verifier and assert they all agree on accept/reject. Skipped
//! backends (Midnight, SP1) are linted for emit well-formedness but do
//! not contribute to the consensus vote.

use pyana_dsl_differential::agreement::AgreementMatrix;
use pyana_dsl_differential::harness::run_case;
use pyana_dsl_differential::predicates::{all_specs, lookup};

#[test]
fn cross_backend_differential() {
    let mut matrix = AgreementMatrix::new();
    let mut total_cases = 0usize;

    for spec in all_specs() {
        let handles = lookup(spec.name)
            .unwrap_or_else(|| panic!("no backend handles for predicate `{}`", spec.name));
        let cases = (spec.cases)();
        for case in &cases {
            total_cases += 1;
            let row = run_case(spec.name, case, &handles);
            matrix.push(row);
        }
    }

    eprintln!("Ran {total_cases} differential cases across 7 backends");
    eprintln!("{}", matrix.summary());

    matrix.assert_all_agree();
}
