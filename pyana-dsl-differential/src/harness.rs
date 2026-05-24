//! Driver that runs each backend's verifier against one [`PredicateCase`]
//! and records the verdicts in a [`RowReport`].

use crate::agreement::{BackendName, BackendVerdict, RowReport};
use crate::air_runner;
use crate::datalog_eval;
use crate::kimchi_sim;
use crate::midnight_lint;
use crate::plonky3_runner;
use crate::predicates::{BackendHandles, PredicateCase};
use crate::sp1_lint;

/// Backend identifiers used in the agreement matrix.
pub const BK_RUST: BackendName = BackendName("gen_rust");
pub const BK_DATALOG: BackendName = BackendName("gen_datalog");
pub const BK_AIR: BackendName = BackendName("gen_air");
pub const BK_KIMCHI: BackendName = BackendName("gen_kimchi");
pub const BK_PLONKY3: BackendName = BackendName("gen_plonky3");
pub const BK_MIDNIGHT: BackendName = BackendName("gen_midnight");
pub const BK_SP1: BackendName = BackendName("gen_sp1");

/// Drive one case through every backend, returning the populated row.
pub fn run_case(
    predicate_name: &'static str,
    case: &PredicateCase,
    handles: &BackendHandles,
) -> RowReport {
    let mut row = RowReport::new(predicate_name, case.label.clone());

    // gen_rust: source of truth.
    let rust_verdict = match (case.rust_eval)() {
        Ok(()) => BackendVerdict::Accept,
        Err(_) => BackendVerdict::Reject,
    };
    row.record(BK_RUST, rust_verdict);

    // gen_datalog: re-evaluate the emitted rule with bindings drawn
    // directly from the case's named inputs.
    let datalog_bindings = datalog_eval::bindings_from_inputs(&case.inputs);
    let datalog_verdict = match datalog_eval::evaluate(handles.datalog_rule, &datalog_bindings) {
        Ok(true) => BackendVerdict::Accept,
        Ok(false) => BackendVerdict::Reject,
        Err(msg) => BackendVerdict::Error(msg),
    };
    row.record(BK_DATALOG, datalog_verdict);

    // gen_air: re-derive from descriptor + diff_witness.
    let air_verdict = match air_runner::evaluate(&handles.air, &case.body.requirements) {
        Ok(true) => BackendVerdict::Accept,
        Ok(false) => BackendVerdict::Reject,
        Err(msg) => BackendVerdict::Error(msg),
    };
    row.record(BK_AIR, air_verdict);

    // gen_kimchi: simulator.
    let kimchi_verdict = match kimchi_sim::evaluate(&handles.kimchi, &case.body.requirements) {
        Ok(true) => BackendVerdict::Accept,
        Ok(false) => BackendVerdict::Reject,
        Err(msg) => BackendVerdict::Error(msg),
    };
    row.record(BK_KIMCHI, kimchi_verdict);

    // gen_plonky3: prove + verify.
    let plonky3_verdict = match plonky3_runner::prove_and_verify(&case.body.requirements) {
        Ok(plonky3_runner::Verdict::Accept) => BackendVerdict::Accept,
        Ok(plonky3_runner::Verdict::Reject) => BackendVerdict::Reject,
        Ok(plonky3_runner::Verdict::Skip { reason }) => BackendVerdict::Skip { reason },
        Err(msg) => BackendVerdict::Error(msg),
    };
    row.record(BK_PLONKY3, plonky3_verdict);

    // Param names for the lint passes — every named input gets a wire in
    // ZKIR and an `sp1_zkvm::io::read` site in the SP1 guest.
    let param_names: Vec<&str> = case
        .inputs
        .u64s
        .iter()
        .map(|(n, _)| *n)
        .chain(case.inputs.bytes.iter().map(|(n, _)| *n))
        .chain(case.inputs.sets.iter().map(|(n, _)| *n))
        .collect();

    // gen_midnight: lint only.
    let midnight_verdict = match midnight_lint::lint(handles.midnight_zkir, &param_names) {
        Ok(()) => BackendVerdict::Skip {
            reason: "Midnight ZKIR v3 requires off-chain proof server; emitted JSON linted only",
        },
        Err(msg) => BackendVerdict::Error(msg),
    };
    row.record(BK_MIDNIGHT, midnight_verdict);

    // gen_sp1: lint only.
    let sp1_verdict = match sp1_lint::lint(handles.sp1_guest, &param_names) {
        Ok(()) => BackendVerdict::Skip {
            reason: "SP1 guest requires sp1-prove / RISC-V toolchain; emitted source linted only",
        },
        Err(msg) => BackendVerdict::Error(msg),
    };
    row.record(BK_SP1, sp1_verdict);

    row
}
