//! Dregg Golden Master Preflight
//!
//! End-to-end integration test gate for devnet -> testnet -> mainnet promotion.
//! Exercises EVERY major subsystem: federation boot, cell lifecycle, turn execution,
//! proof generation/verification, privacy stack, capabilities, intents, apps,
//! proof composition, federation state, sovereign cells, and cross-backend proofs.
//!
//! Run as a binary:
//!   cargo run -p dregg-preflight
//!
//! Run as a test:
//!   cargo test -p dregg-preflight

mod checks;
mod report;

use std::time::Instant;

use report::{PreflightReport, SubsystemResult, run_subsystem};

fn run_all_subsystems() -> Vec<SubsystemResult> {
    vec![
        run_subsystem("Boot", checks::boot::run()),
        run_subsystem("Cell lifecycle", checks::cells::run()),
        run_subsystem("Turn execution", checks::turns::run()),
        run_subsystem("Proofs", checks::proofs::run()),
        run_subsystem("Effect VM", checks::effect_vm::run()),
        run_subsystem("Privacy", checks::privacy::run()),
        run_subsystem("Capabilities", checks::caps::run()),
        run_subsystem("Intents", checks::intents::run()),
        run_subsystem("Apps", checks::apps::run()),
        run_subsystem("Composition", checks::composition::run()),
        run_subsystem("Federation", checks::federation::run()),
        run_subsystem("Blocklace", checks::blocklace::run()),
        run_subsystem("Factory & Sovereign", checks::sovereign::run()),
        run_subsystem("Cross-backend", checks::backends::run()),
        run_subsystem("CapTP", checks::captp::run()),
        run_subsystem("DFA Routing", checks::routing::run()),
        run_subsystem("Storage", checks::storage::run()),
        run_subsystem("Nameservice", checks::nameservice::run()),
        run_subsystem("Relay", checks::relay::run()),
        run_subsystem("CLI", checks::cli::run()),
        run_subsystem("Node", checks::node::run()),
        run_subsystem("Wire Protocol", checks::wire::run()),
        run_subsystem("Solver", checks::solver::run()),
        run_subsystem("Bridges", checks::bridges::run()),
        run_subsystem("Demo-Agent Examples", checks::demo_agent::run()),
        run_subsystem("StateConstraint surface", checks::state_constraints::run()),
    ]
}

fn main() {
    let start = Instant::now();
    let subsystems = run_all_subsystems();
    let total_duration = start.elapsed();

    let report = PreflightReport {
        subsystems,
        total_duration,
    };

    print!("{report}");

    if !report.all_passed() {
        std::process::exit(1);
    }
}

// ===========================================================================
// Test harness: same checks, but as #[test] functions for `cargo test`
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_all_passed(name: &str, results: Vec<CheckResult>) {
        for r in &results {
            assert!(r.passed, "{name}::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_boot() {
        assert_all_passed("boot", checks::boot::run());
    }

    #[test]
    fn preflight_cells() {
        assert_all_passed("cells", checks::cells::run());
    }

    #[test]
    fn preflight_turns() {
        assert_all_passed("turns", checks::turns::run());
    }

    #[test]
    fn preflight_proofs() {
        assert_all_passed("proofs", checks::proofs::run());
    }

    #[test]
    fn preflight_privacy() {
        assert_all_passed("privacy", checks::privacy::run());
    }

    #[test]
    fn preflight_caps() {
        assert_all_passed("caps", checks::caps::run());
    }

    #[test]
    fn preflight_intents() {
        assert_all_passed("intents", checks::intents::run());
    }

    #[test]
    fn preflight_apps() {
        assert_all_passed("apps", checks::apps::run());
    }

    #[test]
    fn preflight_composition() {
        assert_all_passed("composition", checks::composition::run());
    }

    #[test]
    fn preflight_federation() {
        assert_all_passed("federation", checks::federation::run());
    }

    #[test]
    fn preflight_sovereign() {
        assert_all_passed("sovereign", checks::sovereign::run());
    }

    #[test]
    fn preflight_effect_vm() {
        assert_all_passed("effect_vm", checks::effect_vm::run());
    }

    #[test]
    fn preflight_blocklace() {
        assert_all_passed("blocklace", checks::blocklace::run());
    }

    #[test]
    fn preflight_backends() {
        assert_all_passed("backends", checks::backends::run());
    }

    #[test]
    fn preflight_captp() {
        assert_all_passed("captp", checks::captp::run());
    }

    #[test]
    fn preflight_routing() {
        assert_all_passed("routing", checks::routing::run());
    }

    #[test]
    fn preflight_storage() {
        assert_all_passed("storage", checks::storage::run());
    }

    #[test]
    fn preflight_nameservice() {
        assert_all_passed("nameservice", checks::nameservice::run());
    }

    #[test]
    fn preflight_relay() {
        assert_all_passed("relay", checks::relay::run());
    }

    #[test]
    fn preflight_cli() {
        assert_all_passed("cli", checks::cli::run());
    }

    #[test]
    fn preflight_node() {
        assert_all_passed("node", checks::node::run());
    }

    #[test]
    fn preflight_wire() {
        assert_all_passed("wire", checks::wire::run());
    }

    #[test]
    fn preflight_solver() {
        assert_all_passed("solver", checks::solver::run());
    }

    #[test]
    fn preflight_bridges() {
        assert_all_passed("bridges", checks::bridges::run());
    }

    #[test]
    fn preflight_demo_agent() {
        assert_all_passed("demo_agent", checks::demo_agent::run());
    }

    #[test]
    fn preflight_state_constraints() {
        assert_all_passed("state_constraints", checks::state_constraints::run());
    }

    /// The golden master: ALL checks in one pass.
    #[test]
    fn preflight_golden_master() {
        let start = Instant::now();
        let subsystems = run_all_subsystems();
        let total_duration = start.elapsed();

        let report = PreflightReport {
            subsystems,
            total_duration,
        };

        print!("{report}");
        assert!(
            report.all_passed(),
            "PREFLIGHT FAILED: {}/{} checks passed",
            report.total_passed(),
            report.total_checks()
        );
    }
}
