//! Pyana Golden Master Preflight
//!
//! End-to-end integration test gate for devnet -> testnet -> mainnet promotion.
//! Exercises EVERY major subsystem: federation boot, cell lifecycle, turn execution,
//! proof generation/verification, privacy stack, capabilities, intents, apps,
//! proof composition, federation state, sovereign cells, and cross-backend proofs.
//!
//! Run as a binary:
//!   cargo run -p pyana-preflight
//!
//! Run as a test:
//!   cargo test -p pyana-preflight

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

    #[test]
    fn preflight_boot() {
        let results = checks::boot::run();
        for r in &results {
            assert!(r.passed, "boot::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_cells() {
        let results = checks::cells::run();
        for r in &results {
            assert!(r.passed, "cells::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_turns() {
        let results = checks::turns::run();
        for r in &results {
            assert!(r.passed, "turns::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_proofs() {
        let results = checks::proofs::run();
        for r in &results {
            assert!(r.passed, "proofs::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_privacy() {
        let results = checks::privacy::run();
        for r in &results {
            assert!(r.passed, "privacy::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_caps() {
        let results = checks::caps::run();
        for r in &results {
            assert!(r.passed, "caps::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_intents() {
        let results = checks::intents::run();
        for r in &results {
            assert!(r.passed, "intents::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_apps() {
        let results = checks::apps::run();
        for r in &results {
            assert!(r.passed, "apps::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_composition() {
        let results = checks::composition::run();
        for r in &results {
            assert!(r.passed, "composition::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_federation() {
        let results = checks::federation::run();
        for r in &results {
            assert!(r.passed, "federation::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_sovereign() {
        let results = checks::sovereign::run();
        for r in &results {
            assert!(r.passed, "sovereign::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_effect_vm() {
        let results = checks::effect_vm::run();
        for r in &results {
            assert!(r.passed, "effect_vm::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_blocklace() {
        let results = checks::blocklace::run();
        for r in &results {
            assert!(r.passed, "blocklace::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_backends() {
        let results = checks::backends::run();
        for r in &results {
            assert!(r.passed, "backends::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_captp() {
        let results = checks::captp::run();
        for r in &results {
            assert!(r.passed, "captp::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_routing() {
        let results = checks::routing::run();
        for r in &results {
            assert!(r.passed, "routing::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_storage() {
        let results = checks::storage::run();
        for r in &results {
            assert!(r.passed, "storage::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_nameservice() {
        let results = checks::nameservice::run();
        for r in &results {
            assert!(r.passed, "nameservice::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_relay() {
        let results = checks::relay::run();
        for r in &results {
            assert!(r.passed, "relay::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_cli() {
        let results = checks::cli::run();
        for r in &results {
            assert!(r.passed, "cli::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_node() {
        let results = checks::node::run();
        for r in &results {
            assert!(r.passed, "node::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_wire() {
        let results = checks::wire::run();
        for r in &results {
            assert!(r.passed, "wire::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_solver() {
        let results = checks::solver::run();
        for r in &results {
            assert!(r.passed, "solver::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_bridges() {
        let results = checks::bridges::run();
        for r in &results {
            assert!(r.passed, "bridges::{} failed: {:?}", r.name, r.error);
        }
    }

    #[test]
    fn preflight_demo_agent() {
        let results = checks::demo_agent::run();
        for r in &results {
            assert!(
                r.passed,
                "demo_agent::{} failed: {:?}",
                r.name, r.error
            );
        }
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
