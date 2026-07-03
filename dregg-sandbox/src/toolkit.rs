//! `toolkit` — wire the owned sandbox engine into the confined-agent gate.
//!
//! The agent toolkit — the [`Toolkit`] registry, the cap-gated / metered /
//! receipted tool dispatch, the witness binding, the re-witness oracle — lives in
//! the substrate crate [`dregg_agent::toolkit`]. It owns no compute engine: its
//! compute tools take an **injected runner** ([`dregg_agent::toolkit::RunFn`], a
//! `Fn(&str, &str) -> Result<RunReport, String>`).
//!
//! This module is the engine behind that seam. [`SandboxToolkit`] injects the
//! owned wasmi sandbox ([`crate::run_source`]) as the toolkit's `run_tests` /
//! `run_workload` runner at a chosen [`CapTier`], and [`rewitness_run_tests`] rides
//! the same engine for the Layer-3 re-witness. The open core owns the witness; this
//! crate owns the engine — one agent runtime, this crate as the engine plug. Every
//! run reached this way is therefore cap-gated + metered + receipted by the gate,
//! and executed inside the empty-Linker wasm floor.

use crate::CapTier;
use dregg_agent::agent::{ReWitness, WitnessedRun};
use dregg_agent::toolkit::{RunReport, Toolkit};

/// Map a [`crate::Output`] to the open toolkit's [`RunReport`].
fn report_of(out: crate::Output) -> RunReport {
    RunReport::new(out.values, out.enforcement)
}

/// Extension over the open [`Toolkit`] that injects the owned wasmi sandbox as the
/// compute runner, so the witnessed binding (computed in the open core) ties to a
/// genuine sandboxed execution at `tier`.
pub trait SandboxToolkit: Sized {
    /// Wire a **run_tests** tool whose runner is the owned sandbox at `tier`.
    fn with_run_tests_in(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        tier: CapTier,
    ) -> Toolkit;

    /// Wire a **run_workload** tool whose runner is the owned sandbox at `tier`.
    fn with_run_workload_in(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        tier: CapTier,
    ) -> Toolkit;
}

impl SandboxToolkit for Toolkit {
    fn with_run_tests_in(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        tier: CapTier,
    ) -> Toolkit {
        self.with_run_tests(name, lang, source, move |l, s| {
            crate::run_source(l, s, tier, &[])
                .map(report_of)
                .map_err(|e| e.to_string())
        })
    }

    fn with_run_workload_in(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        tier: CapTier,
    ) -> Toolkit {
        self.with_run_workload(name, lang, source, move |l, s| {
            crate::run_source(l, s, tier, &[])
                .map(report_of)
                .map_err(|e| e.to_string())
        })
    }
}

/// The **re-witness oracle** for a `run_tests` binding, riding the owned engine:
/// re-execute `source` (the code the binding's `code_root` commits to) at `tier`
/// and reproduce its `(exit, output_digest)`. Handed to
/// [`dregg_agent::agent::verify_witnessed_qa`] as the `rerun` closure. Returns
/// `None` (fail-closed) when `source` does not match the binding's `code_root` or
/// the workload could not be executed.
pub fn rewitness_run_tests(
    lang: &str,
    source: &str,
    tier: CapTier,
    bound: &WitnessedRun,
) -> Option<ReWitness> {
    dregg_agent::toolkit::rewitness_run_tests(lang, source, bound, move |l, s| {
        crate::run_source(l, s, tier, &[])
            .map(report_of)
            .map_err(|e| e.to_string())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_agent::agent::{
        AgentAction, AgentCloud, AgentSpec, PlannedBrain, verify_agent_run, verify_witnessed_qa,
    };
    use dregg_agent::toolkit::code_root;

    /// A core-module WAT that exports `run` returning the i32 `n` — a suite
    /// reporting `n` failures (0 = green), executed by the OWNED wasmi engine.
    fn wat_returning(n: i32) -> String {
        format!("(module (func (export \"run\") (result i32) (i32.const {n})))")
    }

    fn spec(id: &str, budget: i64, services: &[&str]) -> AgentSpec {
        let mut s = AgentSpec::new(id, budget);
        s.services = services.iter().map(|s| s.to_string()).collect();
        s.cells = vec!["/deploy".to_string()];
        s
    }

    /// The owned wrapper genuinely runs a wat suite in the sandbox, binds the
    /// witness, and the whole run re-witnesses — proving the engine wiring over the
    /// open toolkit (i.e. that a run driven through the cap-gated / metered /
    /// receipted gate actually executes on the empty-Linker wasm floor).
    #[test]
    fn run_tests_binds_a_real_sandboxed_execution() {
        let cloud = AgentCloud::from_seed([60u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:sbxqa", 10, &["run_tests"]))
            .unwrap();
        let src = wat_returning(0);
        let deployed_root = code_root(&src);

        let toolkit =
            Toolkit::new().with_run_tests_in("run_tests", "wat", &src, CapTier::Sandboxed);
        let plan = vec![
            AgentAction::CellWrite {
                path: "/deploy".into(),
                value: deployed_root.clone(),
            },
            AgentAction::Invoke {
                service: "run_tests".into(),
            },
        ];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);
        verify_agent_run(&report).expect("the chain + bound re-witness");

        // Layer 3: re-run the bound on the owned engine — it reproduces the result.
        let v = verify_witnessed_qa(&report, &deployed_root, |w| {
            rewitness_run_tests("wat", &src, CapTier::Sandboxed, w)
        })
        .expect("the witnessed execution re-witnesses on the owned engine");
        assert_eq!(v.passed, 1, "the suite really passed on re-execution");
    }
}
