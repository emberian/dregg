//! App integration checks.
//!
//! `apps/gallery` and `apps/identity` were both retired in the
//! `apps/ → starbridge-apps/` migration (STARBRIDGE-APPS-PLAN.md §4.1).
//!
//! - `apps/identity` was deleted entirely; `starbridge-identity` replaces it
//!   with a different public API.
//! - `apps/gallery` is no longer a workspace member and cannot be depended on
//!   from preflight.
//!
//! The gallery and identity preflight checks are retired accordingly.
//! When a starbridge-apps integration check is added, add a dep in
//! `preflight/Cargo.toml` (behind an optional feature) and a `run_check`
//! call here.
//!
//! NOTE: stablecoin / amm / orderbook / lending / dao-treasury / prediction-market
//! were also retired; see STARBRIDGE-APPS-PLAN.md §4.1 for the rationale.

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    let mut checks = Vec::new();

    // Gallery check retired: apps/gallery is no longer a workspace member
    // (deleted in apps/ → starbridge-apps/ sweep).
    checks.push(run_check("gallery", || {
        Err("RETIRED: apps/gallery deleted in starbridge-apps migration; \
             add starbridge-apps integration check when ready"
            .into())
    }));

    // Identity check retired: apps/identity deleted; starbridge-identity has
    // a different public API (pyana-credentials-backed, no pyana_identity::*).
    checks.push(run_check("identity", || {
        Err("RETIRED: apps/identity deleted in starbridge-apps migration; \
             add starbridge-identity integration check when ready"
            .into())
    }));

    checks
}
