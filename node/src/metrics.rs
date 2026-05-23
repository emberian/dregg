//! Prometheus metrics for operational observability.
//!
//! Installs a Prometheus recorder and exposes a `/metrics` HTTP handler
//! that renders the exposition format.

use metrics::{counter, gauge, histogram};
use metrics_exporter_prometheus::{PrometheusBuilder, PrometheusHandle};

/// Install the Prometheus metrics recorder. Returns the handle used to render
/// the exposition-format output from the `/metrics` endpoint.
pub fn install_recorder() -> PrometheusHandle {
    PrometheusBuilder::new()
        .install_recorder()
        .expect("failed to install Prometheus metrics recorder")
}

/// Axum handler for GET /metrics.
pub async fn metrics_handler(
    axum::extract::State(handle): axum::extract::State<PrometheusHandle>,
) -> String {
    handle.render()
}

// ─── Counters ────────────────────────────────────────────────────────────────

/// Increment the turns-submitted counter.
pub fn inc_turns_submitted() {
    counter!("pyana_turns_submitted_total").increment(1);
}

/// Increment the turns-executed counter with a status label.
pub fn inc_turns_executed(status: &'static str) {
    counter!("pyana_turns_executed_total", "status" => status).increment(1);
}

/// Increment proof verification outcomes.
pub fn inc_proofs_verified(result: &'static str) {
    counter!("pyana_proofs_verified_total", "result" => result).increment(1);
}

/// Increment revocations processed.
pub fn inc_revocations() {
    counter!("pyana_revocations_total").increment(1);
}

/// Increment gossip message counter.
pub fn inc_gossip(direction: &'static str) {
    counter!("pyana_gossip_messages_total", "direction" => direction).increment(1);
}

// ─── Histograms ──────────────────────────────────────────────────────────────

/// Record turn execution duration.
pub fn record_turn_execution_duration(seconds: f64) {
    histogram!("pyana_turn_execution_duration_seconds").record(seconds);
}

/// Record proof verification duration.
pub fn record_proof_verification_duration(seconds: f64) {
    histogram!("pyana_proof_verification_duration_seconds").record(seconds);
}

// ─── Gauges ──────────────────────────────────────────────────────────────────

/// Set the current peer count.
pub fn set_federation_peers_connected(count: f64) {
    gauge!("pyana_federation_peers_connected").set(count);
}

/// Set the current ledger cell count.
pub fn set_ledger_cell_count(count: f64) {
    gauge!("pyana_ledger_cell_count").set(count);
}

/// Set the current block height.
pub fn set_block_height(height: f64) {
    gauge!("pyana_block_height").set(height);
}

/// Set time since the last root update (seconds).
pub fn set_federation_root_age(seconds: f64) {
    gauge!("pyana_federation_root_age_seconds").set(seconds);
}
