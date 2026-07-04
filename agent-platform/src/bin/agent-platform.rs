//! Host confined agent grains live on a TCP port. An agent (or a human) POSTs a
//! rental to the control endpoint, then drives its grain by host.
//!
//! Every route is gated on the verified `X-Dregg-Subject` (set by the webauth
//! forward-auth proxy in a real deploy; supplied directly when curling the bare
//! bin). The grain is owned by that subject — never a body-supplied account.
//!
//! ```text
//!   agent-platform 127.0.0.1:8903
//!   curl -H 'Host: control.localhost' -H 'X-Dregg-Subject: dga1_alice' \
//!     -XPOST http://127.0.0.1:8903/rent \
//!     -d '{"host":"alice.grain","caps":"fs","budget":100000,"rent_per_period":100,"period":50}'
//!   curl -H 'Host: alice.grain' -H 'X-Dregg-Subject: dga1_alice' http://127.0.0.1:8903/verify
//! ```
//!
//! Driving (`POST <grain-host> /drive`) needs a live brain — build with
//! `--features live-brain` and set an LLM key. `DREGG_OPERATOR_SUBJECT` names the
//! subject allowed to tick the block clock (`POST control /clock`); unset, the
//! clock route is disabled and NO grain ever lapses (fine for a demo, wrong for
//! production).

use std::sync::Arc;

use agent_platform::AgentPlatform;
use agent_platform::serve::serve_platform;
use dregg_cell::CellId;

fn cid(n: u8) -> CellId {
    CellId::from_bytes([n; 32])
}

fn main() -> std::io::Result<()> {
    let bind = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "127.0.0.1:8903".to_string());
    let platform = Arc::new(AgentPlatform::new());
    let workdir_base = std::env::temp_dir().join("dregg-grains");
    std::fs::create_dir_all(&workdir_base).ok();
    let operator = std::env::var("DREGG_OPERATOR_SUBJECT").ok();
    if operator.is_none() {
        eprintln!(
            "agent-platform: DREGG_OPERATOR_SUBJECT unset — the /clock route is disabled, so no grain will ever lapse for non-payment"
        );
    }

    eprintln!("agent-platform: hosting confined agent grains on http://{bind}");
    eprintln!(
        "  rent : curl -H 'Host: control.localhost' -H 'X-Dregg-Subject: dga1_alice' -XPOST http://{bind}/rent -d '{{\"host\":\"alice.grain\",\"caps\":\"fs\",\"budget\":100000,\"rent_per_period\":100,\"period\":50}}'"
    );
    eprintln!(
        "  verify: curl -H 'Host: alice.grain' -H 'X-Dregg-Subject: dga1_alice' http://{bind}/verify"
    );
    eprintln!("  drive : needs --features live-brain + an LLM key (POST <grain-host> /drive)");
    serve_platform(
        &bind,
        "control.localhost".to_string(),
        cid(2),
        cid(9),
        workdir_base,
        operator,
        platform,
    )
}
