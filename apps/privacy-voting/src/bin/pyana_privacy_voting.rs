//! Standalone pyana-privacy-voting server binary.

use pyana_app_framework::blinded_endpoint::FairDistributionEndpoint;
use pyana_app_framework::server::{AppConfig, AppServer};
use pyana_privacy_voting::EligibilityAuthority;
use pyana_privacy_voting::server::{AppState, router};
use pyana_types::PublicKey;

#[tokio::main]
async fn main() {
    let config = AppConfig::from_env()
        .with_listen(std::env::var("LISTEN").unwrap_or_else(|_| "0.0.0.0:3100".into()));

    // REVIEW[P2]: In a real deployment the eligibility issuer's public key
    // would come from a config file or nameservice lookup. For local dev we
    // accept `PYANA_VOTING_ISSUER_PK` (hex-encoded 32 bytes), falling back to
    // a deterministic placeholder. The placeholder issuer is unable to issue
    // valid credentials because no one holds its signing key — that's the
    // safe default (open == reject all).
    let issuer_pk_bytes: [u8; 32] = std::env::var("PYANA_VOTING_ISSUER_PK")
        .ok()
        .and_then(|s| pyana_app_framework::hex::hex_to_bytes32(&s).ok())
        .unwrap_or([0xCAu8; 32]);
    let authority = EligibilityAuthority::Single(PublicKey(issuer_pk_bytes));

    let app_state = AppState::new(authority, 4096);
    let app_routes = router().with_state(app_state.clone());

    // A blinded-queue endpoint exposed at `/queue/ballots`. The voting flow
    // does NOT route ballots through this endpoint (we go via `/ballots/...`
    // so we can enforce eligibility on submit). This is here for cross-app
    // cipherclerks that talk to many blinded queues uniformly: they can read the
    // commitment root, status, etc.
    let blinded = FairDistributionEndpoint::new(4096);

    AppServer::new(config)
        .service_name("pyana-privacy-voting")
        .with_health()
        .with_cors()
        .with_blinded_endpoint("/queue/ballots", blinded)
        .with_name(
            "privacy-voting",
            vec!["governance".into(), "privacy".into()],
        )
        .routes(app_routes)
        .serve()
        .await
        .unwrap();
}
