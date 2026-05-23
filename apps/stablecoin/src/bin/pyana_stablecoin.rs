//! Standalone pyana-stablecoin server binary.
//!
//! Uses the shared app-framework infrastructure for health, CORS, and configuration.

use pyana_app_framework::server::{AppConfig, AppServer};
use pyana_stablecoin::fee_endpoints::default_fee_policy;
use pyana_stablecoin::liquidation_queue::LiquidationQueue;
use pyana_stablecoin::server::{AppState, router};

#[tokio::main]
async fn main() {
    let config = AppConfig::from_env().with_listen("0.0.0.0:3050");

    let app_state = AppState::new();
    let app_routes = router().with_state(app_state);

    // Upgrade 1: programmable liquidation queue endpoint.
    let liq_endpoint = LiquidationQueue::make_endpoint();

    // Upgrade 2: multi-asset fee policy.
    let fee_policy = default_fee_policy();

    AppServer::new(config)
        .service_name("pyana-stablecoin")
        .with_health()
        .with_cors()
        .with_queue_endpoint("/queue/liquidations", liq_endpoint)
        .with_fee_policy(fee_policy)
        .routes(app_routes)
        .serve()
        .await
        .unwrap();
}
