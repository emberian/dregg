//! Standalone pyana-lending server binary.
//!
//! Uses the shared app-framework infrastructure for health, CORS, and configuration.

use pyana_app_framework::server::{AppConfig, AppServer};
use pyana_lending::server::{AppState, router};

#[tokio::main]
async fn main() {
    let config = AppConfig::from_env().with_listen("0.0.0.0:3060");

    let app_state = AppState::new();
    let app_routes = router().with_state(app_state);

    AppServer::new(config)
        .service_name("pyana-lending")
        .with_health()
        .with_cors()
        .routes(app_routes)
        .serve()
        .await
        .unwrap();
}
