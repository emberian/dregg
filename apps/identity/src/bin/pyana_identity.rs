//! Standalone pyana-identity server binary.
//!
//! Uses the shared `AppServer` from `pyana-app-framework` for standard
//! middleware (health, CORS) and environment-based configuration.

use pyana_app_framework::server::{AppConfig, AppServer};
use pyana_identity::server::{AppState, router};

#[tokio::main]
async fn main() {
    let config = AppConfig::from_env().with_listen("0.0.0.0:3052");
    let app_routes = router().with_state(AppState::new());

    AppServer::new(config)
        .service_name("pyana-identity")
        .with_health()
        .with_cors()
        .routes(app_routes)
        .serve()
        .await
        .unwrap();
}
