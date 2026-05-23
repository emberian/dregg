//! Standalone pyana-stablecoin server binary.

use pyana_stablecoin::server::{AppState, router};
use tokio::net::TcpListener;

#[tokio::main]
async fn main() {
    let app = router().with_state(AppState::new());
    let listener = TcpListener::bind("0.0.0.0:3050").await.unwrap();
    eprintln!("pyana-stablecoin listening on http://0.0.0.0:3050");
    axum::serve(listener, app).await.unwrap();
}
