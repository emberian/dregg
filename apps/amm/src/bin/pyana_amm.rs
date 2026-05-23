//! Standalone pyana-amm server binary.

use pyana_amm::server::{AppState, router};
use tokio::net::TcpListener;

#[tokio::main]
async fn main() {
    let app = router().with_state(AppState::new());
    let listener = TcpListener::bind("0.0.0.0:3051").await.unwrap();
    eprintln!("pyana-amm listening on http://0.0.0.0:3051");
    axum::serve(listener, app).await.unwrap();
}
