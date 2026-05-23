//! Standalone pyana-identity server binary.

use pyana_identity::server::{AppState, router};
use tokio::net::TcpListener;

#[tokio::main]
async fn main() {
    let app = router().with_state(AppState::new());
    let listener = TcpListener::bind("0.0.0.0:3052").await.unwrap();
    eprintln!("pyana-identity listening on http://0.0.0.0:3052");
    axum::serve(listener, app).await.unwrap();
}
