//! Standalone pyana-orderbook server binary.

use pyana_orderbook::server::{AppState, router};
use tokio::net::TcpListener;

#[tokio::main]
async fn main() {
    let app = router().with_state(AppState::new());
    let listener = TcpListener::bind("0.0.0.0:3053").await.unwrap();
    eprintln!("pyana-orderbook listening on http://0.0.0.0:3053");
    axum::serve(listener, app).await.unwrap();
}
