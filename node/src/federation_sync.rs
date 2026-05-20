//! Background federation sync task.
//!
//! Connects to federation peers via TCP, receives new attested roots,
//! and updates local state. Reconnects on failure with exponential backoff.

use std::collections::HashMap;
use std::net::SocketAddr;
use std::time::Duration;

use tracing::{info, warn};

use crate::state::NodeState;

/// Run the federation sync loop as a background task.
///
/// This connects to all configured peers and listens for finalized blocks.
/// When a new attested root arrives, it is persisted to the local store.
pub async fn run_federation_sync(state: NodeState) {
    let peers = {
        let s = state.read().await;
        s.peers.clone()
    };

    if peers.is_empty() {
        info!("no federation peers configured, sync disabled");
        return;
    }

    info!(peer_count = peers.len(), "starting federation sync");

    let mut backoff = Duration::from_secs(1);
    let max_backoff = Duration::from_secs(60);

    loop {
        match try_sync_round(&state, &peers).await {
            Ok(()) => {
                // Successful round, reset backoff.
                backoff = Duration::from_secs(1);
            }
            Err(e) => {
                warn!(error = %e, backoff_secs = backoff.as_secs(), "federation sync error, will retry");
                tokio::time::sleep(backoff).await;
                backoff = (backoff * 2).min(max_backoff);
            }
        }

        // Small delay between successful rounds to avoid busy-looping.
        tokio::time::sleep(Duration::from_secs(1)).await;
    }
}

/// Attempt one sync round: connect to peers and poll for messages.
async fn try_sync_round(_state: &NodeState, peers: &[String]) -> Result<(), String> {
    // Parse peer addresses.
    let mut peer_map: HashMap<usize, SocketAddr> = HashMap::new();
    for (i, peer) in peers.iter().enumerate() {
        let addr: SocketAddr = peer
            .parse()
            .map_err(|e| format!("invalid peer address '{peer}': {e}"))?;
        peer_map.insert(i, addr);
    }

    // For now, we do a simple polling approach: try to connect to each peer
    // and check for new attested roots via the store. A full implementation
    // would use TcpFederationTransport to receive consensus messages in real-time.
    //
    // TODO: Integrate with TcpFederationTransport for real-time consensus participation.
    // For the initial scaffolding, we just verify connectivity.

    for (id, addr) in &peer_map {
        match tokio::net::TcpStream::connect(addr).await {
            Ok(_stream) => {
                tracing::debug!(peer_id = id, addr = %addr, "peer reachable");
            }
            Err(e) => {
                tracing::debug!(peer_id = id, addr = %addr, error = %e, "peer unreachable");
            }
        }
    }

    Ok(())
}
