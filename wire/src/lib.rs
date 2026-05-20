//! pyana-wire: Network wire protocol for cross-silo token presentation and
//! federation synchronization.
//!
//! This crate implements the binary wire protocol used between organizational silos
//! in the Pyana federation. It handles:
//!
//! - **Token presentation**: Transmitting STARK proofs (~24 KiB) over TCP for
//!   cross-silo authorization verification.
//! - **Federation sync**: Exchanging attested revocation roots between silos.
//! - **Revocation propagation**: Submitting and acknowledging token revocations.
//! - **Non-membership proofs**: Requesting proof that a token is not revoked.
//! - **Federation discovery**: Handshake protocol for peers joining the federation view.
//!
//! # Wire Format
//!
//! Each message is length-prefixed:
//! ```text
//! [4-byte LE length][postcard-encoded payload]
//! ```
//!
//! Messages are serialized with [postcard](https://docs.rs/postcard), a compact
//! binary format built on serde. The length prefix does NOT include itself (it
//! encodes only the payload size).
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────┐         TCP          ┌─────────────────┐
//! │   Silo "acme"   │◄────────────────────►│ Silo "partner"  │
//! │                 │                       │                 │
//! │ SiloServer      │  Hello/Welcome        │ SiloServer      │
//! │ PeerConnection  │  PresentToken         │ PeerConnection  │
//! │ SiloState       │  SubmitRevocation     │ SiloState       │
//! └─────────────────┘                       └─────────────────┘
//! ```
//!
//! # Example
//!
//! ```no_run
//! use pyana_wire::prelude::*;
//!
//! #[tokio::main]
//! async fn main() {
//!     // Start a silo server
//!     let config = SiloConfig::new("my-silo");
//!     let server = SiloServer::new("127.0.0.1:9100".parse().unwrap(), config);
//!
//!     // In production, run the server in a background task
//!     // tokio::spawn(async move { server.run().await });
//! }
//! ```

pub mod codec;
pub mod connection;
pub mod message;
pub mod server;

#[cfg(feature = "federation")]
pub mod federation_bridge;

/// Convenience re-exports for common usage.
pub mod prelude {
    pub use crate::codec::{CodecError, FrameStats, MAX_MESSAGE_SIZE};
    pub use crate::connection::{ConnectionError, ConnectionPool, ConnectionStats, PeerConnection};
    pub use crate::message::{
        AuthorizationRequest, PublicKey, Signature, ThresholdQC, WireMessage, error_codes,
        PROTOCOL_VERSION,
    };
    pub use crate::server::{
        MinSizeVerifier, NoopVerifier, ProofVerifier, RejectAllVerifier, SiloConfig,
        SiloServer, SiloState, StarkVerifier, VerificationMode,
    };
}
