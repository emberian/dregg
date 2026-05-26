//! pyana-wire: Network wire protocol for cross-silo token presentation and
//! federation synchronization.
//!
//! # Trust Model
//!
//! This crate is a **TRANSPORT** layer — it is NOT a trust boundary itself.
//!
//! - **Soundness**: The wire protocol provides authenticated channels (via TLS + PeerRole)
//!   and message integrity (length-prefixed framing with nonce-based replay protection).
//!   It does NOT independently verify the semantic content of messages.
//! - **Assumptions**: TLS provides confidentiality and authentication of the transport.
//!   `PeerRole` classification is correct (configured at the federation level). Nonce
//!   caches prevent replay within the configured window.
//! - **Verifiable by**: Connection peers (via TLS certificate validation). The protocol
//!   itself is transparent to inspection by federation operators.
//!
//! ## What Crosses This Layer
//! - STARK proofs (verified by the receiving silo's verifier, NOT by the wire layer)
//! - Revocation attestations (verified against federation root, NOT by wire)
//! - Federation sync messages (applied by the executor, NOT by wire)
//!
//! The wire layer's security properties are:
//! 1. Authentication: PeerRole ensures only authorized peers can connect.
//! 2. Integrity: Length-prefixed framing detects truncation/corruption.
//! 3. Replay protection: Nonce cache + timestamp window rejects replayed messages.
//! 4. DoS resistance: MAX_MESSAGE_SIZE bounds memory consumption.
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

pub mod auth;
pub mod captp_routing;
pub mod codec;
pub mod connection;
pub mod dfa_router;
pub mod hardening;
pub mod message;
pub mod server;

// =============================================================================
// Unified Lace Compatibility
// =============================================================================
//
// In the unified blocklace model, a "federation" is simply a reference group
// (GroupId). The wire protocol fields named `federation_id` and `federation_root`
// are semantically equivalent to `group_id` and `group_root`. The field names
// are frozen for wire-format stability; they will be renamed in protocol v2.
//
// See `blocklace::addressing::FabricAddress` for the full addressing taxonomy.
// See `plans/unified-lace-propagation.md` for the full migration plan.

/// Convenience re-exports for common usage.
pub mod prelude {
    pub use crate::auth::{
        AuthConfig, BanConfig, BanList, BanReason, GossipFilter, RateLimitConfig,
        RateLimiter as AuthRateLimiter, SharedBanList, new_shared_ban_list,
    };
    pub use crate::codec::{CodecError, FrameStats, MAX_MESSAGE_SIZE};
    pub use crate::connection::{ConnectionError, ConnectionPool, ConnectionStats, PeerConnection};
    pub use crate::hardening::{
        ConnectionMetrics, DEFAULT_MAX_MESSAGE_SIZE, HEARTBEAT_INTERVAL, HEARTBEAT_TIMEOUT,
        HardeningConfig, OUTGOING_CHANNEL_CAPACITY, OutgoingMessage, RateLimiter,
        ShutdownCoordinator, message_cost, outgoing_channel,
    };
    pub use crate::message::{
        AuthorizationRequest, Envelope, MAX_NONCE_CACHE_SIZE, MAX_REQUEST_AGE_SECS,
        PROTOCOL_VERSION, PublicKey, ReceiptBody, ReceiptUnavailable, Signature, ThresholdQC,
        WireMessage, error_codes,
    };
    pub use crate::server::{
        CapTpState, CapTpTurnDispatcher, ConnectionAuth, MinSizeVerifier, NonceCache, NoopVerifier,
        ParticipantSource, PeerRole, PendingAttestedRoot, ProofVerifier, RejectAllVerifier,
        SiloConfig, SiloServer, SiloState, StarkVerifier, StaticParticipants, TlsConfig,
        VerificationMode, peer_auth_signing_message, revocation_signing_message,
    };
}
