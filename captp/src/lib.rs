//! CapTP: Capability Transport Protocol for the Pyana federation.
//!
//! # Trust Model
//!
//! This crate operates at **MIXED** trust levels:
//!
//! ## Executor-Trusted Components
//! - **Session management** ([`session`]): CapTP sessions track import/export state between
//!   peers. Session correctness relies on the federation executor maintaining accurate
//!   reference counts and routing tables.
//! - **Swiss table** ([`sturdy`]): Maps swiss numbers to live capabilities. The swiss
//!   number is a bearer secret -- possession IS authorization. The executor must faithfully
//!   maintain the mapping.
//! - **Distributed GC** ([`gc`]): Reference counting across federations. Incorrect GC
//!   could leak capabilities (not release them) or prematurely revoke them.
//!
//! ## Trustless Components (when proven)
//! - **Handoff protocol** ([`handoff`]): The `HandoffCertificate` is cryptographically
//!   signed by the introducer. Validation (`validate_handoff`) is independently verifiable --
//!   any party can check the certificate's Ed25519 signature without trusting the executor.
//! - **Store-and-forward** ([`store_forward`]): Messages are encrypted to the recipient's
//!   X25519 key. The relay cannot read or forge messages (only delay or drop them).
//!
//! ## Soundness
//! - Capability confinement: a capability cannot be accessed without knowledge of its swiss number.
//! - Handoff integrity: a handoff certificate cannot be forged without the introducer's private key.
//! - Forward secrecy: store-and-forward messages are encrypted; relay operators see only ciphertext.
//!
//! ## Assumptions
//! - Federation executor honestly maintains swiss table and session state.
//! - Ed25519 signature scheme is secure (for handoff certificates).
//! - X25519 key exchange is secure (for store-and-forward encryption).
//!
//! ## Verifiable by
//! - Handoff certificates: anyone with the introducer's public key.
//! - Session state: federation members via replication.
//! - Store-and-forward integrity: recipient (via authenticated decryption).
//!
//! This crate implements sturdy references — durable, serializable capability URIs
//! that survive disconnection and enable offline sharing. A sturdy ref is a `pyana://`
//! URI containing a federation ID, cell ID, and swiss number (a random secret that
//! proves you were given access).
//!
//! # Architecture
//!
//! - **Sturdy references** (`uri::PyanaUri`) are the offline-shareable form of a capability.
//! - **Swiss table** (`sturdy::SwissTable`) maps swiss numbers to live capabilities.
//! - **CapTP sessions** (`session::CapSession`) track import/export state between peers.
//! - **Distributed GC** (`gc`) tracks reference counts across federations.
//! - **Handoff protocol** (`handoff`) enables offline capability transfer to third parties.
//! - **Store-and-forward** (`store_forward`) queues encrypted messages for offline destinations.
//!
//! # Protocol
//!
//! To enliven a sturdy ref:
//! 1. Parse the `pyana://` URI
//! 2. Connect to the federation (identified by federation_id)
//! 3. Present the swiss number
//! 4. If valid: receive a live reference token
//!
//! # Distributed GC
//!
//! When federation A exports a capability to federation B:
//! - A's `ExportGcManager` records that B holds a reference.
//! - When B no longer needs it, B sends a `DropRef` → A decrements the count.
//! - At zero refs, A can revoke the export.
//!
//! # Handoff Protocol
//!
//! To transfer a capability to a third party without requiring simultaneous connectivity:
//! 1. Introducer registers a swiss entry at the target federation.
//! 2. Introducer creates a signed `HandoffCertificate` naming the recipient.
//! 3. Certificate travels out-of-band (QR code, email, BLE, file).
//! 4. Recipient presents the certificate to the target.
//! 5. Target validates and creates a routing entry.

use serde::{Deserialize, Serialize};

pub mod gc;
pub mod handoff;
pub mod pipeline;
pub mod session;
pub mod store_forward;
pub mod sturdy;
pub mod uri;

pub use gc::{DropMessage, DropResult, ExportGcManager, ImportGcManager, SessionId};
pub use handoff::{
    HandoffAcceptance, HandoffCertificate, HandoffError, HandoffPresentation, validate_handoff,
};
pub use pipeline::{
    BrokenPromiseNotification, CrossFedPipelineBridge, PipelineError, PipelinePromiseState,
    PipelineRegistry, PipelineResultValue, PipelineWireMessage, PipelinedAction, PipelinedMessage,
};
pub use session::CapSession;
pub use store_forward::{
    BlocklaceEnvelope, DecryptError, MessagePriority, MessageRelay, QueuedMessage, RelayError,
    RelayInfo, SendResult, StoreForwardClient, generate_x25519_keypair,
};
pub use sturdy::{EnlivenError, SwissEntry, SwissTable};
pub use uri::{PyanaUri, UriError};

// =============================================================================
// Shared types
// =============================================================================

/// Identifies a federation (or reference group) in the CapTP protocol.
///
/// Currently a 32-byte value (typically derived from the federation's public key
/// or a BLAKE3 hash of its identity material).
///
/// # Unified Lace Model
///
/// In the unified blocklace model, a "federation" is simply a *reference group*
/// (a set of strands with shared ordering over a single DAG). This type is
/// semantically equivalent to `blocklace::addressing::GroupId`. CapTP sessions
/// are ultimately between strands (bilateral), but `FederationId` remains as
/// the routing-level group identifier for backward compatibility.
///
/// See `blocklace::addressing::FabricAddress` for the full addressing taxonomy.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FederationId(pub [u8; 32]);

/// Type alias: in the unified lace model, a FederationId is equivalent to a GroupId.
pub type GroupId = FederationId;

/// Identifies a strand (a single participant's append-only log) in the blocklace.
///
/// In the unified model, CapTP sessions are bilateral between strands, not between
/// groups. The `StrandId` is the identifier of a specific strand, typically derived
/// from the strand owner's public key or identity material.
///
/// This is used as the key for GC tracking (who holds a reference) and session
/// addressing (which strand we are talking to).
pub type StrandId = [u8; 32];

impl std::fmt::Debug for FederationId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "FedId({})",
            self.0[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

impl std::fmt::Display for FederationId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0[..8]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}
