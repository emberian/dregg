//! CapTP: Capability Transport Protocol for the Pyana federation.
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

pub use gc::{DropMessage, DropResult, ExportGcManager, ImportGcManager};
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
    RelayInfo, SendResult, StoreForwardClient,
};
pub use sturdy::{EnlivenError, SwissEntry, SwissTable};
pub use uri::{PyanaUri, UriError};

// =============================================================================
// Shared types
// =============================================================================

/// Identifies a federation in the CapTP protocol.
///
/// Currently a 32-byte value (typically derived from the federation's public key
/// or a BLAKE3 hash of its identity material).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FederationId(pub [u8; 32]);

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
