//! Wire protocol message types for cross-silo token presentation and federation sync.
//!
//! All messages are serialized with postcard (compact binary, serde-compatible) and
//! transmitted over TCP with length-prefixed framing.

use serde::{Deserialize, Serialize};

pub use pyana_types::{
    AttestedRoot as TypesAttestedRoot, PublicKey, RevocationEvent as TypesRevocationEvent,
    Signature, ThresholdQC,
};

// =============================================================================
// Authorization Request
// =============================================================================

/// An authorization request that accompanies a token presentation.
///
/// Describes what action is being requested so the verifying silo can check
/// whether the presented proof actually authorizes the specific action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthorizationRequest {
    /// The resource being accessed (e.g., "api/v1/users").
    pub resource: String,
    /// The action being performed (e.g., "read", "write", "admin").
    pub action: String,
    /// The requesting principal identifier.
    pub principal: String,
    /// Optional scope constraints (e.g., ["org:acme", "team:platform"]).
    pub scopes: Vec<String>,
    /// Unix timestamp when the request was made.
    pub timestamp: i64,
    /// A nonce to prevent replay attacks.
    pub nonce: [u8; 16],
}

impl AuthorizationRequest {
    /// Create a new authorization request with a random nonce.
    pub fn new(
        resource: impl Into<String>,
        action: impl Into<String>,
        principal: impl Into<String>,
    ) -> Self {
        let mut nonce = [0u8; 16];
        getrandom_fill(&mut nonce);
        Self {
            resource: resource.into(),
            action: action.into(),
            principal: principal.into(),
            scopes: Vec::new(),
            timestamp: current_timestamp(),
            nonce,
        }
    }

    /// Add scopes to this request.
    pub fn with_scopes(mut self, scopes: Vec<String>) -> Self {
        self.scopes = scopes;
        self
    }

    /// Compute a BLAKE3 hash of this request for signing/binding.
    ///
    /// Uses length-prefixed encoding to avoid ambiguity when field values contain
    /// arbitrary bytes (a null-byte separator would be collision-prone).
    pub fn digest(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-wire authorization-request v1");
        // Length-prefixed encoding: each variable-length field is preceded by its
        // byte length as a u32 LE value. This eliminates collision ambiguity
        // regardless of field contents (e.g., fields containing null bytes).
        hasher.update(&(self.resource.len() as u32).to_le_bytes());
        hasher.update(self.resource.as_bytes());
        hasher.update(&(self.action.len() as u32).to_le_bytes());
        hasher.update(self.action.as_bytes());
        hasher.update(&(self.principal.len() as u32).to_le_bytes());
        hasher.update(self.principal.as_bytes());
        // Scope count + length-prefixed scope values
        hasher.update(&(self.scopes.len() as u32).to_le_bytes());
        for scope in &self.scopes {
            hasher.update(&(scope.len() as u32).to_le_bytes());
            hasher.update(scope.as_bytes());
        }
        hasher.update(&self.timestamp.to_le_bytes());
        hasher.update(&self.nonce);
        *hasher.finalize().as_bytes()
    }
}

// =============================================================================
// Wire Messages
// =============================================================================

/// The top-level wire protocol message enum.
///
/// Each variant represents a distinct message type that can be exchanged between
/// silos over TCP. Messages are serialized with postcard and framed with a
/// 4-byte little-endian length prefix.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WireMessage {
    // -------------------------------------------------------------------------
    // Token Presentation
    // -------------------------------------------------------------------------
    /// Present a token proof to a remote silo for authorization.
    ///
    /// The proof is the serialized STARK presentation proof (~24 KiB) generated
    /// by the circuit crate. The federation_root anchors the proof to the
    /// current attested revocation tree.
    PresentToken {
        /// The serialized presentation proof (STARK).
        proof: Vec<u8>,
        /// The authorization request being made.
        request: AuthorizationRequest,
        /// The federation root the proof was generated against.
        federation_root: [u8; 32],
    },

    /// Result of a token presentation verification.
    PresentationResult {
        /// Whether the presentation was accepted.
        accepted: bool,
        /// Human-readable reason (especially useful for rejections).
        reason: Option<String>,
        /// The request digest this result corresponds to.
        request_digest: [u8; 32],
    },

    // -------------------------------------------------------------------------
    // Federation Sync
    // -------------------------------------------------------------------------
    /// Request the current attested revocation root from a peer.
    RequestAttestedRoot,

    /// Response containing the current attested revocation root.
    ///
    /// Signatures are FULL 64-byte Ed25519 signatures (not truncated).
    AttestedRoot {
        /// The Merkle root of the revocation tree.
        root: [u8; 32],
        /// The block height at which this root was finalized.
        height: u64,
        /// Unix timestamp when finalized.
        timestamp: i64,
        /// Quorum signatures: (public_key, signature) pairs.
        /// Public keys are 32 bytes, signatures are 64 bytes (Ed25519).
        signatures: Vec<(PublicKey, Signature)>,
        /// Optional threshold aggregate QC (constant-size BLS).
        threshold_qc: Option<ThresholdQC>,
    },

    // -------------------------------------------------------------------------
    // Revocation
    // -------------------------------------------------------------------------
    /// Submit a revocation to a peer silo for propagation.
    SubmitRevocation {
        /// The token ID being revoked.
        token_id: String,
        /// The revoking authority's public key.
        authority: PublicKey,
        /// Signature from the revoking authority (64 bytes, Ed25519).
        authority_sig: Signature,
        /// Unique nonce to prevent replay attacks on revocation submissions.
        nonce: [u8; 16],
        /// Unix timestamp when the revocation was submitted.
        timestamp: i64,
    },

    /// Acknowledgment of a revocation submission.
    RevocationAck {
        /// The new Merkle root after incorporating the revocation.
        new_root: [u8; 32],
        /// The new block height.
        height: u64,
    },

    // -------------------------------------------------------------------------
    // Non-membership proofs
    // -------------------------------------------------------------------------
    /// Request a non-membership proof for a token ID.
    ///
    /// Used to verify that a token has NOT been revoked. The response includes
    /// a Merkle non-membership proof anchored to the current attested root.
    RequestNonMembership {
        /// The token ID to check.
        token_id: String,
    },

    /// Response containing a non-membership proof (or None if revoked).
    NonMembershipResponse {
        /// The token ID this response is for.
        token_id: String,
        /// The non-membership proof, or None if the token IS revoked.
        proof: Option<Vec<u8>>,
        /// The attested root this proof is anchored to.
        root: [u8; 32],
        /// Height of the root.
        height: u64,
    },

    // -------------------------------------------------------------------------
    // Federation Discovery / Handshake
    // -------------------------------------------------------------------------
    /// Initial handshake message sent when connecting to a peer.
    Hello {
        /// This node's public key / identity.
        node_id: [u8; 32],
        /// Human-readable node name.
        node_name: String,
        /// Protocol version.
        protocol_version: u32,
        /// Capabilities advertised by this node.
        capabilities: Vec<String>,
    },

    /// Response to a Hello, welcoming the peer into the federation view.
    Welcome {
        /// The current federation root.
        federation_root: [u8; 32],
        /// Number of members in the federation.
        member_count: u32,
        /// The responder's node identity.
        node_id: [u8; 32],
        /// Human-readable node name.
        node_name: String,
    },

    // -------------------------------------------------------------------------
    // CapTP Session Management
    // -------------------------------------------------------------------------
    /// Establish a CapTP session with the peer, exporting initial swiss entries.
    ///
    /// Sent after the Hello/Welcome handshake to begin a capability session.
    /// The `federation_id` identifies the sender's federation; `initial_exports`
    /// lists cells the sender is making available to this peer.
    CapHello {
        /// The sender's federation identity.
        federation_id: [u8; 32],
        /// Cell IDs that the sender is initially exporting to this peer.
        initial_exports: Vec<[u8; 32]>,
    },

    /// Tear down a CapTP session, releasing all held references.
    ///
    /// All exports and imports for this session are invalidated. The peer should
    /// drop all references acquired during this session.
    CapGoodbye {
        /// The federation terminating the session.
        federation_id: [u8; 32],
        /// Human-readable reason for disconnection (optional).
        reason: Option<String>,
    },

    /// Present a `pyana://` URI to enliven a sturdy reference.
    ///
    /// The peer validates the swiss number and (if valid) responds with an
    /// `EnlivenResponse` containing the granted cell reference.
    EnlivenSturdyRef {
        /// The full serialized PyanaUri (federation_id + cell_id + swiss).
        uri_bytes: Vec<u8>,
        /// The current federation height known to the requester.
        requester_height: u64,
    },

    /// Response to an `EnlivenSturdyRef` request.
    EnlivenResponse {
        /// Whether the enliven succeeded.
        success: bool,
        /// On success: the cell ID that was enlivened.
        cell_id: Option<[u8; 32]>,
        /// On success: the permissions granted.
        permissions_tag: u8,
        /// On failure: the error reason.
        error: Option<String>,
    },

    /// Distributed GC: the remote peer dropped a reference to one of our exports.
    ///
    /// The receiver should decrement the reference count for the specified cell
    /// from the specified federation. If the count reaches zero, the export can
    /// be cleaned up.
    DropRemoteRef {
        /// The federation that is dropping the reference.
        from_federation: [u8; 32],
        /// The cell ID being dropped.
        cell_id: [u8; 32],
        /// The session epoch under which this drop was issued.
        /// Must match the current session epoch; stale-epoch drops are rejected.
        /// Defaults to 0 for backward compatibility with legacy senders.
        #[serde(default)]
        session_epoch: u64,
    },

    /// A pipelined message targeting an unresolved promise on the receiver.
    ///
    /// The receiver queues this message until the target promise resolves,
    /// then delivers it. This enables cross-federation promise pipelining
    /// (eliminating round-trip latency).
    PipelinedMsg {
        /// The promise ID on the RECEIVER's side.
        target_promise_id: u64,
        /// The method to invoke once the promise resolves.
        method: String,
        /// Serialized action arguments.
        args: Vec<u8>,
        /// Serialized authorization.
        authorization: Vec<u8>,
        /// Where to send the result (a promise on the SENDER's side).
        result_promise_id: Option<u64>,
        /// The federation sending this pipelined message.
        sender_federation: [u8; 32],
        /// The session epoch under which this message was sent.
        /// Must match the current session epoch; stale-epoch messages are rejected.
        /// Defaults to 0 for backward compatibility with legacy senders.
        #[serde(default)]
        session_epoch: u64,
    },

    /// Present a handoff certificate to the target federation.
    ///
    /// The recipient proves they own the recipient_pk named in the certificate
    /// by including a signature. The target validates the introducer's signature,
    /// checks the swiss number, and (if valid) responds with `HandoffAccepted`.
    PresentHandoff {
        /// The serialized `HandoffPresentation` (certificate + recipient signature).
        presentation_bytes: Vec<u8>,
        /// The introducer's public key (for signature verification).
        introducer_pk: [u8; 32],
    },

    /// Response to a successful handoff presentation.
    HandoffAccepted {
        /// A routing token the recipient can use for subsequent access.
        routing_token: [u8; 32],
        /// The cell the recipient now has access to.
        cell_id: [u8; 32],
        /// The permissions granted (encoded as a tag byte).
        permissions_tag: u8,
    },

    // -------------------------------------------------------------------------
    // Keepalive / Diagnostics
    // -------------------------------------------------------------------------
    /// Periodic heartbeat to keep connections alive.
    Ping {
        /// Sequence number for round-trip measurement.
        seq: u64,
        /// Timestamp when the ping was sent.
        timestamp: i64,
    },

    /// Response to a Ping.
    Pong {
        /// The sequence number from the corresponding Ping.
        seq: u64,
        /// Timestamp when the pong was sent.
        timestamp: i64,
    },

    /// Protocol error — sent when a message cannot be processed.
    Error {
        /// Error code.
        code: u32,
        /// Human-readable error message.
        message: String,
    },
}

impl WireMessage {
    /// Return a human-readable name for the message variant.
    pub fn variant_name(&self) -> &'static str {
        match self {
            Self::PresentToken { .. } => "PresentToken",
            Self::PresentationResult { .. } => "PresentationResult",
            Self::RequestAttestedRoot => "RequestAttestedRoot",
            Self::AttestedRoot { .. } => "AttestedRoot",
            Self::SubmitRevocation { .. } => "SubmitRevocation",
            Self::RevocationAck { .. } => "RevocationAck",
            Self::RequestNonMembership { .. } => "RequestNonMembership",
            Self::NonMembershipResponse { .. } => "NonMembershipResponse",
            Self::Hello { .. } => "Hello",
            Self::Welcome { .. } => "Welcome",
            Self::CapHello { .. } => "CapHello",
            Self::CapGoodbye { .. } => "CapGoodbye",
            Self::EnlivenSturdyRef { .. } => "EnlivenSturdyRef",
            Self::EnlivenResponse { .. } => "EnlivenResponse",
            Self::DropRemoteRef { .. } => "DropRemoteRef",
            Self::PipelinedMsg { .. } => "PipelinedMsg",
            Self::PresentHandoff { .. } => "PresentHandoff",
            Self::HandoffAccepted { .. } => "HandoffAccepted",
            Self::Ping { .. } => "Ping",
            Self::Pong { .. } => "Pong",
            Self::Error { .. } => "Error",
        }
    }

    /// Estimate the wire size of this message (useful for logging).
    pub fn estimated_size(&self) -> usize {
        // Use postcard to get the actual serialized size
        postcard::to_stdvec(self).map(|v| v.len()).unwrap_or(0)
    }

    /// Format size in human-readable form.
    pub fn size_display(&self) -> String {
        let bytes = self.estimated_size();
        if bytes < 1024 {
            format!("{bytes} B")
        } else if bytes < 1024 * 1024 {
            format!("{:.1} KiB", bytes as f64 / 1024.0)
        } else {
            format!("{:.1} MiB", bytes as f64 / (1024.0 * 1024.0))
        }
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Fill a buffer with cryptographically secure random bytes.
fn getrandom_fill(buf: &mut [u8]) {
    getrandom::fill(buf).expect("getrandom failed to provide random bytes");
}

/// Get the current Unix timestamp in seconds.
fn current_timestamp() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

// =============================================================================
// Error Codes
// =============================================================================

/// Well-known wire protocol error codes.
pub mod error_codes {
    /// The message could not be deserialized.
    pub const MALFORMED_MESSAGE: u32 = 1;
    /// The protocol version is not supported.
    pub const UNSUPPORTED_VERSION: u32 = 2;
    /// The federation root is unknown/stale.
    pub const UNKNOWN_FEDERATION_ROOT: u32 = 3;
    /// The proof verification failed.
    pub const PROOF_VERIFICATION_FAILED: u32 = 4;
    /// The token has been revoked.
    pub const TOKEN_REVOKED: u32 = 5;
    /// The request has expired (timestamp too old).
    pub const REQUEST_EXPIRED: u32 = 6;
    /// A cryptographic signature failed verification.
    pub const INVALID_SIGNATURE: u32 = 7;
    /// A Hello handshake is required before sending other messages.
    pub const HANDSHAKE_REQUIRED: u32 = 8;
    /// The server is at connection capacity.
    pub const CONNECTION_LIMIT: u32 = 9;
    /// Internal server error.
    pub const INTERNAL_ERROR: u32 = 100;
    /// No CapTP session established (CapHello required).
    pub const CAPTP_SESSION_REQUIRED: u32 = 10;
    /// The sturdy reference could not be enlivened (not found, expired, or exhausted).
    pub const ENLIVEN_FAILED: u32 = 11;
    /// Handoff validation failed.
    pub const HANDOFF_FAILED: u32 = 12;
    /// The GC drop was invalid (unknown federation or cell).
    pub const INVALID_DROP: u32 = 13;
    /// The message carries a stale session epoch (from a terminated session).
    pub const STALE_EPOCH: u32 = 14;
}

/// The current protocol version.
pub const PROTOCOL_VERSION: u32 = 1;

/// Maximum age (in seconds) for a request timestamp to be considered fresh.
/// Requests older than this are rejected as stale (anti-replay).
pub const MAX_REQUEST_AGE_SECS: i64 = 300; // 5 minutes

/// Maximum number of nonces to track for replay prevention.
/// Once this limit is reached, the oldest entries are evicted.
pub const MAX_NONCE_CACHE_SIZE: usize = 100_000;

// =============================================================================
// Wire Envelope (version-tagged wrapper)
// =============================================================================

/// A version-tagged envelope that wraps every wire message.
///
/// All messages on the wire MUST be wrapped in an `Envelope`. The receiver
/// checks the version field and rejects messages with unsupported protocol
/// versions before attempting to interpret the payload.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Envelope {
    /// Protocol version of the sender.
    pub version: u32,
    /// The actual wire message payload.
    pub message: WireMessage,
}

impl Envelope {
    /// Wrap a message in an envelope with the current protocol version.
    pub fn wrap(message: WireMessage) -> Self {
        Self {
            version: PROTOCOL_VERSION,
            message,
        }
    }

    /// Check whether this envelope's version is supported.
    pub fn is_version_supported(&self) -> bool {
        self.version == PROTOCOL_VERSION
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_hello() {
        let msg = WireMessage::Hello {
            node_id: [0xab; 32],
            node_name: "test-node".to_string(),
            protocol_version: PROTOCOL_VERSION,
            capabilities: vec!["present".to_string(), "revoke".to_string()],
        };
        let bytes = postcard::to_stdvec(&msg).unwrap();
        let decoded: WireMessage = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(msg, decoded);
    }

    #[test]
    fn roundtrip_present_token() {
        let proof = vec![0u8; 24_000]; // ~24 KiB proof
        let request = AuthorizationRequest::new("api/users", "read", "alice@acme.corp");
        let msg = WireMessage::PresentToken {
            proof,
            request,
            federation_root: [0x42; 32],
        };
        let bytes = postcard::to_stdvec(&msg).unwrap();
        let decoded: WireMessage = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(msg, decoded);
    }

    #[test]
    fn roundtrip_all_variants() {
        let messages = vec![
            WireMessage::RequestAttestedRoot,
            WireMessage::AttestedRoot {
                root: [1; 32],
                height: 42,
                timestamp: 1700000000,
                signatures: vec![(PublicKey([2; 32]), Signature([3; 64]))],
                threshold_qc: None,
            },
            WireMessage::SubmitRevocation {
                token_id: "tok-123".to_string(),
                authority: PublicKey([4; 32]),
                authority_sig: Signature([4; 64]),
                nonce: [0x05; 16],
                timestamp: 1700000000,
            },
            WireMessage::RevocationAck {
                new_root: [5; 32],
                height: 43,
            },
            WireMessage::RequestNonMembership {
                token_id: "tok-456".to_string(),
            },
            WireMessage::NonMembershipResponse {
                token_id: "tok-456".to_string(),
                proof: Some(vec![6; 128]),
                root: [7; 32],
                height: 44,
            },
            WireMessage::Welcome {
                federation_root: [8; 32],
                member_count: 5,
                node_id: [9; 32],
                node_name: "responder".to_string(),
            },
            WireMessage::Ping {
                seq: 1,
                timestamp: 100,
            },
            WireMessage::Pong {
                seq: 1,
                timestamp: 101,
            },
            WireMessage::PresentationResult {
                accepted: true,
                reason: None,
                request_digest: [10; 32],
            },
            WireMessage::Error {
                code: error_codes::MALFORMED_MESSAGE,
                message: "bad frame".to_string(),
            },
            // CapTP variants
            WireMessage::CapHello {
                federation_id: [0xF0; 32],
                initial_exports: vec![[0xF1; 32], [0xF2; 32]],
            },
            WireMessage::CapGoodbye {
                federation_id: [0xF0; 32],
                reason: Some("shutting down".to_string()),
            },
            WireMessage::EnlivenSturdyRef {
                uri_bytes: vec![0xAA; 96],
                requester_height: 500,
            },
            WireMessage::EnlivenResponse {
                success: true,
                cell_id: Some([0xBB; 32]),
                permissions_tag: 1,
                error: None,
            },
            WireMessage::DropRemoteRef {
                from_federation: [0xCC; 32],
                cell_id: [0xDD; 32],
                session_epoch: 5,
            },
            WireMessage::PipelinedMsg {
                target_promise_id: 42,
                method: "transfer".to_string(),
                args: vec![1, 2, 3],
                authorization: vec![0xDE, 0xAD],
                result_promise_id: Some(99),
                sender_federation: [0xEE; 32],
                session_epoch: 7,
            },
            WireMessage::PresentHandoff {
                presentation_bytes: vec![0x11; 200],
                introducer_pk: [0x22; 32],
            },
            WireMessage::HandoffAccepted {
                routing_token: [0x33; 32],
                cell_id: [0x44; 32],
                permissions_tag: 2,
            },
        ];

        for msg in messages {
            let bytes = postcard::to_stdvec(&msg).unwrap();
            let decoded: WireMessage = postcard::from_bytes(&bytes).unwrap();
            assert_eq!(
                msg,
                decoded,
                "roundtrip failed for {:?}",
                msg.variant_name()
            );
        }
    }

    #[test]
    fn authorization_request_digest_deterministic() {
        let mut req = AuthorizationRequest::new("res", "act", "princ");
        req.nonce = [0; 16]; // fix nonce for determinism
        req.timestamp = 12345;

        let d1 = req.digest();
        let d2 = req.digest();
        assert_eq!(d1, d2);
    }

    #[test]
    fn authorization_request_digest_varies_on_input() {
        let mut req1 = AuthorizationRequest::new("res1", "act", "princ");
        req1.nonce = [0; 16];
        req1.timestamp = 12345;

        let mut req2 = AuthorizationRequest::new("res2", "act", "princ");
        req2.nonce = [0; 16];
        req2.timestamp = 12345;

        assert_ne!(req1.digest(), req2.digest());
    }
}
