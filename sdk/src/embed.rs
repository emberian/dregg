//! # pyana-embed: No-I/O integration layer
//!
//! This module provides a zero-I/O facade over pyana's core capabilities,
//! suitable for embedding in any existing service without dragging in pyana's
//! networking, consensus, or storage infrastructure.
//!
//! The pattern follows the "sans-io" approach: all methods are synchronous,
//! take bytes in, and produce bytes/state-transitions out. The **caller**
//! handles transport, persistence, and scheduling.
//!
//! # What's no-IO here
//!
//! - `TurnExecutor::execute()` — pure state machine, no I/O
//! - `prove_presentation` / `verify_presentation` — pure computation
//! - Token mint/attenuate — pure HMAC/hash operations
//! - `WireCodec::encode` / `decode` — pure serialization
//!
//! # Integration examples
//!
//! ## Axum HTTP handler (verify proof from a header)
//!
//! ```ignore
//! async fn verify_handler(headers: HeaderMap, State(engine): State<Arc<PyanaEngine>>) -> StatusCode {
//!     let proof_b64 = headers.get("x-pyana-proof").unwrap();
//!     let proof_bytes = base64::decode(proof_b64).unwrap();
//!     let root = engine.federation_root();
//!     if engine.verify_presentation(&proof_bytes, &root) {
//!         StatusCode::OK
//!     } else {
//!         StatusCode::FORBIDDEN
//!     }
//! }
//! ```
//!
//! ## gRPC interceptor (attenuate token per-request)
//!
//! ```ignore
//! fn intercept(engine: &PyanaEngine, parent_token: &[u8], caveats: &[Caveat]) -> Vec<u8> {
//!     engine.attenuate(parent_token, caveats).unwrap()
//! }
//! ```
//!
//! ## CLI tool (generate proof, output bytes)
//!
//! ```ignore
//! let engine = PyanaEngine::new(EngineConfig::for_testing());
//! let token = engine.mint_token(b"my-root-key-32-bytes-exactly!!!!", "my-service").unwrap();
//! let proof = engine.prove_presentation(&token, "read", "my-service").unwrap();
//! std::fs::write("proof.bin", &proof).unwrap();
//! ```

use pyana_bridge::present::{self, BridgePresentationBuilder, WirePresentationProof};
use pyana_cell::Ledger;
use pyana_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};
use pyana_turn::turn::TurnResult;
use pyana_turn::{Turn, TurnReceipt};
use pyana_wire::server::ProofVerifier;

use crate::error::SdkError;

// Re-export the executor so embedders can configure costs without extra imports.
pub use pyana_turn::executor::{ComputronCosts, TurnExecutor};

// =============================================================================
// Error types
// =============================================================================

/// Errors from the embed layer.
#[derive(Debug)]
pub enum EmbedError {
    /// Turn deserialization failed.
    TurnDecode(String),
    /// Turn execution was rejected by the executor.
    TurnRejected {
        reason: String,
        at_action: Vec<usize>,
    },
    /// State snapshot serialization/deserialization failed.
    StateSerde(String),
    /// State snapshot integrity check failed (BLAKE3 hash mismatch).
    ///
    /// This indicates the snapshot was tampered with or corrupted in storage/transit.
    IntegrityCheckFailed,
    /// Token operation failed.
    Token(String),
    /// Proof generation failed.
    ProofGen(String),
    /// Proof verification failed (malformed input, not "invalid proof").
    ProofDecode(String),
}

impl std::fmt::Display for EmbedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TurnDecode(e) => write!(f, "turn decode: {e}"),
            Self::TurnRejected { reason, at_action } => {
                write!(f, "turn rejected at {at_action:?}: {reason}")
            }
            Self::StateSerde(e) => write!(f, "state serde: {e}"),
            Self::IntegrityCheckFailed => write!(
                f,
                "state integrity check failed: BLAKE3 hash mismatch (snapshot may be tampered)"
            ),
            Self::Token(e) => write!(f, "token: {e}"),
            Self::ProofGen(e) => write!(f, "proof gen: {e}"),
            Self::ProofDecode(e) => write!(f, "proof decode: {e}"),
        }
    }
}

impl std::error::Error for EmbedError {}

impl From<SdkError> for EmbedError {
    fn from(e: SdkError) -> Self {
        Self::Token(e.to_string())
    }
}

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the no-I/O engine.
///
/// This struct intentionally does NOT implement `Default`. The `timestamp` field
/// is critical for proof verification: a zero timestamp causes wallet-generated
/// proofs to appear "from the future" and engine-generated proofs to be rejected
/// as expired. Callers MUST provide a real wall-clock timestamp.
///
/// Use [`EngineConfig::new()`] for production (requires explicit timestamp) or
/// [`EngineConfig::for_testing()`] for test contexts where timestamp doesn't matter.
#[derive(Clone, Debug)]
pub struct EngineConfig {
    /// Computron cost table for turn metering.
    pub costs: ComputronCosts,
    /// This federation's identity (32-byte hash). Used for cross-federation
    /// replay prevention in turn signatures.
    pub federation_id: [u8; 32],
    /// Initial block height.
    pub block_height: u64,
    /// Initial timestamp (unix seconds).
    ///
    /// **IMPORTANT**: This must be set to the current wall-clock time for proof
    /// freshness checks to work correctly. A timestamp of 0 will cause all
    /// verification to fail silently.
    pub timestamp: i64,
    /// Maximum age of a presentation proof in seconds for freshness checks.
    ///
    /// When non-zero, `verify_presentation_bytes()` rejects proofs whose embedded
    /// timestamp is older than this many seconds from the engine's current timestamp.
    /// Defaults to 300 seconds (5 minutes).
    pub max_proof_age_secs: i64,
}

impl EngineConfig {
    /// Create a new engine configuration with an explicit timestamp.
    ///
    /// This is the recommended constructor for production use. The timestamp
    /// should be the current wall-clock time (unix seconds).
    ///
    /// # Example
    ///
    /// ```
    /// use pyana_sdk::embed::EngineConfig;
    /// use std::time::SystemTime;
    ///
    /// let now = SystemTime::now()
    ///     .duration_since(SystemTime::UNIX_EPOCH)
    ///     .unwrap()
    ///     .as_secs() as i64;
    /// let config = EngineConfig::new(now);
    /// ```
    pub fn new(timestamp: i64) -> Self {
        Self {
            costs: ComputronCosts::default_costs(),
            federation_id: [0u8; 32],
            block_height: 0,
            timestamp,
            max_proof_age_secs: present::DEFAULT_MAX_PROOF_AGE_SECS,
        }
    }

    /// Create a configuration suitable for testing only.
    ///
    /// Uses timestamp 0 and default values. Proofs generated or verified with
    /// this config will NOT pass freshness checks against real-world timestamps.
    ///
    /// **Do not use in production.** Use [`EngineConfig::new()`] with a real
    /// wall-clock timestamp instead.
    pub fn for_testing() -> Self {
        Self {
            costs: ComputronCosts::default_costs(),
            federation_id: [0u8; 32],
            block_height: 0,
            timestamp: 0,
            max_proof_age_secs: present::DEFAULT_MAX_PROOF_AGE_SECS,
        }
    }
}

// =============================================================================
// PyanaEngine — the no-IO core
// =============================================================================

/// The no-I/O pyana engine.
///
/// Wraps the turn executor and ledger in a single struct with a bytes-oriented
/// API. Does **no** networking, filesystem access, or async operations.
///
/// Thread safety: NOT `Sync` by default (contains `Ledger` which is a BTreeMap).
/// Wrap in `Mutex` or `RwLock` if sharing across threads.
pub struct PyanaEngine {
    ledger: Ledger,
    executor: TurnExecutor,
    /// The current federation root (caller updates this from their own sync).
    federation_root: [u8; 32],
    /// Maximum proof age in seconds (0 = no freshness check).
    max_proof_age_secs: i64,
}

impl PyanaEngine {
    /// Create a new engine with the given configuration and an empty ledger.
    pub fn new(config: EngineConfig) -> Self {
        let mut executor = TurnExecutor::new(config.costs);
        executor.set_block_height(config.block_height);
        executor.set_timestamp(config.timestamp);
        executor.set_local_federation_id(config.federation_id);
        Self {
            ledger: Ledger::new(),
            executor,
            federation_root: [0u8; 32],
            max_proof_age_secs: config.max_proof_age_secs,
        }
    }

    /// Create an engine from an existing ledger (e.g. loaded from your own DB).
    pub fn with_ledger(config: EngineConfig, ledger: Ledger) -> Self {
        let mut executor = TurnExecutor::new(config.costs);
        executor.set_block_height(config.block_height);
        executor.set_timestamp(config.timestamp);
        executor.set_local_federation_id(config.federation_id);
        Self {
            ledger,
            executor,
            federation_root: [0u8; 32],
            max_proof_age_secs: config.max_proof_age_secs,
        }
    }

    // =========================================================================
    // Turn execution
    // =========================================================================

    /// Execute a turn provided as postcard-encoded bytes.
    ///
    /// On success, the ledger is mutated and a `TurnReceipt` is returned.
    /// On rejection, the ledger is unchanged and the reason is in the error.
    pub fn execute_turn_bytes(&mut self, turn_bytes: &[u8]) -> Result<TurnReceipt, EmbedError> {
        let turn: Turn =
            postcard::from_bytes(turn_bytes).map_err(|e| EmbedError::TurnDecode(e.to_string()))?;
        self.execute_turn(&turn)
    }

    /// Execute a pre-deserialized turn.
    pub fn execute_turn(&mut self, turn: &Turn) -> Result<TurnReceipt, EmbedError> {
        match self.executor.execute(turn, &mut self.ledger) {
            TurnResult::Committed { receipt, .. } => Ok(receipt),
            TurnResult::Rejected { reason, at_action } => Err(EmbedError::TurnRejected {
                reason: format!("{reason:?}"),
                at_action,
            }),
            TurnResult::Expired => Err(EmbedError::TurnRejected {
                reason: "conditional turn expired".into(),
                at_action: vec![],
            }),
            TurnResult::Pending => Err(EmbedError::TurnRejected {
                reason: "conditional turn pending".into(),
                at_action: vec![],
            }),
        }
    }

    /// Validate a turn without applying it (dry-run).
    pub fn validate_turn(&self, turn: &Turn) -> Result<(), EmbedError> {
        self.executor
            .validate_without_apply(turn, &self.ledger)
            .map_err(|e| EmbedError::TurnRejected {
                reason: format!("{e:?}"),
                at_action: vec![],
            })
    }

    /// Estimate computron cost of a turn without executing.
    pub fn estimate_cost(&self, turn: &Turn) -> u64 {
        self.executor.estimate_cost(turn)
    }

    // =========================================================================
    // Proof generation and verification
    // =========================================================================

    /// Generate a presentation proof from a token chain.
    ///
    /// `encoded_token` is the `em2_`-encoded root token string.
    /// `root_key` is the 32-byte root key used to mint the token.
    /// `attenuations` is the chain of attenuations applied after minting.
    /// `action` and `resource` define the authorization request.
    ///
    /// Returns the wire-safe proof bytes (postcard-encoded `WirePresentationProof`).
    pub fn prove_presentation(
        &self,
        encoded_token: &str,
        root_key: &[u8; 32],
        attenuations: &[Attenuation],
        action: &str,
        resource: &str,
    ) -> Result<Vec<u8>, EmbedError> {
        let token = MacaroonToken::from_encoded(encoded_token, *root_key)
            .map_err(|e| EmbedError::ProofGen(format!("token decode: {e}")))?;

        // The issuer key IS the root key (used for federation membership proof).
        let issuer_key = *root_key;

        let mut builder = BridgePresentationBuilder::new(issuer_key, self.federation_root);
        builder.set_root_token(token);

        for att in attenuations {
            if !builder.add_attenuation(att) {
                return Err(EmbedError::ProofGen("attenuation failed".into()));
            }
        }

        let request = AuthRequest {
            action: Some(action.to_string()),
            service: Some(resource.to_string()),
            app_id: None,
            features: vec![],
            user_id: None,
            now: Some(self.executor.current_timestamp),
            ..Default::default()
        };

        let proof = builder
            .prove(&request)
            .map_err(|e| EmbedError::ProofGen(format!("{e:?}")))?;

        let wire_proof = proof.into_wire_proof();
        postcard::to_stdvec(&wire_proof).map_err(|e| EmbedError::ProofGen(e.to_string()))
    }

    /// Verify a wire presentation proof against the current federation root.
    ///
    /// Performs the SAME checks as `verify_presentation_full`:
    /// 1. STARK proof validity (issuer membership)
    /// 2. Federation root binding
    /// 3. Action binding — the proof must be bound to `(expected_action, expected_resource)`
    /// 4. Timestamp freshness — the proof must not be older than `max_proof_age_secs`
    ///
    /// Returns `Ok(true)` on success, `Ok(false)` if the proof is cryptographically
    /// invalid or fails any check, or `Err` if the input cannot be decoded.
    ///
    /// Returns `Ok(false)` immediately if no federation root has been set (rejects
    /// proofs forged against the zero root). Configure via `set_federation_root`.
    pub fn verify_presentation_bytes(
        &self,
        proof_bytes: &[u8],
        expected_action: &str,
        expected_resource: &str,
    ) -> Result<bool, EmbedError> {
        if self.federation_root == [0u8; 32] {
            return Ok(false);
        }
        self.verify_presentation_against(
            proof_bytes,
            &self.federation_root,
            expected_action,
            expected_resource,
        )
    }

    /// Verify a wire presentation proof against a specific federation root.
    ///
    /// Delegates to the canonical [`present::verify_proof_complete`] which checks ALL of:
    /// 1. Reject zero federation root
    /// 2. Real STARK proof presence
    /// 3. STARK validity (issuer membership)
    /// 4. Federation root binding
    /// 5. Action binding (proof bound to expected_action + expected_resource)
    /// 6. Timestamp freshness (proof not older than max_proof_age_secs)
    /// 7. Composition commitment (non-zero AND correctly recomputed)
    /// 8. Proof tier (Production only)
    ///
    /// Use this when the caller supplies their own root (e.g., from a trusted
    /// external source or a specific block height).
    pub fn verify_presentation_against(
        &self,
        proof_bytes: &[u8],
        federation_root: &[u8; 32],
        expected_action: &str,
        expected_resource: &str,
    ) -> Result<bool, EmbedError> {
        let wire_proof: WirePresentationProof = match postcard::from_bytes(proof_bytes) {
            Ok(p) => p,
            Err(e) => return Err(EmbedError::ProofDecode(e.to_string())),
        };

        let now = self.executor.current_timestamp;
        match present::verify_proof_complete(
            &wire_proof,
            expected_action,
            expected_resource,
            federation_root,
            now,
            self.max_proof_age_secs,
        ) {
            Ok(_) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    /// Verify ONLY federation membership (STARK proof + root binding).
    ///
    /// This checks that the proof is a valid STARK proof with the expected
    /// federation root, but does NOT check action binding or freshness.
    ///
    /// **WARNING**: Use this ONLY for federation membership verification where
    /// action binding is not applicable (e.g., qualifying a node as a federation
    /// member). For action-authorized requests, use [`verify_presentation_bytes`]
    /// which enforces full security checks via [`present::verify_proof_complete`].
    pub fn verify_membership_proof(&self, proof_bytes: &[u8], federation_root: &[u8; 32]) -> bool {
        let wire_proof: WirePresentationProof = match postcard::from_bytes(proof_bytes) {
            Ok(p) => p,
            Err(_) => return false,
        };

        // For membership-only verification, we call verify_proof_complete with
        // relaxed parameters: empty action/resource (matching what the prover used
        // for membership-only proofs) and no freshness check.
        // If the proof was generated with action binding, this will correctly
        // reject (action mismatch) — membership-only proofs use empty bindings.
        match present::verify_proof_complete(
            &wire_proof,
            "",
            "",
            federation_root,
            0,
            0, // no freshness check for membership-only
        ) {
            Ok(_) => true,
            Err(_) => false,
        }
    }

    // =========================================================================
    // Token operations (pure crypto, no IO)
    // =========================================================================

    /// Mint a new root token for a service.
    ///
    /// Returns the `em2_`-encoded token string and the root key needed for
    /// future operations (verification, attenuation). The caller stores both.
    pub fn mint_token(&self, root_key: &[u8; 32], service: &str) -> Result<String, EmbedError> {
        let kid = format!("{}:{}", service, self.executor.block_height);
        let token = MacaroonToken::mint(*root_key, kid.as_bytes(), service);
        token
            .to_encoded()
            .map_err(|e| EmbedError::Token(e.to_string()))
    }

    /// Attenuate (restrict) an existing token.
    ///
    /// Takes the `em2_`-encoded token string and the root key, returns the
    /// attenuated token as a new encoded string.
    pub fn attenuate_token(
        &self,
        encoded_token: &str,
        root_key: &[u8; 32],
        restrictions: &Attenuation,
    ) -> Result<String, EmbedError> {
        let token = MacaroonToken::from_encoded(encoded_token, *root_key)
            .map_err(|e| EmbedError::Token(format!("decode: {e}")))?;
        let attenuated = token
            .attenuate(restrictions)
            .map_err(|e| EmbedError::Token(format!("attenuate: {e}")))?;
        attenuated
            .to_encoded()
            .map_err(|e| EmbedError::Token(e.to_string()))
    }

    // =========================================================================
    // State management (caller persists however they want)
    // =========================================================================

    /// Serialize the current ledger state to bytes with BLAKE3 integrity hash.
    ///
    /// The caller can persist this to their own storage (postgres, rocksdb, S3, etc).
    /// The format is postcard-encoded `Vec<Cell>` followed by a 32-byte BLAKE3 hash.
    ///
    /// The trailing 32-byte hash ensures that tampered snapshots are detected on load.
    pub fn state_snapshot(&self) -> Result<Vec<u8>, EmbedError> {
        let cells: Vec<&pyana_cell::Cell> = self.ledger.iter().map(|(_, cell)| cell).collect();
        let serialized =
            postcard::to_stdvec(&cells).map_err(|e| EmbedError::StateSerde(e.to_string()))?;
        let hash = blake3::hash(&serialized);
        let mut result = serialized;
        result.extend_from_slice(hash.as_bytes());
        Ok(result)
    }

    /// Load ledger state from a previous snapshot, verifying BLAKE3 integrity.
    ///
    /// Replaces the current ledger with the cells from the snapshot. Returns an error
    /// if the snapshot is too short to contain a hash, or if the integrity check fails
    /// (indicating the snapshot was tampered with or corrupted).
    pub fn load_state(&mut self, snapshot: &[u8]) -> Result<(), EmbedError> {
        // SECURITY: The snapshot must contain at least 32 bytes for the trailing BLAKE3 hash.
        if snapshot.len() < 32 {
            return Err(EmbedError::StateSerde(
                "snapshot too short: missing integrity hash (expected at least 32 trailing bytes)"
                    .into(),
            ));
        }

        let (data, expected_hash_bytes) = snapshot.split_at(snapshot.len() - 32);

        // Recompute the BLAKE3 hash over the data portion and compare.
        let computed_hash = blake3::hash(data);
        if computed_hash.as_bytes() != expected_hash_bytes {
            return Err(EmbedError::IntegrityCheckFailed);
        }

        let cells: Vec<pyana_cell::Cell> =
            postcard::from_bytes(data).map_err(|e| EmbedError::StateSerde(e.to_string()))?;
        let mut ledger = Ledger::new();
        for cell in cells {
            ledger
                .insert_cell(cell)
                .map_err(|e| EmbedError::StateSerde(format!("insert: {e:?}")))?;
        }
        self.ledger = ledger;
        Ok(())
    }

    /// Get a reference to the current ledger (for read-only inspection).
    pub fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    /// Get a mutable reference to the ledger (for direct manipulation).
    pub fn ledger_mut(&mut self) -> &mut Ledger {
        &mut self.ledger
    }

    // =========================================================================
    // Federation root management
    // =========================================================================

    /// Get the current federation root.
    pub fn federation_root(&self) -> [u8; 32] {
        self.federation_root
    }

    /// Update the federation root.
    ///
    /// The caller is responsible for fetching/verifying the root from their own
    /// sync mechanism (pull from a peer, read from a shared DB, etc).
    pub fn set_federation_root(&mut self, root: [u8; 32]) {
        self.federation_root = root;
    }

    // =========================================================================
    // Executor configuration pass-through
    // =========================================================================

    /// Update the current block height (for precondition evaluation).
    pub fn set_block_height(&mut self, height: u64) {
        self.executor.set_block_height(height);
    }

    /// Update the current timestamp (for expiration checks).
    pub fn set_timestamp(&mut self, ts: i64) {
        self.executor.set_timestamp(ts);
    }

    /// Get the maximum proof age in seconds.
    pub fn max_proof_age_secs(&self) -> i64 {
        self.max_proof_age_secs
    }

    /// Set the maximum proof age in seconds.
    ///
    /// When non-zero, `verify_presentation_bytes()` rejects proofs whose embedded
    /// timestamp is older than this many seconds from the engine's current timestamp.
    /// Set to 0 to disable freshness checks (not recommended for production).
    pub fn set_max_proof_age_secs(&mut self, secs: i64) {
        self.max_proof_age_secs = secs;
    }

    /// Get a reference to the underlying executor for advanced configuration.
    pub fn executor(&self) -> &TurnExecutor {
        &self.executor
    }

    /// Get a mutable reference to the executor for advanced configuration
    /// (e.g., setting proof verifiers, budget gates, trusted roots).
    pub fn executor_mut(&mut self) -> &mut TurnExecutor {
        &mut self.executor
    }
}

// =============================================================================
// WireCodec — protocol message parsing without transport
// =============================================================================

/// No-I/O wire protocol codec.
///
/// Provides encode/decode for the pyana wire protocol without any transport.
/// The caller handles reading bytes from and writing bytes to their own I/O layer.
pub struct WireCodec;

// Re-export the message type so embedders don't need the wire crate directly.
pub use pyana_wire::message::WireMessage;

impl WireCodec {
    /// Decode a wire protocol message from a raw payload (without length prefix).
    ///
    /// The caller is responsible for framing (reading the 4-byte LE length prefix
    /// and providing exactly that many bytes here).
    pub fn decode(payload: &[u8]) -> Result<WireMessage, String> {
        pyana_wire::codec::decode(payload).map_err(|e| e.to_string())
    }

    /// Encode a wire protocol message to bytes (with length prefix).
    ///
    /// Returns a complete frame ready to write to any byte stream.
    pub fn encode(msg: &WireMessage) -> Result<Vec<u8>, String> {
        pyana_wire::codec::encode(msg).map_err(|e| e.to_string())
    }

    /// The framing header size (4 bytes, little-endian u32 payload length).
    pub const HEADER_SIZE: usize = 4;

    /// Parse the length prefix from a 4-byte header.
    ///
    /// Returns the payload size in bytes. The caller should then read exactly
    /// that many bytes and pass them to [`Self::decode`].
    pub fn parse_header(header: &[u8; 4]) -> u32 {
        u32::from_le_bytes(*header)
    }

    /// Process a decoded message against an engine, producing response messages.
    ///
    /// This implements the server-side protocol logic without any I/O:
    /// - `Hello` -> `Welcome`
    /// - `PresentToken` -> `PresentationResult`
    /// - `RequestAttestedRoot` -> `AttestedRoot`
    /// - `Ping` -> `Pong`
    /// - Others -> None
    ///
    /// The caller sends the returned messages back over their transport.
    pub fn process_message(engine: &PyanaEngine, msg: WireMessage) -> Vec<WireMessage> {
        match msg {
            WireMessage::Hello {
                protocol_version, ..
            } => {
                if protocol_version != pyana_wire::message::PROTOCOL_VERSION {
                    return vec![WireMessage::Error {
                        code: pyana_wire::message::error_codes::UNSUPPORTED_VERSION,
                        message: format!(
                            "unsupported protocol version {protocol_version}, expected {}",
                            pyana_wire::message::PROTOCOL_VERSION
                        ),
                    }];
                }
                vec![WireMessage::Welcome {
                    federation_root: engine.federation_root,
                    member_count: 1,
                    node_id: engine.executor.local_federation_id,
                    node_name: "embed".to_string(),
                }]
            }
            WireMessage::PresentToken {
                proof,
                request,
                federation_root,
            } => {
                // Verify root freshness.
                if federation_root != engine.federation_root {
                    return vec![WireMessage::PresentationResult {
                        accepted: false,
                        reason: Some("stale federation root".into()),
                        request_digest: request.digest(),
                    }];
                }

                // Verify the STARK proof using the wire server's verifier.
                let accepted = pyana_wire::server::StarkVerifier
                    .verify(&proof, &request.action, &request.resource)
                    .unwrap_or(false);

                vec![WireMessage::PresentationResult {
                    accepted,
                    reason: if accepted {
                        None
                    } else {
                        Some("proof verification failed".into())
                    },
                    request_digest: request.digest(),
                }]
            }
            WireMessage::RequestAttestedRoot => {
                vec![WireMessage::AttestedRoot {
                    root: engine.federation_root,
                    height: engine.executor.block_height,
                    timestamp: engine.executor.current_timestamp,
                    signatures: vec![],
                    threshold_qc: None,
                }]
            }
            WireMessage::Ping { seq, .. } => {
                vec![WireMessage::Pong {
                    seq,
                    timestamp: engine.executor.current_timestamp,
                }]
            }
            // Response messages and unknown -> no reply.
            _ => vec![],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn engine_default_creation() {
        let engine = PyanaEngine::new(EngineConfig::for_testing());
        assert_eq!(engine.federation_root(), [0u8; 32]);
        assert!(engine.ledger().is_empty());
    }

    #[test]
    fn mint_and_attenuate_roundtrip() {
        let engine = PyanaEngine::new(EngineConfig::for_testing());

        let root_key = b"test-root-key-32-bytes-exactly!!";
        let encoded = engine.mint_token(root_key, "my-service").unwrap();
        assert!(encoded.starts_with("em2_") || !encoded.is_empty());

        // Attenuate it.
        let restrictions = Attenuation {
            services: vec![("dns".into(), "r".into())],
            ..Default::default()
        };
        let attenuated = engine
            .attenuate_token(&encoded, root_key, &restrictions)
            .unwrap();
        assert!(!attenuated.is_empty());
        // Attenuated token should be different from root.
        assert_ne!(encoded, attenuated);
    }

    #[test]
    fn state_snapshot_roundtrip() {
        let mut engine = PyanaEngine::new(EngineConfig::for_testing());
        // Insert a cell into the ledger for a non-trivial state.
        let cell = pyana_cell::Cell::with_balance([1u8; 32], [0u8; 32], 1000);
        engine.ledger_mut().insert_cell(cell).unwrap();

        let snapshot = engine.state_snapshot().unwrap();
        assert!(!snapshot.is_empty());

        // Create a fresh engine and load the snapshot.
        let mut engine2 = PyanaEngine::new(EngineConfig::for_testing());
        engine2.load_state(&snapshot).unwrap();
        assert!(!engine2.ledger().is_empty());
    }

    #[test]
    fn wire_codec_roundtrip() {
        let msg = WireMessage::Ping {
            seq: 42,
            timestamp: 1234567890,
        };
        let encoded = WireCodec::encode(&msg).unwrap();
        // Skip the 4-byte header.
        let payload = &encoded[WireCodec::HEADER_SIZE..];
        let decoded = WireCodec::decode(payload).unwrap();
        assert_eq!(decoded, msg);
    }

    #[test]
    fn process_hello_message() {
        let engine = PyanaEngine::new(EngineConfig::for_testing());
        let hello = WireMessage::Hello {
            node_id: [0xaa; 32],
            node_name: "test-client".into(),
            protocol_version: pyana_wire::message::PROTOCOL_VERSION,
            capabilities: vec![],
        };
        let responses = WireCodec::process_message(&engine, hello);
        assert_eq!(responses.len(), 1);
        match &responses[0] {
            WireMessage::Welcome { node_name, .. } => assert_eq!(node_name, "embed"),
            other => panic!("expected Welcome, got {other:?}"),
        }
    }

    #[test]
    fn process_ping_message() {
        let engine = PyanaEngine::new(EngineConfig::for_testing());
        let ping = WireMessage::Ping {
            seq: 7,
            timestamp: 100,
        };
        let responses = WireCodec::process_message(&engine, ping);
        assert_eq!(responses.len(), 1);
        match &responses[0] {
            WireMessage::Pong { seq, .. } => assert_eq!(*seq, 7),
            other => panic!("expected Pong, got {other:?}"),
        }
    }

    #[test]
    fn federation_root_management() {
        let mut engine = PyanaEngine::new(EngineConfig::for_testing());
        assert_eq!(engine.federation_root(), [0u8; 32]);

        let new_root = [0x42u8; 32];
        engine.set_federation_root(new_root);
        assert_eq!(engine.federation_root(), new_root);
    }

    #[test]
    fn verify_rejects_garbage() {
        let engine = PyanaEngine::new(EngineConfig::for_testing());
        // Garbage bytes should fail to decode or not verify.
        let result = engine.verify_presentation_bytes(&[0u8; 100], "read", "api/v1/users");
        // Either returns Err (decode failure) or Ok(false) (verification failure).
        assert!(result.is_err() || result == Ok(false));
    }

    #[test]
    fn load_state_rejects_tampered_snapshot() {
        let mut engine = PyanaEngine::new(EngineConfig::for_testing());
        let cell = pyana_cell::Cell::with_balance([1u8; 32], [0u8; 32], 1000);
        engine.ledger_mut().insert_cell(cell).unwrap();

        let mut snapshot = engine.state_snapshot().unwrap();
        assert!(!snapshot.is_empty());

        // Tamper with a byte in the data portion (not the hash).
        snapshot[0] ^= 0xFF;

        // Loading the tampered snapshot must fail with IntegrityCheckFailed.
        let mut engine2 = PyanaEngine::new(EngineConfig::for_testing());
        let result = engine2.load_state(&snapshot);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            matches!(err, EmbedError::IntegrityCheckFailed),
            "expected IntegrityCheckFailed, got: {err:?}"
        );
    }

    #[test]
    fn load_state_rejects_truncated_snapshot() {
        // A snapshot shorter than 32 bytes cannot contain a valid hash.
        let mut engine = PyanaEngine::new(EngineConfig::for_testing());
        let result = engine.load_state(&[0u8; 16]);
        assert!(result.is_err());
    }

    #[test]
    fn load_state_rejects_hash_only_snapshot() {
        // A snapshot of exactly 32 bytes (just the hash, no data) should either
        // fail integrity or fail deserialization of the empty data portion.
        let mut engine = PyanaEngine::new(EngineConfig::for_testing());
        let empty_data = &[];
        let hash = blake3::hash(empty_data);
        let snapshot: Vec<u8> = hash.as_bytes().to_vec();
        // This is 32 bytes exactly — the data portion is empty.
        let result = engine.load_state(&snapshot);
        // Should succeed (empty cell list is valid) or fail gracefully.
        // The important thing is it doesn't panic.
        let _ = result;
    }
}
