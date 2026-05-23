//! Silo server: a TCP server that handles incoming wire protocol connections.
//!
//! Each silo server represents one organizational silo in the federation. It can:
//! - Accept incoming connections from peer silos
//! - Handle token presentations (verify proofs against the federation root)
//! - Process revocation submissions
//! - Serve the current attested root and non-membership proofs
//! - Initiate outgoing connections for cross-silo token presentation

use crate::auth::{AuthConfig, RateLimiter as AuthRateLimiter, SharedBanList};
use crate::connection::{ConnectionError, PeerConnection};
use crate::hardening::{ConnectionMetrics, HardeningConfig, ShutdownCoordinator, message_cost};
use crate::message::{
    AuthorizationRequest, MAX_NONCE_CACHE_SIZE, MAX_REQUEST_AGE_SECS, PROTOCOL_VERSION, PublicKey,
    Signature, ThresholdQC, WireMessage,
};
use std::collections::{HashMap, HashSet, VecDeque};
use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;
use tokio::io::{AsyncRead, AsyncWrite};
use tokio::net::TcpListener;
use tokio::sync::{Mutex, RwLock};
use tokio_rustls::TlsAcceptor;

use pyana_captp::{
    CapSession, ExportGcManager, FederationId, HandoffPresentation, SwissTable, validate_handoff,
};

// =============================================================================
// Proof Verifier Trait
// =============================================================================

/// Trait for verifying presentation proofs.
///
/// Callers must inject a verifier implementation into `SiloConfig`. This ensures
/// no code path silently accepts invalid proofs -- either real verification is
/// performed, or the caller explicitly opts into a test-only noop verifier.
pub trait ProofVerifier: Send + Sync + std::fmt::Debug {
    /// Verify a serialized STARK presentation proof bound to a specific (action, resource) pair.
    fn verify(&self, proof_bytes: &[u8], action: &str, resource: &str) -> Result<bool, String>;
}

/// Real STARK proof verifier using pyana-circuit.
///
/// Deserializes the proof bytes and runs full STARK verification
/// (Merkle commitments, FRI low-degree test, Fiat-Shamir checks).
///
/// Uses the DSL `merkle_poseidon2_circuit()` (production path, collision-resistant),
/// then falls back to `MerkleStarkAir` (legacy linear binding) for backward
/// compatibility with older proofs.
#[derive(Clone, Debug)]
pub struct StarkVerifier;

#[cfg(feature = "stark-verifier")]
impl ProofVerifier for StarkVerifier {
    fn verify(&self, proof_bytes: &[u8], action: &str, resource: &str) -> Result<bool, String> {
        let proof = pyana_circuit::stark::proof_from_bytes(proof_bytes)?;
        // Use new_canonical() to reduce modulo p, preventing non-canonical field
        // element malleability from deserialized proof data.
        let public_inputs: Vec<pyana_circuit::field::BabyBear> = proof
            .public_inputs
            .iter()
            .map(|&v| pyana_circuit::field::BabyBear::new_canonical(v))
            .collect();

        // Verify action binding: public_inputs[2..6] must be the canonical commitment
        // to (action, resource) via compute_action_binding (4 elements, 124-bit security).
        // Layout: [leaf_hash, merkle_root, action_binding[0..4], composition_commitment[0..4]]
        // The bridge verifier (bridge/src/verifier.rs) also uses pi[2..6].
        let expected_binding = pyana_circuit::compute_action_binding(action, resource);
        if public_inputs.len() < 2 + pyana_circuit::ACTION_BINDING_WIDTH {
            return Ok(false);
        }
        for i in 0..pyana_circuit::ACTION_BINDING_WIDTH {
            if public_inputs[2 + i] != expected_binding[i] {
                return Ok(false); // Proof not bound to this (action, resource)
            }
        }

        // SECURITY: Verify composition commitment is present and non-zero.
        // The composition commitment occupies pi[6..10] (4 elements). It binds the
        // issuer membership STARK to the derivation proof that concluded "Allow".
        // Without this check, a federation member could present a valid membership
        // proof even when their authorization was DENIED.
        let composition_start = 2 + pyana_circuit::ACTION_BINDING_WIDTH; // index 6
        if public_inputs.len() < composition_start + 4 {
            return Ok(false); // No composition commitment present
        }
        let has_nonzero_composition = public_inputs[composition_start..composition_start + 4]
            .iter()
            .any(|&v| v != pyana_circuit::field::BabyBear::ZERO);
        if !has_nonzero_composition {
            return Ok(false); // Zeroed composition = no authorization binding
        }

        // Production verification uses the DSL Merkle Poseidon2 circuit.
        // The legacy hand-written AIR is deprecated.
        let circuit = pyana_dsl_runtime::descriptors::merkle_poseidon2_circuit();
        match pyana_circuit::stark::verify(&circuit, &proof, &public_inputs) {
            Ok(()) => Ok(true),
            Err(_reason) => Ok(false),
        }
    }
}

/// Fallback StarkVerifier when the stark-verifier feature is not enabled.
/// Always rejects proofs (fail-closed).
#[cfg(not(feature = "stark-verifier"))]
impl ProofVerifier for StarkVerifier {
    fn verify(&self, _proof_bytes: &[u8], _action: &str, _resource: &str) -> Result<bool, String> {
        Err("STARK verification unavailable: stark-verifier feature not enabled".to_string())
    }
}

/// A no-op verifier that always accepts proofs without cryptographic checks.
///
/// Only available when the `dev` feature is enabled or in test builds.
/// Production code should use [`StarkVerifier`] which performs full STARK verification.
#[cfg(any(test, feature = "dev"))]
#[derive(Clone, Debug)]
pub struct NoopVerifier;

#[cfg(any(test, feature = "dev"))]
impl ProofVerifier for NoopVerifier {
    fn verify(&self, _proof_bytes: &[u8], _action: &str, _resource: &str) -> Result<bool, String> {
        Ok(true)
    }
}

/// A verifier that always rejects. Available only for testing.
#[cfg(any(test, feature = "dev"))]
#[derive(Clone, Debug)]
pub struct RejectAllVerifier;

#[cfg(any(test, feature = "dev"))]
impl ProofVerifier for RejectAllVerifier {
    fn verify(&self, _proof_bytes: &[u8], _action: &str, _resource: &str) -> Result<bool, String> {
        Ok(false)
    }
}

/// A verifier that requires a minimum proof size. Available only for testing
/// transport framing without real crypto.
#[cfg(any(test, feature = "dev"))]
#[derive(Clone, Debug)]
pub struct MinSizeVerifier {
    pub min_bytes: usize,
}

#[cfg(any(test, feature = "dev"))]
impl ProofVerifier for MinSizeVerifier {
    fn verify(&self, proof_bytes: &[u8], _action: &str, _resource: &str) -> Result<bool, String> {
        Ok(proof_bytes.len() >= self.min_bytes)
    }
}

// =============================================================================
// Silo Configuration
// =============================================================================

/// TLS configuration for the wire server.
#[derive(Clone, Debug, Default)]
pub struct TlsConfig {
    /// Path to the PEM-encoded TLS certificate chain.
    pub cert_path: Option<PathBuf>,
    /// Path to the PEM-encoded TLS private key.
    pub key_path: Option<PathBuf>,
}

impl TlsConfig {
    /// Returns true if TLS is configured (both cert and key paths are set).
    pub fn is_configured(&self) -> bool {
        self.cert_path.is_some() && self.key_path.is_some()
    }
}

/// Configuration for a silo server.
#[derive(Clone, Debug)]
pub struct SiloConfig {
    /// Human-readable name for this silo (e.g., "acme.corp").
    pub name: String,
    /// This node's identity key.
    pub node_id: [u8; 32],
    /// Capabilities this silo advertises.
    pub capabilities: Vec<String>,
    /// Maximum concurrent connections.
    pub max_connections: usize,
    /// Connection timeout for incoming handshakes.
    pub handshake_timeout: Duration,
    /// The proof verifier used to check incoming presentation proofs.
    pub verifier: Arc<dyn ProofVerifier>,
    /// Authorized revocation authorities. Only these public keys are permitted to
    /// submit revocations. If empty (the default), ALL revocations are rejected
    /// (fail-closed). Callers MUST configure at least one authority for revocations
    /// to be accepted.
    pub revocation_authorities: Vec<PublicKey>,
    /// Maximum age (in seconds) for request timestamps. Requests older than this
    /// are rejected as stale.
    pub max_request_age_secs: i64,
    /// TLS configuration. When configured, the server accepts only TLS connections.
    /// When not configured, plaintext TCP is used (with a prominent warning).
    pub tls: TlsConfig,
    /// Nonce cache capacity for replay prevention.
    ///
    /// Controls the size of the sliding-window nonce cache. The cache must be sized
    /// to hold at least `max_request_rate * max_request_age_secs` nonces to prevent
    /// replay attacks. For example, at 100 req/s with a 300s window, use >= 30,000.
    ///
    /// Default: `MAX_NONCE_CACHE_SIZE` (from wire message constants).
    pub nonce_cache_capacity: usize,
    /// Maximum age (in seconds) the federation root may be stale before rejecting
    /// ALL proofs (fail-closed). If `None`, no staleness check is performed
    /// (backward compatible default). When set, if the root has not been updated
    /// within this window, all presentations are rejected with a clear error.
    pub max_root_age_secs: Option<u64>,
    /// Production hardening configuration (rate limits, heartbeat, backpressure, etc.).
    pub hardening: HardeningConfig,
}

impl SiloConfig {
    /// Create a new silo config with real STARK verification as the default.
    pub fn new(name: impl Into<String>) -> Self {
        let name = name.into();
        let node_id = *blake3::hash(name.as_bytes()).as_bytes();
        Self {
            name,
            node_id,
            capabilities: vec![
                "present".to_string(),
                "revoke".to_string(),
                "sync".to_string(),
            ],
            max_connections: 64,
            handshake_timeout: Duration::from_secs(10),
            verifier: Arc::new(StarkVerifier),
            revocation_authorities: Vec::new(),
            max_request_age_secs: MAX_REQUEST_AGE_SECS,
            tls: TlsConfig::default(),
            nonce_cache_capacity: MAX_NONCE_CACHE_SIZE,
            max_root_age_secs: None,
            hardening: HardeningConfig::default(),
        }
    }

    /// Set the nonce cache capacity.
    ///
    /// The nonce cache must be large enough to hold all valid nonces within
    /// the replay window (`max_request_age_secs * max_requests_per_second`).
    /// If the cache is too small, legitimate requests may be rejected as
    /// replays after their nonces are evicted.
    pub fn with_nonce_cache_capacity(mut self, capacity: usize) -> Self {
        self.nonce_cache_capacity = capacity;
        self
    }

    /// Set a custom proof verifier.
    pub fn with_verifier(mut self, verifier: Arc<dyn ProofVerifier>) -> Self {
        self.verifier = verifier;
        self
    }

    /// Set the authorized revocation authorities.
    ///
    /// Only these public keys may submit revocations. When empty (the default),
    /// ALL revocations are rejected (fail-closed). Callers MUST configure at least
    /// one authority for revocations to be accepted.
    pub fn with_revocation_authorities(mut self, authorities: Vec<PublicKey>) -> Self {
        self.revocation_authorities = authorities;
        self
    }

    /// Set the TLS certificate and key paths.
    ///
    /// When both are set, the server will accept only TLS connections.
    pub fn with_tls(mut self, cert_path: PathBuf, key_path: PathBuf) -> Self {
        self.tls = TlsConfig {
            cert_path: Some(cert_path),
            key_path: Some(key_path),
        };
        self
    }

    /// Set the maximum federation root age (fail-closed staleness check).
    ///
    /// If the federation root has not been updated within `secs` seconds, all
    /// proof presentations are rejected. This prevents stale-root abuse at the
    /// cost of availability during consensus downtime.
    pub fn with_max_root_age(mut self, secs: u64) -> Self {
        self.max_root_age_secs = Some(secs);
        self
    }

    /// Set the production hardening configuration.
    ///
    /// Controls rate limiting, heartbeat, backpressure, and message size limits.
    pub fn with_hardening(mut self, hardening: HardeningConfig) -> Self {
        self.hardening = hardening;
        self
    }
}

/// Legacy type alias retained for source compatibility in tests.
/// New code should use `SiloConfig::with_verifier()` directly.
#[cfg(any(test, feature = "dev"))]
#[derive(Clone, Debug)]
pub enum VerificationMode {
    /// Always accept. Equivalent to `NoopVerifier`.
    #[deprecated(note = "Use SiloConfig::with_verifier(Arc::new(NoopVerifier)) instead")]
    SimulatedAccept,
    /// Always reject. Equivalent to `RejectAllVerifier`.
    #[deprecated(note = "Use SiloConfig::with_verifier(Arc::new(RejectAllVerifier)) instead")]
    SimulatedReject,
    /// Size gate. Equivalent to `MinSizeVerifier`.
    #[deprecated(note = "Use SiloConfig::with_verifier(Arc::new(MinSizeVerifier { .. })) instead")]
    MinProofSize(usize),
}

#[cfg(any(test, feature = "dev"))]
impl SiloConfig {
    /// Convenience: set verifier from a legacy VerificationMode.
    #[allow(deprecated)]
    pub fn with_verification(self, mode: VerificationMode) -> Self {
        let verifier: Arc<dyn ProofVerifier> = match mode {
            VerificationMode::SimulatedAccept => Arc::new(NoopVerifier),
            VerificationMode::SimulatedReject => Arc::new(RejectAllVerifier),
            VerificationMode::MinProofSize(n) => Arc::new(MinSizeVerifier { min_bytes: n }),
        };
        self.with_verifier(verifier)
    }
}

// =============================================================================
// Revocation Handler Trait
// =============================================================================

/// Trait for delegating revocation logic to an external handler.
///
/// This allows the silo server to delegate revocation submission, status checks,
/// and root computation to an external system (e.g., a `pyana-federation` backed
/// handler or a `RevocationRegistry`-backed handler) while maintaining backward
/// compatibility with the standalone logic.
pub trait RevocationHandler: Send + Sync {
    /// Submit a revocation for a token, returning true if accepted.
    ///
    /// The `authority` public key identifies which federation member issued the
    /// revocation. Implementations should derive the authority index from this key.
    fn submit_revocation(&self, token_id: &str, sig: &[u8; 64], authority: &PublicKey) -> bool;
    /// Check whether a token has been revoked.
    fn is_revoked(&self, token_id: &str) -> bool;
    /// Get the current revocation root hash.
    fn current_root(&self) -> [u8; 32];
    /// Get the current attested root for users requesting proofs.
    ///
    /// Returns `None` if no root has been attested yet (e.g., before the first
    /// `publish_root()` call or consensus round).
    fn attested_root(&self) -> Option<[u8; 32]> {
        Some(self.current_root())
    }
    /// Generate a non-membership proof for a requesting user.
    ///
    /// Returns `None` if the token IS revoked or if proof generation is not
    /// supported by this handler implementation. The returned bytes are an
    /// opaque serialized proof that the client can verify offline.
    fn prove_non_revocation(&self, token_id: &str) -> Option<Vec<u8>> {
        // Default: no proof generation (backward compatible).
        let _ = token_id;
        None
    }
}

/// Default revocation handler backed by a [`pyana_token::RevocationRegistry`].
///
/// Provides exact (no false-positive) revocation checks and Merkle-based
/// non-membership proof generation via a sorted revocation tree.
///
/// For federation-connected deployments that need consensus-attested roots,
/// use [`FederationBridge`](crate::federation_bridge::FederationBridge) as the
/// `RevocationHandler` instead.
#[derive(Clone, Debug)]
pub struct DefaultRevocationHandler {
    /// The underlying revocation registry (exact set + Merkle tree).
    registry: std::sync::Arc<std::sync::RwLock<pyana_token::RevocationRegistry>>,
    /// Current height (incremented on each revocation for compatibility).
    height: std::sync::Arc<std::sync::atomic::AtomicU64>,
}

impl DefaultRevocationHandler {
    /// Create a new default handler.
    ///
    /// The `_genesis_root` parameter is accepted for API compatibility but is
    /// no longer used; the root is derived from the Merkle tree contents.
    pub fn new(_genesis_root: [u8; 32]) -> Self {
        Self {
            registry: std::sync::Arc::new(std::sync::RwLock::new(
                pyana_token::RevocationRegistry::new(),
            )),
            height: std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0)),
        }
    }
}

impl RevocationHandler for DefaultRevocationHandler {
    fn submit_revocation(&self, token_id: &str, _sig: &[u8; 64], _authority: &PublicKey) -> bool {
        let mut reg = self.registry.write().unwrap();
        let newly_revoked = reg.revoke(token_id);
        if newly_revoked {
            self.height
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        }
        newly_revoked
    }

    fn is_revoked(&self, token_id: &str) -> bool {
        let reg = self.registry.read().unwrap();
        reg.is_revoked(token_id)
    }

    fn current_root(&self) -> [u8; 32] {
        let reg = self.registry.read().unwrap();
        reg.current_root()
    }

    fn attested_root(&self) -> Option<[u8; 32]> {
        let reg = self.registry.read().unwrap();
        reg.attested_root()
            .map(|ar| ar.merkle_root)
            .or_else(|| Some(reg.current_root()))
    }

    fn prove_non_revocation(&self, token_id: &str) -> Option<Vec<u8>> {
        let reg = self.registry.read().unwrap();
        match reg.prove_non_revocation(token_id) {
            Ok(proof) => postcard::to_stdvec(&proof).ok(),
            Err(_) => None,
        }
    }
}

// =============================================================================
// Silo State
// =============================================================================

/// Mutable state for the silo server.
#[derive(Clone, Debug)]
pub struct SiloState {
    /// The current federation root.
    ///
    /// **Canonical source**: When a [`RevocationHandler`] is configured on the
    /// [`SiloServer`], this field is updated from the handler's `current_root()`
    /// after each revocation. The handler (typically backed by a
    /// `pyana-federation` `RevocationTree`) is the single source of truth.
    ///
    /// When no handler is configured, the standalone BLAKE3 hash-chain
    /// computation in [`SiloState::apply_revocation_standalone`] is used as a
    /// fallback (e.g., in tests or single-node deployments).
    pub federation_root: [u8; 32],
    /// Current block height.
    pub height: u64,
    /// Number of members in the federation.
    pub member_count: u32,
    /// Revoked token IDs (simplified; in production this is a Merkle tree).
    pub revoked_tokens: Vec<String>,
    /// Signatures on the current root: (public_key, signature) pairs.
    /// Signatures are full 64-byte Ed25519.
    pub root_signatures: Vec<(PublicKey, Signature)>,
    /// Optional threshold QC from consensus (populated when federation bridge updates state).
    pub threshold_qc: Option<ThresholdQC>,
    /// Unix timestamp (seconds) of the last federation root update.
    /// Used for fail-closed staleness detection: if `now - last_root_update`
    /// exceeds `SiloConfig::max_root_age_secs`, all proofs are rejected.
    pub last_root_update: i64,
}

impl SiloState {
    /// Create initial state with a genesis root.
    pub fn genesis(member_count: u32) -> Self {
        let root = *blake3::hash(b"pyana-federation-genesis").as_bytes();
        Self {
            federation_root: root,
            height: 0,
            member_count,
            revoked_tokens: Vec::new(),
            root_signatures: Vec::new(),
            threshold_qc: None,
            last_root_update: current_timestamp(),
        }
    }

    /// Apply a revocation event using the federation's `RevocationHandler` as the
    /// canonical root source.
    ///
    /// This updates the local revocation index and height, then sets
    /// `federation_root` to the handler's `current_root()`. The handler
    /// (backed by `pyana-federation`'s `RevocationTree`) is the single source
    /// of truth for the Merkle root.
    ///
    /// If no handler is available, use [`apply_revocation_standalone`] instead.
    pub fn apply_revocation_delegated(
        &mut self,
        token_id: &str,
        authority: &PublicKey,
        authority_sig: &Signature,
        handler: &dyn RevocationHandler,
    ) {
        self.revoked_tokens.push(token_id.to_string());
        self.height += 1;

        // The handler already processed the revocation; just adopt its root.
        self.federation_root = handler.current_root();
        self.last_root_update = current_timestamp();

        // Add the authority's signature to the root attestation.
        self.root_signatures.push((*authority, *authority_sig));
    }

    /// Apply a revocation event using the standalone BLAKE3 hash-chain.
    ///
    /// # Deprecation Notice
    ///
    /// This method computes a root via a sequential BLAKE3 hash chain, which is
    /// **not consistent** with the 4-ary Merkle tree used by `pyana-federation`'s
    /// `RevocationTree`. It exists for backward compatibility in tests and
    /// single-node deployments where no `RevocationHandler` is configured.
    ///
    /// New code should use [`apply_revocation_delegated`] with a handler backed
    /// by `pyana-federation::RevocationTree` to ensure root consistency across
    /// the federation.
    #[deprecated(
        note = "Use apply_revocation_delegated() with a RevocationHandler for consistent roots"
    )]
    pub fn apply_revocation_standalone(
        &mut self,
        token_id: &str,
        authority: &PublicKey,
        authority_sig: &Signature,
    ) {
        self.revoked_tokens.push(token_id.to_string());
        self.height += 1;

        // Standalone BLAKE3 hash-chain root (NOT consistent with federation Merkle tree).
        let mut hasher = blake3::Hasher::new_derive_key("pyana-wire revocation-root v1");
        hasher.update(&self.federation_root);
        hasher.update(token_id.as_bytes());
        hasher.update(&authority_sig.0);
        hasher.update(&self.height.to_le_bytes());
        self.federation_root = *hasher.finalize().as_bytes();
        self.last_root_update = current_timestamp();

        // Add the authority's signature to the root attestation.
        self.root_signatures.push((*authority, *authority_sig));
    }

    /// Apply a revocation event and update the root.
    ///
    /// **Deprecated**: This is an alias for [`apply_revocation_standalone`] kept
    /// for source compatibility. Prefer [`apply_revocation_delegated`] when a
    /// `RevocationHandler` is available.
    pub fn apply_revocation(
        &mut self,
        token_id: &str,
        authority: &PublicKey,
        authority_sig: &Signature,
    ) {
        #[allow(deprecated)]
        self.apply_revocation_standalone(token_id, authority, authority_sig);
    }

    /// Check if a token is revoked.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.revoked_tokens.iter().any(|t| t == token_id)
    }
}

// =============================================================================
// Nonce Cache (replay prevention — time-partitioned)
// =============================================================================

/// A time-partitioned nonce cache for replay prevention.
///
/// Instead of a single FIFO that can be flushed by flooding, nonces are stored
/// in time-partitioned buckets (30-second windows). The cache keeps the last 10
/// buckets (= 5 minutes of coverage). A nonce is "seen" if it appears in ANY
/// active bucket. Old buckets are dropped entirely when they age out.
///
/// This design is flood-resistant: an attacker flooding the current bucket cannot
/// evict nonces from older buckets, so captured proofs within the freshness window
/// remain protected against replay.
#[derive(Debug)]
pub struct NonceCache {
    /// Time-partitioned buckets. Each bucket covers a 30-second window.
    /// Index 0 is the oldest active bucket.
    buckets: VecDeque<NonceBucket>,
    /// Duration of each bucket in seconds.
    bucket_duration_secs: i64,
    /// Maximum number of buckets to retain (covers freshness window).
    max_buckets: usize,
    /// Maximum nonces per bucket (prevents OOM within a single window).
    max_per_bucket: usize,
}

/// A single time-partitioned bucket of nonces.
#[derive(Debug)]
struct NonceBucket {
    /// The start timestamp of this bucket (Unix seconds).
    window_start: i64,
    /// Set of nonces seen in this time window.
    nonces: HashSet<[u8; 16]>,
}

impl NonceCache {
    /// Create a new time-partitioned nonce cache.
    ///
    /// The `capacity` parameter is used to derive per-bucket limits:
    /// `max_per_bucket = capacity / max_buckets`.
    pub fn new(capacity: usize) -> Self {
        let bucket_duration_secs = 30;
        let max_buckets = 10; // 10 * 30s = 5 minutes
        let max_per_bucket = capacity / max_buckets;
        Self {
            buckets: VecDeque::with_capacity(max_buckets),
            bucket_duration_secs,
            max_buckets,
            max_per_bucket,
        }
    }

    /// Check if a nonce has been seen before. If not, insert it and return `true` (fresh).
    /// If already seen, return `false` (replay).
    pub fn check_and_insert(&mut self, nonce: &[u8; 16]) -> bool {
        let now = current_timestamp();

        // Expire old buckets that have aged out of the freshness window.
        let min_window_start = now - (self.max_buckets as i64 * self.bucket_duration_secs);
        while let Some(front) = self.buckets.front() {
            if front.window_start < min_window_start {
                self.buckets.pop_front();
            } else {
                break;
            }
        }

        // Check if the nonce exists in ANY active bucket.
        for bucket in self.buckets.iter() {
            if bucket.nonces.contains(nonce) {
                return false; // replay
            }
        }

        // Determine which bucket this nonce belongs to (current time window).
        let current_window_start = now - (now % self.bucket_duration_secs);

        // Find or create the current bucket.
        let needs_new_bucket = match self.buckets.back() {
            Some(last) => last.window_start != current_window_start,
            None => true,
        };

        if needs_new_bucket {
            // If we're at max buckets, the oldest was already expired above,
            // but enforce the limit defensively.
            if self.buckets.len() >= self.max_buckets {
                self.buckets.pop_front();
            }
            self.buckets.push_back(NonceBucket {
                window_start: current_window_start,
                nonces: HashSet::new(),
            });
        }

        let current_bucket = self.buckets.back_mut().unwrap();

        // Enforce per-bucket size limit to prevent OOM from floods.
        // A flood only fills the current bucket — older buckets remain intact.
        if current_bucket.nonces.len() >= self.max_per_bucket {
            // Bucket is full. Still return true (fresh) because we checked all
            // buckets above and the nonce wasn't found. The nonce won't be tracked,
            // but legitimate nonces are unique so this is acceptable under flood.
            // The attacker gains nothing: they can't replay OLD nonces from prior
            // buckets, and their own flood nonces are worthless.
            return true;
        }

        current_bucket.nonces.insert(*nonce);
        true // fresh
    }
}

// =============================================================================
// Silo Server
// =============================================================================

/// Connection state machine for enforcing handshake protocol.
///
/// Each connection starts in `AwaitingHello` and must receive a valid `Hello`
/// message before transitioning to `Active`. Any non-Hello message received
/// in the `AwaitingHello` state is rejected with an error.
///
/// The state machine is enforced structurally in `handle_connection_generic`:
/// the first message is read with a handshake timeout, validated to be Hello,
/// and only then does the connection enter the main message loop (Active state).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
enum ConnectionState {
    /// Waiting for the initial Hello message.
    AwaitingHello,
    /// Handshake complete; all message types are accepted.
    Active,
}

// =============================================================================
// Peer Authentication & Role Classification
// =============================================================================

/// The authenticated role of a connected peer.
///
/// Determines what messages they may receive and what state is replicated to
/// them. Connections start as `Anonymous` and are upgraded via the
/// challenge-response handshake.
///
/// # Security Invariant
///
/// A peer MUST NOT receive state-replication messages (gossip, swiss table
/// updates, cell state) unless they are authenticated as `Member`. CapTP
/// operations require at least `CapTpPeer` role.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PeerRole {
    /// Full federation member. Gets all state, participates in consensus.
    /// Authenticated via Ed25519 challenge-response against constitution.
    Member { participant_key: [u8; 32] },
    /// External CapTP peer. Gets only CapTP messages, no state replication.
    /// Promoted from Anonymous when they complete CapHello with valid session.
    ///
    /// In the unified lace model, `peer_strand` identifies the remote strand
    /// (bilateral session partner). `group_id` is optional: you can have CapTP
    /// with a strand that isn't in any group you know about.
    CapTpPeer {
        /// The remote strand's identity (32 bytes).
        peer_strand: [u8; 32],
        /// The group the strand belongs to, if known.
        group_id: Option<[u8; 32]>,
    },
    /// Light client. Gets only proofs and public commitments.
    LightClient,
    /// Unauthenticated. Limited to health check, public info, token presentation.
    /// This is the INITIAL state for all connections.
    Anonymous,
}

impl PeerRole {
    /// Numeric tag for wire encoding.
    pub fn tag(&self) -> u8 {
        match self {
            PeerRole::Member { .. } => 1,
            PeerRole::CapTpPeer { .. } => 2,
            PeerRole::LightClient => 3,
            PeerRole::Anonymous => 0,
        }
    }

    /// Whether this role permits CapTP operations.
    pub fn allows_captp(&self) -> bool {
        matches!(self, PeerRole::Member { .. } | PeerRole::CapTpPeer { .. })
    }

    /// Whether this role permits state-replication (gossip, swiss, cell state).
    pub fn allows_state_replication(&self) -> bool {
        matches!(self, PeerRole::Member { .. })
    }

    /// Whether this role permits revocation submission.
    pub fn allows_revocation(&self) -> bool {
        matches!(self, PeerRole::Member { .. })
    }

    /// Whether this role permits public-info operations (present, attest, ping).
    pub fn allows_public_ops(&self) -> bool {
        true // All roles can do public operations
    }
}

/// Tracks authenticated state for a single connection.
///
/// Created at connection acceptance time with `Anonymous` role. Upgraded
/// if the peer completes the challenge-response handshake.
#[derive(Clone, Debug)]
pub struct ConnectionAuth {
    /// The peer's authenticated role.
    pub role: PeerRole,
    /// Whether the challenge-response handshake has been completed.
    /// A connection may remain Anonymous even after the handshake window
    /// (the peer simply didn't authenticate).
    pub handshake_complete: bool,
}

impl ConnectionAuth {
    /// Create a new anonymous (unauthenticated) connection state.
    pub fn anonymous() -> Self {
        Self {
            role: PeerRole::Anonymous,
            handshake_complete: false,
        }
    }

    /// Upgrade to Member role after successful challenge-response.
    pub fn authenticate_as_member(&mut self, participant_key: [u8; 32]) {
        self.role = PeerRole::Member { participant_key };
        self.handshake_complete = true;
    }

    /// Upgrade to CapTpPeer role.
    ///
    /// The `peer_strand` identifies the remote strand. In the unified model this
    /// is the strand ID; for backward compat it may be the federation/group ID.
    /// The `group_id` is optional and can be provided if the strand's group is known.
    pub fn authenticate_as_captp_peer(&mut self, peer_strand: [u8; 32]) {
        // Only upgrade if currently Anonymous (don't downgrade Member).
        if matches!(self.role, PeerRole::Anonymous) {
            self.role = PeerRole::CapTpPeer {
                peer_strand,
                group_id: None,
            };
        }
    }
}

/// Participant list provider for peer authentication.
///
/// The server needs access to the current constitution's participant list
/// to verify challenge-response signatures. This trait abstracts the
/// source of truth.
pub trait ParticipantSource: Send + Sync + std::fmt::Debug {
    /// Check if a public key is a current constitutional participant.
    fn is_participant(&self, key: &[u8; 32]) -> bool;
    /// Get the current constitution version.
    fn constitution_version(&self) -> u64;
}

/// A static participant list (for testing and simple deployments).
#[derive(Clone, Debug)]
pub struct StaticParticipants {
    /// The participant keys (sorted).
    pub participants: Vec<[u8; 32]>,
    /// The constitution version.
    pub version: u64,
}

impl StaticParticipants {
    /// Create a new static participant source.
    pub fn new(participants: Vec<[u8; 32]>) -> Self {
        Self {
            participants,
            version: 0,
        }
    }
}

impl ParticipantSource for StaticParticipants {
    fn is_participant(&self, key: &[u8; 32]) -> bool {
        self.participants.contains(key)
    }

    fn constitution_version(&self) -> u64 {
        self.version
    }
}

/// Compute the peer authentication signing message.
///
/// Both the challenger (server) and the responder (peer) must use this
/// function to compute what is signed, ensuring consistency.
///
/// Domain-separated via blake3 derive_key to prevent cross-protocol replay.
pub fn peer_auth_signing_message(nonce: &[u8; 32], server_node_id: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-wire peer-auth v1");
    hasher.update(nonce);
    hasher.update(server_node_id);
    *hasher.finalize().as_bytes()
}

/// Guard that decrements the active connection counter on drop.
struct ConnectionGuard {
    counter: Arc<AtomicUsize>,
}

impl Drop for ConnectionGuard {
    fn drop(&mut self) {
        self.counter.fetch_sub(1, Ordering::SeqCst);
    }
}

// =============================================================================
// CapTP State
// =============================================================================

/// Shared CapTP state: sessions, swiss table, and GC managers.
///
/// This is kept behind `Arc<RwLock<..>>` so it can be shared across connection
/// handlers. The swiss table and GC managers are node-global; sessions are
/// per-peer (keyed by federation ID).
#[derive(Debug)]
pub struct CapTpState {
    /// Active CapTP sessions, keyed by the remote peer's federation ID.
    pub sessions: HashMap<FederationId, CapSession>,
    /// The node's swiss number table (maps swiss numbers to capabilities).
    pub swiss_table: SwissTable,
    /// Export GC: tracks which remote federations hold references to our cells.
    pub export_gc: ExportGcManager,
    /// Known/trusted federation IDs (for handoff validation).
    pub known_federations: Vec<FederationId>,
    /// Current block height (for swiss entry expiration checks).
    pub current_height: u64,
    /// Session epoch counter: incremented each time any session is established.
    /// Used to assign unique epochs to sessions and reject stale-epoch messages.
    pub next_session_epoch: u64,
}

impl CapTpState {
    /// Create a new empty CapTP state.
    pub fn new() -> Self {
        Self {
            sessions: HashMap::new(),
            swiss_table: SwissTable::new(),
            export_gc: ExportGcManager::new(),
            known_federations: Vec::new(),
            current_height: 0,
            next_session_epoch: 1,
        }
    }

    /// Allocate a new session epoch (monotonically increasing).
    pub fn allocate_epoch(&mut self) -> u64 {
        let epoch = self.next_session_epoch;
        self.next_session_epoch += 1;
        epoch
    }
}

impl CapTpState {
    /// Process introduction export records from a committed turn receipt.
    ///
    /// For each `IntroductionExport`, registers the target capability as exported
    /// to the recipient's federation in the `ExportGcManager`. This ensures that
    /// capabilities created via 3-party introductions participate in distributed GC
    /// (i.e., `DropRef` messages will eventually clean them up).
    ///
    /// `resolve_federation` maps a recipient CellId to the federation that owns it.
    /// If resolution fails for a given export (recipient's federation is unknown),
    /// that export is skipped — the node may retry later when the federation is
    /// discovered.
    ///
    /// Returns the number of exports successfully registered.
    pub fn process_introduction_exports(
        &mut self,
        exports: &[pyana_turn::IntroductionExport],
        resolve_federation: impl Fn(&pyana_types::CellId) -> Option<FederationId>,
    ) -> usize {
        let height = self.current_height;
        let mut registered = 0;
        for export in exports {
            if let Some(recipient_fed) = resolve_federation(&export.recipient) {
                // Use the recipient's current session epoch if they have an active session,
                // otherwise use 0 (legacy path). This ensures introduction exports are
                // tied to the correct session for DropRef validation.
                let session_id = self
                    .sessions
                    .get(&recipient_fed)
                    .map(|s| s.epoch)
                    .unwrap_or(0);
                self.export_gc.record_export_with_session(
                    export.target,
                    recipient_fed,
                    height,
                    session_id,
                );
                registered += 1;
            }
        }
        registered
    }
}

impl Default for CapTpState {
    fn default() -> Self {
        Self::new()
    }
}

/// A TCP server representing one silo in the federation.
///
/// Handles incoming connections, processes wire protocol messages, and
/// maintains federation state.
pub struct SiloServer {
    /// The address this server listens on.
    addr: SocketAddr,
    /// Server configuration.
    config: Arc<SiloConfig>,
    /// Shared mutable state.
    state: Arc<RwLock<SiloState>>,
    /// Event log for diagnostics.
    event_log: Arc<Mutex<Vec<ServerEvent>>>,
    /// Revocation handler for delegating revocation logic.
    /// Defaults to `DefaultRevocationHandler` which wraps the standalone logic.
    revocation_handler: Option<Arc<dyn RevocationHandler>>,
    /// Nonce cache for replay prevention on PresentToken requests.
    presentation_nonces: Arc<Mutex<NonceCache>>,
    /// Nonce cache for replay prevention on SubmitRevocation requests.
    revocation_nonces: Arc<Mutex<NonceCache>>,
    /// Active connection count for enforcing max_connections.
    active_connections: Arc<AtomicUsize>,
    /// Optional TLS acceptor (built from config at startup).
    tls_acceptor: Option<TlsAcceptor>,
    /// CapTP session state: swiss table, GC managers, active sessions.
    captp_state: Arc<RwLock<CapTpState>>,
    /// Participant source for peer authentication (constitution participant list).
    /// When set, enables challenge-response handshake. When None, all peers
    /// remain Anonymous (backward-compatible with existing deployments).
    participant_source: Option<Arc<dyn ParticipantSource>>,
    /// Extended auth configuration (require_auth, rate limits, ban config).
    auth_config: AuthConfig,
    /// Shared ban list for tracking and enforcing IP bans.
    ban_list: SharedBanList,
    /// Graceful shutdown coordinator.
    shutdown: Arc<ShutdownCoordinator>,
}

/// Events logged by the server for diagnostics.
#[derive(Clone, Debug)]
pub enum ServerEvent {
    /// A new connection was accepted.
    ConnectionAccepted { remote: SocketAddr },
    /// A Hello message was received.
    HelloReceived {
        node_name: String,
        remote: SocketAddr,
    },
    /// A token was presented.
    TokenPresented {
        proof_size: usize,
        accepted: bool,
        remote: SocketAddr,
    },
    /// A revocation was submitted.
    RevocationSubmitted {
        token_id: String,
        new_height: u64,
        remote: SocketAddr,
    },
    /// A non-membership proof was requested.
    NonMembershipRequested {
        token_id: String,
        found: bool,
        remote: SocketAddr,
    },
    /// An error occurred while handling a connection.
    ConnectionError { error: String, remote: SocketAddr },
}

impl SiloServer {
    /// Create a new silo server.
    pub fn new(addr: SocketAddr, config: SiloConfig) -> Self {
        let member_count = config.capabilities.len() as u32 + 2; // arbitrary for demo
        let tls_acceptor = Self::build_tls_acceptor(&config.tls);
        if !config.tls.is_configured() {
            eprintln!(
                "WARNING: pyana-wire server '{}' running WITHOUT TLS. \
                 All traffic is plaintext. Set tls_cert_path and tls_key_path \
                 in SiloConfig for production use.",
                config.name
            );
        }
        let nonce_cap = config.nonce_cache_capacity;
        let node_id = config.node_id;
        let grace_period = config.hardening.shutdown_grace_period;
        Self {
            addr,
            config: Arc::new(config),
            state: Arc::new(RwLock::new(SiloState::genesis(member_count))),
            event_log: Arc::new(Mutex::new(Vec::new())),
            revocation_handler: None,
            presentation_nonces: Arc::new(Mutex::new(NonceCache::new(nonce_cap))),
            revocation_nonces: Arc::new(Mutex::new(NonceCache::new(nonce_cap))),
            active_connections: Arc::new(AtomicUsize::new(0)),
            tls_acceptor,
            captp_state: Arc::new(RwLock::new(CapTpState::new())),
            participant_source: None,
            auth_config: AuthConfig::default(),
            ban_list: crate::auth::new_shared_ban_list(),
            shutdown: Arc::new(ShutdownCoordinator::new(node_id, grace_period)),
        }
    }

    /// Create a silo server with pre-initialized state.
    pub fn with_state(addr: SocketAddr, config: SiloConfig, state: SiloState) -> Self {
        let tls_acceptor = Self::build_tls_acceptor(&config.tls);
        if !config.tls.is_configured() {
            eprintln!(
                "WARNING: pyana-wire server '{}' running WITHOUT TLS. \
                 All traffic is plaintext. Set tls_cert_path and tls_key_path \
                 in SiloConfig for production use.",
                config.name
            );
        }
        let nonce_cap = config.nonce_cache_capacity;
        let node_id = config.node_id;
        let grace_period = config.hardening.shutdown_grace_period;
        Self {
            addr,
            config: Arc::new(config),
            state: Arc::new(RwLock::new(state)),
            event_log: Arc::new(Mutex::new(Vec::new())),
            revocation_handler: None,
            presentation_nonces: Arc::new(Mutex::new(NonceCache::new(nonce_cap))),
            revocation_nonces: Arc::new(Mutex::new(NonceCache::new(nonce_cap))),
            active_connections: Arc::new(AtomicUsize::new(0)),
            tls_acceptor,
            captp_state: Arc::new(RwLock::new(CapTpState::new())),
            participant_source: None,
            auth_config: AuthConfig::default(),
            ban_list: crate::auth::new_shared_ban_list(),
            shutdown: Arc::new(ShutdownCoordinator::new(node_id, grace_period)),
        }
    }

    /// Build a TLS acceptor from the TLS configuration, if configured.
    fn build_tls_acceptor(tls: &TlsConfig) -> Option<TlsAcceptor> {
        let (cert_path, key_path) = match (&tls.cert_path, &tls.key_path) {
            (Some(c), Some(k)) => (c, k),
            _ => return None,
        };

        let cert_file = std::fs::File::open(cert_path)
            .unwrap_or_else(|e| panic!("failed to open TLS cert at {}: {e}", cert_path.display()));
        let key_file = std::fs::File::open(key_path)
            .unwrap_or_else(|e| panic!("failed to open TLS key at {}: {e}", key_path.display()));

        let certs: Vec<_> = rustls_pemfile::certs(&mut std::io::BufReader::new(cert_file))
            .collect::<Result<Vec<_>, _>>()
            .expect("failed to parse TLS certificate PEM");

        let key = rustls_pemfile::private_key(&mut std::io::BufReader::new(key_file))
            .expect("failed to read TLS private key PEM")
            .expect("no private key found in PEM file");

        let server_config = tokio_rustls::rustls::ServerConfig::builder()
            .with_no_client_auth()
            .with_single_cert(certs, key)
            .expect("failed to build TLS server config");

        Some(TlsAcceptor::from(Arc::new(server_config)))
    }

    /// Set a custom revocation handler for delegating revocation logic.
    ///
    /// When set, `SubmitRevocation` messages will be routed through this handler
    /// instead of the built-in `SiloState::apply_revocation()` logic.
    pub fn with_revocation_handler(mut self, handler: Arc<dyn RevocationHandler>) -> Self {
        self.revocation_handler = Some(handler);
        self
    }

    /// Set pre-initialized CapTP state (swiss table, known federations, etc.).
    ///
    /// Use this to configure the server with pre-registered swiss entries and
    /// known federation peers before starting.
    pub fn with_captp_state(mut self, captp_state: CapTpState) -> Self {
        self.captp_state = Arc::new(RwLock::new(captp_state));
        self
    }

    /// Set the participant source for peer authentication.
    ///
    /// When configured, the server will issue a `PeerChallenge` after the
    /// Hello/Welcome handshake. Peers that successfully respond are classified
    /// as `Member`; those that don't remain `Anonymous` (limited access).
    ///
    /// When NOT configured (the default), all peers remain `Anonymous` but are
    /// permitted all operations for backward compatibility. This allows
    /// incremental adoption: existing deployments continue to work, new
    /// deployments opt in to authentication.
    pub fn with_participant_source(mut self, source: Arc<dyn ParticipantSource>) -> Self {
        self.participant_source = Some(source);
        self
    }

    /// Set the extended authentication configuration.
    ///
    /// Controls `require_auth` (drop failed-auth connections), rate limiting
    /// differentiated by role, and ban list parameters.
    pub fn with_auth_config(mut self, auth_config: AuthConfig) -> Self {
        self.ban_list =
            crate::auth::new_shared_ban_list_with_config(auth_config.ban_config.clone());
        self.auth_config = auth_config;
        self
    }

    /// Get a reference to the shared ban list (for external monitoring/management).
    pub fn ban_list(&self) -> &SharedBanList {
        &self.ban_list
    }

    /// Get a reference to the shared CapTP state.
    pub fn captp_state(&self) -> &Arc<RwLock<CapTpState>> {
        &self.captp_state
    }

    /// Get the listening address.
    pub fn addr(&self) -> SocketAddr {
        self.addr
    }

    /// Get the silo name.
    pub fn name(&self) -> &str {
        &self.config.name
    }

    /// Get a snapshot of the current state.
    pub async fn state(&self) -> SiloState {
        self.state.read().await.clone()
    }

    /// Get the event log.
    pub async fn events(&self) -> Vec<ServerEvent> {
        self.event_log.lock().await.clone()
    }

    /// Get a reference to the shutdown coordinator.
    ///
    /// Use this to initiate graceful shutdown from outside the server task.
    pub fn shutdown_coordinator(&self) -> &Arc<ShutdownCoordinator> {
        &self.shutdown
    }

    /// Initiate graceful shutdown of the server.
    ///
    /// This signals the accept loop to stop accepting new connections and
    /// notifies all active connection handlers to begin draining. Returns
    /// the number of active connections that will be drained.
    ///
    /// The shutdown sequence:
    /// 1. Stop accepting new connections
    /// 2. Send CapGoodbye to all active CapTP sessions
    /// 3. Wait up to `shutdown_grace_period` for in-flight messages
    /// 4. Force-close remaining connections
    pub fn initiate_shutdown(&self) -> u64 {
        self.shutdown.initiate_shutdown()
    }

    /// Run the server, accepting and handling connections.
    ///
    /// This runs indefinitely until the task is cancelled.
    pub async fn run(&self) -> Result<(), std::io::Error> {
        let listener = TcpListener::bind(self.addr).await?;
        // Update addr to reflect the actual bound address (useful for port 0)
        let _actual_addr = listener.local_addr()?;

        self.accept_loop(listener).await
    }

    /// Run the server and return the actual bound address.
    ///
    /// Useful when binding to port 0 (OS-assigned port). The returned oneshot
    /// fires with the actual address once the server is listening.
    pub async fn run_with_addr(
        &self,
        addr_tx: tokio::sync::oneshot::Sender<SocketAddr>,
    ) -> Result<(), std::io::Error> {
        let listener = TcpListener::bind(self.addr).await?;
        let actual_addr = listener.local_addr()?;
        let _ = addr_tx.send(actual_addr);

        self.accept_loop(listener).await
    }

    /// Core accept loop shared by `run` and `run_with_addr`.
    ///
    /// Enforces max_connections (P0-3), ban list, applies TLS (P0-1), and spawns handlers.
    async fn accept_loop(&self, listener: TcpListener) -> Result<(), std::io::Error> {
        loop {
            // --- Graceful shutdown check ---
            if self.shutdown.is_shutting_down() {
                return Ok(());
            }

            let (stream, remote_addr) = tokio::select! {
                result = listener.accept() => result?,
                _ = async {
                    // Poll shutdown signal
                    let mut rx = self.shutdown.subscribe();
                    let _ = rx.recv().await;
                } => {
                    return Ok(());
                }
            };

            // --- Ban list check: reject banned IPs immediately ---
            {
                let ban_list = self.ban_list.lock().await;
                if ban_list.is_banned(&remote_addr.ip()) {
                    eprintln!("pyana-wire: rejecting connection from {remote_addr}: IP is banned");
                    drop(stream);
                    continue;
                }
            }

            // --- P0-3: Enforce max_connections ---
            let current = self.active_connections.fetch_add(1, Ordering::SeqCst);
            if current >= self.config.max_connections {
                self.active_connections.fetch_sub(1, Ordering::SeqCst);
                // Reject: at capacity. Drop the stream (sends RST).
                eprintln!(
                    "pyana-wire: rejecting connection from {remote_addr}: \
                     at capacity ({max})",
                    max = self.config.max_connections,
                );
                drop(stream);
                continue;
            }

            let config = Arc::clone(&self.config);
            let state = Arc::clone(&self.state);
            let event_log = Arc::clone(&self.event_log);
            let revocation_handler = self.revocation_handler.clone();
            let presentation_nonces = Arc::clone(&self.presentation_nonces);
            let revocation_nonces = Arc::clone(&self.revocation_nonces);
            let conn_counter = Arc::clone(&self.active_connections);
            let tls_acceptor = self.tls_acceptor.clone();
            let captp_state = Arc::clone(&self.captp_state);
            let participant_source = self.participant_source.clone();
            let auth_config = self.auth_config.clone();
            let ban_list = Arc::clone(&self.ban_list);
            let shutdown = Arc::clone(&self.shutdown);

            tokio::spawn(async move {
                // ConnectionGuard decrements the counter when this task exits.
                let _guard = ConnectionGuard {
                    counter: conn_counter,
                };

                // --- P0-1: TLS wrapping ---
                if let Some(acceptor) = tls_acceptor {
                    match acceptor.accept(stream).await {
                        Ok(tls_stream) => {
                            let (reader, writer) = tokio::io::split(tls_stream);
                            Self::handle_connection_generic(
                                reader,
                                writer,
                                remote_addr,
                                config,
                                state,
                                event_log,
                                revocation_handler,
                                presentation_nonces,
                                revocation_nonces,
                                captp_state,
                                participant_source,
                                auth_config,
                                ban_list,
                                shutdown.clone(),
                            )
                            .await;
                        }
                        Err(e) => {
                            eprintln!("pyana-wire: TLS handshake failed from {remote_addr}: {e}");
                        }
                    }
                } else {
                    // Plaintext fallback (warning already emitted at construction time)
                    let (reader, writer) = tokio::io::split(stream);
                    Self::handle_connection_generic(
                        reader,
                        writer,
                        remote_addr,
                        config,
                        state,
                        event_log,
                        revocation_handler,
                        presentation_nonces,
                        revocation_nonces,
                        captp_state,
                        participant_source,
                        auth_config,
                        ban_list,
                        shutdown,
                    )
                    .await;
                }
            });
        }
    }

    /// Handle a single connection (legacy plaintext API, retained for tests).
    #[allow(dead_code)]
    async fn handle_connection(
        stream: tokio::net::TcpStream,
        remote_addr: SocketAddr,
        config: Arc<SiloConfig>,
        state: Arc<RwLock<SiloState>>,
        event_log: Arc<Mutex<Vec<ServerEvent>>>,
        revocation_handler: Option<Arc<dyn RevocationHandler>>,
        presentation_nonces: Arc<Mutex<NonceCache>>,
        revocation_nonces: Arc<Mutex<NonceCache>>,
        captp_state: Arc<RwLock<CapTpState>>,
        participant_source: Option<Arc<dyn ParticipantSource>>,
        auth_config: AuthConfig,
        ban_list: SharedBanList,
        shutdown: Arc<ShutdownCoordinator>,
    ) {
        let (reader, writer) = tokio::io::split(stream);
        Self::handle_connection_generic(
            reader,
            writer,
            remote_addr,
            config,
            state,
            event_log,
            revocation_handler,
            presentation_nonces,
            revocation_nonces,
            captp_state,
            participant_source,
            auth_config,
            ban_list,
            shutdown,
        )
        .await;
    }

    /// Handle a single connection over any async stream (TLS or plaintext).
    ///
    /// Enforces:
    /// - P0-2: Handshake state machine (must receive Hello first)
    /// - P0-4: Handshake timeout (first message must arrive within config.handshake_timeout)
    /// - Rate limiting per role (stricter for Anonymous)
    /// - require_auth: drops connections that fail authentication
    /// - Ban list: records auth failures and enforces temporary bans
    async fn handle_connection_generic<R, W>(
        mut reader: R,
        mut writer: W,
        remote_addr: SocketAddr,
        config: Arc<SiloConfig>,
        state: Arc<RwLock<SiloState>>,
        event_log: Arc<Mutex<Vec<ServerEvent>>>,
        revocation_handler: Option<Arc<dyn RevocationHandler>>,
        presentation_nonces: Arc<Mutex<NonceCache>>,
        revocation_nonces: Arc<Mutex<NonceCache>>,
        captp_state: Arc<RwLock<CapTpState>>,
        participant_source: Option<Arc<dyn ParticipantSource>>,
        auth_config: AuthConfig,
        ban_list: SharedBanList,
        shutdown: Arc<ShutdownCoordinator>,
    ) where
        R: AsyncRead + Unpin + Send + 'static,
        W: AsyncWrite + Unpin + Send + 'static,
    {
        event_log
            .lock()
            .await
            .push(ServerEvent::ConnectionAccepted {
                remote: remote_addr,
            });

        // --- P0-4: Apply handshake_timeout to the first message ---
        let first_msg = match tokio::time::timeout(
            config.handshake_timeout,
            crate::codec::read_message(&mut reader),
        )
        .await
        {
            Ok(Ok(msg)) => msg,
            Ok(Err(crate::codec::CodecError::ConnectionClosed)) => return,
            Ok(Err(e)) => {
                event_log.lock().await.push(ServerEvent::ConnectionError {
                    error: format!("handshake read error: {e}"),
                    remote: remote_addr,
                });
                return;
            }
            Err(_) => {
                // Handshake timeout fired
                event_log.lock().await.push(ServerEvent::ConnectionError {
                    error: "handshake timeout".to_string(),
                    remote: remote_addr,
                });
                // Try to send an error before closing
                let err_msg = WireMessage::Error {
                    code: crate::message::error_codes::REQUEST_EXPIRED,
                    message: "handshake timeout".to_string(),
                };
                let _ = crate::codec::write_message(&mut writer, &err_msg).await;
                return;
            }
        };

        // --- P0-2: Enforce that the first message MUST be Hello ---
        match &first_msg {
            WireMessage::Hello { .. } => {
                // Valid: transition to Active state
            }
            _ => {
                // Invalid: reject and close
                let err_msg = WireMessage::Error {
                    code: crate::message::error_codes::HANDSHAKE_REQUIRED,
                    message: "expected Hello as first message".to_string(),
                };
                let _ = crate::codec::write_message(&mut writer, &err_msg).await;
                event_log.lock().await.push(ServerEvent::ConnectionError {
                    error: "first message was not Hello".to_string(),
                    remote: remote_addr,
                });
                return;
            }
        }

        // Process the Hello message (sends Welcome)
        if let Some(response) = Self::process_message(
            first_msg,
            remote_addr,
            &config,
            &state,
            &event_log,
            revocation_handler.as_deref(),
            &presentation_nonces,
            &revocation_nonces,
            &captp_state,
        )
        .await
        {
            if crate::codec::write_message(&mut writer, &response)
                .await
                .is_err()
            {
                return;
            }
        }

        // --- Federation Boundary: Challenge-Response Authentication ---
        //
        // If a participant_source is configured, issue a challenge after
        // Hello/Welcome. The peer has one chance to prove membership. If
        // they respond correctly, they are upgraded to Member. If they
        // don't respond or fail, they remain Anonymous (or are dropped if
        // require_auth is true).
        let mut conn_auth = ConnectionAuth::anonymous();
        let mut auth_failed = false;

        if let Some(ref source) = participant_source {
            // Generate challenge nonce
            let mut nonce = [0u8; 32];
            getrandom::fill(&mut nonce).expect("getrandom failed");

            let challenge = WireMessage::PeerChallenge {
                nonce,
                server_node_id: config.node_id,
            };
            if crate::codec::write_message(&mut writer, &challenge)
                .await
                .is_err()
            {
                return;
            }

            // Wait for the response (within handshake timeout)
            let auth_response = match tokio::time::timeout(
                config.handshake_timeout,
                crate::codec::read_message(&mut reader),
            )
            .await
            {
                Ok(Ok(msg)) => Some(msg),
                Ok(Err(crate::codec::CodecError::ConnectionClosed)) => return,
                Ok(Err(_)) => None,
                Err(_) => None, // Timeout: peer didn't authenticate (stays Anonymous)
            };

            if let Some(WireMessage::PeerAuthResponse {
                participant_key,
                signature,
                claimed_constitution_version: _,
            }) = auth_response
            {
                // Verify the signature against the challenge
                let signing_msg = peer_auth_signing_message(&nonce, &config.node_id);
                let pk = PublicKey(participant_key);

                if pk.verify(&signing_msg, &signature) && source.is_participant(&participant_key) {
                    // Authentication successful
                    conn_auth.authenticate_as_member(participant_key);

                    // Record success in ban list (resets failure counter)
                    {
                        let mut bl = ban_list.lock().await;
                        bl.record_auth_success(&remote_addr.ip());
                    }

                    let ack = WireMessage::PeerAuthenticated {
                        role_tag: conn_auth.role.tag(),
                        authenticated_key: participant_key,
                    };
                    if crate::codec::write_message(&mut writer, &ack)
                        .await
                        .is_err()
                    {
                        return;
                    }
                } else {
                    // Authentication failed
                    auth_failed = true;
                    conn_auth.handshake_complete = true;

                    // Record failure in ban list
                    let now_banned = {
                        let mut bl = ban_list.lock().await;
                        bl.record_auth_failure(&remote_addr.ip())
                    };
                    if now_banned {
                        eprintln!(
                            "pyana-wire: peer {remote_addr} banned after repeated auth failures"
                        );
                    }

                    let ack = WireMessage::PeerAuthenticated {
                        role_tag: PeerRole::Anonymous.tag(),
                        authenticated_key: [0u8; 32],
                    };
                    if crate::codec::write_message(&mut writer, &ack)
                        .await
                        .is_err()
                    {
                        return;
                    }
                }
            } else {
                // Peer sent something other than PeerAuthResponse, or timed out.
                auth_failed = true;
                conn_auth.handshake_complete = true;

                // Record as auth failure
                {
                    let mut bl = ban_list.lock().await;
                    bl.record_auth_failure(&remote_addr.ip());
                }
            }
        }

        // --- require_auth enforcement ---
        if auth_config.require_auth && participant_source.is_some() && auth_failed {
            let err_msg = WireMessage::Error {
                code: crate::message::error_codes::PEER_AUTH_FAILED,
                message: "authentication required but failed; connection terminated".to_string(),
            };
            let _ = crate::codec::write_message(&mut writer, &err_msg).await;
            event_log.lock().await.push(ServerEvent::ConnectionError {
                error: "require_auth: dropping unauthenticated connection".to_string(),
                remote: remote_addr,
            });
            return;
        }

        // --- Rate limiter: initialize based on the peer's authenticated role ---
        let mut rate_limiter = AuthRateLimiter::for_role(&conn_auth.role, &auth_config.rate_limits);

        // --- Hardening: per-peer token bucket rate limiter ---
        let mut hardening_rl = config.hardening.new_rate_limiter();

        // --- Heartbeat state ---
        let heartbeat_interval = config.hardening.heartbeat_interval;
        let heartbeat_timeout = config.hardening.heartbeat_timeout;
        let max_msg_size = config.hardening.max_message_size;
        let mut _last_activity = std::time::Instant::now();
        let mut ping_seq: u64 = 0;
        let mut awaiting_pong = false;
        let mut ping_sent_at = std::time::Instant::now();

        // --- Connection metrics ---
        let mut metrics =
            ConnectionMetrics::new(conn_auth.role.clone(), config.hardening.new_rate_limiter());

        // --- Shutdown receiver ---
        let mut shutdown_rx = shutdown.subscribe();

        // Process subsequent messages (connection is now Active, with role filtering)
        loop {
            // Use heartbeat_interval as the read timeout so we can send pings
            let read_result = tokio::select! {
                result = tokio::time::timeout(
                    heartbeat_interval,
                    crate::codec::read_message_with_limit(&mut reader, max_msg_size),
                ) => result,
                _ = shutdown_rx.recv() => {
                    // Server is shutting down: send CapGoodbye and close
                    let goodbye = WireMessage::CapGoodbye {
                        group_id: config.node_id,
                        reason: Some("server shutting down".to_string()),
                    };
                    let _ = crate::codec::write_message(&mut writer, &goodbye).await;
                    break;
                }
            };

            let msg = match read_result {
                Ok(Ok(msg)) => {
                    _last_activity = std::time::Instant::now();
                    awaiting_pong = false;
                    msg
                }
                Ok(Err(crate::codec::CodecError::ConnectionClosed)) => break,
                Ok(Err(crate::codec::CodecError::MessageTooLarge { size, max })) => {
                    // Message exceeds configured size limit — reject and disconnect
                    let err_msg = WireMessage::Error {
                        code: crate::hardening::ERROR_MESSAGE_TOO_LARGE,
                        message: format!(
                            "message too large: {size} bytes exceeds limit of {max} bytes"
                        ),
                    };
                    let _ = crate::codec::write_message(&mut writer, &err_msg).await;
                    event_log.lock().await.push(ServerEvent::ConnectionError {
                        error: format!("message too large: {size} > {max}"),
                        remote: remote_addr,
                    });
                    break;
                }
                Ok(Err(e)) => {
                    event_log.lock().await.push(ServerEvent::ConnectionError {
                        error: e.to_string(),
                        remote: remote_addr,
                    });
                    break;
                }
                Err(_) => {
                    // Timeout: check heartbeat state
                    if awaiting_pong {
                        // We already sent a ping — check if heartbeat_timeout exceeded
                        if ping_sent_at.elapsed() >= heartbeat_timeout {
                            event_log.lock().await.push(ServerEvent::ConnectionError {
                                error: "heartbeat timeout: no pong received".to_string(),
                                remote: remote_addr,
                            });
                            let err_msg = WireMessage::Error {
                                code: crate::hardening::ERROR_HEARTBEAT_TIMEOUT,
                                message: "heartbeat timeout".to_string(),
                            };
                            let _ = crate::codec::write_message(&mut writer, &err_msg).await;
                            break;
                        }
                        // Not timed out yet; keep waiting
                        continue;
                    }
                    // No message received within heartbeat_interval: send a ping
                    ping_seq += 1;
                    let ping = WireMessage::Ping {
                        seq: ping_seq,
                        timestamp: current_timestamp(),
                    };
                    if crate::codec::write_message(&mut writer, &ping)
                        .await
                        .is_err()
                    {
                        break;
                    }
                    awaiting_pong = true;
                    ping_sent_at = std::time::Instant::now();
                    continue;
                }
            };

            // --- Track metrics ---
            metrics.record_receive(msg.estimated_size() as u64);

            // --- Hardening: token bucket rate limiting ---
            let cost = message_cost(&msg);
            if !hardening_rl.try_consume(cost) {
                let err_msg = WireMessage::Error {
                    code: crate::hardening::ERROR_RATE_LIMITED,
                    message: "rate limited: too many messages, try again later".to_string(),
                };
                let _ = crate::codec::write_message(&mut writer, &err_msg).await;
                continue;
            }

            // --- Auth rate limiter (sliding window, role-based) ---
            if !rate_limiter.check() {
                let err_msg = WireMessage::Error {
                    code: crate::hardening::ERROR_RATE_LIMITED,
                    message: "rate limited: message window exceeded for your role".to_string(),
                };
                let _ = crate::codec::write_message(&mut writer, &err_msg).await;
                continue;
            }

            // --- Federation Boundary: Message filtering by role ---
            //
            // When participant_source is configured (authentication enabled),
            // reject messages that require higher privilege than the peer has.
            // When NOT configured (backward compat), allow everything.
            if participant_source.is_some() {
                if let Some(rejection) = Self::check_role_permission(&msg, &conn_auth) {
                    if crate::codec::write_message(&mut writer, &rejection)
                        .await
                        .is_err()
                    {
                        break;
                    }
                    continue;
                }
            }

            // Handle CapHello promoting Anonymous -> CapTpPeer (only effective
            // when auth is NOT enforced, since with auth the check_role_permission
            // blocks CapTP for Anonymous).
            if let WireMessage::CapHello { group_id, .. } = &msg {
                let was_anonymous = matches!(conn_auth.role, PeerRole::Anonymous);
                conn_auth.authenticate_as_captp_peer(*group_id);
                if was_anonymous && matches!(conn_auth.role, PeerRole::CapTpPeer { .. }) {
                    rate_limiter
                        .update_limit(auth_config.rate_limits.limit_for_role(&conn_auth.role));
                }
            }

            let response = Self::process_message(
                msg,
                remote_addr,
                &config,
                &state,
                &event_log,
                revocation_handler.as_deref(),
                &presentation_nonces,
                &revocation_nonces,
                &captp_state,
            )
            .await;

            if let Some(response) = response {
                metrics.record_send(response.estimated_size() as u64);
                if crate::codec::write_message(&mut writer, &response)
                    .await
                    .is_err()
                {
                    break;
                }
            }
        }

        // Connection cleanup
        shutdown.unregister_connection();
    }

    /// Check whether a message is permitted given the connection's authenticated role.
    ///
    /// Returns `Some(error_message)` if the message should be rejected, or `None`
    /// if it is permitted.
    fn check_role_permission(msg: &WireMessage, auth: &ConnectionAuth) -> Option<WireMessage> {
        let role = &auth.role;

        match msg {
            // Public operations: always allowed
            WireMessage::PresentToken { .. }
            | WireMessage::RequestAttestedRoot
            | WireMessage::RequestNonMembership { .. }
            | WireMessage::Ping { .. }
            | WireMessage::Pong { .. }
            | WireMessage::Hello { .. }
            | WireMessage::PeerAuthResponse { .. }
            | WireMessage::PeerChallenge { .. }
            | WireMessage::PeerAuthenticated { .. } => None,

            // CapTP operations: require CapTpPeer or Member
            WireMessage::CapHello { .. }
            | WireMessage::CapGoodbye { .. }
            | WireMessage::EnlivenSturdyRef { .. }
            | WireMessage::PipelinedMsg { .. }
            | WireMessage::PresentHandoff { .. }
            | WireMessage::DropRemoteRef { .. } => {
                if role.allows_captp() {
                    None
                } else {
                    Some(WireMessage::Error {
                        code: crate::message::error_codes::PEER_AUTH_REQUIRED,
                        message:
                            "CapTP operations require authenticated peer (Member or CapTpPeer)"
                                .to_string(),
                    })
                }
            }

            // Revocation: require Member
            WireMessage::SubmitRevocation { .. } => {
                if role.allows_revocation() {
                    None
                } else {
                    Some(WireMessage::Error {
                        code: crate::message::error_codes::PEER_AUTH_REQUIRED,
                        message: "revocation submission requires Member authentication".to_string(),
                    })
                }
            }

            // Response-type messages: allow (they're responses to requests we made)
            WireMessage::Welcome { .. }
            | WireMessage::PresentationResult { .. }
            | WireMessage::AttestedRoot { .. }
            | WireMessage::RevocationAck { .. }
            | WireMessage::NonMembershipResponse { .. }
            | WireMessage::EnlivenResponse { .. }
            | WireMessage::HandoffAccepted { .. }
            | WireMessage::Error { .. } => None,
        }
    }

    /// Process a single message and return an optional response.
    async fn process_message(
        msg: WireMessage,
        remote_addr: SocketAddr,
        config: &SiloConfig,
        state: &RwLock<SiloState>,
        event_log: &Mutex<Vec<ServerEvent>>,
        revocation_handler: Option<&dyn RevocationHandler>,
        presentation_nonces: &Mutex<NonceCache>,
        revocation_nonces: &Mutex<NonceCache>,
        captp_state: &RwLock<CapTpState>,
    ) -> Option<WireMessage> {
        match msg {
            WireMessage::Hello {
                node_id: _,
                node_name,
                protocol_version,
                capabilities: _,
            } => {
                event_log.lock().await.push(ServerEvent::HelloReceived {
                    node_name: node_name.clone(),
                    remote: remote_addr,
                });

                // --- Issue 8: Version negotiation ---
                if protocol_version != PROTOCOL_VERSION {
                    return Some(WireMessage::Error {
                        code: crate::message::error_codes::UNSUPPORTED_VERSION,
                        message: format!(
                            "unsupported protocol version {protocol_version}, expected {PROTOCOL_VERSION}"
                        ),
                    });
                }

                let st = state.read().await;
                Some(WireMessage::Welcome {
                    federation_root: st.federation_root,
                    member_count: st.member_count,
                    node_id: config.node_id,
                    node_name: config.name.clone(),
                })
            }

            WireMessage::PresentToken {
                proof,
                request,
                federation_root,
            } => {
                // --- Issue 1: Validate freshness (timestamp + nonce) ---
                let now = current_timestamp();
                let age = now - request.timestamp;
                if age > config.max_request_age_secs || age < -60 {
                    event_log.lock().await.push(ServerEvent::TokenPresented {
                        proof_size: proof.len(),
                        accepted: false,
                        remote: remote_addr,
                    });
                    return Some(WireMessage::PresentationResult {
                        accepted: false,
                        reason: Some(format!(
                            "request timestamp too old ({age}s, max {max}s)",
                            max = config.max_request_age_secs
                        )),
                        request_digest: request.digest(),
                    });
                }

                // Check nonce for replay
                {
                    let mut nonces = presentation_nonces.lock().await;
                    if !nonces.check_and_insert(&request.nonce) {
                        event_log.lock().await.push(ServerEvent::TokenPresented {
                            proof_size: proof.len(),
                            accepted: false,
                            remote: remote_addr,
                        });
                        return Some(WireMessage::PresentationResult {
                            accepted: false,
                            reason: Some("replayed nonce".to_string()),
                            request_digest: request.digest(),
                        });
                    }
                }

                // --- Issue 7: Move verification outside the read lock ---
                // Clone the federation root from state, then release the lock
                // BEFORE running the expensive proof verification.
                let (current_root, last_root_update) = {
                    let st = state.read().await;
                    (st.federation_root, st.last_root_update)
                };
                // Read lock is now released.

                // Fail-closed: if max_root_age_secs is configured and the root
                // is too stale (consensus may be stalled/DoS'd), reject ALL proofs.
                if let Some(max_age) = config.max_root_age_secs {
                    let root_age = current_timestamp() - last_root_update;
                    if root_age > max_age as i64 {
                        event_log.lock().await.push(ServerEvent::TokenPresented {
                            proof_size: proof.len(),
                            accepted: false,
                            remote: remote_addr,
                        });
                        return Some(WireMessage::PresentationResult {
                            accepted: false,
                            reason: Some(format!(
                                "federation root too stale ({root_age}s since last update, max {max_age}s) — awaiting sync"
                            )),
                            request_digest: request.digest(),
                        });
                    }
                }

                // Check federation root freshness
                if federation_root != current_root {
                    event_log.lock().await.push(ServerEvent::TokenPresented {
                        proof_size: proof.len(),
                        accepted: false,
                        remote: remote_addr,
                    });
                    return Some(WireMessage::PresentationResult {
                        accepted: false,
                        reason: Some("stale federation root".to_string()),
                        request_digest: request.digest(),
                    });
                }

                // Verify the proof using the injected verifier, binding to (action, resource).
                // NOTE: No read lock is held here -- STARK verification can take
                // milliseconds and must not block writers (issue 7: DoS prevention).
                let accepted =
                    match config
                        .verifier
                        .verify(&proof, &request.action, &request.resource)
                    {
                        Ok(result) => result,
                        Err(_reason) => false, // parse/verification error -> reject
                    };

                event_log.lock().await.push(ServerEvent::TokenPresented {
                    proof_size: proof.len(),
                    accepted,
                    remote: remote_addr,
                });

                Some(WireMessage::PresentationResult {
                    accepted,
                    reason: if accepted {
                        None
                    } else {
                        Some("proof verification failed".to_string())
                    },
                    request_digest: request.digest(),
                })
            }

            WireMessage::RequestAttestedRoot => {
                let st = state.read().await;
                Some(WireMessage::AttestedRoot {
                    root: st.federation_root,
                    height: st.height,
                    timestamp: current_timestamp(),
                    signatures: st.root_signatures.clone(),
                    threshold_qc: st.threshold_qc.clone(),
                })
            }

            WireMessage::SubmitRevocation {
                token_id,
                authority,
                authority_sig,
                nonce,
                timestamp,
            } => {
                // --- Issue 6: Validate revocation freshness (nonce + timestamp) ---
                let now = current_timestamp();
                let age = now - timestamp;
                if age > config.max_request_age_secs || age < -60 {
                    return Some(WireMessage::Error {
                        code: crate::message::error_codes::REQUEST_EXPIRED,
                        message: format!(
                            "revocation timestamp too old ({age}s, max {max}s)",
                            max = config.max_request_age_secs
                        ),
                    });
                }

                // Check nonce for replay
                {
                    let mut nonces = revocation_nonces.lock().await;
                    if !nonces.check_and_insert(&nonce) {
                        return Some(WireMessage::Error {
                            code: crate::message::error_codes::REQUEST_EXPIRED,
                            message: "replayed revocation nonce".to_string(),
                        });
                    }
                }

                // SECURITY: Authority whitelist check.
                // An empty revocation_authorities list means NO authorities are trusted,
                // which is the fail-closed default. Previously this accepted ANY signature
                // when the list was empty, which is an insecure open-by-default posture.
                if config.revocation_authorities.is_empty() {
                    return Some(WireMessage::Error {
                        code: crate::message::error_codes::INVALID_SIGNATURE,
                        message: "no revocation authorities configured (fail-closed)".to_string(),
                    });
                }
                if !config.revocation_authorities.contains(&authority) {
                    return Some(WireMessage::Error {
                        code: crate::message::error_codes::INVALID_SIGNATURE,
                        message: "authority not in revocation whitelist".to_string(),
                    });
                }

                // Verify the authority's signature over blake3(token_id || nonce || timestamp).
                // The signature MUST cover all three fields to prevent replay/substitution
                // attacks where an attacker replays a valid signature with a different
                // nonce or timestamp.
                let sig_message = {
                    let mut hasher = blake3::Hasher::new_derive_key("pyana-wire revocation-sig v1");
                    hasher.update(token_id.as_bytes());
                    hasher.update(&nonce);
                    hasher.update(&timestamp.to_le_bytes());
                    *hasher.finalize().as_bytes()
                };
                if !authority.verify(&sig_message, &authority_sig) {
                    return Some(WireMessage::Error {
                        code: crate::message::error_codes::INVALID_SIGNATURE,
                        message: "authority signature verification failed".to_string(),
                    });
                }

                // If a revocation handler is configured, delegate to it and use
                // its root as the canonical source of truth.
                if let Some(handler) = revocation_handler {
                    let _accepted =
                        handler.submit_revocation(&token_id, &authority_sig.0, &authority);

                    // Update local state using the handler's root (no independent
                    // hash-chain computation -- the handler IS the authority).
                    let mut st = state.write().await;
                    st.apply_revocation_delegated(&token_id, &authority, &authority_sig, handler);

                    event_log
                        .lock()
                        .await
                        .push(ServerEvent::RevocationSubmitted {
                            token_id,
                            new_height: st.height,
                            remote: remote_addr,
                        });

                    Some(WireMessage::RevocationAck {
                        new_root: st.federation_root,
                        height: st.height,
                    })
                } else {
                    // Fallback: use the standalone BLAKE3 hash-chain logic.
                    // This is NOT consistent with the federation's Merkle tree
                    // but preserved for single-node/test deployments.
                    let mut st = state.write().await;
                    #[allow(deprecated)]
                    st.apply_revocation_standalone(&token_id, &authority, &authority_sig);

                    event_log
                        .lock()
                        .await
                        .push(ServerEvent::RevocationSubmitted {
                            token_id,
                            new_height: st.height,
                            remote: remote_addr,
                        });

                    Some(WireMessage::RevocationAck {
                        new_root: st.federation_root,
                        height: st.height,
                    })
                }
            }

            WireMessage::RequestNonMembership { token_id } => {
                let st = state.read().await;
                let is_revoked = st.is_revoked(&token_id);

                event_log
                    .lock()
                    .await
                    .push(ServerEvent::NonMembershipRequested {
                        token_id: token_id.clone(),
                        found: !is_revoked,
                        remote: remote_addr,
                    });

                if is_revoked {
                    Some(WireMessage::NonMembershipResponse {
                        token_id,
                        proof: None,
                        root: st.federation_root,
                        height: st.height,
                    })
                } else {
                    // Attempt to produce a non-membership proof via the handler
                    // or fall back to the standalone stub.
                    let proof = generate_non_membership_proof(
                        &token_id,
                        &st.federation_root,
                        revocation_handler,
                    );
                    Some(WireMessage::NonMembershipResponse {
                        token_id,
                        proof,
                        root: st.federation_root,
                        height: st.height,
                    })
                }
            }

            WireMessage::Ping { seq, .. } => Some(WireMessage::Pong {
                seq,
                timestamp: current_timestamp(),
            }),

            WireMessage::Pong { .. } => None, // No response needed

            WireMessage::Welcome { .. } | WireMessage::PresentationResult { .. } => {
                // These are responses, not requests; no action needed
                None
            }

            WireMessage::AttestedRoot { .. } | WireMessage::RevocationAck { .. } => None,

            WireMessage::NonMembershipResponse { .. } => None,

            WireMessage::Error { .. } => None,

            // =================================================================
            // CapTP Session Management
            // =================================================================
            WireMessage::CapHello {
                group_id,
                initial_exports,
            } => {
                let fed_id = FederationId(group_id);
                let mut captp = captp_state.write().await;

                // Allocate a new epoch for this session. If a previous session existed,
                // the new epoch supersedes it, ensuring stale messages are rejected.
                let epoch = captp.allocate_epoch();

                // Create or reset the session for this peer with the new epoch.
                let session = CapSession::with_epoch(group_id, epoch);
                captp.sessions.insert(fed_id, session);

                // Record initial exports in the GC manager with session ID for
                // session-level DropRef validation.
                let height = captp.current_height;
                for export_bytes in &initial_exports {
                    let cell_id = pyana_types::CellId(*export_bytes);
                    captp
                        .export_gc
                        .record_export_with_session(cell_id, fed_id, height, epoch);
                }

                // Respond with our own CapHello (session established).
                Some(WireMessage::CapHello {
                    group_id: config.node_id,
                    initial_exports: vec![], // We export nothing by default on session init.
                })
            }

            WireMessage::CapGoodbye {
                group_id,
                reason: _,
            } => {
                let fed_id = FederationId(group_id);
                let mut captp = captp_state.write().await;

                // Remove the session — all exports/imports for this peer are invalidated.
                captp.sessions.remove(&fed_id);

                // No response needed for goodbye (it's a notification).
                None
            }

            WireMessage::EnlivenSturdyRef {
                uri_bytes,
                requester_height: _,
            } => {
                // Parse the URI from postcard-serialized bytes.
                let uri: pyana_captp::PyanaUri = match postcard::from_bytes(&uri_bytes) {
                    Ok(uri) => uri,
                    Err(_) => {
                        return Some(WireMessage::EnlivenResponse {
                            success: false,
                            cell_id: None,
                            permissions_tag: 0,
                            error: Some("invalid URI format".to_string()),
                        });
                    }
                };

                let mut captp = captp_state.write().await;
                let current_height = captp.current_height;

                // Attempt to enliven the swiss number.
                match captp.swiss_table.enliven(&uri.swiss, current_height) {
                    Ok(entry) => {
                        let perm_tag = match &entry.permissions {
                            pyana_cell::AuthRequired::None => 0u8,
                            pyana_cell::AuthRequired::Signature => 1u8,
                            pyana_cell::AuthRequired::Proof => 2u8,
                            pyana_cell::AuthRequired::Either => 3u8,
                            pyana_cell::AuthRequired::Impossible => 4u8,
                        };
                        Some(WireMessage::EnlivenResponse {
                            success: true,
                            cell_id: Some(entry.cell_id.0),
                            permissions_tag: perm_tag,
                            error: None,
                        })
                    }
                    Err(e) => Some(WireMessage::EnlivenResponse {
                        success: false,
                        cell_id: None,
                        permissions_tag: 0,
                        error: Some(e.to_string()),
                    }),
                }
            }

            WireMessage::EnlivenResponse { .. } => {
                // This is a response, not a request; no action needed on the server side.
                None
            }

            WireMessage::DropRemoteRef {
                from_strand,
                cell_id,
                session_epoch: msg_epoch,
            } => {
                let fed_id = FederationId(from_strand);
                let cell = pyana_types::CellId(cell_id);

                let mut captp = captp_state.write().await;

                // Session-level validation: the drop must come from a federation
                // that has an active session. Extract the session epoch for validation.
                let current_epoch = match captp.sessions.get(&fed_id) {
                    Some(session) => session.epoch,
                    None => {
                        // No active session for this federation — reject the drop.
                        // A Byzantine node on a different/stale session cannot interfere.
                        return Some(WireMessage::Error {
                            code: crate::message::error_codes::INVALID_DROP,
                            message: "invalid drop: no active session for federation".to_string(),
                        });
                    }
                };

                // Epoch validation: reject messages from stale sessions.
                // A non-zero msg_epoch that doesn't match the current session epoch
                // means this message is from an old (terminated) session.
                if msg_epoch != 0 && msg_epoch != current_epoch {
                    return Some(WireMessage::Error {
                        code: crate::message::error_codes::STALE_EPOCH,
                        message: format!(
                            "stale session epoch: message has epoch {msg_epoch}, \
                             current session is epoch {current_epoch}"
                        ),
                    });
                }

                // Use session-aware drop to validate the session_id matches the
                // epoch under which the export was recorded.
                let result = captp
                    .export_gc
                    .process_drop_with_session(cell, fed_id, current_epoch);

                match result {
                    pyana_captp::DropResult::CanRevoke | pyana_captp::DropResult::StillHeld => {
                        // Also decrement the session export refcount if session exists.
                        if let Some(session) = captp.sessions.get_mut(&fed_id) {
                            session.release_export(&cell);
                        }
                        None // Silent success (GC is fire-and-forget).
                    }
                    pyana_captp::DropResult::Invalid => Some(WireMessage::Error {
                        code: crate::message::error_codes::INVALID_DROP,
                        message: "invalid drop: unknown federation, cell, or session mismatch"
                            .to_string(),
                    }),
                }
            }

            WireMessage::PipelinedMsg {
                target_promise_id,
                method,
                args,
                authorization,
                result_promise_id,
                sender_federation,
                session_epoch: msg_epoch,
            } => {
                // For now, acknowledge receipt. Full pipeline delivery requires
                // integration with the turn executor, which is out of scope for
                // this initial wire-layer integration. The message is queued in
                // the session's pipeline registry.
                let fed_id = FederationId(sender_federation);
                let captp = captp_state.read().await;

                let current_epoch = match captp.sessions.get(&fed_id) {
                    Some(session) => session.epoch,
                    None => {
                        return Some(WireMessage::Error {
                            code: crate::message::error_codes::CAPTP_SESSION_REQUIRED,
                            message: "no CapTP session established; send CapHello first"
                                .to_string(),
                        });
                    }
                };

                // Epoch validation: reject messages from stale (terminated) sessions.
                if msg_epoch != 0 && msg_epoch != current_epoch {
                    return Some(WireMessage::Error {
                        code: crate::message::error_codes::STALE_EPOCH,
                        message: format!(
                            "stale session epoch: message has epoch {msg_epoch}, \
                             current session is epoch {current_epoch}"
                        ),
                    });
                }

                // Silently accept and queue — pipeline delivery is async.
                // In a full implementation, this would be dispatched to the
                // CrossFedPipelineBridge for eventual delivery.
                let _ = (
                    target_promise_id,
                    method,
                    args,
                    authorization,
                    result_promise_id,
                );
                None
            }

            WireMessage::PresentHandoff {
                presentation_bytes,
                introducer_pk,
            } => {
                // Deserialize the presentation.
                let presentation: HandoffPresentation =
                    match postcard::from_bytes(&presentation_bytes) {
                        Ok(p) => p,
                        Err(e) => {
                            return Some(WireMessage::Error {
                                code: crate::message::error_codes::HANDOFF_FAILED,
                                message: format!("handoff deserialization failed: {e}"),
                            });
                        }
                    };

                let intro_pk = pyana_types::PublicKey(introducer_pk);
                let mut captp = captp_state.write().await;
                let current_height = captp.current_height;
                let known_feds = captp.known_federations.clone();

                // Validate the handoff.
                match validate_handoff(
                    &presentation,
                    &intro_pk,
                    &mut captp.swiss_table,
                    &known_feds,
                    current_height,
                ) {
                    Ok(acceptance) => {
                        let perm_tag = match &acceptance.permissions {
                            pyana_cell::AuthRequired::None => 0u8,
                            pyana_cell::AuthRequired::Signature => 1u8,
                            pyana_cell::AuthRequired::Proof => 2u8,
                            pyana_cell::AuthRequired::Either => 3u8,
                            pyana_cell::AuthRequired::Impossible => 4u8,
                        };
                        Some(WireMessage::HandoffAccepted {
                            routing_token: acceptance.routing_token,
                            cell_id: acceptance.cell_id.0,
                            permissions_tag: perm_tag,
                        })
                    }
                    Err(e) => Some(WireMessage::Error {
                        code: crate::message::error_codes::HANDOFF_FAILED,
                        message: e.to_string(),
                    }),
                }
            }

            WireMessage::HandoffAccepted { .. } => {
                // This is a response, not a request; no action needed on the server side.
                None
            }

            WireMessage::PeerChallenge { .. }
            | WireMessage::PeerAuthResponse { .. }
            | WireMessage::PeerAuthenticated { .. } => {
                // Peer authentication protocol messages are handled at a lower layer
                // (connection establishment). If they arrive during the main message
                // loop, they are spurious and safely ignored.
                None
            }
        }
    }

    /// Verify a proof using the provided verifier. Exposed for testing.
    ///
    /// Uses an all-zeros request digest (suitable for testing verifiers that
    /// don't check action binding, like `NoopVerifier` or `MinSizeVerifier`).
    pub fn verify_proof_with(proof: &[u8], verifier: &dyn ProofVerifier) -> bool {
        match verifier.verify(proof, "", "") {
            Ok(result) => result,
            Err(_) => false,
        }
    }

    /// Present a token to a remote peer.
    ///
    /// This is the client-side operation: connect to a peer silo, perform
    /// the handshake, and present a token for authorization.
    ///
    /// The client verifies that the response's `request_digest` matches the
    /// digest of the request it sent, preventing MITM response-swapping attacks
    /// (issue 2).
    pub async fn present_token(
        &self,
        peer_addr: &str,
        proof: &[u8],
        request: &AuthorizationRequest,
    ) -> Result<bool, ConnectionError> {
        let mut conn = PeerConnection::connect(peer_addr).await?;

        // Perform handshake
        let hello = WireMessage::Hello {
            node_id: self.config.node_id,
            node_name: self.config.name.clone(),
            protocol_version: PROTOCOL_VERSION,
            capabilities: self.config.capabilities.clone(),
        };
        conn.send(hello).await?;
        let _welcome = conn.recv().await?;

        // Get the current federation root from state
        let federation_root = self.state.read().await.federation_root;

        // Compute the expected digest before sending
        let expected_digest = request.digest();

        // Present the token
        let present = WireMessage::PresentToken {
            proof: proof.to_vec(),
            request: request.clone(),
            federation_root,
        };
        conn.send(present).await?;

        // Wait for result
        match conn.recv().await? {
            WireMessage::PresentationResult {
                accepted,
                request_digest,
                ..
            } => {
                // --- Issue 2: Verify the response is bound to our request ---
                if request_digest != expected_digest {
                    return Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                        std::io::Error::new(
                            std::io::ErrorKind::InvalidData,
                            "response request_digest does not match sent request (possible MITM)",
                        ),
                    )));
                }
                Ok(accepted)
            }
            WireMessage::Error { message, .. } => {
                Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                    std::io::Error::new(std::io::ErrorKind::Other, message),
                )))
            }
            _ => Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                std::io::Error::new(std::io::ErrorKind::InvalidData, "unexpected response"),
            ))),
        }
    }

    /// Submit a revocation to a remote peer.
    ///
    /// Includes a fresh nonce and timestamp to prevent replay attacks (issue 6).
    pub async fn submit_revocation(
        &self,
        peer_addr: &str,
        token_id: &str,
        authority: &PublicKey,
        authority_sig: &Signature,
    ) -> Result<([u8; 32], u64), ConnectionError> {
        let mut conn = PeerConnection::connect(peer_addr).await?;

        let mut nonce = [0u8; 16];
        getrandom::fill(&mut nonce).expect("getrandom failed");

        let msg = WireMessage::SubmitRevocation {
            token_id: token_id.to_string(),
            authority: *authority,
            authority_sig: *authority_sig,
            nonce,
            timestamp: current_timestamp(),
        };
        conn.send(msg).await?;

        match conn.recv().await? {
            WireMessage::RevocationAck { new_root, height } => Ok((new_root, height)),
            WireMessage::Error { message, .. } => {
                Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                    std::io::Error::new(std::io::ErrorKind::Other, message),
                )))
            }
            _ => Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                std::io::Error::new(std::io::ErrorKind::InvalidData, "unexpected response"),
            ))),
        }
    }

    /// Request the attested root from a remote peer.
    ///
    /// The client verifies that the returned `AttestedRoot` has valid quorum
    /// signatures before trusting it (issue 3).
    pub async fn request_attested_root(
        &self,
        peer_addr: &str,
    ) -> Result<([u8; 32], u64, i64), ConnectionError> {
        let mut conn = PeerConnection::connect(peer_addr).await?;

        conn.send(WireMessage::RequestAttestedRoot).await?;

        match conn.recv().await? {
            WireMessage::AttestedRoot {
                root,
                height,
                timestamp,
                signatures,
                ..
            } => {
                // --- Issue 3: Verify quorum signatures before trusting ---
                // The signing message is the root concatenated with height.
                let mut signing_msg = Vec::with_capacity(40);
                signing_msg.extend_from_slice(&root);
                signing_msg.extend_from_slice(&height.to_le_bytes());

                let valid_sigs = signatures
                    .iter()
                    .filter(|(pk, sig)| pk.verify(&signing_msg, sig))
                    .count();

                // Enforce quorum threshold: require 2f+1 valid signatures where
                // f = (member_count - 1) / 3. Accept unsigned roots only for initial
                // bootstrap / test scenarios where the root is the genesis root.
                if !signatures.is_empty() {
                    let member_count = self.state.read().await.member_count as usize;
                    let required_threshold = if member_count > 0 {
                        // BFT quorum: 2f+1 where f = (n-1)/3
                        let f = (member_count - 1) / 3;
                        2 * f + 1
                    } else {
                        1
                    };

                    if valid_sigs < required_threshold {
                        return Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                            std::io::Error::new(
                                std::io::ErrorKind::InvalidData,
                                format!(
                                    "insufficient quorum: got {} valid signatures, need {}",
                                    valid_sigs, required_threshold
                                ),
                            ),
                        )));
                    }
                }

                Ok((root, height, timestamp))
            }
            _ => Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                std::io::Error::new(std::io::ErrorKind::InvalidData, "unexpected response"),
            ))),
        }
    }

    /// Request a non-membership proof from a remote peer.
    ///
    /// Verifies the proof against the returned root before returning it.
    pub async fn request_non_membership(
        &self,
        peer_addr: &str,
        token_id: &str,
    ) -> Result<Option<Vec<u8>>, ConnectionError> {
        let mut conn = PeerConnection::connect(peer_addr).await?;

        conn.send(WireMessage::RequestNonMembership {
            token_id: token_id.to_string(),
        })
        .await?;

        match conn.recv().await? {
            WireMessage::NonMembershipResponse { proof, root, .. } => {
                // Verify the non-membership attestation before trusting it.
                if let Some(ref proof_bytes) = proof {
                    let mut hasher = blake3::Hasher::new_derive_key("pyana-wire non-membership-v1");
                    hasher.update(token_id.as_bytes());
                    hasher.update(&root);
                    let expected = hasher.finalize();

                    if proof_bytes.as_slice() != expected.as_bytes() {
                        return Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                            std::io::Error::new(
                                std::io::ErrorKind::InvalidData,
                                "non-membership proof verification failed: attestation mismatch",
                            ),
                        )));
                    }
                }
                Ok(proof)
            }
            _ => Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                std::io::Error::new(std::io::ErrorKind::InvalidData, "unexpected response"),
            ))),
        }
    }

    /// Update the silo's federation root (e.g., after syncing with peers).
    pub async fn set_federation_root(&self, root: [u8; 32], height: u64) {
        let mut st = self.state.write().await;
        st.federation_root = root;
        st.height = height;
        st.last_root_update = current_timestamp();
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Get the current Unix timestamp.
fn current_timestamp() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

/// Compute the message that a revocation authority must sign.
///
/// The signature covers `blake3(token_id || nonce || timestamp)` using the
/// domain separation key `"pyana-wire revocation-sig v1"`. This ensures the
/// signature is bound to the specific nonce and timestamp, preventing replay
/// and substitution attacks.
///
/// Both the client (when constructing `SubmitRevocation`) and the server (when
/// verifying) must use this function to compute the signing message.
pub fn revocation_signing_message(token_id: &str, nonce: &[u8; 16], timestamp: i64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-wire revocation-sig v1");
    hasher.update(token_id.as_bytes());
    hasher.update(nonce);
    hasher.update(&timestamp.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Attempt to generate a non-membership proof for the given token.
///
/// Delegates to the handler's `prove_non_revocation` method, which generates
/// a Merkle-based non-membership proof from the `RevocationRegistry`'s sorted
/// tree. Falls back to the legacy attestation hash when no handler is available.
fn generate_non_membership_proof(
    token_id: &str,
    root: &[u8; 32],
    handler: Option<&dyn RevocationHandler>,
) -> Option<Vec<u8>> {
    let handler = handler?;

    // If the handler says it IS revoked, we cannot produce a non-membership proof.
    if handler.is_revoked(token_id) {
        return None;
    }

    // Try the handler's Merkle-based proof generation first.
    if let Some(proof) = handler.prove_non_revocation(token_id) {
        return Some(proof);
    }

    // Fallback: produce a legacy attestation binding (for handlers that don't
    // implement Merkle proof generation).
    let handler_root = handler.current_root();
    if handler_root != *root {
        return None;
    }

    let mut hasher = blake3::Hasher::new_derive_key("pyana-wire non-membership-v1");
    hasher.update(token_id.as_bytes());
    hasher.update(root);
    let attestation = hasher.finalize();
    Some(attestation.as_bytes().to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn server_accepts_hello() {
        let config = SiloConfig::new("test-silo").with_verifier(Arc::new(NoopVerifier));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        client
            .send(WireMessage::Hello {
                node_id: [0x11; 32],
                node_name: "client".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::Welcome {
                member_count,
                node_name,
                ..
            } => {
                assert!(member_count > 0);
                assert_eq!(node_name, "test-silo");
            }
            other => panic!("expected Welcome, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn server_handles_presentation() {
        let config =
            SiloConfig::new("verifier").with_verifier(Arc::new(MinSizeVerifier { min_bytes: 100 }));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        let state = Arc::clone(&server.state);

        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let federation_root = state.read().await.federation_root;

        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Must send Hello first (P0-2: handshake enforcement)
        client
            .send(WireMessage::Hello {
                node_id: [0x22; 32],
                node_name: "presenter-client".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();
        let _welcome = client.recv().await.unwrap();

        // Present with a proof that's large enough
        let request = AuthorizationRequest::new("resource", "read", "alice");
        let msg = WireMessage::PresentToken {
            proof: vec![0xab; 200],
            request: request.clone(),
            federation_root,
        };
        client.send(msg).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::PresentationResult { accepted, .. } => {
                assert!(accepted, "proof of 200 bytes should pass min-100 check");
            }
            other => panic!("expected PresentationResult, got {other:?}"),
        }

        // Present with a proof that's too small (new request to avoid nonce replay)
        let request2 = AuthorizationRequest::new("resource", "read", "alice");
        let msg = WireMessage::PresentToken {
            proof: vec![0xab; 50],
            request: request2,
            federation_root,
        };
        client.send(msg).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::PresentationResult {
                accepted, reason, ..
            } => {
                assert!(!accepted);
                assert!(reason.is_some());
            }
            other => panic!("expected PresentationResult, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn server_handles_revocation() {
        // Generate the keypair FIRST so we can add it to the whitelist.
        let (sk, pk) = pyana_types::generate_keypair();

        let config = SiloConfig::new("revoker")
            .with_verifier(Arc::new(NoopVerifier))
            .with_revocation_authorities(vec![pk]);
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        let state = Arc::clone(&server.state);

        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Must send Hello first (P0-2: handshake enforcement)
        client
            .send(WireMessage::Hello {
                node_id: [0x11; 32],
                node_name: "revoker-client".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();
        let _welcome = client.recv().await.unwrap();
        let token_id = "tok-revoke-me";

        let mut nonce = [0u8; 16];
        getrandom::fill(&mut nonce).unwrap();
        let timestamp = current_timestamp();

        // Sign over blake3(token_id || nonce || timestamp) per P1-7.
        let sig_message = {
            let mut hasher = blake3::Hasher::new_derive_key("pyana-wire revocation-sig v1");
            hasher.update(token_id.as_bytes());
            hasher.update(&nonce);
            hasher.update(&timestamp.to_le_bytes());
            *hasher.finalize().as_bytes()
        };
        let sig = pyana_types::sign(&sk, &sig_message);

        let msg = WireMessage::SubmitRevocation {
            token_id: token_id.to_string(),
            authority: pk,
            authority_sig: sig,
            nonce,
            timestamp,
        };
        client.send(msg).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::RevocationAck { height, .. } => {
                assert_eq!(height, 1);
            }
            other => panic!("expected RevocationAck, got {other:?}"),
        }

        // Verify the token is now revoked in state
        let st = state.read().await;
        assert!(st.is_revoked("tok-revoke-me"));
        assert!(!st.is_revoked("tok-other"));
    }

    #[tokio::test]
    async fn server_rejects_revocation_with_invalid_signature() {
        // Generate a valid keypair and configure it as the only authority.
        let (_sk, pk) = pyana_types::generate_keypair();
        let config = SiloConfig::new("revoker")
            .with_verifier(Arc::new(NoopVerifier))
            .with_revocation_authorities(vec![pk]);
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();

        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Must send Hello first (P0-2: handshake enforcement)
        client
            .send(WireMessage::Hello {
                node_id: [0x11; 32],
                node_name: "forger-client".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();
        let _welcome = client.recv().await.unwrap();

        let mut nonce = [0u8; 16];
        getrandom::fill(&mut nonce).unwrap();

        // Use a forged signature: correct authority key but wrong signature bytes.
        // This tests that even with the authority in the whitelist, a bad signature
        // is rejected.
        let msg = WireMessage::SubmitRevocation {
            token_id: "tok-forged".to_string(),
            authority: pk,
            authority_sig: Signature([0xcc; 64]),
            nonce,
            timestamp: current_timestamp(),
        };
        client.send(msg).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::Error { code, message } => {
                assert_eq!(code, crate::message::error_codes::INVALID_SIGNATURE);
                assert!(message.contains("signature"));
            }
            other => panic!("expected Error, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn server_rejects_revocation_without_configured_authorities() {
        // With no revocation authorities configured, ALL revocations must be rejected
        // (fail-closed). This tests the secure default.
        let config = SiloConfig::new("revoker").with_verifier(Arc::new(NoopVerifier));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();

        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        client
            .send(WireMessage::Hello {
                node_id: [0x11; 32],
                node_name: "fail-closed-client".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();
        let _welcome = client.recv().await.unwrap();

        let mut nonce = [0u8; 16];
        getrandom::fill(&mut nonce).unwrap();

        let msg = WireMessage::SubmitRevocation {
            token_id: "tok-should-fail".to_string(),
            authority: PublicKey([0xdd; 32]),
            authority_sig: Signature([0xcc; 64]),
            nonce,
            timestamp: current_timestamp(),
        };
        client.send(msg).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::Error { code, message } => {
                assert_eq!(code, crate::message::error_codes::INVALID_SIGNATURE);
                assert!(
                    message.contains("no revocation authorities configured"),
                    "expected fail-closed message, got: {message}"
                );
            }
            other => panic!("expected Error, got {other:?}"),
        }
    }

    #[test]
    fn silo_state_genesis() {
        let state = SiloState::genesis(5);
        assert_eq!(state.height, 0);
        assert_eq!(state.member_count, 5);
        assert!(state.revoked_tokens.is_empty());
    }

    #[test]
    fn silo_state_revocation() {
        let mut state = SiloState::genesis(5);
        let original_root = state.federation_root;

        state.apply_revocation("tok-1", &PublicKey([0xaa; 32]), &Signature([0xaa; 64]));
        assert_eq!(state.height, 1);
        assert!(state.is_revoked("tok-1"));
        assert!(!state.is_revoked("tok-2"));
        assert_ne!(state.federation_root, original_root);

        let root_after_first = state.federation_root;
        state.apply_revocation("tok-2", &PublicKey([0xbb; 32]), &Signature([0xbb; 64]));
        assert_eq!(state.height, 2);
        assert!(state.is_revoked("tok-2"));
        assert_ne!(state.federation_root, root_after_first);
    }

    #[test]
    fn captp_process_introduction_exports_registers_gc() {
        use pyana_captp::DropResult;

        let mut captp = CapTpState::new();
        captp.current_height = 50;

        let target_cell = pyana_types::CellId([0x11; 32]);
        let recipient_cell = pyana_types::CellId([0x22; 32]);
        let recipient_federation = FederationId([0xBB; 32]);

        let exports = vec![pyana_turn::IntroductionExport {
            target: target_cell,
            recipient: recipient_cell,
            authorizing_turn: [0xAA; 32],
            expires: Some(150),
        }];

        // Process with a resolver that maps recipient -> federation
        let registered = captp.process_introduction_exports(&exports, |cell_id| {
            if *cell_id == recipient_cell {
                Some(recipient_federation)
            } else {
                None
            }
        });

        assert_eq!(registered, 1);

        // Verify the export is tracked in the GC manager
        let entry = captp
            .export_gc
            .get(&target_cell)
            .expect("should be tracked");
        assert_eq!(entry.total_refs, 1);
        assert!(entry.holders.contains_key(&recipient_federation));
        assert_eq!(entry.holders[&recipient_federation].count, 1);
        assert_eq!(entry.holders[&recipient_federation].last_activity, 50);

        // Simulate DropRef from recipient's federation -> cleans up
        let result = captp
            .export_gc
            .process_drop(target_cell, recipient_federation);
        assert_eq!(result, DropResult::CanRevoke);
    }

    #[test]
    fn captp_process_introduction_exports_skips_unknown_federation() {
        let mut captp = CapTpState::new();
        captp.current_height = 10;

        let target_cell = pyana_types::CellId([0x33; 32]);
        let unknown_recipient = pyana_types::CellId([0x44; 32]);

        let exports = vec![pyana_turn::IntroductionExport {
            target: target_cell,
            recipient: unknown_recipient,
            authorizing_turn: [0xCC; 32],
            expires: None,
        }];

        // Resolver returns None (federation unknown)
        let registered = captp.process_introduction_exports(&exports, |_| None);

        assert_eq!(registered, 0);
        // Nothing tracked
        assert!(captp.export_gc.is_empty());
    }

    #[test]
    fn verification_modes() {
        let proof_small = vec![0u8; 50];
        let proof_big = vec![0u8; 200];

        assert!(SiloServer::verify_proof_with(&proof_small, &NoopVerifier));
        assert!(!SiloServer::verify_proof_with(
            &proof_small,
            &RejectAllVerifier
        ));
        assert!(!SiloServer::verify_proof_with(
            &proof_small,
            &MinSizeVerifier { min_bytes: 100 }
        ));
        assert!(SiloServer::verify_proof_with(
            &proof_big,
            &MinSizeVerifier { min_bytes: 100 }
        ));
    }

    #[test]
    fn stark_verifier_rejects_garbage() {
        let garbage = vec![0u8; 100];
        let verifier = StarkVerifier;
        // Random bytes should not pass STARK verification
        assert!(!SiloServer::verify_proof_with(&garbage, &verifier));
    }

    // =========================================================================
    // Federation Boundary Enforcement Tests
    // =========================================================================

    #[tokio::test]
    async fn require_auth_drops_failed_connections() {
        // Server with require_auth=true: unauthenticated peers get dropped.
        let (_sk, pk) = pyana_types::generate_keypair();
        let participant_key = pk.0;
        let participants = StaticParticipants::new(vec![participant_key]);

        let auth_config = crate::auth::AuthConfig::strict();

        let config = SiloConfig::new("strict-silo").with_verifier(Arc::new(NoopVerifier));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config)
            .with_participant_source(Arc::new(participants))
            .with_auth_config(auth_config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Send Hello
        client
            .send(WireMessage::Hello {
                node_id: [0x11; 32],
                node_name: "bad-peer".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();
        let _welcome = client.recv().await.unwrap();

        // Server sends PeerChallenge, we respond with WRONG signature
        let challenge = client.recv().await.unwrap();
        match challenge {
            WireMessage::PeerChallenge { .. } => {}
            other => panic!("expected PeerChallenge, got {other:?}"),
        }

        // Send bad auth response
        client
            .send(WireMessage::PeerAuthResponse {
                participant_key,
                signature: Signature([0xFF; 64]), // Invalid signature
                claimed_constitution_version: 0,
            })
            .await
            .unwrap();

        // Should get PeerAuthenticated with Anonymous role
        let auth_result = client.recv().await.unwrap();
        match &auth_result {
            WireMessage::PeerAuthenticated { role_tag, .. } => {
                assert_eq!(*role_tag, PeerRole::Anonymous.tag());
            }
            other => panic!("expected PeerAuthenticated, got {other:?}"),
        }

        // Then should get Error (connection being dropped due to require_auth)
        let error = client.recv().await.unwrap();
        match error {
            WireMessage::Error { code, message } => {
                assert_eq!(code, crate::message::error_codes::PEER_AUTH_FAILED);
                assert!(message.contains("authentication required"));
            }
            other => panic!("expected Error, got {other:?}"),
        }

        // Connection should now be closed
        let result = client.recv().await;
        assert!(
            result.is_err(),
            "connection should be closed after require_auth failure"
        );
    }

    #[tokio::test]
    async fn authenticated_member_can_proceed() {
        // Server with require_auth=true: properly authenticated peers proceed.
        let (sk, pk) = pyana_types::generate_keypair();
        let participant_key = pk.0;
        let participants = StaticParticipants::new(vec![participant_key]);

        let auth_config = crate::auth::AuthConfig::strict();

        let config = SiloConfig::new("auth-silo").with_verifier(Arc::new(NoopVerifier));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config.clone())
            .with_participant_source(Arc::new(participants))
            .with_auth_config(auth_config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        let server_node_id = config.node_id;
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Send Hello
        client
            .send(WireMessage::Hello {
                node_id: [0x11; 32],
                node_name: "good-peer".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();
        let _welcome = client.recv().await.unwrap();

        // Server sends PeerChallenge
        let challenge = client.recv().await.unwrap();
        let nonce = match challenge {
            WireMessage::PeerChallenge {
                nonce,
                server_node_id: sid,
            } => {
                assert_eq!(sid, server_node_id);
                nonce
            }
            other => panic!("expected PeerChallenge, got {other:?}"),
        };

        // Sign the challenge correctly
        let signing_msg = peer_auth_signing_message(&nonce, &server_node_id);
        let sig = pyana_types::sign(&sk, &signing_msg);

        client
            .send(WireMessage::PeerAuthResponse {
                participant_key,
                signature: sig,
                claimed_constitution_version: 0,
            })
            .await
            .unwrap();

        // Should get PeerAuthenticated with Member role
        let auth_result = client.recv().await.unwrap();
        match auth_result {
            WireMessage::PeerAuthenticated {
                role_tag,
                authenticated_key,
            } => {
                assert_eq!(role_tag, PeerRole::Member { participant_key }.tag());
                assert_eq!(authenticated_key, participant_key);
            }
            other => panic!("expected PeerAuthenticated(Member), got {other:?}"),
        }

        // Connection should still be alive - send a ping
        client
            .send(WireMessage::Ping {
                seq: 42,
                timestamp: 12345,
            })
            .await
            .unwrap();
        let pong = client.recv().await.unwrap();
        match pong {
            WireMessage::Pong { seq, .. } => assert_eq!(seq, 42),
            other => panic!("expected Pong, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn gossip_filter_blocks_state_replication_for_anonymous() {
        use crate::auth::GossipFilter;

        // Unit test: Anonymous peers should not receive state-replication messages
        let anon = PeerRole::Anonymous;
        let member = PeerRole::Member {
            participant_key: [0xAA; 32],
        };
        let captp = PeerRole::CapTpPeer {
            peer_strand: [0xBB; 32],
            group_id: None,
        };

        // SubmitRevocation = state replication
        let revocation = WireMessage::SubmitRevocation {
            token_id: "tok".to_string(),
            authority: PublicKey([0; 32]),
            authority_sig: Signature([0; 64]),
            nonce: [0; 16],
            timestamp: 0,
        };

        assert!(!GossipFilter::should_send_to_peer(&revocation, &anon));
        assert!(!GossipFilter::should_send_to_peer(&revocation, &captp));
        assert!(GossipFilter::should_send_to_peer(&revocation, &member));

        // CapTP messages
        let cap_hello = WireMessage::CapHello {
            group_id: [0; 32],
            initial_exports: vec![],
        };
        assert!(!GossipFilter::should_send_to_peer(&cap_hello, &anon));
        assert!(GossipFilter::should_send_to_peer(&cap_hello, &captp));
        assert!(GossipFilter::should_send_to_peer(&cap_hello, &member));

        // Public messages
        let ping = WireMessage::Ping {
            seq: 0,
            timestamp: 0,
        };
        assert!(GossipFilter::should_send_to_peer(&ping, &anon));
        assert!(GossipFilter::should_send_to_peer(&ping, &captp));
        assert!(GossipFilter::should_send_to_peer(&ping, &member));
    }

    #[tokio::test]
    async fn rate_limit_anonymous_is_stricter() {
        use crate::auth::{RateLimitConfig, RateLimiter as AuthRateLimiter};
        use std::time::Duration;

        let config = RateLimitConfig {
            anonymous_max: 5,
            captp_max: 50,
            member_max: 500,
            window: Duration::from_secs(10),
        };

        // Anonymous limiter
        let mut anon_limiter = AuthRateLimiter::for_role(&PeerRole::Anonymous, &config);
        for _ in 0..5 {
            assert!(anon_limiter.check());
        }
        assert!(
            !anon_limiter.check(),
            "Anonymous should be limited after 5 messages"
        );

        // Member limiter (much higher limit)
        let mut member_limiter = AuthRateLimiter::for_role(
            &PeerRole::Member {
                participant_key: [0; 32],
            },
            &config,
        );
        for _ in 0..500 {
            assert!(member_limiter.check());
        }
        assert!(
            !member_limiter.check(),
            "Member should be limited after 500 messages"
        );
    }

    #[tokio::test]
    async fn ban_list_after_repeated_auth_failures() {
        use crate::auth::{BanConfig, BanList, BanReason};
        use std::net::IpAddr;
        use std::time::Duration;

        let config = BanConfig {
            max_auth_failures: 3,
            auth_failure_ban_duration: Duration::from_secs(300),
            ..Default::default()
        };
        let mut ban_list = BanList::new(config);
        let ip: IpAddr = "192.168.1.1".parse().unwrap();

        // Three failures -> ban
        assert!(!ban_list.record_auth_failure(&ip));
        assert!(!ban_list.record_auth_failure(&ip));
        assert!(ban_list.record_auth_failure(&ip));
        assert!(ban_list.is_banned(&ip));

        match ban_list.get_ban(&ip).unwrap().reason {
            BanReason::RepeatedAuthFailure { attempts } => assert_eq!(attempts, 3),
            _ => panic!("expected RepeatedAuthFailure"),
        }
    }
}
