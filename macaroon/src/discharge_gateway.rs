//! Discharge gateway: evaluates conditions and issues discharge macaroons for
//! third-party caveats.
//!
//! # Overview
//!
//! The discharge gateway is how dregg becomes useful without federation/ZK — just
//! macaroons:
//!
//! 1. Service A issues a token with caveat "get discharge from Service B"
//! 2. Client goes to Service B (the gateway), presents the ticket
//! 3. Gateway evaluates a condition (KYC, payment, proof, time, rate limit, etc.)
//! 4. Gateway issues a discharge macaroon
//! 5. Client binds discharge to their token, presents to Service A
//! 6. Service A verifies: token valid + discharge valid + binding correct
//!
//! This module provides the core logic, reusable without any HTTP layer.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use zeroize::Zeroize;

use crate::caveat_3p::ThirdPartyCaveat;
use crate::crypto;
use crate::macaroon::create_discharge;

// =============================================================================
// Core types
// =============================================================================

/// A request to obtain a discharge macaroon from the gateway.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DischargeRequest {
    /// Encrypted ticket from the 3P caveat (sent by the client).
    pub ticket: Vec<u8>,
    /// Who is asking (optional client identifier).
    pub client_id: Option<String>,
    /// Optional evidence (ZK proof or other).
    pub proof: Option<Vec<u8>>,
    /// Optional payment amount.
    pub payment: Option<u64>,
    /// Arbitrary key-value context for evaluator use.
    #[serde(default)]
    pub metadata: HashMap<String, String>,
}

/// A successful discharge response.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DischargeResponse {
    /// Base64-encoded discharge macaroon (em2_ prefixed).
    pub discharge: String,
    /// Unix timestamp when this discharge expires.
    pub expires_at: i64,
    /// Which condition was satisfied.
    pub condition_met: String,
}

/// Error returned when a discharge request is denied.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DischargeError {
    /// Human-readable denial reason.
    pub reason: String,
    /// The condition that was not met.
    pub condition: String,
}

impl std::fmt::Display for DischargeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "discharge denied ({}): {}", self.condition, self.reason)
    }
}

impl std::error::Error for DischargeError {}

// =============================================================================
// Condition Evaluators
// =============================================================================

/// Trait for evaluating whether a discharge condition is satisfied.
///
/// Implementations must be thread-safe and deterministic for a given request state.
pub trait ConditionEvaluator: Send + Sync {
    /// Evaluate whether the condition is satisfied.
    ///
    /// Returns `Ok(())` if the discharge should be issued, or `Err(reason)` if denied.
    fn evaluate(&self, request: &DischargeRequest) -> Result<(), String>;

    /// Human-readable name of this evaluator (for logging/metrics).
    fn name(&self) -> &str;
}

/// Always issue a discharge (for testing / open gateways).
pub struct AlwaysAllow;

impl ConditionEvaluator for AlwaysAllow {
    fn evaluate(&self, _request: &DischargeRequest) -> Result<(), String> {
        Ok(())
    }

    fn name(&self) -> &str {
        "always_allow"
    }
}

/// Issue only during a time window (e.g., business hours in a given timezone offset).
pub struct TimeWindowEvaluator {
    /// Start hour (0-23, inclusive).
    pub start_hour: u8,
    /// End hour (0-23, inclusive).
    pub end_hour: u8,
    /// UTC offset in hours (e.g., -5 for EST, +1 for CET).
    pub utc_offset_hours: i8,
}

impl ConditionEvaluator for TimeWindowEvaluator {
    fn evaluate(&self, _request: &DischargeRequest) -> Result<(), String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|e| format!("system clock error: {e}"))?;
        let secs = now.as_secs() as i64 + (self.utc_offset_hours as i64 * 3600);
        // Normalize to positive seconds.
        let secs = if secs < 0 { secs + 86400 } else { secs };
        let hour_of_day = ((secs % 86400) / 3600) as u8;

        if self.start_hour <= self.end_hour {
            // Normal range: e.g., 9..17
            if hour_of_day >= self.start_hour && hour_of_day <= self.end_hour {
                Ok(())
            } else {
                Err(format!(
                    "outside time window: current hour {} not in [{}, {}]",
                    hour_of_day, self.start_hour, self.end_hour
                ))
            }
        } else {
            // Wrapped range: e.g., 22..6 (overnight)
            if hour_of_day >= self.start_hour || hour_of_day <= self.end_hour {
                Ok(())
            } else {
                Err(format!(
                    "outside time window: current hour {} not in [{}, {}] (wrap)",
                    hour_of_day, self.start_hour, self.end_hour
                ))
            }
        }
    }

    fn name(&self) -> &str {
        "time_window"
    }
}

/// Per-client rate limiting: max N discharges per client per window.
pub struct RateLimitEvaluator {
    /// Maximum discharges per client per window.
    pub max_per_window: u32,
    /// Window duration in seconds.
    pub window_secs: u64,
    /// Maximum number of tracked clients (LRU eviction when exceeded).
    max_clients: usize,
    /// State: client_id -> (count, window_start_unix).
    state: Mutex<HashMap<String, (u32, u64)>>,
}

impl RateLimitEvaluator {
    /// Create a new rate limit evaluator.
    pub fn new(max_per_window: u32, window_secs: u64) -> Self {
        Self {
            max_per_window,
            window_secs,
            max_clients: 10_000,
            state: Mutex::new(HashMap::new()),
        }
    }

    /// Create a rate limit evaluator with a custom max clients limit.
    pub fn with_max_clients(max_per_window: u32, window_secs: u64, max_clients: usize) -> Self {
        Self {
            max_per_window,
            window_secs,
            max_clients,
            state: Mutex::new(HashMap::new()),
        }
    }
}

impl ConditionEvaluator for RateLimitEvaluator {
    fn evaluate(&self, request: &DischargeRequest) -> Result<(), String> {
        let client_id = request.client_id.as_deref().unwrap_or("anonymous");

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|e| format!("system clock error: {e}"))?
            .as_secs();

        let mut state = self
            .state
            .lock()
            .map_err(|e| format!("lock poisoned: {e}"))?;

        // Evict expired entries when the state grows too large to prevent
        // unbounded memory growth from accumulating stale client entries.
        if state.len() >= self.max_clients {
            state.retain(|_, (_, window_start)| now - *window_start < self.window_secs);
            // If still at capacity after evicting expired entries, clear all.
            if state.len() >= self.max_clients {
                state.clear();
            }
        }

        let entry = state.entry(client_id.to_string()).or_insert((0, now));

        // Reset window if expired.
        if now - entry.1 >= self.window_secs {
            *entry = (0, now);
        }

        // Check THEN increment to avoid off-by-one: a client at max_per_window
        // has already used their full quota.
        if entry.0 >= self.max_per_window {
            Err(format!(
                "rate limit exceeded: {} discharges in {}s window (max {})",
                entry.0, self.window_secs, self.max_per_window
            ))
        } else {
            entry.0 += 1;
            Ok(())
        }
    }

    fn name(&self) -> &str {
        "rate_limit"
    }
}

/// Require a minimum payment amount in the request.
pub struct PaymentEvaluator {
    /// Minimum payment amount required.
    pub min_amount: u64,
}

impl ConditionEvaluator for PaymentEvaluator {
    fn evaluate(&self, request: &DischargeRequest) -> Result<(), String> {
        match request.payment {
            Some(amount) if amount >= self.min_amount => Ok(()),
            Some(amount) => Err(format!(
                "insufficient payment: got {}, need at least {}",
                amount, self.min_amount
            )),
            None => Err(format!(
                "payment required: at least {} computrons",
                self.min_amount
            )),
        }
    }

    fn name(&self) -> &str {
        "payment"
    }
}

/// Require a non-empty proof blob in the request.
///
/// This evaluator only checks that proof bytes are present and non-empty.
/// For real deployments, use [`VerifyingProofEvaluator`] which actually
/// verifies the proof cryptographically.
pub struct ProofRequiredEvaluator;

impl ConditionEvaluator for ProofRequiredEvaluator {
    fn evaluate(&self, request: &DischargeRequest) -> Result<(), String> {
        match &request.proof {
            Some(proof) if !proof.is_empty() => Ok(()),
            _ => Err("proof required but not provided".to_string()),
        }
    }

    fn name(&self) -> &str {
        "proof_required"
    }
}

/// A proof verifier function signature.
///
/// Takes the raw proof bytes and the condition string (from the caveat),
/// and returns Ok(()) if verification passes or Err(reason) if it fails.
///
/// Implementors should:
/// - Deserialize the proof bytes into their proof format
/// - Extract public inputs and verify against expected values
/// - Call the actual cryptographic verification (e.g., STARK verify)
pub type ProofVerifierFn =
    Box<dyn Fn(&[u8], &DischargeRequest) -> Result<(), String> + Send + Sync>;

/// Require a cryptographically valid proof in the request.
///
/// Unlike [`ProofRequiredEvaluator`] which only checks presence, this evaluator
/// calls a user-provided verification function to actually verify the proof.
/// This is the production-grade evaluator for ZK proof discharge conditions.
///
/// # Example
///
/// ```
/// use dregg_macaroon::discharge_gateway::{VerifyingProofEvaluator, DischargeRequest};
///
/// let evaluator = VerifyingProofEvaluator::new(Box::new(|proof_bytes, _request| {
///     // In production: deserialize and verify the STARK proof
///     if proof_bytes.len() < 64 {
///         return Err("proof too short".to_string());
///     }
///     // ... actual verification ...
///     Ok(())
/// }));
/// ```
pub struct VerifyingProofEvaluator {
    verifier: ProofVerifierFn,
}

impl VerifyingProofEvaluator {
    /// Create a new verifying proof evaluator with the given verification function.
    pub fn new(verifier: ProofVerifierFn) -> Self {
        Self { verifier }
    }
}

impl ConditionEvaluator for VerifyingProofEvaluator {
    fn evaluate(&self, request: &DischargeRequest) -> Result<(), String> {
        match &request.proof {
            Some(proof) if !proof.is_empty() => (self.verifier)(proof, request),
            Some(_) => Err("proof is empty".to_string()),
            None => Err("proof required but not provided".to_string()),
        }
    }

    fn name(&self) -> &str {
        "verifying_proof"
    }
}

/// Require the client to be in an allowlist.
pub struct AllowlistEvaluator {
    /// Set of allowed client IDs.
    pub allowed: HashSet<String>,
}

impl ConditionEvaluator for AllowlistEvaluator {
    fn evaluate(&self, request: &DischargeRequest) -> Result<(), String> {
        match &request.client_id {
            Some(id) if self.allowed.contains(id) => Ok(()),
            Some(id) => Err(format!("client '{}' not in allowlist", id)),
            None => Err("client_id required for allowlist check".to_string()),
        }
    }

    fn name(&self) -> &str {
        "allowlist"
    }
}

/// Composite: ALL conditions must be satisfied.
pub struct AllOfEvaluator {
    pub evaluators: Vec<Box<dyn ConditionEvaluator>>,
}

impl ConditionEvaluator for AllOfEvaluator {
    fn evaluate(&self, request: &DischargeRequest) -> Result<(), String> {
        for eval in &self.evaluators {
            eval.evaluate(request)?;
        }
        Ok(())
    }

    fn name(&self) -> &str {
        "all_of"
    }
}

/// Composite: ANY condition must be satisfied.
pub struct AnyOfEvaluator {
    pub evaluators: Vec<Box<dyn ConditionEvaluator>>,
}

impl ConditionEvaluator for AnyOfEvaluator {
    fn evaluate(&self, request: &DischargeRequest) -> Result<(), String> {
        if self.evaluators.is_empty() {
            return Err("no evaluators configured".to_string());
        }
        let mut last_err = String::new();
        for eval in &self.evaluators {
            match eval.evaluate(request) {
                Ok(()) => return Ok(()),
                Err(e) => last_err = e,
            }
        }
        Err(format!("no condition satisfied; last: {}", last_err))
    }

    fn name(&self) -> &str {
        "any_of"
    }
}

// =============================================================================
// Discharge Gateway
// =============================================================================

/// Maximum number of entries in the replay prevention set before eviction.
/// When exceeded, the oldest entries are removed to bound memory usage.
const MAX_ISSUED_CACHE: usize = 100_000;

/// The discharge gateway: evaluates conditions and issues discharge macaroons.
pub struct DischargeGateway {
    /// The shared key for decrypting third-party tickets.
    /// This is the `KA` shared between the token issuer and this gateway.
    shared_key: [u8; 32],

    /// The gateway's location identifier (must match the 3P caveat location).
    location: String,

    /// Registered condition evaluators.
    evaluators: Vec<Box<dyn ConditionEvaluator>>,

    /// Issued discharge ticket hashes (for replay prevention).
    /// Uses a HashSet for O(1) lookup paired with a VecDeque for FIFO eviction.
    /// When the set exceeds MAX_ISSUED_CACHE entries, the oldest entries are
    /// removed. This bounds memory to ~3.2 MB (100K * 32 bytes) while still
    /// catching replays within the gateway's TTL window.
    issued: Mutex<BoundedReplaySet>,

    /// Discharge validity duration in seconds (default: 300 = 5 minutes).
    discharge_ttl_secs: i64,

    /// Counter of total discharges issued (for metrics).
    issued_count: Mutex<u64>,
}

/// Bounded replay prevention set: O(1) contains + FIFO eviction.
struct BoundedReplaySet {
    set: HashSet<[u8; 32]>,
    order: VecDeque<[u8; 32]>,
}

impl BoundedReplaySet {
    fn new() -> Self {
        Self {
            set: HashSet::new(),
            order: VecDeque::new(),
        }
    }

    fn contains(&self, hash: &[u8; 32]) -> bool {
        self.set.contains(hash)
    }

    fn insert(&mut self, hash: [u8; 32]) {
        // Evict oldest entries if at capacity.
        while self.set.len() >= MAX_ISSUED_CACHE {
            if let Some(oldest) = self.order.pop_front() {
                self.set.remove(&oldest);
            } else {
                break;
            }
        }
        self.set.insert(hash);
        self.order.push_back(hash);
    }

    fn clear(&mut self) {
        self.set.clear();
        self.order.clear();
    }
}

impl DischargeGateway {
    /// Create a new discharge gateway.
    ///
    /// # Arguments
    /// - `shared_key`: The key shared between token issuers and this gateway (`KA`).
    /// - `location`: The gateway's URL/identifier (must match 3P caveat locations).
    pub fn new(shared_key: [u8; 32], location: String) -> Self {
        Self {
            shared_key,
            location,
            evaluators: Vec::new(),
            issued: Mutex::new(BoundedReplaySet::new()),
            discharge_ttl_secs: 300,
            issued_count: Mutex::new(0),
        }
    }

    /// Set the discharge TTL (time-to-live) in seconds.
    pub fn set_discharge_ttl(&mut self, ttl_secs: i64) {
        self.discharge_ttl_secs = ttl_secs;
    }

    /// Register a condition evaluator.
    ///
    /// When a discharge is requested, ALL registered evaluators must pass.
    /// Use [`AllOfEvaluator`] or [`AnyOfEvaluator`] for composite logic.
    pub fn add_evaluator(&mut self, evaluator: Box<dyn ConditionEvaluator>) {
        self.evaluators.push(evaluator);
    }

    /// Get the gateway's location.
    pub fn location(&self) -> &str {
        &self.location
    }

    /// Get the number of discharges issued.
    pub fn issued_count(&self) -> u64 {
        *self.issued_count.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Get the shared key (for use in tests or setup).
    pub fn shared_key(&self) -> &[u8; 32] {
        &self.shared_key
    }

    /// Process a discharge request.
    ///
    /// 1. Decrypt the ticket using the shared key.
    /// 2. Check for replay (same ticket issued before).
    /// 3. Evaluate all registered conditions.
    /// 4. Issue a discharge macaroon signed with the discharge key from the ticket.
    ///
    /// # Returns
    /// - `Ok(DischargeResponse)` with the discharge macaroon if all conditions pass.
    /// - `Err(DischargeError)` if any condition fails or the ticket is invalid.
    pub fn process_request(
        &self,
        request: &DischargeRequest,
    ) -> Result<DischargeResponse, DischargeError> {
        // Step 1: Decrypt the ticket.
        let wire_ticket = ThirdPartyCaveat::decrypt_ticket(&request.ticket, &self.shared_key)
            .map_err(|e| DischargeError {
                reason: format!("failed to decrypt ticket: {e}"),
                condition: "ticket_decryption".to_string(),
            })?;

        // Step 2: Replay prevention — hash the ticket and check if already issued.
        let ticket_hash = crypto::hmac_sha256(&self.shared_key, &request.ticket);
        {
            let mut issued = self.issued.lock().map_err(|_| DischargeError {
                reason: "internal lock error".to_string(),
                condition: "internal".to_string(),
            })?;
            if issued.contains(&ticket_hash) {
                return Err(DischargeError {
                    reason: "ticket already discharged (replay detected)".to_string(),
                    condition: "replay_prevention".to_string(),
                });
            }
            issued.insert(ticket_hash);
        }

        // Step 3: Evaluate all conditions.
        let mut condition_met = String::from("none");
        for evaluator in &self.evaluators {
            evaluator
                .evaluate(request)
                .map_err(|reason| DischargeError {
                    reason,
                    condition: evaluator.name().to_string(),
                })?;
            condition_met = evaluator.name().to_string();
        }
        if self.evaluators.is_empty() {
            condition_met = "unconditional".to_string();
        }

        // Step 4: Issue the discharge macaroon.
        let mut discharge_key = [0u8; 32];
        discharge_key.copy_from_slice(&wire_ticket.discharge_key);

        let discharge = create_discharge(
            request.ticket.clone(),
            &discharge_key,
            self.location.clone(),
            &[], // No additional first-party caveats on the discharge itself.
        );

        let encoded = discharge.encode().map_err(|e| DischargeError {
            reason: format!("failed to encode discharge: {e}"),
            condition: "encoding".to_string(),
        })?;

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64;

        // Increment issued counter.
        if let Ok(mut count) = self.issued_count.lock() {
            *count += 1;
        }

        Ok(DischargeResponse {
            discharge: encoded,
            expires_at: now + self.discharge_ttl_secs,
            condition_met,
        })
    }

    /// Reset the replay prevention set (for testing only).
    #[cfg(test)]
    pub fn reset_issued(&self) {
        if let Ok(mut issued) = self.issued.lock() {
            issued.clear();
        }
    }

    /// Serialize the replay prevention set for persistence.
    ///
    /// Returns a byte vector containing all ticket hashes in FIFO order.
    /// Each hash is 32 bytes, concatenated sequentially.
    pub fn serialize_issued_set(&self) -> Vec<u8> {
        let issued = match self.issued.lock() {
            Ok(guard) => guard,
            Err(e) => e.into_inner(),
        };
        let mut data = Vec::with_capacity(issued.order.len() * 32);
        for hash in &issued.order {
            data.extend_from_slice(hash);
        }
        data
    }

    /// Load a previously persisted replay prevention set.
    ///
    /// The input must be a sequence of 32-byte hashes (as produced by
    /// `serialize_issued_set`). Invalid-length data is silently ignored.
    pub fn load_issued_set(&self, data: &[u8]) {
        if data.len() % 32 != 0 {
            return;
        }
        let mut issued = match self.issued.lock() {
            Ok(guard) => guard,
            Err(e) => e.into_inner(),
        };
        issued.clear();
        for chunk in data.chunks_exact(32) {
            let mut hash = [0u8; 32];
            hash.copy_from_slice(chunk);
            // Use insert which handles eviction of oldest entries.
            issued.insert(hash);
        }
    }
}

impl Drop for DischargeGateway {
    fn drop(&mut self) {
        self.shared_key.zeroize();
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CaveatSet, Macaroon};

    /// Helper: create a macaroon with a 3P caveat targeting our gateway.
    fn setup_3p_macaroon(root_key: &[u8; 32], shared_key: &[u8; 32], location: &str) -> Macaroon {
        let mut mac = Macaroon::new(root_key, b"test-kid".to_vec(), "https://issuer.dev".into());
        mac.add_third_party(location, shared_key, CaveatSet::new())
            .unwrap();
        mac
    }

    /// Extract the ticket from a macaroon's 3P caveat.
    fn extract_ticket(mac: &Macaroon) -> Vec<u8> {
        let tp_caveats = mac.caveats.third_party_caveats();
        let tp = ThirdPartyCaveat::decode_body(&tp_caveats[0].body).unwrap();
        tp.ticket.clone()
    }

    #[test]
    fn test_always_allow_issues_discharge() {
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();
        let location = "https://gateway.dev";

        let mut gateway = DischargeGateway::new(shared_key, location.to_string());
        gateway.add_evaluator(Box::new(AlwaysAllow));

        let mac = setup_3p_macaroon(&root_key, &shared_key, location);
        let ticket = extract_ticket(&mac);

        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: None,
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };

        let response = gateway.process_request(&request).unwrap();
        assert!(!response.discharge.is_empty());
        assert!(response.discharge.starts_with("em2_"));
        assert_eq!(response.condition_met, "always_allow");
        assert!(response.expires_at > 0);

        // Now bind the discharge and verify the full token.
        let mut discharge = Macaroon::decode(&response.discharge).unwrap();
        mac.bind_discharge(&mut discharge);
        let result = mac.verify(&root_key, &[discharge]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_replay_prevention() {
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();
        let location = "https://gateway.dev";

        let mut gateway = DischargeGateway::new(shared_key, location.to_string());
        gateway.add_evaluator(Box::new(AlwaysAllow));

        let mac = setup_3p_macaroon(&root_key, &shared_key, location);
        let ticket = extract_ticket(&mac);

        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: None,
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };

        // First request succeeds.
        let resp = gateway.process_request(&request);
        assert!(resp.is_ok());

        // Second request with same ticket is rejected (replay).
        let resp = gateway.process_request(&request);
        assert!(resp.is_err());
        let err = resp.unwrap_err();
        assert!(err.reason.contains("replay"));
    }

    #[test]
    fn test_rate_limit_enforced() {
        let shared_key = crypto::random_key();
        let location = "https://gateway.dev";

        let mut gateway = DischargeGateway::new(shared_key, location.to_string());
        gateway.add_evaluator(Box::new(RateLimitEvaluator::new(2, 3600)));

        // Issue 2 discharges (different tickets each time).
        for i in 0..2 {
            let root_key = crypto::random_key();
            let mac = setup_3p_macaroon(&root_key, &shared_key, location);
            let ticket = extract_ticket(&mac);

            let request = DischargeRequest {
                ticket,
                client_id: Some("client-1".into()),
                proof: None,
                payment: None,
                metadata: HashMap::new(),
            };

            let resp = gateway.process_request(&request);
            assert!(resp.is_ok(), "request {} should succeed", i);
        }

        // 3rd should be rejected.
        let root_key = crypto::random_key();
        let mac = setup_3p_macaroon(&root_key, &shared_key, location);
        let ticket = extract_ticket(&mac);

        let request = DischargeRequest {
            ticket,
            client_id: Some("client-1".into()),
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };

        let resp = gateway.process_request(&request);
        assert!(resp.is_err());
        let err = resp.unwrap_err();
        assert_eq!(err.condition, "rate_limit");
    }

    #[test]
    fn test_payment_required() {
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();
        let location = "https://gateway.dev";

        let mut gateway = DischargeGateway::new(shared_key, location.to_string());
        gateway.add_evaluator(Box::new(PaymentEvaluator { min_amount: 100 }));

        let mac = setup_3p_macaroon(&root_key, &shared_key, location);
        let ticket = extract_ticket(&mac);

        // No payment → rejected.
        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: None,
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };
        let resp = gateway.process_request(&request);
        assert!(resp.is_err());

        // Reset replay set for re-test.
        gateway.reset_issued();

        // Insufficient payment → rejected.
        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: None,
            proof: None,
            payment: Some(50),
            metadata: HashMap::new(),
        };
        let resp = gateway.process_request(&request);
        assert!(resp.is_err());

        gateway.reset_issued();

        // Sufficient payment → success.
        let request = DischargeRequest {
            ticket,
            client_id: None,
            proof: None,
            payment: Some(100),
            metadata: HashMap::new(),
        };
        let resp = gateway.process_request(&request);
        assert!(resp.is_ok());
    }

    #[test]
    fn test_allowlist_evaluator() {
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();
        let location = "https://gateway.dev";

        let mut allowed = HashSet::new();
        allowed.insert("alice".to_string());
        allowed.insert("bob".to_string());

        let mut gateway = DischargeGateway::new(shared_key, location.to_string());
        gateway.add_evaluator(Box::new(AllowlistEvaluator { allowed }));

        let mac = setup_3p_macaroon(&root_key, &shared_key, location);
        let ticket = extract_ticket(&mac);

        // Alice is allowed.
        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: Some("alice".into()),
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };
        assert!(gateway.process_request(&request).is_ok());

        gateway.reset_issued();

        // Eve is denied.
        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: Some("eve".into()),
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };
        let resp = gateway.process_request(&request);
        assert!(resp.is_err());
        assert_eq!(resp.unwrap_err().condition, "allowlist");
    }

    #[test]
    fn test_composite_all_of() {
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();
        let location = "https://gateway.dev";

        let mut allowed = HashSet::new();
        allowed.insert("alice".to_string());

        let mut gateway = DischargeGateway::new(shared_key, location.to_string());
        gateway.add_evaluator(Box::new(AllOfEvaluator {
            evaluators: vec![
                Box::new(AllowlistEvaluator { allowed }),
                Box::new(PaymentEvaluator { min_amount: 10 }),
            ],
        }));

        let mac = setup_3p_macaroon(&root_key, &shared_key, location);
        let ticket = extract_ticket(&mac);

        // Alice with payment passes.
        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: Some("alice".into()),
            proof: None,
            payment: Some(10),
            metadata: HashMap::new(),
        };
        assert!(gateway.process_request(&request).is_ok());

        gateway.reset_issued();

        // Alice without payment fails.
        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: Some("alice".into()),
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };
        assert!(gateway.process_request(&request).is_err());

        gateway.reset_issued();

        // Bob with payment fails (not in allowlist).
        let request = DischargeRequest {
            ticket,
            client_id: Some("bob".into()),
            proof: None,
            payment: Some(100),
            metadata: HashMap::new(),
        };
        assert!(gateway.process_request(&request).is_err());
    }

    #[test]
    fn test_composite_any_of() {
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();
        let location = "https://gateway.dev";

        let mut allowed = HashSet::new();
        allowed.insert("vip".to_string());

        let mut gateway = DischargeGateway::new(shared_key, location.to_string());
        gateway.add_evaluator(Box::new(AnyOfEvaluator {
            evaluators: vec![
                Box::new(AllowlistEvaluator { allowed }),
                Box::new(PaymentEvaluator { min_amount: 100 }),
            ],
        }));

        let mac = setup_3p_macaroon(&root_key, &shared_key, location);
        let ticket = extract_ticket(&mac);

        // VIP passes without payment.
        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: Some("vip".into()),
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };
        assert!(gateway.process_request(&request).is_ok());

        gateway.reset_issued();

        // Non-VIP with payment passes.
        let request = DischargeRequest {
            ticket: ticket.clone(),
            client_id: Some("normie".into()),
            proof: None,
            payment: Some(200),
            metadata: HashMap::new(),
        };
        assert!(gateway.process_request(&request).is_ok());

        gateway.reset_issued();

        // Non-VIP without payment fails.
        let request = DischargeRequest {
            ticket,
            client_id: Some("normie".into()),
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };
        assert!(gateway.process_request(&request).is_err());
    }

    #[test]
    fn test_wrong_shared_key_rejects() {
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();
        let wrong_key = crypto::random_key();
        let location = "https://gateway.dev";

        // Gateway uses a DIFFERENT key than what the macaroon was created with.
        let mut gateway = DischargeGateway::new(wrong_key, location.to_string());
        gateway.add_evaluator(Box::new(AlwaysAllow));

        let mac = setup_3p_macaroon(&root_key, &shared_key, location);
        let ticket = extract_ticket(&mac);

        let request = DischargeRequest {
            ticket,
            client_id: None,
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };

        let resp = gateway.process_request(&request);
        assert!(resp.is_err());
        assert!(resp.unwrap_err().condition.contains("ticket_decryption"));
    }

    #[test]
    fn test_issued_count() {
        let shared_key = crypto::random_key();
        let location = "https://gateway.dev";

        let mut gateway = DischargeGateway::new(shared_key, location.to_string());
        gateway.add_evaluator(Box::new(AlwaysAllow));

        assert_eq!(gateway.issued_count(), 0);

        for _ in 0..3 {
            let root_key = crypto::random_key();
            let mac = setup_3p_macaroon(&root_key, &shared_key, location);
            let ticket = extract_ticket(&mac);
            let request = DischargeRequest {
                ticket,
                client_id: None,
                proof: None,
                payment: None,
                metadata: HashMap::new(),
            };
            gateway.process_request(&request).unwrap();
        }

        assert_eq!(gateway.issued_count(), 3);
    }

    #[test]
    fn test_full_end_to_end_flow() {
        // Simulates the complete flow:
        // 1. Issuer creates token with 3P caveat
        // 2. Client extracts ticket, sends to gateway
        // 3. Gateway issues discharge
        // 4. Client binds discharge to root token
        // 5. Verifier checks everything

        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();
        let location = "https://gateway.dregg.dev";

        // 1. Issuer creates token with 3P caveat.
        let mut token = Macaroon::new(
            &root_key,
            b"service-token".to_vec(),
            "https://service.dev".into(),
        );
        token
            .add_third_party(location, &shared_key, CaveatSet::new())
            .unwrap();

        // 2. Gateway setup.
        let mut gateway = DischargeGateway::new(shared_key, location.to_string());
        gateway.add_evaluator(Box::new(AlwaysAllow));

        // 3. Client extracts ticket and requests discharge.
        let ticket = extract_ticket(&token);
        let request = DischargeRequest {
            ticket,
            client_id: Some("test-client".into()),
            proof: None,
            payment: None,
            metadata: HashMap::new(),
        };
        let response = gateway.process_request(&request).unwrap();

        // 4. Client decodes discharge and binds to root.
        let mut discharge = Macaroon::decode(&response.discharge).unwrap();
        token.bind_discharge(&mut discharge);

        // 5. Verifier checks.
        let result = token.verify(&root_key, &[discharge]);
        assert!(
            result.is_ok(),
            "full flow verification failed: {:?}",
            result.err()
        );
    }
}
