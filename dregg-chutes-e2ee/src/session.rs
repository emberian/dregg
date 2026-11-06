//! **Attested-session caching** — the thing that makes attested inference usable per-turn.
//!
//! The live cold path measured ~12.5s: resolve model → chute, discover instances, fetch the TDX
//! evidence with a fresh nonce, pull DCAP collateral, run the full quote verification. Paying
//! that on every narration turn is not a narrator, it is a stall.
//!
//! It is also unnecessary, and the reason is a property of the protocol rather than an
//! optimisation we are hoping holds: an instance's `e2e_pubkey` is **per-instance-lifetime**, and
//! the attestation binds `SHA-256(nonce ‖ e2e_pubkey)` into the quote's `report_data`. So one
//! successful verification establishes, for that instance, "this ML-KEM public key belongs to an
//! enclave whose measurements match the pinned registry". That fact does not decay per request —
//! it decays when the instance goes away or when we choose to stop trusting a stale check.
//!
//! So we cache exactly that fact, and the per-request work drops to what it should be: pick the
//! cached attested instance, take a fresh single-use invocation nonce, ML-KEM-encapsulate,
//! ChaCha20-Poly1305 the body. Microseconds.
//!
//! ## What invalidates a cached session
//!
//! 1. **TTL** — a configurable ceiling on how stale a verification may be (default
//!    [`DEFAULT_TTL_SECS`] = 30 min). This is a policy knob, not a protocol requirement: it bounds
//!    how long we would keep trusting an instance whose TCB posture changed under us.
//! 2. **The instance disappears** from discovery → re-attest (a different instance means a
//!    different key, which MUST be verified before it is encrypted to).
//! 3. **An invocation error** → the caller invalidates, so the next call re-attests rather than
//!    hammering an instance that is failing.
//!
//! Invocation nonces are handled SEPARATELY and deliberately: they are single-use and short-lived
//! (~55s), so exhausting them refetches nonces from discovery WITHOUT re-attesting. Re-attesting
//! on nonce exhaustion would silently restore the 12.5s per-turn cost.
//!
//! ## Fail-closed
//!
//! [`SessionCache::acquire`] returns `Err` when attestation fails and inserts NOTHING. There is no
//! path in this module that yields an `e2e_pubkey` which did not pass [`crate::attest::attest_chute`].

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::attest::{attest_chute, AttestationRecord, VerifierConfig};
use crate::client::http_client_with_timeout;
use crate::discovery::{discover, resolve_chute_id};
use crate::error::ClientError;

/// Default attestation TTL: 30 minutes.
pub const DEFAULT_TTL_SECS: u64 = 1800;

/// A monotonic seconds source. Abstracted so TTL expiry is testable without sleeping.
pub trait Clock: Send + Sync {
    /// Monotonic seconds since an arbitrary fixed origin.
    fn now_secs(&self) -> u64;
}

/// The real clock — `Instant`-based, so it is immune to wall-clock jumps.
pub struct MonotonicClock {
    base: Instant,
}

impl MonotonicClock {
    /// A clock whose origin is now.
    pub fn new() -> MonotonicClock {
        MonotonicClock {
            base: Instant::now(),
        }
    }
}

impl Default for MonotonicClock {
    fn default() -> Self {
        MonotonicClock::new()
    }
}

impl Clock for MonotonicClock {
    fn now_secs(&self) -> u64 {
        self.base.elapsed().as_secs()
    }
}

/// A VERIFIED instance, pinned for reuse. Holding one of these is the claim "this `e2e_pubkey`
/// was bound into a DCAP-verified TDX quote from an enclave matching the pinned measurements" —
/// the only way to construct one is through a successful attestation.
#[derive(Debug, Clone)]
pub struct AttestedSession {
    /// The chute (model) this instance serves.
    pub chute_id: String,
    /// The enclave instance, pinned as `X-Instance-Id` on every invocation.
    pub instance_id: String,
    /// The ATTESTED ML-KEM-768 public key (base64) — the only key we encrypt to.
    pub e2e_pubkey_b64: String,
    /// The receipt: measurement, TCB status, and the raw quote bytes that were verified.
    pub record: AttestationRecord,
}

/// Establishes and refreshes attested sessions. The real implementation ([`ChutesAttestor`]) talks
/// to Chutes and runs the DCAP verifier; tests substitute a fake so the cache's
/// attest-once/reuse/expire/invalidate behaviour is provable offline.
pub trait Attestor: Send + Sync {
    /// Resolve `model` → chute, discover, **attest (fail-closed)**, and return the pinned instance
    /// plus the invocation nonces discovery handed back for it.
    fn establish(&self, model: &str) -> Result<(AttestedSession, Vec<String>), ClientError>;

    /// Refetch invocation nonces for an ALREADY-ATTESTED instance — no re-attestation.
    /// `Ok(None)` means the instance is gone from discovery, so the caller must re-attest.
    fn refresh_nonces(
        &self,
        chute_id: &str,
        instance_id: &str,
    ) -> Result<Option<Vec<String>>, ClientError>;
}

/// A usable attested instance plus ONE single-use invocation nonce.
#[derive(Debug, Clone)]
pub struct Lease {
    /// The verified instance to encrypt to.
    pub session: Arc<AttestedSession>,
    /// A single-use invocation token, consumed from the cache (never handed out twice).
    pub nonce: String,
    /// Whether this lease required a fresh ATTESTATION (the expensive path) — `false` means it
    /// was served from cache. Tests and metrics read this to prove the cold path is not re-run.
    pub attested: bool,
}

struct Entry {
    session: Arc<AttestedSession>,
    attested_at: u64,
    nonces: Vec<String>,
}

/// A per-model cache of attested instances.
///
/// The lock is held across the (rare) attestation network call on purpose: concurrent narration
/// turns that arrive during a cold start queue behind ONE attestation instead of stampeding the
/// evidence endpoint with N quote verifications.
pub struct SessionCache {
    ttl_secs: u64,
    clock: Arc<dyn Clock>,
    entries: Mutex<HashMap<String, Entry>>,
}

impl SessionCache {
    /// A cache with an explicit attestation TTL in seconds (0 = re-attest every call).
    pub fn new(ttl_secs: u64) -> SessionCache {
        SessionCache::with_clock(ttl_secs, Arc::new(MonotonicClock::new()))
    }

    /// A cache with an injected clock — the test seam for TTL expiry.
    pub fn with_clock(ttl_secs: u64, clock: Arc<dyn Clock>) -> SessionCache {
        SessionCache {
            ttl_secs,
            clock,
            entries: Mutex::new(HashMap::new()),
        }
    }

    /// The configured attestation TTL, in seconds.
    pub fn ttl_secs(&self) -> u64 {
        self.ttl_secs
    }

    /// Get a usable (attested instance, fresh invocation nonce) for `model`, attesting ONLY when
    /// there is no live cached verification for it.
    ///
    /// Order of preference, cheapest first:
    /// 1. cached session, still within TTL, with an unused nonce — pure memory;
    /// 2. cached session within TTL whose nonces ran out — refetch nonces, **no re-attestation**;
    /// 3. otherwise (cold, expired, or the instance vanished) — full attestation.
    ///
    /// Fail-closed: a failed attestation returns `Err` and leaves NOTHING cached.
    pub fn acquire(&self, model: &str, attestor: &dyn Attestor) -> Result<Lease, ClientError> {
        let mut entries = self.entries.lock().unwrap_or_else(|e| e.into_inner());
        let now = self.clock.now_secs();

        if let Some(entry) = entries.get_mut(model) {
            if now.saturating_sub(entry.attested_at) < self.ttl_secs {
                // (1) still verified, still has a nonce.
                if let Some(nonce) = entry.nonces.pop() {
                    return Ok(Lease {
                        session: entry.session.clone(),
                        nonce,
                        attested: false,
                    });
                }
                // (2) nonces exhausted — refetch them for the SAME attested instance. This does
                //     NOT re-verify anything: the instance and its bound pubkey are unchanged.
                match attestor.refresh_nonces(&entry.session.chute_id, &entry.session.instance_id) {
                    Ok(Some(fresh)) if !fresh.is_empty() => {
                        entry.nonces = fresh;
                        let nonce = entry.nonces.pop().expect("non-empty");
                        return Ok(Lease {
                            session: entry.session.clone(),
                            nonce,
                            attested: false,
                        });
                    }
                    // Instance gone, no nonces left for it, or discovery failed → the cached
                    // verification is no longer actionable. Drop it and re-attest below.
                    _ => {
                        entries.remove(model);
                    }
                }
            } else {
                // TTL expired — a stale verification is not reused.
                entries.remove(model);
            }
        }

        // (3) COLD PATH: full attestation. `?` here is the fail-closed gate — on refusal we
        //     return before anything is cached and before any inference is attempted.
        let (session, nonces) = attestor.establish(model)?;
        let mut entry = Entry {
            session: Arc::new(session),
            attested_at: now,
            nonces,
        };
        let nonce = entry.nonces.pop().ok_or(ClientError::NoUsableInstance)?;
        let session = entry.session.clone();
        entries.insert(model.to_string(), entry);
        Ok(Lease {
            session,
            nonce,
            attested: true,
        })
    }

    /// Force a FRESH invocation nonce for `model` after one was rejected as stale, reusing the
    /// cached attestation when the instance is still there (no re-verification), and re-attesting
    /// only if it is gone.
    pub fn refresh(&self, model: &str, attestor: &dyn Attestor) -> Result<Lease, ClientError> {
        {
            let mut entries = self.entries.lock().unwrap_or_else(|e| e.into_inner());
            if let Some(entry) = entries.get_mut(model) {
                let (chute_id, instance_id) = (
                    entry.session.chute_id.clone(),
                    entry.session.instance_id.clone(),
                );
                match attestor.refresh_nonces(&chute_id, &instance_id) {
                    Ok(Some(fresh)) if !fresh.is_empty() => {
                        entry.nonces = fresh;
                        let nonce = entry.nonces.pop().expect("non-empty");
                        return Ok(Lease {
                            session: entry.session.clone(),
                            nonce,
                            attested: false,
                        });
                    }
                    _ => {
                        entries.remove(model);
                    }
                }
            }
        }
        self.acquire(model, attestor)
    }

    /// Drop any cached verification for `model` — the next [`SessionCache::acquire`] re-attests.
    pub fn invalidate(&self, model: &str) {
        let mut entries = self.entries.lock().unwrap_or_else(|e| e.into_inner());
        entries.remove(model);
    }

    /// The cached session for `model`, if one is live (ignoring nonce availability). For metrics
    /// and receipts; it does NOT extend or refresh anything.
    pub fn cached(&self, model: &str) -> Option<Arc<AttestedSession>> {
        let entries = self.entries.lock().unwrap_or_else(|e| e.into_inner());
        let entry = entries.get(model)?;
        if self.clock.now_secs().saturating_sub(entry.attested_at) < self.ttl_secs {
            Some(entry.session.clone())
        } else {
            None
        }
    }
}

/// The REAL attestor: Chutes discovery + the fail-closed DCAP attestation gate.
pub struct ChutesAttestor {
    http: reqwest::blocking::Client,
    cfg: VerifierConfig,
    cpk: String,
}

impl ChutesAttestor {
    /// An attestor over `cfg` authenticating with the Chutes API key `cpk`.
    pub fn new(cfg: VerifierConfig, cpk: impl Into<String>) -> Result<ChutesAttestor, ClientError> {
        ChutesAttestor::with_timeout(cfg, cpk, crate::client::DEFAULT_TIMEOUT_SECS)
    }

    /// An attestor with an explicit HTTP timeout (seconds).
    pub fn with_timeout(
        cfg: VerifierConfig,
        cpk: impl Into<String>,
        timeout_secs: u64,
    ) -> Result<ChutesAttestor, ClientError> {
        Ok(ChutesAttestor {
            http: http_client_with_timeout(timeout_secs)?,
            cfg,
            cpk: cpk.into(),
        })
    }

    /// The verifier configuration this attestor enforces.
    pub fn config(&self) -> &VerifierConfig {
        &self.cfg
    }

    /// The API key, for the invoker that shares this attestor's configuration.
    pub(crate) fn cpk(&self) -> &str {
        &self.cpk
    }

    /// The shared blocking HTTP client.
    pub(crate) fn http(&self) -> &reqwest::blocking::Client {
        &self.http
    }
}

impl Attestor for ChutesAttestor {
    fn establish(&self, model: &str) -> Result<(AttestedSession, Vec<String>), ClientError> {
        let chute_id = resolve_chute_id(&self.http, &self.cfg.models_base, model, &self.cpk)?;
        let discovered = discover(&self.http, &self.cfg.api_base, &chute_id, &self.cpk)?;
        // FAIL-CLOSED: no attested instance → Err, and no session is ever produced.
        let attested = attest_chute(&self.http, &self.cfg, &chute_id, &self.cpk, &discovered)?;

        for a in &attested {
            let Some(info) = discovered.by_id(&a.instance_id) else {
                continue;
            };
            if info.nonces.is_empty() {
                continue;
            }
            return Ok((
                AttestedSession {
                    chute_id: chute_id.clone(),
                    instance_id: a.instance_id.clone(),
                    e2e_pubkey_b64: a.e2e_pubkey_b64.clone(),
                    record: AttestationRecord::from(a),
                },
                info.nonces.clone(),
            ));
        }
        Err(ClientError::NoUsableInstance)
    }

    fn refresh_nonces(
        &self,
        chute_id: &str,
        instance_id: &str,
    ) -> Result<Option<Vec<String>>, ClientError> {
        let discovered = discover(&self.http, &self.cfg.api_base, chute_id, &self.cpk)?;
        Ok(discovered.by_id(instance_id).map(|i| i.nonces.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    /// A clock the test drives by hand.
    pub struct TestClock(AtomicU64);
    impl TestClock {
        fn new() -> TestClock {
            TestClock(AtomicU64::new(0))
        }
        fn advance(&self, secs: u64) {
            self.0.fetch_add(secs, Ordering::SeqCst);
        }
    }
    impl Clock for TestClock {
        fn now_secs(&self) -> u64 {
            self.0.load(Ordering::SeqCst)
        }
    }

    /// A fake attestor that COUNTS how often the expensive path runs.
    struct FakeAttestor {
        establishes: AtomicU64,
        refreshes: AtomicU64,
        /// Nonces handed back per establish/refresh.
        nonces_per_batch: usize,
        /// When true, `establish` refuses (models an attestation refusal).
        refuse: bool,
        /// When true, `refresh_nonces` reports the instance is gone.
        instance_gone: bool,
    }

    impl FakeAttestor {
        fn new(nonces_per_batch: usize) -> FakeAttestor {
            FakeAttestor {
                establishes: AtomicU64::new(0),
                refreshes: AtomicU64::new(0),
                nonces_per_batch,
                refuse: false,
                instance_gone: false,
            }
        }
        fn refusing() -> FakeAttestor {
            FakeAttestor {
                refuse: true,
                ..FakeAttestor::new(4)
            }
        }
        fn establishes(&self) -> u64 {
            self.establishes.load(Ordering::SeqCst)
        }
        fn refreshes(&self) -> u64 {
            self.refreshes.load(Ordering::SeqCst)
        }
        fn batch(&self, tag: &str) -> Vec<String> {
            (0..self.nonces_per_batch)
                .map(|i| format!("{tag}-nonce-{i}"))
                .collect()
        }
    }

    impl Attestor for FakeAttestor {
        fn establish(&self, model: &str) -> Result<(AttestedSession, Vec<String>), ClientError> {
            let n = self.establishes.fetch_add(1, Ordering::SeqCst);
            if self.refuse {
                return Err(ClientError::AttestationRefused(
                    "fake: no instance attested".into(),
                ));
            }
            Ok((
                AttestedSession {
                    chute_id: format!("chute-for-{model}"),
                    instance_id: format!("instance-{n}"),
                    e2e_pubkey_b64: format!("pubkey-{n}"),
                    record: AttestationRecord {
                        instance_id: format!("instance-{n}"),
                        measurement: [0xAB; 32],
                        tcb_status: "UpToDate".to_string(),
                        quote_bytes: vec![n as u8; 16],
                        nonce_hex: format!("{n:064x}"),
                        e2e_pubkey_b64: format!("pubkey-{n}"),
                        gpus: vec![],
                    },
                },
                self.batch(&format!("est{n}")),
            ))
        }

        fn refresh_nonces(
            &self,
            _chute_id: &str,
            _instance_id: &str,
        ) -> Result<Option<Vec<String>>, ClientError> {
            let n = self.refreshes.fetch_add(1, Ordering::SeqCst);
            if self.instance_gone {
                return Ok(None);
            }
            Ok(Some(self.batch(&format!("ref{n}"))))
        }
    }

    const MODEL: &str = "Qwen/Qwen3-32B-TEE";

    /// THE PERF CLAIM: the first call attests, subsequent calls do NOT.
    #[test]
    fn first_call_attests_then_the_cache_serves_without_re_attesting() {
        let cache = SessionCache::new(DEFAULT_TTL_SECS);
        let att = FakeAttestor::new(8);

        let first = cache.acquire(MODEL, &att).unwrap();
        assert!(first.attested, "cold start must attest");
        assert_eq!(att.establishes(), 1);

        for _ in 0..7 {
            let lease = cache.acquire(MODEL, &att).unwrap();
            assert!(!lease.attested, "a cached session must not re-attest");
            assert_eq!(lease.session.instance_id, first.session.instance_id);
        }
        assert_eq!(att.establishes(), 1, "exactly ONE attestation for 8 calls");
        assert_eq!(att.refreshes(), 0, "8 nonces covered 8 calls");
    }

    /// Every lease gets a DISTINCT single-use invocation nonce — the cache never replays one.
    #[test]
    fn nonces_are_never_handed_out_twice() {
        let cache = SessionCache::new(DEFAULT_TTL_SECS);
        let att = FakeAttestor::new(3);
        let mut seen = Vec::new();
        for _ in 0..9 {
            seen.push(cache.acquire(MODEL, &att).unwrap().nonce);
        }
        let mut sorted = seen.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            seen.len(),
            "duplicate nonce handed out: {seen:?}"
        );
    }

    /// Exhausting the nonce pool refetches NONCES — it must NOT trigger a re-attestation.
    #[test]
    fn nonce_exhaustion_refetches_nonces_without_re_attesting() {
        let cache = SessionCache::new(DEFAULT_TTL_SECS);
        let att = FakeAttestor::new(2);

        for _ in 0..6 {
            cache.acquire(MODEL, &att).unwrap();
        }
        assert_eq!(
            att.establishes(),
            1,
            "nonce exhaustion is NOT a re-attestation"
        );
        assert_eq!(att.refreshes(), 2, "two refills covered calls 3-6");
    }

    /// TTL expiry re-attests.
    #[test]
    fn ttl_expiry_re_attests() {
        let clock = Arc::new(TestClock::new());
        let cache = SessionCache::with_clock(60, clock.clone());
        let att = FakeAttestor::new(64);

        let a = cache.acquire(MODEL, &att).unwrap();
        assert!(a.attested);

        clock.advance(59);
        let b = cache.acquire(MODEL, &att).unwrap();
        assert!(!b.attested, "still inside the TTL");
        assert_eq!(att.establishes(), 1);

        clock.advance(1); // now exactly at the TTL boundary — expired.
        let c = cache.acquire(MODEL, &att).unwrap();
        assert!(c.attested, "past the TTL the verification is re-run");
        assert_eq!(att.establishes(), 2);
        assert_ne!(c.session.instance_id, a.session.instance_id);
    }

    /// A TTL of zero means "never reuse a verification".
    #[test]
    fn zero_ttl_attests_every_call() {
        let cache = SessionCache::new(0);
        let att = FakeAttestor::new(8);
        for _ in 0..3 {
            assert!(cache.acquire(MODEL, &att).unwrap().attested);
        }
        assert_eq!(att.establishes(), 3);
    }

    /// Explicit invalidation (what the backend does on an invocation error) re-attests next call.
    #[test]
    fn invalidation_forces_re_attestation() {
        let cache = SessionCache::new(DEFAULT_TTL_SECS);
        let att = FakeAttestor::new(8);

        cache.acquire(MODEL, &att).unwrap();
        assert!(!cache.acquire(MODEL, &att).unwrap().attested);
        assert_eq!(att.establishes(), 1);

        cache.invalidate(MODEL);
        assert!(cache.acquire(MODEL, &att).unwrap().attested);
        assert_eq!(att.establishes(), 2);
    }

    /// If the cached instance vanishes from discovery, we do NOT keep encrypting to its key —
    /// the cache drops it and attests a fresh instance.
    #[test]
    fn vanished_instance_is_re_attested_not_reused() {
        let cache = SessionCache::new(DEFAULT_TTL_SECS);
        let mut att = FakeAttestor::new(1);

        let first = cache.acquire(MODEL, &att).unwrap();
        assert!(first.attested);

        att.instance_gone = true;
        let second = cache.acquire(MODEL, &att).unwrap();
        assert!(second.attested, "a vanished instance forces re-attestation");
        assert_ne!(second.session.instance_id, first.session.instance_id);
        assert_eq!(att.establishes(), 2);
    }

    /// FAIL-CLOSED: a refused attestation yields `Err` and caches NOTHING — a later call cannot
    /// pick up a half-established session.
    #[test]
    fn refused_attestation_errors_and_caches_nothing() {
        let cache = SessionCache::new(DEFAULT_TTL_SECS);
        let att = FakeAttestor::refusing();

        let err = cache.acquire(MODEL, &att).unwrap_err();
        assert!(
            matches!(err, ClientError::AttestationRefused(_)),
            "got {err:?}"
        );
        assert!(cache.cached(MODEL).is_none(), "nothing may be cached");
        assert!(cache.acquire(MODEL, &att).is_err());
        assert_eq!(att.establishes(), 2, "each call re-tries, none succeeds");
    }

    /// `refresh` (the stale-invocation-nonce path) reuses the cached attestation.
    #[test]
    fn refresh_after_a_stale_nonce_does_not_re_attest() {
        let cache = SessionCache::new(DEFAULT_TTL_SECS);
        let att = FakeAttestor::new(4);

        let a = cache.acquire(MODEL, &att).unwrap();
        let b = cache.refresh(MODEL, &att).unwrap();
        assert!(!b.attested);
        assert_eq!(b.session.instance_id, a.session.instance_id);
        assert_eq!(att.establishes(), 1);
        assert_eq!(att.refreshes(), 1);
        assert_ne!(a.nonce, b.nonce);
    }

    /// Distinct models keep distinct sessions (one attestation each, no cross-talk).
    #[test]
    fn sessions_are_per_model() {
        let cache = SessionCache::new(DEFAULT_TTL_SECS);
        let att = FakeAttestor::new(8);
        let a = cache.acquire("model-a-TEE", &att).unwrap();
        let b = cache.acquire("model-b-TEE", &att).unwrap();
        assert_eq!(att.establishes(), 2);
        assert_ne!(a.session.chute_id, b.session.chute_id);
        assert!(!cache.acquire("model-a-TEE", &att).unwrap().attested);
        assert_eq!(att.establishes(), 2);
    }
}
