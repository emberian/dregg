//! **The attested narrator backend** — `dregg_narrator::ConverseBackend` served by a
//! DCAP-verified TDX enclave.
//!
//! ## Where this lives, and why the dependency points this way
//!
//! `dregg-chutes-e2ee` → `dregg-narrator`, never the reverse. `dregg-narrator` is the LIGHT crate
//! everything that narrates depends on (the dungeon service, the Discord bot, hermes, the web
//! surface); this crate pulls `dregg-tee-verify` → `dcap-qvl` → PQClean ML-KEM C. Putting the
//! backend here means the attestation stack reaches only the processes that actually attest, and
//! `cargo build -p dregg-narrator` is unchanged. There is no cycle: narrator does not know this
//! crate exists — it only exposes the trait, the request/response types, and (deliberately) the
//! `build_chat_body` / `parse_chat_response` mapping this backend REUSES rather than mirrors.
//!
//! ## What is attested, and what is not
//!
//! Per turn, the request body is ML-KEM-768-encapsulated to an `e2e_pubkey` that was bound into a
//! TDX quote we verified against the pinned Chutes measurement registry, and the reply is
//! decrypted with an ephemeral key only this process holds. What that buys is confidentiality and
//! code identity of the SERVING enclave — it is not a proof about the model weights or the
//! sampled tokens. [`dregg_narrator::AttestationSummary`] on the response says exactly which
//! enclave, under which measurement and TCB status; the full quote — plus the nonce and instance
//! key that make its `report_data` binding recomputable by anyone — stays retrievable through
//! [`dregg_narrator::AttestationEvidence::attestation_for`], keyed by the summary's own quote
//! digest, for a receipt lane to archive. ([`ChutesTeeBackend::last_attestation`] is the older,
//! unkeyed read; it cannot say WHICH call a record belongs to, so an archive uses the keyed one.)
//!
//! ## Fail-closed
//!
//! If attestation is configured and does not pass, [`ChutesTeeBackend::converse`] returns `Err`
//! and **no inference is attempted** — there is no fall-through to the plain Chutes endpoint.
//! `DREGG_NARRATOR=chutes-tee` likewise resolves in narrator to
//! `HostedProvider::ExternalAttested`, which contributes NO built-in backend, so a missing
//! composition yields no narration rather than unattested narration.

use std::collections::VecDeque;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use serde_json::Value;
use sha2::{Digest, Sha256};

use dregg_narrator::{
    build_chat_body, parse_chat_response, AttestationEvidence, AttestationQuote,
    AttestationSummary, ConverseBackend, ConverseRequest, ConverseResponse, Narrator,
};

use crate::attest::{AttestationRecord, CollateralSource, VerifierConfig};
use crate::client::{invoke_encrypted, InvokeError};
use crate::discovery::{model_pricing, ProviderPricing, DEFAULT_API_BASE, DEFAULT_MODELS_BASE};
use crate::error::ClientError;
use crate::session::{AttestedSession, Attestor, ChutesAttestor, SessionCache, DEFAULT_TTL_SECS};

/// The default sampling temperature (matches the plain OpenAI-compatible narrator backend).
pub const DEFAULT_TEMPERATURE: f32 = 0.7;
/// The default Chutes TEE measurements registry.
pub const DEFAULT_MEASUREMENTS_URL: &str = "https://api.chutes.ai/servers/tee/measurements";
/// The default PCCS base used to fetch DCAP collateral (only with `--features collateral-fetch`).
pub const DEFAULT_PCCS_URL: &str = "https://pccs.phala.network";
/// The default key file consulted when no key env var is set.
pub const DEFAULT_KEY_FILE: &str = ".chutes-key";

/// Runs ONE encrypted invocation against an already-attested session. Abstracted so the backend's
/// fail-closed ordering is provable offline with an invoker that panics if it is ever reached.
pub trait Invoker: Send + Sync {
    /// Encrypt `request` to `session.e2e_pubkey_b64`, POST it pinned to `session.instance_id`,
    /// and return the decrypted OpenAI response envelope.
    fn invoke(
        &self,
        session: &AttestedSession,
        invocation_nonce: &str,
        request: &Value,
    ) -> Result<Value, InvokeError>;
}

/// The real invoker — [`invoke_encrypted`] over a shared blocking HTTP client.
pub struct ChutesInvoker {
    http: reqwest::blocking::Client,
    cfg: VerifierConfig,
    cpk: String,
}

impl ChutesInvoker {
    /// An invoker sharing an attestor's configuration, key and HTTP client.
    pub fn from_attestor(attestor: &ChutesAttestor) -> ChutesInvoker {
        ChutesInvoker {
            http: attestor.http().clone(),
            cfg: attestor.config().clone(),
            cpk: attestor.cpk().to_string(),
        }
    }
}

impl Invoker for ChutesInvoker {
    fn invoke(
        &self,
        session: &AttestedSession,
        invocation_nonce: &str,
        request: &Value,
    ) -> Result<Value, InvokeError> {
        invoke_encrypted(
            &self.http,
            &self.cfg,
            &session.chute_id,
            &session.instance_id,
            // The ONLY key we encrypt to is the one the cached session attested.
            &session.e2e_pubkey_b64,
            invocation_nonce,
            request,
            &self.cpk,
        )
    }
}

/// How many distinct attestation records the backend keeps retrievable by quote digest.
///
/// A verification is reused for a whole TTL window and is per-model, so the live working set is
/// "one record per configured model", i.e. one. The window exists so a receipt lane that reads
/// the evidence one turn after the response still finds it, and so a model switch or a
/// re-attestation mid-archive does not evict the record the caller is holding a summary for.
/// It is a BOUND, not a history: an archive that wants the bytes forever must persist them.
const RETAINED_ATTESTATIONS: usize = 8;

/// A [`ConverseBackend`] whose inference runs inside a DCAP-verified Intel TDX enclave.
pub struct ChutesTeeBackend {
    attestor: Arc<dyn Attestor>,
    invoker: Arc<dyn Invoker>,
    cache: SessionCache,
    temperature: f32,
    last: Mutex<Option<AttestationRecord>>,
    /// The bounded, DIGEST-KEYED retention behind [`AttestationEvidence`]. Keyed by digest
    /// because `last` cannot answer "the evidence for THIS summary" — under two interleaved
    /// models it answers "the evidence for whichever call finished most recently", and an
    /// archive built on that would file a real quote under the wrong turn.
    retained: Mutex<VecDeque<([u8; 32], AttestationRecord)>>,
}

impl ChutesTeeBackend {
    /// A backend over explicit parts — the seam tests use to substitute fakes.
    pub fn new(
        attestor: Arc<dyn Attestor>,
        invoker: Arc<dyn Invoker>,
        cache: SessionCache,
        temperature: f32,
    ) -> ChutesTeeBackend {
        ChutesTeeBackend {
            attestor,
            invoker,
            cache,
            temperature,
            last: Mutex::new(None),
            retained: Mutex::new(VecDeque::new()),
        }
    }

    /// A backend over a real [`ChutesAttestor`] with the given attestation TTL and temperature.
    pub fn over_chutes(
        attestor: ChutesAttestor,
        ttl_secs: u64,
        temperature: f32,
    ) -> ChutesTeeBackend {
        let invoker = Arc::new(ChutesInvoker::from_attestor(&attestor));
        ChutesTeeBackend::new(
            Arc::new(attestor),
            invoker,
            SessionCache::new(ttl_secs),
            temperature,
        )
    }

    /// Build from the environment. See [`TeeNarratorEnv`] for the full surface. Fails (never
    /// silently degrades) when the attestation inputs are missing.
    pub fn from_env() -> Result<ChutesTeeBackend, String> {
        TeeNarratorEnv::from_env()?.build_backend()
    }

    /// The FULL attestation record of the most recent successful call — including the raw quote
    /// bytes a receipt lane commits. `None` before the first success.
    pub fn last_attestation(&self) -> Option<AttestationRecord> {
        self.last.lock().unwrap_or_else(|e| e.into_inner()).clone()
    }

    /// The attestation TTL this backend caches verifications for, in seconds.
    pub fn attestation_ttl_secs(&self) -> u64 {
        self.cache.ttl_secs()
    }

    /// The live cached session for `model`, if any (metrics/diagnostics; does not refresh).
    pub fn cached_session(&self, model: &str) -> Option<Arc<AttestedSession>> {
        self.cache.cached(model)
    }

    fn record_last(&self, record: &AttestationRecord) {
        *self.last.lock().unwrap_or_else(|e| e.into_inner()) = Some(record.clone());

        let digest = quote_digest(&record.quote_bytes);
        let mut retained = self.retained.lock().unwrap_or_else(|e| e.into_inner());
        // A cached verification is replayed on every turn of its TTL window, so the same digest
        // arrives over and over: re-inserting would evict the OTHER models' records for nothing.
        if retained.iter().any(|(d, _)| *d == digest) {
            return;
        }
        retained.push_back((digest, record.clone()));
        while retained.len() > RETAINED_ATTESTATIONS {
            retained.pop_front();
        }
    }

    /// Parse the decrypted OpenAI envelope and stamp it with the attestation that covered it.
    fn finish(
        &self,
        req: &ConverseRequest,
        value: Value,
        session: &AttestedSession,
    ) -> Result<ConverseResponse, String> {
        let mut resp = parse_chat_response(&value, req)?;
        resp.attestation = Some(summarize(&session.record));
        self.record_last(&session.record);
        Ok(resp)
    }
}

/// SHA-256 of a raw quote — the ONE definition of the handle that links an
/// [`AttestationSummary`] to the [`AttestationRecord`] behind it.
fn quote_digest(quote_bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(quote_bytes);
    let mut out = [0u8; 32];
    out.copy_from_slice(&hasher.finalize());
    out
}

/// Summarize an attestation record for the narrator response (light: digest, not the quote).
pub fn summarize(record: &AttestationRecord) -> AttestationSummary {
    AttestationSummary {
        instance_id: record.instance_id.clone(),
        measurement: record.measurement,
        tcb_status: record.tcb_status.clone(),
        quote_sha256: quote_digest(&record.quote_bytes),
        quote_len: record.quote_bytes.len(),
    }
}

impl AttestationEvidence for ChutesTeeBackend {
    /// The retained evidence whose quote hashes to `quote_sha256`.
    ///
    /// The digest is RE-DERIVED from the stored bytes on the way out, not read off the key, so a
    /// record can only be returned under the digest it actually has. A caller archiving this can
    /// therefore treat "the digest in my summary" and "the bytes I got" as the same object
    /// without trusting the map.
    fn attestation_for(&self, quote_sha256: &[u8; 32]) -> Option<AttestationQuote> {
        let retained = self.retained.lock().unwrap_or_else(|e| e.into_inner());
        let (_, record) = retained.iter().find(|(d, _)| d == quote_sha256)?;
        if quote_digest(&record.quote_bytes) != *quote_sha256 {
            return None;
        }
        Some(AttestationQuote {
            instance_id: record.instance_id.clone(),
            measurement: record.measurement,
            tcb_status: record.tcb_status.clone(),
            nonce_hex: record.nonce_hex.clone(),
            e2e_pubkey_b64: record.e2e_pubkey_b64.clone(),
            quote_bytes: record.quote_bytes.clone(),
        })
    }
}

impl ConverseBackend for ChutesTeeBackend {
    fn converse(&self, req: &ConverseRequest) -> Result<ConverseResponse, String> {
        // The SAME OpenAI mapping the plain narrator backend uses — this path differs in where the
        // bytes go, not in what they say.
        let body = build_chat_body(req, self.temperature);

        // ATTESTATION GATE, first and fail-closed: `?` here means an attestation failure returns
        // before `invoker.invoke` is ever reached, so no request body is built or sent.
        let lease = self
            .cache
            .acquire(&req.model, self.attestor.as_ref())
            .map_err(|e| format!("chutes-tee: attestation failed, NO inference attempted: {e}"))?;

        let value = match self.invoker.invoke(&lease.session, &lease.nonce, &body) {
            Ok(v) => v,
            Err(InvokeError::StaleNonce(_)) => {
                // A single-use invocation token expired. Take a fresh one on the SAME attested
                // instance — this is NOT a re-attestation — and retry exactly once.
                let retry = self
                    .cache
                    .refresh(&req.model, self.attestor.as_ref())
                    .map_err(|e| {
                        format!("chutes-tee: attestation failed on nonce refresh, NO inference attempted: {e}")
                    })?;
                match self.invoker.invoke(&retry.session, &retry.nonce, &body) {
                    Ok(v) => {
                        return self.finish(req, v, &retry.session);
                    }
                    Err(e) => {
                        self.cache.invalidate(&req.model);
                        return Err(format!(
                            "chutes-tee invoke (after nonce refresh): {}",
                            describe(e)
                        ));
                    }
                }
            }
            Err(e) => {
                // The instance errored — drop the cached verification so the next turn re-attests
                // rather than repeatedly encrypting to an instance that is failing.
                self.cache.invalidate(&req.model);
                return Err(format!("chutes-tee invoke: {}", describe(e)));
            }
        };

        self.finish(req, value, &lease.session)
    }
}

fn describe(e: InvokeError) -> String {
    ClientError::from(e).to_string()
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// Environment configuration
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The resolved environment configuration for the attested narrator.
///
/// | variable | meaning | default |
/// |---|---|---|
/// | `DREGG_NARRATOR=chutes-tee` | selects this backend | — |
/// | `DREGG_NARRATOR_MODEL` | the model id; must be a `-TEE` chute (e.g. `Qwen/Qwen3-32B-TEE`) | **required** |
/// | `CHUTES_API_KEY` | the `cpk_…` key | — |
/// | `CHUTES_API_KEY_FILE` | a file holding the key (trimmed) | `~/.chutes-key` |
/// | `CHUTES_MEASUREMENTS_JSON` | PINNED measurements registry file (preferred) | — |
/// | `CHUTES_MEASUREMENTS_URL` | registry URL, fetched at construction | [`DEFAULT_MEASUREMENTS_URL`] |
/// | `CHUTES_COLLATERAL_JSON` | pre-fetched DCAP `QuoteCollateralV3` JSON file | — |
/// | `CHUTES_PCCS_URL` | PCCS base to fetch collateral from (`collateral-fetch` feature) | [`DEFAULT_PCCS_URL`] |
/// | `CHUTES_ACCEPTED_STATUSES` | comma-separated accepted TCB statuses | `UpToDate` |
/// | `CHUTES_API_BASE` / `CHUTES_MODELS_BASE` | API endpoints | Chutes defaults |
/// | `DREGG_NARRATOR_ATTESTATION_TTL_SECS` | how long a verification is reused | `1800` (30 min) |
/// | `DREGG_NARRATOR_TEMPERATURE` | sampling temperature | `0.7` |
/// | `DREGG_NARRATOR_HTTP_TIMEOUT_SECS` | HTTP timeout | `120` |
/// | `DREGG_NARRATOR_REQUIRE_GPU_ATTESTATION` | `1` = every GPU must verify (NVIDIA chain, RIM goldens, OCSP) | off: CPU TD only, logged loudly per attestation |
///
/// PRICING: the model must also be priced, or the metered layer refuses it fail-closed. It no
/// longer has to be priced BY HAND: Chutes' catalog publishes a machine-readable per-model rate
/// (`GET {models_base}/v1/models` → `pricing.{prompt,completion}`, USD per 1,000,000 tokens) for
/// `-TEE` chutes as for any other, and [`TeeNarratorEnv::provider_pricing`] reads it. An operator
/// who sets BOTH `DREGG_NARRATOR_PRICE_INPUT_PER_1K` and `_OUTPUT_PER_1K` still wins — their
/// intent is not overridden — but the pinned rate is then labelled honestly as an override rather
/// than as a verified rate. Half a price pins nothing (the model stays unpriced and is refused) —
/// see `ModelRegistry::apply_price_override`.
pub struct TeeNarratorEnv {
    /// The `-TEE` model id.
    pub model: String,
    /// The Chutes API key.
    pub cpk: String,
    /// The attestation gate configuration (registry, collateral, accepted TCB, endpoints).
    pub verifier: VerifierConfig,
    /// Attestation TTL, seconds.
    pub ttl_secs: u64,
    /// Sampling temperature.
    pub temperature: f32,
    /// HTTP timeout, seconds.
    pub timeout_secs: u64,
}

impl TeeNarratorEnv {
    /// Resolve everything from the process environment, failing with an actionable message.
    pub fn from_env() -> Result<TeeNarratorEnv, String> {
        let model = non_empty_var("DREGG_NARRATOR_MODEL").ok_or_else(|| {
            "chutes-tee: DREGG_NARRATOR_MODEL is not set — name the attested model id \
             (a `-TEE` chute, e.g. Qwen/Qwen3-32B-TEE)"
                .to_string()
        })?;
        let cpk = resolve_api_key()?;
        let timeout_secs = parse_var("DREGG_NARRATOR_HTTP_TIMEOUT_SECS", 120u64);
        let measurements_json = load_measurements(timeout_secs)?;
        let collateral = load_collateral_source()?;

        let mut verifier = VerifierConfig::new(String::new(), measurements_json);
        verifier.collateral = collateral;
        if let Some(base) = non_empty_var("CHUTES_API_BASE") {
            verifier.api_base = base;
        } else {
            verifier.api_base = DEFAULT_API_BASE.to_string();
        }
        if let Some(base) = non_empty_var("CHUTES_MODELS_BASE") {
            verifier.models_base = base;
        } else {
            verifier.models_base = DEFAULT_MODELS_BASE.to_string();
        }
        // The GPU gate is OFF on the narrator path until a live run confirms chutes passes the
        // user nonce through to GPU evidence collection (if it does not, an enforced gate would
        // refuse every instance). Opt in explicitly; the default is announced, not silent.
        verifier.gpu.required = narrator_requires_gpu(
            non_empty_var("DREGG_NARRATOR_REQUIRE_GPU_ATTESTATION").as_deref(),
        );
        if !verifier.gpu.required {
            eprintln!(
                "WARNING chutes-tee narrator: GPU attestation is NOT enforced (CPU TD only). \
                 Set DREGG_NARRATOR_REQUIRE_GPU_ATTESTATION=1 to require every GPU to verify."
            );
        }
        if let Some(list) = non_empty_var("CHUTES_ACCEPTED_STATUSES") {
            verifier.accepted_statuses = parse_statuses(&list);
            if verifier.accepted_statuses.is_empty() {
                return Err(
                    "chutes-tee: CHUTES_ACCEPTED_STATUSES is set but empty — that would accept \
                     NO TCB status; unset it for the strict `UpToDate` default"
                        .to_string(),
                );
            }
        }

        Ok(TeeNarratorEnv {
            model,
            cpk,
            verifier,
            ttl_secs: parse_var("DREGG_NARRATOR_ATTESTATION_TTL_SECS", DEFAULT_TTL_SECS),
            temperature: parse_var("DREGG_NARRATOR_TEMPERATURE", DEFAULT_TEMPERATURE),
            timeout_secs,
        })
    }

    /// **The provider's own published rate for [`Self::model`]**, in USD per 1,000 tokens, read
    /// from the Chutes catalog (`GET {models_base}/v1/models`).
    ///
    /// Call this BEFORE [`Self::build_backend`] (which consumes `self`) so the metered layer can
    /// price the model from the provider's numbers rather than an operator's typed-in guess.
    ///
    /// `Ok(None)` = the catalog does not publish a usable rate pair for this model; the caller
    /// falls back to whatever it was already going to use. `Err` = the catalog was UNREACHABLE,
    /// which is deliberately distinguishable from "it says nothing" — the caller must not read a
    /// network failure as an absent price.
    pub fn provider_pricing(&self) -> Result<Option<ProviderPricing>, String> {
        let http = crate::client::http_client_with_timeout(self.timeout_secs)
            .map_err(|e| format!("chutes-tee: http client for the price catalog: {e}"))?;
        model_pricing(&http, &self.verifier.models_base, &self.model, &self.cpk)
            .map_err(|e| format!("chutes-tee: read the price catalog: {e}"))
    }

    /// Build the backend this configuration describes.
    pub fn build_backend(self) -> Result<ChutesTeeBackend, String> {
        let attestor = ChutesAttestor::with_timeout(self.verifier, self.cpk, self.timeout_secs)
            .map_err(|e| format!("chutes-tee: build attestor: {e}"))?;
        Ok(ChutesTeeBackend::over_chutes(
            attestor,
            self.ttl_secs,
            self.temperature,
        ))
    }
}

/// Compose a [`Narrator`] whose ONLY hosted backend is the attested one.
///
/// `Ok(None)` when `DREGG_NARRATOR` does not select the attested path (the caller keeps its usual
/// chain). `Err` when it IS selected but cannot be built — the whole point of this backend is that
/// a misconfigured attestation is a refusal, not a quiet downgrade to plain inference.
///
/// The composed narrator has NO scripted tier: a failed attested call surfaces as `Err` so the
/// caller decides, in the open, what to do about it.
pub fn attested_narrator_from_env() -> Result<Option<Narrator>, String> {
    if !attested_selected() {
        return Ok(None);
    }
    let env = TeeNarratorEnv::from_env()?;
    let model = env.model.clone();
    let backend = env.build_backend()?;
    let shared: Arc<dyn ConverseBackend + Send + Sync> = Arc::new(backend);
    Ok(Some(Narrator::with_hosted(vec![(shared, model)], false)))
}

/// Whether the narrator path enforces GPU attestation: only the exact value `1` opts in.
pub fn narrator_requires_gpu(var: Option<&str>) -> bool {
    var.map(str::trim) == Some("1")
}

/// Whether `DREGG_NARRATOR` selects the attested backend.
pub fn attested_selected() -> bool {
    matches!(
        dregg_narrator::hosted_provider(),
        dregg_narrator::HostedProvider::ExternalAttested
    )
}

/// Split a comma-separated accepted-TCB-status list, dropping blanks.
pub fn parse_statuses(list: &str) -> Vec<String> {
    list.split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect()
}

/// Read an API key from a file, trimming the trailing newline a `cat > ~/.chutes-key` leaves.
pub fn read_key_file(path: &Path) -> Result<String, String> {
    let raw = std::fs::read_to_string(path)
        .map_err(|e| format!("chutes-tee: read key file {}: {e}", path.display()))?;
    let key = raw.trim().to_string();
    if key.is_empty() {
        return Err(format!("chutes-tee: key file {} is empty", path.display()));
    }
    Ok(key)
}

/// `CHUTES_API_KEY` → `CHUTES_API_KEY_FILE` → `DREGG_NARRATOR_API_KEY` →
/// `DREGG_NARRATOR_API_KEY_FILE` → `~/.chutes-key`.
fn resolve_api_key() -> Result<String, String> {
    for var in ["CHUTES_API_KEY", "DREGG_NARRATOR_API_KEY"] {
        if let Some(k) = non_empty_var(var) {
            return Ok(k.trim().to_string());
        }
    }
    for var in ["CHUTES_API_KEY_FILE", "DREGG_NARRATOR_API_KEY_FILE"] {
        if let Some(p) = non_empty_var(var) {
            return read_key_file(Path::new(&p));
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        let path = PathBuf::from(home).join(DEFAULT_KEY_FILE);
        if path.exists() {
            return read_key_file(&path);
        }
    }
    Err(
        "chutes-tee: no Chutes API key — set CHUTES_API_KEY, or CHUTES_API_KEY_FILE, or place \
         the key in ~/.chutes-key"
            .to_string(),
    )
}

/// The pinned measurements registry: a local file (preferred — it is a PIN) or a fetched URL.
fn load_measurements(timeout_secs: u64) -> Result<String, String> {
    if let Some(path) = non_empty_var("CHUTES_MEASUREMENTS_JSON") {
        return std::fs::read_to_string(&path)
            .map_err(|e| format!("chutes-tee: read CHUTES_MEASUREMENTS_JSON {path}: {e}"));
    }
    let url = non_empty_var("CHUTES_MEASUREMENTS_URL")
        .unwrap_or_else(|| DEFAULT_MEASUREMENTS_URL.to_string());
    let http = crate::client::http_client_with_timeout(timeout_secs)
        .map_err(|e| format!("chutes-tee: http client: {e}"))?;
    let resp = http
        .get(&url)
        .send()
        .map_err(|e| format!("chutes-tee: fetch measurements {url}: {e}"))?;
    if !resp.status().is_success() {
        return Err(format!(
            "chutes-tee: fetch measurements {url} -> {}",
            resp.status()
        ));
    }
    resp.text()
        .map_err(|e| format!("chutes-tee: read measurements body: {e}"))
}

/// The DCAP collateral source. Fail-closed: with neither a pre-fetched file nor the
/// `collateral-fetch` feature there is nothing to verify a quote against, so we refuse.
fn load_collateral_source() -> Result<CollateralSource, String> {
    if let Some(path) = non_empty_var("CHUTES_COLLATERAL_JSON") {
        let json = std::fs::read_to_string(&path)
            .map_err(|e| format!("chutes-tee: read CHUTES_COLLATERAL_JSON {path}: {e}"))?;
        return Ok(CollateralSource::PrefetchedJson(json));
    }
    #[cfg(feature = "collateral-fetch")]
    {
        let url = non_empty_var("CHUTES_PCCS_URL").unwrap_or_else(|| DEFAULT_PCCS_URL.to_string());
        return Ok(CollateralSource::Pccs(url));
    }
    #[cfg(not(feature = "collateral-fetch"))]
    Err(
        "chutes-tee: no DCAP collateral source — set CHUTES_COLLATERAL_JSON to a pre-fetched \
         QuoteCollateralV3 JSON, or build with --features collateral-fetch to pull it from a \
         PCCS. Refusing (a quote cannot be verified without collateral)."
            .to_string(),
    )
}

fn non_empty_var(key: &str) -> Option<String> {
    std::env::var(key)
        .ok()
        .map(|v| v.trim().to_string())
        .filter(|v| !v.is_empty())
}

fn parse_var<T: std::str::FromStr>(key: &str, default: T) -> T {
    non_empty_var(key)
        .and_then(|v| v.parse::<T>().ok())
        .unwrap_or(default)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_narrator::{ConverseMessage, ToolDef};
    use serde_json::json;
    use std::sync::atomic::{AtomicU64, Ordering};

    // ── fakes ────────────────────────────────────────────────────────────────────────────────

    struct FakeAttestor {
        establishes: AtomicU64,
        refuse: bool,
    }
    impl FakeAttestor {
        fn ok() -> Arc<FakeAttestor> {
            Arc::new(FakeAttestor {
                establishes: AtomicU64::new(0),
                refuse: false,
            })
        }
        fn refusing() -> Arc<FakeAttestor> {
            Arc::new(FakeAttestor {
                establishes: AtomicU64::new(0),
                refuse: true,
            })
        }
    }
    impl Attestor for FakeAttestor {
        fn establish(&self, _model: &str) -> Result<(AttestedSession, Vec<String>), ClientError> {
            self.establishes.fetch_add(1, Ordering::SeqCst);
            if self.refuse {
                return Err(ClientError::AttestationRefused(
                    "measurement not in pinned registry".into(),
                ));
            }
            Ok((
                AttestedSession {
                    chute_id: "chute-1".to_string(),
                    instance_id: "1d5fdd83-fake".to_string(),
                    e2e_pubkey_b64: "QVRURVNURUQ=".to_string(),
                    record: AttestationRecord {
                        instance_id: "1d5fdd83-fake".to_string(),
                        measurement: [0x7d; 32],
                        tcb_status: "UpToDate".to_string(),
                        quote_bytes: b"quote-bytes".to_vec(),
                        nonce_hex: "ab".repeat(32),
                        e2e_pubkey_b64: "QVRURVNURUQ=".to_string(),
                        gpus: vec![],
                    },
                },
                (0..16).map(|i| format!("nonce-{i}")).collect(),
            ))
        }
        fn refresh_nonces(
            &self,
            _chute_id: &str,
            _instance_id: &str,
        ) -> Result<Option<Vec<String>>, ClientError> {
            Ok(Some((0..16).map(|i| format!("fresh-{i}")).collect()))
        }
    }

    /// Records the request bodies it was asked to encrypt and replies with a canned envelope.
    struct RecordingInvoker {
        seen: Mutex<Vec<(String, String, Value)>>,
        reply: Value,
    }
    impl RecordingInvoker {
        fn new(reply: Value) -> Arc<RecordingInvoker> {
            Arc::new(RecordingInvoker {
                seen: Mutex::new(Vec::new()),
                reply,
            })
        }
        fn calls(&self) -> usize {
            self.seen.lock().unwrap().len()
        }
        fn last_body(&self) -> Value {
            self.seen.lock().unwrap().last().unwrap().2.clone()
        }
        fn last_pubkey(&self) -> String {
            self.seen.lock().unwrap().last().unwrap().0.clone()
        }
        fn nonces(&self) -> Vec<String> {
            self.seen
                .lock()
                .unwrap()
                .iter()
                .map(|(_, n, _)| n.clone())
                .collect()
        }
    }
    impl Invoker for RecordingInvoker {
        fn invoke(
            &self,
            session: &AttestedSession,
            nonce: &str,
            request: &Value,
        ) -> Result<Value, InvokeError> {
            self.seen.lock().unwrap().push((
                session.e2e_pubkey_b64.clone(),
                nonce.to_string(),
                request.clone(),
            ));
            Ok(self.reply.clone())
        }
    }

    /// PANICS if reached — proves the attestation gate short-circuits before any inference.
    struct PanicInvoker;
    impl Invoker for PanicInvoker {
        fn invoke(
            &self,
            _session: &AttestedSession,
            _nonce: &str,
            _request: &Value,
        ) -> Result<Value, InvokeError> {
            panic!("inference was attempted despite a FAILED attestation");
        }
    }

    /// Fails the first call with a stale-nonce error, then succeeds.
    struct StaleThenOk {
        calls: AtomicU64,
        reply: Value,
    }
    impl Invoker for StaleThenOk {
        fn invoke(
            &self,
            _session: &AttestedSession,
            _nonce: &str,
            _request: &Value,
        ) -> Result<Value, InvokeError> {
            if self.calls.fetch_add(1, Ordering::SeqCst) == 0 {
                return Err(InvokeError::StaleNonce("nonce expired".into()));
            }
            Ok(self.reply.clone())
        }
    }

    struct AlwaysErr;
    impl Invoker for AlwaysErr {
        fn invoke(
            &self,
            _session: &AttestedSession,
            _nonce: &str,
            _request: &Value,
        ) -> Result<Value, InvokeError> {
            Err(InvokeError::Other(ClientError::Invoke(
                "instance 503".into(),
            )))
        }
    }

    const MODEL: &str = "Qwen/Qwen3-32B-TEE";

    fn completion() -> Value {
        json!({
            "id": "chatcmpl-fake",
            "choices": [{
                "message": { "role": "assistant", "content": "The torchlight fails at the stair." },
                "finish_reason": "stop"
            }],
            "usage": { "prompt_tokens": 137, "completion_tokens": 42 }
        })
    }

    fn backend(
        attestor: Arc<dyn Attestor>,
        invoker: Arc<dyn Invoker>,
        ttl: u64,
    ) -> ChutesTeeBackend {
        ChutesTeeBackend::new(attestor, invoker, SessionCache::new(ttl), 0.7)
    }

    fn request() -> ConverseRequest {
        ConverseRequest {
            model: MODEL.to_string(),
            system: "You are the DM.".to_string(),
            messages: vec![
                ConverseMessage::user("I open the door."),
                ConverseMessage::assistant("It resists."),
                ConverseMessage::user("I shoulder it."),
            ],
            max_tokens: 256,
            tools: Vec::new(),
        }
    }

    // ── request mapping ──────────────────────────────────────────────────────────────────────

    /// The ConverseRequest → OpenAI-JSON mapping the enclave actually receives.
    #[test]
    fn request_maps_to_the_openai_body_that_gets_encrypted() {
        let invoker = RecordingInvoker::new(completion());
        let be = backend(FakeAttestor::ok(), invoker.clone(), DEFAULT_TTL_SECS);
        be.converse(&request()).unwrap();

        let body = invoker.last_body();
        assert_eq!(body["model"], MODEL);
        assert_eq!(body["max_tokens"], 256);
        assert_eq!(body["stream"], false);
        // f32 → JSON, so compare with tolerance rather than pretending it round-trips exactly.
        assert!((body["temperature"].as_f64().unwrap() - 0.7).abs() < 1e-6);
        let msgs = body["messages"].as_array().unwrap();
        assert_eq!(msgs.len(), 4, "system + 3 turns");
        assert_eq!(msgs[0]["role"], "system");
        assert_eq!(msgs[0]["content"], "You are the DM.");
        assert_eq!(msgs[1]["role"], "user");
        assert_eq!(msgs[2]["role"], "assistant");
        assert_eq!(msgs[3]["content"], "I shoulder it.");
        assert!(body.get("tools").is_none());
        // And it went to the ATTESTED key, not some other one.
        assert_eq!(invoker.last_pubkey(), "QVRURVNURUQ=");
    }

    /// Tools survive the mapping (the Discord bot's typed-turn path depends on this).
    #[test]
    fn tools_are_carried_into_the_encrypted_body() {
        let invoker = RecordingInvoker::new(completion());
        let be = backend(FakeAttestor::ok(), invoker.clone(), DEFAULT_TTL_SECS);
        let mut req = request();
        req.tools = vec![ToolDef {
            name: "submit_dungeon_turn".to_string(),
            description: "submit the party's turn".to_string(),
            input_schema: json!({"type":"object","properties":{"command":{"type":"string"}}}),
        }];
        be.converse(&req).unwrap();

        let body = invoker.last_body();
        let tools = body["tools"].as_array().unwrap();
        assert_eq!(tools[0]["type"], "function");
        assert_eq!(tools[0]["function"]["name"], "submit_dungeon_turn");
        assert_eq!(
            tools[0]["function"]["parameters"]["properties"]["command"]["type"],
            "string"
        );
    }

    // ── response mapping ─────────────────────────────────────────────────────────────────────

    /// The decrypted envelope → ConverseResponse mapping, INCLUDING the usage the ledger prices.
    #[test]
    fn response_maps_text_and_real_usage_tokens() {
        let be = backend(
            FakeAttestor::ok(),
            RecordingInvoker::new(completion()),
            DEFAULT_TTL_SECS,
        );
        let resp = be.converse(&request()).unwrap();
        assert_eq!(resp.text, "The torchlight fails at the stair.");
        assert_eq!(resp.stop_reason, "stop");
        assert_eq!(resp.input_tokens, 137, "true-up prices the REAL usage");
        assert_eq!(resp.output_tokens, 42);
        assert!(resp.tool_calls.is_empty());
    }

    #[test]
    fn response_maps_tool_calls() {
        let reply = json!({
            "choices": [{
                "message": {
                    "role": "assistant",
                    "content": null,
                    "tool_calls": [{
                        "id": "call_1",
                        "type": "function",
                        "function": { "name": "submit_dungeon_turn",
                                      "arguments": "{\"command\":\"press_on\"}" }
                    }]
                },
                "finish_reason": "tool_calls"
            }],
            "usage": { "prompt_tokens": 9, "completion_tokens": 4 }
        });
        let be = backend(
            FakeAttestor::ok(),
            RecordingInvoker::new(reply),
            DEFAULT_TTL_SECS,
        );
        let resp = be.converse(&request()).unwrap();
        assert_eq!(resp.tool_calls.len(), 1);
        assert_eq!(resp.tool_calls[0].name, "submit_dungeon_turn");
        assert_eq!(resp.tool_calls[0].input["command"], "press_on");
        assert_eq!(resp.input_tokens, 9);
    }

    /// A provider error envelope inside a successfully-decrypted reply is an error, not empty prose.
    #[test]
    fn error_envelope_from_the_enclave_is_an_error() {
        let be = backend(
            FakeAttestor::ok(),
            RecordingInvoker::new(json!({"error": {"message": "model overloaded"}})),
            DEFAULT_TTL_SECS,
        );
        let err = be.converse(&request()).unwrap_err();
        assert!(err.contains("model overloaded"), "got: {err}");
    }

    // ── attestation surfacing ────────────────────────────────────────────────────────────────

    /// The response carries the attestation, and the FULL quote stays retrievable for a receipt.
    #[test]
    fn response_carries_the_attestation_and_the_quote_is_retrievable() {
        let be = backend(
            FakeAttestor::ok(),
            RecordingInvoker::new(completion()),
            DEFAULT_TTL_SECS,
        );
        assert!(be.last_attestation().is_none(), "nothing before a call");

        let resp = be.converse(&request()).unwrap();
        let att = resp.attestation.expect("attested response");
        assert_eq!(att.instance_id, "1d5fdd83-fake");
        assert_eq!(att.tcb_status, "UpToDate");
        assert_eq!(att.measurement, [0x7d; 32]);
        assert_eq!(att.quote_len, b"quote-bytes".len());
        assert_eq!(att.measurement_hex().len(), 64);

        // The summary's digest is a real handle onto the full quote the backend kept.
        let record = be.last_attestation().expect("full record");
        assert_eq!(record.quote_bytes, b"quote-bytes".to_vec());
        let mut h = Sha256::new();
        h.update(&record.quote_bytes);
        assert_eq!(att.quote_sha256.as_slice(), h.finalize().as_slice());
        assert_eq!(att.quote_sha256_hex().len(), 64);
    }

    /// **The archive seam.** A receipt lane holding only the response's summary can pull the FULL
    /// evidence by the summary's own quote digest — the raw quote plus the nonce/pubkey pair that
    /// makes the provider's `report_data` binding recomputable by a third party.
    ///
    /// The teeth are the two negatives: a digest that was never attested yields NOTHING (the
    /// backend does not hand out "the closest record"), and the returned bytes hash to the digest
    /// that was asked for.
    #[test]
    fn the_full_evidence_is_retrievable_by_the_summarys_quote_digest() {
        let be = backend(
            FakeAttestor::ok(),
            RecordingInvoker::new(completion()),
            DEFAULT_TTL_SECS,
        );
        let summary = be
            .converse(&request())
            .unwrap()
            .attestation
            .expect("attested response");

        let evidence = be
            .attestation_for(&summary.quote_sha256)
            .expect("the evidence behind the summary is retained");
        assert_eq!(evidence.quote_bytes, b"quote-bytes".to_vec());
        assert_eq!(evidence.instance_id, summary.instance_id);
        assert_eq!(evidence.measurement, summary.measurement);
        assert_eq!(evidence.tcb_status, summary.tcb_status);
        // The binding preimages travel, so an archive of this is checkable rather than asserted.
        assert_eq!(evidence.nonce_hex.len(), 64);
        assert_eq!(evidence.e2e_pubkey_b64, "QVRURVNURUQ=");
        let mut h = Sha256::new();
        h.update(&evidence.quote_bytes);
        assert_eq!(
            h.finalize().as_slice(),
            summary.quote_sha256.as_slice(),
            "the bytes handed back hash to the digest that was asked for"
        );

        // A digest we never attested gets nothing — not the nearest record, not the last one.
        assert!(
            be.attestation_for(&[0xFF; 32]).is_none(),
            "an unknown digest must not resolve to some other call's quote"
        );
    }

    /// A digest is retrievable ONLY after a real attested call, and a refused attestation retains
    /// nothing — the archive can never acquire evidence for a turn that did not attest.
    #[test]
    fn a_refused_attestation_retains_no_evidence() {
        let be = backend(
            FakeAttestor::refusing(),
            Arc::new(PanicInvoker),
            DEFAULT_TTL_SECS,
        );
        assert!(be.converse(&request()).is_err());
        let mut h = Sha256::new();
        h.update(b"quote-bytes");
        let mut digest = [0u8; 32];
        digest.copy_from_slice(&h.finalize());
        assert!(be.attestation_for(&digest).is_none());
    }

    /// The retention is BOUNDED and the cached-verification replay does not churn it: twelve
    /// turns on one cached attestation keep exactly one record (not twelve), and it stays
    /// retrievable throughout.
    #[test]
    fn retention_is_bounded_and_a_reused_verification_does_not_churn_it() {
        let be = backend(
            FakeAttestor::ok(),
            RecordingInvoker::new(completion()),
            DEFAULT_TTL_SECS,
        );
        let mut digest = None;
        for _ in 0..12 {
            let summary = be.converse(&request()).unwrap().attestation.unwrap();
            digest = Some(summary.quote_sha256);
        }
        assert_eq!(
            be.retained.lock().unwrap().len(),
            1,
            "one verification reused across 12 turns is ONE retained record"
        );
        assert!(be.attestation_for(&digest.unwrap()).is_some());
    }

    // ── FAIL-CLOSED ──────────────────────────────────────────────────────────────────────────

    /// THE POINT: a failed attestation returns `Err` and NO inference is attempted. The invoker
    /// panics if reached, so a fall-through would fail the test loudly rather than silently pass.
    #[test]
    fn attestation_failure_errors_and_never_reaches_inference() {
        let att = FakeAttestor::refusing();
        let be = backend(att.clone(), Arc::new(PanicInvoker), DEFAULT_TTL_SECS);

        let err = be.converse(&request()).unwrap_err();
        assert!(err.contains("NO inference attempted"), "got: {err}");
        assert!(err.contains("ATTESTATION REFUSED"), "got: {err}");
        assert!(be.last_attestation().is_none());
        assert_eq!(att.establishes.load(Ordering::SeqCst), 1);
    }

    /// Repeated failures keep failing — a refusal is never cached into a success.
    #[test]
    fn attestation_failure_does_not_become_a_cached_success() {
        let be = backend(
            FakeAttestor::refusing(),
            Arc::new(PanicInvoker),
            DEFAULT_TTL_SECS,
        );
        for _ in 0..3 {
            assert!(be.converse(&request()).is_err());
        }
        assert!(be.cached_session(MODEL).is_none());
    }

    // ── caching + retry ──────────────────────────────────────────────────────────────────────

    /// The perf claim at the BACKEND level: N narration turns, ONE attestation.
    #[test]
    fn repeated_turns_attest_once() {
        let att = FakeAttestor::ok();
        let invoker = RecordingInvoker::new(completion());
        let be = backend(att.clone(), invoker.clone(), DEFAULT_TTL_SECS);

        for _ in 0..12 {
            be.converse(&request()).unwrap();
        }
        assert_eq!(
            att.establishes.load(Ordering::SeqCst),
            1,
            "12 turns must cost exactly ONE attestation"
        );
        assert_eq!(invoker.calls(), 12);
        let mut nonces = invoker.nonces();
        nonces.sort();
        nonces.dedup();
        assert_eq!(
            nonces.len(),
            12,
            "each turn used a distinct invocation nonce"
        );
    }

    /// A zero TTL re-attests every turn — the knob is real, not decorative.
    #[test]
    fn zero_ttl_re_attests_every_turn() {
        let att = FakeAttestor::ok();
        let be = backend(att.clone(), RecordingInvoker::new(completion()), 0);
        for _ in 0..3 {
            be.converse(&request()).unwrap();
        }
        assert_eq!(att.establishes.load(Ordering::SeqCst), 3);
    }

    /// A stale invocation nonce retries on the SAME attested instance — no re-attestation.
    #[test]
    fn stale_nonce_retries_without_re_attesting() {
        let att = FakeAttestor::ok();
        let invoker = Arc::new(StaleThenOk {
            calls: AtomicU64::new(0),
            reply: completion(),
        });
        let be = backend(att.clone(), invoker.clone(), DEFAULT_TTL_SECS);

        let resp = be.converse(&request()).unwrap();
        assert_eq!(resp.text, "The torchlight fails at the stair.");
        assert!(resp.attestation.is_some());
        assert_eq!(invoker.calls.load(Ordering::SeqCst), 2, "one retry");
        assert_eq!(
            att.establishes.load(Ordering::SeqCst),
            1,
            "a stale nonce is NOT an attestation failure"
        );
    }

    /// An invocation error invalidates the cached verification, so the next turn re-attests.
    #[test]
    fn invocation_error_invalidates_the_cached_attestation() {
        let att = FakeAttestor::ok();
        let be = backend(att.clone(), Arc::new(AlwaysErr), DEFAULT_TTL_SECS);

        assert!(be
            .converse(&request())
            .unwrap_err()
            .contains("instance 503"));
        assert!(be.cached_session(MODEL).is_none(), "cache dropped on error");
        assert!(be.converse(&request()).is_err());
        assert_eq!(
            att.establishes.load(Ordering::SeqCst),
            2,
            "the second turn re-attested rather than reusing a failing instance"
        );
    }

    // ── config helpers ───────────────────────────────────────────────────────────────────────

    #[test]
    fn statuses_parse_and_drop_blanks() {
        assert_eq!(parse_statuses("UpToDate"), vec!["UpToDate"]);
        assert_eq!(
            parse_statuses(" UpToDate , SWHardeningNeeded ,"),
            vec!["UpToDate", "SWHardeningNeeded"]
        );
        assert!(parse_statuses(" , ").is_empty());
    }

    /// The `*_FILE` form is how the key is actually stored (`~/.chutes-key`), trailing newline
    /// and all — a key read with the newline attached would 401 every request.
    #[test]
    fn key_file_is_read_and_trimmed() {
        let dir = std::env::temp_dir().join(format!(
            "chutes-tee-key-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("chutes-key");
        std::fs::write(&path, "cpk_abc123\n").unwrap();
        assert_eq!(read_key_file(&path).unwrap(), "cpk_abc123");

        std::fs::write(&path, "   \n").unwrap();
        assert!(read_key_file(&path).unwrap_err().contains("empty"));
        assert!(read_key_file(&dir.join("nope")).is_err());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn narrator_gpu_gate_is_opt_in() {
        assert!(!narrator_requires_gpu(None));
        assert!(!narrator_requires_gpu(Some("0")));
        assert!(!narrator_requires_gpu(Some("yes")));
        assert!(narrator_requires_gpu(Some("1")));
        // the library default stays enforcing
        assert!(VerifierConfig::new("", "[]").gpu.required);
    }

    #[test]
    fn summary_digest_matches_the_quote() {
        let record = AttestationRecord {
            instance_id: "i".to_string(),
            measurement: [1u8; 32],
            tcb_status: "UpToDate".to_string(),
            quote_bytes: vec![9u8; 4096],
            nonce_hex: "cd".repeat(32),
            e2e_pubkey_b64: "QVRURVNURUQ=".to_string(),
            gpus: vec![],
        };
        let s = summarize(&record);
        assert_eq!(s.quote_len, 4096);
        let mut h = Sha256::new();
        h.update(&record.quote_bytes);
        assert_eq!(s.quote_sha256.as_slice(), h.finalize().as_slice());
    }
}
