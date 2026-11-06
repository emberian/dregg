//! The attestation gate — our value-add over the reference client, and it is FAIL-CLOSED:
//! before a single byte is encrypted, we independently DCAP-verify that the instance's
//! ML-KEM `e2e_pubkey` was measured into a TDX quote by an enclave whose measurements match
//! the pinned Chutes registry, with a fresh nonce (replay-kill). Only an `e2e_pubkey` whose
//! instance attested is used for encryption, and that instance id is pinned as
//! `X-Instance-Id`. A failed attestation returns `Err` and NO request is sent.
//!
//! Evidence source: `GET {api_base}/chutes/{chute_id}/evidence?nonce=<fresh 64-hex>` (Bearer),
//! confirmed against chutes-api `api/chute/router.py::get_tee_chute_evidence` (public route,
//! `response_model=TeeChuteEvidence`). Response shape (`api/server/schemas.py`):
//! `{evidence:[{quote (base64 TDX quote), gpu_evidence:[...], instance_id, certificate
//! (base64 DER TLS cert)}], failed_instance_ids:[...]}`.
//!
//! Every GPU the instance reports must ALSO verify ([`crate::gpu`]): NVIDIA device chain,
//! report signature over the same fresh nonce, FWID, goldens from NVIDIA's signed RIMs, OCSP.
//! An instance with no GPU evidence, or any GPU that fails, is refused.
//!
//! The nonce/pubkey binding recomputed here is the FIXED string binding
//! (`SHA-256(ascii(nonce_hex) ‖ ascii(e2e_pubkey_b64))`) from `dregg_tee_verify::tdx` — see
//! that module for the byte-for-byte correspondence to chutes-api.

use std::time::{SystemTime, UNIX_EPOCH};

use serde::Deserialize;

use dregg_tee_verify::tdx::{apply_chutes_bindings, TdxVerifier};
use dregg_tee_verify::{decode_quote_field, parse_chutes_measurements, QuoteCollateralV3};

use crate::discovery::Instances;
use crate::error::ClientError;
use crate::gpu::{gate_instance, GpuAttestation, GpuEvidenceItem, GpuGate};

/// Where DCAP collateral (`QuoteCollateralV3`) comes from. Production supplies it pre-fetched
/// so the verify path is network-free (the TCB stays offline); the live acceptance test can
/// fetch it per-quote from a PCCS under the `collateral-fetch` feature.
#[derive(Clone)]
pub enum CollateralSource {
    /// A pre-fetched `QuoteCollateralV3` as JSON (the shape a PCCS/Chutes cache stores).
    PrefetchedJson(String),
    /// Fetch collateral per-quote from a PCCS/PCS base URL (e.g. `https://pccs.phala.network`).
    /// Only available with the `collateral-fetch` feature.
    #[cfg(feature = "collateral-fetch")]
    Pccs(String),
}

/// Configuration for the attestation gate.
#[derive(Clone)]
pub struct VerifierConfig {
    /// E2EE API base (default `https://api.chutes.ai`) — where `/chutes/{id}/evidence`,
    /// `/e2e/instances/{id}` and `/e2e/invoke` live.
    pub api_base: String,
    /// Models base (default `https://llm.chutes.ai`) — where `/v1/models` lives (model→chute_id).
    pub models_base: String,
    /// DCAP collateral source.
    pub collateral: CollateralSource,
    /// The Chutes TEE measurements registry JSON (top-level array of entries, as served by
    /// `https://api.chutes.ai/servers/tee/measurements`). An instance is accepted only if its
    /// MRTD + RTMR0..2 match at least one entry.
    pub measurements_json: String,
    /// Accepted DCAP TCB statuses. STRICT default `["UpToDate"]`; widen deliberately (e.g.
    /// add `"SWHardeningNeeded"`) with eyes open.
    pub accepted_statuses: Vec<String>,
    /// The GPU gate. Default: at least one GPU, RIMs and OCSP fetched from NVIDIA per GPU.
    pub gpu: GpuGate,
}

impl VerifierConfig {
    /// STRICT config over pre-fetched collateral + a measurements registry.
    pub fn new(collateral_json: impl Into<String>, measurements_json: impl Into<String>) -> Self {
        VerifierConfig {
            api_base: crate::discovery::DEFAULT_API_BASE.to_string(),
            models_base: crate::discovery::DEFAULT_MODELS_BASE.to_string(),
            collateral: CollateralSource::PrefetchedJson(collateral_json.into()),
            measurements_json: measurements_json.into(),
            accepted_statuses: vec!["UpToDate".to_string()],
            gpu: GpuGate::default(),
        }
    }
}

/// A single instance that PASSED attestation. `e2e_pubkey_b64` is safe to encrypt to; pin
/// `instance_id` as `X-Instance-Id`.
#[derive(Debug, Clone)]
pub struct AttestedInstance {
    pub instance_id: String,
    pub e2e_pubkey_b64: String,
    pub measurement: [u8; 32],
    pub tcb_status: String,
    pub quote_bytes: Vec<u8>,
    /// The FRESH attestation nonce this quote was fetched with. Carried out of the verification
    /// (rather than dropped on the floor) because it is half of the `report_data` binding: with
    /// `nonce_hex` + `e2e_pubkey_b64` anyone holding the quote can recompute
    /// `SHA-256(ascii(nonce) ‖ ascii(pubkey))` and see the quote was minted for THIS key. Without
    /// it an archived quote proves only that some enclave with these measurements signed
    /// something, at no particular time.
    pub nonce_hex: String,
    /// The instance's GPUs, each verified against NVIDIA's PKI and signed RIMs.
    pub gpus: Vec<GpuAttestation>,
}

/// The attestation record returned alongside a completion — a portable receipt of WHICH
/// enclave served the request and under what code identity / TCB.
///
/// It carries the two binding preimages (`nonce_hex`, `e2e_pubkey_b64`) alongside the quote so a
/// receipt lane can archive something a THIRD PARTY can check, not just something we assert. What
/// the archived record establishes is unchanged from what the live verification established:
/// where the inference ran, under which code identity and TCB verdict — never anything about the
/// tokens that came back.
#[derive(Debug, Clone)]
pub struct AttestationRecord {
    pub instance_id: String,
    pub measurement: [u8; 32],
    pub tcb_status: String,
    pub quote_bytes: Vec<u8>,
    /// The fresh 64-hex attestation nonce bound into `report_data`.
    pub nonce_hex: String,
    /// The base64 ML-KEM-768 instance key bound into `report_data` — the key the request was
    /// encapsulated to.
    pub e2e_pubkey_b64: String,
    /// The GPUs that verified: device identity (leaf fingerprint), driver and VBIOS versions,
    /// RIM signers. A summary of the live check; the raw GPU evidence is not archived here.
    pub gpus: Vec<GpuAttestation>,
}

impl From<&AttestedInstance> for AttestationRecord {
    fn from(a: &AttestedInstance) -> Self {
        AttestationRecord {
            instance_id: a.instance_id.clone(),
            measurement: a.measurement,
            tcb_status: a.tcb_status.clone(),
            quote_bytes: a.quote_bytes.clone(),
            nonce_hex: a.nonce_hex.clone(),
            e2e_pubkey_b64: a.e2e_pubkey_b64.clone(),
            gpus: a.gpus.clone(),
        }
    }
}

// ---- Evidence response shape (chutes-api api/server/schemas.py) ----

#[derive(Debug, Deserialize)]
struct TeeChuteEvidence {
    #[serde(default)]
    evidence: Vec<TeeInstanceEvidence>,
    #[serde(default)]
    #[allow(dead_code)]
    failed_instance_ids: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct TeeInstanceEvidence {
    /// Base64-encoded TDX quote.
    quote: String,
    /// Per-GPU evidence. Defaulted so that an absent field reaches the GPU gate and is refused
    /// THERE, with a reason, rather than failing the whole response's parse.
    #[serde(default)]
    gpu_evidence: Vec<GpuEvidenceItem>,
    /// Instance ID (present when part of a chute's evidence list).
    #[serde(default)]
    instance_id: Option<String>,
    #[allow(dead_code)]
    #[serde(default)]
    certificate: Option<String>,
}

/// The quote-digest handle and the archived-record re-check, RE-EXPORTED rather than restated.
///
/// Both used to live here, and both only ever called `dregg_tee_verify` primitives. They moved
/// down to that crate when a second consumer appeared (`dungeon_on_dregg::attest_check`, the
/// verifier a player runs on the files `/dungeon attestation` hands them) so there is exactly one
/// definition of "the digest" and one of "does this record still match its own quote" — the
/// checker a player runs and the check this crate's archive lane runs are the SAME function, not
/// two that agree today. See [`dregg_tee_verify::tdx::recheck_archived_binding`] for the full
/// statement of what that re-check does and does not establish.
pub use dregg_tee_verify::{quote_sha256_hex, recheck_archived_binding};

/// Generate a fresh 64-hex-char (32-byte) attestation nonce, per chutes-api
/// `validate_user_nonce`. This is SEPARATE from the opaque invocation nonce and from the
/// 12-byte AEAD nonce.
pub fn fresh_attestation_nonce() -> Result<String, ClientError> {
    let mut b = [0u8; 32];
    getrandom::fill(&mut b).map_err(|e| ClientError::Config(format!("nonce RNG: {e}")))?;
    Ok(hex::encode(b))
}

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

fn load_collateral(
    source: &CollateralSource,
    _quote_bytes: &[u8],
) -> Result<QuoteCollateralV3, ClientError> {
    match source {
        CollateralSource::PrefetchedJson(json) => serde_json::from_str::<QuoteCollateralV3>(json)
            .map_err(|e| ClientError::Config(format!("collateral JSON parse: {e}"))),
        #[cfg(feature = "collateral-fetch")]
        CollateralSource::Pccs(url) => {
            dregg_tee_verify::tdx::fetch_collateral_blocking(_quote_bytes, url)
                .map_err(ClientError::Evidence)
        }
    }
}

/// Fetch evidence for `chute_id` with a fresh attestation nonce and DCAP-verify each
/// instance, returning the instances that attested (fail-closed). `discovered` supplies the
/// `e2e_pubkey` per instance id (the value bound into the quote's `report_data`).
///
/// An instance passes only if ALL of: (1) the DCAP crypto verifies against pinned collateral
/// and roots at the pinned Intel SGX Root CA; (2) `report_data[0..32] ==
/// SHA-256(ascii(nonce_hex) ‖ ascii(discovered e2e_pubkey_b64))`; (3) MRTD+RTMR0..2 match a
/// registry entry; (4) the TCB status is in `accepted_statuses`; (5) every reported GPU verifies
/// under `cfg.gpu` with the same nonce, and there are at least `cfg.gpu.min_gpus` of them.
pub fn attest_chute(
    http: &reqwest::blocking::Client,
    cfg: &VerifierConfig,
    chute_id: &str,
    cpk: &str,
    discovered: &Instances,
) -> Result<Vec<AttestedInstance>, ClientError> {
    let nonce_hex = fresh_attestation_nonce()?;
    let url = format!(
        "{}/chutes/{}/evidence",
        cfg.api_base.trim_end_matches('/'),
        chute_id
    );
    let resp = http
        .get(&url)
        .query(&[("nonce", nonce_hex.as_str())])
        .bearer_auth(cpk)
        .send()
        .map_err(ClientError::Http)?;
    let status = resp.status();
    if !status.is_success() {
        let body = resp.text().unwrap_or_default();
        return Err(ClientError::Evidence(format!(
            "GET {url} -> {status}: {body}"
        )));
    }
    let evidence: TeeChuteEvidence = resp.json().map_err(ClientError::Http)?;

    let measurements = parse_chutes_measurements(&cfg.measurements_json)
        .map_err(|e| ClientError::Config(format!("measurements registry: {e}")))?;
    if measurements.is_empty() {
        return Err(ClientError::Config(
            "measurements registry is empty — cannot pin any code identity".into(),
        ));
    }

    let mut attested = Vec::new();
    let mut reasons = Vec::new();

    for ev in &evidence.evidence {
        let Some(instance_id) = ev.instance_id.clone() else {
            continue;
        };
        // The e2e_pubkey we will encrypt to MUST come from discovery and MUST be the one the
        // quote binds. Skip instances we did not discover (no pubkey to bind / encrypt to).
        let Some(inst) = discovered.by_id(&instance_id) else {
            reasons.push(format!("{instance_id}: not in discovery (no e2e_pubkey)"));
            continue;
        };
        let e2e_pubkey_b64 = inst.e2e_pubkey.clone();

        let quote_bytes = match decode_quote_field(&ev.quote) {
            Ok(q) => q,
            Err(e) => {
                reasons.push(format!("{instance_id}: quote decode: {e}"));
                continue;
            }
        };

        let collateral = load_collateral(&cfg.collateral, &quote_bytes)?;
        let verifier = TdxVerifier::new(collateral)
            .with_accepted_statuses(cfg.accepted_statuses.iter().cloned());

        // (1) DCAP crypto core (pinned-root + full DCAP verify + measurement extraction).
        let rep = match verifier.verify_tdx_core(&quote_bytes, now_secs()) {
            Ok(r) => r,
            Err(e) => {
                reasons.push(format!("{instance_id}: DCAP verify: {e}"));
                continue;
            }
        };

        // (4) TCB gate, fail-closed (apply_chutes_bindings passes tcb_ok THROUGH without
        //     rejecting, so we enforce it here).
        if !rep.tcb_ok {
            reasons.push(format!(
                "{instance_id}: TCB status {:?} not in accepted set",
                rep.status
            ));
            continue;
        }

        // (2)+(3) nonce/pubkey string binding + measurement match against each registry
        // entry (the binding is entry-independent; only the measurement match differs).
        let mut bound = false;
        for entry in &measurements {
            if apply_chutes_bindings(&rep, &nonce_hex, &e2e_pubkey_b64, entry).is_ok() {
                bound = true;
                break;
            }
        }
        if !bound {
            reasons.push(format!(
                "{instance_id}: report_data binding or measurement match failed for all {} registry entries",
                measurements.len()
            ));
            continue;
        }

        // (5) the GPUs, against the same fresh nonce.
        let gpus = match gate_instance(http, &ev.gpu_evidence, &nonce_hex, &cfg.gpu, now_secs()) {
            Ok(g) => g,
            Err(e) => {
                reasons.push(format!("{instance_id}: GPU attestation: {e}"));
                continue;
            }
        };

        attested.push(AttestedInstance {
            instance_id,
            e2e_pubkey_b64,
            measurement: rep.measurement,
            tcb_status: rep.status.clone(),
            quote_bytes,
            // The nonce this evidence request was made with — the one `apply_chutes_bindings`
            // just checked `report_data` against, so the pair travels with the quote.
            nonce_hex: nonce_hex.clone(),
            gpus,
        });
    }

    if attested.is_empty() {
        return Err(ClientError::AttestationRefused(format!(
            "no instance of chute {chute_id} attested [{}]",
            reasons.join("; ")
        )));
    }
    Ok(attested)
}
