//! Host-side TEE attestation verifiers — the real vendor crypto behind
//! [`dregg_cell::tee_attest::TeeAttestationVerifier`].
//!
//! Kept OUT of `dregg-cell` so the cell crate stays light (no X.509 / P-384 /
//! CBOR). Install into the fail-closed
//! [`dregg_cell::tee_attest::TeeWitnessedPredicateVerifier`] via `with_verifier`.
//!
//! ## AWS Nitro Enclaves ([`NitroVerifier`])
//!
//! Verifies a real Nitro attestation document (a CBOR/COSE_Sign1 blob signed by the
//! Nitro Security Module) against the **pinned AWS Nitro Enclaves root G1**
//! certificate (embedded; SHA-256 fingerprint
//! `641a0321a3e244efe456463195d606317ed7cdcc3c1756e09893f3c68f79bb5b`). It:
//! 1. parses the COSE_Sign1 and the attestation-doc payload;
//! 2. verifies the X.509 chain leaf ← cabundle ← the pinned root (each link's
//!    signature + validity window, checked against the doc's own timestamp);
//! 3. verifies the ES384 (ECDSA-P384 / SHA-384) COSE signature over the canonical
//!    `Sig_structure` using the leaf certificate's public key;
//! 4. extracts `measurement = SHA-256(PCR0‖PCR1‖PCR2)` and
//!    `report_data = user_data`.
//!
//! ⚑ **NITRO HAS NO TCB RUNG, AND THE CLAIMS NOW SAY SO.** An attestation document exposes
//! no microcode/firmware version, so there is nothing for a pinned minimum to compare
//! against; [`verify_nitro_core`] returns
//! [`TcbStatus::NoPolicyOnPlatform`](dregg_cell::tee_attest::TcbStatus::NoPolicyOnPlatform)
//! rather than the hardcoded `tcb_ok: true` it returned until 2026-07-30. On this platform
//! the enclave-identity pin (`expected_measurement`) is doing the whole job that a TCB
//! policy does elsewhere — a caller relying on a TCB decision must know it is absent, and
//! a comment could not tell it.
//!
//! Freshness (is the doc *recent*) is enforced only in the trait entry point
//! against wall-clock now; the crypto core uses the doc's timestamp so a captured
//! fixture verifies deterministically forever.
//!
//! ## AMD SEV-SNP ([`snp::SnpVerifier`])
//!
//! Parses the fixed-layout 1184-byte SEV-SNP `ATTESTATION_REPORT`, extracts the launch
//! `measurement` (folded to 32 bytes via SHA-256) and `report_data` (first 32 bytes),
//! and verifies the report-body ECDSA-P384/SHA-384 signature with the chip's VCEK
//! public key after checking VCEK ← ASK ← pinned-ARK. The **real AMD roots** (ARK/ASK per
//! product: Milan/Genoa/Turin) are embedded from the AMD KDS — build the anchored verifier
//! with [`SnpVerifier::new_with_amd_roots`]. Fail-closed: [`SnpVerifier::new`] (no roots)
//! rejects every report. See [`snp`] and [`snp::snp_chain`] (roots + provenance).

use std::collections::BTreeMap;
use std::time::{SystemTime, UNIX_EPOCH};

use dregg_cell::tee_attest::{TcbStatus, TeeAttestationVerifier, TeeQuoteKind, TeeReportClaims};
use serde::Deserialize;
use serde_bytes::ByteBuf;
use sha2::{Digest, Sha256};
use x509_parser::prelude::*;

pub mod attested_data;
pub mod nvidia;
pub mod oracle_mark;
pub mod snp;
pub mod tdx;
pub use attested_data::{
    attest_data, AttestedDataInput, AttestedError, AttestedFact, PayloadBinding, TrustGrade,
};
pub use oracle_mark::{Grade, GradedMark, MarkError, MarkPrice, MarkProvenance};
pub use snp::{SnpError, SnpPolicy, SnpProduct, SnpTrust, SnpVerifier, TcbVersion};
pub use tdx::{
    apply_chutes_bindings, check_chutes_preimages_well_formed, check_pck_chain_roots_at_pinned,
    chutes_report_data_binding, decode_quote_field, fold_tdx_measurement,
    parse_chutes_measurements, pck_chain_structural_unverified, quote_sha256_hex,
    recheck_archived_binding, registers_structural_unverified, report_data_structural_unverified,
    ChutesMeasurements, QuoteCollateralV3, TdxRegisters, TdxVerifiedReport, TdxVerifier,
};

/// The pinned AWS Nitro Enclaves root G1 certificate (PEM).
const AWS_NITRO_ROOT_PEM: &[u8] = include_bytes!("aws_nitro_root_g1.pem");

/// Max age (seconds) a Nitro doc may be, checked against wall-clock now in the trait
/// entry point. Callers wanting stronger freshness should bind a fresh nonce into
/// `report_data`.
const MAX_DOC_AGE_SECS: u64 = 3600;

/// COSE_Sign1 = `[protected: bstr, unprotected: map, payload: bstr, signature: bstr]`.
#[derive(Deserialize)]
struct CoseSign1(
    ByteBuf,
    #[allow(dead_code)] ciborium::value::Value,
    ByteBuf,
    ByteBuf,
);

/// The Nitro attestation document (the COSE payload).
#[derive(Deserialize)]
struct AttDoc {
    #[allow(dead_code)]
    module_id: String,
    #[allow(dead_code)]
    digest: String,
    /// Milliseconds since epoch.
    timestamp: u64,
    pcrs: BTreeMap<u8, ByteBuf>,
    /// Leaf certificate (DER) that signed this doc.
    certificate: ByteBuf,
    /// Chain from the root down to the leaf's issuer: `[root, int1, .., intN]`.
    cabundle: Vec<ByteBuf>,
    #[serde(default)]
    #[allow(dead_code)]
    public_key: Option<ByteBuf>,
    /// The caller-bound 64-byte-max field — where we bind the turn/session commitment.
    #[serde(default)]
    user_data: Option<ByteBuf>,
    #[serde(default)]
    #[allow(dead_code)]
    nonce: Option<ByteBuf>,
}

/// Verifier for AWS Nitro Enclaves attestation documents.
pub struct NitroVerifier {
    /// Max doc age against wall-clock now; `None` disables the freshness check (for
    /// captured fixtures, or when freshness is enforced by a bound nonce upstream).
    max_age_secs: Option<u64>,
}

impl NitroVerifier {
    /// Default: enforce a [`MAX_DOC_AGE_SECS`] freshness window.
    pub fn new() -> NitroVerifier {
        NitroVerifier {
            max_age_secs: Some(MAX_DOC_AGE_SECS),
        }
    }

    /// No freshness bound — verify the crypto only (captured fixtures; or when a fresh
    /// nonce is bound into `report_data` and freshness is checked there).
    pub fn without_freshness() -> NitroVerifier {
        NitroVerifier { max_age_secs: None }
    }

    /// Enforce a custom freshness window (seconds).
    pub fn with_max_age(secs: u64) -> NitroVerifier {
        NitroVerifier {
            max_age_secs: Some(secs),
        }
    }
}

impl Default for NitroVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl TeeAttestationVerifier for NitroVerifier {
    fn verify_report(
        &self,
        kind: TeeQuoteKind,
        report_bytes: &[u8],
    ) -> Result<TeeReportClaims, String> {
        if kind != TeeQuoteKind::AwsNitro {
            return Err(format!("NitroVerifier handles AwsNitro only, got {kind:?}"));
        }
        let (claims, doc_ts_ms) = verify_nitro_core(report_bytes)?;
        // Freshness against wall-clock now (the crypto core already validated the cert
        // chain against the doc's own timestamp).
        if let Some(max_age) = self.max_age_secs {
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_err(|_| {
                    "Nitro freshness: system clock is before the Unix epoch; refused".to_string()
                })?
                .as_secs();
            check_nitro_freshness(now, doc_ts_ms, max_age)?;
        }
        Ok(claims)
    }
}

/// How far in the future (seconds) a Nitro doc's timestamp may sit relative to our clock
/// before it is refused. Covers ordinary skew between the enclave host and this verifier.
pub const MAX_FUTURE_SKEW_SECS: u64 = 60;

/// Freshness of a Nitro doc at `now_secs` (wall-clock seconds since the epoch). F10: this
/// fails CLOSED. A clock that reads before the doc by more than [`MAX_FUTURE_SKEW_SECS`]
/// is either a bad clock or a future-dated doc, and neither lets us say the doc is recent,
/// so both are refused; before this, `now` fell back to 0 on a clock error and a
/// future-dated doc skipped the age check entirely.
pub fn check_nitro_freshness(
    now_secs: u64,
    doc_ts_ms: u64,
    max_age_secs: u64,
) -> Result<(), String> {
    let doc_ts = doc_ts_ms / 1000;
    if doc_ts > now_secs {
        let ahead = doc_ts - now_secs;
        if ahead > MAX_FUTURE_SKEW_SECS {
            return Err(format!(
                "Nitro doc timestamp is {ahead}s ahead of this verifier's clock (max skew {MAX_FUTURE_SKEW_SECS}s): bad clock or future-dated doc; refused"
            ));
        }
        return Ok(());
    }
    let age = now_secs - doc_ts;
    if age > max_age_secs {
        return Err(format!("stale Nitro doc: {age}s old (max {max_age_secs})"));
    }
    Ok(())
}

/// The time-independent crypto core: verifies chain + COSE signature and extracts the
/// claims, checking cert validity against the doc's OWN timestamp. Returns the claims
/// and the doc timestamp (ms). A captured fixture passes this forever.
pub fn verify_nitro_core(report: &[u8]) -> Result<(TeeReportClaims, u64), String> {
    let cose: CoseSign1 =
        ciborium::from_reader(report).map_err(|e| format!("COSE_Sign1 parse: {e}"))?;
    let protected = cose.0.into_vec();
    let payload = cose.2.into_vec();
    let signature = cose.3.into_vec();
    if signature.len() != 96 {
        return Err(format!(
            "expected a 96-byte ES384 signature, got {}",
            signature.len()
        ));
    }

    let doc: AttDoc =
        ciborium::from_reader(payload.as_slice()).map_err(|e| format!("payload parse: {e}"))?;

    // The doc's own timestamp is the reference for cert-validity (self-consistent).
    let ref_time =
        ASN1Time::from_timestamp((doc.timestamp / 1000) as i64).map_err(|e| format!("ts: {e}"))?;

    verify_cert_chain(&doc, ref_time)?;
    verify_cose_sig(&protected, &payload, &signature, doc.certificate.as_ref())?;

    let claims = TeeReportClaims {
        measurement: fold_pcrs(&doc.pcrs)?,
        report_data: extract_report_data(&doc)?,
        // ⚑ MEASURED 2026-07-30. This was `tcb_ok: true` with this same reason in a trailing
        // comment — a hardcoded pass on a field whose entire purpose is to report a policy
        // decision, read by the fail-closed `attested_data` gate as though a policy had run.
        // A Nitro attestation document carries NO microcode/firmware version: its trust is
        // the certificate chain to the pinned root (verified above) plus the PCR measurement
        // (the caller's `expected_measurement` pin). There is no rung to gate on, so the
        // honest value is the ABSENCE, not a pass — and a caller can now branch on it.
        tcb: TcbStatus::NoPolicyOnPlatform,
    };
    Ok((claims, doc.timestamp))
}

/// Verify leaf ← cabundle ← the PINNED root: byte-identical root, each link's
/// signature, and every cert's validity window at `ref_time`.
fn verify_cert_chain(doc: &AttDoc, ref_time: ASN1Time) -> Result<(), String> {
    if doc.cabundle.is_empty() {
        return Err("empty cabundle".into());
    }

    // The trust anchor is our EMBEDDED root — require the doc's cabundle[0] to be
    // byte-identical to it (the doc includes the root first).
    let pinned = Pem::iter_from_buffer(AWS_NITRO_ROOT_PEM)
        .next()
        .ok_or("no PEM in pinned root")?
        .map_err(|e| format!("pinned root PEM: {e}"))?;
    if pinned.contents.as_slice() != doc.cabundle[0].as_ref() {
        return Err("cabundle[0] is not the pinned AWS Nitro root".into());
    }

    // Parse the full chain: cabundle (root..intN) then the leaf.
    let mut chain_der: Vec<&[u8]> = doc.cabundle.iter().map(|c| c.as_ref()).collect();
    chain_der.push(doc.certificate.as_ref());

    let mut parsed = Vec::with_capacity(chain_der.len());
    for der in &chain_der {
        let (_, c) = X509Certificate::from_der(der).map_err(|e| format!("cert parse: {e}"))?;
        parsed.push(c);
    }

    for (i, cert) in parsed.iter().enumerate() {
        if !cert.validity().is_valid_at(ref_time) {
            return Err(format!("cert {i} not valid at the doc timestamp"));
        }
        // Each cert (after the root) must be signed by its predecessor's key.
        if i > 0 {
            let issuer = &parsed[i - 1];
            cert.verify_signature(Some(issuer.public_key()))
                .map_err(|e| format!("chain link {i} signature: {e:?}"))?;
        }
    }
    Ok(())
}

/// Verify the COSE_Sign1 signature over the canonical `Sig_structure` with the leaf
/// certificate's P-384 public key (ES384 = ECDSA-P384 / SHA-384).
fn verify_cose_sig(
    protected: &[u8],
    payload: &[u8],
    sig: &[u8],
    leaf_der: &[u8],
) -> Result<(), String> {
    use p384::ecdsa::signature::Verifier;
    use p384::ecdsa::{Signature, VerifyingKey};

    // Sig_structure = ["Signature1", body_protected, external_aad(empty), payload].
    let sig_structure = ciborium::value::Value::Array(vec![
        ciborium::value::Value::Text("Signature1".to_string()),
        ciborium::value::Value::Bytes(protected.to_vec()),
        ciborium::value::Value::Bytes(Vec::new()),
        ciborium::value::Value::Bytes(payload.to_vec()),
    ]);
    let mut signed = Vec::new();
    ciborium::into_writer(&sig_structure, &mut signed)
        .map_err(|e| format!("Sig_structure encode: {e}"))?;

    let (_, leaf) = X509Certificate::from_der(leaf_der).map_err(|e| format!("leaf parse: {e}"))?;
    let point = leaf.public_key().subject_public_key.data.as_ref();
    let vk = VerifyingKey::from_sec1_bytes(point).map_err(|e| format!("leaf P-384 key: {e}"))?;
    let signature = Signature::from_slice(sig).map_err(|e| format!("signature decode: {e}"))?;
    vk.verify(&signed, &signature)
        .map_err(|e| format!("COSE signature verify FAILED: {e}"))?;
    Ok(())
}

/// The enclave code identity: `SHA-256(PCR0 ‖ PCR1 ‖ PCR2)`.
fn fold_pcrs(pcrs: &BTreeMap<u8, ByteBuf>) -> Result<[u8; 32], String> {
    let mut h = Sha256::new();
    for i in [0u8, 1, 2] {
        let p = pcrs.get(&i).ok_or_else(|| format!("missing PCR{i}"))?;
        h.update(p.as_ref());
    }
    Ok(h.finalize().into())
}

/// The bound commitment: `user_data` must be exactly 32 bytes.
fn extract_report_data(doc: &AttDoc) -> Result<[u8; 32], String> {
    let ud = doc
        .user_data
        .as_ref()
        .ok_or("attestation doc carries no user_data (report_data)")?;
    if ud.len() != 32 {
        return Err(format!("user_data must be 32 bytes, got {}", ud.len()));
    }
    let mut r = [0u8; 32];
    r.copy_from_slice(ud.as_ref());
    Ok(r)
}

#[cfg(test)]
mod freshness_tests {
    use super::*;

    const DOC_MS: u64 = 1_700_000_000_000;
    const DOC_S: u64 = DOC_MS / 1000;

    #[test]
    fn fresh_doc_passes() {
        check_nitro_freshness(DOC_S, DOC_MS, 3600).unwrap();
        check_nitro_freshness(DOC_S + 3600, DOC_MS, 3600).unwrap();
        check_nitro_freshness(DOC_S - MAX_FUTURE_SKEW_SECS, DOC_MS, 3600).unwrap();
    }

    #[test]
    fn stale_doc_is_refused() {
        let e = check_nitro_freshness(DOC_S + 3601, DOC_MS, 3600).unwrap_err();
        assert!(e.contains("stale"), "{e}");
    }

    /// F10: a clock that reads 0 (the old `unwrap_or(0)` fallback) used to make every doc
    /// fresh. It is now refused.
    #[test]
    fn zeroed_clock_is_refused() {
        let e = check_nitro_freshness(0, DOC_MS, 3600).unwrap_err();
        assert!(e.contains("ahead"), "{e}");
    }

    /// F10: a future-dated doc used to skip the age check (`now > doc_ts && ...`).
    #[test]
    fn future_dated_doc_is_refused() {
        let e = check_nitro_freshness(DOC_S, DOC_MS + (MAX_FUTURE_SKEW_SECS + 1) * 1000, 3600)
            .unwrap_err();
        assert!(e.contains("ahead"), "{e}");
    }
}
