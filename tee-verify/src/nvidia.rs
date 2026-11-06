//! # NVIDIA confidential-GPU attestation (SPDM GET_MEASUREMENTS) — offline verifier.
//!
//! Until this module, `dregg-chutes-e2ee` documented a `gpu_evidence` field and never read it,
//! so "confidential GPU" meant "a CPU TD with a pinned image". This verifies the GPU's own
//! evidence, offline, fail-closed:
//!
//! 1. **Chain.** The PEM chain (leaf first, root last) must END in the PINNED
//!    `NVIDIA Device Identity CA` (byte-identical DER, embedded here), every link's signature
//!    must verify against its issuer, and every certificate must be valid at `now`.
//! 2. **Signature.** The report is `request(37 bytes) ‖ response`; the response's trailing
//!    96 bytes are a raw P-384 ECDSA signature (big-endian `r ‖ s`, SHA-384) by the LEAF key over
//!    everything before them. This is the NVIDIA local verifier's construction
//!    (`attestation/__init__.py::concatenate`).
//! 3. **Freshness.** The request's 32-byte nonce must equal the caller's fresh nonce.
//! 4. **Measurements.** The response's measurement record must parse strictly (DMTF blocks,
//!    unique indices, exact lengths), and every block must equal the caller's GOLDEN value for
//!    its index. A measured index with no golden value is a refusal unless the caller opts in.
//!
//! Format source (read, not copied): NVIDIA nvtrust `local_gpu_verifier`
//! `attestation/spdm_msrt_req_msg.py` and `spdm_msrt_resp_msg.py` (SPDM 1.1 layout:
//! version, code, param1, param2, number-of-blocks, 3-byte LE record length, record, 32-byte
//! nonce, 2-byte LE opaque length, opaque TLVs, signature).
//!
//! NOT done here (named): deriving the golden values from NVIDIA's signed RIM files (driver and
//! VBIOS SWID tags, with their own certificate chains); OCSP revocation of the device chain;
//! binding the GPU report's nonce to the CPU TD quote (the caller passes the SAME fresh nonce
//! to both, which is the binding); the meaning of individual measurement indices.

use std::collections::BTreeMap;

use p384::ecdsa::signature::Verifier;
use p384::ecdsa::{Signature, VerifyingKey};
use x509_parser::pem::Pem;
use x509_parser::prelude::*;

/// The pinned trust anchor: NVIDIA Device Identity CA (self-signed, P-384).
pub const NVIDIA_DEVICE_IDENTITY_CA_PEM: &[u8] = include_bytes!("nvidia_device_identity_ca.pem");

/// Length of the SPDM GET_MEASUREMENTS request carried at the front of the report.
pub const SPDM_REQUEST_LEN: usize = 37;
/// Raw P-384 signature length (`r ‖ s`).
pub const SIGNATURE_LEN: usize = 96;
/// SPDM nonce length.
pub const NONCE_LEN: usize = 32;
/// SPDM response code for MEASUREMENTS; request code for GET_MEASUREMENTS.
const MEASUREMENTS_RESPONSE: u8 = 0x60;
const GET_MEASUREMENTS_REQUEST: u8 = 0xE0;
/// DMTF measurement-specification bit.
const DMTF_SPEC: u8 = 1;

/// A parsed GPU attestation report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GpuReport {
    pub spdm_version: u8,
    pub request_nonce: [u8; NONCE_LEN],
    pub response_nonce: [u8; NONCE_LEN],
    /// Measurement index → DMTF measurement value (the digest bytes).
    pub measurements: BTreeMap<u8, Vec<u8>>,
    /// Opaque-data TLVs in order: (type, value). E.g. 3 = driver version, 6 = VBIOS version,
    /// 20 = FWID, 21 = protected-PCIe status (nvtrust `OpaqueData.OPAQUE_DATA_TYPES`).
    pub opaque: Vec<(u16, Vec<u8>)>,
    /// The signed prefix (`request ‖ response` minus the signature) and the signature.
    pub signed: Vec<u8>,
    pub signature: [u8; SIGNATURE_LEN],
}

impl GpuReport {
    /// The opaque value of the first TLV with `ty`, if present.
    pub fn opaque_field(&self, ty: u16) -> Option<&[u8]> {
        self.opaque
            .iter()
            .find(|(t, _)| *t == ty)
            .map(|(_, v)| v.as_slice())
    }
}

fn take<'a>(b: &'a [u8], at: &mut usize, n: usize, what: &str) -> Result<&'a [u8], String> {
    let end = at
        .checked_add(n)
        .ok_or_else(|| format!("{what}: length overflow"))?;
    let s = b
        .get(*at..end)
        .ok_or_else(|| format!("{what}: truncated at {at}"))?;
    *at = end;
    Ok(s)
}

fn le(b: &[u8]) -> usize {
    b.iter()
        .rev()
        .fold(0usize, |acc, &x| (acc << 8) | usize::from(x))
}

/// Parse strictly: every length must match exactly, and the response must end exactly at the
/// signature. Fail-closed on anything else.
pub fn parse_report(report: &[u8]) -> Result<GpuReport, String> {
    if report.len() <= SPDM_REQUEST_LEN + SIGNATURE_LEN {
        return Err("report too short".into());
    }
    let (req, resp) = report.split_at(SPDM_REQUEST_LEN);
    if req[1] != GET_MEASUREMENTS_REQUEST {
        return Err(format!(
            "request code {:#04x} is not GET_MEASUREMENTS",
            req[1]
        ));
    }
    let mut request_nonce = [0u8; NONCE_LEN];
    request_nonce.copy_from_slice(&req[4..4 + NONCE_LEN]);

    let mut at = 0usize;
    let hdr = take(resp, &mut at, 4, "response header")?;
    if hdr[0] != req[0] {
        return Err("SPDM version differs between request and response".into());
    }
    if hdr[1] != MEASUREMENTS_RESPONSE {
        return Err(format!("response code {:#04x} is not MEASUREMENTS", hdr[1]));
    }
    let nblocks = usize::from(take(resp, &mut at, 1, "block count")?[0]);
    let rec_len = le(take(resp, &mut at, 3, "record length")?);
    let record = take(resp, &mut at, rec_len, "measurement record")?;

    let mut measurements = BTreeMap::new();
    let mut r = 0usize;
    while r < record.len() {
        let index = take(record, &mut r, 1, "block index")?[0];
        let spec = take(record, &mut r, 1, "block spec")?[0];
        if spec != DMTF_SPEC {
            return Err(format!(
                "block {index}: measurement spec {spec} is not DMTF"
            ));
        }
        let size = le(take(record, &mut r, 2, "block size")?);
        let block = take(record, &mut r, size, "block body")?;
        if block.len() < 3 {
            return Err(format!("block {index}: DMTF body shorter than its header"));
        }
        let vsize = le(&block[1..3]);
        if 3 + vsize != block.len() {
            return Err(format!(
                "block {index}: DMTF value size {vsize} disagrees with block size"
            ));
        }
        if measurements.insert(index, block[3..].to_vec()).is_some() {
            return Err(format!("block {index} appears twice"));
        }
    }
    if measurements.len() != nblocks {
        return Err(format!(
            "{} blocks parsed, header says {nblocks}",
            measurements.len()
        ));
    }

    let mut response_nonce = [0u8; NONCE_LEN];
    response_nonce.copy_from_slice(take(resp, &mut at, NONCE_LEN, "response nonce")?);
    let opaque_len = le(take(resp, &mut at, 2, "opaque length")?);
    let opaque_bytes = take(resp, &mut at, opaque_len, "opaque data")?;
    let mut opaque = Vec::new();
    let mut o = 0usize;
    while o < opaque_bytes.len() {
        let ty = le(take(opaque_bytes, &mut o, 2, "opaque type")?) as u16;
        let n = le(take(opaque_bytes, &mut o, 2, "opaque size")?);
        opaque.push((ty, take(opaque_bytes, &mut o, n, "opaque value")?.to_vec()));
    }
    let sig = take(resp, &mut at, SIGNATURE_LEN, "signature")?;
    if at != resp.len() {
        return Err(format!(
            "{} trailing bytes after the signature",
            resp.len() - at
        ));
    }
    let mut signature = [0u8; SIGNATURE_LEN];
    signature.copy_from_slice(sig);
    Ok(GpuReport {
        spdm_version: req[0],
        request_nonce,
        response_nonce,
        measurements,
        opaque,
        signed: report[..report.len() - SIGNATURE_LEN].to_vec(),
        signature,
    })
}

/// Golden measurements (from NVIDIA RIMs, supplied by the caller): index → accepted values.
#[derive(Debug, Clone, Default)]
pub struct GoldenMeasurements {
    pub values: BTreeMap<u8, Vec<Vec<u8>>>,
    /// If false (the default), a measured index with no golden entry is a refusal.
    pub allow_uncovered: bool,
}

/// What a successful verification establishes.
#[derive(Debug, Clone)]
pub struct GpuVerified {
    pub report: GpuReport,
    /// SHA-256 of the leaf certificate's DER: the attesting device's identity for a registry.
    pub leaf_fingerprint: [u8; 32],
    /// Measured indices that had no golden value (empty unless `allow_uncovered`).
    pub uncovered: Vec<u8>,
}

fn pem_chain(pem: &[u8]) -> Result<Vec<Vec<u8>>, String> {
    let mut out = Vec::new();
    for p in Pem::iter_from_buffer(pem) {
        let p = p.map_err(|e| format!("chain PEM: {e}"))?;
        out.push(p.contents);
    }
    if out.is_empty() {
        return Err("empty certificate chain".into());
    }
    Ok(out)
}

/// Verify the chain (leaf first) to the pinned NVIDIA root at `now`; return the leaf key.
pub fn verify_chain(chain_pem: &[u8], now: ASN1Time) -> Result<(VerifyingKey, [u8; 32]), String> {
    use sha2::{Digest, Sha256};
    let ders = pem_chain(chain_pem)?;
    let pinned = pem_chain(NVIDIA_DEVICE_IDENTITY_CA_PEM)?;
    if ders.last().map(Vec::as_slice) != Some(pinned[0].as_slice()) {
        return Err("chain does not end in the pinned NVIDIA Device Identity CA".into());
    }
    let mut parsed = Vec::with_capacity(ders.len());
    for der in &ders {
        let (_, c) = X509Certificate::from_der(der).map_err(|e| format!("cert parse: {e}"))?;
        parsed.push(c);
    }
    for (i, cert) in parsed.iter().enumerate() {
        if !cert.validity().is_valid_at(now) {
            return Err(format!("cert {i} not valid at the reference time"));
        }
        let issuer = parsed.get(i + 1).unwrap_or(cert); // the root is self-signed
        cert.verify_signature(Some(issuer.public_key()))
            .map_err(|e| format!("chain link {i} signature: {e:?}"))?;
    }
    let leaf = &parsed[0];
    let key = VerifyingKey::from_sec1_bytes(&leaf.public_key().subject_public_key.data)
        .map_err(|e| format!("leaf key is not P-384: {e}"))?;
    let fp: [u8; 32] = Sha256::digest(&ders[0]).into();
    Ok((key, fp))
}

/// Full offline verification, fail-closed at every step.
pub fn verify_gpu_report(
    report_bytes: &[u8],
    chain_pem: &[u8],
    expected_nonce: &[u8; NONCE_LEN],
    golden: &GoldenMeasurements,
    now: ASN1Time,
) -> Result<GpuVerified, String> {
    let report = parse_report(report_bytes)?;
    let (key, leaf_fingerprint) = verify_chain(chain_pem, now)?;
    let sig =
        Signature::from_slice(&report.signature).map_err(|e| format!("signature encoding: {e}"))?;
    key.verify(&report.signed, &sig)
        .map_err(|_| "GPU report signature does not verify under the leaf key".to_string())?;
    if &report.request_nonce != expected_nonce {
        return Err("GPU report nonce is not the caller's fresh nonce (replay)".into());
    }
    let mut uncovered = Vec::new();
    for (index, value) in &report.measurements {
        match golden.values.get(index) {
            Some(accepted) => {
                if !accepted.iter().any(|g| g == value) {
                    return Err(format!(
                        "measurement {index} does not match any golden value"
                    ));
                }
            }
            None if golden.allow_uncovered => uncovered.push(*index),
            None => return Err(format!("measurement {index} has no golden value")),
        }
    }
    for index in golden.values.keys() {
        if !report.measurements.contains_key(index) {
            return Err(format!(
                "golden measurement {index} is absent from the report"
            ));
        }
    }
    Ok(GpuVerified {
        report,
        leaf_fingerprint,
        uncovered,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const REPORT_HEX: &str = include_str!("../tests/data/nvidia_hopper_attestation_report.hex");
    const CHAIN: &[u8] = include_bytes!("../tests/data/nvidia_hopper_cert_chain.pem");

    fn report() -> Vec<u8> {
        hex::decode(REPORT_HEX.trim()).expect("sample hex")
    }
    fn now() -> ASN1Time {
        ASN1Time::from_timestamp(1_793_000_000).expect("time") // 2026-10-26
    }
    fn self_golden(r: &GpuReport) -> GoldenMeasurements {
        GoldenMeasurements {
            values: r
                .measurements
                .iter()
                .map(|(k, v)| (*k, vec![v.clone()]))
                .collect(),
            allow_uncovered: false,
        }
    }

    #[test]
    fn nvidia_sample_parses_strictly() {
        let r = parse_report(&report()).expect("parses");
        assert_eq!(r.spdm_version, 0x11);
        assert_eq!(r.measurements.len(), 64);
        assert!(
            r.measurements.values().all(|v| v.len() == 48),
            "SHA-384 measurement values"
        );
        assert!(r.opaque_field(3).is_some(), "driver version TLV present");
        assert!(r.opaque_field(6).is_some(), "VBIOS version TLV present");
    }

    #[test]
    fn nvidia_sample_verifies_end_to_end() {
        let bytes = report();
        let r = parse_report(&bytes).unwrap();
        let v = verify_gpu_report(&bytes, CHAIN, &r.request_nonce, &self_golden(&r), now())
            .expect("the public NVIDIA sample verifies against the pinned root");
        assert!(v.uncovered.is_empty());
    }

    /// Falsifiers: each one must REFUSE, so the accept above is not vacuous.
    #[test]
    fn nvidia_sample_refusals() {
        let bytes = report();
        let r = parse_report(&bytes).unwrap();
        let g = self_golden(&r);
        // 1. wrong nonce: replay refused
        let mut other = r.request_nonce;
        other[0] ^= 1;
        assert!(verify_gpu_report(&bytes, CHAIN, &other, &g, now()).is_err());
        // 2. one flipped measurement byte inside the signed region: signature refuses
        let mut tampered = bytes.clone();
        tampered[SPDM_REQUEST_LEN + 8 + 4 + 3] ^= 1;
        assert!(verify_gpu_report(&tampered, CHAIN, &r.request_nonce, &g, now()).is_err());
        // 3. golden mismatch: the comparator refuses
        let mut g2 = g.clone();
        g2.values.get_mut(&1).unwrap()[0][0] ^= 1;
        assert!(verify_gpu_report(&bytes, CHAIN, &r.request_nonce, &g2, now()).is_err());
        // 4. uncovered index without opt-in: refused; with opt-in: accepted and reported
        let mut g3 = g.clone();
        g3.values.remove(&64);
        assert!(verify_gpu_report(&bytes, CHAIN, &r.request_nonce, &g3, now()).is_err());
        g3.allow_uncovered = true;
        let v = verify_gpu_report(&bytes, CHAIN, &r.request_nonce, &g3, now()).unwrap();
        assert_eq!(v.uncovered, vec![64]);
        // 5. chain that does not end in the pinned root: refused
        let chain = String::from_utf8(CHAIN.to_vec()).unwrap();
        let cut = chain.rfind("-----BEGIN CERTIFICATE-----").unwrap();
        assert!(verify_chain(chain[..cut].as_bytes(), now()).is_err());
        // 6. trailing garbage after the signature: parse refuses
        let mut long = bytes.clone();
        long.push(0);
        assert!(parse_report(&long).is_err());
    }
}
