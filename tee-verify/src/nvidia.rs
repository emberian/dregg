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
//! [`verify_gpu_evidence`] composes this with the signed RIMs ([`crate::nvidia_rim`]: the golden
//! values come from NVIDIA's driver and VBIOS manifests, not from the report) and OCSP
//! revocation of the device chain and both RIM chains ([`crate::nvidia_ocsp`]), all at one
//! reference time.
//!
//! NOT done here (named): binding the GPU report's nonce to the CPU TD quote (the caller passes
//! the SAME fresh nonce to both, which is the binding); the meaning of individual measurement
//! indices; fetching (RIMs and OCSP responses are inputs).

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

/// Everything a GPU attests with, as the relying party receives it.
#[derive(Debug, Clone)]
pub struct GpuEvidence {
    /// The SPDM report (request ‖ response), raw bytes.
    pub report: Vec<u8>,
    /// The device certificate chain, PEM, leaf first.
    pub chain_pem: Vec<u8>,
    /// The driver and VBIOS RIMs (signed SWID tags) for the versions the report names.
    pub driver_rim: Vec<u8>,
    pub vbios_rim: Vec<u8>,
    /// OCSP responses covering the device chain (all but its leaf) and both RIM chains.
    pub ocsp: Vec<crate::nvidia_ocsp::OcspEvidence>,
}

/// What [`verify_gpu_evidence`] establishes.
#[derive(Debug, Clone)]
pub struct GpuEvidenceVerified {
    pub gpu: GpuVerified,
    pub driver_version: String,
    pub vbios_version: String,
    pub driver_rim_signer: [u8; 32],
    pub vbios_rim_signer: [u8; 32],
}

/// The product whose RIMs this verifier accepts.
pub const PRODUCT_GH100: &str = "GH100";

/// Composed, fail-closed, at ONE reference time `now`:
/// report chain + signature + nonce; device chain not revoked; VBIOS RIM signed, chained and
/// not revoked; driver RIM likewise; RIM versions equal the report's; every measurement equals
/// a RIM-derived golden value (inactive indices must be zero).
pub fn verify_gpu_evidence(
    ev: &GpuEvidence,
    expected_nonce: &[u8; NONCE_LEN],
    ocsp_policy: &crate::nvidia_ocsp::OcspPolicy,
    now: ASN1Time,
) -> Result<GpuEvidenceVerified, String> {
    use crate::nvidia_ocsp::verify_chain_not_revoked;
    use crate::nvidia_rim::{goldens_from_rims, verify_rim};
    let report = parse_report(&ev.report)?;
    // Chain, signature and nonce first (the goldens are checked last, below).
    let probe = GoldenMeasurements {
        values: BTreeMap::new(),
        allow_uncovered: true,
    };
    verify_gpu_report(&ev.report, &ev.chain_pem, expected_nonce, &probe, now)?;
    let device_chain = pem_chain(&ev.chain_pem)?;
    check_fwid(&report, &device_chain[0])?;
    verify_chain_not_revoked(&device_chain, 1, &ev.ocsp, ocsp_policy, now)
        .map_err(|e| format!("device chain: {e}"))?;
    let vbios = verify_rim(&ev.vbios_rim, now).map_err(|e| format!("VBIOS RIM: {e}"))?;
    verify_chain_not_revoked(&vbios.chain_der, 0, &ev.ocsp, ocsp_policy, now)
        .map_err(|e| format!("VBIOS RIM chain: {e}"))?;
    let driver = verify_rim(&ev.driver_rim, now).map_err(|e| format!("driver RIM: {e}"))?;
    verify_chain_not_revoked(&driver.chain_der, 0, &ev.ocsp, ocsp_policy, now)
        .map_err(|e| format!("driver RIM chain: {e}"))?;
    let golden = goldens_from_rims(&report, &driver, &vbios, PRODUCT_GH100)?;
    let gpu = verify_gpu_report(&ev.report, &ev.chain_pem, expected_nonce, &golden, now)?;
    Ok(GpuEvidenceVerified {
        driver_version: driver.colloquial_version,
        vbios_version: vbios.colloquial_version,
        driver_rim_signer: driver.signer_fingerprint,
        vbios_rim_signer: vbios.signer_fingerprint,
        gpu,
    })
}

/// Opaque TLV 20: the firmware ID the GPU reports.
pub const OPAQUE_FWID: u16 = 20;
const OID_TCG_DICE_FWID: &str = "2.23.133.5.4.1";
const OID_TCG_DICE_FWID_1: &str = "2.23.133.5.4.1.1";

/// The report's FWID must equal the FWID the attestation (leaf) certificate carries in its TCG
/// DICE extension (Hopper: the extension value's last 48 bytes, as nvtrust `extract_fwid`).
/// Stricter than nvtrust, which skips the check when the report has no FWID: here a missing
/// FWID on either side is a refusal.
pub fn check_fwid(report: &GpuReport, leaf_der: &[u8]) -> Result<(), String> {
    let fwid = report
        .opaque_field(OPAQUE_FWID)
        .ok_or_else(|| "report carries no FWID".to_string())?;
    if fwid.len() != 48 {
        return Err(format!("report FWID is {} bytes, expected 48", fwid.len()));
    }
    let (_, leaf) = X509Certificate::from_der(leaf_der).map_err(|e| format!("leaf parse: {e}"))?;
    let mut found = None;
    for ext in leaf.extensions() {
        let oid = ext.oid.to_id_string();
        if oid == OID_TCG_DICE_FWID || oid == OID_TCG_DICE_FWID_1 {
            if found.is_some() {
                return Err("leaf carries more than one FWID extension".into());
            }
            found = Some(ext.value);
        }
    }
    let v = found.ok_or_else(|| "leaf certificate carries no FWID extension".to_string())?;
    if v.len() < 48 || &v[v.len() - 48..] != fwid {
        return Err("report FWID differs from the attestation certificate's FWID".into());
    }
    Ok(())
}

/// Opaque TLVs naming the board, for the RIM service ids (nvtrust `get_*_rim_file_id`).
pub const OPAQUE_CHIP_SKU: u16 = 15;
pub const OPAQUE_PROJECT: u16 = 17;
pub const OPAQUE_PROJECT_SKU: u16 = 18;

fn opaque_ascii(r: &GpuReport, ty: u16, what: &str) -> Result<String, String> {
    let v = r
        .opaque_field(ty)
        .ok_or_else(|| format!("report carries no {what}"))?;
    let v = v.split(|&b| b == 0).next().unwrap_or(&[]);
    let s = std::str::from_utf8(v)
        .map_err(|_| format!("{what} is not ASCII"))?
        .trim();
    if s.is_empty() || !s.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'.') {
        return Err(format!(
            "{what} {s:?} is empty or has unexpected characters"
        ));
    }
    Ok(s.to_ascii_uppercase())
}

/// The NVIDIA RIM service ids (driver, VBIOS) for the versions and board a Hopper report names.
/// These choose which manifests to fetch; they are not a trust step (the verifier re-binds the
/// versions from the signed RIMs to the report).
pub fn rim_ids(report: &GpuReport) -> Result<(String, String), String> {
    let driver = crate::nvidia_rim::report_driver_version(report)?;
    let vbios = crate::nvidia_rim::report_vbios_version(report)?
        .replace('.', "")
        .to_ascii_uppercase();
    Ok((
        format!("NV_GPU_DRIVER_{PRODUCT_GH100}_{driver}"),
        format!(
            "NV_GPU_VBIOS_{}_{}_{}_{vbios}",
            opaque_ascii(report, OPAQUE_PROJECT, "project")?,
            opaque_ascii(report, OPAQUE_PROJECT_SKU, "project SKU")?,
            opaque_ascii(report, OPAQUE_CHIP_SKU, "chip SKU")?
        ),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    const REPORT_HEX: &str = include_str!("../tests/data/nvidia_hopper_attestation_report.hex");
    const CHAIN: &[u8] = include_bytes!("../tests/data/nvidia_hopper_cert_chain.pem");

    fn report() -> Vec<u8> {
        hex::decode(REPORT_HEX.trim()).expect("sample hex")
    }
    /// 2026-03-01T00:00:00Z: inside every device and RIM certificate's validity window.
    fn now() -> ASN1Time {
        ASN1Time::from_timestamp(1_772_323_200).expect("time")
    }
    const DRIVER_RIM: &[u8] =
        include_bytes!("../tests/data/nvidia_rim_driver_GH100_550.90.07.swidtag");
    const VBIOS_RIM: &[u8] =
        include_bytes!("../tests/data/nvidia_rim_vbios_1010_0200_882_96009F0001.swidtag");
    /// The goldens from NVIDIA's signed RIMs for the sample's driver and VBIOS.
    fn rim_golden(r: &GpuReport) -> GoldenMeasurements {
        let d = crate::nvidia_rim::verify_rim(DRIVER_RIM, now()).expect("driver RIM");
        let v = crate::nvidia_rim::verify_rim(VBIOS_RIM, now()).expect("VBIOS RIM");
        crate::nvidia_rim::goldens_from_rims(r, &d, &v, PRODUCT_GH100).expect("goldens")
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
        let v = verify_gpu_report(&bytes, CHAIN, &r.request_nonce, &rim_golden(&r), now())
            .expect("the public NVIDIA sample verifies against the pinned root and the RIMs");
        assert!(v.uncovered.is_empty());
        assert_eq!(v.report.measurements.len(), 64);
    }

    /// Falsifiers: each one must REFUSE, so the accept above is not vacuous.
    #[test]
    fn nvidia_sample_refusals() {
        let bytes = report();
        let r = parse_report(&bytes).unwrap();
        let g = rim_golden(&r);
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
        // 7. RIMs swapped: the version binding refuses
        let d = crate::nvidia_rim::verify_rim(DRIVER_RIM, now()).unwrap();
        let v = crate::nvidia_rim::verify_rim(VBIOS_RIM, now()).unwrap();
        assert!(crate::nvidia_rim::goldens_from_rims(&r, &v, &d, PRODUCT_GH100).is_err());
        // 8. a non-zero value where neither RIM expects a measurement: refused
        let inactive = *g
            .values
            .iter()
            .find(|(_, a)| a == &&vec![vec![0u8; 48]])
            .unwrap()
            .0;
        let mut g4 = g.clone();
        g4.values.insert(inactive, vec![vec![1u8; 48]]);
        assert!(verify_gpu_report(&bytes, CHAIN, &r.request_nonce, &g4, now()).is_err());
    }

    #[test]
    fn nvidia_fwid_and_rim_ids() {
        let r = parse_report(&report()).unwrap();
        let chain = pem_chain(CHAIN).unwrap();
        check_fwid(&r, &chain[0]).expect("sample FWID matches its leaf");
        // a different FWID in the report: refused
        let mut r2 = r.clone();
        for (t, v) in r2.opaque.iter_mut() {
            if *t == OPAQUE_FWID {
                v[0] ^= 1;
            }
        }
        assert!(check_fwid(&r2, &chain[0]).is_err());
        // no FWID extension (a non-leaf certificate): refused
        assert!(check_fwid(&r, &chain[1]).is_err());
        assert_eq!(
            rim_ids(&r).unwrap(),
            (
                "NV_GPU_DRIVER_GH100_550.90.07".to_string(),
                "NV_GPU_VBIOS_1010_0200_882_96009F0001".to_string()
            )
        );
    }

    /// Both RIM signing chains are shown unrevoked by the captured responses.
    #[test]
    fn nvidia_rim_chains_not_revoked() {
        use crate::nvidia_ocsp::tests::{evidence, t2, POLICY};
        use crate::nvidia_ocsp::verify_chain_not_revoked;
        for (rim, prefix) in [(DRIVER_RIM, "driver_svc"), (VBIOS_RIM, "vbios_svc")] {
            let chain = crate::nvidia_rim::verify_rim(rim, now()).unwrap().chain_der;
            let ev: Vec<_> = (0..3).map(|i| evidence(&format!("{prefix}_{i}"))).collect();
            verify_chain_not_revoked(&chain, 0, &ev, &POLICY, t2()).expect(prefix);
        }
    }

    /// The composed verifier at the OCSP capture time. The public sample cannot pass it at
    /// ANY single instant: NVIDIA's RIM service still serves the driver 550.90.07 RIM signed
    /// by a certificate that expired 2026-06-01, and the OCSP responses are from 2026-11-06.
    /// So the composed check must refuse, and must refuse at the driver RIM, after the report,
    /// the device-chain revocation, the VBIOS RIM and its revocation all passed.
    #[test]
    fn nvidia_evidence_composed_refuses_expired_driver_rim() {
        use crate::nvidia_ocsp::tests::{evidence, t2, POLICY};
        let names = [
            "device_1",
            "device_2",
            "device_3",
            "vbios_svc_0",
            "vbios_svc_1",
            "vbios_svc_2",
            "driver_svc_0",
            "driver_svc_1",
            "driver_svc_2",
        ];
        let ev = GpuEvidence {
            report: report(),
            chain_pem: CHAIN.to_vec(),
            driver_rim: DRIVER_RIM.to_vec(),
            vbios_rim: VBIOS_RIM.to_vec(),
            ocsp: names.map(evidence).into(),
        };
        let nonce = parse_report(&ev.report).unwrap().request_nonce;
        let err = verify_gpu_evidence(&ev, &nonce, &POLICY, t2()).unwrap_err();
        assert!(err.starts_with("driver RIM: RIM chain cert 0"), "{err}");
        // without the VBIOS chain's responses it refuses earlier, at the VBIOS RIM chain
        let mut ev2 = ev.clone();
        ev2.ocsp.truncate(3);
        let err = verify_gpu_evidence(&ev2, &nonce, &POLICY, t2()).unwrap_err();
        assert!(err.starts_with("VBIOS RIM chain"), "{err}");
        // and at the reference time where the RIMs are valid, the OCSP responses are not yet
        let err = verify_gpu_evidence(&ev, &nonce, &POLICY, now()).unwrap_err();
        assert!(err.starts_with("device chain"), "{err}");
    }
}
