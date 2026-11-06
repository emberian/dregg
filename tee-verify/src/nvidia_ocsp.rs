//! # OCSP revocation of NVIDIA certificate chains (device identity and RIM signing) — offline.
//!
//! NVIDIA runs one OCSP service (`ocsp.ndis.nvidia.com`) for both PKIs. Responses are signed
//! by a delegated responder certificate carried in the response. A certificate is accepted as
//! not revoked only if a supplied response, verified here at `now`, says so:
//!
//! 1. The response is `successful` and of type `id-pkix-ocsp-basic`; DER is parsed strictly.
//! 2. The signer is either the issuer itself, or the ONE certificate in the response, which
//!    must be signed by the issuer, carry `id-kp-OCSPSigning`, and be valid at `now`
//!    (RFC 6960 §4.2.2.2, delegated responder).
//! 3. The signature over `tbsResponseData` verifies (ECDSA P-384 / SHA-384 or P-256 / SHA-256).
//! 4. Exactly one `SingleResponse` names this certificate: its `CertID` hash algorithm is
//!    SHA-256 or SHA-384 and `issuerNameHash`, `issuerKeyHash` and `serialNumber` match values
//!    computed here from the certificate and its issuer.
//! 5. Its status is `good` (`revoked` and `unknown` both refuse; nvtrust's optional
//!    "certificate hold" leniency for RIM certificates is not offered).
//! 6. Freshness: `thisUpdate <= now <= nextUpdate` (a response without `nextUpdate` refuses)
//!    and `now - thisUpdate <= max_age`.
//! 7. If the caller supplies the nonce it sent, the response's nonce extension must equal it.
//!
//! Compared with nvtrust's `ocsp_certificate_chain_validation`, steps 4 and 6 are added: that
//! code takes the status of the response's single entry without matching it to the
//! certificate it asked about, and does not read `thisUpdate`/`nextUpdate`.

use p384::ecdsa::signature::Verifier as _;
use sha2::{Digest, Sha256, Sha384};
use x509_parser::prelude::*;

const OID_OCSP_BASIC: &[u8] = &[0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x30, 0x01, 0x01];
const OID_OCSP_NONCE: &[u8] = &[0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x30, 0x01, 0x02];
const OID_SHA256: &[u8] = &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01];
const OID_SHA384: &[u8] = &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02];
const OID_ECDSA_SHA256: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02];
const OID_ECDSA_SHA384: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x03];

// ---------------------------------------------------------------------------------------
// Minimal strict DER reader
// ---------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct Tlv<'a> {
    tag: u8,
    /// The whole encoding (tag, length, value).
    raw: &'a [u8],
    value: &'a [u8],
}

fn read_tlv<'a>(b: &'a [u8]) -> Result<(Tlv<'a>, &'a [u8]), String> {
    let tag = *b.first().ok_or("der: empty")?;
    if tag & 0x1f == 0x1f {
        return Err("der: multi-byte tags are not used by OCSP".into());
    }
    let l0 = *b.get(1).ok_or("der: no length")?;
    let (len, hdr) = if l0 < 0x80 {
        (usize::from(l0), 2)
    } else {
        let n = usize::from(l0 & 0x7f);
        if n == 0 || n > 4 {
            return Err("der: indefinite or oversized length".into());
        }
        let lb = b.get(2..2 + n).ok_or("der: truncated length")?;
        if lb[0] == 0 {
            return Err("der: non-minimal length".into());
        }
        let len = lb.iter().fold(0usize, |a, &x| (a << 8) | usize::from(x));
        if len < 0x80 {
            return Err("der: non-minimal length".into());
        }
        (len, 2 + n)
    };
    let end = hdr.checked_add(len).ok_or("der: length overflow")?;
    let raw = b.get(..end).ok_or("der: truncated value")?;
    Ok((
        Tlv {
            tag,
            raw,
            value: &raw[hdr..],
        },
        &b[end..],
    ))
}

fn expect<'a>(b: &'a [u8], tag: u8, what: &str) -> Result<(Tlv<'a>, &'a [u8]), String> {
    let (t, rest) = read_tlv(b)?;
    if t.tag != tag {
        return Err(format!(
            "ocsp: {what}: tag {:#04x}, expected {tag:#04x}",
            t.tag
        ));
    }
    Ok((t, rest))
}

fn only<'a>(b: &'a [u8], tag: u8, what: &str) -> Result<Tlv<'a>, String> {
    let (t, rest) = expect(b, tag, what)?;
    if !rest.is_empty() {
        return Err(format!("ocsp: trailing bytes after {what}"));
    }
    Ok(t)
}

fn seq_items(b: &[u8]) -> Result<Vec<Tlv<'_>>, String> {
    let mut out = Vec::new();
    let mut rest = b;
    while !rest.is_empty() {
        let (t, r) = read_tlv(rest)?;
        out.push(t);
        rest = r;
    }
    Ok(out)
}

/// The OID inside an AlgorithmIdentifier (parameters must be absent or NULL).
fn alg_oid<'a>(t: &Tlv<'a>) -> Result<&'a [u8], String> {
    if t.tag != 0x30 {
        return Err("ocsp: AlgorithmIdentifier is not a SEQUENCE".into());
    }
    let items = seq_items(t.value)?;
    match items.as_slice() {
        [oid] if oid.tag == 0x06 => Ok(oid.value),
        [oid, null] if oid.tag == 0x06 && null.tag == 0x05 && null.value.is_empty() => {
            Ok(oid.value)
        }
        _ => Err("ocsp: unexpected AlgorithmIdentifier parameters".into()),
    }
}

/// GeneralizedTime `YYYYMMDDHHMMSSZ` (DER form, no fraction) to Unix seconds.
fn gen_time(t: &Tlv<'_>) -> Result<i64, String> {
    if t.tag != 0x18 {
        return Err("ocsp: expected GeneralizedTime".into());
    }
    let s = std::str::from_utf8(t.value).map_err(|_| "ocsp: time not ASCII")?;
    if s.len() != 15 || !s.ends_with('Z') || !s[..14].bytes().all(|c| c.is_ascii_digit()) {
        return Err(format!("ocsp: time {s:?} is not YYYYMMDDHHMMSSZ"));
    }
    let n = |a: usize, b: usize| s[a..b].parse::<i64>().unwrap();
    let (y, mo, d, h, mi, se) = (n(0, 4), n(4, 6), n(6, 8), n(8, 10), n(10, 12), n(12, 14));
    if !(1..=12).contains(&mo) || !(1..=31).contains(&d) || h > 23 || mi > 59 || se > 59 {
        return Err(format!("ocsp: time {s:?} out of range"));
    }
    // days from civil (Howard Hinnant's algorithm)
    let yy = if mo <= 2 { y - 1 } else { y };
    let era = yy.div_euclid(400);
    let yoe = yy - era * 400;
    let mp = (mo + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    let days = era * 146_097 + doe - 719_468;
    Ok(days * 86_400 + h * 3_600 + mi * 60 + se)
}

/// Strip leading zero octets of a DER INTEGER's content (keeping one), for comparison.
fn int_bytes(v: &[u8]) -> &[u8] {
    let mut v = v;
    while v.len() > 1 && v[0] == 0 {
        v = &v[1..];
    }
    v
}

// ---------------------------------------------------------------------------------------
// Verification
// ---------------------------------------------------------------------------------------

/// What the caller requires of a response.
#[derive(Debug, Clone, Copy)]
pub struct OcspPolicy {
    /// Maximum age of `thisUpdate` at `now`, in seconds.
    pub max_age_secs: i64,
}

/// A response the caller obtained, with the nonce it sent (if it sent one and kept it).
#[derive(Debug, Clone)]
pub struct OcspEvidence {
    pub response_der: Vec<u8>,
    pub nonce: Option<Vec<u8>>,
}

fn verify_sig(
    spki: &SubjectPublicKeyInfo<'_>,
    alg: &[u8],
    msg: &[u8],
    sig_der: &[u8],
) -> Result<(), String> {
    let key = &spki.subject_public_key.data;
    match alg {
        OID_ECDSA_SHA384 => {
            let k = p384::ecdsa::VerifyingKey::from_sec1_bytes(key)
                .map_err(|_| "ocsp: signer key is not P-384")?;
            let s = p384::ecdsa::Signature::from_der(sig_der)
                .map_err(|_| "ocsp: bad signature encoding")?;
            k.verify(msg, &s)
                .map_err(|_| "ocsp: response signature does not verify".to_string())
        }
        OID_ECDSA_SHA256 => {
            Err("ocsp: ECDSA-SHA256 responses are not used by NVIDIA; refused".into())
        }
        _ => Err("ocsp: unsupported signature algorithm".into()),
    }
}

/// Verify that `cert` (issued by `issuer`) is not revoked according to `ev` at `now`.
/// Returns the response's `thisUpdate` (Unix seconds).
pub fn verify_ocsp(
    cert_der: &[u8],
    issuer_der: &[u8],
    ev: &OcspEvidence,
    policy: &OcspPolicy,
    now: ASN1Time,
) -> Result<i64, String> {
    let (_, cert) =
        X509Certificate::from_der(cert_der).map_err(|e| format!("ocsp: cert parse: {e}"))?;
    let (_, issuer) =
        X509Certificate::from_der(issuer_der).map_err(|e| format!("ocsp: issuer parse: {e}"))?;
    if cert.issuer().as_raw() != issuer.subject().as_raw() {
        return Err("ocsp: the named issuer did not issue this certificate".into());
    }

    // 1. OCSPResponse → BasicOCSPResponse
    let resp = only(&ev.response_der, 0x30, "OCSPResponse")?;
    let (status, rest) = expect(resp.value, 0x0a, "responseStatus")?;
    if status.value != [0] {
        return Err(format!(
            "ocsp: responseStatus {:?} is not successful",
            status.value
        ));
    }
    let rb = only(rest, 0xa0, "responseBytes")?;
    let rb = only(rb.value, 0x30, "ResponseBytes")?;
    let (rtype, rest) = expect(rb.value, 0x06, "responseType")?;
    if rtype.value != OID_OCSP_BASIC {
        return Err("ocsp: response type is not id-pkix-ocsp-basic".into());
    }
    let octets = only(rest, 0x04, "response")?;
    let basic = only(octets.value, 0x30, "BasicOCSPResponse")?;
    let (tbs, rest) = expect(basic.value, 0x30, "tbsResponseData")?;
    let (sig_alg, rest) = expect(rest, 0x30, "signatureAlgorithm")?;
    let sig_alg = alg_oid(&sig_alg)?;
    let (sig_bits, rest) = expect(rest, 0x03, "signature")?;
    if sig_bits.value.first() != Some(&0) {
        return Err("ocsp: signature BIT STRING has unused bits".into());
    }
    let sig_der = &sig_bits.value[1..];
    let mut responder_ders: Vec<&[u8]> = Vec::new();
    if !rest.is_empty() {
        let certs = only(rest, 0xa0, "certs")?;
        let certs = only(certs.value, 0x30, "certs SEQUENCE")?;
        for c in seq_items(certs.value)? {
            responder_ders.push(c.raw);
        }
    }

    // 2. the signer, and 3. the signature
    match responder_ders.as_slice() {
        [] => verify_sig(issuer.public_key(), sig_alg, tbs.raw, sig_der)?,
        [rder] => {
            let (r_rest, responder) = X509Certificate::from_der(rder)
                .map_err(|e| format!("ocsp: responder parse: {e}"))?;
            if !r_rest.is_empty() {
                return Err("ocsp: responder certificate has trailing bytes".into());
            }
            if responder.issuer().as_raw() != issuer.subject().as_raw() {
                return Err("ocsp: responder was not issued by the certificate's issuer".into());
            }
            responder
                .verify_signature(Some(issuer.public_key()))
                .map_err(|_| {
                    "ocsp: responder certificate is not signed by the issuer".to_string()
                })?;
            let ocsp_signing = matches!(
                responder.extended_key_usage(),
                Ok(Some(eku)) if eku.value.ocsp_signing
            );
            if !ocsp_signing {
                return Err("ocsp: responder certificate lacks id-kp-OCSPSigning".into());
            }
            if !responder.validity().is_valid_at(now) {
                return Err("ocsp: responder certificate not valid at the reference time".into());
            }
            verify_sig(responder.public_key(), sig_alg, tbs.raw, sig_der)?;
        }
        _ => return Err("ocsp: more than one responder certificate".into()),
    }

    // ResponseData
    let mut items = seq_items(tbs.value)?.into_iter().peekable();
    if items.peek().map(|t| t.tag) == Some(0xa0) {
        let v = items.next().unwrap();
        if only(v.value, 0x02, "version")?.value != [0] {
            return Err("ocsp: unsupported ResponseData version".into());
        }
    }
    match items.next() {
        Some(t) if t.tag == 0xa1 || t.tag == 0xa2 => {}
        _ => return Err("ocsp: missing responderID".into()),
    }
    let produced = items.next().ok_or("ocsp: missing producedAt")?;
    gen_time(&produced)?;
    let responses = items
        .next()
        .filter(|t| t.tag == 0x30)
        .ok_or("ocsp: missing responses")?;
    let extensions = match items.next() {
        Some(t) if t.tag == 0xa1 => Some(t),
        None => None,
        Some(_) => return Err("ocsp: unexpected field in ResponseData".into()),
    };
    if items.next().is_some() {
        return Err("ocsp: trailing fields in ResponseData".into());
    }

    // 4. the one SingleResponse naming this certificate
    let mut matched = Vec::new();
    for single in seq_items(responses.value)? {
        if single.tag != 0x30 {
            return Err("ocsp: SingleResponse is not a SEQUENCE".into());
        }
        let f = seq_items(single.value)?;
        let cert_id = f
            .first()
            .filter(|t| t.tag == 0x30)
            .ok_or("ocsp: missing CertID")?;
        let id = seq_items(cert_id.value)?;
        let [halg, name_hash, key_hash, serial] = id.as_slice() else {
            return Err("ocsp: CertID has the wrong shape".into());
        };
        if name_hash.tag != 0x04 || key_hash.tag != 0x04 || serial.tag != 0x02 {
            return Err("ocsp: CertID field types".into());
        }
        let (want_name, want_key): (Vec<u8>, Vec<u8>) = match alg_oid(halg)? {
            OID_SHA384 => (
                Sha384::digest(issuer.subject().as_raw()).to_vec(),
                Sha384::digest(&issuer.public_key().subject_public_key.data).to_vec(),
            ),
            OID_SHA256 => (
                Sha256::digest(issuer.subject().as_raw()).to_vec(),
                Sha256::digest(&issuer.public_key().subject_public_key.data).to_vec(),
            ),
            _ => continue, // a CertID under a hash we do not compute cannot name our cert
        };
        if name_hash.value == want_name.as_slice()
            && key_hash.value == want_key.as_slice()
            && int_bytes(serial.value) == int_bytes(cert.raw_serial())
        {
            matched.push(f);
        }
    }
    let f = match matched.as_slice() {
        [f] => f,
        [] => return Err("ocsp: no SingleResponse names this certificate".into()),
        _ => return Err("ocsp: more than one SingleResponse names this certificate".into()),
    };

    // 5. status
    let status = f.get(1).ok_or("ocsp: missing certStatus")?;
    match status.tag {
        0x80 if status.value.is_empty() => {}
        0xa1 => return Err("ocsp: certificate is REVOKED".into()),
        0x82 => return Err("ocsp: certificate status is UNKNOWN".into()),
        _ => return Err("ocsp: malformed certStatus".into()),
    }

    // 6. freshness
    let this_update = gen_time(f.get(2).ok_or("ocsp: missing thisUpdate")?)?;
    let next = f
        .get(3)
        .filter(|t| t.tag == 0xa0)
        .ok_or("ocsp: response has no nextUpdate; refused")?;
    let next_update = gen_time(&only(next.value, 0x18, "nextUpdate")?)?;
    let now_s = now.timestamp();
    if now_s < this_update {
        return Err("ocsp: response thisUpdate is after the reference time".into());
    }
    if now_s > next_update {
        return Err("ocsp: response is past its nextUpdate (stale)".into());
    }
    if now_s - this_update > policy.max_age_secs {
        return Err("ocsp: response is older than the policy's maximum age".into());
    }

    // 7. nonce
    if let Some(want) = &ev.nonce {
        let exts = extensions.ok_or("ocsp: response has no extensions, so no nonce")?;
        let exts = only(exts.value, 0x30, "responseExtensions")?;
        let mut found = None;
        for ext in seq_items(exts.value)? {
            let parts = seq_items(ext.value)?;
            if parts.first().map(|t| (t.tag, t.value)) == Some((0x06, OID_OCSP_NONCE)) {
                let val = parts
                    .last()
                    .filter(|t| t.tag == 0x04)
                    .ok_or("ocsp: nonce extnValue")?;
                // RFC 8954: extnValue wraps an OCTET STRING holding the nonce.
                let inner = only(val.value, 0x04, "nonce")?;
                found = Some(inner.value);
            }
        }
        if found != Some(want.as_slice()) {
            return Err("ocsp: response nonce is not the nonce sent".into());
        }
    }
    Ok(this_update)
}

fn der(tag: u8, value: &[u8]) -> Vec<u8> {
    let mut out = vec![tag];
    let n = value.len();
    if n < 0x80 {
        out.push(n as u8);
    } else {
        let bytes: Vec<u8> = n
            .to_be_bytes()
            .into_iter()
            .skip_while(|&b| b == 0)
            .collect();
        out.push(0x80 | bytes.len() as u8);
        out.extend_from_slice(&bytes);
    }
    out.extend_from_slice(value);
    out
}

/// The DER OCSP request nvtrust sends: one SHA-384 `CertID` for `cert` under `issuer`, and a
/// critical nonce extension (RFC 8954 form). Building it is not a trust step; it is here so a
/// fetcher and the verifier compute the same `CertID`.
pub fn build_ocsp_request(
    cert_der: &[u8],
    issuer_der: &[u8],
    nonce: &[u8],
) -> Result<Vec<u8>, String> {
    let (_, cert) =
        X509Certificate::from_der(cert_der).map_err(|e| format!("ocsp: cert parse: {e}"))?;
    let (_, issuer) =
        X509Certificate::from_der(issuer_der).map_err(|e| format!("ocsp: issuer parse: {e}"))?;
    if cert.issuer().as_raw() != issuer.subject().as_raw() {
        return Err("ocsp: the named issuer did not issue this certificate".into());
    }
    let alg = der(0x30, &[der(0x06, OID_SHA384), vec![0x05, 0x00]].concat());
    let serial = cert.raw_serial();
    let serial = if serial.first().is_some_and(|&b| b & 0x80 != 0) {
        [&[0u8][..], serial].concat()
    } else {
        serial.to_vec()
    };
    let cert_id = der(
        0x30,
        &[
            alg,
            der(0x04, &Sha384::digest(issuer.subject().as_raw())),
            der(
                0x04,
                &Sha384::digest(&issuer.public_key().subject_public_key.data),
            ),
            der(0x02, &serial),
        ]
        .concat(),
    );
    let request_list = der(0x30, &der(0x30, &cert_id));
    let nonce_ext = der(
        0x30,
        &[
            der(0x06, OID_OCSP_NONCE),
            vec![0x01, 0x01, 0xff],
            der(0x04, &der(0x04, nonce)),
        ]
        .concat(),
    );
    let exts = der(0xa2, &der(0x30, &nonce_ext));
    Ok(der(0x30, &der(0x30, &[request_list, exts].concat())))
}

/// Every certificate `chain[i]` for `start <= i < chain.len() - 1` (leaf first, root last;
/// the root is the pinned anchor and is not checked) must be shown not revoked by one of
/// `evidence`. The device chain uses `start = 1`: its leaf is generated on the GPU and is not
/// in NVIDIA's responder (as in nvtrust).
pub fn verify_chain_not_revoked(
    chain_der: &[Vec<u8>],
    start: usize,
    evidence: &[OcspEvidence],
    policy: &OcspPolicy,
    now: ASN1Time,
) -> Result<(), String> {
    if chain_der.len() < 2 || start >= chain_der.len() - 1 {
        return Err("ocsp: chain has no certificate to check".into());
    }
    for i in start..chain_der.len() - 1 {
        let mut last_err = String::from("ocsp: no response supplied");
        let ok = evidence.iter().any(|ev| {
            match verify_ocsp(&chain_der[i], &chain_der[i + 1], ev, policy, now) {
                Ok(_) => true,
                Err(e) => {
                    last_err = e;
                    false
                }
            }
        });
        if !ok {
            return Err(format!("chain cert {i}: not shown unrevoked ({last_err})"));
        }
    }
    Ok(())
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub(crate) fn evidence(name: &str) -> OcspEvidence {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/nvidia_ocsp");
        let der = std::fs::read(format!("{dir}/{name}.der")).unwrap();
        let nonces = std::fs::read_to_string(format!("{dir}/nonces.txt")).unwrap();
        let nonce = nonces
            .lines()
            .find_map(|l| l.strip_prefix(&format!("{name} ")))
            .map(|h| hex::decode(h).unwrap());
        OcspEvidence {
            response_der: der,
            nonce,
        }
    }

    /// 2026-11-06T06:31:44Z: one hour after the captured responses' thisUpdate.
    pub(crate) fn t2() -> ASN1Time {
        ASN1Time::from_timestamp(1_793_946_704).unwrap()
    }
    pub(crate) const POLICY: OcspPolicy = OcspPolicy {
        max_age_secs: 24 * 3600,
    };

    fn device_chain() -> Vec<Vec<u8>> {
        let pem = include_bytes!("../tests/data/nvidia_hopper_cert_chain.pem");
        x509_parser::pem::Pem::iter_from_buffer(pem)
            .map(|p| p.unwrap().contents)
            .collect()
    }

    /// The request builder is byte-identical to the request Python `cryptography` built for
    /// the captured `device_1` response (same nonce).
    #[test]
    fn nvidia_ocsp_request_matches_reference() {
        let chain = device_chain();
        let ev = evidence("device_1");
        let req = build_ocsp_request(&chain[1], &chain[2], ev.nonce.as_ref().unwrap()).unwrap();
        let want = include_bytes!("../tests/data/nvidia_ocsp/device_1.req.der");
        assert_eq!(req.as_slice(), want.as_slice());
    }

    #[test]
    fn nvidia_ocsp_device_chain_good() {
        let chain = device_chain();
        let ev: Vec<_> = ["device_1", "device_2", "device_3"].map(evidence).into();
        verify_chain_not_revoked(&chain, 1, &ev, &POLICY, t2()).expect("device chain unrevoked");
    }

    /// Each must refuse, so the accept above is not vacuous.
    #[test]
    fn nvidia_ocsp_refusals() {
        let chain = device_chain();
        let ev1 = evidence("device_1");
        // a response about a different certificate (CertID mismatch)
        let other = evidence("device_2");
        assert!(verify_ocsp(&chain[1], &chain[2], &other, &POLICY, t2()).is_err());
        // a missing response for one certificate in the chain
        let ev: Vec<_> = ["device_1", "device_3"].map(evidence).into();
        assert!(verify_chain_not_revoked(&chain, 1, &ev, &POLICY, t2()).is_err());
        // stale: past nextUpdate
        let late = ASN1Time::from_timestamp(1_793_946_704 + 2 * 86_400).unwrap();
        assert!(verify_ocsp(&chain[1], &chain[2], &ev1, &POLICY, late)
            .unwrap_err()
            .contains("stale"));
        // not yet valid: before thisUpdate
        let early = ASN1Time::from_timestamp(1_793_946_704 - 2 * 3_600).unwrap();
        assert!(verify_ocsp(&chain[1], &chain[2], &ev1, &POLICY, early).is_err());
        // older than the policy allows
        let strict = OcspPolicy { max_age_secs: 600 };
        assert!(verify_ocsp(&chain[1], &chain[2], &ev1, &strict, t2())
            .unwrap_err()
            .contains("maximum age"));
        // a nonce other than the one sent
        let mut wrong = ev1.clone();
        wrong.nonce.as_mut().unwrap()[0] ^= 1;
        assert!(verify_ocsp(&chain[1], &chain[2], &wrong, &POLICY, t2())
            .unwrap_err()
            .contains("nonce"));
        // one flipped byte in the signed response data: signature refuses
        let mut tampered = ev1.clone();
        let n = tampered.response_der.len();
        let at = tampered
            .response_der
            .windows(2)
            .position(|w| w == [0x18, 0x0f])
            .unwrap()
            + 5; // inside producedAt's digits
        assert!(at < n);
        tampered.response_der[at] ^= 1;
        assert!(verify_ocsp(&chain[1], &chain[2], &tampered, &POLICY, t2()).is_err());
        // the right response with the wrong issuer named
        assert!(verify_ocsp(&chain[1], &chain[3], &ev1, &POLICY, t2()).is_err());
    }
}
