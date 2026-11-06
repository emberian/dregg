//! The GPU half of the attestation gate. Before this, `gpu_evidence` was deserialised by
//! chutes-api's schema and never read here, so "confidential GPU" meant only "a CPU TD whose
//! image is pinned". Now an instance attests only if EVERY GPU it reports verifies through
//! [`dregg_tee_verify::nvidia::verify_gpu_evidence`]: device chain to the pinned NVIDIA root,
//! report signature, fresh nonce, FWID binding, goldens from NVIDIA's signed driver and VBIOS
//! RIMs, and OCSP for the device chain and both RIM chains. Absent GPU evidence is a refusal.
//!
//! Wire shape (chutes-api `api/server/schemas.py::TeeInstanceEvidence.gpu_evidence`, a list of
//! per-GPU dicts, verified server-side by `chutes-nvattest`): each item is nvtrust's remote
//! evidence form (`cc_admin.py::collect_gpu_evidence_remote`):
//! `{"certificate": base64(PEM chain, leaf first), "evidence": base64(raw SPDM report),
//! "arch": "HOPPER"}`.
//!
//! The GPU report's nonce must equal the instance's binding
//! `SHA-256(ascii(nonce_hex) ‖ ascii(e2e_pubkey_b64))`, the same 32 bytes the TDX quote carries
//! in `report_data[0..32]`. MEASURED live 2026-11-06 (degg-research critique W4): on every
//! instance whose key discovery returned, the GPU report's SPDM nonce equals that binding, and
//! not the raw nonce. So the GPU report is bound to the fresh nonce AND to the ML-KEM key the
//! request is encrypted to.
//!
//! Collateral (RIMs and OCSP responses) is an INPUT to the offline verifier. It is either
//! pre-fetched, or fetched per GPU from NVIDIA's RIM and OCSP services (each OCSP request with
//! its own fresh nonce, checked on the response).

use std::collections::BTreeMap;

use base64::Engine;
use serde::Deserialize;

use dregg_tee_verify::nvidia::{
    parse_report, rim_ids, verify_gpu_evidence, ASN1Time, GpuEvidence, NONCE_LEN,
};
use dregg_tee_verify::nvidia_ocsp::{build_ocsp_request, OcspEvidence, OcspPolicy};

use crate::error::ClientError;

/// NVIDIA's RIM service and OCSP responder (nvtrust `config.py` defaults).
pub const NVIDIA_RIM_BASE: &str = "https://rim.attestation.nvidia.com/v1/rim/";
pub const NVIDIA_OCSP_URL: &str = "https://ocsp.ndis.nvidia.com/";

/// One GPU's evidence as chutes-api serves it.
#[derive(Debug, Clone, Deserialize)]
pub struct GpuEvidenceItem {
    pub certificate: String,
    pub evidence: String,
    pub arch: String,
}

/// Where RIMs and OCSP responses come from.
#[derive(Clone)]
pub enum GpuCollateralSource {
    /// RIMs keyed by RIM service id (e.g. `NV_GPU_DRIVER_GH100_550.90.07`), and OCSP responses
    /// covering every certificate to be checked. Offline; for tests and pinned deployments.
    Prefetched {
        rims: BTreeMap<String, Vec<u8>>,
        ocsp: Vec<OcspEvidence>,
    },
    /// Fetch per GPU from NVIDIA's services.
    Nvidia { rim_base: String, ocsp_url: String },
}

/// The GPU gate's configuration.
#[derive(Clone)]
pub struct GpuGate {
    pub collateral: GpuCollateralSource,
    pub ocsp_policy: OcspPolicy,
    /// An instance must report at least this many GPUs (default 1: no GPU, no attestation).
    pub min_gpus: usize,
    /// Whether an instance's GPUs must verify for it to attest. `true` by default. `false`
    /// skips the GPU gate entirely (the pre-2026-11-06 behaviour, CPU TD only), logs a loud
    /// line on every attestation, and leaves `gpus` empty in the record. It exists for the
    /// narrator path until a live run confirms that chutes passes the user nonce to GPU
    /// evidence collection; the verifier itself has no lenient mode.
    pub required: bool,
}

impl Default for GpuGate {
    fn default() -> Self {
        GpuGate {
            collateral: GpuCollateralSource::Nvidia {
                rim_base: NVIDIA_RIM_BASE.to_string(),
                ocsp_url: NVIDIA_OCSP_URL.to_string(),
            },
            ocsp_policy: OcspPolicy {
                max_age_secs: 24 * 3600,
            },
            min_gpus: 1,
            required: true,
        }
    }
}

/// What one verified GPU contributes to the attestation record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GpuAttestation {
    /// SHA-256 of the GPU attestation (leaf) certificate's DER: which physical GPU.
    pub leaf_fingerprint: [u8; 32],
    pub driver_version: String,
    pub vbios_version: String,
    pub driver_rim_signer: [u8; 32],
    pub vbios_rim_signer: [u8; 32],
}

fn b64(s: &str, what: &str) -> Result<Vec<u8>, String> {
    base64::engine::general_purpose::STANDARD
        .decode(s.trim())
        .map_err(|e| format!("{what}: base64: {e}"))
}

fn pem_ders(pem: &[u8]) -> Result<Vec<Vec<u8>>, String> {
    let mut out = Vec::new();
    for p in dregg_tee_verify::nvidia::pem_iter(pem) {
        out.push(p?);
    }
    Ok(out)
}

/// Supplies, for one GPU, its two RIMs and the OCSP responses for its chains.
pub trait GpuCollateral {
    fn rim(&mut self, id: &str) -> Result<Vec<u8>, String>;
    /// OCSP evidence for `cert` issued by `issuer`.
    fn ocsp(&mut self, cert: &[u8], issuer: &[u8]) -> Result<Vec<OcspEvidence>, String>;
}

struct Prefetched<'a> {
    rims: &'a BTreeMap<String, Vec<u8>>,
    ocsp: &'a [OcspEvidence],
}

impl GpuCollateral for Prefetched<'_> {
    fn rim(&mut self, id: &str) -> Result<Vec<u8>, String> {
        self.rims
            .get(id)
            .cloned()
            .ok_or_else(|| format!("no pre-fetched RIM {id}"))
    }
    fn ocsp(&mut self, _cert: &[u8], _issuer: &[u8]) -> Result<Vec<OcspEvidence>, String> {
        Ok(self.ocsp.to_vec())
    }
}

struct NvidiaFetch<'a> {
    http: &'a reqwest::blocking::Client,
    rim_base: &'a str,
    ocsp_url: &'a str,
}

#[derive(Deserialize)]
struct RimServiceResponse {
    rim: String,
}

impl GpuCollateral for NvidiaFetch<'_> {
    fn rim(&mut self, id: &str) -> Result<Vec<u8>, String> {
        let url = format!("{}{id}", self.rim_base);
        let resp = self
            .http
            .get(&url)
            .send()
            .map_err(|e| format!("GET {url}: {e}"))?;
        if !resp.status().is_success() {
            return Err(format!("GET {url} -> {}", resp.status()));
        }
        let body: RimServiceResponse = resp.json().map_err(|e| format!("RIM JSON: {e}"))?;
        b64(&body.rim, "RIM")
    }
    fn ocsp(&mut self, cert: &[u8], issuer: &[u8]) -> Result<Vec<OcspEvidence>, String> {
        let mut nonce = vec![0u8; 32];
        getrandom::fill(&mut nonce).map_err(|e| format!("OCSP nonce RNG: {e}"))?;
        let req = build_ocsp_request(cert, issuer, &nonce)?;
        let resp = self
            .http
            .post(self.ocsp_url)
            .header("Content-Type", "application/ocsp-request")
            .body(req)
            .send()
            .map_err(|e| format!("OCSP POST: {e}"))?;
        if !resp.status().is_success() {
            return Err(format!("OCSP POST -> {}", resp.status()));
        }
        let der = resp
            .bytes()
            .map_err(|e| format!("OCSP body: {e}"))?
            .to_vec();
        Ok(vec![OcspEvidence {
            response_der: der,
            nonce: Some(nonce),
        }])
    }
}

/// Verify one GPU item: decode, gather collateral, and run the composed offline verifier.
pub fn verify_gpu_item(
    item: &GpuEvidenceItem,
    nonce: &[u8; NONCE_LEN],
    collateral: &mut dyn GpuCollateral,
    policy: &OcspPolicy,
    now: ASN1Time,
) -> Result<GpuAttestation, String> {
    if item.arch != "HOPPER" {
        return Err(format!(
            "GPU arch {:?} is not supported (HOPPER only)",
            item.arch
        ));
    }
    let report = b64(&item.evidence, "GPU evidence")?;
    let chain_pem = b64(&item.certificate, "GPU certificate chain")?;
    let parsed = parse_report(&report)?;
    let (driver_id, vbios_id) = rim_ids(&parsed)?;
    let driver_rim = collateral.rim(&driver_id)?;
    let vbios_rim = collateral.rim(&vbios_id)?;

    // The certificates OCSP must cover: the device chain but its leaf, and both RIM chains
    // (read from the RIMs' KeyInfo; the verifier re-derives and re-checks all of them).
    let mut to_check: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    let device = pem_ders(&chain_pem)?;
    for w in device.windows(2).skip(1) {
        to_check.push((w[0].clone(), w[1].clone()));
    }
    for rim in [&driver_rim, &vbios_rim] {
        let chain = dregg_tee_verify::nvidia_rim::rim_key_info_chain(rim)?;
        for w in chain.windows(2) {
            to_check.push((w[0].clone(), w[1].clone()));
        }
    }
    let mut ocsp = Vec::new();
    for (cert, issuer) in &to_check {
        ocsp.extend(collateral.ocsp(cert, issuer)?);
    }

    let ev = GpuEvidence {
        report,
        chain_pem,
        driver_rim,
        vbios_rim,
        ocsp,
    };
    let v = verify_gpu_evidence(&ev, nonce, policy, now)?;
    Ok(GpuAttestation {
        leaf_fingerprint: v.gpu.leaf_fingerprint,
        driver_version: v.driver_version,
        vbios_version: v.vbios_version,
        driver_rim_signer: v.driver_rim_signer,
        vbios_rim_signer: v.vbios_rim_signer,
    })
}

/// The instance-level gate: at least `min_gpus` items, every one verifies, and no physical GPU
/// (leaf certificate) is counted twice.
pub fn verify_instance_gpus(
    items: &[GpuEvidenceItem],
    nonce: &[u8; NONCE_LEN],
    collateral: &mut dyn GpuCollateral,
    gate: &GpuGate,
    now: ASN1Time,
) -> Result<Vec<GpuAttestation>, String> {
    if items.len() < gate.min_gpus.max(1) {
        return Err(format!(
            "{} GPU evidence item(s), at least {} required",
            items.len(),
            gate.min_gpus.max(1)
        ));
    }
    let mut out: Vec<GpuAttestation> = Vec::with_capacity(items.len());
    for (i, item) in items.iter().enumerate() {
        let g = verify_gpu_item(item, nonce, collateral, &gate.ocsp_policy, now)
            .map_err(|e| format!("GPU {i}: {e}"))?;
        if out.iter().any(|o| o.leaf_fingerprint == g.leaf_fingerprint) {
            return Err(format!("GPU {i}: the same GPU's evidence appears twice"));
        }
        out.push(g);
    }
    Ok(out)
}

/// Run the gate with the configured collateral source.
pub fn gate_instance(
    http: &reqwest::blocking::Client,
    items: &[GpuEvidenceItem],
    nonce_hex: &str,
    e2e_pubkey_b64: &str,
    gate: &GpuGate,
    now_secs: u64,
) -> Result<Vec<GpuAttestation>, ClientError> {
    let nonce: [u8; NONCE_LEN] =
        dregg_tee_verify::tdx::chutes_report_data_binding(nonce_hex, e2e_pubkey_b64);
    let now = ASN1Time::from_timestamp(now_secs as i64)
        .map_err(|e| ClientError::Config(format!("clock: {e}")))?;
    let r = match &gate.collateral {
        GpuCollateralSource::Prefetched { rims, ocsp } => {
            verify_instance_gpus(items, &nonce, &mut Prefetched { rims, ocsp }, gate, now)
        }
        GpuCollateralSource::Nvidia { rim_base, ocsp_url } => verify_instance_gpus(
            items,
            &nonce,
            &mut NvidiaFetch {
                http,
                rim_base,
                ocsp_url,
            },
            gate,
            now,
        ),
    };
    r.map_err(ClientError::Evidence)
}

#[cfg(test)]
mod tests {
    use super::*;

    const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../tee-verify/tests/data");

    fn read(name: &str) -> Vec<u8> {
        std::fs::read(format!("{DATA}/{name}")).unwrap()
    }

    /// The public NVIDIA sample in chutes-api's wire shape.
    fn sample_item() -> GpuEvidenceItem {
        let report = hex::decode(
            String::from_utf8(read("nvidia_hopper_attestation_report.hex"))
                .unwrap()
                .trim(),
        )
        .unwrap();
        let e = base64::engine::general_purpose::STANDARD;
        GpuEvidenceItem {
            certificate: e.encode(read("nvidia_hopper_cert_chain.pem")),
            evidence: e.encode(report),
            arch: "HOPPER".into(),
        }
    }

    fn sample_nonce() -> [u8; NONCE_LEN] {
        let r = base64::engine::general_purpose::STANDARD
            .decode(&sample_item().evidence)
            .unwrap();
        parse_report(&r).unwrap().request_nonce
    }

    fn prefetched_gate() -> GpuGate {
        let mut rims = BTreeMap::new();
        rims.insert(
            "NV_GPU_DRIVER_GH100_550.90.07".to_string(),
            read("nvidia_rim_driver_GH100_550.90.07.swidtag"),
        );
        rims.insert(
            "NV_GPU_VBIOS_1010_0200_882_96009F0001".to_string(),
            read("nvidia_rim_vbios_1010_0200_882_96009F0001.swidtag"),
        );
        let nonces = String::from_utf8(read("nvidia_ocsp/nonces.txt")).unwrap();
        let ocsp = nonces
            .lines()
            .map(|l| {
                let (name, nonce) = l.split_once(' ').unwrap();
                OcspEvidence {
                    response_der: read(&format!("nvidia_ocsp/{name}.der")),
                    nonce: Some(hex::decode(nonce).unwrap()),
                }
            })
            .collect();
        GpuGate {
            collateral: GpuCollateralSource::Prefetched { rims, ocsp },
            ..GpuGate::default()
        }
    }

    fn run(
        items: &[GpuEvidenceItem],
        nonce: &[u8; NONCE_LEN],
        now: i64,
    ) -> Result<Vec<GpuAttestation>, String> {
        let gate = prefetched_gate();
        let GpuCollateralSource::Prefetched { rims, ocsp } = &gate.collateral else {
            unreachable!()
        };
        verify_instance_gpus(
            items,
            nonce,
            &mut Prefetched { rims, ocsp },
            &gate,
            ASN1Time::from_timestamp(now).unwrap(),
        )
    }

    /// 2026-11-06T06:31:44Z, one hour after the OCSP capture.
    const T2: i64 = 1_793_946_704;

    /// The live capture (2026-11-06, one instance of a -TEE chute): the GPU report's SPDM nonce
    /// is the instance's report_data binding SHA-256(nonce_hex || e2e_pubkey_b64), equal to the
    /// TDX quote's report_data[0..32]; and the raw nonce is NOT what the GPU signed.
    #[test]
    fn chutes_live_gpu_nonce_is_the_report_data_binding() {
        let j: serde_json::Value = serde_json::from_slice(
            &std::fs::read(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/data/chutes_live_evidence_2026-11-06.json"
            ))
            .unwrap(),
        )
        .unwrap();
        let nonce_hex = j["nonce_hex"].as_str().unwrap();
        let pk = j["e2e_pubkey_b64"].as_str().unwrap();
        let want = dregg_tee_verify::tdx::chutes_report_data_binding(nonce_hex, pk);
        let e = base64::engine::general_purpose::STANDARD;
        let quote = e.decode(j["quote_b64"].as_str().unwrap()).unwrap();
        assert_eq!(
            &quote[48 + 520..48 + 552],
            &want[..],
            "TDX report_data[0..32]"
        );
        let items: Vec<GpuEvidenceItem> =
            serde_json::from_value(j["gpu_evidence"].clone()).unwrap();
        assert!(!items.is_empty());
        for item in &items {
            let r = parse_report(&e.decode(&item.evidence).unwrap()).unwrap();
            assert_eq!(r.request_nonce, want, "GPU nonce is the binding");
            assert_ne!(
                r.request_nonce.to_vec(),
                hex::decode(nonce_hex).unwrap(),
                "not the raw nonce"
            );
        }
    }

    #[test]
    fn chutes_gpu_evidence_absent_refuses() {
        let err = run(&[], &sample_nonce(), T2).unwrap_err();
        assert!(err.contains("at least 1"), "{err}");
    }

    /// The real sample flows through the real verifier and is refused for the reason the
    /// composed verifier gives (its driver RIM's signer expired 2026-06-01): every step before
    /// that one passed through this crate's decoding, id derivation and collateral plumbing.
    #[test]
    fn chutes_gpu_evidence_routes_through_the_nvidia_verifier() {
        let err = run(&[sample_item()], &sample_nonce(), T2).unwrap_err();
        assert!(
            err.starts_with("GPU 0: driver RIM: RIM chain cert 0"),
            "{err}"
        );
    }

    #[test]
    fn chutes_gpu_evidence_failing_refuses() {
        let nonce = sample_nonce();
        // a nonce other than the one the GPU signed (replay)
        let mut other = nonce;
        other[0] ^= 1;
        assert!(run(&[sample_item()], &other, T2)
            .unwrap_err()
            .contains("nonce"));
        // an unsupported architecture
        let mut item = sample_item();
        item.arch = "BLACKWELL".into();
        assert!(run(&[item], &nonce, T2).unwrap_err().contains("HOPPER"));
        // evidence that is not base64
        let mut item = sample_item();
        item.evidence = "not base64!".into();
        assert!(run(&[item], &nonce, T2).unwrap_err().contains("base64"));
        // a tampered report (one measurement byte): signature refuses
        let mut item = sample_item();
        let e = base64::engine::general_purpose::STANDARD;
        let mut r = e.decode(&item.evidence).unwrap();
        r[dregg_tee_verify::nvidia::SPDM_REQUEST_LEN + 11] ^= 1;
        item.evidence = e.encode(r);
        assert!(run(&[item], &nonce, T2).is_err());
        // no RIM for the GPU's driver
        let gate = GpuGate {
            collateral: GpuCollateralSource::Prefetched {
                rims: BTreeMap::new(),
                ocsp: vec![],
            },
            ..GpuGate::default()
        };
        let mut c = Prefetched {
            rims: &BTreeMap::new(),
            ocsp: &[],
        };
        let err = verify_instance_gpus(
            &[sample_item()],
            &nonce,
            &mut c,
            &gate,
            ASN1Time::from_timestamp(T2).unwrap(),
        )
        .unwrap_err();
        assert!(err.contains("no pre-fetched RIM"), "{err}");
        // the wire shape: chutes-api's JSON item deserialises; a missing field refuses
        let j = serde_json::json!({"certificate": "a", "evidence": "b", "arch": "HOPPER"});
        assert!(serde_json::from_value::<GpuEvidenceItem>(j).is_ok());
        let j = serde_json::json!({"certificate": "a", "arch": "HOPPER"});
        assert!(serde_json::from_value::<GpuEvidenceItem>(j).is_err());
    }
}
