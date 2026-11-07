//! The committed request record, its digest (the MMR leaf), and the requester's countersignature.

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// One served request, as committed before its beacon round exists.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RequestRecord {
    /// The audit session (64 hex digits), fixed and countersigned before any of its rounds.
    pub session: String,
    /// MMR position.
    pub position: u64,
    /// The requester's nonce (distinct records for replayed payloads).
    pub nonce: String,
    /// The commitment ID the requester pinned (64 hex digits).
    pub commitment_id: String,
    pub r: u32,
    pub e: u32,
    /// SHA-256 of the request file, the token file, and the proof file (`None`: the provider
    /// committed to handing over no proof).
    pub req_sha256: String,
    pub y_sha256: String,
    pub proof_sha256: Option<String>,
    /// The latest drand round the requester had seen when it countersigned.
    pub seen_round: u64,
}

impl RequestRecord {
    /// The MMR leaf value: BLAKE3-derive-key over the record's canonical JSON (field order fixed
    /// by the struct).
    pub fn digest(&self) -> [u8; 32] {
        let j = serde_json::to_vec(self).expect("record serializes");
        let mut h = blake3::Hasher::new_derive_key("dregg audit-flashprove 2026-11-06 record v2");
        h.update(&j);
        *h.finalize().as_bytes()
    }
}

/// SHA-256 of a file's bytes, hex.
pub fn sha256_file(p: &std::path::Path) -> std::io::Result<String> {
    Ok(hex::encode(Sha256::digest(std::fs::read(p)?)))
}

/// Which checker a fired audit runs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Checker {
    /// FlashProve's `cp_verify`; `Policy::commitment_id` is the FlashProve commitment ID and
    /// `Policy::build` the `cp_verify` build digest.
    CpVerify,
    /// An exact recompute of gptoss-int v0: `spec` and `params` are the recompute's pins, and
    /// `Policy::commitment_id` is the weights' registry commitment. A record's `r` is the prompt
    /// length and `e` the prompt plus output length; its request file holds the prompt tokens and
    /// its token file the committed output tokens, `t1,t2,...`; there is no proof file.
    Exact { spec: String, params: String },
}

/// The audit policy the requester agrees to: what the auditor will pin, at what rate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Policy {
    pub session: String,
    pub checker: Checker,
    pub commitment_id: String,
    pub build: String,
    pub accept_work: bool,
    pub p_num: u64,
}

impl Policy {
    pub fn digest(&self) -> [u8; 32] {
        let j = serde_json::to_vec(self).expect("policy serializes");
        *blake3::Hasher::new_derive_key("dregg audit-flashprove 2026-11-06 policy v2")
            .update(&j)
            .finalize()
            .as_bytes()
    }
}

/// The bytes the requester signs: the policy, the position, the record, the root after the
/// append, and the round it had seen.
pub fn countersign_msg(
    policy: &Policy,
    position: u64,
    digest: &[u8; 32],
    root: &[u8; 32],
    seen_round: u64,
) -> Vec<u8> {
    let mut m = b"dregg audit-flashprove countersign v2".to_vec();
    m.extend_from_slice(&policy.digest());
    m.extend_from_slice(&position.to_le_bytes());
    m.extend_from_slice(digest);
    m.extend_from_slice(root);
    m.extend_from_slice(&seen_round.to_le_bytes());
    m
}

pub fn countersign(sk: &SigningKey, msg: &[u8]) -> String {
    hex::encode(sk.sign(msg).to_bytes())
}

pub fn verify_countersign(pk_hex: &str, msg: &[u8], sig_hex: &str) -> Result<(), String> {
    let pk: [u8; 32] = hex::decode(pk_hex)
        .map_err(|e| e.to_string())?
        .try_into()
        .map_err(|_| "pk length")?;
    let pk = VerifyingKey::from_bytes(&pk).map_err(|e| e.to_string())?;
    let sig: [u8; 64] = hex::decode(sig_hex)
        .map_err(|e| e.to_string())?
        .try_into()
        .map_err(|_| "sig length")?;
    pk.verify(msg, &Signature::from_bytes(&sig))
        .map_err(|e| e.to_string())
}

/// 32 bytes from the operating system's random source.
pub fn os_random32() -> std::io::Result<[u8; 32]> {
    use std::io::Read;
    let mut b = [0u8; 32];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut b)?;
    Ok(b)
}
