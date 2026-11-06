//! The beacon leg: drand quicknet (`bls-unchained-g1-rfc9380`), verified with `blst`.
//!
//! The network is untrusted: [`fetch`] shells out to `curl` for the JSON of one round, and
//! [`DrandRound::verify`] is what makes it a beacon (the BLS signature on SHA-256 of the
//! big-endian round number under the pinned group key). The audit round of a record is
//! `seen_round + AUDIT_ROUND_MARGIN`, where `seen_round` is the latest round the requester named
//! when it countersigned, so the coin did not exist when the commitment was fixed. What this
//! cannot check is that the requester told the truth about the round it had seen; that residual,
//! with drand's threshold honesty, is the `εbeacon` the Lean instance carries as a hypothesis.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// quicknet chain hash.
pub const QUICKNET_CHAIN: &str = "52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971";
/// quicknet group public key (G2, compressed).
pub const QUICKNET_PK: &str = "83cf0f2896adee7eb8b5f01fcad3912212c437e0073e911fb90022d3e760183c8c4b450b6a0a6c3ac6a5776a2d1064510d1fec758c921cc22b0e17e63aaf4bcb5ed66304de9cf809bd274ca73bab4af5a6e9c76a4bc09e76eae8991ef5ece45a";
/// quicknet genesis (unix seconds) and period.
pub const QUICKNET_GENESIS: u64 = 1_692_803_367;
pub const QUICKNET_PERIOD: u64 = 3;
/// The audit round is this many rounds after the round the requester named.
pub const AUDIT_ROUND_MARGIN: u64 = 2;
const DST: &[u8] = b"BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_";

/// One drand round as the HTTP API returns it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DrandRound {
    pub round: u64,
    pub randomness: String,
    pub signature: String,
}

impl DrandRound {
    /// The BLS check, and that `randomness = SHA-256(signature)`.
    pub fn verify(&self) -> Result<(), String> {
        let sig_bytes = hex::decode(&self.signature).map_err(|e| format!("signature hex: {e}"))?;
        let pk_bytes = hex::decode(QUICKNET_PK).expect("pinned key");
        let pk =
            blst::min_sig::PublicKey::key_validate(&pk_bytes).map_err(|e| format!("pk: {e:?}"))?;
        let sig = blst::min_sig::Signature::sig_validate(&sig_bytes, true)
            .map_err(|e| format!("sig: {e:?}"))?;
        let msg = Sha256::digest(self.round.to_be_bytes());
        let r = sig.verify(true, &msg, DST, &[], &pk, true);
        if r != blst::BLST_ERROR::BLST_SUCCESS {
            return Err(format!(
                "round {}: BLS verification failed: {r:?}",
                self.round
            ));
        }
        let rand = hex::encode(Sha256::digest(&sig_bytes));
        if rand != self.randomness {
            return Err(format!(
                "round {}: randomness is not SHA-256(signature)",
                self.round
            ));
        }
        Ok(())
    }

    /// The unix time at which this round is emitted.
    pub fn emitted_at(&self) -> u64 {
        QUICKNET_GENESIS + (self.round - 1) * QUICKNET_PERIOD
    }
}

/// Fetch one round (`latest` when `round` is `None`) and verify it.
pub fn fetch(round: Option<u64>) -> Result<DrandRound, String> {
    let which = round.map_or_else(|| "latest".to_string(), |r| r.to_string());
    let url = format!("https://api.drand.sh/{QUICKNET_CHAIN}/public/{which}");
    let out = std::process::Command::new("curl")
        .args(["-s", "-m", "20", "--fail", &url])
        .output()
        .map_err(|e| format!("curl: {e}"))?;
    if !out.status.success() {
        return Err(format!("curl {url}: {}", out.status));
    }
    let r: DrandRound =
        serde_json::from_slice(&out.stdout).map_err(|e| format!("drand json: {e}"))?;
    if let Some(want) = round
        && r.round != want
    {
        return Err(format!("asked for round {want}, got {}", r.round));
    }
    r.verify()?;
    Ok(r)
}

/// The 64-bit audit coin of MMR position `position` under the drand round `sig_hex`:
/// the first 8 bytes, little-endian, of BLAKE3-derive-key("fpaudit coin v1", sig ‖ position).
pub fn coin(sig_hex: &str, position: u64) -> u64 {
    let sig = hex::decode(sig_hex).unwrap_or_default();
    let mut h = blake3::Hasher::new_derive_key("dregg audit-flashprove 2026-11-06 coin v1");
    h.update(&sig);
    h.update(&position.to_le_bytes());
    let d = h.finalize();
    u64::from_le_bytes(d.as_bytes()[..8].try_into().expect("8 bytes"))
}

/// `⌊p · 2^64⌋` for a rate given in parts per million.
pub fn p_num_ppm(ppm: u64) -> u64 {
    ((u128::from(ppm) << 64) / 1_000_000) as u64
}
