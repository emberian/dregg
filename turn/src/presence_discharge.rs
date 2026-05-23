//! Presence attestation discharge verification for pyana capability caveats.
//!
//! This module allows any part of the system to verify that a presence attestation
//! (issued by the Discord bot or any trusted presence oracle) satisfies a presence
//! caveat on a capability token.
//!
//! The attestation is a BLAKE3-keyed MAC: self-contained, verifiable without
//! contacting the issuing bot.

use serde::{Deserialize, Serialize};

/// What a presence caveat requires.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PresenceClaimRequirement {
    /// User must be currently online.
    CurrentlyOnline,
    /// User was online at a specific time.
    WasOnlineAt { timestamp: i64 },
    /// User has been online for at least N seconds.
    OnlineForAtLeast { duration_secs: u64 },
    /// User was online within the last N seconds.
    OnlineWithin { window_secs: u64 },
}

/// A caveat on a capability token that requires presence attestation to discharge.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PresenceCaveat {
    /// The signing key of the trusted attestor (the bot's key, used as BLAKE3 MAC key).
    pub issuer_key: [u8; 32],
    /// The required presence claim.
    pub required_claim: PresenceClaimRequirement,
    /// The user ID this caveat applies to.
    pub user_id: u64,
    /// The cell ID this caveat applies to.
    pub cell_id: [u8; 32],
}

/// A presence attestation (discharge token) as received from a presence oracle.
///
/// This is a compact representation matching the wire format used by the Discord bot.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PresenceDischarge {
    /// The user being attested.
    pub user_id: u64,
    /// Their pyana cell ID.
    pub cell_id: [u8; 32],
    /// The claim being attested (encoded as a tag byte).
    pub claim_tag: u8,
    /// Claim data (interpretation depends on claim_tag).
    pub claim_data: u64,
    /// When the attestation was issued (unix timestamp).
    pub issued_at: i64,
    /// When the attestation expires (unix timestamp).
    pub expires_at: i64,
    /// BLAKE3-keyed MAC signature.
    pub signature: [u8; 32],
}

impl PresenceDischarge {
    /// Decode from hex string (as emitted by the Discord bot).
    pub fn from_hex(hex_str: &str) -> Option<Self> {
        let data = hex::decode(hex_str).ok()?;
        Self::from_bytes(&data)
    }

    /// Decode from raw bytes.
    pub fn from_bytes(data: &[u8]) -> Option<Self> {
        // Minimum size: 8 (user_id) + 32 (cell_id) + 1 (tag) + 8 (issued) + 8 (expires) + 32 (sig)
        if data.len() < 89 {
            return None;
        }

        let mut pos = 0;
        let user_id = u64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
        pos += 8;

        let cell_id: [u8; 32] = data[pos..pos + 32].try_into().ok()?;
        pos += 32;

        let claim_tag = data[pos];
        pos += 1;

        // Claims 1, 2, 3 have 8 bytes of data; claim 0 has none.
        let claim_data = if claim_tag == 0 {
            0
        } else {
            if data.len() < pos + 8 + 8 + 8 + 32 {
                return None;
            }
            let val = u64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
            pos += 8;
            val
        };

        if data.len() < pos + 8 + 8 + 32 {
            return None;
        }

        let issued_at = i64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
        pos += 8;
        let expires_at = i64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
        pos += 8;
        let signature: [u8; 32] = data[pos..pos + 32].try_into().ok()?;

        Some(Self {
            user_id,
            cell_id,
            claim_tag,
            claim_data,
            issued_at,
            expires_at,
            signature,
        })
    }

    /// Encode to bytes (matching the bot's wire format).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(128);
        buf.extend_from_slice(&self.user_id.to_le_bytes());
        buf.extend_from_slice(&self.cell_id);
        buf.push(self.claim_tag);
        if self.claim_tag != 0 {
            buf.extend_from_slice(&self.claim_data.to_le_bytes());
        }
        buf.extend_from_slice(&self.issued_at.to_le_bytes());
        buf.extend_from_slice(&self.expires_at.to_le_bytes());
        buf.extend_from_slice(&self.signature);
        buf
    }

    /// Compute the signed content (everything except the signature).
    fn content_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(96);
        buf.extend_from_slice(&self.user_id.to_le_bytes());
        buf.extend_from_slice(&self.cell_id);
        buf.push(self.claim_tag);
        if self.claim_tag != 0 {
            buf.extend_from_slice(&self.claim_data.to_le_bytes());
        }
        buf.extend_from_slice(&self.issued_at.to_le_bytes());
        buf.extend_from_slice(&self.expires_at.to_le_bytes());
        buf
    }

    /// Verify the MAC signature against a key.
    pub fn verify_signature(&self, key: &[u8; 32]) -> bool {
        let content = self.content_bytes();
        let expected = blake3::keyed_hash(key, &content);
        self.signature == *expected.as_bytes()
    }

    /// Extract the claim requirement this discharge attests to.
    pub fn claim(&self) -> Option<PresenceClaimRequirement> {
        match self.claim_tag {
            0 => Some(PresenceClaimRequirement::CurrentlyOnline),
            1 => Some(PresenceClaimRequirement::WasOnlineAt {
                timestamp: self.claim_data as i64,
            }),
            2 => Some(PresenceClaimRequirement::OnlineForAtLeast {
                duration_secs: self.claim_data,
            }),
            3 => Some(PresenceClaimRequirement::OnlineWithin {
                window_secs: self.claim_data,
            }),
            _ => None,
        }
    }
}

/// Verify that a presence discharge satisfies a presence caveat.
///
/// Checks:
/// 1. Signature valid (BLAKE3-keyed MAC against the caveat's issuer key)
/// 2. Not expired (expires_at >= current_time)
/// 3. User/cell match
/// 4. Attested claim satisfies the required claim
///
/// Returns `Ok(())` on success, `Err(reason)` on failure.
pub fn verify_presence_discharge(
    discharge: &PresenceDischarge,
    caveat: &PresenceCaveat,
    current_time: i64,
) -> Result<(), PresenceDischargeError> {
    // 1. Verify signature.
    if !discharge.verify_signature(&caveat.issuer_key) {
        return Err(PresenceDischargeError::InvalidSignature);
    }

    // 2. Check expiry.
    if discharge.expires_at < current_time {
        return Err(PresenceDischargeError::Expired {
            expired_at: discharge.expires_at,
            current_time,
        });
    }

    // 3. Check user/cell match.
    if discharge.user_id != caveat.user_id {
        return Err(PresenceDischargeError::UserMismatch {
            expected: caveat.user_id,
            actual: discharge.user_id,
        });
    }
    if discharge.cell_id != caveat.cell_id {
        return Err(PresenceDischargeError::CellMismatch);
    }

    // 4. Check claim satisfies requirement.
    let attested_claim = discharge
        .claim()
        .ok_or(PresenceDischargeError::UnknownClaimType(
            discharge.claim_tag,
        ))?;

    if !claim_satisfies(&attested_claim, &caveat.required_claim) {
        return Err(PresenceDischargeError::ClaimInsufficient {
            attested: attested_claim,
            required: caveat.required_claim.clone(),
        });
    }

    Ok(())
}

/// Check whether an attested claim satisfies a required claim.
fn claim_satisfies(
    attested: &PresenceClaimRequirement,
    required: &PresenceClaimRequirement,
) -> bool {
    match (attested, required) {
        // Exact match.
        (a, b) if a == b => true,
        // CurrentlyOnline satisfies OnlineWithin for any window.
        (
            PresenceClaimRequirement::CurrentlyOnline,
            PresenceClaimRequirement::OnlineWithin { .. },
        ) => true,
        // OnlineForAtLeast(N) satisfies OnlineForAtLeast(M) if N >= M.
        (
            PresenceClaimRequirement::OnlineForAtLeast {
                duration_secs: attested_dur,
            },
            PresenceClaimRequirement::OnlineForAtLeast {
                duration_secs: required_dur,
            },
        ) => attested_dur >= required_dur,
        // OnlineWithin(N) satisfies OnlineWithin(M) if N <= M (tighter is stronger).
        (
            PresenceClaimRequirement::OnlineWithin {
                window_secs: attested_window,
            },
            PresenceClaimRequirement::OnlineWithin {
                window_secs: required_window,
            },
        ) => attested_window <= required_window,
        _ => false,
    }
}

/// Errors from presence discharge verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PresenceDischargeError {
    /// The BLAKE3-keyed MAC did not verify.
    InvalidSignature,
    /// The attestation has expired.
    Expired { expired_at: i64, current_time: i64 },
    /// The user ID does not match the caveat.
    UserMismatch { expected: u64, actual: u64 },
    /// The cell ID does not match the caveat.
    CellMismatch,
    /// Unknown claim tag in the discharge.
    UnknownClaimType(u8),
    /// The attested claim does not satisfy the required claim.
    ClaimInsufficient {
        attested: PresenceClaimRequirement,
        required: PresenceClaimRequirement,
    },
}

impl std::fmt::Display for PresenceDischargeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSignature => write!(f, "presence attestation signature invalid"),
            Self::Expired {
                expired_at,
                current_time,
            } => {
                write!(
                    f,
                    "presence attestation expired at {expired_at} (now {current_time})"
                )
            }
            Self::UserMismatch { expected, actual } => {
                write!(f, "user mismatch: expected {expected}, got {actual}")
            }
            Self::CellMismatch => write!(f, "cell ID mismatch"),
            Self::UnknownClaimType(tag) => write!(f, "unknown claim type tag: {tag}"),
            Self::ClaimInsufficient { attested, required } => {
                write!(
                    f,
                    "attested claim {attested:?} does not satisfy required {required:?}"
                )
            }
        }
    }
}

impl std::error::Error for PresenceDischargeError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_key() -> [u8; 32] {
        blake3::derive_key("test-presence-key", b"test-secret")
    }

    fn test_cell() -> [u8; 32] {
        [0xAB; 32]
    }

    /// Helper: create a signed discharge for testing.
    fn make_discharge(
        key: &[u8; 32],
        user_id: u64,
        cell_id: [u8; 32],
        claim_tag: u8,
        claim_data: u64,
        issued_at: i64,
        expires_at: i64,
    ) -> PresenceDischarge {
        let mut d = PresenceDischarge {
            user_id,
            cell_id,
            claim_tag,
            claim_data,
            issued_at,
            expires_at,
            signature: [0; 32],
        };
        let content = d.content_bytes();
        let mac = blake3::keyed_hash(key, &content);
        d.signature = *mac.as_bytes();
        d
    }

    #[test]
    fn test_discharge_verify_valid() {
        let key = test_key();
        let d = make_discharge(&key, 12345, test_cell(), 0, 0, 1000, 2000);

        let caveat = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::CurrentlyOnline,
            user_id: 12345,
            cell_id: test_cell(),
        };

        assert!(verify_presence_discharge(&d, &caveat, 1500).is_ok());
    }

    #[test]
    fn test_discharge_verify_expired() {
        let key = test_key();
        let d = make_discharge(&key, 12345, test_cell(), 0, 0, 1000, 2000);

        let caveat = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::CurrentlyOnline,
            user_id: 12345,
            cell_id: test_cell(),
        };

        let result = verify_presence_discharge(&d, &caveat, 3000);
        assert_eq!(
            result,
            Err(PresenceDischargeError::Expired {
                expired_at: 2000,
                current_time: 3000
            })
        );
    }

    #[test]
    fn test_discharge_verify_wrong_signature() {
        let key = test_key();
        let mut d = make_discharge(&key, 12345, test_cell(), 0, 0, 1000, 2000);
        d.signature[0] ^= 0xFF; // Corrupt

        let caveat = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::CurrentlyOnline,
            user_id: 12345,
            cell_id: test_cell(),
        };

        assert_eq!(
            verify_presence_discharge(&d, &caveat, 1500),
            Err(PresenceDischargeError::InvalidSignature)
        );
    }

    #[test]
    fn test_discharge_verify_user_mismatch() {
        let key = test_key();
        let d = make_discharge(&key, 12345, test_cell(), 0, 0, 1000, 2000);

        let caveat = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::CurrentlyOnline,
            user_id: 99999, // Mismatch
            cell_id: test_cell(),
        };

        assert_eq!(
            verify_presence_discharge(&d, &caveat, 1500),
            Err(PresenceDischargeError::UserMismatch {
                expected: 99999,
                actual: 12345
            })
        );
    }

    #[test]
    fn test_discharge_verify_cell_mismatch() {
        let key = test_key();
        let d = make_discharge(&key, 12345, test_cell(), 0, 0, 1000, 2000);

        let caveat = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::CurrentlyOnline,
            user_id: 12345,
            cell_id: [0xFF; 32], // Mismatch
        };

        assert_eq!(
            verify_presence_discharge(&d, &caveat, 1500),
            Err(PresenceDischargeError::CellMismatch)
        );
    }

    #[test]
    fn test_discharge_claim_online_for_at_least() {
        let key = test_key();
        // Attest: online for at least 7200s
        let d = make_discharge(&key, 12345, test_cell(), 2, 7200, 1000, 2000);

        // Require: online for at least 3600s — should pass (7200 >= 3600)
        let caveat = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::OnlineForAtLeast {
                duration_secs: 3600,
            },
            user_id: 12345,
            cell_id: test_cell(),
        };
        assert!(verify_presence_discharge(&d, &caveat, 1500).is_ok());

        // Require: online for at least 10000s — should fail (7200 < 10000)
        let caveat2 = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::OnlineForAtLeast {
                duration_secs: 10000,
            },
            user_id: 12345,
            cell_id: test_cell(),
        };
        assert!(verify_presence_discharge(&d, &caveat2, 1500).is_err());
    }

    #[test]
    fn test_discharge_claim_online_within() {
        let key = test_key();
        // Attest: online within 300s
        let d = make_discharge(&key, 12345, test_cell(), 3, 300, 1000, 2000);

        // Require: online within 600s — should pass (300 <= 600, tighter is stronger)
        let caveat = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::OnlineWithin { window_secs: 600 },
            user_id: 12345,
            cell_id: test_cell(),
        };
        assert!(verify_presence_discharge(&d, &caveat, 1500).is_ok());

        // Require: online within 100s — should fail (300 > 100)
        let caveat2 = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::OnlineWithin { window_secs: 100 },
            user_id: 12345,
            cell_id: test_cell(),
        };
        assert!(verify_presence_discharge(&d, &caveat2, 1500).is_err());
    }

    #[test]
    fn test_discharge_currently_online_satisfies_online_within() {
        let key = test_key();
        // Attest: CurrentlyOnline (tag 0)
        let d = make_discharge(&key, 12345, test_cell(), 0, 0, 1000, 2000);

        // Require: OnlineWithin(3600) — CurrentlyOnline is strictly stronger
        let caveat = PresenceCaveat {
            issuer_key: key,
            required_claim: PresenceClaimRequirement::OnlineWithin { window_secs: 3600 },
            user_id: 12345,
            cell_id: test_cell(),
        };
        assert!(verify_presence_discharge(&d, &caveat, 1500).is_ok());
    }

    #[test]
    fn test_discharge_roundtrip_bytes() {
        let key = test_key();
        let d = make_discharge(&key, 12345, test_cell(), 2, 3600, 1000, 2000);

        let bytes = d.to_bytes();
        let recovered = PresenceDischarge::from_bytes(&bytes).unwrap();

        assert_eq!(recovered.user_id, d.user_id);
        assert_eq!(recovered.cell_id, d.cell_id);
        assert_eq!(recovered.claim_tag, d.claim_tag);
        assert_eq!(recovered.claim_data, d.claim_data);
        assert_eq!(recovered.issued_at, d.issued_at);
        assert_eq!(recovered.expires_at, d.expires_at);
        assert_eq!(recovered.signature, d.signature);
        assert!(recovered.verify_signature(&key));
    }

    #[test]
    fn test_discharge_roundtrip_hex() {
        let key = test_key();
        let d = make_discharge(&key, 12345, test_cell(), 0, 0, 1000, 2000);

        let hex_str = hex::encode(d.to_bytes());
        let recovered = PresenceDischarge::from_hex(&hex_str).unwrap();

        assert_eq!(recovered.user_id, d.user_id);
        assert!(recovered.verify_signature(&key));
    }
}
