//! Core macaroon type: construction, attenuation, verification, and binding.
//!
//! A macaroon is an HMAC-authenticated bearer token with chained caveats.
//! The key security property: caveats can only be added (restricting access),
//! never removed — enforced by the HMAC chain.
//!
//! ```text
//! Macaroon {
//!     Nonce { kid, random }     ← identifies the token
//!     Location                  ← issuer identifier
//!     Caveats [C₁, C₂, ..Cₙ]  ← authorization predicates
//!     Tail                      ← HMAC-SHA256 chain tag
//! }
//!
//! Tail derivation:
//!   T₀ = HMAC(root_key, nonce_bytes)
//!   T₁ = HMAC(T₀, encode(C₁))
//!   T₂ = HMAC(T₁, encode(C₂))
//!   ...
//!   Tₙ = HMAC(Tₙ₋₁, encode(Cₙ))
//! ```

use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use zeroize::Zeroize;

use crate::caveat::{CAV_BIND_TO_PARENT, CAV_THIRD_PARTY, Caveat, CaveatSet, WireCaveat};
use crate::caveat_3p::ThirdPartyCaveat;
use crate::crypto;
use crate::error::MacaroonError;
use crate::format;

/// Maximum age of a discharge macaroon in seconds (5 minutes).
const MAX_DISCHARGE_AGE: i64 = 300;

/// The nonce uniquely identifies a macaroon and seeds the HMAC chain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Nonce {
    /// Key identifier — opaque bytes chosen by the issuer.
    /// For discharge macaroons, this is the encrypted ticket (CID).
    pub kid: Vec<u8>,

    /// Random bytes for uniqueness.
    pub rnd: [u8; 16],

    /// Unix timestamp (seconds) when this nonce was created.
    /// Used for discharge replay protection — discharges older than
    /// `MAX_DISCHARGE_AGE` are rejected.
    #[serde(default)]
    pub created_at: i64,
}

impl Drop for Nonce {
    fn drop(&mut self) {
        self.rnd.zeroize();
    }
}

impl Nonce {
    /// Create a new nonce with a key ID and random bytes.
    pub fn new(kid: Vec<u8>) -> Self {
        Self {
            kid,
            rnd: crypto::random_bytes::<16>(),
            created_at: 0,
        }
    }

    /// Encode the nonce to bytes for HMAC input.
    pub fn encode(&self) -> Vec<u8> {
        rmp_serde::to_vec(self).expect("nonce serialization should not fail")
    }
}

/// A macaroon token.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Macaroon {
    /// Nonce: key ID + random bytes.
    pub nonce: Nonce,

    /// Issuer location (URL or identifier).
    pub location: String,

    /// Ordered list of caveats (first-party and third-party).
    pub caveats: CaveatSet,

    /// The current HMAC-SHA256 chain tail (signature tag).
    pub tail: [u8; 32],
}

impl Drop for Macaroon {
    fn drop(&mut self) {
        self.tail.zeroize();
    }
}

impl Macaroon {
    /// Create a new macaroon with the given root key.
    ///
    /// The root key is used to compute the initial HMAC tag. It must be
    /// kept secret by the issuer — it's the only way to verify the token.
    pub fn new(root_key: &[u8; 32], kid: Vec<u8>, location: String) -> Self {
        let nonce = Nonce::new(kid);
        let nonce_bytes = nonce.encode();
        let tail = crypto::hmac_sha256(root_key, &nonce_bytes);

        Self {
            nonce,
            location,
            caveats: CaveatSet::new(),
            tail,
        }
    }

    /// Create a new macaroon with a specific nonce (used for discharge macaroons).
    pub fn with_nonce(root_key: &[u8; 32], nonce: Nonce, location: String) -> Self {
        let nonce_bytes = nonce.encode();
        let tail = crypto::hmac_sha256(root_key, &nonce_bytes);

        Self {
            nonce,
            location,
            caveats: CaveatSet::new(),
            tail,
        }
    }

    // --- Attenuation (adding caveats) ---

    /// Add a first-party caveat. The HMAC chain extends:
    /// `new_tail = HMAC(old_tail, encode(caveat))`
    ///
    /// This is the fundamental attenuation operation — it can only restrict
    /// what the token allows, never expand it.
    pub fn add_first_party(&mut self, caveat: &dyn Caveat) {
        let wire = WireCaveat::from_caveat(caveat);
        let encoded = wire.encode();
        self.tail = crypto::hmac_sha256(&self.tail, &encoded);
        self.caveats.push(wire);
    }

    /// Add a first-party caveat from a pre-built wire representation.
    pub fn add_first_party_wire(&mut self, wire: WireCaveat) {
        let encoded = wire.encode();
        self.tail = crypto::hmac_sha256(&self.tail, &encoded);
        self.caveats.push(wire);
    }

    /// Add a third-party caveat.
    ///
    /// Generates an ephemeral discharge key, encrypts it for both the verifier
    /// (VID, encrypted under current tail) and the third party (ticket, encrypted
    /// under shared key KA).
    ///
    /// # Arguments
    /// - `location`: URL of the 3P discharge service
    /// - `shared_key`: Pre-shared key between issuer and the 3P
    /// - `caveats_for_3p`: Caveats the 3P must check when issuing a discharge
    pub fn add_third_party(
        &mut self,
        location: &str,
        shared_key: &[u8; 32],
        caveats_for_3p: CaveatSet,
    ) -> Result<(), MacaroonError> {
        let (tp_caveat, _discharge_key) =
            ThirdPartyCaveat::new(location.to_string(), &self.tail, shared_key, caveats_for_3p)?;

        let wire = WireCaveat::new(CAV_THIRD_PARTY, tp_caveat.encode_body()?);
        let encoded = wire.encode();
        self.tail = crypto::hmac_sha256(&self.tail, &encoded);
        self.caveats.push(wire);

        Ok(())
    }

    // --- Verification ---

    /// Verify the macaroon's signature and return all collected caveats.
    ///
    /// This replays the HMAC chain from the root key and verifies:
    /// 1. The chain tail matches the stored tail
    /// 2. All third-party caveats have matching discharges
    /// 3. Discharge signatures are valid and bound to this root
    ///
    /// Returns a `CaveatSet` containing all first-party caveats from both
    /// the root macaroon and all discharges. The caller is responsible for
    /// "clearing" these caveats against the actual access request.
    pub fn verify(
        &self,
        root_key: &[u8; 32],
        discharges: &[Macaroon],
    ) -> Result<CaveatSet, MacaroonError> {
        let mut collected = CaveatSet::new();

        // Replay the HMAC chain
        let nonce_bytes = self.nonce.encode();
        let mut current_tail = crypto::hmac_sha256(root_key, &nonce_bytes);

        for wire_caveat in self.caveats.iter() {
            let encoded = wire_caveat.encode();

            if wire_caveat.caveat_type == CAV_THIRD_PARTY {
                // Handle third-party caveat
                let tp = ThirdPartyCaveat::decode_body(&wire_caveat.body)?;

                // Find matching discharge by ticket (KID) and location.
                // Both must match to prevent a discharge from a different service
                // that happens to share the same ticket bytes from being accepted.
                let discharge = discharges
                    .iter()
                    .find(|d| d.nonce.kid == tp.ticket && d.location == tp.location)
                    .ok_or_else(|| MacaroonError::MissingDischarge {
                        location: tp.location.clone(),
                    })?;

                // Decrypt the VID to recover the discharge key
                let discharge_key =
                    ThirdPartyCaveat::decrypt_verifier_key(&tp.verifier_key, &current_tail)?;

                // Verify the discharge macaroon using the discharge key
                let discharge_caveats = discharge
                    .verify_discharge(&discharge_key, &self.tail)
                    .map_err(|_| MacaroonError::DischargeInvalid {
                        location: tp.location.clone(),
                    })?;

                // Collect discharge's first-party caveats
                collected.extend(discharge_caveats);
            } else if wire_caveat.caveat_type == CAV_BIND_TO_PARENT {
                // Bind-to-parent caveats are structural, not collected for clearing
            } else {
                // First-party caveat — collect for clearing
                collected.push(wire_caveat.clone());
            }

            // Advance the HMAC chain
            current_tail = crypto::hmac_sha256(&current_tail, &encoded);
        }

        // Verify the final tail matches (constant-time)
        if !crypto::constant_time_eq(&current_tail, &self.tail) {
            return Err(MacaroonError::SignatureInvalid);
        }

        Ok(collected)
    }

    /// Verify a discharge macaroon. Similar to `verify` but also checks
    /// that the discharge is bound to the expected parent tail and is fresh
    /// (created within `MAX_DISCHARGE_AGE` seconds).
    fn verify_discharge(
        &self,
        discharge_key: &[u8; 32],
        expected_parent_tail: &[u8; 32],
    ) -> Result<CaveatSet, MacaroonError> {
        // Check discharge freshness (replay protection).
        // A created_at of 0 means the discharge predates this check — reject it
        // to force upgrade (fail-closed).
        if self.nonce.created_at == 0 {
            return Err(MacaroonError::Malformed(
                "discharge missing created_at timestamp".into(),
            ));
        }
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock before UNIX epoch")
            .as_secs() as i64;
        let age = now - self.nonce.created_at;
        if age < 0 || age > MAX_DISCHARGE_AGE {
            return Err(MacaroonError::Malformed(format!(
                "discharge expired (age={age}s, max={MAX_DISCHARGE_AGE}s)"
            )));
        }

        let mut collected = CaveatSet::new();
        let mut found_binding = false;

        let nonce_bytes = self.nonce.encode();
        let mut current_tail = crypto::hmac_sha256(discharge_key, &nonce_bytes);

        for wire_caveat in self.caveats.iter() {
            let encoded = wire_caveat.encode();

            if wire_caveat.caveat_type == CAV_BIND_TO_PARENT {
                // Check the binding (constant-time comparison of full 32-byte hash)
                let expected_hash = crypto::binding_hash(expected_parent_tail);
                if crypto::binding_hash_eq(&wire_caveat.body, &expected_hash) {
                    found_binding = true;
                } else {
                    return Err(MacaroonError::DischargeUnbound);
                }
            } else if wire_caveat.caveat_type == CAV_THIRD_PARTY {
                // Nested 3P caveats in discharges are not supported in v1
                return Err(MacaroonError::Malformed(
                    "nested 3P caveats in discharge not yet supported".into(),
                ));
            } else {
                collected.push(wire_caveat.clone());
            }

            current_tail = crypto::hmac_sha256(&current_tail, &encoded);
        }

        if !crypto::constant_time_eq(&current_tail, &self.tail) {
            return Err(MacaroonError::SignatureInvalid);
        }

        if !found_binding {
            // Enforce binding: ALL discharges must be bound to the parent.
            // An unbound discharge (even with zero caveats) could be replayed
            // with a less-attenuated root macaroon. Reject unconditionally (fail-closed).
            return Err(MacaroonError::DischargeUnbound);
        }

        Ok(collected)
    }

    // --- Binding ---

    /// Bind a discharge macaroon to this root macaroon.
    ///
    /// Adds a `BindToParentToken` caveat to the discharge containing
    /// the full `SHA256(root_tail)` (32 bytes). This prevents the discharge
    /// from being replayed with a less-attenuated version of the root.
    pub fn bind_discharge(&self, discharge: &mut Macaroon) {
        let hash = crypto::binding_hash(&self.tail);
        let wire = WireCaveat::new(CAV_BIND_TO_PARENT, hash.to_vec());
        let encoded = wire.encode();
        discharge.tail = crypto::hmac_sha256(&discharge.tail, &encoded);
        discharge.caveats.push(wire);
    }

    // --- Serialization ---

    /// Serialize to binary (MsgPack).
    pub fn serialize(&self) -> Result<Vec<u8>, MacaroonError> {
        rmp_serde::to_vec(self).map_err(|e| MacaroonError::Encoding(e.to_string()))
    }

    /// Deserialize from binary (MsgPack).
    pub fn deserialize(data: &[u8]) -> Result<Self, MacaroonError> {
        rmp_serde::from_slice(data).map_err(|e| MacaroonError::Encoding(e.to_string()))
    }

    /// Encode to wire format: `em2_<base64url>`.
    pub fn encode(&self) -> Result<String, MacaroonError> {
        let binary = self.serialize()?;
        Ok(format::encode_token(&binary))
    }

    /// Decode from wire format.
    pub fn decode(token: &str) -> Result<Self, MacaroonError> {
        let binary = format::decode_token(token)?;
        Self::deserialize(&binary)
    }
}

/// Create a discharge macaroon for a third-party caveat.
///
/// Called by the third-party service after decrypting the ticket.
///
/// # Arguments
/// - `ticket`: The raw encrypted ticket bytes (used as KID for matching)
/// - `discharge_key`: The key from the decrypted ticket
/// - `location`: The 3P service's location
/// - `additional_caveats`: Extra caveats to add (e.g., ConfineUser, ValidityWindow)
pub fn create_discharge(
    ticket: Vec<u8>,
    discharge_key: &[u8; 32],
    location: String,
    additional_caveats: &[&dyn Caveat],
) -> Macaroon {
    let nonce = Nonce {
        kid: ticket,
        rnd: crypto::random_bytes::<16>(),
        created_at: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock before UNIX epoch")
            .as_secs() as i64,
    };
    let mut macaroon = Macaroon::with_nonce(discharge_key, nonce, location);

    for caveat in additional_caveats {
        macaroon.add_first_party(*caveat);
    }

    macaroon
}

#[cfg(test)]
mod tests {
    use super::*;
    /// A simple test caveat that checks a string value.
    struct TestCaveat {
        key: String,
        value: String,
    }

    impl Caveat for TestCaveat {
        fn caveat_type(&self) -> u16 {
            48 // user-defined range
        }
        fn name(&self) -> &str {
            "test"
        }
        fn prohibits(
            &self,
            _access: &dyn crate::access::Access,
        ) -> Result<(), crate::error::CaveatError> {
            Ok(())
        }
        fn encode_body(&self) -> Vec<u8> {
            rmp_serde::to_vec(&(&self.key, &self.value)).unwrap()
        }
    }

    #[test]
    fn test_attenuation_and_verify() {
        let root_key = crypto::random_key();
        let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://pyana.dev".into());

        // Add caveats
        let c1 = TestCaveat {
            key: "app".into(),
            value: "my-app".into(),
        };
        let c2 = TestCaveat {
            key: "action".into(),
            value: "read".into(),
        };
        mac.add_first_party(&c1);
        mac.add_first_party(&c2);

        // Verify succeeds
        let collected = mac.verify(&root_key, &[]).unwrap();
        assert_eq!(collected.len(), 2);
    }

    #[test]
    fn test_wrong_key_fails() {
        let root_key = crypto::random_key();
        let wrong_key = crypto::random_key();
        let mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://pyana.dev".into());

        assert!(mac.verify(&wrong_key, &[]).is_err());
    }

    #[test]
    fn test_tampered_caveat_fails() {
        let root_key = crypto::random_key();
        let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://pyana.dev".into());

        mac.add_first_party(&TestCaveat {
            key: "app".into(),
            value: "my-app".into(),
        });

        // Tamper: change the caveat body
        let mut tampered = mac.clone();
        if let Some(c) = tampered.caveats.as_slice().first() {
            let mut modified = c.clone();
            modified.body = vec![0xff, 0xfe];
            tampered.caveats = CaveatSet::new();
            tampered.caveats.push(modified);
        }

        assert!(tampered.verify(&root_key, &[]).is_err());
    }

    #[test]
    fn test_removed_caveat_fails() {
        let root_key = crypto::random_key();
        let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://pyana.dev".into());

        mac.add_first_party(&TestCaveat {
            key: "app".into(),
            value: "my-app".into(),
        });
        mac.add_first_party(&TestCaveat {
            key: "action".into(),
            value: "read".into(),
        });

        // Try to remove the second caveat — tail won't match
        let mut stripped = mac.clone();
        stripped.caveats = CaveatSet::new();
        stripped.caveats.push(mac.caveats.as_slice()[0].clone());

        assert!(stripped.verify(&root_key, &[]).is_err());
    }

    #[test]
    fn test_serialize_deserialize_roundtrip() {
        let root_key = crypto::random_key();
        let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://pyana.dev".into());
        mac.add_first_party(&TestCaveat {
            key: "app".into(),
            value: "test".into(),
        });

        let binary = mac.serialize().unwrap();
        let restored = Macaroon::deserialize(&binary).unwrap();

        assert_eq!(mac.nonce, restored.nonce);
        assert_eq!(mac.location, restored.location);
        assert_eq!(mac.tail, restored.tail);
        assert_eq!(mac.caveats, restored.caveats);

        // Verify still works on deserialized
        restored.verify(&root_key, &[]).unwrap();
    }

    #[test]
    fn test_encode_decode_roundtrip() {
        let root_key = crypto::random_key();
        let mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://pyana.dev".into());

        let encoded = mac.encode().unwrap();
        assert!(encoded.starts_with("em2_"));

        let decoded = Macaroon::decode(&encoded).unwrap();
        assert_eq!(mac.tail, decoded.tail);
        decoded.verify(&root_key, &[]).unwrap();
    }

    #[test]
    fn test_third_party_caveat_full_flow() {
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();

        // 1. Create root macaroon with 3P caveat
        let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://pyana.dev".into());
        mac.add_first_party(&TestCaveat {
            key: "org".into(),
            value: "pyana".into(),
        });
        mac.add_third_party("https://auth.pyana.dev", &shared_key, CaveatSet::new())
            .unwrap();

        // 2. Extract ticket from 3P caveat
        let tp_caveats = mac.caveats.third_party_caveats();
        assert_eq!(tp_caveats.len(), 1);
        let tp = ThirdPartyCaveat::decode_body(&tp_caveats[0].body).unwrap();

        // 3. Third party decrypts ticket and creates discharge
        let wire_ticket = ThirdPartyCaveat::decrypt_ticket(&tp.ticket, &shared_key).unwrap();
        let mut dk = [0u8; 32];
        dk.copy_from_slice(&wire_ticket.discharge_key);

        let mut discharge =
            create_discharge(tp.ticket.clone(), &dk, "https://auth.pyana.dev".into(), &[]);

        // 4. Bind discharge to root
        mac.bind_discharge(&mut discharge);

        // 5. Verify succeeds
        let collected = mac.verify(&root_key, &[discharge]).unwrap();
        // Should have the first-party caveat from the root
        assert_eq!(collected.len(), 1);
    }

    #[test]
    fn test_unbound_discharge_rejected_even_when_empty() {
        // ALL discharges must be bound, even empty ones. An unbound discharge
        // could be replayed with a less-attenuated root macaroon.
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();

        let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://pyana.dev".into());
        mac.add_third_party("https://auth.pyana.dev", &shared_key, CaveatSet::new())
            .unwrap();

        let tp_caveats = mac.caveats.third_party_caveats();
        let tp = ThirdPartyCaveat::decode_body(&tp_caveats[0].body).unwrap();
        let wire_ticket = ThirdPartyCaveat::decrypt_ticket(&tp.ticket, &shared_key).unwrap();
        let mut dk = [0u8; 32];
        dk.copy_from_slice(&wire_ticket.discharge_key);

        // Create discharge WITHOUT binding (empty discharge, just the key)
        let discharge =
            create_discharge(tp.ticket.clone(), &dk, "https://auth.pyana.dev".into(), &[]);

        // Must be rejected — unbound discharges are never allowed
        assert!(mac.verify(&root_key, &[discharge]).is_err());
    }

    #[test]
    fn test_bound_empty_discharge_succeeds() {
        // A properly bound empty discharge should still verify.
        let root_key = crypto::random_key();
        let shared_key = crypto::random_key();

        let mut mac = Macaroon::new(&root_key, b"kid-1".to_vec(), "https://pyana.dev".into());
        mac.add_third_party("https://auth.pyana.dev", &shared_key, CaveatSet::new())
            .unwrap();

        let tp_caveats = mac.caveats.third_party_caveats();
        let tp = ThirdPartyCaveat::decode_body(&tp_caveats[0].body).unwrap();
        let wire_ticket = ThirdPartyCaveat::decrypt_ticket(&tp.ticket, &shared_key).unwrap();
        let mut dk = [0u8; 32];
        dk.copy_from_slice(&wire_ticket.discharge_key);

        let mut discharge =
            create_discharge(tp.ticket.clone(), &dk, "https://auth.pyana.dev".into(), &[]);

        // Bind the discharge to the root — this should make it valid
        mac.bind_discharge(&mut discharge);
        mac.verify(&root_key, &[discharge]).unwrap();
    }
}
