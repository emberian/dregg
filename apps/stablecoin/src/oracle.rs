//! Price oracle: signed attestations with freshness checks.
//!
//! The oracle provides price data that is bound into the CDP circuit via a
//! commitment (hash of price, timestamp, oracle public key). This commitment
//! becomes a public input to the STARK proof, ensuring the prover used the
//! correct oracle-attested price.
//!
//! # Security Model
//!
//! - The oracle signs `(asset_pair, price, timestamp)` tuples.
//! - The CDP circuit binds to `oracle_commitment = Poseidon2(price, timestamp, oracle_pk_hash)`.
//! - Freshness is enforced by requiring `current_time - timestamp <= max_age`.
//! - Multiple oracle sources can be supported via a median mechanism.

use ed25519_dalek::{Signature, VerifyingKey};
use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Serde helper for `[u8; 64]` (Ed25519 signatures).
mod serde_sig64 {
    use super::*;
    pub fn serialize<S: Serializer>(bytes: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().serialize(ser)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(de)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes"))
    }
}

/// A price attestation from an oracle.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PriceAttestation {
    /// The asset pair (e.g., "ETH/USD").
    pub asset_pair: String,
    /// Price in the smallest unit (e.g., cents for USD).
    pub price: u64,
    /// Unix timestamp when this price was observed.
    pub timestamp: u64,
    /// The oracle's public key (Ed25519, 32 bytes).
    pub oracle_pubkey: [u8; 32],
    /// Ed25519 signature over `(asset_pair, price, timestamp)`.
    #[serde(with = "serde_sig64")]
    pub signature: [u8; 64],
}

impl PriceAttestation {
    /// Compute the oracle commitment for this attestation.
    ///
    /// This is the value that gets bound as a public input in the CDP circuit.
    /// commitment = Poseidon2(price, timestamp, oracle_pk_hash)
    pub fn commitment(&self) -> BabyBear {
        let price_field = BabyBear::from_u64(self.price);
        let timestamp_field = BabyBear::from_u64(self.timestamp);
        let pk_hash = BabyBear::from_u64(
            u64::from_le_bytes(self.oracle_pubkey[0..8].try_into().unwrap())
                % pyana_circuit::field::BABYBEAR_P as u64,
        );
        poseidon2::hash_fact(price_field, &[timestamp_field, pk_hash])
    }

    /// Compute the message bytes that should be signed.
    /// Message = asset_pair_bytes || price_le_bytes || timestamp_le_bytes
    pub fn message_bytes(&self) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(self.asset_pair.as_bytes());
        msg.extend_from_slice(&self.price.to_le_bytes());
        msg.extend_from_slice(&self.timestamp.to_le_bytes());
        msg
    }

    /// Verify the Ed25519 signature over the attestation message.
    ///
    /// Returns Ok(()) if the signature is valid, Err if invalid or the key is malformed.
    pub fn verify_signature(&self) -> Result<(), OracleError> {
        // Reject placeholder signatures (all zeros)
        if self.signature == [0u8; 64] {
            return Err(OracleError::InvalidSignature);
        }

        let verifying_key = VerifyingKey::from_bytes(&self.oracle_pubkey)
            .map_err(|_| OracleError::InvalidSignature)?;

        let signature =
            Signature::from_bytes(&self.signature);

        let msg = self.message_bytes();

        use ed25519_dalek::Verifier;
        verifying_key
            .verify(&msg, &signature)
            .map_err(|_| OracleError::InvalidSignature)
    }
}

/// Price oracle configuration.
#[derive(Clone, Debug)]
pub struct PriceOracle {
    /// Trusted oracle public keys.
    trusted_keys: Vec<[u8; 32]>,
    /// Maximum allowed age for a price attestation (in seconds/blocks).
    pub max_age: u64,
    /// Latest attestations per asset pair.
    latest_prices: Vec<PriceAttestation>,
}

/// Errors from oracle operations.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum OracleError {
    #[error("oracle key {key:?} is not trusted")]
    UntrustedOracle { key: [u8; 32] },
    #[error("price attestation is stale: age {age} exceeds max {max_age}")]
    StalePrice { age: u64, max_age: u64 },
    #[error("no price available for asset pair: {pair}")]
    NoPriceAvailable { pair: String },
    #[error("signature verification failed")]
    InvalidSignature,
}

impl PriceOracle {
    /// Create a new price oracle with the given trusted keys and max age.
    pub fn new(trusted_keys: Vec<[u8; 32]>, max_age: u64) -> Self {
        Self {
            trusted_keys,
            max_age,
            latest_prices: Vec::new(),
        }
    }

    /// Submit a price attestation.
    ///
    /// Verifies:
    /// 1. The oracle key is in the trusted set
    /// 2. The Ed25519 signature is valid over (asset_pair || price || timestamp)
    /// 3. The attestation is fresh (not stale)
    pub fn submit_attestation(
        &mut self,
        attestation: PriceAttestation,
        current_time: u64,
    ) -> Result<(), OracleError> {
        // Check oracle is trusted
        if !self.trusted_keys.contains(&attestation.oracle_pubkey) {
            return Err(OracleError::UntrustedOracle {
                key: attestation.oracle_pubkey,
            });
        }

        // Verify Ed25519 signature
        attestation.verify_signature()?;

        // Check freshness
        let age = current_time.saturating_sub(attestation.timestamp);
        if age > self.max_age {
            return Err(OracleError::StalePrice {
                age,
                max_age: self.max_age,
            });
        }

        // Store (replace previous for same asset pair)
        self.latest_prices
            .retain(|p| p.asset_pair != attestation.asset_pair);
        self.latest_prices.push(attestation);
        Ok(())
    }

    /// Get the latest price for an asset pair.
    pub fn get_price(
        &self,
        asset_pair: &str,
        current_time: u64,
    ) -> Result<&PriceAttestation, OracleError> {
        let attestation = self
            .latest_prices
            .iter()
            .find(|p| p.asset_pair == asset_pair)
            .ok_or_else(|| OracleError::NoPriceAvailable {
                pair: asset_pair.to_string(),
            })?;

        // Re-check freshness at query time
        let age = current_time.saturating_sub(attestation.timestamp);
        if age > self.max_age {
            return Err(OracleError::StalePrice {
                age,
                max_age: self.max_age,
            });
        }

        Ok(attestation)
    }

    /// Check if a price commitment matches the latest attestation for an asset pair.
    pub fn verify_commitment(
        &self,
        asset_pair: &str,
        commitment: BabyBear,
        current_time: u64,
    ) -> Result<bool, OracleError> {
        let attestation = self.get_price(asset_pair, current_time)?;
        Ok(attestation.commitment() == commitment)
    }

    /// Add a trusted oracle key.
    pub fn add_trusted_key(&mut self, key: [u8; 32]) {
        if !self.trusted_keys.contains(&key) {
            self.trusted_keys.push(key);
        }
    }

    /// Remove a trusted oracle key.
    pub fn remove_trusted_key(&mut self, key: &[u8; 32]) {
        self.trusted_keys.retain(|k| k != key);
    }

    /// List all trusted oracle keys.
    pub fn trusted_keys(&self) -> &[[u8; 32]] {
        &self.trusted_keys
    }
}

/// Helper: create a test attestation with a real Ed25519 signature.
///
/// The `oracle_key` parameter is treated as the 32-byte Ed25519 SIGNING key.
/// The public key (for trusted_keys) is derived and stored in `oracle_pubkey`.
/// This maintains backward compatibility — callers pass the same key to both
/// `PriceOracle::new(trusted_keys)` and `test_attestation()`, but must now pass
/// the DERIVED public key to trusted_keys.
///
/// For the common test pattern: use `test_oracle_pubkey(signing_key)` to derive
/// the pubkey for the trusted_keys list.
pub fn test_attestation(
    asset_pair: &str,
    price: u64,
    timestamp: u64,
    oracle_key: [u8; 32],
) -> PriceAttestation {
    test_attestation_signed(asset_pair, price, timestamp, &oracle_key)
}

/// Helper: create a test attestation with a real Ed25519 signature.
///
/// The `signing_key_bytes` must be the 32-byte Ed25519 secret key.
/// The oracle_pubkey field is set to the derived verifying key.
pub fn test_attestation_signed(
    asset_pair: &str,
    price: u64,
    timestamp: u64,
    signing_key_bytes: &[u8; 32],
) -> PriceAttestation {
    use ed25519_dalek::{Signer, SigningKey};

    let signing_key = SigningKey::from_bytes(signing_key_bytes);
    let oracle_pubkey: [u8; 32] = signing_key.verifying_key().to_bytes();

    let mut msg = Vec::new();
    msg.extend_from_slice(asset_pair.as_bytes());
    msg.extend_from_slice(&price.to_le_bytes());
    msg.extend_from_slice(&timestamp.to_le_bytes());

    let sig = signing_key.sign(&msg);

    PriceAttestation {
        asset_pair: asset_pair.to_string(),
        price,
        timestamp,
        oracle_pubkey,
        signature: sig.to_bytes(),
    }
}

/// Derive the Ed25519 public key from a signing key (for use in trusted_keys lists).
pub fn test_oracle_pubkey(signing_key: &[u8; 32]) -> [u8; 32] {
    use ed25519_dalek::SigningKey;
    let sk = SigningKey::from_bytes(signing_key);
    sk.verifying_key().to_bytes()
}

/// Helper: create a test attestation WITHOUT a real signature (for testing rejection).
pub fn test_attestation_unsigned(
    asset_pair: &str,
    price: u64,
    timestamp: u64,
    oracle_key: [u8; 32],
) -> PriceAttestation {
    PriceAttestation {
        asset_pair: asset_pair.to_string(),
        price,
        timestamp,
        oracle_pubkey: oracle_key,
        signature: [0u8; 64], // placeholder — will be rejected by verify_signature()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // A fixed test signing key (32 bytes) — the pubkey is derived from this.
    const TEST_SIGNING_KEY: [u8; 32] = [0x01; 32];

    fn test_oracle_pubkey() -> [u8; 32] {
        use ed25519_dalek::SigningKey;
        let sk = SigningKey::from_bytes(&TEST_SIGNING_KEY);
        sk.verifying_key().to_bytes()
    }

    #[test]
    fn submit_and_query_price() {
        let pubkey = test_oracle_pubkey();
        let mut oracle = PriceOracle::new(vec![pubkey], 100);
        let attestation = test_attestation_signed("ETH/USD", 2000_00, 50, &TEST_SIGNING_KEY);
        oracle.submit_attestation(attestation, 60).unwrap();

        let price = oracle.get_price("ETH/USD", 70).unwrap();
        assert_eq!(price.price, 2000_00);
    }

    #[test]
    fn invalid_signature_rejected() {
        let pubkey = test_oracle_pubkey();
        let mut oracle = PriceOracle::new(vec![pubkey], 100);
        // Use the unsigned helper — should be rejected
        let attestation = test_attestation_unsigned("ETH/USD", 2000_00, 50, pubkey);
        let result = oracle.submit_attestation(attestation, 60);
        assert!(matches!(result, Err(OracleError::InvalidSignature)));
    }

    #[test]
    fn stale_price_rejected_on_submit() {
        let pubkey = test_oracle_pubkey();
        let mut oracle = PriceOracle::new(vec![pubkey], 100);
        let attestation = test_attestation_signed("ETH/USD", 2000_00, 10, &TEST_SIGNING_KEY);
        let result = oracle.submit_attestation(attestation, 200);
        assert!(matches!(result, Err(OracleError::StalePrice { .. })));
    }

    #[test]
    fn stale_price_rejected_on_query() {
        let pubkey = test_oracle_pubkey();
        let mut oracle = PriceOracle::new(vec![pubkey], 100);
        let attestation = test_attestation_signed("ETH/USD", 2000_00, 50, &TEST_SIGNING_KEY);
        oracle.submit_attestation(attestation, 60).unwrap();

        // Query at time 200: age = 200 - 50 = 150 > max_age(100)
        let result = oracle.get_price("ETH/USD", 200);
        assert!(matches!(result, Err(OracleError::StalePrice { .. })));
    }

    #[test]
    fn untrusted_oracle_rejected() {
        let pubkey = test_oracle_pubkey();
        let mut oracle = PriceOracle::new(vec![pubkey], 100);
        // Use a different signing key (untrusted pubkey)
        let bad_signing_key = [0xFF; 32];
        let attestation = test_attestation_signed("ETH/USD", 2000_00, 50, &bad_signing_key);
        let result = oracle.submit_attestation(attestation, 60);
        assert!(matches!(result, Err(OracleError::UntrustedOracle { .. })));
    }

    #[test]
    fn commitment_deterministic() {
        let a1 = test_attestation_signed("ETH/USD", 2000, 100, &TEST_SIGNING_KEY);
        let a2 = test_attestation_signed("ETH/USD", 2000, 100, &TEST_SIGNING_KEY);
        assert_eq!(a1.commitment(), a2.commitment());

        // Different price => different commitment
        let a3 = test_attestation_signed("ETH/USD", 3000, 100, &TEST_SIGNING_KEY);
        assert_ne!(a1.commitment(), a3.commitment());
    }

    #[test]
    fn verify_signature_works() {
        let attestation = test_attestation_signed("BTC/USD", 50000_00, 1000, &TEST_SIGNING_KEY);
        assert!(attestation.verify_signature().is_ok());
    }

    #[test]
    fn tampered_price_fails_signature() {
        let mut attestation =
            test_attestation_signed("BTC/USD", 50000_00, 1000, &TEST_SIGNING_KEY);
        // Tamper with the price after signing
        attestation.price = 99999_99;
        assert!(attestation.verify_signature().is_err());
    }
}
