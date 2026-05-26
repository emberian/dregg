//! Threshold signature integration using the `hints` crate.
//!
//! This module wraps the hints weighted threshold signature scheme (BLS12-381 + KZG)
//! to provide constant-size quorum certificates for the federation. Instead of
//! collecting N x 64-byte Ed25519 signatures, a quorum certificate is ONE aggregate
//! BLS signature regardless of committee size.
//!
//! # Architecture
//!
//! - [`FederationCommittee`]: Holds the hints setup (GlobalData, UniverseSetup) for a
//!   fixed set of federation members with equal weights.
//! - [`ThresholdQC`]: A constant-size aggregate signature proving that a weighted
//!   threshold of committee members signed a message.
//! - [`MemberSecret`]: A member's BLS secret key and precomputed hint for signing.

use std::sync::Arc;

use ark_ff::One;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};

use hints::{
    self, Aggregator, GlobalData, Hint, HintsError, PartialSignature, PublicKey as BlsPublicKey,
    SecretKey as BlsSecretKey, Signature as BlsSignature, UniverseSetup, Verifier, generate_hint,
    setup_universe, sign as bls_sign, sign_aggregate, snark::F, verify_aggregate,
};

// =============================================================================
// FederationCommittee
// =============================================================================

/// A federation committee configured for threshold signatures.
///
/// This encapsulates the hints trusted setup, universe setup, and provides
/// methods for signing, aggregation, and verification.
#[derive(Clone)]
pub struct FederationCommittee {
    /// The global KZG parameters (from trusted setup or random generation).
    pub global: Arc<GlobalData>,
    /// The universe setup for this specific committee.
    pub universe: UniverseSetup,
    /// Number of members (n-1 in hints terms, since hints uses power-of-2 domain).
    pub num_members: usize,
    /// The BFT threshold as a field element.
    pub threshold: F,
    /// The threshold as a u64 for display/comparison.
    pub threshold_value: u64,
}

/// A member's secret material for participating in threshold signing.
#[derive(Clone)]
pub struct MemberSecret {
    /// The member's BLS secret key.
    pub secret_key: BlsSecretKey,
    /// The member's BLS public key.
    pub public_key: BlsPublicKey,
    /// The member's index in the committee.
    pub index: usize,
}

/// A threshold quorum certificate: one constant-size aggregate BLS signature
/// proving that a weighted threshold of committee members approved a message.
#[derive(Clone, Debug)]
pub struct ThresholdQC {
    /// The aggregate BLS signature with SNARK proof.
    signature: BlsSignature,
    /// The threshold that was required.
    threshold: F,
}

// Custom Serialize/Deserialize for ThresholdQC using ark_serialize
impl Serialize for ThresholdQC {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let bytes = self.to_bytes();
        serializer.serialize_bytes(&bytes)
    }
}

impl<'de> Deserialize<'de> for ThresholdQC {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let bytes: Vec<u8> = Deserialize::deserialize(deserializer)?;
        Self::from_bytes(&bytes)
            .ok_or_else(|| serde::de::Error::custom("invalid ThresholdQC bytes"))
    }
}

// =============================================================================
// Error type
// =============================================================================

/// Errors from the threshold signature layer.
#[derive(Debug)]
pub enum ThresholdError {
    /// The hints library returned an error.
    Hints(HintsError),
    /// Not enough partial signatures to meet threshold.
    InsufficientSignatures,
    /// Verification of the aggregate signature failed.
    VerificationFailed,
    /// Serialization/deserialization error.
    SerializationError(String),
}

impl std::fmt::Display for ThresholdError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ThresholdError::Hints(e) => write!(f, "threshold signature error: {}", e),
            ThresholdError::InsufficientSignatures => {
                write!(f, "not enough partial signatures to meet threshold")
            }
            ThresholdError::VerificationFailed => {
                write!(f, "aggregate signature verification failed")
            }
            ThresholdError::SerializationError(s) => {
                write!(f, "serialization error: {}", s)
            }
        }
    }
}

impl std::error::Error for ThresholdError {}

impl From<HintsError> for ThresholdError {
    fn from(e: HintsError) -> Self {
        ThresholdError::Hints(e)
    }
}

// =============================================================================
// FederationCommittee implementation
// =============================================================================

impl FederationCommittee {
    /// Create a new federation committee with the given member keys, equal weights,
    /// and a BFT threshold.
    ///
    /// Uses a random KZG setup with OS-provided entropy. For production with
    /// auditable parameters, use `new_with_eth_setup` which uses the Ethereum
    /// KZG ceremony.
    ///
    /// `num_members` must be <= 63 (since hints requires power-of-2 domain, and
    /// the max supported degree with random setup depends on the RNG).
    pub fn new(member_secrets: &[MemberSecret], threshold: u64) -> Result<Self, ThresholdError> {
        Self::new_with_rng(member_secrets, threshold, &mut ark_std::rand::rngs::OsRng)
    }

    /// Create a new federation committee with a caller-supplied RNG.
    ///
    /// This is the inner constructor that both `new` (OsRng) and
    /// `new_deterministic` (test_rng) delegate to.
    pub fn new_with_rng(
        member_secrets: &[MemberSecret],
        threshold: u64,
        rng: &mut impl ark_std::rand::RngCore,
    ) -> Result<Self, ThresholdError> {
        let num_members = member_secrets.len();
        // hints requires domain size to be a power of 2, with exactly domain_size-1 parties.
        let domain_size = (num_members + 1).next_power_of_two();

        let gd = GlobalData::new(domain_size, rng)?;

        Self::from_global_data(gd, member_secrets, threshold)
    }

    /// Create a new federation committee with a deterministic test RNG.
    ///
    /// # Security
    /// **This must only be used in tests.** The RNG is seeded with a fixed value,
    /// meaning the KZG toxic waste is known and proofs can be forged.
    #[cfg(test)]
    pub fn new_deterministic(
        member_secrets: &[MemberSecret],
        threshold: u64,
    ) -> Result<Self, ThresholdError> {
        Self::new_with_rng(member_secrets, threshold, &mut ark_std::test_rng())
    }

    /// Create a committee using the Ethereum KZG trusted setup.
    ///
    /// Supports up to 63 members (limited by the Ethereum ceremony's 64-degree max).
    pub fn new_with_eth_setup(
        member_secrets: &[MemberSecret],
        threshold: u64,
    ) -> Result<Self, ThresholdError> {
        let num_members = member_secrets.len();
        let domain_size = (num_members + 1).next_power_of_two();

        if domain_size > 64 {
            return Err(ThresholdError::Hints(HintsError::InvalidInput(
                "Ethereum KZG setup supports at most 63 members (domain 64)".to_string(),
            )));
        }

        let gd = hints::setup_eth(domain_size)?;
        Self::from_global_data(gd, member_secrets, threshold)
    }

    /// Internal constructor from pre-existing GlobalData.
    ///
    /// hints requires exactly `domain_size - 1` participants. If we have fewer
    /// real members, we pad with zero-weight dummy members.
    fn from_global_data(
        gd: Arc<GlobalData>,
        member_secrets: &[MemberSecret],
        threshold: u64,
    ) -> Result<Self, ThresholdError> {
        let num_members = member_secrets.len();
        // domain_size is the power-of-2 "n" for the polynomial domain.
        // hints expects exactly n-1 participants.
        let domain_size = (num_members + 1).next_power_of_two();

        let total_slots = domain_size - 1; // total participant slots expected by hints

        // Collect real member public keys
        let mut pks: Vec<BlsPublicKey> = member_secrets
            .iter()
            .map(|m| m.public_key.clone())
            .collect();

        // Generate hints for real members
        let mut all_hints: Vec<Hint> = member_secrets
            .iter()
            .map(|m| generate_hint(&gd, &m.secret_key, domain_size, m.index))
            .collect::<Result<Vec<_>, _>>()?;

        // Weights: real members get weight 1, padding members get weight 0
        let mut weights: Vec<F> = vec![F::one(); num_members];

        // Pad with dummy members (zero-weight, dummy keys)
        let dummy_sk = BlsSecretKey::dummy();
        let dummy_pk = dummy_sk.public(&gd);
        for i in num_members..total_slots {
            pks.push(dummy_pk.clone());
            all_hints.push(generate_hint(&gd, &dummy_sk, domain_size, i)?);
            weights.push(F::from(0u64));
        }

        // Setup the universe
        let universe = setup_universe(&gd, pks, &all_hints, weights)?;

        if !universe.party_errors.is_empty() {
            return Err(ThresholdError::Hints(HintsError::InvalidInput(format!(
                "Party errors during setup: {:?}",
                universe.party_errors
            ))));
        }

        let threshold_f = F::from(threshold);

        Ok(Self {
            global: gd,
            universe,
            num_members,
            threshold: threshold_f,
            threshold_value: threshold,
        })
    }

    /// Sign a message as a committee member, producing a partial signature.
    pub fn sign_share(&self, member: &MemberSecret, message: &[u8]) -> PartialSignature {
        bls_sign(&member.secret_key, message)
    }

    /// Aggregate partial signatures into a threshold QC.
    ///
    /// `shares` is a list of (member_index, partial_signature) pairs.
    /// Returns `None` if the threshold is not met or signatures are invalid.
    pub fn aggregate(
        &self,
        shares: &[(usize, PartialSignature)],
        message: &[u8],
    ) -> Result<ThresholdQC, ThresholdError> {
        let aggregator = self.universe.aggregator();
        let sig = sign_aggregate(&aggregator, self.threshold, shares, message)?;
        Ok(ThresholdQC {
            signature: sig,
            threshold: self.threshold,
        })
    }

    /// Verify a threshold QC against this committee.
    pub fn verify(&self, qc: &ThresholdQC, message: &[u8]) -> Result<(), ThresholdError> {
        if qc.threshold < self.threshold {
            return Err(ThresholdError::VerificationFailed);
        }

        let verifier = self.universe.verifier();
        verify_aggregate(&verifier, &qc.signature, message)
            .map_err(|_| ThresholdError::VerificationFailed)
    }

    /// Get the verifier for this committee (can be stored separately for lightweight verification).
    pub fn verifier(&self) -> Verifier {
        self.universe.verifier()
    }

    /// Get the aggregator for this committee.
    pub fn aggregator(&self) -> Aggregator {
        self.universe.aggregator()
    }
}

// =============================================================================
// MemberSecret implementation
// =============================================================================

impl MemberSecret {
    /// Generate a new random BLS keypair for a committee member.
    pub fn generate(gd: &GlobalData, index: usize) -> Self {
        let mut rng = ark_std::rand::thread_rng();
        let (sk, pk) = hints::generate_keypair(gd, &mut rng);
        Self {
            secret_key: sk,
            public_key: pk,
            index,
        }
    }

    /// Generate a member secret from a test RNG (deterministic, for testing).
    pub fn generate_deterministic(gd: &GlobalData, index: usize) -> Self {
        let mut rng = ark_std::test_rng();
        let (sk, pk) = hints::generate_keypair(gd, &mut rng);
        Self {
            secret_key: sk,
            public_key: pk,
            index,
        }
    }
}

// =============================================================================
// ThresholdQC implementation
// =============================================================================

impl ThresholdQC {
    /// Verify this QC against a verifier.
    pub fn verify_with(&self, verifier: &Verifier, message: &[u8]) -> bool {
        verify_aggregate(verifier, &self.signature, message).is_ok()
    }

    /// Serialize to bytes (compressed arkworks serialization).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.signature
            .serialize_compressed(&mut buf)
            .expect("serialization should not fail");
        buf
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let signature = BlsSignature::deserialize_compressed(bytes).ok()?;
        let threshold = signature.threshold;
        Some(Self {
            signature,
            threshold,
        })
    }

    /// Get the threshold value from the signature.
    pub fn threshold(&self) -> F {
        self.threshold
    }
}

// =============================================================================
// Utility: generate a full test committee
// =============================================================================

/// Generate a full test committee with `n` members and threshold `t`.
///
/// Returns the committee and all member secrets. Uses a deterministic RNG
/// for reproducibility in tests.
pub fn generate_test_committee(
    n: usize,
    threshold: u64,
) -> Result<(FederationCommittee, Vec<MemberSecret>), ThresholdError> {
    generate_test_committee_with_rng(n, threshold, &mut ark_std::test_rng())
}

/// Generate a full test committee with `n` members and threshold `t` from a
/// caller-supplied seed.
///
/// This keeps integration fixtures reproducible while allowing tests to build
/// two genuinely distinct committees in the same process.
pub fn generate_test_committee_with_seed(
    n: usize,
    threshold: u64,
    seed: [u8; 32],
) -> Result<(FederationCommittee, Vec<MemberSecret>), ThresholdError> {
    let mut rng = StdRng::from_seed(seed);
    generate_test_committee_with_rng(n, threshold, &mut rng)
}

fn generate_test_committee_with_rng(
    n: usize,
    threshold: u64,
    rng: &mut impl ark_std::rand::RngCore,
) -> Result<(FederationCommittee, Vec<MemberSecret>), ThresholdError> {
    let domain_size = (n + 1).next_power_of_two();

    let gd = GlobalData::new(domain_size, rng)?;

    // Generate member secrets from the same fixture RNG so repeated seeded
    // calls are reproducible.
    let members: Vec<MemberSecret> = (0..n)
        .map(|i| {
            let sk = BlsSecretKey::random(&mut *rng);
            let pk = sk.public(&gd);
            MemberSecret {
                secret_key: sk,
                public_key: pk,
                index: i,
            }
        })
        .collect();

    let committee = FederationCommittee::from_global_data(gd, &members, threshold)?;
    Ok((committee, members))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_threshold_sign_and_verify() {
        // 4 members, threshold 3 (BFT: can tolerate 1 fault)
        let (committee, members) = generate_test_committee(4, 3).unwrap();

        let message = b"dregg-federation-vote-v1:deadbeef";

        // Collect partial signatures from 3 out of 4 members
        let shares: Vec<(usize, PartialSignature)> = members[0..3]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, message)))
            .collect();

        // Aggregate
        let qc = committee.aggregate(&shares, message).unwrap();

        // Verify
        assert!(committee.verify(&qc, message).is_ok());
    }

    #[test]
    fn test_threshold_not_met() {
        // 4 members, threshold 3
        let (committee, members) = generate_test_committee(4, 3).unwrap();

        let message = b"test message";

        // Only 2 signatures (below threshold of 3)
        let shares: Vec<(usize, PartialSignature)> = members[0..2]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, message)))
            .collect();

        // Should fail
        let result = committee.aggregate(&shares, message);
        assert!(result.is_err());
    }

    #[test]
    fn test_threshold_wrong_message_fails_verification() {
        let (committee, members) = generate_test_committee(4, 3).unwrap();

        let message = b"correct message";
        let wrong_message = b"wrong message";

        let shares: Vec<(usize, PartialSignature)> = members[0..3]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, message)))
            .collect();

        let qc = committee.aggregate(&shares, message).unwrap();

        // Verify with wrong message should fail
        assert!(committee.verify(&qc, wrong_message).is_err());
    }

    #[test]
    fn test_threshold_qc_below_committee_threshold_rejected() {
        let (weak_committee, members) =
            generate_test_committee_with_seed(4, 2, [77u8; 32]).unwrap();
        let strong_committee =
            FederationCommittee::from_global_data(weak_committee.global.clone(), &members, 3)
                .unwrap();

        let message = b"threshold downgrade attempt";
        let shares: Vec<(usize, PartialSignature)> = members[0..2]
            .iter()
            .map(|m| (m.index, weak_committee.sign_share(m, message)))
            .collect();

        let qc = weak_committee.aggregate(&shares, message).unwrap();
        assert!(weak_committee.verify(&qc, message).is_ok());
        assert!(
            strong_committee.verify(&qc, message).is_err(),
            "QC aggregated below the committee threshold must not verify"
        );
    }

    #[test]
    fn test_threshold_qc_serialization() {
        let (committee, members) = generate_test_committee(4, 3).unwrap();

        let message = b"serialization test";

        let shares: Vec<(usize, PartialSignature)> = members[0..3]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, message)))
            .collect();

        let qc = committee.aggregate(&shares, message).unwrap();

        // Round-trip serialize
        let bytes = qc.to_bytes();
        let qc2 = ThresholdQC::from_bytes(&bytes).unwrap();

        // Verify the deserialized QC
        assert!(committee.verify(&qc2, message).is_ok());
    }

    #[test]
    fn test_constant_size_regardless_of_committee() {
        // The whole point: QC size should not grow with committee size.
        let (committee_4, members_4) = generate_test_committee(4, 3).unwrap();
        let (committee_7, members_7) = generate_test_committee(7, 5).unwrap();

        let message = b"size test";

        let shares_4: Vec<(usize, PartialSignature)> = members_4[0..3]
            .iter()
            .map(|m| (m.index, committee_4.sign_share(m, message)))
            .collect();

        let shares_7: Vec<(usize, PartialSignature)> = members_7[0..5]
            .iter()
            .map(|m| (m.index, committee_7.sign_share(m, message)))
            .collect();

        let qc_4 = committee_4.aggregate(&shares_4, message).unwrap();
        let qc_7 = committee_7.aggregate(&shares_7, message).unwrap();

        let bytes_4 = qc_4.to_bytes();
        let bytes_7 = qc_7.to_bytes();

        // Both should be the same size (constant-size aggregate signature)
        assert_eq!(
            bytes_4.len(),
            bytes_7.len(),
            "QC size should be constant regardless of committee size: {} vs {}",
            bytes_4.len(),
            bytes_7.len()
        );
    }

    #[test]
    fn test_all_members_sign() {
        let (committee, members) = generate_test_committee(4, 3).unwrap();

        let message = b"all sign";

        // All 4 members sign
        let shares: Vec<(usize, PartialSignature)> = members
            .iter()
            .map(|m| (m.index, committee.sign_share(m, message)))
            .collect();

        let qc = committee.aggregate(&shares, message).unwrap();
        assert!(committee.verify(&qc, message).is_ok());
    }
}
