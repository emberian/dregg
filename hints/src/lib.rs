#![doc = include_str!("../README.md")]

use std::sync::Arc;

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_std::{rand::RngCore, vec::Vec, UniformRand};

pub mod kzg;
pub mod snark;
pub(crate) mod trusted_setup;
mod types;
pub mod utils;

use kzg::UniversalParams;
use snark::*;
pub use snark::{F, G1, G2};
pub use trusted_setup::*;
pub use types::*;

impl SecretKey {
    /// Generate a random secret key.
    pub fn random(rng: &mut impl RngCore) -> Self {
        Self(F::rand(rng))
    }

    /// A dummy secret key for testing.
    pub fn dummy() -> Self {
        Self(F::from(-1i64))
    }

    /// Derive the public key from this secret key.
    pub fn public(&self, gd: &GlobalData) -> PublicKey {
        PublicKey((gd.params.powers_of_g[0] * self.0).into_affine())
    }
}

/// Generate a hint for a party's secret key.
///
/// Does not depend on the weights or other keys present. Can be re-used.
pub fn generate_hint(
    gd: &GlobalData,
    sk: &SecretKey,
    n: usize,
    i: usize,
) -> Result<Hint, HintsError> {
    gd.generate_hint(sk, n, i)
}

/// Setup a universe of participants.
///
/// Needs to be done whenever weights changes.
pub fn setup_universe(
    gd: &Arc<GlobalData>,
    keys: Vec<PublicKey>,
    hints: &[Hint],
    weights: Vec<F>,
) -> Result<UniverseSetup, HintsError> {
    gd.setup_universe(keys, hints, weights)
}

/// Setup: Generate the Common Reference String (CRS) for a maximum degree.
///
/// Uses the Ethereum KZG trusted setup. Maximum supported max_degree is 64.
pub fn setup_eth(max_degree: usize) -> Result<Arc<GlobalData>, HintsError> {
    let ts = crate::trusted_setup::JsonTrustedSetup::default().deserialize::<Curve>()?;
    if max_degree > 64 {
        return Err(HintsError::InvalidInput(
            "Maximum supported max_degree with setup_eth is 64 (ceremony limitation)".to_string(),
        ));
    }
    let mut params = UniversalParams {
        powers_of_g: ts.g1_points.to_vec(),
        powers_of_h: ts.g2_points.to_vec(),
    };
    params.truncate(max_degree);
    GlobalData::from_params(params)
}

/// Generate a BLS key pair.
pub fn generate_keypair<R: RngCore>(gd: &GlobalData, rng: &mut R) -> (SecretKey, PublicKey) {
    let sk = F::rand(rng);
    let pk = gd.params.powers_of_g[0]
        .mul_bigint(sk.into_bigint())
        .into_affine();
    (SecretKey(sk), PublicKey(pk))
}

/// Create a BLS partial signature.
pub fn sign(sk: &SecretKey, msg: &[u8]) -> PartialSignature {
    let h_m = utils::hash_to_g2(msg);
    PartialSignature((h_m * sk.0).into_affine())
}

/// Verify a BLS partial signature.
///
/// Includes subgroup checks on the public key and signature points to
/// prevent invalid-curve / small-order subgroup attacks.
pub fn verify_partial(
    gd: &GlobalData,
    pk: &PublicKey,
    msg: &[u8],
    partial_sig: &PartialSignature,
) -> bool {
    // Reject identity or points not in the prime-order subgroup
    if pk.0.is_zero() || !pk.0.is_in_correct_subgroup_assuming_on_curve() {
        return false;
    }
    if partial_sig.0.is_zero() || !partial_sig.0.is_in_correct_subgroup_assuming_on_curve() {
        return false;
    }
    let g1 = gd.params.powers_of_g[0];
    let h_m = utils::hash_to_g2(msg);
    Curve::pairing(pk.0, h_m) == Curve::pairing(g1, partial_sig.0)
}

/// Aggregate partial signatures and generate the final signature with proof.
fn sign_aggregate_inner(
    agg: &Aggregator,
    threshold: F,
    partial_sigs: &[(usize, PartialSignature)],
    msg: &[u8],
    check_partials: bool,
) -> Result<Signature, HintsError> {
    let n = agg.agg_key.degree_max;
    let mut bitmap = vec![F::zero(); n - 1];
    let mut signer_indices = Vec::new();

    let mut weight_here = F::zero();

    let mut agg_sig = G2Projective::zero();

    // Verify partial signatures and build bitmap
    for (i, partial_sig) in partial_sigs {
        if *i >= n - 1 {
            continue;
        } // Index out of bounds (bitmap has n-1 elements)
        if agg.agg_key.failed_hint_indices.contains(i) {
            continue;
        } // Skip party if hint failed

        let pk = &agg.agg_key.pks[*i];
        if check_partials && !verify_partial(&agg.global, pk, msg, partial_sig) {
            continue;
        }
        bitmap[*i] = F::one();
        agg_sig += partial_sig.0;
        signer_indices.push(*i);
        weight_here += agg.agg_key.weights[*i];
    }

    if weight_here < threshold {
        return Err(HintsError::ThresholdNotMet);
    }

    if agg_sig.is_zero() {
        return Err(HintsError::InvalidInput(
            "No valid partial signatures provided".to_string(),
        ));
    }

    let agg_sig_prime =
        (agg_sig.into_affine() * F::from(n as u64).inverse().unwrap()).into_affine();

    let proof = prove(&agg.global, &agg.agg_key, &agg.agg_key.weights, &bitmap)?;

    // --- Package Signature ---
    Ok(Signature {
        agg_sig_prime,
        threshold,
        proof,
    })
}

/// Aggregate partial signatures and generate validity proof.
///
/// Checks partial signature validity and filters out invalid partials.
pub fn sign_aggregate(
    agg: &Aggregator,
    threshold: F,
    partial_sigs: &[(usize, PartialSignature)],
    msg: &[u8],
) -> Result<Signature, HintsError> {
    let sig = sign_aggregate_inner(agg, threshold, partial_sigs, msg, true)?;
    debug_assert!({
        let h_m = utils::hash_to_g2(msg);

        Curve::pairing(sig.proof.agg_pk, h_m)
            == Curve::pairing(agg.global.params.powers_of_g[0], sig.agg_sig_prime)
    });

    Ok(sig)
}

/// Aggregate partial signatures and generate validity proof.
///
/// Does not check partial signature validity. Use this when you are externally verifying the partials.
pub fn sign_aggregate_unchecked(
    agg: &Aggregator,
    threshold: F,
    partial_sigs: &[(usize, PartialSignature)],
    msg: &[u8],
) -> Result<Signature, HintsError> {
    sign_aggregate_inner(agg, threshold, partial_sigs, msg, false)
}

/// Verify: Check the aggregated signature against the threshold and VK.
pub fn verify_aggregate(verif: &Verifier, sig: &Signature, msg: &[u8]) -> Result<(), HintsError> {
    // 1. Check threshold
    if sig.proof.agg_weight < sig.threshold {
        return Err(HintsError::ThresholdNotMet);
    }

    // 2. Call Internal Verifier (SNARK check)
    // Adapt proof_system::verify signature or call directly
    // It needs vk-like data and the proof parts from sig
    match verify_proof(&verif.global, &verif.vk, &sig.proof) {
        Ok(()) => {}
        Err(e) => {
            return Err(HintsError::ProofVerificationError(format!(
                "SNARK failed to verify: {}",
                e
            )))
        }
    }

    // 3. Final BLS Check
    let h_m = utils::hash_to_g2(msg);
    if Curve::pairing(sig.proof.agg_pk, h_m) != Curve::pairing(verif.vk.g_0, sig.agg_sig_prime) {
        return Err(HintsError::BlsVerificationFailed);
    }

    Ok(())
}

#[cfg(test)]
mod tests;
