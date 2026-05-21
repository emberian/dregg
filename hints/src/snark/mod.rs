//! SNARK for certifying weighted aggregation (implementation detail)

use std::sync::Arc;

use ark_ec::VariableBaseMSM;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::RngCore;
use ark_std::{One, Zero};

use crate::utils;
use crate::{kzg::*, GlobalData, HintsError, PublicKey};

mod hints;
mod prover;
mod verifier;

pub use hints::*;
pub use prover::*;
pub use verifier::*;

// ark_blst includes a GPU-"accelerated" backend for msm but it's actually
// substantially slower than the CPU in benchmarks (measured on an M2 Pro)

pub type Curve = ark_bls12_381::Bls12_381;

pub type KZG = KZG10<Curve, UniPoly381>;
pub type UniPoly381 = DensePolynomial<<Curve as Pairing>::ScalarField>;
pub type F = <Curve as Pairing>::ScalarField;
pub type G1 = <Curve as Pairing>::G1Affine;
pub type G2 = <Curve as Pairing>::G2Affine;
pub type G1Projective = <Curve as Pairing>::G1;
pub type G2Projective = <Curve as Pairing>::G2;

pub const LOCKSTITCH_DOMAIN: &str = "hints-bls12-381-snark";

// Trait to abstract the source of Fiat-Shamir data (VerifierKey or AggregationKey)
pub trait FiatShamirTranscriptData {
    fn mix_fs_data(&self, transcript: &mut lockstitch::Protocol) -> Result<(), HintsError>;
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProofCommitments {
    pub psw_of_x_com: G1,
    pub b_of_x_com: G1,
    pub psw_wff_q_of_x_com: G1,
    pub psw_check_q_of_x_com: G1,
    pub b_wff_q_of_x_com: G1,
    pub b_check_q_of_x_com: G1,
    pub sk_q1_com: G1,
    pub sk_q2_com: G1,
}

impl GlobalData {
    /// Create a new global data from a randomly generated KZG setup.
    pub fn new<R: RngCore>(domain_max: usize, rng: &mut R) -> Result<Arc<Self>, HintsError> {
        let params = KZG::setup(domain_max, rng)?;
        Self::from_params(params)
    }

    /// Create a new global data from the given parameters.
    pub fn from_params(params: UniversalParams<Curve>) -> Result<Arc<Self>, HintsError> {
        Self::from_params_and_domain(params, LOCKSTITCH_DOMAIN.to_string())
    }

    /// Create a new global data from the given parameters.
    ///
    /// Uses `domain` for the lockstitch protocol.
    pub fn from_params_and_domain(
        params: UniversalParams<Curve>,
        domain: String,
    ) -> Result<Arc<Self>, HintsError> {
        let domain_max = params.powers_of_h.len() - 1;

        if domain_max == 0 || domain_max & (domain_max - 1) != 0 {
            return Err(HintsError::InvalidInput(
                "n must be a power of 2".to_string(),
            ));
        }

        if domain_max + 1 > params.powers_of_h.len() {
            return Err(HintsError::PolynomialDegreeTooLarge);
        }

        let lagrange_polynomials: Vec<_> = (0..domain_max)
            .map(|i| utils::lagrange_poly(domain_max, i))
            .collect();

        let lagrange_coms_g1 = lagrange_polynomials
            .iter()
            .map(|h| KZG10::commit_g1(&params, h).unwrap())
            .collect();

        let lagrange_coms_g2 = lagrange_polynomials
            .iter()
            .map(|h| KZG10::commit_g2(&params, h).unwrap())
            .collect();

        let lockstitch = lockstitch::Protocol::new(&domain);

        Ok(Arc::new(Self {
            params,
            domain,
            lagrange_polynomials,
            lagrange_coms_g1,
            lagrange_coms_g2,
            lockstitch,
        }))
    }
}

/// Compute aggregate public key
pub fn compute_apk(
    all_pks: &[PublicKey],
    all_l_polys: &[DensePolynomial<F>],
    full_bitmap: &[F],
) -> G1 {
    let n = full_bitmap.len();
    assert_eq!(all_pks.len(), n, "compute_apk pks length mismatch");
    assert!(
        all_l_polys.len() >= n,
        "compute_apk l_polys length mismatch"
    );

    let unwrapped_pks: Vec<G1> = all_pks.iter().map(|pk| pk.0).collect();
    let exponents: Vec<F> = full_bitmap
        .iter()
        .zip(all_l_polys.iter())
        .map(|(bitmap_value, l_i_of_x)| {
            if bitmap_value.is_one() {
                l_i_of_x.evaluate(&F::zero())
            } else {
                F::zero()
            }
        })
        .collect();

    <<Curve as Pairing>::G1 as VariableBaseMSM>::msm(&unwrapped_pks, &exponents)
        .expect("MSM failed in compute_apk")
        .into_affine()
}

fn mix_object<T: CanonicalSerialize>(
    transcript: &mut lockstitch::Protocol,
    label: &str,
    obj: &T,
) -> Result<(), HintsError> {
    let mut buf = Vec::new();
    obj.serialize_uncompressed(&mut buf)?;
    transcript.mix(label, &buf);
    Ok(())
}

fn derive_field_element(transcript: &mut lockstitch::Protocol, label: &str) -> F {
    let mut buf = [0u8; 48];
    transcript.derive(label, &mut buf);
    F::from_le_bytes_mod_order(&buf)
}

/// Deterministic Fiat-Shamir style challenge point derivation
pub fn compute_challenge_r(
    base_transcript: &lockstitch::Protocol,
    vp_or_ak: &impl FiatShamirTranscriptData,
    agg_pk: &G1,
    agg_weight: &F,
    commitments: &ProofCommitments,
) -> Result<F, HintsError> {
    let mut transcript = base_transcript.clone();

    vp_or_ak.mix_fs_data(&mut transcript)?;

    mix_object(&mut transcript, "agg_pk", agg_pk)?;
    mix_object(&mut transcript, "agg_weight", agg_weight)?;
    mix_object(&mut transcript, "psw_com", &commitments.psw_of_x_com)?;
    mix_object(&mut transcript, "b_com", &commitments.b_of_x_com)?;
    mix_object(
        &mut transcript,
        "psw_wff_q_com",
        &commitments.psw_wff_q_of_x_com,
    )?;
    mix_object(
        &mut transcript,
        "psw_check_q_com",
        &commitments.psw_check_q_of_x_com,
    )?;
    mix_object(
        &mut transcript,
        "b_wff_q_com",
        &commitments.b_wff_q_of_x_com,
    )?;
    mix_object(
        &mut transcript,
        "b_check_q_com",
        &commitments.b_check_q_of_x_com,
    )?;
    mix_object(&mut transcript, "sk_q1_com", &commitments.sk_q1_com)?;
    mix_object(&mut transcript, "sk_q2_com", &commitments.sk_q2_com)?;

    Ok(derive_field_element(&mut transcript, "challenge_r"))
}

impl FiatShamirTranscriptData for VerifierKey {
    fn mix_fs_data(&self, transcript: &mut lockstitch::Protocol) -> Result<(), HintsError> {
        mix_object(transcript, "degree_max", &self.degree_max)?;
        mix_object(transcript, "ln-1_com", &self.l_n_minus_1_of_x_com)?;
        mix_object(transcript, "w_com", &self.w_of_x_com)?;
        mix_object(transcript, "sk_com", &self.sk_of_x_com)?;
        mix_object(transcript, "vanish_com", &self.vanishing_com)?;
        mix_object(transcript, "x_mono_com", &self.x_monomial_com)?;
        // Bind individual PKs, weights, and excluded indices to prevent
        // selective-disclosure attacks on the aggregate
        for pk in self.pks.iter() {
            mix_object(transcript, "pk", &pk.0)?;
        }
        for w in self.weights.iter() {
            mix_object(transcript, "weight", w)?;
        }
        mix_object(transcript, "failed_indices", &self.failed_hint_indices)?;
        Ok(())
    }
}

impl FiatShamirTranscriptData for AggregationKey {
    fn mix_fs_data(&self, transcript: &mut lockstitch::Protocol) -> Result<(), HintsError> {
        mix_object(transcript, "degree_max", &self.degree_max)?;
        mix_object(transcript, "ln-1_com", &self.vk_l_n_minus_1_com)?;
        mix_object(transcript, "w_com", &self.vk_w_of_x_com)?;
        mix_object(transcript, "sk_com", &self.vk_sk_of_x_com)?;
        mix_object(transcript, "vanish_com", &self.vk_vanishing_com)?;
        mix_object(transcript, "x_mono_com", &self.vk_x_monomial_com)?;
        // Bind individual PKs, weights, and excluded indices (must match VerifierKey)
        for pk in self.pks.iter() {
            mix_object(transcript, "pk", &pk.0)?;
        }
        for w in self.weights.iter() {
            mix_object(transcript, "weight", w)?;
        }
        mix_object(transcript, "failed_indices", &self.failed_hint_indices)?;
        Ok(())
    }
}
