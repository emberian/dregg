use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::Field;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::ops::*;

use crate::HintsError;

use super::*;

/// Parameters used for verifying proofs.
#[derive(Clone, Debug, PartialEq, Eq, Hash, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey {
    pub degree_max: usize, //size of the committee as a power of 2
    pub g_0: G1,           //first element from the KZG SRS over G1
    pub h_0: G2,           //first element from the KZG SRS over G2
    pub h_1: G2,           //2nd element from the KZG SRS over G2
    pub l_n_minus_1_of_x_com: G1,
    pub w_of_x_com: G1,
    pub sk_of_x_com: G2, //commitment to the sigma_{i \in [N]} sk_i l_i(x) polynomial
    pub vanishing_com: G2, //commitment to Z(x) = x^n - 1
    pub x_monomial_com: G2, //commentment to f(x) = x
    /// All participant public keys (bound into Fiat-Shamir transcript)
    pub pks: Vec<PublicKey>,
    /// All participant weights (bound into Fiat-Shamir transcript)
    pub weights: Vec<F>,
    /// Indices of participants whose hints failed verification
    pub failed_hint_indices: Vec<usize>,
}

macro_rules! lhs_rhs_eq {
    ($lhs:expr, $rhs:expr, $e:expr) => {
        if $lhs != $rhs {
            return Err(HintsError::VerificationStep($e));
        }
    };
}

fn verify_opening(
    vp: &VerifierKey,
    commitment: &G1,
    point: &F,
    evaluation: &F,
    opening_proof: &G1,
) -> Result<(), HintsError> {
    let eval_com: G1 = vp.g_0.mul(evaluation).into();
    let point_com: G2 = vp.h_0.mul(point).into();

    let lhs = <Curve as Pairing>::pairing(*commitment - eval_com, vp.h_0);
    let rhs = <Curve as Pairing>::pairing(*opening_proof, vp.h_1 - point_com);
    lhs_rhs_eq!(lhs, rhs, "verify_opening");
    Ok(())
}

fn verify_openings(vp: &VerifierKey, π: &Proof, r_expected: &F) -> Result<(), HintsError> {
    //adjust the w_of_x_com
    let adjustment = F::from(0) - π.agg_weight;
    let adjustment_com = vp.l_n_minus_1_of_x_com.mul(adjustment);
    let w_of_x_com: G1 = (vp.w_of_x_com + adjustment_com).into();

    let psw_of_r_argument = π.coms.psw_of_x_com - vp.g_0.mul(π.psw_of_r).into_affine();
    let mut w_of_r_argument = w_of_x_com - vp.g_0.mul(π.w_of_r).into_affine();
    let mut b_of_r_argument = π.coms.b_of_x_com - vp.g_0.mul(π.b_of_r).into_affine();
    let mut psw_wff_q_of_r_argument =
        π.coms.psw_wff_q_of_x_com - vp.g_0.mul(π.psw_wff_q_of_r).into_affine();
    let mut psw_check_q_of_r_argument =
        π.coms.psw_check_q_of_x_com - vp.g_0.mul(π.psw_check_q_of_r).into_affine();
    let mut b_wff_q_of_r_argument =
        π.coms.b_wff_q_of_x_com - vp.g_0.mul(π.b_wff_q_of_r).into_affine();
    let mut b_check_q_of_r_argument =
        π.coms.b_check_q_of_x_com - vp.g_0.mul(π.b_check_q_of_r).into_affine();

    let mut r_pows = *r_expected;
    w_of_r_argument *= r_pows;
    r_pows *= r_expected;
    b_of_r_argument *= r_pows;
    r_pows *= r_expected;
    psw_wff_q_of_r_argument *= r_pows;
    r_pows *= r_expected;
    psw_check_q_of_r_argument *= r_pows;
    r_pows *= r_expected;
    b_wff_q_of_r_argument *= r_pows;
    r_pows *= r_expected;
    b_check_q_of_r_argument *= r_pows;

    let mut merged_argument = psw_of_r_argument;
    merged_argument += w_of_r_argument;
    merged_argument += b_of_r_argument;
    merged_argument += psw_wff_q_of_r_argument;
    merged_argument += psw_check_q_of_r_argument;
    merged_argument += b_wff_q_of_r_argument;
    merged_argument += b_check_q_of_r_argument;
    /* alternative:
        let merged_argument: G1 = (psw_of_r_argument
            + w_of_r_argument
            + b_of_r_argument
            + psw_wff_q_of_r_argument.mul(r_expected.pow([3]))
            + psw_check_q_of_r_argument.mul(r_expected.pow([4]))
            + b_wff_q_of_r_argument.mul(r_expected.pow([5]))
            + b_check_q_of_r_argument.mul(r_expected.pow([6])))
        .into_affine();
    */

    let lhs = <Curve as Pairing>::pairing(merged_argument, vp.h_0);
    let rhs = <Curve as Pairing>::pairing(
        π.merged_proof,
        vp.h_1 - vp.h_0.mul(r_expected).into_affine(),
    );

    lhs_rhs_eq!(lhs, rhs, "merged proofs");

    let domain = Radix2EvaluationDomain::<F>::new(vp.degree_max)
        .ok_or(HintsError::PolynomialDegreeTooLarge)?;
    let ω: F = domain.group_gen;
    let r_div_ω: F = *r_expected / ω;
    verify_opening(
        vp,
        &π.coms.psw_of_x_com,
        &r_div_ω,
        &π.psw_of_r_div_ω,
        &π.psw_of_r_div_ω_proof,
    )
}

/// Verify a proof for an aggregated signature.
pub fn verify_proof(gd: &GlobalData, vp: &VerifierKey, π: &Proof) -> Result<(), HintsError> {
    // --- Fiat-Shamir: Recompute challenge r ---
    let r_expected = compute_challenge_r(
        &gd.lockstitch,
        vp, // VerifierKey implements FiatShamirTranscriptData
        &π.agg_pk,
        &π.agg_weight,
        &π.coms,
    )?;
    lhs_rhs_eq!(r_expected, π.r, "proof.r == r_expected"); // Check if received r matches derived r
                                                           // --- End Fiat-Shamir ---

    let domain = Radix2EvaluationDomain::<F>::new(vp.degree_max)
        .ok_or(HintsError::PolynomialDegreeTooLarge)?;
    let ω: F = domain.group_gen;

    let n: u64 = vp.degree_max as u64;
    let vanishing_of_r: F = r_expected.pow([n]) - F::from(1);

    // compute L_i(r) using the relation L_i(x) = Z_V(x) / ( Z_V'(x) (x - ω^i) )
    // where Z_V'(x)^-1 = x / N for N = |V|.
    let ω_pow_n_minus_1 = ω.pow([n - 1]);
    let l_n_minus_1_of_r =
        (ω_pow_n_minus_1 / F::from(n)) * (vanishing_of_r / (r_expected - ω_pow_n_minus_1));

    verify_openings(vp, π, &r_expected)?;

    let lhs = <Curve as Pairing>::pairing(π.coms.b_of_x_com, vp.sk_of_x_com);
    let x1 = <Curve as Pairing>::pairing(π.coms.sk_q1_com, vp.vanishing_com);
    let x2 = <Curve as Pairing>::pairing(π.coms.sk_q2_com, vp.x_monomial_com);
    let x3 = <Curve as Pairing>::pairing(π.agg_pk, vp.h_0);
    let rhs = x1.add(x2).add(x3);
    lhs_rhs_eq!(lhs, rhs, "secret part");

    let lhs = π.psw_of_r - π.psw_of_r_div_ω - π.w_of_r * π.b_of_r;
    let rhs = π.psw_wff_q_of_r * vanishing_of_r;
    lhs_rhs_eq!(
        lhs,
        rhs,
        "ParSumW(r) - ParSumW(r/ω) - W(r) · b(r) = Q(r) · (r^n − 1)"
    );

    //TODO: compute l_n_minus_1_of_r in verifier -- dont put it in the proof.
    let lhs = l_n_minus_1_of_r * π.psw_of_r;
    let rhs = vanishing_of_r * π.psw_check_q_of_r;
    lhs_rhs_eq!(lhs, rhs, "Ln−1(X) · ParSumW(X) = Z(X) · Q2(X)");

    let lhs = π.b_of_r * π.b_of_r - π.b_of_r;
    let rhs = π.b_wff_q_of_r * vanishing_of_r;
    lhs_rhs_eq!(lhs, rhs, "b(r) * b(r) - b(r) = Q(r) · (r^n − 1)");

    let lhs = l_n_minus_1_of_r * (π.b_of_r - F::from(1));
    let rhs = vanishing_of_r * π.b_check_q_of_r;
    lhs_rhs_eq!(lhs, rhs, "Ln−1(X) · (b(X) − 1) = Z(X) · Q4(X)");

    Ok(())
}
