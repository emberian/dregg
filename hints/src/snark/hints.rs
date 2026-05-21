use std::sync::Arc;

use ark_ec::{pairing::Pairing, CurveGroup};
use ark_poly::Polynomial;
use ark_std::{ops::*, One, Zero};

use crate::utils::{self};
use crate::HintsError;
use crate::{snark::*, Hint, PublicKey, SecretKey, UniverseSetup};
use serde::{Deserialize, Serialize};

pub(crate) fn preprocess_q1_contributions(q1_contributions: &[Vec<G1>]) -> Vec<G1> {
    let n = q1_contributions.len();
    let mut q1_coms = vec![];

    for i in 0..n {
        let mut party_i_q1_com = q1_contributions[i][i];
        for (j, contr) in q1_contributions.iter().enumerate().take(n) {
            if i != j {
                let party_j_contribution = contr[i];
                party_i_q1_com = party_i_q1_com.add(party_j_contribution).into();
            }
        }
        q1_coms.push(party_i_q1_com);
    }
    q1_coms
}

pub(crate) fn filter_and_add(
    params: &UniversalParams<Curve>,
    elements: &[G1],
    bitmap_full: &[F],
) -> G1 {
    assert_eq!(
        elements.len(),
        bitmap_full.len(),
        "filter_and_add length mismatch"
    );
    elements
        .iter()
        .zip(bitmap_full.iter())
        .fold(get_zero_poly_com_g1(params), |acc, (e, b)| {
            if b.is_one() {
                acc.add(e).into_affine()
            } else {
                acc
            }
        })
}

fn add_all_g2<'a>(
    params: &UniversalParams<Curve>,
    elements: impl IntoIterator<Item = &'a G2>,
) -> G2 {
    elements
        .into_iter()
        .fold(get_zero_poly_com_g2(params), |acc, e| {
            acc.add(e).into_affine()
        })
}

fn get_zero_poly_com_g1(params: &UniversalParams<Curve>) -> G1 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g1(params, &zero_poly).unwrap()
}

fn get_zero_poly_com_g2(params: &UniversalParams<Curve>) -> G2 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g2(params, &zero_poly).unwrap()
}

/// Errors that can occur during hint verification.
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PartyError {
    /// Invalid hint structure.
    InvalidStructure(usize),
    /// Pairing check failed.
    PairingCheckFailed,
}

impl GlobalData {
    /// Generate a hint for a party's secret key.
    pub(crate) fn generate_hint(
        &self,
        sk: &SecretKey,
        n: usize,
        i: usize,
    ) -> Result<Hint, HintsError> {
        if n == 0 || n & (n - 1) != 0 {
            return Err(HintsError::InvalidInput(
                "n must be a power of 2".to_string(),
            ));
        }
        if i >= n {
            return Err(HintsError::InvalidInput(format!(
                "Party index {} out of bounds for n={}",
                i, n
            )));
        }
        if n > self.params.powers_of_g.len() {
            return Err(HintsError::PolynomialDegreeTooLarge);
        }

        let params = &self.params;

        let l_i_of_x = self.lagrange_polynomials[i].clone();
        let z_of_x = utils::compute_vanishing_poly(n); // Needed for denominators

        // com_sk_li_tau: [sk_i * L_i(τ)]_2
        let sk_li_poly = utils::poly_eval_mult_c(&l_i_of_x, &sk.0);
        let com_sk_li_tau = KZG10::commit_g2(params, &sk_li_poly)?;

        // com_q1_contributions: [sk_i * F_ij]_1
        let mut q1_material = Vec::with_capacity(n);
        for j in 0..n {
            let num = if i == j {
                &l_i_of_x * &l_i_of_x - &l_i_of_x
            } else {
                let l_j_of_x = &self.lagrange_polynomials[j];
                l_j_of_x * &l_i_of_x
            };
            let f = &num / &z_of_x;
            let sk_f_poly = utils::poly_eval_mult_c(&f, &sk.0);
            let com = KZG10::commit_g1(params, &sk_f_poly)?;
            q1_material.push(com);
        }

        // com_q2_contribution: [sk_i * F'_i]_1
        let x_monomial = utils::compute_x_monomial();
        let l_i_of_0 = l_i_of_x.evaluate(&F::zero());
        let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);
        let num = &l_i_of_x - &l_i_of_0_poly;
        // Need to handle potential division by zero if τ=0. Usually τ is non-zero.
        let f = &num / &x_monomial; // Assuming τ != 0
        let sk_f_poly = utils::poly_eval_mult_c(&f, &sk.0);
        let q2_com = KZG10::commit_g1(params, &sk_f_poly)?;

        Ok(Hint {
            com_sk_li_tau,
            com_q1_contributions: q1_material,
            com_q2_contribution: q2_com,
        })
    }

    /// Setup a "universe" of participants
    ///
    /// This needs to be rerun any time the weights change(!)
    pub(crate) fn setup_universe(
        self: &Arc<Self>,
        keys: Vec<PublicKey>,
        hints: &[Hint],
        weights: Vec<F>,
    ) -> Result<UniverseSetup, HintsError> {
        let degree_max = self.params.powers_of_g.len() - 1;

        if !(keys.len() == hints.len() && keys.len() == weights.len()) {
            return Err(HintsError::InvalidInput(
                "Keys, hints, and weights must have the same length".to_string(),
            ));
        }

        // Pad with defaults if fewer participants than n? The proof system assumes size n.
        // Let's assume keys_hints_weights.len() == n for now. Need clarification.
        if keys.len() + 1 != degree_max {
            return Err(HintsError::InvalidInput(format!(
                "Expected exactly n={} participants, got {}",
                degree_max - 1,
                keys.len(),
            )));
        }

        let hint_aug = self.generate_hint(&SecretKey(F::zero()), degree_max, degree_max - 1)?;
        let pk_aug = PublicKey((self.params.powers_of_g[0] * F::zero()).into_affine());
        let params = &self.params;

        let mut failed_hint_indices = Vec::new();
        let mut party_errors = Vec::new();
        for (i, (pk, hint)) in keys
            .iter()
            .zip(hints.iter())
            .chain(std::iter::once((&pk_aug, &hint_aug)))
            .enumerate()
        {
            if hint.com_q1_contributions.len() != degree_max {
                failed_hint_indices.push(i);
                party_errors.push((
                    i,
                    PartyError::InvalidStructure(hint.com_q1_contributions.len()),
                ));
                continue;
            }

            let l_i_tau_g2 = self.lagrange_coms_g2[i];

            let lhs = Curve::pairing(pk.0, l_i_tau_g2);
            let rhs = Curve::pairing(params.powers_of_g[0], hint.com_sk_li_tau);

            if lhs != rhs {
                failed_hint_indices.push(i);
                party_errors.push((i, PartyError::PairingCheckFailed));
                continue;
            }
        }

        // --- Compute VK ---
        let mut vk_com_sk_tau = G2Projective::zero();
        let mut vk_com_w_tau = G1Projective::zero();

        for (i, hint) in hints.iter().enumerate() {
            if !failed_hint_indices.contains(&i) {
                vk_com_sk_tau += hint.com_sk_li_tau;

                let com_li_tau_g1 = &self.lagrange_coms_g1[i];
                vk_com_w_tau += com_li_tau_g1.mul(weights[i]);
            }
        }

        vk_com_sk_tau += hint_aug.com_sk_li_tau;

        let w_of_x = utils::compute_poly(&weights, &F::zero(), degree_max)?;
        let w_of_x_com = KZG::commit_g1(params, &w_of_x).unwrap();
        let z_of_x = utils::compute_vanishing_poly(degree_max);
        let x_monomial = utils::compute_x_monomial();
        let l_n_minus_1_of_x = &self.lagrange_polynomials[degree_max - 1];

        let vp = VerifierKey {
            degree_max,
            g_0: params.powers_of_g[0],
            h_0: params.powers_of_h[0],
            h_1: params.powers_of_h[1],
            l_n_minus_1_of_x_com: KZG::commit_g1(params, l_n_minus_1_of_x).unwrap(),
            w_of_x_com,
            sk_of_x_com: add_all_g2(
                params,
                hints
                    .iter()
                    .chain(std::iter::once(&hint_aug))
                    .map(|h| &h.com_sk_li_tau),
            ),
            vanishing_com: KZG::commit_g2(params, &z_of_x).unwrap(),
            x_monomial_com: KZG::commit_g2(params, &x_monomial).unwrap(),
            pks: keys.clone(),
            weights: weights.clone(),
            failed_hint_indices: failed_hint_indices.clone(),
        };

        // --- Compute AK ---
        // Precompute aggregated hint commitments for the prover
        let q1_coms = preprocess_q1_contributions(
            &hints
                .iter()
                .chain(std::iter::once(&hint_aug))
                .map(|h| h.com_q1_contributions.clone())
                .collect::<Vec<_>>(),
        );
        let q2_coms: Vec<G1> = hints
            .iter()
            .chain(std::iter::once(&hint_aug))
            .map(|h| h.com_q2_contribution)
            .collect();

        // Filter q1_coms and q2_coms based on failed_hint_indices?
        // The proof system's filter_and_add expects the full list and filters based on bitmap.
        // Let's pass the full list for now.

        // Filter q1_coms and q2_coms based on failed_hint_indices?
        // The proof system's filter_and_add expects the full list and filters based on bitmap.
        // Let's pass the full list for now.

        let pp = AggregationKey {
            degree_max,
            weights,
            pks: keys,
            q1_coms,
            q2_coms,
            failed_hint_indices,
            vk_l_n_minus_1_com: vp.l_n_minus_1_of_x_com,
            vk_vanishing_com: vp.vanishing_com,
            vk_x_monomial_com: vp.x_monomial_com,
            vk_w_of_x_com: vp.w_of_x_com,
            vk_sk_of_x_com: vp.sk_of_x_com,
        };

        Ok(UniverseSetup {
            agg_key: Arc::new(pp.into()),
            vk: Arc::new(vp.into()),
            global: self.clone(),
            party_errors,
        })
    }
}
