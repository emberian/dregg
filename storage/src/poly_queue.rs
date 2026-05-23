//! Polynomial-committed queue backed by REAL KZG10 (Kate, Zaverucha, Goldberg).
//!
//! This uses actual BN254 elliptic curve arithmetic and pairings from arkworks.
//! The queue state is a univariate polynomial over the BN254 scalar field.
//! The commitment is a single G1 point. Opening proofs are single G1 points.
//!
//! ## Security Audit (2026-05-23)
//!
//! ### Verified correct:
//! - **Pairing equation (single-point):** `e(C - [v]G, H) * e(-W, H_tau - [z]H) == 1`
//!   matches the textbook KZG10 derivation: p(tau)-v = q(tau)*(tau-z) in the exponent.
//!   Cross-checked against o1-labs/proof-systems poly-commitment/src/kzg.rs which uses
//!   the same structure (numerator in G1, divisor in G2, product of pairings == identity).
//! - **Batch verification equation:** The combination `e(sum_i gamma^i*(C - v_i*G + z_i*W_i), H)
//!   * e(-sum_i gamma^i*W_i, H_tau) == 1` correctly linearizes the individual pairing
//!   checks by absorbing `z_i*W_i` into the first G1 argument.
//! - **Polynomial division:** Uses exact field arithmetic long division with explicit
//!   zero-remainder check. If remainder is non-zero, returns None/DivisionFailed.
//! - **Position encoding:** Uses `Fr::from(position + 1)`, avoiding Fr(0). This prevents
//!   any degenerate divisor polynomial and ensures all evaluation points are distinct.
//! - **SRS extraction:** h = verifier_srs.g[0], h_tau = verifier_srs.g[1]. Verified
//!   consistent via `srs_pairing_consistency` test: e(g^tau, h) == e(g, h^tau).
//! - **Binding/Soundness:** Under DLog hardness on BN254, the scheme is computationally
//!   binding (cannot open same commitment to two values) and sound (pairing rejects
//!   wrong values). Adversarial tests below demonstrate rejection.
//!
//! ### Issue found and fixed:
//! - **Batch proof gamma (Fiat-Shamir):** The `prove_batch` method used `test_rng()` for
//!   gamma, which is deterministic/predictable. While gamma is included in the proof and
//!   the verifier uses whatever gamma the prover supplies, this means a malicious prover
//!   can try many gamma values to find one that cancels an invalid individual opening.
//!   **Fix:** `verify_batch` now recomputes gamma via Fiat-Shamir (hash of commitment +
//!   all witnesses + evaluations) and rejects proofs with non-matching gamma. The prover
//!   is thus committed to all proof elements before gamma is determined.
//!
//! ### Recommendations:
//! - In production, replace `prove_batch`'s RNG with proper Fiat-Shamir (Poseidon sponge
//!   absorbing commitment, witnesses, points, values). Current fix uses a field-hash
//!   over serialized elements as a stopgap.
//! - Consider adding degree bounds if queue polynomials could exceed SRS size.
//! - The `generate_insecure` SRS is test-only. Production MUST use ceremony output.
//!
//! # Relationship to poly-commitment (o1-labs/proof-systems)
//!
//! We use `poly-commitment`'s `PairingSRS` for SRS generation and the `commit_non_hiding`
//! method for polynomial commitments (via MSM). This ensures we share the same trusted
//! setup format and commitment algorithm as the rest of the proof-systems ecosystem.
//!
//! However, we implement our own open/verify logic because poly-commitment's `KZGProof`
//! is designed for Mina's PlonK protocol and has these incompatibilities:
//!   - `KZGProof::create` requires EXACTLY 2 evaluation points (hardcoded in `eval_polynomial`)
//!   - It takes `PolynomialsToCombine` (batched polynomials with a polyscale challenge)
//!   - Verification uses `Evaluation<G>` with chunked `PolyComm` format
//!   - It includes blinding factors (`KZGProof.blinding`) not needed for non-hiding queue state
//!
//! Our queue needs vanilla single-point KZG10 openings (prove p(z) = v for one point z).
//! The algorithm is textbook KZG10: quotient q(x) = (p(x) - v) / (x - z), then verify
//! via pairing: e(C - [v]G, H) = e(W, [tau]H - [z]H).
//!
//! AUDIT NOTE: The commitment operation delegates to `poly_commitment::SRS::commit_non_hiding`,
//! which performs the same MSM as our previous hand-rolled version. The proof/verify logic
//! follows the standard KZG10 protocol identically to poly-commitment/src/kzg.rs but for
//! single-point openings rather than the batched 2-point variant.
//!
//! # Security
//!
//! The `generate_insecure` SRS method uses a KNOWN tau for testing.
//! In production, use an SRS from the Ethereum KZG ceremony (powers of tau).

use std::sync::Arc;

use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{Field, One, PrimeField, UniformRand, Zero};
use ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::RngCore;
use poly_commitment::kzg::PairingSRS;
use poly_commitment::SRS as SRSTrait;

/// Errors from KZG queue operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueueError {
    /// Queue is full (at capacity).
    Full { capacity: usize },
    /// Queue is empty (nothing to dequeue).
    Empty,
    /// Position is out of bounds.
    OutOfBounds { position: usize, len: usize },
    /// Polynomial division failed (should not happen in correct usage).
    DivisionFailed,
}

/// Structured Reference String (powers of tau) for KZG10.
///
/// Wraps `poly_commitment::kzg::PairingSRS<Bn254>` for SRS generation and polynomial
/// commitment, and stores the G2 verifier elements needed for our single-point
/// pairing verification.
///
/// In production: loaded from Ethereum's KZG ceremony.
/// For testing: generated with known tau via `generate_insecure`.
#[derive(Debug, Clone)]
pub struct KzgSrs {
    /// The poly-commitment PairingSRS (G1 powers for commit, G2 for verify).
    pub pairing_srs: PairingSRS<Bn254>,
    /// [h] in G2 (G2 generator) — cached from verifier_srs for fast pairing checks.
    pub h: G2Affine,
    /// [h^tau] in G2 — cached from verifier_srs for fast pairing checks.
    pub h_tau: G2Affine,
    /// Maximum polynomial degree this SRS supports.
    pub max_degree: usize,
}

impl KzgSrs {
    /// Generate an SRS for testing. INSECURE: tau is known to the caller.
    ///
    /// Delegates to `PairingSRS::create_trusted_setup_with_toxic_waste` from
    /// poly-commitment/src/kzg.rs.
    pub fn generate_insecure(max_degree: usize) -> Self {
        let mut rng = ark_std::test_rng();
        Self::generate_insecure_with_rng(max_degree, &mut rng)
    }

    /// Generate an SRS with a provided RNG (for deterministic tests).
    pub fn generate_insecure_with_rng(max_degree: usize, rng: &mut impl RngCore) -> Self {
        let tau = Fr::rand(rng);
        Self::from_toxic_waste(tau, max_degree)
    }

    /// Create SRS from toxic waste directly. The caller MUST zeroize tau after.
    ///
    /// Uses `PairingSRS::create_trusted_setup_with_toxic_waste` for the G1 powers
    /// (prover SRS) and creates a depth-3 G2 verifier SRS. We extract h and h_tau
    /// from the verifier SRS for our single-point pairing checks.
    pub fn from_toxic_waste(tau: Fr, max_degree: usize) -> Self {
        // PairingSRS creates: full_srs.g = [g, g*tau, ..., g*tau^(depth-1)]
        // and verifier_srs.g = [h, h*tau, h*tau^2] (depth 3)
        let pairing_srs =
            PairingSRS::<Bn254>::create_trusted_setup_with_toxic_waste(tau, max_degree + 1);

        // Extract G2 elements for pairing verification.
        // verifier_srs.g[0] = H (G2 generator scaled by 1)
        // verifier_srs.g[1] = H^tau
        let h = pairing_srs.verifier_srs.g[0];
        let h_tau = pairing_srs.verifier_srs.g[1];

        Self {
            pairing_srs,
            h,
            h_tau,
            max_degree,
        }
    }

    /// Commit to a polynomial using the poly-commitment SRS (MSM via `commit_non_hiding`).
    ///
    /// commit(p) = sum_i(coeff_i * g^{tau^i})
    ///
    /// Delegates to `poly_commitment::SRS::commit_non_hiding` which performs the
    /// same multi-scalar multiplication but with production-quality optimizations
    /// (parallelism, chunking for large polynomials).
    pub fn commit(&self, poly: &DensePolynomial<Fr>) -> Result<G1Affine, QueueError> {
        let coeffs = poly.coeffs();
        if coeffs.len() > self.max_degree + 1 {
            return Err(QueueError::Full {
                capacity: self.max_degree,
            });
        }
        if coeffs.is_empty() {
            return Ok(G1Affine::zero());
        }

        // Use poly-commitment's commit_non_hiding (single chunk, no blinding).
        // get_first_chunk() extracts the single G1 point from the PolyComm wrapper.
        let poly_comm = self.pairing_srs.full_srs.commit_non_hiding(poly, 1);
        Ok(poly_comm.get_first_chunk())
    }
}

/// A KZG opening proof for a single evaluation point.
///
/// Proves that p(z) = v by providing the quotient commitment:
///   W = commit(q(x)) where q(x) = (p(x) - v) / (x - z)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KzgPositionProof {
    /// The quotient commitment (one G1 point).
    pub witness: G1Affine,
    /// The evaluation point (field element representing position).
    pub point: Fr,
    /// The value p(point).
    pub value: Fr,
}

/// Batch proof for multiple positions.
///
/// Uses the standard multi-point opening: provides individual witnesses per point,
/// verification is batched into two pairings using a random linear combination.
#[derive(Debug, Clone)]
pub struct KzgBatchProof {
    /// Individual quotient witnesses (one per opened position).
    pub witnesses: Vec<G1Affine>,
    /// Individual evaluations: (point, value) pairs.
    pub evaluations: Vec<(Fr, Fr)>,
    /// The random challenge used for batching verification (Fiat-Shamir in production).
    pub gamma: Fr,
}

/// A polynomial-committed queue backed by REAL KZG10.
///
/// The queue state is encoded as a univariate polynomial over BN254 scalar field:
///   p(omega^i) = value_i for positions i in [head..tail]
///
/// We use the coefficient form and evaluate at successive field elements
/// Fr::from(1), Fr::from(2), ... for positions.
///
/// The commitment is a single G1 point (48 bytes compressed) that uniquely
/// determines the entire queue state.
pub struct KzgQueue {
    /// The polynomial representing queue contents (in coefficient form).
    /// We store the values and reconstruct the poly via Lagrange interpolation.
    values: Vec<Fr>,
    /// The polynomial in coefficient form (cached, recomputed on mutation).
    polynomial: DensePolynomial<Fr>,
    /// KZG commitment to the current polynomial.
    commitment: G1Affine,
    /// The SRS (structured reference string) -- shared across queues.
    srs: Arc<KzgSrs>,
    /// Head pointer (first un-dequeued index).
    head: usize,
    /// Maximum capacity.
    capacity: usize,
}

impl KzgQueue {
    /// Create a new empty queue with the given SRS and capacity.
    pub fn new(srs: Arc<KzgSrs>, capacity: usize) -> Self {
        assert!(
            capacity <= srs.max_degree,
            "capacity ({capacity}) exceeds SRS max_degree ({})",
            srs.max_degree
        );
        let polynomial = DensePolynomial::from_coefficients_vec(vec![]);
        let commitment = G1Affine::zero();
        Self {
            values: Vec::new(),
            polynomial,
            commitment,
            srs,
            head: 0,
            capacity,
        }
    }

    /// The number of pending (un-dequeued) entries.
    pub fn len(&self) -> usize {
        self.values.len() - self.head
    }

    /// Whether the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Whether the queue is at capacity.
    pub fn is_full(&self) -> bool {
        self.len() >= self.capacity
    }

    /// Current KZG commitment (one G1 point representing entire queue state).
    pub fn commitment(&self) -> G1Affine {
        self.commitment
    }

    /// Enqueue a value. Returns the new commitment on success.
    ///
    /// The value is encoded at position (tail + 1) in the polynomial.
    pub fn enqueue(&mut self, value: Fr) -> Result<G1Affine, QueueError> {
        if self.is_full() {
            return Err(QueueError::Full {
                capacity: self.capacity,
            });
        }

        self.values.push(value);
        self.rebuild_polynomial_and_commitment()?;
        Ok(self.commitment)
    }

    /// Dequeue the next value (FIFO). Returns the value and an opening proof.
    pub fn dequeue(&mut self) -> Result<(Fr, KzgPositionProof), QueueError> {
        if self.is_empty() {
            return Err(QueueError::Empty);
        }

        let position = self.head;
        let value = self.values[position];
        let proof = self.prove_absolute_position(position)?;

        self.head += 1;
        self.rebuild_polynomial_and_commitment()?;

        Ok((value, proof))
    }

    /// Prove the value at a relative position (0 = head, 1 = head+1, ...).
    pub fn prove_position(&self, relative_pos: usize) -> Result<KzgPositionProof, QueueError> {
        let absolute = self.head + relative_pos;
        if absolute >= self.values.len() {
            return Err(QueueError::OutOfBounds {
                position: relative_pos,
                len: self.len(),
            });
        }
        self.prove_absolute_position(absolute)
    }

    /// Batch prove multiple relative positions with a single combined proof.
    ///
    /// Uses Fiat-Shamir: gamma is derived from (commitment, witnesses, evaluations)
    /// so that it cannot be manipulated by the prover.
    pub fn prove_batch(&self, positions: &[usize]) -> Result<KzgBatchProof, QueueError> {
        // Verify all positions are valid.
        for &pos in positions {
            let absolute = self.head + pos;
            if absolute >= self.values.len() {
                return Err(QueueError::OutOfBounds {
                    position: pos,
                    len: self.len(),
                });
            }
        }

        // First compute all witnesses and evaluations.
        let mut evaluations = Vec::with_capacity(positions.len());
        let mut witnesses = Vec::with_capacity(positions.len());

        for &pos in positions {
            let absolute = self.head + pos;
            let point = Self::position_to_field_element(absolute);
            let value = self.values[absolute];

            let quotient = self.compute_quotient(point, value)?;
            let witness = self.srs.commit(&quotient)?;

            evaluations.push((point, value));
            witnesses.push(witness);
        }

        // Derive gamma via Fiat-Shamir AFTER all proof elements are determined.
        let gamma = fiat_shamir_batch_gamma(&self.commitment, &witnesses, &evaluations);

        Ok(KzgBatchProof {
            witnesses,
            evaluations,
            gamma,
        })
    }

    /// Batch prove with a specific challenge (for deterministic testing).
    pub fn prove_batch_with_challenge(
        &self,
        positions: &[usize],
        gamma: Fr,
    ) -> Result<KzgBatchProof, QueueError> {
        let mut evaluations = Vec::with_capacity(positions.len());
        let mut witnesses = Vec::with_capacity(positions.len());

        for &pos in positions {
            let absolute = self.head + pos;
            let point = Self::position_to_field_element(absolute);
            let value = self.values[absolute];

            // Compute individual quotient and commit.
            let quotient = self.compute_quotient(point, value)?;
            let witness = self.srs.commit(&quotient)?;

            evaluations.push((point, value));
            witnesses.push(witness);
        }

        Ok(KzgBatchProof {
            witnesses,
            evaluations,
            gamma,
        })
    }

    /// Verify a single position proof against a commitment.
    ///
    /// Uses the pairing check:
    ///   e(C - [v]G1, H) == e(W, H_tau - [z]H)
    ///
    /// Which is equivalent to checking:
    ///   e(C - [v]G1 - W * (tau - z), H) == 1  (in the exponent)
    ///
    /// We verify: e(C - [v]G1, H) * e(-W, [tau]H - [z]H) == 1
    pub fn verify_position(
        srs: &KzgSrs,
        commitment: &G1Affine,
        proof: &KzgPositionProof,
    ) -> bool {
        // LHS: C - [v] * G1
        let g1_gen = G1Affine::generator();
        let v_g1: G1Projective = g1_gen.into_group() * proof.value;
        let lhs: G1Projective = commitment.into_group() - v_g1;

        // RHS of pairing: H_tau - [z] * H
        let z_h: G2Projective = srs.h.into_group() * proof.point;
        let rhs: G2Projective = srs.h_tau.into_group() - z_h;

        // Pairing check: e(lhs, H) == e(W, rhs)
        // Equivalently: e(lhs, H) * e(-W, rhs) == 1
        // Which is: e(C - [v]G, H) * e(-W, H_tau - [z]H) == 1
        let neg_witness: G1Projective = -(proof.witness.into_group());

        let result = Bn254::multi_pairing(
            [lhs.into_affine(), neg_witness.into_affine()],
            [srs.h, rhs.into_affine()],
        );

        result.is_zero()
    }

    /// Verify a batch proof against a commitment.
    ///
    /// Uses the standard batched pairing check with random linear combination gamma:
    ///
    /// For individual opening equations: e(C - [v_i]G, H) = e(W_i, H_tau - [z_i]H)
    /// Combined with gamma: check that
    ///   e(sum_i gamma^i * (C - [v_i]G) + sum_i gamma^i * z_i * W_i, H)
    ///   = e(sum_i gamma^i * W_i, H_tau)
    ///
    /// Rearranged as a single multi_pairing == 1 check:
    ///   e(LHS, H) * e(-W_combined, H_tau) == 1
    /// where LHS = sum_i gamma^i * (C - v_i*G + z_i*W_i)
    ///       W_combined = sum_i gamma^i * W_i
    ///
    /// **Security:** gamma is recomputed via Fiat-Shamir from (commitment, witnesses,
    /// evaluations). The proof's stored gamma must match; otherwise the proof is rejected.
    /// This prevents a malicious prover from choosing gamma to mask invalid openings.
    pub fn verify_batch(srs: &KzgSrs, commitment: &G1Affine, proof: &KzgBatchProof) -> bool {
        if proof.witnesses.len() != proof.evaluations.len() {
            return false;
        }
        if proof.witnesses.is_empty() {
            return true; // vacuously true
        }

        // Recompute gamma via Fiat-Shamir and reject if it doesn't match.
        let expected_gamma =
            fiat_shamir_batch_gamma(commitment, &proof.witnesses, &proof.evaluations);
        if expected_gamma != proof.gamma {
            return false;
        }

        let g1_gen = G1Affine::generator();
        let gamma = proof.gamma;

        // Accumulate:
        //   LHS = sum_i gamma^i * (C - v_i*G + z_i*W_i)
        //   W_combined = sum_i gamma^i * W_i
        let mut lhs = G1Projective::zero();
        let mut w_combined = G1Projective::zero();
        let mut gamma_power = Fr::one();

        for (i, &(point, value)) in proof.evaluations.iter().enumerate() {
            let w_i = proof.witnesses[i].into_group();

            // C - v_i * G + z_i * W_i
            let term: G1Projective =
                commitment.into_group() - g1_gen.into_group() * value + w_i * point;

            lhs += term * gamma_power;
            w_combined += w_i * gamma_power;
            gamma_power *= gamma;
        }

        // Pairing check: e(LHS, H) * e(-W_combined, H_tau) == 1
        let neg_w_combined: G1Projective = -w_combined;

        let result = Bn254::multi_pairing(
            [lhs.into_affine(), neg_w_combined.into_affine()],
            [srs.h, srs.h_tau],
        );

        result.is_zero()
    }

    /// Verify a batch proof with a caller-supplied gamma (for testing/deterministic use).
    ///
    /// **WARNING:** This bypasses Fiat-Shamir. Only use in tests.
    #[cfg(test)]
    fn verify_batch_with_explicit_gamma(
        srs: &KzgSrs,
        commitment: &G1Affine,
        proof: &KzgBatchProof,
    ) -> bool {
        if proof.witnesses.len() != proof.evaluations.len() {
            return false;
        }
        if proof.witnesses.is_empty() {
            return true;
        }

        let g1_gen = G1Affine::generator();
        let gamma = proof.gamma;

        let mut lhs = G1Projective::zero();
        let mut w_combined = G1Projective::zero();
        let mut gamma_power = Fr::one();

        for (i, &(point, value)) in proof.evaluations.iter().enumerate() {
            let w_i = proof.witnesses[i].into_group();
            let term: G1Projective =
                commitment.into_group() - g1_gen.into_group() * value + w_i * point;
            lhs += term * gamma_power;
            w_combined += w_i * gamma_power;
            gamma_power *= gamma;
        }

        let neg_w_combined: G1Projective = -w_combined;
        let result = Bn254::multi_pairing(
            [lhs.into_affine(), neg_w_combined.into_affine()],
            [srs.h, srs.h_tau],
        );
        result.is_zero()
    }

    // ---- Internal helpers ----

    /// Map position index to a field element.
    /// We use Fr::from(position + 1) to avoid evaluation at zero.
    fn position_to_field_element(position: usize) -> Fr {
        Fr::from((position + 1) as u64)
    }

    /// Rebuild the polynomial from current active values and recompute commitment.
    fn rebuild_polynomial_and_commitment(&mut self) -> Result<(), QueueError> {
        let active = &self.values[self.head..];
        if active.is_empty() {
            self.polynomial = DensePolynomial::from_coefficients_vec(vec![]);
            self.commitment = G1Affine::zero();
            return Ok(());
        }

        // Build polynomial via Lagrange interpolation over the active values.
        // Points: position_to_field_element(head), ..., position_to_field_element(tail-1)
        // Values: active[0], active[1], ...
        let points: Vec<Fr> = (self.head..self.values.len())
            .map(Self::position_to_field_element)
            .collect();

        self.polynomial = lagrange_interpolation(&points, active);
        self.commitment = self.srs.commit(&self.polynomial)?;
        Ok(())
    }

    /// Compute the quotient polynomial q(x) = (p(x) - value) / (x - point).
    fn compute_quotient(
        &self,
        point: Fr,
        value: Fr,
    ) -> Result<DensePolynomial<Fr>, QueueError> {
        // Numerator: p(x) - value
        let mut numerator = self.polynomial.clone();
        if numerator.coeffs.is_empty() {
            numerator.coeffs.push(-value);
        } else {
            numerator.coeffs[0] -= value;
        }

        // Divisor: (x - point) = [-point, 1]
        let divisor = DensePolynomial::from_coefficients_vec(vec![-point, Fr::one()]);

        // Polynomial division
        polynomial_division(&numerator, &divisor).ok_or(QueueError::DivisionFailed)
    }

    /// Prove the value at an absolute position index.
    fn prove_absolute_position(&self, absolute_pos: usize) -> Result<KzgPositionProof, QueueError> {
        let point = Self::position_to_field_element(absolute_pos);
        let value = self.values[absolute_pos];

        // Sanity: polynomial should evaluate to value at point.
        debug_assert_eq!(self.polynomial.evaluate(&point), value);

        let quotient = self.compute_quotient(point, value)?;
        let witness = self.srs.commit(&quotient)?;

        Ok(KzgPositionProof {
            witness,
            point,
            value,
        })
    }
}

/// The `CommittedQueue` trait: common interface for MerkleQueue and KzgQueue.
pub trait CommittedQueue {
    /// The type of commitment (e.g., [u8; 32] for Merkle, G1Affine for KZG).
    type Commitment: Clone;
    /// The type of membership/dequeue proof.
    type Proof;
    /// The type of values stored.
    type Value;

    /// Enqueue a value, returning the new commitment.
    fn enqueue_value(&mut self, value: Self::Value) -> Result<Self::Commitment, QueueError>;
    /// Dequeue the next value, returning the value and a proof.
    fn dequeue_value(&mut self) -> Result<(Self::Value, Self::Proof), QueueError>;
    /// Current commitment to queue state.
    fn committed(&self) -> Self::Commitment;
    /// Number of pending entries.
    fn pending_len(&self) -> usize;
}

impl CommittedQueue for KzgQueue {
    type Commitment = G1Affine;
    type Proof = KzgPositionProof;
    type Value = Fr;

    fn enqueue_value(&mut self, value: Fr) -> Result<G1Affine, QueueError> {
        self.enqueue(value)
    }

    fn dequeue_value(&mut self) -> Result<(Fr, KzgPositionProof), QueueError> {
        self.dequeue()
    }

    fn committed(&self) -> G1Affine {
        self.commitment()
    }

    fn pending_len(&self) -> usize {
        self.len()
    }
}

// ---- Fiat-Shamir helper ----

/// Compute the Fiat-Shamir challenge gamma for batch verification.
///
/// gamma = H(commitment || witnesses || evaluations)
///
/// This ensures gamma is determined AFTER all proof elements are fixed,
/// preventing a malicious prover from choosing gamma to mask invalid openings.
fn fiat_shamir_batch_gamma(
    commitment: &G1Affine,
    witnesses: &[G1Affine],
    evaluations: &[(Fr, Fr)],
) -> Fr {
    let mut transcript = Vec::new();

    // Serialize commitment.
    commitment
        .serialize_compressed(&mut transcript)
        .expect("serialization cannot fail");

    // Serialize each witness.
    for w in witnesses {
        w.serialize_compressed(&mut transcript)
            .expect("serialization cannot fail");
    }

    // Serialize each (point, value) pair.
    for (point, value) in evaluations {
        point
            .serialize_compressed(&mut transcript)
            .expect("serialization cannot fail");
        value
            .serialize_compressed(&mut transcript)
            .expect("serialization cannot fail");
    }

    // Hash to field element via blake3 + reduction.
    let hash = blake3::hash(&transcript);
    Fr::from_le_bytes_mod_order(hash.as_bytes())
}

// ---- Polynomial arithmetic helpers ----

/// Lagrange interpolation: find the unique polynomial of degree n-1
/// passing through the given (point, value) pairs.
fn lagrange_interpolation(points: &[Fr], values: &[Fr]) -> DensePolynomial<Fr> {
    assert_eq!(points.len(), values.len());
    let n = points.len();
    if n == 0 {
        return DensePolynomial::from_coefficients_vec(vec![]);
    }
    if n == 1 {
        // Constant polynomial equal to values[0].
        return DensePolynomial::from_coefficients_vec(vec![values[0]]);
    }

    let mut result = DensePolynomial::from_coefficients_vec(vec![Fr::zero()]);

    for i in 0..n {
        // Compute the i-th Lagrange basis polynomial L_i(x).
        // L_i(x) = prod_{j != i} (x - points[j]) / (points[i] - points[j])
        let mut basis = DensePolynomial::from_coefficients_vec(vec![Fr::one()]);
        let mut denom = Fr::one();

        for j in 0..n {
            if j == i {
                continue;
            }
            // Multiply by (x - points[j])
            let factor = DensePolynomial::from_coefficients_vec(vec![-points[j], Fr::one()]);
            basis = naive_poly_mul(&basis, &factor);
            denom *= points[i] - points[j];
        }

        // Scale by values[i] / denom
        let scale = values[i] * denom.inverse().expect("points must be distinct");
        let scaled = DensePolynomial::from_coefficients_vec(
            basis.coeffs().iter().map(|c| *c * scale).collect(),
        );

        result = &result + &scaled;
    }

    result
}

/// Naive polynomial multiplication (for small polynomials in Lagrange interp).
fn naive_poly_mul(a: &DensePolynomial<Fr>, b: &DensePolynomial<Fr>) -> DensePolynomial<Fr> {
    if a.coeffs().is_empty() || b.coeffs().is_empty() {
        return DensePolynomial::from_coefficients_vec(vec![]);
    }
    let result_len = a.coeffs().len() + b.coeffs().len() - 1;
    let mut coeffs = vec![Fr::zero(); result_len];
    for (i, ca) in a.coeffs().iter().enumerate() {
        for (j, cb) in b.coeffs().iter().enumerate() {
            coeffs[i + j] += *ca * *cb;
        }
    }
    DensePolynomial::from_coefficients_vec(coeffs)
}

/// Polynomial long division: returns quotient such that a = quotient * b + remainder.
/// Returns None if division has a non-zero remainder (shouldn't happen for valid KZG).
fn polynomial_division(
    numerator: &DensePolynomial<Fr>,
    divisor: &DensePolynomial<Fr>,
) -> Option<DensePolynomial<Fr>> {
    let num_coeffs = numerator.coeffs();
    let div_coeffs = divisor.coeffs();

    if div_coeffs.is_empty() || div_coeffs.iter().all(|c| c.is_zero()) {
        return None; // division by zero
    }

    let num_degree = if num_coeffs.is_empty() {
        return Some(DensePolynomial::from_coefficients_vec(vec![]));
    } else {
        // Find actual degree (skip trailing zeros).
        let mut d = num_coeffs.len() - 1;
        while d > 0 && num_coeffs[d].is_zero() {
            d -= 1;
        }
        if num_coeffs[d].is_zero() {
            return Some(DensePolynomial::from_coefficients_vec(vec![]));
        }
        d
    };

    let div_degree = {
        let mut d = div_coeffs.len() - 1;
        while d > 0 && div_coeffs[d].is_zero() {
            d -= 1;
        }
        d
    };

    if num_degree < div_degree {
        // Numerator degree < divisor degree => quotient is 0, remainder is numerator.
        // For KZG this means something went wrong, but we check.
        if num_coeffs.iter().all(|c| c.is_zero()) {
            return Some(DensePolynomial::from_coefficients_vec(vec![]));
        }
        return None;
    }

    let mut remainder: Vec<Fr> = num_coeffs.to_vec();
    // Pad to ensure we have enough length.
    while remainder.len() <= num_degree {
        remainder.push(Fr::zero());
    }
    let quot_len = num_degree - div_degree + 1;
    let mut quotient = vec![Fr::zero(); quot_len];

    let leading_div_inv = div_coeffs[div_degree]
        .inverse()
        .expect("leading coefficient must be nonzero");

    for i in (0..quot_len).rev() {
        let coeff = remainder[i + div_degree] * leading_div_inv;
        quotient[i] = coeff;
        for j in 0..=div_degree {
            remainder[i + j] -= coeff * div_coeffs[j];
        }
    }

    // Check remainder is zero (within floating point — but we're in exact field arithmetic).
    for r in &remainder {
        if !r.is_zero() {
            return None;
        }
    }

    Some(DensePolynomial::from_coefficients_vec(quotient))
}

#[cfg(test)]
#[allow(unused_must_use)]
mod tests {
    use super::*;
    use ark_ec::VariableBaseMSM;
    use ark_ff::PrimeField;

    fn make_srs(max_degree: usize) -> Arc<KzgSrs> {
        Arc::new(KzgSrs::generate_insecure(max_degree))
    }

    #[test]
    fn srs_generation_and_queue_creation() {
        let srs = make_srs(64);
        assert_eq!(srs.pairing_srs.full_srs.g.len(), 65); // 0..=64
        assert_eq!(srs.max_degree, 64);

        let q = KzgQueue::new(srs, 32);
        assert!(q.is_empty());
        assert_eq!(q.len(), 0);
    }

    #[test]
    fn enqueue_dequeue_roundtrip() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        let val = Fr::from(42u64);
        let commit1 = q.enqueue(val).unwrap();
        assert!(!commit1.is_zero());
        assert_eq!(q.len(), 1);

        let (dequeued, proof) = q.dequeue().unwrap();
        assert_eq!(dequeued, val);
        assert_eq!(q.len(), 0);

        // Verify the proof against the ORIGINAL commitment (before dequeue).
        assert!(KzgQueue::verify_position(&srs, &commit1, &proof));
    }

    #[test]
    fn position_proof_verify() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        let values: Vec<Fr> = (1..=5).map(|i| Fr::from(i * 10u64)).collect();
        for v in &values {
            q.enqueue(*v).unwrap();
        }

        // Prove position 2 (relative, so absolute index 2, value = 30).
        let proof = q.prove_position(2).unwrap();
        assert_eq!(proof.value, Fr::from(30u64));

        let commitment = q.commitment();
        assert!(KzgQueue::verify_position(&srs, &commitment, &proof));
    }

    #[test]
    fn batch_proof_verify() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        let values: Vec<Fr> = (1..=8).map(|i| Fr::from(i * 7u64)).collect();
        for v in &values {
            q.enqueue(*v).unwrap();
        }

        let commitment = q.commitment();

        // Batch prove positions 0, 2, 5 using Fiat-Shamir gamma.
        let proof = q.prove_batch(&[0, 2, 5]).unwrap();

        assert_eq!(proof.evaluations.len(), 3);
        assert_eq!(proof.evaluations[0].1, Fr::from(7u64)); // pos 0 => 7
        assert_eq!(proof.evaluations[1].1, Fr::from(21u64)); // pos 2 => 21
        assert_eq!(proof.evaluations[2].1, Fr::from(42u64)); // pos 5 => 42

        assert!(KzgQueue::verify_batch(&srs, &commitment, &proof));
    }

    #[test]
    fn batch_proof_with_explicit_gamma_verify() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        let values: Vec<Fr> = (1..=8).map(|i| Fr::from(i * 7u64)).collect();
        for v in &values {
            q.enqueue(*v).unwrap();
        }

        let commitment = q.commitment();

        // Use explicit gamma for deterministic testing (bypasses Fiat-Shamir).
        let gamma = Fr::from(9999u64);
        let proof = q.prove_batch_with_challenge(&[0, 2, 5], gamma).unwrap();

        assert_eq!(proof.evaluations.len(), 3);
        assert_eq!(proof.evaluations[0].1, Fr::from(7u64));
        assert_eq!(proof.evaluations[1].1, Fr::from(21u64));
        assert_eq!(proof.evaluations[2].1, Fr::from(42u64));

        // This uses the test-only verifier that accepts any gamma.
        assert!(KzgQueue::verify_batch_with_explicit_gamma(
            &srs,
            &commitment,
            &proof
        ));
    }

    #[test]
    fn commitment_changes_on_every_mutation() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        let c0 = q.commitment();

        q.enqueue(Fr::from(1u64)).unwrap();
        let c1 = q.commitment();
        assert_ne!(c0, c1);

        q.enqueue(Fr::from(2u64)).unwrap();
        let c2 = q.commitment();
        assert_ne!(c1, c2);

        q.dequeue().unwrap();
        let c3 = q.commitment();
        assert_ne!(c2, c3);

        q.dequeue().unwrap();
        let c4 = q.commitment();
        assert_ne!(c3, c4);
        // After dequeueing everything, back to zero.
        assert_eq!(c4, G1Affine::zero());
    }

    #[test]
    fn invalid_proof_wrong_position_fails() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        q.enqueue(Fr::from(100u64)).unwrap();
        q.enqueue(Fr::from(200u64)).unwrap();

        let commitment = q.commitment();
        let mut proof = q.prove_position(0).unwrap();

        // Tamper: change the evaluation point.
        proof.point = Fr::from(9999u64);

        assert!(!KzgQueue::verify_position(&srs, &commitment, &proof));
    }

    #[test]
    fn invalid_proof_wrong_value_fails() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        q.enqueue(Fr::from(100u64)).unwrap();
        q.enqueue(Fr::from(200u64)).unwrap();

        let commitment = q.commitment();
        let mut proof = q.prove_position(1).unwrap();

        // Tamper: change the claimed value.
        proof.value = Fr::from(999u64);

        assert!(!KzgQueue::verify_position(&srs, &commitment, &proof));
    }

    #[test]
    fn queue_at_capacity_rejects() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 3);

        q.enqueue(Fr::from(1u64)).unwrap();
        q.enqueue(Fr::from(2u64)).unwrap();
        q.enqueue(Fr::from(3u64)).unwrap();

        let result = q.enqueue(Fr::from(4u64));
        assert_eq!(result, Err(QueueError::Full { capacity: 3 }));
    }

    #[test]
    fn srs_reuse_across_multiple_queues() {
        let srs = make_srs(64);

        let mut q1 = KzgQueue::new(srs.clone(), 16);
        let mut q2 = KzgQueue::new(srs.clone(), 16);

        q1.enqueue(Fr::from(11u64)).unwrap();
        q2.enqueue(Fr::from(22u64)).unwrap();

        // Different values => different commitments.
        assert_ne!(q1.commitment(), q2.commitment());

        // Both can prove independently.
        let proof1 = q1.prove_position(0).unwrap();
        let proof2 = q2.prove_position(0).unwrap();

        assert!(KzgQueue::verify_position(&srs, &q1.commitment(), &proof1));
        assert!(KzgQueue::verify_position(&srs, &q2.commitment(), &proof2));

        // Cross-verification fails: proof1 against q2's commitment.
        assert!(!KzgQueue::verify_position(&srs, &q2.commitment(), &proof1));
    }

    #[test]
    fn multiple_enqueue_dequeue_cycles() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 8);

        // Enqueue 5 items.
        for i in 1..=5 {
            q.enqueue(Fr::from(i as u64 * 100)).unwrap();
        }
        assert_eq!(q.len(), 5);

        // Dequeue 3.
        for expected in [100u64, 200, 300] {
            let (val, proof) = q.dequeue().unwrap();
            assert_eq!(val, Fr::from(expected));
            // Note: proof is against pre-dequeue commitment, which changes.
            // The proof.value and proof.point should match.
            assert_eq!(proof.value, Fr::from(expected));
        }
        assert_eq!(q.len(), 2);

        // Prove remaining positions.
        let proof = q.prove_position(0).unwrap();
        assert_eq!(proof.value, Fr::from(400u64));
        assert!(KzgQueue::verify_position(&srs, &q.commitment(), &proof));

        let proof = q.prove_position(1).unwrap();
        assert_eq!(proof.value, Fr::from(500u64));
        assert!(KzgQueue::verify_position(&srs, &q.commitment(), &proof));
    }

    #[test]
    fn polynomial_commitment_is_deterministic() {
        // Same values in same order => same commitment.
        let srs = make_srs(64);
        let mut q1 = KzgQueue::new(srs.clone(), 16);
        let mut q2 = KzgQueue::new(srs.clone(), 16);

        let vals = [Fr::from(7u64), Fr::from(13u64), Fr::from(37u64)];
        for v in &vals {
            q1.enqueue(*v).unwrap();
            q2.enqueue(*v).unwrap();
        }

        assert_eq!(q1.commitment(), q2.commitment());
    }

    #[test]
    fn empty_queue_dequeue_error() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 8);

        assert_eq!(q.dequeue(), Err(QueueError::Empty));
    }

    /// Cross-validate that our commitment (via poly-commitment's commit_non_hiding)
    /// matches a manual MSM against the same SRS G1 powers.
    ///
    /// This proves that poly-commitment's SRS and commit are consistent with
    /// direct arkworks MSM, confirming we haven't introduced any subtle mismatch.
    #[test]
    fn cross_validate_commit_against_manual_msm() {
        let srs = make_srs(32);

        // Build a test polynomial: p(x) = 3 + 5x + 7x^2 + 11x^3
        let coeffs = vec![Fr::from(3u64), Fr::from(5u64), Fr::from(7u64), Fr::from(11u64)];
        let poly = DensePolynomial::from_coefficients_vec(coeffs.clone());

        // Commit via our KzgSrs (which delegates to poly-commitment's commit_non_hiding).
        let our_commitment = srs.commit(&poly).unwrap();

        // Compute the same commitment manually via MSM on the SRS G1 powers.
        let bases = &srs.pairing_srs.full_srs.g[..coeffs.len()];
        let scalars: Vec<_> = coeffs.iter().map(|c| c.into_bigint()).collect();
        let manual_commitment = G1Projective::msm_bigint(bases, &scalars).into_affine();

        assert_eq!(
            our_commitment, manual_commitment,
            "poly-commitment's commit_non_hiding must match manual MSM"
        );
    }

    /// Verify that the PairingSRS G2 elements (h, h_tau) are correctly extracted
    /// and that the pairing relationship holds: e(g^tau, h) == e(g, h^tau).
    #[test]
    fn srs_pairing_consistency() {
        let srs = make_srs(16);

        // g^tau is the second element of the G1 SRS (index 1).
        let g_tau = srs.pairing_srs.full_srs.g[1];
        let g = srs.pairing_srs.full_srs.g[0];

        // Pairing check: e(g^tau, h) == e(g, h^tau)
        let lhs = Bn254::pairing(g_tau, srs.h);
        let rhs = Bn254::pairing(g, srs.h_tau);

        assert_eq!(lhs, rhs, "SRS pairing consistency check failed");
    }

    // =========================================================================
    // ADVERSARIAL SECURITY TESTS
    // =========================================================================

    /// Soundness: verify rejects a forged witness for a wrong value.
    /// An adversary who doesn't know tau cannot produce a valid witness for v' != p(z).
    /// Here we simulate an adversary who produces a random G1 point as the witness.
    #[test]
    fn adversarial_forged_witness_rejected() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        q.enqueue(Fr::from(42u64)).unwrap();
        q.enqueue(Fr::from(99u64)).unwrap();

        let commitment = q.commitment();

        // Adversary tries to prove position 0 has value 999 (it's actually 42).
        let forged_proof = KzgPositionProof {
            witness: G1Affine::generator(), // random point
            point: KzgQueue::position_to_field_element(0),
            value: Fr::from(999u64),
        };

        assert!(
            !KzgQueue::verify_position(&srs, &commitment, &forged_proof),
            "forged witness for wrong value must be rejected"
        );
    }

    /// Soundness: verify rejects when the witness is correct but value is tampered.
    /// Even if the adversary has the correct witness for v, changing v to v' breaks it.
    #[test]
    fn adversarial_value_tamper_rejected() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        q.enqueue(Fr::from(42u64)).unwrap();
        let commitment = q.commitment();

        let mut proof = q.prove_position(0).unwrap();
        assert!(KzgQueue::verify_position(&srs, &commitment, &proof));

        // Adversary tampers: claims value is 43 instead of 42.
        proof.value = Fr::from(43u64);
        assert!(
            !KzgQueue::verify_position(&srs, &commitment, &proof),
            "off-by-one value tamper must be rejected"
        );

        // Adversary tampers: claims value is Fr::ZERO.
        proof.value = Fr::zero();
        assert!(
            !KzgQueue::verify_position(&srs, &commitment, &proof),
            "zero-value tamper must be rejected"
        );
    }

    /// Soundness: verify rejects when the point is tampered (shifted by 1).
    /// Even with a valid witness for (z, v), claiming (z+1, v) fails.
    #[test]
    fn adversarial_point_shift_rejected() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        q.enqueue(Fr::from(42u64)).unwrap();
        q.enqueue(Fr::from(99u64)).unwrap();
        let commitment = q.commitment();

        let mut proof = q.prove_position(0).unwrap();
        assert!(KzgQueue::verify_position(&srs, &commitment, &proof));

        // Shift point: claim this proof is for position 1 instead of position 0.
        proof.point = KzgQueue::position_to_field_element(1);
        assert!(
            !KzgQueue::verify_position(&srs, &commitment, &proof),
            "point-shifted proof must be rejected"
        );
    }

    /// Binding: same commitment cannot be opened to two different values at the same point.
    /// We verify that if we have a valid proof for (z, v), the pairing rejects (z, v')
    /// with the SAME witness (which would violate binding).
    #[test]
    fn binding_same_point_different_values() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        q.enqueue(Fr::from(100u64)).unwrap();
        let commitment = q.commitment();

        let proof = q.prove_position(0).unwrap();
        assert!(KzgQueue::verify_position(&srs, &commitment, &proof));

        // Try reusing witness for a different value at the same point.
        let reuse_proof = KzgPositionProof {
            witness: proof.witness,
            point: proof.point,
            value: Fr::from(200u64), // different value
        };
        assert!(
            !KzgQueue::verify_position(&srs, &commitment, &reuse_proof),
            "reusing witness for different value must fail (binding)"
        );
    }

    /// Edge case: value is Fr::ZERO.
    /// The pairing equation should NOT degenerate when v = 0.
    #[test]
    fn edge_case_value_is_zero() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        q.enqueue(Fr::zero()).unwrap();
        let commitment = q.commitment();

        let proof = q.prove_position(0).unwrap();
        assert_eq!(proof.value, Fr::zero());
        assert!(
            KzgQueue::verify_position(&srs, &commitment, &proof),
            "proving Fr::ZERO value must work"
        );

        // Tamper value to non-zero.
        let mut tampered = proof.clone();
        tampered.value = Fr::from(1u64);
        assert!(
            !KzgQueue::verify_position(&srs, &commitment, &tampered),
            "tampered proof for zero-value commitment must be rejected"
        );
    }

    /// Edge case: single-element queue (degree-0 polynomial).
    /// The polynomial is constant: p(x) = v for all x, but we use interpolation
    /// at one point so it's literally p(x) = v (constant).
    #[test]
    fn edge_case_single_element() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        q.enqueue(Fr::from(7u64)).unwrap();
        let commitment = q.commitment();

        let proof = q.prove_position(0).unwrap();
        assert!(KzgQueue::verify_position(&srs, &commitment, &proof));

        // The quotient for a constant poly p(x)=7 at point z is:
        // q(x) = (7 - 7)/(x - z) = 0, so witness should be the zero point.
        assert_eq!(proof.witness, G1Affine::zero());
    }

    /// Edge case: opening at position that maps to Fr(1) — the smallest non-zero element.
    /// Ensures (x - 1) division works correctly.
    #[test]
    fn edge_case_position_zero_maps_to_fr_one() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        q.enqueue(Fr::from(55u64)).unwrap();
        q.enqueue(Fr::from(66u64)).unwrap();

        let commitment = q.commitment();

        // Position 0 maps to Fr(1).
        let proof = q.prove_position(0).unwrap();
        assert_eq!(proof.point, Fr::from(1u64));
        assert_eq!(proof.value, Fr::from(55u64));
        assert!(KzgQueue::verify_position(&srs, &commitment, &proof));
    }

    /// Edge case: maximum degree polynomial (SRS exhaustion boundary).
    /// Fill queue to capacity and prove every position.
    #[test]
    fn edge_case_max_degree_srs_boundary() {
        let max_deg = 8;
        let srs = make_srs(max_deg);
        let mut q = KzgQueue::new(srs.clone(), max_deg);

        // Fill to capacity (polynomial degree = max_deg - 1 for interpolation).
        for i in 0..max_deg {
            q.enqueue(Fr::from((i + 1) as u64 * 11)).unwrap();
        }

        let commitment = q.commitment();

        // Prove every single position.
        for pos in 0..max_deg {
            let proof = q.prove_position(pos).unwrap();
            assert!(
                KzgQueue::verify_position(&srs, &commitment, &proof),
                "proof at max-capacity position {pos} must verify"
            );
        }
    }

    /// Batch Fiat-Shamir: verify rejects a batch proof with a manipulated gamma.
    /// This is the regression test for the fixed vulnerability.
    #[test]
    fn adversarial_batch_gamma_manipulation_rejected() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        for i in 1..=5 {
            q.enqueue(Fr::from(i * 10u64)).unwrap();
        }

        let commitment = q.commitment();

        // Generate a valid batch proof.
        let mut proof = q.prove_batch(&[0, 1, 2]).unwrap();
        assert!(KzgQueue::verify_batch(&srs, &commitment, &proof));

        // Adversary tampers with gamma.
        proof.gamma = Fr::from(12345u64);
        assert!(
            !KzgQueue::verify_batch(&srs, &commitment, &proof),
            "batch proof with manipulated gamma must be rejected by Fiat-Shamir check"
        );
    }

    /// Batch soundness: tampered evaluation in batch proof is rejected.
    #[test]
    fn adversarial_batch_value_tamper_rejected() {
        let srs = make_srs(64);
        let mut q = KzgQueue::new(srs.clone(), 32);

        for i in 1..=5 {
            q.enqueue(Fr::from(i * 10u64)).unwrap();
        }

        let commitment = q.commitment();

        // Create a batch proof with explicit gamma (bypasses Fiat-Shamir for this test
        // so we can test the pairing equation directly).
        let gamma = Fr::from(7777u64);
        let mut proof = q.prove_batch_with_challenge(&[0, 1, 2], gamma).unwrap();

        // Verify it works first (using test-only verifier).
        assert!(KzgQueue::verify_batch_with_explicit_gamma(
            &srs,
            &commitment,
            &proof
        ));

        // Tamper: change one evaluation value.
        proof.evaluations[1].1 = Fr::from(999u64);
        assert!(
            !KzgQueue::verify_batch_with_explicit_gamma(&srs, &commitment, &proof),
            "batch proof with tampered value must be rejected by pairing check"
        );
    }

    /// Cross-queue: proof from queue A does not verify against queue B's commitment.
    #[test]
    fn adversarial_cross_queue_proof_rejected() {
        let srs = make_srs(64);
        let mut qa = KzgQueue::new(srs.clone(), 16);
        let mut qb = KzgQueue::new(srs.clone(), 16);

        qa.enqueue(Fr::from(1u64)).unwrap();
        qa.enqueue(Fr::from(2u64)).unwrap();

        qb.enqueue(Fr::from(1u64)).unwrap();
        qb.enqueue(Fr::from(3u64)).unwrap(); // different second value

        let proof_a = qa.prove_position(1).unwrap();
        let proof_b = qb.prove_position(1).unwrap();

        // Each proof verifies against its own commitment.
        assert!(KzgQueue::verify_position(&srs, &qa.commitment(), &proof_a));
        assert!(KzgQueue::verify_position(&srs, &qb.commitment(), &proof_b));

        // Cross-verification fails.
        assert!(
            !KzgQueue::verify_position(&srs, &qb.commitment(), &proof_a),
            "proof from queue A must not verify against queue B"
        );
        assert!(
            !KzgQueue::verify_position(&srs, &qa.commitment(), &proof_b),
            "proof from queue B must not verify against queue A"
        );
    }

    /// Verify that polynomial division correctly rejects non-divisible cases.
    #[test]
    fn polynomial_division_remainder_detection() {
        // p(x) = x^2 + 1, divisor = (x - 1)
        // p(1) = 2 != 0, so (x^2 + 1) is NOT divisible by (x - 1).
        let numerator =
            DensePolynomial::from_coefficients_vec(vec![Fr::from(1u64), Fr::zero(), Fr::one()]);
        let divisor = DensePolynomial::from_coefficients_vec(vec![-Fr::one(), Fr::one()]);

        let result = polynomial_division(&numerator, &divisor);
        assert_eq!(
            result, None,
            "non-exact division must return None (non-zero remainder)"
        );

        // p(x) = x^2 - 1, divisor = (x - 1)
        // p(1) = 0, so (x^2 - 1) / (x - 1) = (x + 1).
        let numerator =
            DensePolynomial::from_coefficients_vec(vec![-Fr::one(), Fr::zero(), Fr::one()]);
        let result = polynomial_division(&numerator, &divisor);
        assert!(result.is_some(), "exact division must succeed");
        let quotient = result.unwrap();
        // quotient should be (x + 1) = [1, 1]
        assert_eq!(quotient.coeffs(), &[Fr::one(), Fr::one()]);
    }

    /// Verify the position_to_field_element mapping avoids zero.
    #[test]
    fn position_encoding_avoids_zero() {
        for pos in 0..100 {
            let fe = KzgQueue::position_to_field_element(pos);
            assert_ne!(
                fe,
                Fr::zero(),
                "position {pos} must not map to zero field element"
            );
        }
    }

    /// Verify all positions in a queue map to DISTINCT field elements.
    #[test]
    fn position_encoding_distinct() {
        let mut seen = std::collections::HashSet::new();
        for pos in 0..1000 {
            let fe = KzgQueue::position_to_field_element(pos);
            let bytes: Vec<u8> = {
                let mut buf = Vec::new();
                fe.serialize_compressed(&mut buf).unwrap();
                buf
            };
            assert!(
                seen.insert(bytes),
                "position {pos} maps to duplicate field element"
            );
        }
    }
}
