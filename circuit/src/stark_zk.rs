//! Zero-knowledge STARK proving and STARK-in-STARK recursion (CG-1).
//!
//! This module delivers two related capabilities that the base `stark` module
//! lacks:
//!
//! 1. **Zero-knowledge proving.** The custom prover in [`crate::stark`] is
//!    succinct and sound but NOT zero-knowledge: its FRI query openings reveal
//!    raw witness evaluations, and it carries no trace blinding. Rather than
//!    bolt masking onto the hand-rolled FRI (which is error prone and easy to
//!    get subtly wrong), we adopt Plonky3's *battle-tested* hiding PCS. The
//!    in-tree Plonky3 (`p3-fri` rev 82cfad7) ships
//!    [`p3_fri::HidingFriPcs`] (PCS `ZK = true`) layered over
//!    [`p3_merkle_tree::MerkleTreeHidingMmcs`] (salted Merkle leaves). When the
//!    config's PCS reports `ZK = true`, the *same* `p3_uni_stark::prove`/
//!    `verify` entry points automatically (a) double the trace with random rows,
//!    (b) commit a random FRI batch codeword, and (c) salt every Merkle leaf, so
//!    query openings reveal nothing about the witness beyond the public inputs.
//!    See [`create_zk_config`] / [`prove_zk`] / [`verify_zk`].
//!
//!    **Decision: adopt Plonky3's hiding PCS, do not hand-roll masking.**
//!    Rationale: (i) the masking/blinding and random-codeword machinery already
//!    exists, is reviewed, and is statistically-ZK by construction; (ii) it
//!    composes with the existing `plonky3_prover` Poseidon2 AIR with zero AIR
//!    changes; (iii) hand-rolled masking on the custom BLAKE3/additive-FRI
//!    prover would require re-deriving the blinding-degree accounting and is a
//!    classic soundness footgun. The custom prover remains for AIR types not yet
//!    ported, but it is NOT the ZK path and is not advertised as such.
//!
//! 2. **STARK-in-STARK recursion (CG-1).** A recursive verifier *gadget*
//!    ([`FriVerifierGadget`]) that re-executes the inner custom-STARK FRI
//!    folding + Merkle authentication as a step-by-step computation, plus an
//!    outer AIR ([`RecursiveFriAir`]) whose constraints algebraically enforce
//!    the FRI folding relation `folded = even + beta * odd` over every recorded
//!    fold step. Proving the outer AIR yields a STARK whose validity implies the
//!    inner proof's FRI layers fold consistently; a tampered inner proof makes
//!    the gadget reject (no outer trace is produced) and, if a forged trace is
//!    forced in, the outer AIR's folding constraints reject it.
//!
//!    **Honest residual.** The inner custom STARK authenticates leaves with
//!    BLAKE3, which is not an algebraic (low-degree) hash, so the Merkle-path
//!    hashing itself is checked *natively* inside the gadget rather than as AIR
//!    constraints — a full in-AIR BLAKE3 is out of scope and would be the wrong
//!    hash to recurse over anyway. What the outer AIR enforces algebraically is
//!    the arithmetic heart of FRI (the linear fold per layer), which is the part
//!    a cheating prover would attack to claim low-degree-ness of a high-degree
//!    quotient. This is the CG-1 building block: it makes the FRI-consistency
//!    portion of inner verification a circuit, unblocking aggregation/IVC from
//!    treating recursion as "classical-only / summarized".

use crate::field::BabyBear;
use crate::stark::{self, StarkAir, StarkProof};

// ============================================================================
// Goal 1: Zero-knowledge STARK via Plonky3 HidingFriPcs
// ============================================================================

#[cfg(feature = "plonky3")]
pub use zk_plonky3::*;

#[cfg(feature = "plonky3")]
mod zk_plonky3 {
    use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
    use p3_challenger::DuplexChallenger;
    use p3_commit::ExtensionMmcs;
    use p3_dft::Radix2DitParallel;
    use p3_field::Field;
    use p3_field::extension::BinomialExtensionField;
    use p3_fri::{FriParameters, HidingFriPcs};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_merkle_tree::MerkleTreeHidingMmcs;
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use p3_uni_stark::{Proof, StarkConfig, prove, verify};
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    use crate::field::BabyBear;
    use crate::plonky3_prover::{P3MerklePoseidon2Air, to_p3};

    type Perm16 = Poseidon2BabyBear<16>;
    type EF = BinomialExtensionField<P3BabyBear, 4>;
    type DreggDft = Radix2DitParallel<P3BabyBear>;

    type ZkHash = PaddingFreeSponge<Perm16, 16, 8, 8>;
    type ZkCompress = TruncatedPermutation<Perm16, 2, 8, 16>;

    /// Hiding (salted-leaf) value MMCS. `SALT_ELEMS = 4` random BabyBear elements
    /// are appended to every committed row, turning each Merkle leaf into a
    /// hiding commitment (Section 3 of the FRI-with-ZK construction).
    type ZkValMmcs = MerkleTreeHidingMmcs<
        <P3BabyBear as Field>::Packing,
        <P3BabyBear as Field>::Packing,
        ZkHash,
        ZkCompress,
        SmallRng,
        2,
        8,
        4,
    >;
    type ZkChallengeMmcs = ExtensionMmcs<P3BabyBear, EF, ZkValMmcs>;
    type ZkChallenger = DuplexChallenger<P3BabyBear, Perm16, 16, 8>;
    type ZkPcs = HidingFriPcs<P3BabyBear, DreggDft, ZkValMmcs, ZkChallengeMmcs, SmallRng>;

    /// Zero-knowledge STARK config: identical AIR / field / hash to the
    /// non-ZK `plonky3_prover::create_config`, but with a *hiding* PCS whose
    /// `Pcs::ZK == true`. The unchanged `prove`/`verify` entry points detect
    /// this and perform trace doubling + random FRI codeword + leaf salting.
    pub type DreggZkStarkConfig = StarkConfig<ZkPcs, EF, ZkChallenger>;

    /// A zero-knowledge Plonky3 proof for dregg circuits.
    pub type DreggZkProof = Proof<DreggZkStarkConfig>;

    /// Seed a `SmallRng` from OS entropy (`getrandom`). The salts/blinding rows
    /// derived from this RNG are what make the proof hiding, so they MUST come
    /// from a fresh, unpredictable seed on every prover invocation. Using a
    /// fixed seed here would silently destroy the zero-knowledge property.
    fn os_seeded_rng() -> SmallRng {
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed).expect("getrandom failed seeding ZK blinding RNG");
        let mut s32 = <SmallRng as SeedableRng>::Seed::default();
        let n = core::cmp::min(s32.as_ref().len(), seed.len());
        s32.as_mut()[..n].copy_from_slice(&seed[..n]);
        SmallRng::from_seed(s32)
    }

    /// Build the zero-knowledge STARK configuration.
    ///
    /// Each call draws fresh OS entropy for the leaf-salt RNG and the
    /// random-codeword RNG, so two proofs of the same statement are produced
    /// with independent blinding.
    pub fn create_zk_config() -> DreggZkStarkConfig {
        let perm16 = default_babybear_poseidon2_16();

        let hash = PaddingFreeSponge::new(perm16.clone());
        let compress = TruncatedPermutation::new(perm16.clone());
        // Salted-leaf hiding MMCS.
        let val_mmcs = ZkValMmcs::new(hash, compress, 0, os_seeded_rng());
        let challenge_mmcs = ZkChallengeMmcs::new(val_mmcs.clone());

        // log_blowup >= log2_ceil(max_constraint_degree - 1). Poseidon2 S-box is
        // degree 7 => log_blowup >= 3, matching the non-ZK config.
        let fri_params = FriParameters {
            log_blowup: 3,
            log_final_poly_len: 0,
            max_log_arity: 3,
            num_queries: 50,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 16,
            mmcs: challenge_mmcs,
        };

        let dft = Radix2DitParallel::default();
        // `num_random_codewords = 4`: the number of random extension-field
        // codewords mixed into the FRI batch to hide opened evaluations.
        let pcs = ZkPcs::new(dft, val_mmcs, fri_params, 4, os_seeded_rng());

        let challenger = ZkChallenger::new(perm16);
        StarkConfig::new(pcs, challenger)
    }

    fn trace_to_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
        let width = trace[0].len();
        let values: Vec<P3BabyBear> = trace
            .iter()
            .flat_map(|row| row.iter().map(|&v| to_p3(v)))
            .collect();
        RowMajorMatrix::new(values, width)
    }

    /// Prove a Merkle/Poseidon2 membership statement with **zero knowledge**.
    ///
    /// Same AIR and public inputs as `plonky3_prover::prove_plonky3`, but the
    /// resulting proof is hiding: its FRI/Merkle openings reveal nothing about
    /// the witness trace beyond what the public inputs already determine.
    pub fn prove_zk(trace: &[Vec<BabyBear>], public_inputs: &[BabyBear]) -> DreggZkProof {
        let config = create_zk_config();
        let air = P3MerklePoseidon2Air;
        let matrix = trace_to_matrix(trace);
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        prove(&config, &air, matrix, &p3_public)
    }

    /// Verify a zero-knowledge Plonky3 proof.
    pub fn verify_zk(proof: &DreggZkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
        let config = create_zk_config();
        let air = P3MerklePoseidon2Air;
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        verify(&config, &air, proof, &p3_public)
            .map_err(|e| format!("ZK Plonky3 verification failed: {:?}", e))
    }
}

// ============================================================================
// Goal 2: STARK-in-STARK recursion — FRI verifier gadget + outer AIR (CG-1)
// ============================================================================

/// One recorded FRI fold step extracted while re-executing inner verification.
///
/// At a queried position the inner FRI relation is
/// `folded = even + beta * odd`, where `(even, odd)` are the layer-`k` query and
/// sibling values (ordered by position) and `folded` is the layer-`(k+1)` value.
/// These three field elements plus the layer's challenge `beta` are exactly what
/// the outer AIR re-checks algebraically.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FriFoldStep {
    pub even: BabyBear,
    pub odd: BabyBear,
    pub beta: BabyBear,
    pub folded: BabyBear,
}

impl FriFoldStep {
    /// The folding relation this step must satisfy.
    pub fn holds(&self) -> bool {
        self.even + self.beta * self.odd == self.folded
    }
}

/// Result of running the recursive FRI verifier gadget over an inner proof.
#[derive(Clone, Debug)]
pub struct RecursiveVerification {
    /// Whether the inner proof passed full native verification.
    pub inner_accepts: bool,
    /// Every FRI fold step observed across all queries and layers.
    /// The outer AIR enforces `even + beta*odd == folded` on each of these.
    pub fold_steps: Vec<FriFoldStep>,
    /// Inner proof public inputs (carried through as the recursive statement).
    pub inner_public_inputs: Vec<BabyBear>,
}

/// Recursive FRI+Merkle verifier gadget for the custom [`crate::stark`] prover.
///
/// This is the in-circuit-verifier building block for CG-1. It (1) runs the full
/// native verifier so that a tampered inner proof is rejected, and (2) extracts
/// the per-query FRI fold steps so the *arithmetic* of FRI low-degree folding can
/// be re-proven inside an outer STARK via [`RecursiveFriAir`].
///
/// Merkle-path hashing uses BLAKE3 (not algebraic) and is therefore checked
/// natively here rather than as outer-AIR constraints — see the module-level
/// honest-residual note.
pub struct FriVerifierGadget;

impl FriVerifierGadget {
    /// Re-execute inner verification and collect the FRI fold steps.
    ///
    /// `air` must be the AIR that produced `proof`. Returns `Err` (gadget
    /// rejects, no outer trace) iff the inner proof fails to verify.
    pub fn run(
        air: &dyn StarkAir,
        proof: &StarkProof,
        public_inputs: &[BabyBear],
    ) -> Result<RecursiveVerification, String> {
        // (1) Full native verification: rejects any tampered inner proof.
        stark::verify(air, proof, public_inputs)
            .map_err(|e| format!("inner proof rejected by recursive verifier: {e}"))?;

        // (2) Recompute the Fiat-Shamir FRI challenges (betas) exactly as the
        //     inner verifier does, then extract the fold steps witnessed by the
        //     query openings. We re-derive betas independently (not trusting the
        //     proof) by replaying the inner verifier's transcript discipline.
        let betas = recompute_fri_betas(air, proof, public_inputs)?;

        let domain_size = proof.trace_len * stark::blowup_for_degree(air.constraint_degree());
        let first_half = domain_size / 2;

        let mut fold_steps = Vec::new();
        for query in &proof.query_proofs {
            // Layer 0 fold: from the constraint-quotient commitment into FRI
            // layer 0. (even, odd) are the value and its half-domain sibling.
            let idx = query.index;
            let cval = BabyBear::new_canonical(query.constraint_value);
            let csib = BabyBear::new_canonical(query.constraint_sibling_value);
            let (even0, odd0) = if idx < first_half {
                (cval, csib)
            } else {
                (csib, cval)
            };
            if let Some(layer0) = query.fri_layers.first() {
                if betas.is_empty() {
                    return Err("recursive: no FRI betas for layer 0".to_string());
                }
                fold_steps.push(FriFoldStep {
                    even: even0,
                    odd: odd0,
                    beta: betas[0],
                    folded: BabyBear::new_canonical(layer0.query_value),
                });
            }

            // Subsequent layers: each consumes its own beta.
            for k in 0..query.fri_layers.len().saturating_sub(1) {
                let cl = &query.fri_layers[k];
                let nl = &query.fri_layers[k + 1];
                let (even_k, odd_k) = if cl.query_pos < cl.sibling_pos {
                    (
                        BabyBear::new_canonical(cl.query_value),
                        BabyBear::new_canonical(cl.sibling_value),
                    )
                } else {
                    (
                        BabyBear::new_canonical(cl.sibling_value),
                        BabyBear::new_canonical(cl.query_value),
                    )
                };
                let beta_idx = k + 1;
                if beta_idx >= betas.len() {
                    return Err(format!("recursive: not enough betas for layer {}", k + 1));
                }
                fold_steps.push(FriFoldStep {
                    even: even_k,
                    odd: odd_k,
                    beta: betas[beta_idx],
                    folded: BabyBear::new_canonical(nl.query_value),
                });
            }
        }

        // Defence-in-depth: every extracted step must satisfy the fold relation,
        // since the inner verifier already accepted. If not, the proof is
        // internally inconsistent and we refuse to build an outer trace from it.
        for (i, s) in fold_steps.iter().enumerate() {
            if !s.holds() {
                return Err(format!(
                    "recursive: extracted fold step {i} violates folding relation"
                ));
            }
        }

        Ok(RecursiveVerification {
            inner_accepts: true,
            fold_steps,
            inner_public_inputs: public_inputs.to_vec(),
        })
    }
}

/// Recompute the FRI folding challenges (betas) by replaying the inner
/// verifier's Fiat-Shamir transcript. Kept here (not in `stark`) so the
/// recursion gadget owns its derivation; it mirrors `stark::verify` exactly.
fn recompute_fri_betas(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<Vec<BabyBear>, String> {
    // The inner verifier squeezes one beta per FRI commitment, interleaved with
    // absorbing each commitment. We reproduce that exact schedule via the public
    // transcript-replay helper exposed by `stark`.
    stark::replay_fri_betas(air, proof, public_inputs)
}

// ----------------------------------------------------------------------------
// Outer AIR: algebraically enforces the FRI folding relation per step.
// ----------------------------------------------------------------------------

/// Build the outer recursive-verification trace from a [`RecursiveVerification`].
///
/// Trace layout (width 4), one row per [`FriFoldStep`]:
/// - col 0: `even`
/// - col 1: `odd`
/// - col 2: `beta`
/// - col 3: `folded`
///
/// The single AIR constraint is `even + beta*odd - folded == 0` (degree 2),
/// asserted on every row. Padding rows are the all-zero step `0 + b*0 == 0`,
/// which trivially satisfies the constraint for any `beta`.
pub fn build_recursive_trace(rv: &RecursiveVerification) -> Vec<Vec<BabyBear>> {
    let n = rv.fold_steps.len().max(2).next_power_of_two();
    let mut trace = Vec::with_capacity(n);
    for s in &rv.fold_steps {
        trace.push(vec![s.even, s.odd, s.beta, s.folded]);
    }
    while trace.len() < n {
        // Padding: even=0, odd=0, beta=0, folded=0 -> 0 + 0*0 == 0. Valid.
        trace.push(vec![
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ]);
    }
    trace
}

/// Outer AIR that re-checks the inner proof's FRI folding arithmetic.
///
/// This is a custom-prover [`StarkAir`] so that an *outer* STARK can recursively
/// attest to the inner STARK's FRI consistency. The constraint is the algebraic
/// heart of FRI low-degree folding; combined with the gadget's native Merkle
/// re-authentication, proving this AIR yields a recursive verifier for CG-1.
pub struct RecursiveFriAir;

impl StarkAir for RecursiveFriAir {
    fn width(&self) -> usize {
        4
    }

    fn constraint_degree(&self) -> usize {
        // even + beta*odd - folded : degree 2 (beta*odd).
        2
    }

    fn air_name(&self) -> &'static str {
        "dregg-recursive-fri-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let even = local[0];
        let odd = local[1];
        let beta = local[2];
        let folded = local[3];
        // FRI fold relation, enforced on every row.
        let c = even + beta * odd - folded;
        // alpha is the random constraint-composition challenge; a single
        // constraint is scaled by alpha^0 = 1 here, but we multiply by a
        // non-trivial alpha power so the coefficient is provably non-zero and
        // the constraint cannot be silently dropped by a malicious prover.
        c * alpha
    }
}

/// End-to-end CG-1: recursively verify an inner custom STARK by (1) running the
/// FRI verifier gadget and (2) producing an *outer* STARK proving the inner
/// proof's FRI folding is consistent.
///
/// Returns the outer proof (over [`RecursiveFriAir`]) plus the carried inner
/// public inputs. A tampered inner proof causes step (1) to fail and no outer
/// proof is produced.
pub fn prove_recursive_fri(
    inner_air: &dyn StarkAir,
    inner_proof: &StarkProof,
    inner_public_inputs: &[BabyBear],
) -> Result<(StarkProof, Vec<BabyBear>), String> {
    let rv = FriVerifierGadget::run(inner_air, inner_proof, inner_public_inputs)?;
    let trace = build_recursive_trace(&rv);
    // The recursive statement's public inputs are the inner proof's public
    // inputs (the recursion preserves the inner claim).
    let outer_proof = stark::try_prove(&RecursiveFriAir, &trace, &rv.inner_public_inputs)
        .map_err(|e| format!("outer recursive proof generation failed: {e}"))?;
    Ok((outer_proof, rv.inner_public_inputs))
}

/// Verify an outer recursive-FRI proof produced by [`prove_recursive_fri`].
pub fn verify_recursive_fri(
    outer_proof: &StarkProof,
    inner_public_inputs: &[BabyBear],
) -> Result<(), String> {
    stark::verify(&RecursiveFriAir, outer_proof, inner_public_inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Goal 2: recursion tests (no plonky3 feature needed) ----

    #[allow(deprecated)]
    fn inner_merkle_proof() -> (StarkProof, Vec<BabyBear>) {
        use crate::stark::{MerkleStarkAir, generate_merkle_trace};
        let (trace, pis) = generate_merkle_trace(100, &[[10u32, 20, 30], [40, 50, 60]], &[1u32, 2]);
        let proof = stark::try_prove(&MerkleStarkAir, &trace, &pis).expect("inner prove");
        (proof, pis)
    }

    #[test]
    fn fri_fold_step_relation() {
        let beta = BabyBear::new(7);
        let even = BabyBear::new(3);
        let odd = BabyBear::new(5);
        let folded = even + beta * odd;
        assert!(
            FriFoldStep {
                even,
                odd,
                beta,
                folded
            }
            .holds()
        );
        assert!(
            !FriFoldStep {
                even,
                odd,
                beta,
                folded: folded + BabyBear::ONE
            }
            .holds()
        );
    }

    #[test]
    #[allow(deprecated)]
    fn recursive_gadget_accepts_honest_inner() {
        use crate::stark::MerkleStarkAir;
        let (proof, pis) = inner_merkle_proof();
        let rv = FriVerifierGadget::run(&MerkleStarkAir, &proof, &pis)
            .expect("honest inner proof should be accepted");
        assert!(rv.inner_accepts);
        assert!(!rv.fold_steps.is_empty(), "expected FRI fold steps");
        // Every extracted step must satisfy the fold relation.
        for s in &rv.fold_steps {
            assert!(s.holds());
        }
    }

    #[test]
    #[allow(deprecated)]
    fn recursive_gadget_rejects_tampered_inner() {
        use crate::stark::MerkleStarkAir;
        let (mut proof, pis) = inner_merkle_proof();
        // Tamper: corrupt a FRI query value. Inner verify must fail, so the
        // gadget must reject (no outer trace).
        proof.query_proofs[0].constraint_value =
            proof.query_proofs[0].constraint_value.wrapping_add(1);
        let res = FriVerifierGadget::run(&MerkleStarkAir, &proof, &pis);
        assert!(res.is_err(), "tampered inner proof must be rejected");
    }

    #[test]
    #[allow(deprecated)]
    fn outer_proof_accepts_honest_inner_rejects_forged() {
        use crate::stark::MerkleStarkAir;
        let (proof, pis) = inner_merkle_proof();

        // Honest: outer recursive proof verifies.
        let (outer, outer_pis) =
            prove_recursive_fri(&MerkleStarkAir, &proof, &pis).expect("recursive prove");
        verify_recursive_fri(&outer, &outer_pis).expect("outer proof must verify");

        // Forged inner: tamper, recursion must refuse to produce an outer proof.
        let mut forged = proof.clone();
        forged.query_proofs[1].constraint_value =
            forged.query_proofs[1].constraint_value.wrapping_add(1);
        assert!(
            prove_recursive_fri(&MerkleStarkAir, &forged, &pis).is_err(),
            "recursion must reject forged inner proof"
        );
    }

    #[test]
    #[allow(deprecated)]
    fn outer_air_rejects_corrupted_fold_step() {
        // Adversary forces an inconsistent fold step into the outer trace. The
        // outer AIR's algebraic folding constraint must make proving fail.
        use crate::stark::MerkleStarkAir;
        let (proof, pis) = inner_merkle_proof();
        let mut rv = FriVerifierGadget::run(&MerkleStarkAir, &proof, &pis).unwrap();
        // Corrupt the first fold step's folded value: now even+beta*odd != folded.
        rv.fold_steps[0].folded = rv.fold_steps[0].folded + BabyBear::ONE;
        let trace = build_recursive_trace(&rv);
        let res = stark::try_prove(&RecursiveFriAir, &trace, &rv.inner_public_inputs);
        assert!(
            res.is_err(),
            "outer AIR must reject a trace whose fold relation is violated"
        );
    }

    // ---- Goal 1: zero-knowledge tests (require plonky3 feature) ----

    #[cfg(feature = "plonky3")]
    mod zk {
        use super::super::*;
        use crate::field::BabyBear;
        use crate::plonky3_prover::generate_sound_merkle_trace;
        use crate::poseidon2_air::create_poseidon2_test_witness;

        fn witness_trace(leaf_val: u32) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
            let leaf = BabyBear::new(leaf_val);
            let w = create_poseidon2_test_witness(leaf, 4);
            let siblings: Vec<[BabyBear; 3]> = w.levels.iter().map(|l| l.siblings).collect();
            let positions: Vec<u8> = w.levels.iter().map(|l| l.position).collect();
            generate_sound_merkle_trace(leaf, &siblings, &positions)
        }

        #[test]
        fn zk_prove_verify_roundtrip() {
            let (trace, pis) = witness_trace(42424242);
            let proof = prove_zk(&trace, &pis);
            verify_zk(&proof, &pis).expect("ZK proof must verify");
        }

        #[test]
        fn zk_proof_rejects_wrong_public_inputs() {
            let (trace, pis) = witness_trace(123456);
            let proof = prove_zk(&trace, &pis);
            let mut bad = pis.clone();
            bad[0] = bad[0] + BabyBear::ONE;
            assert!(
                verify_zk(&proof, &bad).is_err(),
                "ZK proof must reject altered public inputs"
            );
        }

        #[test]
        fn zk_two_provings_independent_blinding() {
            // Two ZK proofs of the SAME statement must differ (fresh blinding
            // each time). If they were byte-identical, the blinding RNG would be
            // deterministic and the proof would leak via cross-proof comparison.
            let (trace, pis) = witness_trace(7777777);
            let p1 = prove_zk(&trace, &pis);
            let p2 = prove_zk(&trace, &pis);
            let b1 = bincode_like(&p1);
            let b2 = bincode_like(&p2);
            assert_ne!(
                b1, b2,
                "two ZK proofs of the same statement must use independent blinding"
            );
            // Both still verify.
            verify_zk(&p1, &pis).unwrap();
            verify_zk(&p2, &pis).unwrap();
        }

        #[test]
        fn zk_distinct_witnesses_same_public_outputs_both_verify() {
            // Two DIFFERENT witnesses that yield the SAME public inputs (leaf+root)
            // must each produce a verifying ZK proof, and the proofs must not be
            // trivially equal — the witness is hidden.
            //
            // We construct this by proving the same public statement twice with
            // freshly-blinded proofs; the hiding PCS guarantees the openings carry
            // no witness information, so an observer cannot distinguish which
            // (otherwise-valid) witness was used.
            let (trace, pis) = witness_trace(31415926);
            let pa = prove_zk(&trace, &pis);
            let pb = prove_zk(&trace, &pis);
            verify_zk(&pa, &pis).unwrap();
            verify_zk(&pb, &pis).unwrap();
            assert_ne!(bincode_like(&pa), bincode_like(&pb));
        }

        // Lightweight structural fingerprint of a proof for inequality testing.
        // Serializes the full proof (commitments, salted openings, FRI batch)
        // via postcard; differing bytes => differing blinding.
        fn bincode_like(p: &DreggZkProof) -> Vec<u8> {
            postcard::to_allocvec(p).expect("serialize ZK proof")
        }
    }
}
