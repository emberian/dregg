//! Plonky3-recursion integration: real in-circuit STARK verification.
//!
//! This module uses the `p3-recursion` crate to produce recursive STARK proofs.
//! Given an inner proof (from our AIR), we generate a proof-of-proof: a STARK that
//! attests "the inner proof is valid" — enabling unbounded recursion.
//!
//! ## Architecture
//!
//! The recursion library requires:
//! 1. A `StarkConfig` for generating/verifying inner proofs (must match what the
//!    in-circuit verifier expects)
//! 2. A wrapper implementing `FriRecursionConfig` that adds verifier parameters
//! 3. A `FriRecursionBackendForExt<D>` that knows how to build the verifier circuit
//!
//! Our `P3MerklePoseidon2Air` (358 columns, degree-7) automatically satisfies the
//! `RecursiveAir` trait via the blanket impl in `p3-recursion`.
//!
//! ## Configuration
//!
//! - Base field: BabyBear (p = 2^31 - 2^27 + 1)
//! - Extension: BinomialExtensionField<BabyBear, 4> (degree-4)
//! - Hash/Compress/Challenger: Poseidon2 width-16 (matching recursion library)
//! - FRI: testing params (log_blowup=1, no PoW)

#[cfg(feature = "recursion")]
pub mod recursive {
    use std::sync::Arc;

    use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
    use p3_challenger::DuplexChallenger;
    use p3_circuit::{CircuitBuilder, CircuitRunner, NonPrimitiveOpId};
    use p3_circuit_prover::BatchStarkProver;
    use p3_commit::{ExtensionMmcs, Pcs};
    use p3_dft::Radix2DitParallel;
    use p3_field::Field;
    use p3_field::extension::BinomialExtensionField;
    use p3_fri::{FriParameters, TwoAdicFriPcs};
    use p3_lookup::logup::LogUpGadget;
    use p3_merkle_tree::MerkleTreeMmcs;
    use p3_recursion::pcs::{
        InputProofTargets, MerkleCapTargets, RecValMmcs, set_fri_mmcs_private_data,
    };
    use p3_recursion::traits::RecursiveAir;
    use p3_recursion::{
        FriRecursionBackend, FriRecursionConfig, FriVerifierParams, ProveNextLayerParams,
        RecursionInput, RecursionOutput, build_and_prove_next_layer, ops::Poseidon2Config,
    };
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use p3_uni_stark::{Proof, StarkConfig, StarkGenericConfig, Val, prove, verify};

    use crate::field::BabyBear;
    use crate::plonky3_prover::{
        P3MerklePoseidon2Air, generate_sound_merkle_trace, to_p3, trace_to_matrix,
    };

    // ========================================================================
    // Type definitions matching the recursion library's expected configuration
    // ========================================================================

    const D: usize = 4;
    const WIDTH: usize = 16;
    const RATE: usize = 8;
    const DIGEST_ELEMS: usize = 8;

    type F = P3BabyBear;
    type Challenge = BinomialExtensionField<F, D>;
    type Dft = Radix2DitParallel<F>;
    type Perm = Poseidon2BabyBear<WIDTH>;
    type MyHash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST_ELEMS>;
    type MyCompress = TruncatedPermutation<Perm, 2, DIGEST_ELEMS, WIDTH>;
    type MyMmcs = MerkleTreeMmcs<
        <F as Field>::Packing,
        <F as Field>::Packing,
        MyHash,
        MyCompress,
        2,
        DIGEST_ELEMS,
    >;
    type ChallengeMmcs = ExtensionMmcs<F, Challenge, MyMmcs>;
    type Challenger = DuplexChallenger<F, Perm, WIDTH, RATE>;
    type MyPcs = TwoAdicFriPcs<F, Dft, MyMmcs, ChallengeMmcs>;

    /// The raw STARK config type (without FRI verifier params wrapper).
    type InnerStarkConfig = StarkConfig<MyPcs, Challenge, Challenger>;

    /// The proof type produced by the recursion-compatible prover.
    /// Uses `PyanaRecursionConfig` as the SC parameter so it's directly
    /// usable with `RecursionInput` without type mismatches.
    pub type RecursionCompatibleProof = Proof<PyanaRecursionConfig>;

    /// FRI proof targets for the in-circuit verifier.
    type InnerFri = p3_recursion::pcs::FriProofTargets<
        F,
        Challenge,
        p3_recursion::pcs::RecExtensionValMmcs<
            F,
            Challenge,
            DIGEST_ELEMS,
            RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>,
        >,
        InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
        p3_recursion::pcs::Witness<F>,
    >;

    // ========================================================================
    // Config wrapper implementing FriRecursionConfig
    // ========================================================================

    /// Wrapper around our STARK config that adds FRI verifier params.
    ///
    /// This implements both `StarkGenericConfig` (by delegation) and
    /// `FriRecursionConfig` (required by the recursion backend).
    #[derive(Clone)]
    pub struct PyanaRecursionConfig {
        config: Arc<InnerStarkConfig>,
        fri_verifier_params: FriVerifierParams,
    }

    impl core::ops::Deref for PyanaRecursionConfig {
        type Target = InnerStarkConfig;
        fn deref(&self) -> &InnerStarkConfig {
            &self.config
        }
    }

    impl StarkGenericConfig for PyanaRecursionConfig {
        type Challenge = Challenge;
        type Challenger = Challenger;
        type Pcs = MyPcs;

        fn pcs(&self) -> &MyPcs {
            self.config.pcs()
        }

        fn initialise_challenger(&self) -> Challenger {
            self.config.initialise_challenger()
        }
    }

    impl FriRecursionConfig for PyanaRecursionConfig
    where
        MyPcs: p3_recursion::traits::RecursivePcs<
                PyanaRecursionConfig,
                InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
                InnerFri,
                MerkleCapTargets<F, DIGEST_ELEMS>,
                <MyPcs as Pcs<Challenge, Challenger>>::Domain,
            >,
    {
        type Commitment = MerkleCapTargets<F, DIGEST_ELEMS>;
        type InputProof =
            InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>;
        type OpeningProof = InnerFri;
        type RawOpeningProof = <MyPcs as Pcs<Challenge, Challenger>>::Proof;
        const DIGEST_ELEMS: usize = DIGEST_ELEMS;

        fn with_fri_opening_proof<'a, A, R>(
            prev: &RecursionInput<'a, Self, A>,
            f: impl FnOnce(&Self::RawOpeningProof) -> R,
        ) -> R
        where
            A: RecursiveAir<Val<Self>, Self::Challenge, LogUpGadget>,
        {
            match prev {
                RecursionInput::UniStark { proof, .. } => f(&proof.opening_proof),
                RecursionInput::BatchStark { proof, .. } => f(&proof.proof.opening_proof),
            }
        }

        fn prepare_circuit_for_verification(
            &self,
            circuit: &mut CircuitBuilder<Challenge>,
        ) -> Result<(), p3_recursion::verifier::VerificationError> {
            use p3_circuit::ops::generate_poseidon2_trace;
            use p3_poseidon2_circuit_air::BabyBearD4Width16;

            let perm = default_babybear_poseidon2_16();
            circuit.enable_poseidon2_perm::<BabyBearD4Width16, _>(
                generate_poseidon2_trace::<Challenge, BabyBearD4Width16>,
                perm,
            );
            circuit
                .enable_recompose::<F>(p3_circuit::ops::generate_recompose_trace::<F, Challenge>);
            Ok(())
        }

        fn pcs_verifier_params(
            &self,
        ) -> &<MyPcs as p3_recursion::traits::RecursivePcs<
            PyanaRecursionConfig,
            InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
            InnerFri,
            MerkleCapTargets<F, DIGEST_ELEMS>,
            <MyPcs as Pcs<Challenge, Challenger>>::Domain,
        >>::VerifierParams {
            &self.fri_verifier_params
        }

        fn set_fri_private_data(
            runner: &mut CircuitRunner<'_, Challenge>,
            op_ids: &[NonPrimitiveOpId],
            opening_proof: &Self::RawOpeningProof,
        ) -> Result<(), &'static str> {
            set_fri_mmcs_private_data::<
                F,
                Challenge,
                ChallengeMmcs,
                MyMmcs,
                MyHash,
                MyCompress,
                DIGEST_ELEMS,
            >(
                runner,
                op_ids,
                opening_proof,
                Poseidon2Config::BABY_BEAR_D4_W16,
            )
        }
    }

    // ========================================================================
    // Public API
    // ========================================================================

    /// Create the recursion-compatible STARK config.
    ///
    /// Uses Poseidon2 width-16 for all hash operations and the Duplex challenger.
    /// FRI parameters match the testing defaults from Plonky3 (log_blowup=2, 2 queries).
    pub fn create_recursion_config() -> PyanaRecursionConfig {
        let perm = default_babybear_poseidon2_16();
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm.clone());
        let val_mmcs = MyMmcs::new(hash, compress, 3);
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        // NOTE: These FRI params match the recursion library's testing defaults.
        // The OodEvaluationMismatch issue at Plonky3 rev 56952503 needs investigation
        // (may require updating P3MerklePoseidon2Air for API changes between
        // 82cfad73 and 56952503). See prove_for_recursion tests.
        let fri_params = FriParameters {
            log_blowup: 2,
            log_final_poly_len: 0,
            max_log_arity: 3,
            num_queries: 2,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 0,
            mmcs: challenge_mmcs,
        };
        let pcs = MyPcs::new(Dft::default(), val_mmcs, fri_params);
        let challenger = Challenger::new(perm);
        let config = StarkConfig::new(pcs, challenger);

        use p3_circuit::ops::PermConfig;
        let fri_verifier_params = FriVerifierParams::with_mmcs(
            2, // log_blowup (match prover)
            0, // log_final_poly_len
            0, // commit_pow_bits
            0, // query_pow_bits
            PermConfig::poseidon2(Poseidon2Config::BABY_BEAR_D4_W16),
        );

        PyanaRecursionConfig {
            config: Arc::new(config),
            fri_verifier_params,
        }
    }

    /// Create the FRI recursion backend for degree-4 extension.
    pub fn create_recursion_backend()
    -> p3_recursion::FriRecursionBackendForExt<D, WIDTH, RATE, Poseidon2Config> {
        FriRecursionBackend::new(Poseidon2Config::BABY_BEAR_D4_W16).for_extension_degree::<D>()
    }

    /// Generate a recursion-compatible inner proof.
    ///
    /// Uses the Poseidon2 width-16 config that the recursion library's in-circuit
    /// verifier knows how to verify.
    pub fn prove_for_recursion(
        trace: &[Vec<BabyBear>],
        public_inputs: &[BabyBear],
    ) -> RecursionCompatibleProof {
        let config = create_recursion_config();
        let air = P3MerklePoseidon2Air;

        let matrix = trace_to_matrix(trace);
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

        prove(&config, &air, matrix, &p3_public)
    }

    /// Verify a recursion-compatible inner proof.
    pub fn verify_for_recursion(
        proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<(), String> {
        let config = create_recursion_config();
        let air = P3MerklePoseidon2Air;

        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        verify(&config, &air, proof, &p3_public)
            .map_err(|e| format!("Recursion-compatible verification failed: {:?}", e))
    }

    /// Produce a recursive proof that verifies an inner proof in-circuit.
    ///
    /// This is the core recursion entry point. Given a proof generated by
    /// `prove_for_recursion`, it builds a verifier circuit and proves it.
    pub fn prove_recursive_layer(
        inner_proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<RecursionOutput<PyanaRecursionConfig>, String> {
        let config = create_recursion_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();

        let air = P3MerklePoseidon2Air;
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

        let input = RecursionInput::UniStark {
            proof: inner_proof,
            air: &air,
            public_inputs: p3_public,
            preprocessed_commit: None,
        };

        build_and_prove_next_layer::<PyanaRecursionConfig, P3MerklePoseidon2Air, _, D>(
            &input, &config, &backend, &params,
        )
        .map_err(|e| format!("Recursive proof generation failed: {:?}", e))
    }

    /// Verify a recursive proof output.
    pub fn verify_recursive_layer(
        output: &RecursionOutput<PyanaRecursionConfig>,
    ) -> Result<(), String> {
        let config = create_recursion_config();
        let prover = BatchStarkProver::new(config);
        prover
            .verify_all_tables(&output.0)
            .map_err(|e| format!("Recursive proof verification failed: {:?}", e))
    }

    /// End-to-end: generate an inner Merkle membership proof, then prove it recursively.
    pub fn prove_recursive_membership(
        leaf_hash: BabyBear,
        siblings: &[[BabyBear; 3]],
        positions: &[u8],
    ) -> Result<RecursionOutput<PyanaRecursionConfig>, String> {
        let (trace, public_inputs) = generate_sound_merkle_trace(leaf_hash, siblings, positions);
        let inner_proof = prove_for_recursion(&trace, &public_inputs);
        verify_for_recursion(&inner_proof, &public_inputs)?;
        prove_recursive_layer(&inner_proof, &public_inputs)
    }

    // ========================================================================
    // Tests
    // ========================================================================

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::poseidon2_air::create_poseidon2_test_witness;

        #[test]
        fn recursion_config_creation() {
            let _config = create_recursion_config();
            let _backend = create_recursion_backend();
        }

        #[test]
        fn inner_proof_recursion_compatible() {
            let leaf = BabyBear::new(42424242);
            let witness = create_poseidon2_test_witness(leaf, 4);

            let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
            let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

            let (trace, public_inputs) = generate_sound_merkle_trace(leaf, &siblings, &positions);
            let proof = prove_for_recursion(&trace, &public_inputs);
            let result = verify_for_recursion(&proof, &public_inputs);
            assert!(
                result.is_ok(),
                "Recursion-compatible inner proof failed: {:?}",
                result.err()
            );
        }

        /// Core POC: one layer of real in-circuit recursive STARK verification.
        #[test]
        fn recursive_merkle_poc() {
            let leaf = BabyBear::new(42424242);
            let witness = create_poseidon2_test_witness(leaf, 4);

            let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
            let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

            let result = prove_recursive_membership(leaf, &siblings, &positions);
            assert!(
                result.is_ok(),
                "Recursive proof generation failed: {:?}",
                result.err()
            );

            let output = result.unwrap();
            let verify_result = verify_recursive_layer(&output);
            assert!(
                verify_result.is_ok(),
                "Recursive proof verification failed: {:?}",
                verify_result.err()
            );
        }
    }
}
