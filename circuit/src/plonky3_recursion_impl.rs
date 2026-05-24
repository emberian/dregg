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
//! Any AIR that implements `p3-air::Air<InteractionSymbolicBuilder<F, EF>>`
//! automatically satisfies the `RecursiveAir` trait via the blanket impl in
//! `p3-recursion`. `P3MerklePoseidon2Air` (358 columns, degree-7) was the first
//! AIR proven through this path; `prove_recursive_layer` is now generic so any
//! `Air`-implementing AIR (e.g., `AggregationAir`, the Effect VM AIR via its
//! `p3-air` bridge) can be wrapped without code duplication.
//!
//! ## Configuration
//!
//! - Base field: BabyBear (p = 2^31 - 2^27 + 1)
//! - Extension: BinomialExtensionField<BabyBear, 4> (degree-4)
//! - Hash/Compress/Challenger: Poseidon2 width-16 (matching recursion library)
//! - FRI: log_blowup=3 (required for degree-7 AIR), cap_height=0, max_log_arity=1
//!   — the same blowup is reused for lower-degree AIRs; it costs a little prover
//!   work but the resulting recursion config is shared.

#[cfg(feature = "recursion")]
pub mod recursive {
    use std::sync::Arc;

    use p3_air::{Air, BaseAir, SymbolicExpressionExt};
    use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
    use p3_challenger::DuplexChallenger;
    use p3_circuit::{CircuitBuilder, CircuitRunner, NonPrimitiveOpId};
    use p3_circuit_prover::BatchStarkProver;
    use p3_commit::{ExtensionMmcs, Pcs};
    use p3_dft::Radix2DitParallel;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{Algebra, Field};
    use p3_fri::{FriParameters, TwoAdicFriPcs};
    use p3_lookup::logup::LogUpGadget;
    use p3_lookup::symbolic::InteractionSymbolicBuilder;
    use p3_matrix::dense::RowMajorMatrix;
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
    use p3_uni_stark::{
        Proof, StarkConfig, StarkGenericConfig, SymbolicExpression, Val, prove, verify,
    };

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
    /// FRI parameters: log_blowup=3 (for degree-7 AIR), max_log_arity=1, 2 queries, no PoW.
    pub fn create_recursion_config() -> PyanaRecursionConfig {
        let perm = default_babybear_poseidon2_16();
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm.clone());
        // cap_height=0: single root digest. This is required because with small traces
        // (e.g. 4 rows -> tree depth 2), a larger cap_height would exceed tree depth.
        // The recursion library derives cap structure from the proof, so cap_height=0
        // gives the most compatible behavior.
        let val_mmcs = MyMmcs::new(hash, compress, 0);
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        // log_blowup must be >= 3 because our AIR has degree-7 constraints (x^7 S-box).
        // With degree d=7 and blowup B, the quotient domain needs B >= d-1 = 6, so log_blowup >= 3.
        let fri_params = FriParameters {
            log_blowup: 3,
            log_final_poly_len: 0,
            max_log_arity: 1,
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
            3, // log_blowup (match prover)
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

    /// Trait alias capturing the bounds an AIR must satisfy to flow through this
    /// recursion path. Any AIR implementing `p3-air::Air` against both the
    /// uni-stark prover/verifier and the `InteractionSymbolicBuilder` (which is
    /// what `p3-recursion`'s blanket `RecursiveAir` impl needs) satisfies this.
    ///
    /// Concretely, this means:
    /// 1. `BaseAir<F>` — width + public-value count for the prover/verifier.
    /// 2. `Air<SymbolicAirBuilder<F>>` — what `p3_uni_stark` calls into when
    ///    extracting symbolic constraints prior to proving.
    /// 3. `Air<ProverConstraintFolder<SC>>` and
    ///    `Air<VerifierConstraintFolder<SC>>` — what `p3_uni_stark::prove` and
    ///    `verify` invoke for the standalone inner proof.
    /// 4. `Air<DebugConstraintBuilder<F>>` — what `p3_uni_stark` uses for the
    ///    debug-mode trace consistency check.
    /// 5. `Air<InteractionSymbolicBuilder<F, EF>>` — what the recursion
    ///    library's blanket `RecursiveAir` impl extracts symbolic constraints
    ///    from for the verifier circuit.
    ///
    /// Plus `Sync + 'static` so the proof generator can hand the AIR around.
    pub trait RecursableAir:
        BaseAir<P3BabyBear>
        + for<'a> Air<p3_uni_stark::ProverConstraintFolder<'a, PyanaRecursionConfig>>
        + for<'a> Air<p3_uni_stark::VerifierConstraintFolder<'a, PyanaRecursionConfig>>
        + for<'a> Air<p3_air::DebugConstraintBuilder<'a, P3BabyBear>>
        + Air<p3_uni_stark::SymbolicAirBuilder<P3BabyBear>>
        + Air<InteractionSymbolicBuilder<P3BabyBear, Challenge>>
        + Sync
        + 'static
    {
    }

    impl<A> RecursableAir for A where
        A: BaseAir<P3BabyBear>
            + for<'a> Air<p3_uni_stark::ProverConstraintFolder<'a, PyanaRecursionConfig>>
            + for<'a> Air<p3_uni_stark::VerifierConstraintFolder<'a, PyanaRecursionConfig>>
            + for<'a> Air<p3_air::DebugConstraintBuilder<'a, P3BabyBear>>
            + Air<p3_uni_stark::SymbolicAirBuilder<P3BabyBear>>
            + Air<InteractionSymbolicBuilder<P3BabyBear, Challenge>>
            + Sync
            + 'static
    {
    }

    /// Generate a recursion-compatible inner proof for `P3MerklePoseidon2Air`
    /// from a pre-built trace.
    ///
    /// Kept as a convenience for the Merkle-membership POC; new callers should
    /// prefer [`prove_inner_for_air`] which accepts any [`RecursableAir`].
    pub fn prove_for_recursion(
        trace: &[Vec<BabyBear>],
        public_inputs: &[BabyBear],
    ) -> RecursionCompatibleProof {
        let air = P3MerklePoseidon2Air;
        let matrix = trace_to_matrix(trace);
        prove_inner_for_air(&air, matrix, public_inputs)
    }

    /// Verify a recursion-compatible inner proof for `P3MerklePoseidon2Air`.
    pub fn verify_for_recursion(
        proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<(), String> {
        let air = P3MerklePoseidon2Air;
        verify_inner_for_air(&air, proof, public_inputs)
    }

    /// Generic inner proof generator: any AIR satisfying [`RecursableAir`]
    /// can be proven with the recursion-compatible STARK config.
    pub fn prove_inner_for_air<A>(
        air: &A,
        trace: RowMajorMatrix<P3BabyBear>,
        public_inputs: &[BabyBear],
    ) -> RecursionCompatibleProof
    where
        A: RecursableAir,
    {
        let config = create_recursion_config();
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        prove(&config, air, trace, &p3_public)
    }

    /// Generic inner proof verifier (paired with [`prove_inner_for_air`]).
    pub fn verify_inner_for_air<A>(
        air: &A,
        proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<(), String>
    where
        A: RecursableAir,
    {
        let config = create_recursion_config();
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        verify(&config, air, proof, &p3_public)
            .map_err(|e| format!("Recursion-compatible verification failed: {:?}", e))
    }

    /// Produce a recursive proof that verifies a `P3MerklePoseidon2Air` inner
    /// proof in-circuit. Kept for backwards-compatibility with the
    /// Merkle-membership tests; new callers should prefer
    /// [`prove_recursive_layer_for_air`].
    pub fn prove_recursive_layer(
        inner_proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<RecursionOutput<PyanaRecursionConfig>, String> {
        let air = P3MerklePoseidon2Air;
        prove_recursive_layer_for_air(&air, inner_proof, public_inputs)
    }

    /// Produce a recursive proof for any `RecursableAir` inner proof.
    ///
    /// This is the generalized core recursion entry point. The Effect VM AIR
    /// (via its `p3-air` bridge), the simpler `AggregationAir`, and the
    /// canonical `P3MerklePoseidon2Air` all flow through this single function.
    pub fn prove_recursive_layer_for_air<A>(
        air: &A,
        inner_proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<RecursionOutput<PyanaRecursionConfig>, String>
    where
        A: RecursableAir,
    {
        let config = create_recursion_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();

        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

        let input = RecursionInput::UniStark {
            proof: inner_proof,
            air,
            public_inputs: p3_public,
            preprocessed_commit: None,
        };

        build_and_prove_next_layer::<PyanaRecursionConfig, A, _, D>(
            &input, &config, &backend, &params,
        )
        .map_err(|e| format!("Recursive proof generation failed: {:?}", e))
    }

    /// Verify a recursive proof output.
    pub fn verify_recursive_layer(
        output: &RecursionOutput<PyanaRecursionConfig>,
    ) -> Result<(), String> {
        verify_recursive_batch_proof(&output.0)
    }

    /// Verify a recursive proof from just the inner `BatchStarkProof`.
    ///
    /// Useful when the proof was serialised by itself (the
    /// `Rc<CircuitProverData<SC>>` half of `RecursionOutput` is only
    /// needed for *chaining* the proof into another recursion layer, not
    /// for verifying it). Block 3's scope-2 recursive replay path uses
    /// this entrypoint with postcard-decoded bytes.
    pub fn verify_recursive_batch_proof(
        proof: &p3_circuit_prover::BatchStarkProof<PyanaRecursionConfig>,
    ) -> Result<(), String> {
        let config = create_recursion_config();
        let mut prover = BatchStarkProver::new(config);
        // Register the NPO table provers that were used to produce the recursive proof.
        // The verifier needs these to interpret the non-primitive ops in the proof.
        prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
        // split_coeff_tables = false because Poseidon2Config::D (4) == extension degree D (4)
        prover.register_recompose_table::<D>(false);
        prover
            .verify_all_tables(proof)
            .map_err(|e| format!("Recursive proof verification failed: {:?}", e))
    }

    /// Verify a recursive proof from postcard-serialised bytes.
    ///
    /// Convenience wrapper for the verifier side: decodes the
    /// `BatchStarkProof` then delegates to [`verify_recursive_batch_proof`].
    pub fn verify_recursive_layer_bytes(bytes: &[u8]) -> Result<(), String> {
        let proof: p3_circuit_prover::BatchStarkProof<PyanaRecursionConfig> =
            postcard::from_bytes(bytes)
                .map_err(|e| format!("Recursive proof postcard decode failed: {e}"))?;
        verify_recursive_batch_proof(&proof)
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

        /// Block 1 (Kimchi survey § 9.1 starter task): demonstrate that the
        /// recursion path is not bound to `P3MerklePoseidon2Air`. Take the
        /// smallest other `Air`-implementing AIR in the crate
        /// (`AggregationAir`, width 4, degree 1, 2 public inputs — the
        /// minimum-non-trivial shape we have) and run it through the same
        /// `prove_inner_for_air` / `prove_recursive_layer_for_air`
        /// machinery. If this passes, the blanket `RecursiveAir` impl in
        /// `p3-recursion` accepts a column count + constraint set that
        /// differ from the Merkle POC, which is the *mechanical
        /// generalization* the survey asked us to measure.
        ///
        /// Block 1 outcome: clean acceptance (no fork changes required) —
        /// the `RecursableAir` trait alias captures exactly the bounds the
        /// fork's blanket impl needs, and any AIR implementing the standard
        /// `p3-air::Air<AB>` family flows through unmodified.
        #[test]
        fn recursive_aggregation_air_smoke() {
            use crate::plonky3_recursion::AggregationAir;
            use p3_field::PrimeCharacteristicRing;
            use p3_matrix::dense::RowMajorMatrix;

            // Build a minimal aggregation trace by hand: 4 rows, width 4.
            // Row layout: [acc_in, leaf, root, acc_out].
            //
            // The AggregationAir constraints are:
            //   - first row: acc_in == pv[0]
            //   - last row: acc_out == pv[1]
            //   - transition: acc_out[i] == acc_in[i+1]
            //
            // We pick PI = [0, X] and a hand-rolled chain that satisfies the
            // transitions. The hash-chain computation is NOT enforced (this
            // is the recursion-shape smoke test, not the AggregationAir
            // soundness test — that lives in plonky3_recursion::tests).
            let pv0 = P3BabyBear::ZERO;
            let pv1 = P3BabyBear::from_u64(0xC0FFEE);
            let rows: Vec<[P3BabyBear; 4]> = vec![
                [
                    pv0,
                    P3BabyBear::from_u64(1),
                    P3BabyBear::from_u64(2),
                    P3BabyBear::from_u64(10),
                ],
                [
                    P3BabyBear::from_u64(10),
                    P3BabyBear::from_u64(3),
                    P3BabyBear::from_u64(4),
                    P3BabyBear::from_u64(20),
                ],
                [
                    P3BabyBear::from_u64(20),
                    P3BabyBear::from_u64(5),
                    P3BabyBear::from_u64(6),
                    P3BabyBear::from_u64(30),
                ],
                [
                    P3BabyBear::from_u64(30),
                    P3BabyBear::from_u64(7),
                    P3BabyBear::from_u64(8),
                    pv1,
                ],
            ];
            let flat: Vec<P3BabyBear> = rows.iter().flat_map(|r| r.iter().copied()).collect();
            let matrix = RowMajorMatrix::new(flat, 4);

            let pis_bb = vec![BabyBear::ZERO, BabyBear::new(0xC0FFEE)];

            let air = AggregationAir;

            // Inner proof generation through the generalized path.
            let inner = prove_inner_for_air(&air, matrix, &pis_bb);
            verify_inner_for_air(&air, &inner, &pis_bb)
                .expect("AggregationAir inner proof must verify");

            // Recursive layer through the generalized path.
            let rec = prove_recursive_layer_for_air(&air, &inner, &pis_bb)
                .expect("AggregationAir recursive layer must prove");
            verify_recursive_layer(&rec).expect("AggregationAir recursive layer must verify");
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
