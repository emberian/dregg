//! Comprehensive proof generation and verification benchmarks.
//!
//! Measures proving time, verification time, and proof size across all AIR circuits
//! and composed proof pipelines.
//!
//! Run with: `cargo bench -p dregg-circuit --bench proof_benchmarks`

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::dsl::verify_authorization_dsl;
use dregg_circuit::field::BabyBear;
use dregg_circuit::ivc::{
    FoldDelta, create_test_chain, prove_ivc, prove_ivc_stark, verify_ivc, verify_ivc_stark,
};
use dregg_circuit::multi_step_air::{
    MultiStepStarkAir, MultiStepWitness, build_multi_step_witness, prove_authorization_stark,
};
use dregg_circuit::note_spending_air::{
    NoteSpendingAir, NoteSpendingWitness, create_test_witness as create_note_witness,
    prove_note_spend, test_spending_key, verify_note_spend,
};
use dregg_circuit::poseidon2::{Poseidon2State, WIDTH, hash_4_to_1, hash_many};
use dregg_circuit::poseidon2_air::{
    MerklePoseidon2StarkAir, Poseidon2Air, generate_merkle_poseidon2_trace,
};
use dregg_circuit::stark::{
    self, MerkleStarkAir, StarkProof, generate_merkle_trace, proof_to_bytes,
};
use dregg_dsl_runtime::revocation::{
    DslRevocationTree, TREE_DEPTH as REVOCATION_TREE_DEPTH, prove_non_revocation_dsl,
    verify_non_revocation_dsl,
};

// =============================================================================
// 1. Individual AIR proving/verification
// =============================================================================

// -----------------------------------------------------------------------------
// 1a. Poseidon2 hash proof (2-row trace)
// -----------------------------------------------------------------------------

fn bench_poseidon2_stark_prove(c: &mut Criterion) {
    let mut group = c.benchmark_group("poseidon2_stark");

    let input: [BabyBear; WIDTH] = [
        BabyBear::new(1),
        BabyBear::new(2),
        BabyBear::new(3),
        BabyBear::new(4),
        BabyBear::new(5),
        BabyBear::new(6),
        BabyBear::new(7),
        BabyBear::new(8),
        BabyBear::new(9),
        BabyBear::new(10),
        BabyBear::new(11),
        BabyBear::new(12),
        BabyBear::new(13),
        BabyBear::new(14),
        BabyBear::new(15),
        BabyBear::new(16),
    ];
    let (trace, public_inputs) = Poseidon2Air::generate_trace(&input);
    let air = Poseidon2Air;

    group.bench_function("prove", |b| {
        b.iter(|| black_box(stark::prove(&air, &trace, &public_inputs)));
    });

    let proof = stark::prove(&air, &trace, &public_inputs);

    group.bench_function("verify", |b| {
        b.iter(|| black_box(stark::verify(&air, &proof, &public_inputs).unwrap()));
    });

    let proof_bytes = proof_to_bytes(&proof);
    eprintln!(
        "  [poseidon2_stark] proof size: {} bytes ({:.1} KiB)",
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0,
    );

    group.finish();
}

// -----------------------------------------------------------------------------
// 1b. Merkle membership proof (depth 4, 8, 16)
// -----------------------------------------------------------------------------

fn bench_merkle_membership(c: &mut Criterion) {
    let mut group = c.benchmark_group("merkle_membership");
    group.sample_size(10);

    for &depth in &[4, 8, 16] {
        let siblings: Vec<[u32; 3]> = (0..depth)
            .map(|i| {
                [
                    (i * 100 + 10) as u32,
                    (i * 100 + 20) as u32,
                    (i * 100 + 30) as u32,
                ]
            })
            .collect();
        let positions: Vec<u32> = (0..depth).map(|i| (i % 4) as u32).collect();
        let (trace, public_inputs) = generate_merkle_trace(12345, &siblings, &positions);
        let air = MerkleStarkAir;

        group.bench_with_input(
            BenchmarkId::new("prove", format!("d={depth}")),
            &(trace.clone(), public_inputs.clone()),
            |b, (trace, pi)| {
                b.iter(|| black_box(stark::prove(&air, trace, pi)));
            },
        );

        let proof = stark::prove(&air, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);

        group.bench_with_input(
            BenchmarkId::new("verify", format!("d={depth}")),
            &(proof.clone(), public_inputs.clone()),
            |b, (proof, pi)| {
                b.iter(|| black_box(stark::verify(&air, proof, pi).unwrap()));
            },
        );

        eprintln!(
            "  [merkle_membership d={depth}] proof size: {} bytes ({:.1} KiB)",
            proof_bytes.len(),
            proof_bytes.len() as f64 / 1024.0,
        );
    }

    group.finish();
}

// -----------------------------------------------------------------------------
// 1c. Note spending proof (full 19-column AIR)
// -----------------------------------------------------------------------------

fn bench_note_spending(c: &mut Criterion) {
    let mut group = c.benchmark_group("note_spending");
    group.sample_size(10);

    let key = test_spending_key(0xDEAD_BEEF);
    let witness = create_note_witness(
        BabyBear::new(1000),
        BabyBear::new(500),
        BabyBear::new(1),
        key,
        4,
    );
    let nullifier = witness.nullifier();
    let merkle_root = witness.merkle_root();

    group.bench_function("prove_d4", |b| {
        b.iter(|| black_box(prove_note_spend(&witness)));
    });

    let proof = prove_note_spend(&witness);
    let proof_bytes = proof_to_bytes(&proof);

    group.bench_function("verify_d4", |b| {
        b.iter(|| {
            black_box(
                verify_note_spend(
                    nullifier,
                    merkle_root,
                    witness.value,
                    witness.asset_type,
                    &proof,
                )
                .unwrap(),
            )
        });
    });

    eprintln!(
        "  [note_spending d=4] proof size: {} bytes ({:.1} KiB)",
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0,
    );

    // Depth 8
    let witness8 = create_note_witness(
        BabyBear::new(1000),
        BabyBear::new(500),
        BabyBear::new(1),
        key,
        8,
    );
    let null8 = witness8.nullifier();
    let root8 = witness8.merkle_root();

    group.bench_function("prove_d8", |b| {
        b.iter(|| black_box(prove_note_spend(&witness8)));
    });

    let proof8 = prove_note_spend(&witness8);
    let proof_bytes8 = proof_to_bytes(&proof8);

    group.bench_function("verify_d8", |b| {
        b.iter(|| {
            black_box(
                verify_note_spend(null8, root8, witness8.value, witness8.asset_type, &proof8)
                    .unwrap(),
            )
        });
    });

    eprintln!(
        "  [note_spending d=8] proof size: {} bytes ({:.1} KiB)",
        proof_bytes8.len(),
        proof_bytes8.len() as f64 / 1024.0,
    );

    group.finish();
}

// -----------------------------------------------------------------------------
// 1d. Multi-step derivation (1, 8, 32 steps)
// -----------------------------------------------------------------------------

fn make_derivation_step(
    step_idx: u32,
    state_root: BabyBear,
    is_final: bool,
) -> dregg_circuit::derivation_air::DerivationWitness {
    use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
    use dregg_circuit::poseidon2::hash_fact;

    let pred = if is_final {
        BabyBear::new(dregg_circuit::multi_step_air::ALLOW_PREDICATE)
    } else {
        BabyBear::new(step_idx * 100 + 1)
    };
    let terms = [
        BabyBear::new(step_idx * 100 + 2),
        BabyBear::new(step_idx * 100 + 3),
        BabyBear::new(step_idx * 100 + 4),
        BabyBear::new(step_idx * 100 + 5),
    ];
    let body_pred = BabyBear::new(step_idx * 100 + 10);
    let body_terms = [
        BabyBear::new(step_idx * 100 + 2),
        BabyBear::new(step_idx * 100 + 3),
        BabyBear::new(step_idx * 100 + 4),
    ];
    let body_hash = hash_fact(body_pred, &body_terms);

    DerivationWitness {
        rule: CircuitRule {
            id: step_idx,
            num_body_atoms: 1,
            num_variables: 1,
            head_predicate: pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, terms[1]),
                (false, terms[2]),
                (false, terms[3]),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: body_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (false, body_terms[1]),
                    (false, body_terms[2]),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root,
        body_fact_hashes: vec![body_hash],
        substitution: vec![terms[0]],
        derived_predicate: pred,
        derived_terms: terms,
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    }
}

fn build_test_multi_step_witness(num_steps: usize) -> MultiStepWitness {
    let state_root = BabyBear::new(0x1234_5678);
    let request_hash = BabyBear::new(0xABCD_0001);
    let steps: Vec<_> = (0..num_steps)
        .map(|i| make_derivation_step(i as u32, state_root, i == num_steps - 1))
        .collect();
    build_multi_step_witness(state_root, request_hash, steps)
}

fn bench_multi_step_derivation(c: &mut Criterion) {
    let mut group = c.benchmark_group("multi_step_derivation");
    group.sample_size(10);

    for &steps in &[1, 8, 32] {
        let witness = build_test_multi_step_witness(steps);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        group.bench_with_input(
            BenchmarkId::new("prove", format!("{steps}_steps")),
            &witness,
            |b, w| {
                b.iter(|| black_box(prove_authorization_stark(w)));
            },
        );

        let proof = prove_authorization_stark(&witness);
        let proof_bytes = proof_to_bytes(&proof);

        group.bench_with_input(
            BenchmarkId::new("verify", format!("{steps}_steps")),
            &(proof.clone(), conclusion, acc_hash),
            |b, (p, conc, ah)| {
                b.iter(|| black_box(verify_authorization_dsl(*conc, *ah, p).unwrap()));
            },
        );

        eprintln!(
            "  [multi_step {steps} steps] proof size: {} bytes ({:.1} KiB)",
            proof_bytes.len(),
            proof_bytes.len() as f64 / 1024.0,
        );
    }

    group.finish();
}

// -----------------------------------------------------------------------------
// 1e. State transition IVC (1, 5, 20 steps)
// -----------------------------------------------------------------------------

fn bench_state_transition_ivc(c: &mut Criterion) {
    let mut group = c.benchmark_group("state_transition_ivc");
    group.sample_size(10);

    for &steps in &[1, 5, 20] {
        let (initial_root, deltas) = create_test_chain(steps);

        group.bench_with_input(
            BenchmarkId::new("prove", format!("{steps}_steps")),
            &(initial_root, deltas.clone()),
            |b, (root, ds)| {
                b.iter(|| black_box(prove_ivc(*root, ds.clone()).unwrap()));
            },
        );

        let proof = prove_ivc(initial_root, deltas.clone()).unwrap();

        group.bench_with_input(
            BenchmarkId::new("verify", format!("{steps}_steps")),
            &(proof.clone(), initial_root),
            |b, (p, root)| {
                b.iter(|| black_box(verify_ivc(p, Some(*root))));
            },
        );

        eprintln!(
            "  [ivc {steps} steps] proof size: {} bytes ({:.1} KiB)",
            proof.proof_size_bytes(),
            proof.proof_size_bytes() as f64 / 1024.0,
        );
    }

    // Also bench the STARK-based IVC prove/verify
    for &steps in &[1, 5, 20] {
        let (initial_root, deltas) = create_test_chain(steps);
        let new_roots: Vec<BabyBear> = deltas.iter().map(|d| d.fold.new_root).collect();

        group.bench_with_input(
            BenchmarkId::new("stark_prove", format!("{steps}_steps")),
            &(initial_root, new_roots.clone()),
            |b, (root, roots)| {
                b.iter(|| black_box(prove_ivc_stark(*root, roots)));
            },
        );

        let (stark_proof, pub_inputs) = prove_ivc_stark(initial_root, &new_roots);

        group.bench_with_input(
            BenchmarkId::new("stark_verify", format!("{steps}_steps")),
            &(stark_proof.clone(), pub_inputs.clone()),
            |b, (sp, pi)| {
                b.iter(|| black_box(verify_ivc_stark(sp, pi).unwrap()));
            },
        );

        let sp_bytes = proof_to_bytes(&stark_proof);
        eprintln!(
            "  [ivc_stark {steps} steps] proof size: {} bytes ({:.1} KiB)",
            sp_bytes.len(),
            sp_bytes.len() as f64 / 1024.0,
        );
    }

    group.finish();
}

// -----------------------------------------------------------------------------
// 1f. Non-revocation proof (1, 4, 8 ancestors)
// -----------------------------------------------------------------------------

fn make_revocation_hash(seed: u32) -> BabyBear {
    hash_many(&[BabyBear::new(seed), BabyBear::new(0xDEAD)])
}

fn build_test_revocation_tree(num_revoked: usize) -> DslRevocationTree {
    let hashes: Vec<BabyBear> = (1..=num_revoked as u32)
        .map(|i| make_revocation_hash(i * 100))
        .collect();
    DslRevocationTree::new(hashes, REVOCATION_TREE_DEPTH)
}

fn bench_non_revocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("non_revocation");
    group.sample_size(10);

    // Build a tree with 20 revoked entries (enough to test non-membership)
    let tree = build_test_revocation_tree(20);
    let revocation_root = tree.root();

    for &num_ancestors in &[1, 4, 8] {
        // Create ancestor hashes that are NOT in the tree
        let ancestor_hashes: Vec<BabyBear> = (0..num_ancestors)
            .map(|i| hash_many(&[BabyBear::new(0xBEEF_0000 + i as u32), BabyBear::new(0xCAFE)]))
            .collect();

        // DSL circuit proves one ancestor at a time; bench the first one
        let first_hash = ancestor_hashes[0];
        group.bench_with_input(
            BenchmarkId::new("prove", format!("{num_ancestors}_ancestors")),
            &(first_hash, &tree),
            |b, (hash, t)| {
                b.iter(|| black_box(prove_non_revocation_dsl(t, *hash).unwrap()));
            },
        );

        let proof = prove_non_revocation_dsl(&tree, first_hash).unwrap();
        let proof_bytes = proof_to_bytes(&proof);

        group.bench_with_input(
            BenchmarkId::new("verify", format!("{num_ancestors}_ancestors")),
            &(revocation_root, first_hash, proof.clone()),
            |b, (root, hash, p)| {
                b.iter(|| black_box(verify_non_revocation_dsl(p, *root, *hash).unwrap()));
            },
        );

        eprintln!(
            "  [non_revocation {num_ancestors} ancestors] proof size: {} bytes ({:.1} KiB)",
            proof_bytes.len(),
            proof_bytes.len() as f64 / 1024.0,
        );
    }

    group.finish();
}

// =============================================================================
// 2. Composed proofs
// =============================================================================

// -----------------------------------------------------------------------------
// 2a. BodyMembershipProof (derivation + membership proofs)
// -----------------------------------------------------------------------------

fn bench_body_membership_proof(c: &mut Criterion) {
    use dregg_circuit::body_membership::{
        BodyFactMerkleProof, collect_body_fact_hashes, prove_authorization_with_membership,
        verify_authorization_with_membership,
    };

    let mut group = c.benchmark_group("body_membership_composed");
    group.sample_size(10);

    // Build a witness with 4 derivation steps
    let witness = build_test_multi_step_witness(4);
    let conclusion = witness.conclusion();
    let acc_hash = witness.final_accumulated_hash();

    // Create mock Merkle proofs for body facts (depth 4)
    let body_hashes = collect_body_fact_hashes(&witness);
    let body_proofs: Vec<BodyFactMerkleProof> = body_hashes
        .iter()
        .map(|&hash| {
            let siblings: Vec<[BabyBear; 3]> = (0..4)
                .map(|i| {
                    [
                        hash_many(&[hash, BabyBear::new(i * 3 + 1)]),
                        hash_many(&[hash, BabyBear::new(i * 3 + 2)]),
                        hash_many(&[hash, BabyBear::new(i * 3 + 3)]),
                    ]
                })
                .collect();
            let positions = vec![0u8, 1, 2, 3];
            BodyFactMerkleProof {
                fact_hash: hash,
                siblings,
                positions,
            }
        })
        .collect();

    group.bench_function("prove_4_steps", |b| {
        b.iter(|| black_box(prove_authorization_with_membership(&witness, &body_proofs)));
    });

    let composed = prove_authorization_with_membership(&witness, &body_proofs);

    group.bench_function("verify_4_steps", |b| {
        b.iter(|| {
            black_box(
                verify_authorization_with_membership(&composed, conclusion, acc_hash, &body_hashes)
                    .unwrap(),
            )
        });
    });

    // Compute total proof size
    let derivation_size = proof_to_bytes(&composed.derivation_proof).len();
    let membership_size: usize = composed
        .membership_proofs
        .iter()
        .map(|m| proof_to_bytes(&m.proof).len())
        .sum();
    let total_size = derivation_size + membership_size;
    eprintln!(
        "  [body_membership 4 steps] total proof size: {} bytes ({:.1} KiB) \
         (derivation: {:.1} KiB, {} membership proofs: {:.1} KiB)",
        total_size,
        total_size as f64 / 1024.0,
        derivation_size as f64 / 1024.0,
        composed.membership_proofs.len(),
        membership_size as f64 / 1024.0,
    );

    group.finish();
}

// -----------------------------------------------------------------------------
// 2b. ChunkedAuthorizationProof (2, 4 chunks)
// -----------------------------------------------------------------------------

fn bench_chunked_authorization(c: &mut Criterion) {
    use dregg_circuit::chunked_derivation::{
        prove_chunked_authorization, verify_chunked_authorization,
    };

    let mut group = c.benchmark_group("chunked_authorization");
    group.sample_size(10);

    for &(total_steps, chunk_size, label) in &[(4usize, 2usize, "2_chunks"), (8, 2, "4_chunks")] {
        let witness = build_test_multi_step_witness(total_steps);
        let conclusion = witness.conclusion();
        let state_root = witness.initial_state_root;

        group.bench_with_input(
            BenchmarkId::new("prove", label),
            &(witness.clone(), chunk_size),
            |b, (w, cs)| {
                b.iter(|| black_box(prove_chunked_authorization(w, *cs)));
            },
        );

        let proof = prove_chunked_authorization(&witness, chunk_size);

        group.bench_with_input(
            BenchmarkId::new("verify", label),
            &(proof.clone(), conclusion, state_root),
            |b, (p, conc, sr)| {
                b.iter(|| black_box(verify_chunked_authorization(p, *conc, *sr).unwrap()));
            },
        );

        let total_size: usize = proof
            .chunk_proofs
            .iter()
            .map(|p| proof_to_bytes(p).len())
            .sum();
        eprintln!(
            "  [chunked {label}] total proof size: {} bytes ({:.1} KiB), {} chunks",
            total_size,
            total_size as f64 / 1024.0,
            proof.chunk_proofs.len(),
        );
    }

    group.finish();
}

// =============================================================================
// 3. Non-proof operations (for context)
// =============================================================================

fn bench_primitive_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("primitives");

    // Poseidon2 single hash
    let input = [
        BabyBear::new(1),
        BabyBear::new(2),
        BabyBear::new(3),
        BabyBear::new(4),
    ];
    group.bench_function("poseidon2_hash_4_to_1", |b| {
        b.iter(|| black_box(hash_4_to_1(&input)));
    });

    // Poseidon2 permutation
    group.bench_function("poseidon2_permutation", |b| {
        let mut state = Poseidon2State::from_elements(&[
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ]);
        b.iter(|| {
            state.permute();
            black_box(&state);
        });
    });

    // BabyBear field inverse
    let a = BabyBear::new(1_234_567_890);
    group.bench_function("babybear_inverse", |b| {
        b.iter(|| black_box(a.inverse()));
    });

    // BabyBear multiplication
    let bb = BabyBear::new(987_654_321);
    group.bench_function("babybear_mul", |b| {
        b.iter(|| black_box(a * bb));
    });

    group.finish();
}

// =============================================================================
// 4. Pipeline end-to-end (single-iteration for size context)
// =============================================================================

fn bench_full_authorization_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("full_pipeline");
    group.sample_size(10);

    // Full authorization pipeline: build witness -> prove STARK -> serialize -> deserialize -> verify
    let witness = build_test_multi_step_witness(8);
    let conclusion = witness.conclusion();
    let acc_hash = witness.final_accumulated_hash();

    group.bench_function("prove_serialize_deserialize_verify_8step", |b| {
        b.iter(|| {
            // Prove
            let proof = prove_authorization_stark(&witness);
            // Serialize
            let bytes = proof_to_bytes(&proof);
            // Deserialize
            let proof2 = stark::proof_from_bytes(&bytes).unwrap();
            // Verify
            let result = verify_authorization_dsl(conclusion, acc_hash, &proof2);
            black_box(result.unwrap());
        });
    });

    // Measure each phase independently
    group.bench_function("prove_8step", |b| {
        b.iter(|| black_box(prove_authorization_stark(&witness)));
    });

    let proof = prove_authorization_stark(&witness);
    let bytes = proof_to_bytes(&proof);

    group.bench_function("serialize_8step", |b| {
        b.iter(|| black_box(proof_to_bytes(&proof)));
    });

    group.bench_function("deserialize_8step", |b| {
        b.iter(|| black_box(stark::proof_from_bytes(&bytes).unwrap()));
    });

    group.bench_function("verify_8step", |b| {
        b.iter(|| black_box(verify_authorization_dsl(conclusion, acc_hash, &proof).unwrap()));
    });

    eprintln!(
        "  [full_pipeline 8-step] proof size: {} bytes ({:.1} KiB)",
        bytes.len(),
        bytes.len() as f64 / 1024.0,
    );

    group.finish();
}

// =============================================================================
// 5. Plonky3 backend (feature-gated)
// =============================================================================

#[cfg(feature = "plonky3")]
fn bench_plonky3_backend(c: &mut Criterion) {
    use dregg_circuit::plonky3_prover::{prove_membership_plonky3, prove_plonky3, verify_plonky3};
    use dregg_circuit::poseidon2_air::{
        create_poseidon2_test_witness, generate_merkle_poseidon2_trace,
    };

    let mut group = c.benchmark_group("plonky3_backend");
    group.sample_size(10);

    // Merkle membership (depth 4) via Plonky3
    for &depth in &[4usize, 8] {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, depth);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        group.bench_with_input(
            BenchmarkId::new("prove_merkle", format!("d={depth}")),
            &(trace.clone(), public_inputs.clone()),
            |b, (t, pi)| {
                b.iter(|| black_box(prove_plonky3(t, pi)));
            },
        );

        let proof = prove_plonky3(&trace, &public_inputs);

        group.bench_with_input(
            BenchmarkId::new("verify_merkle", format!("d={depth}")),
            &public_inputs,
            |b, pi| {
                b.iter(|| black_box(verify_plonky3(&proof, pi).unwrap()));
            },
        );

        // Compare: custom STARK vs Plonky3 for same statement
        let custom_proof = {
            let air = dregg_circuit::poseidon2_air::MerklePoseidon2StarkAir;
            stark::prove(&air, &trace, &public_inputs)
        };
        let custom_size = proof_to_bytes(&custom_proof).len();
        eprintln!(
            "  [plonky3 d={depth}] custom STARK: {:.1} KiB | Plonky3: (opaque proof object)",
            custom_size as f64 / 1024.0,
        );
    }

    group.finish();
}

// =============================================================================
// 6. Pickles/Mina backend (feature-gated)
// =============================================================================

#[cfg(feature = "mina")]
fn bench_pickles_backend(c: &mut Criterion) {
    let mut group = c.benchmark_group("pickles_backend");
    group.sample_size(10);

    // The Mina/Kimchi backend uses recursive SNARK verification (Pickles protocol).
    // We bench IVC proof generation + verification which exercises the recursive path.
    // With the mina feature, the IVC proof can use Pasta curve IPA commitments
    // for constant-size proofs regardless of chain length.

    // Single recursive step
    let (initial_root, deltas) = create_test_chain(1);
    let new_roots_1: Vec<BabyBear> = deltas.iter().map(|d| d.fold.new_root).collect();

    group.bench_function("recursive_1_step", |b| {
        b.iter(|| {
            let (sp, pi) = prove_ivc_stark(initial_root, &new_roots_1);
            black_box(verify_ivc_stark(&sp, &pi).unwrap());
        });
    });

    // 3-step recursive chain
    let (root3, deltas3) = create_test_chain(3);
    let new_roots_3: Vec<BabyBear> = deltas3.iter().map(|d| d.fold.new_root).collect();

    group.bench_function("recursive_3_step", |b| {
        b.iter(|| {
            let (sp, pi) = prove_ivc_stark(root3, &new_roots_3);
            black_box(verify_ivc_stark(&sp, &pi).unwrap());
        });
    });

    // Compare: constant proof size across chain lengths
    for &steps in &[1, 3, 5] {
        let (root, ds) = create_test_chain(steps);
        let roots: Vec<BabyBear> = ds.iter().map(|d| d.fold.new_root).collect();
        let (sp, _) = prove_ivc_stark(root, &roots);
        let size = proof_to_bytes(&sp).len();
        eprintln!(
            "  [pickles {steps}-step] proof size: {:.1} KiB (should be ~constant)",
            size as f64 / 1024.0
        );
    }

    group.finish();
}

// =============================================================================
// Criterion configuration
// =============================================================================

criterion_group!(
    individual_proofs,
    bench_poseidon2_stark_prove,
    bench_merkle_membership,
    bench_note_spending,
    bench_multi_step_derivation,
    bench_state_transition_ivc,
    bench_non_revocation,
);

criterion_group!(
    composed_proofs,
    bench_body_membership_proof,
    bench_chunked_authorization,
);

criterion_group!(
    context_and_pipeline,
    bench_primitive_operations,
    bench_full_authorization_pipeline,
);

#[cfg(feature = "plonky3")]
criterion_group!(plonky3_benches, bench_plonky3_backend);

#[cfg(feature = "mina")]
criterion_group!(pickles_benches, bench_pickles_backend);

// Main: include feature-gated groups only when enabled
#[cfg(all(not(feature = "plonky3"), not(feature = "mina")))]
criterion_main!(individual_proofs, composed_proofs, context_and_pipeline);

#[cfg(all(feature = "plonky3", not(feature = "mina")))]
criterion_main!(
    individual_proofs,
    composed_proofs,
    context_and_pipeline,
    plonky3_benches
);

#[cfg(all(not(feature = "plonky3"), feature = "mina"))]
criterion_main!(
    individual_proofs,
    composed_proofs,
    context_and_pipeline,
    pickles_benches
);

#[cfg(all(feature = "plonky3", feature = "mina"))]
criterion_main!(
    individual_proofs,
    composed_proofs,
    context_and_pipeline,
    plonky3_benches,
    pickles_benches
);
