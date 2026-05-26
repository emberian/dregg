//! Practical use-case benchmarks for dregg.
//!
//! These measure the real-world operations that users actually perform:
//! token operations, proof generation, proof verification, recursive composition,
//! federation operations, and the full end-to-end flow.
//!
//! Run with: `cargo bench -p dregg-circuit --bench practical_benchmarks`

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};

use dregg_bridge::present::{
    BridgePresentationBuilder, bytes_to_babybear, hash_index, verify_presentation_bb,
    verify_presentation_complete,
};
use dregg_circuit::dsl::verify_authorization_dsl;
use dregg_circuit::field::BabyBear;
use dregg_circuit::ivc::{create_test_chain, prove_ivc_stark, verify_ivc_stark};
use dregg_circuit::multi_step_air::{
    ALLOW_PREDICATE, MultiStepWitness, build_multi_step_witness, prove_authorization_stark,
};
use dregg_circuit::poseidon2;
use dregg_circuit::stark::{proof_from_bytes, proof_to_bytes};
use dregg_dsl_runtime::revocation::{
    DslRevocationTree, TREE_DEPTH as REVOCATION_TREE_DEPTH, prove_non_revocation_dsl,
    verify_non_revocation_dsl,
};
use dregg_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};

// =============================================================================
// Helpers
// =============================================================================

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("dregg-practical-bench:{name}").as_bytes()).as_bytes()
}

/// Compute federation root matching the synthetic Poseidon2 Merkle path for a key.
fn compute_federation_root(key: &[u8; 32]) -> (BabyBear, [u8; 32]) {
    let issuer_hash = bytes_to_babybear(key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(hash_index(i, 0, key)),
            BabyBear::new(hash_index(i, 1, key)),
            BabyBear::new(hash_index(i, 2, key)),
        ];
        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j == position {
                children[j as usize] = current;
            } else {
                children[j as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }
        current = poseidon2::hash_4_to_1(&children);
    }
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&current.0.to_le_bytes());
    (current, bytes)
}

fn make_builder(
    key: &[u8; 32],
    num_attenuations: usize,
) -> (BridgePresentationBuilder, AuthRequest) {
    let (fed_root_bb, fed_root_bytes) = compute_federation_root(key);
    let mut builder =
        BridgePresentationBuilder::new_with_root_bb(*key, fed_root_bytes, fed_root_bb);
    let token = MacaroonToken::mint(*key, b"bench-kid", "dregg.dev");
    builder.set_root_token(token);

    for i in 0..num_attenuations {
        let att = Attenuation {
            apps: vec![(format!("app-{i}"), "rw".into())],
            not_after: Some(2000000000),
            ..Default::default()
        };
        builder.add_attenuation(&att);
    }

    let request = AuthRequest {
        app_id: Some("app-0".into()),
        action: Some("r".into()),
        ..Default::default()
    };

    (builder, request)
}

// =============================================================================
// 1. Token Operations (the fast path -- no ZK)
// =============================================================================

fn bench_token_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("1_token_ops");

    // --- mint_token ---
    let key = test_key("mint");
    group.bench_function("mint_token", |b| {
        b.iter(|| {
            black_box(MacaroonToken::mint(key, b"kid-bench", "dregg.dev"));
        });
    });

    // --- attenuate ---
    let token = MacaroonToken::mint(key, b"kid-bench", "dregg.dev");
    let attenuation = Attenuation {
        apps: vec![("my-app".into(), "rw".into())],
        not_after: Some(2000000000),
        ..Default::default()
    };
    group.bench_function("attenuate", |b| {
        b.iter(|| {
            black_box(token.attenuate(&attenuation).unwrap());
        });
    });

    // --- verify_token (HMAC check, no ZK) ---
    let attenuated = token.attenuate(&attenuation).unwrap();
    let request = AuthRequest {
        app_id: Some("my-app".into()),
        action: Some("r".into()),
        ..Default::default()
    };
    group.bench_function("verify_token_hmac", |b| {
        b.iter(|| {
            black_box(attenuated.verify(&request).unwrap());
        });
    });

    // Verify with deeper caveat chains
    for &depth in &[5, 10, 20] {
        let root = MacaroonToken::mint(key, b"kid-chain", "dregg.dev");
        let mut tok: Box<dyn AuthToken> = Box::new(root);
        for i in 0..depth {
            let att = Attenuation {
                apps: vec![(format!("app-{i}"), "r".into())],
                ..Default::default()
            };
            tok = tok.attenuate(&att).unwrap();
        }
        // Request must match at least one of the caveats
        let req = AuthRequest {
            app_id: Some("app-0".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        group.bench_with_input(
            BenchmarkId::new("verify_hmac_chain", depth),
            &depth,
            |b, _| {
                b.iter(|| black_box(tok.verify(&req).unwrap()));
            },
        );
    }

    group.finish();
}

// =============================================================================
// 2. Proof Generation (the ZK path)
// =============================================================================

fn bench_proof_generation(c: &mut Criterion) {
    let mut group = c.benchmark_group("2_proof_generation");
    group.sample_size(10);

    let key = test_key("prove");

    // --- Full private authorization (end-to-end: token -> wire proof bytes) ---
    // This is cclerk.authorize(FullyPrivate) equivalent
    group.bench_function("authorize_private_1_caveat", |b| {
        b.iter(|| {
            let (mut builder, request) = make_builder(&key, 1);
            black_box(builder.prove(&request).unwrap());
        });
    });

    // --- Break it down: Datalog eval vs STARK generation vs serialization ---

    // Datalog evaluation only (no STARK)
    group.bench_function("datalog_eval_only_1_caveat", |b| {
        b.iter(|| {
            let (mut builder, request) = make_builder(&key, 1);
            let marker =
                dregg_bridge::UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound();
            black_box(
                builder
                    .prove_local_constraint_check_only(&marker, &request)
                    .unwrap(),
            );
        });
    });

    // --- Scale with caveats: 1 vs 5 vs 10 ---
    for &num_caveats in &[1, 5, 10] {
        group.bench_with_input(
            BenchmarkId::new("authorize_private", format!("{num_caveats}_caveats")),
            &num_caveats,
            |b, &n| {
                b.iter(|| {
                    let (mut builder, request) = make_builder(&key, n);
                    black_box(builder.prove(&request).unwrap());
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("datalog_eval_only", format!("{num_caveats}_caveats")),
            &num_caveats,
            |b, &n| {
                b.iter(|| {
                    let (mut builder, request) = make_builder(&key, n);
                    let marker = dregg_bridge::UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound();
                    black_box(
                        builder
                            .prove_local_constraint_check_only(&marker, &request)
                            .unwrap(),
                    );
                });
            },
        );
    }

    // Report proof sizes
    for &num_caveats in &[1, 5, 10] {
        let (mut builder, request) = make_builder(&key, num_caveats);
        let proof = builder.prove(&request).unwrap();
        let wire = proof.into_wire_proof();
        let wire_bytes = rmp_serde::to_vec(&wire).unwrap();
        eprintln!(
            "  [proof_gen {num_caveats} caveats] wire proof size: {} bytes ({:.1} KiB)",
            wire_bytes.len(),
            wire_bytes.len() as f64 / 1024.0
        );
    }

    group.finish();
}

// =============================================================================
// 3. Proof Verification
// =============================================================================

fn bench_proof_verification(c: &mut Criterion) {
    let mut group = c.benchmark_group("3_proof_verification");
    group.sample_size(10);

    let key = test_key("verify");
    let (fed_root_bb, fed_root_bytes) = compute_federation_root(&key);

    // Generate a real proof to verify
    let (mut builder, request) = make_builder(&key, 1);
    let proof = builder.prove(&request).unwrap();

    // --- verify_presentation (STARK verification of issuer membership) ---
    group.bench_function("verify_presentation_stark", |b| {
        b.iter(|| {
            black_box(verify_presentation_bb(&proof, fed_root_bb));
        });
    });

    // --- verify_presentation_complete (full verification incl fold chain) ---
    group.bench_function("verify_presentation_complete", |b| {
        b.iter(|| {
            black_box(verify_presentation_complete(&proof, &fed_root_bytes));
        });
    });

    // --- Serialization round-trip: serialize + deserialize ---
    let wire = proof.clone().into_wire_proof();
    let wire_bytes = rmp_serde::to_vec(&wire).unwrap();
    eprintln!(
        "  [verify] wire proof size: {} bytes ({:.1} KiB)",
        wire_bytes.len(),
        wire_bytes.len() as f64 / 1024.0
    );

    group.bench_function("serialize_wire_proof", |b| {
        b.iter(|| {
            black_box(rmp_serde::to_vec(&wire).unwrap());
        });
    });

    group.bench_function("deserialize_wire_proof", |b| {
        b.iter(|| {
            black_box(
                rmp_serde::from_slice::<dregg_bridge::WirePresentationProof>(&wire_bytes).unwrap(),
            );
        });
    });

    // --- Multi-step derivation STARK verify (the inner STARK) ---
    {
        let witness = build_test_multi_step_witness(4);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();
        let stark_proof = prove_authorization_stark(&witness);
        let proof_bytes = proof_to_bytes(&stark_proof);
        eprintln!(
            "  [verify] derivation STARK (4-step) size: {} bytes ({:.1} KiB)",
            proof_bytes.len(),
            proof_bytes.len() as f64 / 1024.0
        );

        group.bench_function("verify_derivation_stark_4step", |b| {
            b.iter(|| {
                black_box(verify_authorization_dsl(conclusion, acc_hash, &stark_proof).unwrap());
            });
        });

        group.bench_function("deserialize_derivation_stark", |b| {
            b.iter(|| {
                black_box(proof_from_bytes(&proof_bytes).unwrap());
            });
        });
    }

    group.finish();
}

// =============================================================================
// 4. Recursive Composition (Kimchi/Pickles + IVC STARK)
// =============================================================================

#[cfg(feature = "mina")]
fn bench_recursive_composition(c: &mut Criterion) {
    use dregg_circuit::backends::mina::{
        PicklesRecursiveProof, PicklesStateTransition, prove_recursive_step, verify_recursive_proof,
    };

    let mut group = c.benchmark_group("4_recursive_pickles");
    group.sample_size(10);

    // --- prove_recursive_step: base case (no previous proof) ---
    let transition_1 = PicklesStateTransition {
        pre_state_hash: *blake3::hash(b"state-0").as_bytes(),
        post_state_hash: *blake3::hash(b"state-1").as_bytes(),
    };

    group.bench_function("prove_recursive_step_base", |b| {
        b.iter(|| {
            black_box(prove_recursive_step(None, &transition_1).unwrap());
        });
    });

    let base_proof = prove_recursive_step(None, &transition_1).unwrap();

    // --- prove_recursive_step: recursive (with previous proof) ---
    let transition_2 = PicklesStateTransition {
        pre_state_hash: *blake3::hash(b"state-1").as_bytes(),
        post_state_hash: *blake3::hash(b"state-2").as_bytes(),
    };

    group.bench_function("prove_recursive_step_recursive", |b| {
        b.iter(|| {
            black_box(prove_recursive_step(Some(&base_proof), &transition_2).unwrap());
        });
    });

    // --- verify_recursive_proof: should be constant regardless of chain length ---
    group.bench_function("verify_recursive_proof_1step", |b| {
        b.iter(|| {
            black_box(verify_recursive_proof(&base_proof, None).unwrap());
        });
    });

    let step2_proof = prove_recursive_step(Some(&base_proof), &transition_2).unwrap();
    group.bench_function("verify_recursive_proof_2step", |b| {
        b.iter(|| {
            black_box(verify_recursive_proof(&step2_proof, None).unwrap());
        });
    });

    // Build a 5-step chain and verify (demonstrating constant verification time)
    let mut prev: Option<PicklesRecursiveProof> = None;
    for step in 0..5 {
        let t = PicklesStateTransition {
            pre_state_hash: *blake3::hash(format!("state-{step}").as_bytes()).as_bytes(),
            post_state_hash: *blake3::hash(format!("state-{}", step + 1).as_bytes()).as_bytes(),
        };
        let p = prove_recursive_step(prev.as_ref(), &t).unwrap();
        let proof_size = p.public_inputs.len() + p.proof_bytes.len();
        eprintln!(
            "  [pickles] chain_length={} proof_size={} bytes (should be ~constant)",
            step + 1,
            proof_size
        );
        prev = Some(p);
    }

    let final_proof = prev.unwrap();
    group.bench_function("verify_recursive_proof_5step", |b| {
        b.iter(|| {
            black_box(verify_recursive_proof(&final_proof, None).unwrap());
        });
    });

    group.finish();
}

fn bench_ivc_stark(c: &mut Criterion) {
    let mut group = c.benchmark_group("4_ivc_stark");
    group.sample_size(10);

    // IVC prove/verify via STARK (the main recursion path)
    for &steps in &[1, 3, 5, 10] {
        let (initial_root, deltas) = create_test_chain(steps);
        let new_roots: Vec<BabyBear> = deltas.iter().map(|d| d.fold.new_root).collect();

        group.bench_with_input(
            BenchmarkId::new("prove", format!("{steps}_steps")),
            &(initial_root, new_roots.clone()),
            |b, (root, roots)| {
                b.iter(|| black_box(prove_ivc_stark(*root, roots)));
            },
        );

        let (stark_proof, pub_inputs) = prove_ivc_stark(initial_root, &new_roots);
        let sp_bytes = proof_to_bytes(&stark_proof);
        eprintln!(
            "  [ivc_stark {steps}-step] proof size: {} bytes ({:.1} KiB)",
            sp_bytes.len(),
            sp_bytes.len() as f64 / 1024.0
        );

        group.bench_with_input(
            BenchmarkId::new("verify", format!("{steps}_steps")),
            &(stark_proof.clone(), pub_inputs.clone()),
            |b, (sp, pi)| {
                b.iter(|| black_box(verify_ivc_stark(sp, pi).unwrap()));
            },
        );
    }

    group.finish();
}

// =============================================================================
// 5. Federation Operations
// =============================================================================

fn bench_federation_ops(c: &mut Criterion) {
    use dregg_circuit::poseidon2::hash_many;

    let mut group = c.benchmark_group("5_federation_ops");
    group.sample_size(10);

    // --- Turn execution: simple transfer ---
    {
        use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
        use dregg_turn::builder::ActionBuilder;
        use dregg_turn::{ComputronCosts, TurnBuilder, TurnExecutor};

        let costs = ComputronCosts::zero();
        let executor = TurnExecutor::new(costs);

        // Set up a minimal ledger with two cells (open permissions)
        let mut ledger = Ledger::new();
        let sender_pk = [1u8; 32];
        let receiver_pk = [2u8; 32];
        let token_id = [0u8; 32];

        let mut sender = Cell::with_balance(sender_pk, token_id, 100_000);
        sender.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        let sender_id = sender.id();

        let mut receiver = Cell::with_balance(receiver_pk, token_id, 0);
        receiver.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        let receiver_id = receiver.id();

        // Grant capability so sender can act on receiver
        sender.capabilities.grant(receiver_id, AuthRequired::None);

        ledger.insert_cell(sender).unwrap();
        ledger.insert_cell(receiver).unwrap();

        // Build a simple transfer turn
        let mut tb = TurnBuilder::new(sender_id, 0);
        let action = ActionBuilder::new_unchecked_for_tests(sender_id, "transfer", sender_id)
            .effect_transfer(sender_id, receiver_id, 100)
            .build();
        tb.add_action(action);
        let turn = tb.build();

        group.bench_function("turn_execute_transfer", |b| {
            b.iter_batched(
                || ledger.clone(),
                |mut l| {
                    black_box(executor.execute(&turn, &mut l));
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }

    // --- Revocation: prove non-revocation (DSL circuit, ZK path) ---
    {
        let tree = {
            let hashes: Vec<BabyBear> = (1..=20u32)
                .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xDEAD)]))
                .collect();
            DslRevocationTree::new(hashes, REVOCATION_TREE_DEPTH)
        };
        let revocation_root = tree.root();

        for &num_ancestors in &[1, 4, 8] {
            let ancestor_hashes: Vec<BabyBear> = (0..num_ancestors)
                .map(|i| hash_many(&[BabyBear::new(0xBEEF_0000 + i as u32), BabyBear::new(0xCAFE)]))
                .collect();

            // DSL circuit proves one ancestor at a time; bench the first
            let first_hash = ancestor_hashes[0];
            group.bench_with_input(
                BenchmarkId::new("prove_non_revocation", format!("{num_ancestors}_ancestors")),
                &num_ancestors,
                |b, _| {
                    b.iter(|| {
                        black_box(prove_non_revocation_dsl(&tree, first_hash).unwrap());
                    });
                },
            );

            let proof = prove_non_revocation_dsl(&tree, first_hash).unwrap();
            group.bench_with_input(
                BenchmarkId::new(
                    "verify_non_revocation",
                    format!("{num_ancestors}_ancestors"),
                ),
                &num_ancestors,
                |b, _| {
                    b.iter(|| {
                        black_box(
                            verify_non_revocation_dsl(&proof, revocation_root, first_hash).unwrap(),
                        );
                    });
                },
            );

            let proof_bytes = proof_to_bytes(&proof);
            eprintln!(
                "  [non_revocation {num_ancestors} ancestors] proof size: {} bytes ({:.1} KiB)",
                proof_bytes.len(),
                proof_bytes.len() as f64 / 1024.0
            );
        }
    }

    // --- Revocation registry: revoke + prove non-membership ---
    {
        use dregg_token::RevocationRegistry;

        let mut registry = RevocationRegistry::new();
        // Pre-populate with 100 revoked tokens
        for i in 0..100 {
            registry.revoke(&format!("token-{i}"));
        }

        group.bench_function("revocation_registry_revoke", |b| {
            let mut idx = 1000;
            b.iter(|| {
                idx += 1;
                black_box(registry.revoke(&format!("token-{idx}")));
            });
        });

        group.bench_function("revocation_registry_prove_non_revocation", |b| {
            b.iter(|| {
                let _ = black_box(registry.prove_non_revocation("token-not-revoked"));
            });
        });
    }

    group.finish();
}

// =============================================================================
// 6. The "Headline Number": Complete End-to-End Flow
// =============================================================================

fn bench_full_flow(c: &mut Criterion) {
    let mut group = c.benchmark_group("6_headline_e2e");
    group.sample_size(10);

    let key = test_key("headline");
    let (fed_root_bb, fed_root_bytes) = compute_federation_root(&key);

    // Complete flow: mint -> attenuate -> prove(Private) -> serialize -> verify -> accept/reject
    group.bench_function("mint_attenuate_prove_serialize_verify", |b| {
        b.iter(|| {
            // 1. Mint
            let token = MacaroonToken::mint(key, b"e2e-kid", "dregg.dev");

            // 2. Attenuate
            let att = Attenuation {
                apps: vec![("my-app".into(), "rw".into())],
                not_after: Some(2000000000),
                ..Default::default()
            };
            let _attenuated = token.attenuate(&att).unwrap();

            // 3. Build presentation and prove (real STARK)
            let mut builder =
                BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
            builder.set_root_token(MacaroonToken::mint(key, b"e2e-kid", "dregg.dev"));
            builder.add_attenuation(&att);

            let request = AuthRequest {
                app_id: Some("my-app".into()),
                action: Some("r".into()),
                ..Default::default()
            };
            let proof = builder.prove(&request).unwrap();

            // 4. Serialize to wire format
            let wire = proof.clone().into_wire_proof();
            let bytes = rmp_serde::to_vec(&wire).unwrap();

            // 5. Deserialize
            let _wire2: dregg_bridge::WirePresentationProof =
                rmp_serde::from_slice(&bytes).unwrap();

            // 6. Verify (using the original proof object which has federation_root)
            let verified = verify_presentation_complete(&proof, &fed_root_bytes);
            black_box(verified);
        });
    });

    // --- Measure each phase separately for the breakdown ---

    // Phase 1: Mint
    group.bench_function("phase1_mint", |b| {
        b.iter(|| {
            black_box(MacaroonToken::mint(key, b"e2e-kid", "dregg.dev"));
        });
    });

    // Phase 2: Attenuate
    let token = MacaroonToken::mint(key, b"e2e-kid", "dregg.dev");
    let att = Attenuation {
        apps: vec![("my-app".into(), "rw".into())],
        not_after: Some(2000000000),
        ..Default::default()
    };
    group.bench_function("phase2_attenuate", |b| {
        b.iter(|| {
            black_box(token.attenuate(&att).unwrap());
        });
    });

    // Phase 3: Prove (real STARK) -- the expensive part
    group.bench_function("phase3_prove_stark", |b| {
        b.iter(|| {
            let mut builder =
                BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
            builder.set_root_token(MacaroonToken::mint(key, b"e2e-kid", "dregg.dev"));
            builder.add_attenuation(&att);
            let request = AuthRequest {
                app_id: Some("my-app".into()),
                action: Some("r".into()),
                ..Default::default()
            };
            black_box(builder.prove(&request).unwrap());
        });
    });

    // Generate proof for serialize/verify phases
    let mut builder = BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
    builder.set_root_token(MacaroonToken::mint(key, b"e2e-kid", "dregg.dev"));
    builder.add_attenuation(&att);
    let request = AuthRequest {
        app_id: Some("my-app".into()),
        action: Some("r".into()),
        ..Default::default()
    };
    let proof = builder.prove(&request).unwrap();
    let wire = proof.clone().into_wire_proof();

    // Phase 4: Serialize
    group.bench_function("phase4_serialize", |b| {
        b.iter(|| {
            black_box(rmp_serde::to_vec(&wire).unwrap());
        });
    });

    let wire_bytes = rmp_serde::to_vec(&wire).unwrap();
    eprintln!(
        "  [headline] total wire proof: {} bytes ({:.1} KiB)",
        wire_bytes.len(),
        wire_bytes.len() as f64 / 1024.0
    );

    // Phase 5: Deserialize
    group.bench_function("phase5_deserialize", |b| {
        b.iter(|| {
            black_box(
                rmp_serde::from_slice::<dregg_bridge::WirePresentationProof>(&wire_bytes).unwrap(),
            );
        });
    });

    // Phase 6: Verify
    group.bench_function("phase6_verify", |b| {
        b.iter(|| {
            black_box(verify_presentation_complete(&proof, &fed_root_bytes));
        });
    });

    group.finish();
}

// =============================================================================
// Helper: Build multi-step witness for inner STARK benchmarks
// =============================================================================

fn make_derivation_step(
    step_idx: u32,
    state_root: BabyBear,
    is_final: bool,
) -> dregg_circuit::derivation_air::DerivationWitness {
    use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
    use dregg_circuit::poseidon2::hash_fact;

    let pred = if is_final {
        BabyBear::new(ALLOW_PREDICATE)
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

// =============================================================================
// Criterion groups
// =============================================================================

criterion_group!(
    name = token_ops;
    config = Criterion::default();
    targets = bench_token_operations
);

criterion_group!(
    name = proof_generation;
    config = Criterion::default().sample_size(10);
    targets = bench_proof_generation
);

criterion_group!(
    name = proof_verification;
    config = Criterion::default().sample_size(10);
    targets = bench_proof_verification
);

criterion_group!(
    name = ivc_composition;
    config = Criterion::default().sample_size(10);
    targets = bench_ivc_stark
);

#[cfg(feature = "mina")]
criterion_group!(
    name = recursive_composition;
    config = Criterion::default().sample_size(10);
    targets = bench_recursive_composition
);

criterion_group!(
    name = federation_ops;
    config = Criterion::default().sample_size(10);
    targets = bench_federation_ops
);

criterion_group!(
    name = headline_e2e;
    config = Criterion::default().sample_size(10);
    targets = bench_full_flow
);

#[cfg(not(feature = "mina"))]
criterion_main!(
    token_ops,
    proof_generation,
    proof_verification,
    ivc_composition,
    federation_ops,
    headline_e2e,
);

#[cfg(feature = "mina")]
criterion_main!(
    token_ops,
    proof_generation,
    proof_verification,
    ivc_composition,
    recursive_composition,
    federation_ops,
    headline_e2e,
);
