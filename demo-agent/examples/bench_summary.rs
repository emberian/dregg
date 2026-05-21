//! Quick benchmark summary — runs each proof operation ONCE and prints a table.
//!
//! This is NOT statistically rigorous (use `cargo bench` for that). It gives
//! a fast "what are the numbers?" without criterion's warmup/iteration overhead.
//!
//! Run with: `cargo run --release -p pyana-demo-agent --example bench_summary`

use std::time::{Duration, Instant};

use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2::{hash_4_to_1, hash_many};
use pyana_circuit::stark::{self, MerkleStarkAir, generate_merkle_trace, proof_to_bytes};

// ─── Helpers ────────────────────────────────────────────────────────────────

fn time_op<F: FnOnce()>(f: F) -> Duration {
    let start = Instant::now();
    f();
    start.elapsed()
}

fn time_op_avg<F: FnMut()>(mut f: F, iterations: u32) -> Duration {
    // Warmup
    for _ in 0..2 {
        f();
    }
    let start = Instant::now();
    for _ in 0..iterations {
        f();
    }
    start.elapsed() / iterations
}

fn fmt_dur(d: Duration) -> String {
    let nanos = d.as_nanos();
    if nanos < 1_000 {
        format!("{nanos} ns")
    } else if nanos < 1_000_000 {
        format!("{:.1} us", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{:.2} ms", nanos as f64 / 1_000_000.0)
    } else {
        format!("{:.3} s", nanos as f64 / 1_000_000_000.0)
    }
}

fn fmt_size(bytes: usize) -> String {
    if bytes < 1024 {
        format!("{bytes} B")
    } else if bytes < 1024 * 1024 {
        format!("{:.1} KiB", bytes as f64 / 1024.0)
    } else {
        format!("{:.2} MiB", bytes as f64 / (1024.0 * 1024.0))
    }
}

// ─── Derivation witness builder ─────────────────────────────────────────────

fn make_derivation_step(
    step_idx: u32,
    state_root: BabyBear,
    is_final: bool,
) -> pyana_circuit::derivation_air::DerivationWitness {
    use pyana_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
    use pyana_circuit::poseidon2::hash_fact;

    let pred = if is_final {
        BabyBear::new(pyana_circuit::multi_step_air::ALLOW_PREDICATE)
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
    }
}

fn build_witness(num_steps: usize) -> pyana_circuit::multi_step_air::MultiStepWitness {
    let state_root = BabyBear::new(0x1234_5678);
    let request_hash = BabyBear::new(0xABCD_0001);
    let steps: Vec<_> = (0..num_steps)
        .map(|i| make_derivation_step(i as u32, state_root, i == num_steps - 1))
        .collect();
    pyana_circuit::multi_step_air::build_multi_step_witness(state_root, request_hash, steps)
}

// ─── Main ───────────────────────────────────────────────────────────────────

fn main() {
    println!();
    println!("================================================================================");
    println!("  PYANA Proof Benchmark Summary (single-run, release build)");
    println!("================================================================================");
    println!();
    println!(
        "| {:<45} | {:<12} | {:<12} | {:<10} |",
        "Operation", "Prove", "Verify", "Proof Size"
    );
    println!("|{:-<47}|{:-<14}|{:-<14}|{:-<12}|", "", "", "", "");

    // ─── 1. Primitives (context) ────────────────────────────────────────────

    let d = time_op_avg(
        || {
            let _ = hash_4_to_1(&[
                BabyBear::new(1),
                BabyBear::new(2),
                BabyBear::new(3),
                BabyBear::new(4),
            ]);
        },
        100_000,
    );
    println!(
        "| {:<45} | {:<12} | {:<12} | {:<10} |",
        "Poseidon2 hash (4-to-1)",
        fmt_dur(d),
        "-",
        "-"
    );

    let a = BabyBear::new(1_234_567_890);
    let d = time_op_avg(
        || {
            let _ = a.inverse();
        },
        100_000,
    );
    println!(
        "| {:<45} | {:<12} | {:<12} | {:<10} |",
        "BabyBear field inverse",
        fmt_dur(d),
        "-",
        "-"
    );

    // Ed25519 sign + verify
    {
        use ed25519_dalek::{Signer, SigningKey, Verifier};
        let mut key_bytes = [0u8; 32];
        getrandom::fill(&mut key_bytes).unwrap();
        let signing_key = SigningKey::from_bytes(&key_bytes);
        let verifying_key = signing_key.verifying_key();
        let msg = b"benchmark message for ed25519";

        let d_sign = time_op_avg(
            || {
                let _ = signing_key.sign(msg);
            },
            10_000,
        );
        let sig = signing_key.sign(msg);
        let d_verify = time_op_avg(
            || {
                let _ = verifying_key.verify(msg, &sig);
            },
            10_000,
        );

        println!(
            "| {:<45} | {:<12} | {:<12} | {:<10} |",
            "Ed25519 sign + verify",
            fmt_dur(d_sign),
            fmt_dur(d_verify),
            "64 B"
        );
    }

    println!("|{:-<47}|{:-<14}|{:-<14}|{:-<12}|", "", "", "", "");

    // ─── 2. Poseidon2 STARK (2-row trace) ───────────────────────────────────

    {
        use pyana_circuit::poseidon2::WIDTH;
        use pyana_circuit::poseidon2_air::Poseidon2Air;

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
        let (trace, pi) = Poseidon2Air::generate_trace(&input);
        let air = Poseidon2Air;

        let d_prove = time_op(|| {
            let _ = stark::prove(&air, &trace, &pi);
        });
        let proof = stark::prove(&air, &trace, &pi);
        let d_verify = time_op_avg(
            || {
                let _ = stark::verify(&air, &proof, &pi);
            },
            100,
        );
        let size = proof_to_bytes(&proof).len();

        println!(
            "| {:<45} | {:<12} | {:<12} | {:<10} |",
            "Poseidon2 hash proof (2-row STARK)",
            fmt_dur(d_prove),
            fmt_dur(d_verify),
            fmt_size(size)
        );
    }

    // ─── 3. Merkle membership (depth 4, 8, 16) ─────────────────────────────

    for &depth in &[4usize, 8, 16] {
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
        let (trace, pi) = generate_merkle_trace(12345, &siblings, &positions);
        let air = MerkleStarkAir;

        let d_prove = time_op(|| {
            let _ = stark::prove(&air, &trace, &pi);
        });
        let proof = stark::prove(&air, &trace, &pi);
        let d_verify = time_op_avg(
            || {
                let _ = stark::verify(&air, &proof, &pi);
            },
            50,
        );
        let size = proof_to_bytes(&proof).len();

        println!(
            "| {:<45} | {:<12} | {:<12} | {:<10} |",
            format!("Merkle membership (d={depth})"),
            fmt_dur(d_prove),
            fmt_dur(d_verify),
            fmt_size(size)
        );
    }

    println!("|{:-<47}|{:-<14}|{:-<14}|{:-<12}|", "", "", "", "");

    // ─── 4. Note spending proof (depth 4, 8) ────────────────────────────────

    {
        use pyana_circuit::note_spending_air::{
            create_test_witness, prove_note_spend, test_spending_key, verify_note_spend,
        };

        for &depth in &[4usize, 8] {
            let key = test_spending_key(0xDEAD_BEEF);
            let witness = create_test_witness(
                BabyBear::new(1000),
                BabyBear::new(500),
                BabyBear::new(1),
                key,
                depth,
            );
            let nullifier = witness.nullifier();
            let merkle_root = witness.merkle_root();

            let d_prove = time_op(|| {
                let _ = prove_note_spend(&witness);
            });
            let proof = prove_note_spend(&witness);
            let d_verify = time_op_avg(
                || {
                    let _ = verify_note_spend(nullifier, merkle_root, &proof);
                },
                50,
            );
            let size = proof_to_bytes(&proof).len();

            println!(
                "| {:<45} | {:<12} | {:<12} | {:<10} |",
                format!("Note spending (d={depth}, 19-col AIR)"),
                fmt_dur(d_prove),
                fmt_dur(d_verify),
                fmt_size(size)
            );
        }
    }

    println!("|{:-<47}|{:-<14}|{:-<14}|{:-<12}|", "", "", "", "");

    // ─── 5. Multi-step derivation (1, 8, 32 steps) ─────────────────────────

    {
        use pyana_circuit::multi_step_air::{
            prove_authorization_stark, verify_authorization_stark,
        };

        for &steps in &[1usize, 8, 32] {
            let witness = build_witness(steps);
            let conclusion = witness.conclusion();
            let acc_hash = witness.final_accumulated_hash();

            let d_prove = time_op(|| {
                let _ = prove_authorization_stark(&witness);
            });
            let proof = prove_authorization_stark(&witness);
            let d_verify = time_op_avg(
                || {
                    let _ = verify_authorization_stark(conclusion, acc_hash, &proof);
                },
                10,
            );
            let size = proof_to_bytes(&proof).len();

            println!(
                "| {:<45} | {:<12} | {:<12} | {:<10} |",
                format!("{steps}-step derivation (143-col STARK)"),
                fmt_dur(d_prove),
                fmt_dur(d_verify),
                fmt_size(size)
            );
        }
    }

    println!("|{:-<47}|{:-<14}|{:-<14}|{:-<12}|", "", "", "", "");

    // ─── 6. State transition IVC (1, 5, 20 steps) ──────────────────────────

    {
        use pyana_circuit::ivc::{
            create_test_chain, prove_ivc, prove_ivc_stark, verify_ivc, verify_ivc_stark,
        };

        for &steps in &[1usize, 5, 20] {
            let (initial_root, deltas) = create_test_chain(steps);
            let new_roots: Vec<BabyBear> = deltas.iter().map(|d| d.fold.new_root).collect();

            // Constraint-based IVC
            let d_prove = time_op(|| {
                let _ = prove_ivc(initial_root, deltas.clone());
            });
            let proof = prove_ivc(initial_root, deltas.clone()).unwrap();
            let d_verify = time_op_avg(
                || {
                    let _ = verify_ivc(&proof, Some(initial_root));
                },
                100,
            );
            let size = proof.proof_size_bytes();

            println!(
                "| {:<45} | {:<12} | {:<12} | {:<10} |",
                format!("IVC fold chain ({steps} steps, constraint)"),
                fmt_dur(d_prove),
                fmt_dur(d_verify),
                fmt_size(size)
            );

            // STARK-based IVC
            let d_prove_s = time_op(|| {
                let _ = prove_ivc_stark(initial_root, &new_roots);
            });
            let (sp, spi) = prove_ivc_stark(initial_root, &new_roots);
            let d_verify_s = time_op_avg(
                || {
                    let _ = verify_ivc_stark(&sp, &spi);
                },
                50,
            );
            let size_s = proof_to_bytes(&sp).len();

            println!(
                "| {:<45} | {:<12} | {:<12} | {:<10} |",
                format!("IVC state transition ({steps} steps, STARK)"),
                fmt_dur(d_prove_s),
                fmt_dur(d_verify_s),
                fmt_size(size_s)
            );
        }
    }

    println!("|{:-<47}|{:-<14}|{:-<14}|{:-<12}|", "", "", "", "");

    // ─── 7. Non-revocation (1, 4, 8 ancestors) ─────────────────────────────

    {
        use pyana_circuit::non_revocation_air::{
            REVOCATION_TREE_DEPTH, SortedRevocationTree, prove_non_revocation,
            verify_non_revocation,
        };

        let hashes: Vec<BabyBear> = (1..=20u32)
            .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xDEAD)]))
            .collect();
        let tree = SortedRevocationTree::new(hashes, REVOCATION_TREE_DEPTH);
        let rev_root = tree.root();

        for &num_a in &[1usize, 4, 8] {
            let ancestors: Vec<BabyBear> = (0..num_a)
                .map(|i| hash_many(&[BabyBear::new(0xBEEF_0000 + i as u32), BabyBear::new(0xCAFE)]))
                .collect();

            let d_prove = time_op(|| {
                let _ = prove_non_revocation(&ancestors, &tree);
            });
            let proof = prove_non_revocation(&ancestors, &tree).unwrap();
            let d_verify = time_op_avg(
                || {
                    let _ = verify_non_revocation(rev_root, &proof);
                },
                20,
            );
            let size = proof_to_bytes(&proof).len();

            println!(
                "| {:<45} | {:<12} | {:<12} | {:<10} |",
                format!("Non-revocation ({num_a} ancestors)"),
                fmt_dur(d_prove),
                fmt_dur(d_verify),
                fmt_size(size)
            );
        }
    }

    println!("|{:-<47}|{:-<14}|{:-<14}|{:-<12}|", "", "", "", "");

    // ─── 8. Composed: BodyMembershipProof ───────────────────────────────────

    {
        use pyana_circuit::body_membership::{
            BodyFactMerkleProof, collect_body_fact_hashes, prove_authorization_with_membership,
            verify_authorization_with_membership,
        };

        let witness = build_witness(4);
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
                BodyFactMerkleProof {
                    fact_hash: hash,
                    siblings,
                    positions: vec![0, 1, 2, 3],
                }
            })
            .collect();

        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        let d_prove = time_op(|| {
            let _ = prove_authorization_with_membership(&witness, &body_proofs);
        });
        let composed = prove_authorization_with_membership(&witness, &body_proofs);
        let d_verify = time_op(|| {
            let _ =
                verify_authorization_with_membership(&composed, conclusion, acc_hash, &body_hashes);
        });

        let deriv_size = proof_to_bytes(&composed.derivation_proof).len();
        let memb_size: usize = composed
            .membership_proofs
            .iter()
            .map(|m| proof_to_bytes(&m.proof).len())
            .sum();
        let total = deriv_size + memb_size;

        println!(
            "| {:<45} | {:<12} | {:<12} | {:<10} |",
            format!(
                "BodyMembership (4-step + {} memb)",
                composed.membership_proofs.len()
            ),
            fmt_dur(d_prove),
            fmt_dur(d_verify),
            fmt_size(total)
        );
    }

    // ─── 9. Composed: ChunkedAuthorization ──────────────────────────────────

    {
        use pyana_circuit::chunked_derivation::{
            prove_chunked_authorization, verify_chunked_authorization,
        };

        for &(total, chunk_sz) in &[(4usize, 2usize), (8, 2)] {
            let witness = build_witness(total);
            let conclusion = witness.conclusion();
            let state_root = witness.initial_state_root;
            let num_chunks = total.div_ceil(chunk_sz);

            let d_prove = time_op(|| {
                let _ = prove_chunked_authorization(&witness, chunk_sz);
            });
            let proof = prove_chunked_authorization(&witness, chunk_sz);
            let d_verify = time_op(|| {
                let _ = verify_chunked_authorization(&proof, conclusion, state_root);
            });
            let total_size: usize = proof
                .chunk_proofs
                .iter()
                .map(|p| proof_to_bytes(p).len())
                .sum();

            println!(
                "| {:<45} | {:<12} | {:<12} | {:<10} |",
                format!("Chunked authorization ({num_chunks} chunks, {total} steps)"),
                fmt_dur(d_prove),
                fmt_dur(d_verify),
                fmt_size(total_size)
            );
        }
    }

    println!("|{:-<47}|{:-<14}|{:-<14}|{:-<12}|", "", "", "", "");

    // ─── 10. Full pipeline end-to-end ───────────────────────────────────────

    {
        use pyana_circuit::multi_step_air::{
            prove_authorization_stark, verify_authorization_stark,
        };

        let witness = build_witness(8);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        let d_e2e = time_op(|| {
            let proof = prove_authorization_stark(&witness);
            let bytes = proof_to_bytes(&proof);
            let proof2 = stark::proof_from_bytes(&bytes).unwrap();
            let _ = verify_authorization_stark(conclusion, acc_hash, &proof2);
        });

        let proof = prove_authorization_stark(&witness);
        let size = proof_to_bytes(&proof).len();

        println!(
            "| {:<45} | {:<12} | {:<12} | {:<10} |",
            "Full pipeline (8-step prove+ser+deser+verify)",
            fmt_dur(d_e2e),
            "-",
            fmt_size(size)
        );
    }

    // ─── 11. Macaroon token (non-proof context) ─────────────────────────────

    {
        use pyana_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};

        let key = {
            let mut k = [0u8; 32];
            getrandom::fill(&mut k).unwrap();
            k
        };

        let d_mint = time_op_avg(
            || {
                let _ = MacaroonToken::mint(key, b"kid", "pyana.dev");
            },
            10_000,
        );
        let tok = MacaroonToken::mint(key, b"kid", "pyana.dev");
        let req = AuthRequest::default();
        let d_verify = time_op_avg(
            || {
                let _ = tok.verify(&req);
            },
            10_000,
        );

        println!(
            "| {:<45} | {:<12} | {:<12} | {:<10} |",
            "Macaroon mint + verify (0 caveats)",
            fmt_dur(d_mint),
            fmt_dur(d_verify),
            "-"
        );
    }

    println!();
    println!("================================================================================");
    println!("  All timings are single-run (release build). Use `cargo bench` for statistics.");
    println!("================================================================================");
    println!();
}
