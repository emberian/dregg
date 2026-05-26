//! Silver→Golden Bridge: aggregating 5 leaf STARK proofs into a single Pickles
//! recursive root proof.
//!
//! ## What this test demonstrates
//!
//! The Silver Vision produces 5 independent per-step EffectVm STARK proofs.
//! Each proof is individually verified by the STARK verifier.
//!
//! The Golden Vision asks: can verification of the ROOT PROOF algebraically
//! assert that every leaf was valid? This test shows it CAN via Pickles IPA
//! accumulation:
//!
//! ```text
//! Step 1 STARK ──┐
//! Step 2 STARK ──┤  wrap_stark_in_pickles (each)
//! Step 3 STARK ──┤      ↓ ↓ ↓ ↓ ↓
//! Step 4 STARK ──┤  PicklesWrappedStark × 5
//! Step 5 STARK ──┘      ↓
//!                   tree compose (pairwise)
//!                       ↓
//!                   root PicklesWrappedStark
//!                       ↓
//!               verify_pickles_wrapped_stark(root) → kimchi::verifier::verify
//!               (batch-checks all accumulated IPA challenges in one MSM)
//! ```
//!
//! ## Algebraic binding via IPA accumulator
//!
//! Each `wrap_stark_in_pickles` call:
//! 1. Natively verifies the STARK (defense-in-depth guard).
//! 2. Builds a Kimchi circuit encoding the STARK verifier (Poseidon gates for
//!    Merkle paths, Generic gates for BabyBear arithmetic).
//! 3. Proves that circuit in Kimchi over Vesta.
//! 4. Calls `prove_recursive_step` to create a Pickles IVC step whose state
//!    hashes bind the STARK's public inputs and Poseidon trace commitment.
//!
//! `compose_wrapped_starks(a, b)` then calls
//! `prove_recursive_step(Some(&a.pickles_proof), ...)` which uses
//! `create_recursive` to carry `a`'s IPA accumulator as `prev_challenges`.
//! The final `verify_recursive_proof` → `kimchi::verifier::verify` batch-checks
//! ALL accumulated IPA challenges in a single MSM. Tampering any challenge
//! → the MSM check fails.
//!
//! ## Honest soundness caveat (the gap to full Golden Vision)
//!
//! The native STARK verification in step 1 of `wrap_stark_in_pickles` is the
//! PRIMARY soundness anchor today. The Kimchi circuit's equality gates
//! (`computed_root == public_commitment`) bind the trace commitment, and the
//! BabyBear arithmetic gates constrain constraint evaluation, but full Golden
//! Vision = removing the native pre-check and relying solely on the algebraic
//! constraints. That requires every equality-gate path to be adversarially
//! tested to ensure no forged witness can slip through. The gate layout is
//! correct; the adversarial closure is future work.

#[cfg(feature = "mina")]
mod golden_pickles {
    use std::collections::HashMap;

    use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
    use pyana_circuit::{
        BabyBear, CellState as VmCellState, Effect as VmEffect, EffectVmAir,
        backends::stark_in_pickles::{
            WrapConfig, compose_wrapped_starks, verify_pickles_wrapped_stark, wrap_stark_in_pickles,
        },
        generate_effect_vm_trace,
        poseidon_stark::prove_poseidon,
    };
    use pyana_turn::{
        ActionBuilder, CallForest, CommitmentMode, ComputronCosts, DelegationMode, Effect, Turn,
        TurnExecutor, TurnResult,
    };

    fn test_key(name: &str) -> [u8; 32] {
        *blake3::hash(format!("golden-pickles:{name}").as_bytes()).as_bytes()
    }

    fn token_id() -> [u8; 32] {
        *blake3::hash(b"golden-pickles-token").as_bytes()
    }

    fn permissive_cell(seed: &str, balance: u64) -> Cell {
        let key = test_key(seed);
        let mut cell = Cell::with_balance(key, token_id(), balance);
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        cell
    }

    fn make_ledger() -> (Ledger, [CellId; 5]) {
        let seeds = ["issuer", "registry", "subscription", "worker", "settlement"];
        let balances = [1_000_000u64, 1_000_000, 5_000_000, 100_000, 1_000_000];
        let mut ledger = Ledger::new();
        let mut ids = [CellId::from_bytes([0u8; 32]); 5];
        for i in 0..5 {
            let cell = permissive_cell(seeds[i], balances[i]);
            ids[i] = cell.id();
            ledger.insert_cell(cell).unwrap();
        }
        // Grant self-cap and next-cell cap for causal permission checks.
        for i in 0..5 {
            let agent = ledger.get_mut(&ids[i]).unwrap();
            agent.capabilities.grant(ids[i], AuthRequired::None);
            if i + 1 < 5 {
                agent.capabilities.grant(ids[i + 1], AuthRequired::None);
            }
        }
        // Worker (D) also needs cap to C so the Transfer is authorized.
        let d = ledger.get_mut(&ids[3]).unwrap();
        d.capabilities.grant(ids[2], AuthRequired::None);
        (ledger, ids)
    }

    fn single_effect_turn(
        agent: CellId,
        nonce: u64,
        previous_receipt_hash: Option<[u8; 32]>,
        depends_on: Vec<[u8; 32]>,
        target: CellId,
        method: &str,
        effect: Effect,
        memo: &str,
    ) -> Turn {
        let action = ActionBuilder::new_unchecked_for_tests(target, method, agent)
            .delegation(DelegationMode::None)
            .commitment_mode(CommitmentMode::Full)
            .effect(effect)
            .build();
        let mut forest = CallForest::new();
        forest.add_root(action);
        Turn {
            agent,
            nonce,
            call_forest: forest,
            fee: 300,
            memo: Some(memo.into()),
            valid_until: None,
            previous_receipt_hash,
            depends_on,
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// Execute the 5-step causal graph and return per-step (trace, pi, air).
    ///
    /// The VmEffect projections match the pattern in `silver_vision_graph_e2e`:
    /// BabyBear field values are meaningful placeholders — the AIR enforces the
    /// row selector and layout, not the semantic field bytes.
    fn run_5_steps(
        ledger: &mut Ledger,
        ids: [CellId; 5],
    ) -> Vec<(Vec<Vec<BabyBear>>, Vec<BabyBear>, EffectVmAir)> {
        let executor = TurnExecutor::new(ComputronCosts::default_costs());
        let mut results = Vec::new();

        // We build the steps sequentially because depends_on chains on prior turn hashes.
        // Step 1: A issues credential
        let t1 = single_effect_turn(
            ids[0],
            0,
            None,
            vec![],
            ids[0],
            "issue_credential",
            Effect::SetField {
                cell: ids[0],
                index: 0,
                value: *blake3::hash(b"credential-v1").as_bytes(),
            },
            "golden-step1",
        );
        let t1_hash = t1.hash();
        let pre1 = ledger.get(&ids[0]).unwrap().state.balance();
        match executor.execute(&t1, ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!("step1 failed: {other:?}"),
        }
        let state1 = VmCellState::new(pre1, 0);
        let (tr1, pi1) = generate_effect_vm_trace(
            &state1,
            &[VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(1),
            }],
        );
        let air1 = EffectVmAir::new(tr1.len());
        results.push((tr1, pi1, air1));

        // Step 2: B registers name (depends on t1)
        let t2 = single_effect_turn(
            ids[1],
            0,
            None,
            vec![t1_hash],
            ids[1],
            "register_name",
            Effect::SetField {
                cell: ids[1],
                index: 0,
                value: *blake3::hash(b"alice.pyana").as_bytes(),
            },
            "golden-step2",
        );
        let t2_hash = t2.hash();
        let pre2 = ledger.get(&ids[1]).unwrap().state.balance();
        match executor.execute(&t2, ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!("step2 failed: {other:?}"),
        }
        let state2 = VmCellState::new(pre2, 0);
        let (tr2, pi2) = generate_effect_vm_trace(
            &state2,
            &[VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(2),
            }],
        );
        let air2 = EffectVmAir::new(tr2.len());
        results.push((tr2, pi2, air2));

        // Step 3: C publishes bounty (depends on t2)
        let t3 = single_effect_turn(
            ids[2],
            0,
            None,
            vec![t2_hash],
            ids[2],
            "publish_bounty",
            Effect::SetField {
                cell: ids[2],
                index: 0,
                value: *blake3::hash(b"bounty-100").as_bytes(),
            },
            "golden-step3",
        );
        let t3_hash = t3.hash();
        let pre3 = ledger.get(&ids[2]).unwrap().state.balance();
        match executor.execute(&t3, ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!("step3 failed: {other:?}"),
        }
        let state3 = VmCellState::new(pre3, 0);
        let (tr3, pi3) = generate_effect_vm_trace(
            &state3,
            &[VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(3),
            }],
        );
        let air3 = EffectVmAir::new(tr3.len());
        results.push((tr3, pi3, air3));

        // Step 4: D claims bounty from C (Transfer, depends on t3)
        let t4 = single_effect_turn(
            ids[3],
            0,
            None,
            vec![t3_hash],
            ids[2],
            "claim_bounty",
            Effect::Transfer {
                from: ids[2],
                to: ids[3],
                amount: 100,
            },
            "golden-step4",
        );
        let t4_hash = t4.hash();
        let pre4 = ledger.get(&ids[3]).unwrap().state.balance();
        match executor.execute(&t4, ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!("step4 failed: {other:?}"),
        }
        // D's perspective: incoming credit (direction=0)
        let state4 = VmCellState::new(pre4, 0);
        let (tr4, pi4) = generate_effect_vm_trace(
            &state4,
            &[VmEffect::Transfer {
                amount: 100,
                direction: 0,
            }],
        );
        let air4 = EffectVmAir::new(tr4.len());
        results.push((tr4, pi4, air4));

        // Step 5: E records settlement (depends on t4)
        let t5 = single_effect_turn(
            ids[4],
            0,
            None,
            vec![t4_hash],
            ids[4],
            "settle",
            Effect::SetField {
                cell: ids[4],
                index: 0,
                value: *blake3::hash(b"settled").as_bytes(),
            },
            "golden-step5",
        );
        let pre5 = ledger.get(&ids[4]).unwrap().state.balance();
        match executor.execute(&t5, ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!("step5 failed: {other:?}"),
        }
        let state5 = VmCellState::new(pre5, 0);
        let (tr5, pi5) = generate_effect_vm_trace(
            &state5,
            &[VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(5),
            }],
        );
        let air5 = EffectVmAir::new(tr5.len());
        results.push((tr5, pi5, air5));

        results
    }

    /// Full Silver→Golden bridge: 5 leaves → 1 Pickles root proof.
    ///
    /// Ignored in CI because Pickles wrapping × 5 + 4 compositions takes ~30s.
    #[test]
    #[ignore = "SLOW: Pickles wrapping × 5 + 4 compositions (~30s). Run explicitly."]
    fn silver_to_golden_pickles_bridge() {
        let (mut ledger, ids) = make_ledger();
        let steps = run_5_steps(&mut ledger, ids);
        assert_eq!(steps.len(), 5);

        let fast = WrapConfig::fast(); // 1 FRI query for speed

        // ── Phase 1: Poseidon re-prove + Pickles wrap each leaf ───────────────
        let mut wrapped = Vec::new();
        for (i, (trace, pi, air)) in steps.iter().enumerate() {
            let pp = prove_poseidon(air, trace, pi);
            let w = wrap_stark_in_pickles(&pp, air, pi, Some(&fast))
                .unwrap_or_else(|e| panic!("wrap leaf {i}: {e}"));
            assert_eq!(w.air_name, "pyana-effect-vm-v1", "leaf {i}: wrong AIR name");
            println!(
                "  leaf {i}: Kimchi rows={}, Pickles proof={} bytes",
                w.circuit_row_count,
                w.pickles_proof.proof_bytes.len()
            );
            wrapped.push(w);
        }

        // ── Phase 2: binary-tree composition ─────────────────────────────────
        // (0, 1) → w01   (2, 3) → w23   (w01, w23) → w0123   (w0123, 4) → root
        //
        // Each compose(a, b):
        //   native verify(a) + prove_recursive_step(Some(&a), ...) using
        //   create_recursive with a's IPA accumulator as prev_challenges.
        let w01 = compose_wrapped_starks(&wrapped[0], &wrapped[1]).expect("compose(0,1)");
        let w23 = compose_wrapped_starks(&wrapped[2], &wrapped[3]).expect("compose(2,3)");
        let w0123 = compose_wrapped_starks(&w01, &w23).expect("compose(01,23)");
        let root = compose_wrapped_starks(&w0123, &wrapped[4]).expect("compose(0123,4)");

        println!(
            "  root: {} bytes (from 5 leaves via 4 Pickles composition steps)",
            root.pickles_proof.proof_bytes.len()
        );

        // ── Phase 3: verify the root ─────────────────────────────────────────
        // verify_pickles_wrapped_stark → verify_recursive_proof → kimchi::verifier::verify
        // batch-checks all IPA accumulators accumulated across the 4 compose steps.
        let valid = verify_pickles_wrapped_stark(&root, None).expect("root verify");
        assert!(valid, "root proof must verify: IPA batch check passes");

        // ── Phase 4: constant proof size (not linear in leaf count) ──────────
        let leaf_sz = wrapped[0].pickles_proof.proof_bytes.len();
        let root_sz = root.pickles_proof.proof_bytes.len();
        assert!(
            root_sz < leaf_sz * 4,
            "root ({root_sz}B) must not be ≥4× leaf ({leaf_sz}B): ratio={:.2}",
            root_sz as f64 / leaf_sz as f64
        );
        println!(
            "  sizes: leaf={leaf_sz}B  root={root_sz}B  ratio={:.2}",
            root_sz as f64 / leaf_sz as f64
        );

        // ── Phase 5: tampered leaf rejected before contributing ───────────────
        let (trace2, pi2, air2) = &steps[2];
        let mut bad = prove_poseidon(air2, trace2, pi2);
        if let Some(qp) = bad.query_proofs.first_mut() {
            if let Some(tv) = qp.trace_values.first_mut() {
                *tv = tv.wrapping_add(1) % 2013265921u32; // BABYBEAR_P
            }
        }
        assert!(
            wrap_stark_in_pickles(&bad, air2, pi2, Some(&fast)).is_err(),
            "tampered leaf must fail at native STARK verification inside wrap"
        );
        println!("  tamper: rejected (native verify caught it)");
        println!("Silver→Golden bridge: PASS");
    }

    /// Fast smoke test: 2-leaf wrap + compose. Not #[ignore] — runs in normal CI.
    /// Exercises the full type wiring from EffectVmAir → Pickles without the full
    /// 5-step overhead.
    #[test]
    fn pickles_bridge_smoke_two_leaves() {
        let (mut ledger, ids) = make_ledger();
        let steps = run_5_steps(&mut ledger, ids);
        assert!(steps.len() >= 2);

        let fast = WrapConfig::fast();

        let leaves: Vec<_> = steps[..2]
            .iter()
            .enumerate()
            .map(|(i, (trace, pi, air))| {
                let pp = prove_poseidon(air, trace, pi);
                wrap_stark_in_pickles(&pp, air, pi, Some(&fast))
                    .unwrap_or_else(|e| panic!("wrap {i}: {e}"))
            })
            .collect();

        assert_eq!(leaves[0].air_name, "pyana-effect-vm-v1");
        assert_eq!(leaves[1].air_name, "pyana-effect-vm-v1");

        let composed = compose_wrapped_starks(&leaves[0], &leaves[1])
            .expect("2-leaf composition must succeed");

        // Combined public inputs = union of both leaves.
        let expected_pi = leaves[0].public_inputs.len() + leaves[1].public_inputs.len();
        assert_eq!(composed.public_inputs.len(), expected_pi);

        // The composed proof must verify. This exercises kimchi::verifier::verify
        // which batch-checks the IPA accumulator from leaf[0] (carried via
        // create_recursive) plus the new step's IPA opening.
        let valid =
            verify_pickles_wrapped_stark(&composed, None).expect("composed verify must not error");
        assert!(valid, "2-leaf Pickles composition must verify");

        println!(
            "Smoke: leaf[0]={} bytes  composed={} bytes",
            leaves[0].pickles_proof.proof_bytes.len(),
            composed.pickles_proof.proof_bytes.len()
        );
    }

    /// Negative: wrapping a tampered Poseidon proof must fail.
    /// This pinpoints the native pre-check (current soundness anchor).
    #[test]
    fn pickles_wrap_rejects_tampered_stark() {
        let (mut ledger, ids) = make_ledger();
        let steps = run_5_steps(&mut ledger, ids);
        let (trace, pi, air) = &steps[0];

        let mut bad_proof = prove_poseidon(air, trace, pi);
        if let Some(qp) = bad_proof.query_proofs.first_mut() {
            if let Some(tv) = qp.trace_values.first_mut() {
                *tv = tv.wrapping_add(1) % 2013265921u32;
            }
        }

        let result = wrap_stark_in_pickles(&bad_proof, air, pi, Some(&WrapConfig::fast()));
        assert!(
            result.is_err(),
            "tampered STARK must fail at native verify inside wrap_stark_in_pickles"
        );
    }
}

#[cfg(not(feature = "mina"))]
mod golden_pickles {
    #[test]
    fn pickles_bridge_mina_feature_required() {
        // pyana-circuit defaults include mina, so this branch normally never executes.
        println!("golden_vision_pickles_bridge: skipped (mina feature not enabled)");
    }
}
