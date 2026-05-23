//! Full-pipeline integration test: DSL circuits through the executor.
//!
//! Proves the complete path:
//!   1. Construct a CircuitDescriptor (temporal predicate)
//!   2. Create a CellProgram, deploy to ProgramRegistry
//!   3. Create a TurnExecutor with that registry
//!   4. Register a sovereign cell with the program's VK hash
//!   5. Generate a valid trace (3 steps, value=100, threshold=50)
//!   6. Prove using DslCircuit + stark::prove
//!   7. Build a Turn with execution_proof
//!   8. Execute — executor verifies via registry and updates commitment
//!   9. Assert: commitment updated, no error
//!
//! Also tests: wrong proof rejected, wrong VK rejected.

use pyana_cell::{Cell, CellId, Ledger};
use pyana_circuit::dsl::{CellProgram, DslCircuit, ProgramRegistry};
use pyana_circuit::field::{BABYBEAR_P, BabyBear};
use pyana_circuit::stark::{self, StarkAir};
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use pyana_turn::{ComputronCosts, DelegationMode, Effect, TurnBuilder, TurnExecutor, TurnResult};

// ============================================================================
// Temporal predicate descriptor (from pyana-dsl-tests/src/temporal_dsl.rs)
// ============================================================================

const VALUE: usize = 0;
const THRESHOLD: usize = 1;
const DIFF: usize = 2;
const DIFF_BITS_START: usize = 3;
const NUM_DIFF_BITS: usize = 30;
const ACCUMULATOR: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 33
const STEP_INDEX: usize = ACCUMULATOR + 1; // 34
const ACC_PLUS_ONE: usize = STEP_INDEX + 1; // 35
const STEP_PLUS_ONE: usize = ACC_PLUS_ONE + 1; // 36
const TRACE_WIDTH: usize = STEP_PLUS_ONE + 1; // 37

const PI_NUM_STEPS: usize = 0;
const PUBLIC_INPUT_COUNT: usize = 1;

/// Build the temporal predicate CircuitDescriptor.
fn temporal_predicate_descriptor() -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    let mut columns = Vec::with_capacity(TRACE_WIDTH);
    columns.push(ColumnDef {
        name: "value".into(),
        index: VALUE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "threshold".into(),
        index: THRESHOLD,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "diff".into(),
        index: DIFF,
        kind: ColumnKind::Value,
    });
    for i in 0..NUM_DIFF_BITS {
        columns.push(ColumnDef {
            name: format!("diff_bit_{i}"),
            index: DIFF_BITS_START + i,
            kind: ColumnKind::Binary,
        });
    }
    columns.push(ColumnDef {
        name: "accumulator".into(),
        index: ACCUMULATOR,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "step_index".into(),
        index: STEP_INDEX,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "acc_plus_one".into(),
        index: ACC_PLUS_ONE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "step_plus_one".into(),
        index: STEP_PLUS_ONE,
        kind: ColumnKind::Value,
    });

    let mut constraints = Vec::new();

    // C1: diff = value - threshold => diff - value + threshold == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![DIFF],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![VALUE],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![THRESHOLD],
            },
        ],
    });

    // C2: Each diff_bit is binary
    for i in 0..NUM_DIFF_BITS {
        constraints.push(ConstraintExpr::Binary {
            col: DIFF_BITS_START + i,
        });
    }

    // C3: Bit reconstruction matches diff
    {
        let mut terms = Vec::with_capacity(NUM_DIFF_BITS + 1);
        let mut power_of_two = 1u32;
        for i in 0..NUM_DIFF_BITS {
            terms.push(PolyTerm {
                coeff: BabyBear::new(power_of_two),
                col_indices: vec![DIFF_BITS_START + i],
            });
            power_of_two = power_of_two.wrapping_mul(2);
        }
        terms.push(PolyTerm {
            coeff: neg_one,
            col_indices: vec![DIFF],
        });
        constraints.push(ConstraintExpr::Polynomial { terms });
    }

    // C4: High bit is zero (range proof: diff < 2^30)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![DIFF_BITS_START + NUM_DIFF_BITS - 1],
        }],
    });

    // C5: acc_plus_one = accumulator + 1
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![ACC_PLUS_ONE],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![ACCUMULATOR],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            },
        ],
    });

    // C6: step_plus_one = step_index + 1
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![STEP_PLUS_ONE],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![STEP_INDEX],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            },
        ],
    });

    // C7: Transition: next[accumulator] == local[acc_plus_one]
    constraints.push(ConstraintExpr::Transition {
        next_col: ACCUMULATOR,
        local_col: ACC_PLUS_ONE,
    });

    // C8: Transition: next[step_index] == local[step_plus_one]
    constraints.push(ConstraintExpr::Transition {
        next_col: STEP_INDEX,
        local_col: STEP_PLUS_ONE,
    });

    // Boundaries
    let boundaries = vec![
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: ACCUMULATOR,
            value: BabyBear::ONE,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: STEP_INDEX,
            value: BabyBear::ZERO,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: ACCUMULATOR,
            pi_index: PI_NUM_STEPS,
        },
    ];

    CircuitDescriptor {
        name: "pyana-temporal-predicate-dsl-v1".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// Generate a valid temporal predicate trace.
fn generate_temporal_trace(values: &[u32], threshold: u32) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_steps = values.len();
    assert!(num_steps >= 1);

    let padded_len = num_steps.next_power_of_two().max(2);
    let mut trace = Vec::with_capacity(padded_len);

    for step in 0..padded_len {
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        let val = if step < num_steps {
            values[step]
        } else {
            values[num_steps - 1]
        };

        row[VALUE] = BabyBear::new(val);
        row[THRESHOLD] = BabyBear::new(threshold);

        let diff = val.wrapping_sub(threshold);
        row[DIFF] = BabyBear::new(diff);

        for i in 0..NUM_DIFF_BITS {
            row[DIFF_BITS_START + i] = BabyBear::new((diff >> i) & 1);
        }

        let acc = (step + 1) as u32;
        row[ACCUMULATOR] = BabyBear::new(acc);
        row[STEP_INDEX] = BabyBear::new(step as u32);
        row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);
        row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);

        trace.push(row);
    }

    let public_inputs = vec![BabyBear::new(padded_len as u32)];
    (trace, public_inputs)
}

// ============================================================================
// Helper: encode 32 bytes as 8 BabyBear elements (4 bytes each, LE, reduced mod P)
// ============================================================================

fn bytes32_to_babybear(bytes: &[u8; 32]) -> Vec<BabyBear> {
    let mut result = Vec::with_capacity(8);
    for chunk in bytes.chunks(4) {
        let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        result.push(BabyBear(val % BABYBEAR_P));
    }
    result
}

/// Compute the effects hash the same way the executor does.
fn compute_effects_hash(turn: &pyana_turn::Turn) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-sovereign-effects-v1:");
    for root in &turn.call_forest.roots {
        hash_tree_effects(root, &mut hasher);
    }
    *hasher.finalize().as_bytes()
}

fn hash_tree_effects(tree: &pyana_turn::CallTree, hasher: &mut blake3::Hasher) {
    for effect in &tree.action.effects {
        hasher.update(&effect.hash());
    }
    for child in &tree.children {
        hash_tree_effects(child, hasher);
    }
}

// ============================================================================
// Test 1: Full DSL Pipeline — happy path
// ============================================================================

#[test]
fn test_dsl_pipeline_full_proof_carrying_turn() {
    // --- Step 1: Construct the CircuitDescriptor ---
    let descriptor = temporal_predicate_descriptor();
    assert!(descriptor.validate().is_ok());

    // --- Step 2: Create a CellProgram and deploy to ProgramRegistry ---
    let program = CellProgram::new(descriptor.clone(), 1);
    let vk_hash = program.vk_hash;

    let mut registry = ProgramRegistry::new();
    let deployed_vk = registry.deploy(program.clone()).unwrap();
    assert_eq!(deployed_vk, vk_hash);

    // --- Step 3: Create a TurnExecutor with that registry ---
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_program_registry(registry);

    // --- Step 4: Register a sovereign cell with the program's VK hash ---
    let agent_pub_key = *blake3::hash(b"dsl-pipeline-agent").as_bytes();
    let token_id = *blake3::hash(b"dsl-pipeline-domain").as_bytes();

    // Create the agent cell (needed for fee/nonce deduction by executor).
    let agent_cell = Cell::with_balance(agent_pub_key, token_id, 100_000);
    let agent_id = agent_cell.id;

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    // The sovereign cell is separate from the agent — it only stores a commitment.
    let sovereign_pub_key = *blake3::hash(b"dsl-pipeline-sovereign").as_bytes();
    let sovereign_token_id = *blake3::hash(b"dsl-pipeline-sovereign-token").as_bytes();
    let sovereign_cell_id = CellId::derive_raw(&sovereign_pub_key, &sovereign_token_id);

    // Initial commitment for the sovereign cell (arbitrary; represents "old state").
    let old_commitment = *blake3::hash(b"initial-state-commitment").as_bytes();

    // Register with VK hash binding.
    ledger
        .register_sovereign_cell_with_vk(
            sovereign_cell_id,
            old_commitment,
            0,    // current_height
            1000, // ttl_blocks
            Some(vk_hash),
        )
        .unwrap();

    // Verify registration.
    assert!(ledger.is_sovereign_registered(&sovereign_cell_id));

    // --- Step 5: Generate a valid trace (3 steps, value=100, threshold=50) ---
    let values = vec![100u32, 100, 100];
    let threshold = 50u32;
    let (trace, circuit_public_inputs) = generate_temporal_trace(&values, threshold);
    assert_eq!(trace.len(), 4); // padded to next power of 2

    // Verify constraints evaluate to zero on the trace (sanity check).
    let circuit = DslCircuit::new(descriptor.clone());
    let alpha = BabyBear::new(7);
    for i in 0..trace.len() - 1 {
        let result =
            circuit.eval_constraints(&trace[i], &trace[i + 1], &circuit_public_inputs, alpha);
        assert_eq!(result, BabyBear::ZERO, "Constraint nonzero at row {i}");
    }

    // --- Step 6: Prove using DslCircuit + stark::prove ---
    // The executor expects 32 public inputs (8 BabyBear per: old_commitment,
    // new_commitment, effects_hash, cell_id_hash). The temporal predicate circuit
    // only uses 1 public input (num_steps). For the executor's verification to pass,
    // we must prove with the full 32-element public inputs that the executor will
    // reconstruct. The circuit's boundary constraint binds the last pi element
    // (pi[0]) but the circuit only declares `public_input_count: 1`. Since the
    // executor calls verify_transition which uses the full pi vector, we need
    // to ensure the proof is generated with those same public inputs.
    //
    // However, the CellProgram.verify_transition rebuilds the DslCircuit which
    // only checks boundary constraints referencing pi[0]. The extra pi elements
    // (indices 1..31) are unused by the circuit constraints but must be present
    // and match between prove and verify for the STARK commitment to hold.
    //
    // Strategy: We build a descriptor with public_input_count=32 (matching what
    // the executor provides), and set the trace's last-row boundary to pi[0]
    // which happens to hold the first element of old_commitment. We then ensure
    // the trace's accumulator final value matches that.
    //
    // Actually, let's step back: the executor's verify_and_commit_proof calls
    // program.verify_transition(public_inputs, proof_bytes) where public_inputs
    // is the 32-element vector. The CellProgram.verify_transition deserializes the
    // proof and calls stark::verify(&circuit, &proof, public_inputs). The circuit's
    // boundary constraints only reference pi[0], but the STARK commitment includes
    // ALL public inputs in its Fiat-Shamir transcript. So the proof must be generated
    // with the EXACT same public inputs vector.
    //
    // Solution: Build a modified descriptor with public_input_count=32, and generate
    // the proof with the executor's expected public inputs. The last-row boundary
    // constraint on accumulator will reference pi[0] which is old_commitment[0..4]
    // (the first BabyBear of old_commitment). We must set the trace's final accumulator
    // to that value.
    //
    // Simpler solution: use a descriptor with NO boundary constraints referencing
    // public inputs, and set public_input_count=32. Then the proof just needs the
    // constraints to be satisfied, and the public inputs are only bound via Fiat-Shamir.
    //
    // Actually the cleanest approach: build the Turn first to know what effects_hash
    // and cell_id_hash will be, then construct public_inputs, then prove with those.
    // The circuit's internal constraints (temporal predicate) will be satisfied by
    // the trace regardless of public inputs (they only use pi[0] in the boundary
    // constraint for accumulator). So we need to either:
    // a) Remove the pi-binding boundary and use only Fixed boundaries, OR
    // b) Make pi[0] == padded_len (4) so the boundary constraint holds.
    //
    // Let's take approach (b): set pi[0] in the 32-element vector to the padded
    // trace length. This means old_commitment's first 4 bytes must encode the value 4
    // (mod BABYBEAR_P). We'll choose old_commitment accordingly.

    // Choose old_commitment such that its first 4 bytes (LE u32 mod P) == padded_len.
    let padded_len = 4u32;
    let mut chosen_old_commitment = [0u8; 32];
    chosen_old_commitment[0..4].copy_from_slice(&padded_len.to_le_bytes());
    // Fill the rest with recognizable data.
    chosen_old_commitment[4..].copy_from_slice(&blake3::hash(b"old-state-rest").as_bytes()[..28]);

    // Re-register the sovereign cell with the chosen commitment.
    // First deregister, then re-register.
    ledger
        .deregister_sovereign_cell(&sovereign_cell_id)
        .unwrap();
    ledger
        .register_sovereign_cell_with_vk(
            sovereign_cell_id,
            chosen_old_commitment,
            0,
            1000,
            Some(vk_hash),
        )
        .unwrap();

    // Choose new_commitment (arbitrary, different from old).
    let new_commitment = *blake3::hash(b"new-state-after-transition").as_bytes();

    // Build the Turn to compute effects_hash.
    let mut turn_builder = TurnBuilder::new(agent_id, 0);
    turn_builder.set_fee(0);
    {
        // Add a dummy action so the call forest is non-empty.
        let action = turn_builder.action(sovereign_cell_id, "temporal_check");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: sovereign_cell_id,
            index: 0,
            value: new_commitment,
        });
    }
    let mut turn = turn_builder.build();

    // Compute effects hash from the turn's call forest (matches executor logic).
    let effects_hash = compute_effects_hash(&turn);

    // Compute cell_id_hash.
    let cell_id_hash = *blake3::hash(sovereign_cell_id.as_bytes()).as_bytes();

    // Build the 32-element public inputs vector the executor will reconstruct.
    let mut full_public_inputs: Vec<BabyBear> = Vec::with_capacity(32);
    full_public_inputs.extend(bytes32_to_babybear(&chosen_old_commitment));
    full_public_inputs.extend(bytes32_to_babybear(&new_commitment));
    full_public_inputs.extend(bytes32_to_babybear(&effects_hash));
    full_public_inputs.extend(bytes32_to_babybear(&cell_id_hash));
    assert_eq!(full_public_inputs.len(), 32);

    // Verify pi[0] == padded_len (4) so the boundary constraint holds.
    assert_eq!(
        full_public_inputs[0],
        BabyBear::new(padded_len),
        "pi[0] must equal the padded trace length for the boundary constraint"
    );

    // Now we need a descriptor with public_input_count=32 so it accepts 32 public inputs.
    let mut deploy_descriptor = temporal_predicate_descriptor();
    deploy_descriptor.public_input_count = 32;

    // Rebuild the program with the updated descriptor.
    let program32 = CellProgram::new(deploy_descriptor.clone(), 1);
    let vk_hash32 = program32.vk_hash;

    // Re-deploy to a fresh registry with the 32-pi descriptor.
    let mut registry32 = ProgramRegistry::new();
    registry32.deploy(program32.clone()).unwrap();

    // Update executor registry.
    executor.set_program_registry(registry32);

    // Re-register sovereign cell with the new VK hash.
    ledger
        .deregister_sovereign_cell(&sovereign_cell_id)
        .unwrap();
    ledger
        .register_sovereign_cell_with_vk(
            sovereign_cell_id,
            chosen_old_commitment,
            0,
            1000,
            Some(vk_hash32),
        )
        .unwrap();

    // Generate the STARK proof with the DslCircuit + full_public_inputs.
    let circuit32 = DslCircuit::new(deploy_descriptor);
    let proof = stark::prove(&circuit32, &trace, &full_public_inputs);

    // Sanity: verify locally before submitting.
    let local_verify = stark::verify(&circuit32, &proof, &full_public_inputs);
    assert!(
        local_verify.is_ok(),
        "Local STARK verify failed: {:?}",
        local_verify.err()
    );

    // Serialize proof to bytes.
    let proof_bytes = stark::proof_to_bytes(&proof);
    assert!(
        proof_bytes.len() > 100,
        "Proof should be substantial: {} bytes",
        proof_bytes.len()
    );

    // --- Step 7: Build a Turn with execution_proof ---
    turn.execution_proof = Some(proof_bytes.clone());
    turn.execution_proof_cell = Some(sovereign_cell_id);
    turn.execution_proof_new_commitment = Some(new_commitment);

    // --- Step 8: Execute the turn ---
    let result = executor.execute(&turn, &mut ledger);

    // --- Step 9: Assert success ---
    match &result {
        TurnResult::Committed {
            computrons_used, ..
        } => {
            assert_eq!(
                *computrons_used, 0,
                "Proof-carrying turns use zero computrons"
            );
        }
        TurnResult::Rejected { reason, .. } => {
            panic!("Turn was rejected: {:?}", reason);
        }
        other => panic!("Unexpected result: {:?}", other),
    }

    // Verify the sovereign commitment was updated.
    let updated = ledger
        .get_sovereign_registration(&sovereign_cell_id)
        .unwrap();
    assert_eq!(
        updated.commitment, new_commitment,
        "Commitment should be updated to new_commitment after proof-carrying turn"
    );
}

// ============================================================================
// Test 2: Wrong proof rejected
// ============================================================================

#[test]
fn test_dsl_pipeline_wrong_proof_rejected() {
    // Setup: same as happy path but tamper with the proof bytes.
    let mut deploy_descriptor = temporal_predicate_descriptor();
    deploy_descriptor.public_input_count = 32;

    let program = CellProgram::new(deploy_descriptor.clone(), 1);
    let vk_hash = program.vk_hash;

    let mut registry = ProgramRegistry::new();
    registry.deploy(program.clone()).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_program_registry(registry);

    let agent_pub_key = *blake3::hash(b"dsl-pipeline-agent-bad-proof").as_bytes();
    let token_id = *blake3::hash(b"dsl-pipeline-domain-bad-proof").as_bytes();
    let agent_cell = Cell::with_balance(agent_pub_key, token_id, 100_000);
    let agent_id = agent_cell.id;

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let sovereign_pub_key = *blake3::hash(b"dsl-pipeline-sov-bad-proof").as_bytes();
    let sovereign_token_id = *blake3::hash(b"dsl-pipeline-sov-token-bad-proof").as_bytes();
    let sovereign_cell_id = CellId::derive_raw(&sovereign_pub_key, &sovereign_token_id);

    let padded_len = 4u32;
    let mut old_commitment = [0u8; 32];
    old_commitment[0..4].copy_from_slice(&padded_len.to_le_bytes());
    old_commitment[4..].copy_from_slice(&blake3::hash(b"bad-proof-old-rest").as_bytes()[..28]);

    ledger
        .register_sovereign_cell_with_vk(sovereign_cell_id, old_commitment, 0, 1000, Some(vk_hash))
        .unwrap();

    let new_commitment = *blake3::hash(b"bad-proof-new-state").as_bytes();

    // Build turn.
    let mut turn_builder = TurnBuilder::new(agent_id, 0);
    turn_builder.set_fee(0);
    {
        let action = turn_builder.action(sovereign_cell_id, "temporal_check");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: sovereign_cell_id,
            index: 0,
            value: new_commitment,
        });
    }
    let mut turn = turn_builder.build();

    let effects_hash = compute_effects_hash(&turn);
    let cell_id_hash = *blake3::hash(sovereign_cell_id.as_bytes()).as_bytes();

    let mut full_pi: Vec<BabyBear> = Vec::with_capacity(32);
    full_pi.extend(bytes32_to_babybear(&old_commitment));
    full_pi.extend(bytes32_to_babybear(&new_commitment));
    full_pi.extend(bytes32_to_babybear(&effects_hash));
    full_pi.extend(bytes32_to_babybear(&cell_id_hash));

    // Generate a valid proof first.
    let values = vec![100u32, 100, 100];
    let threshold = 50u32;
    let (trace, _) = generate_temporal_trace(&values, threshold);

    let circuit = DslCircuit::new(deploy_descriptor);
    let proof = stark::prove(&circuit, &trace, &full_pi);
    let mut proof_bytes = stark::proof_to_bytes(&proof);

    // Tamper with the proof bytes (flip some bytes in the middle).
    let mid = proof_bytes.len() / 2;
    proof_bytes[mid] ^= 0xFF;
    proof_bytes[mid + 1] ^= 0xAB;
    proof_bytes[mid + 2] ^= 0xCD;

    turn.execution_proof = Some(proof_bytes);
    turn.execution_proof_cell = Some(sovereign_cell_id);
    turn.execution_proof_new_commitment = Some(new_commitment);

    let result = executor.execute(&turn, &mut ledger);

    match result {
        TurnResult::Rejected { reason, .. } => {
            let reason_str = format!("{:?}", reason);
            assert!(
                reason_str.contains("Proof")
                    || reason_str.contains("proof")
                    || reason_str.contains("verification")
                    || reason_str.contains("Verification")
                    || reason_str.contains("deserial")
                    || reason_str.contains("Invalid"),
                "Expected proof-related rejection, got: {}",
                reason_str
            );
        }
        TurnResult::Committed { .. } => {
            panic!("Tampered proof should have been rejected!");
        }
        other => panic!("Unexpected result: {:?}", other),
    }

    // Commitment should NOT have been updated.
    let reg = ledger
        .get_sovereign_registration(&sovereign_cell_id)
        .unwrap();
    assert_eq!(
        reg.commitment, old_commitment,
        "Commitment must not change on rejected proof"
    );
}

// ============================================================================
// Test 3: Wrong VK rejected
// ============================================================================

#[test]
fn test_dsl_pipeline_wrong_vk_rejected() {
    // Deploy a program, but register the cell with a DIFFERENT VK hash.
    let mut deploy_descriptor = temporal_predicate_descriptor();
    deploy_descriptor.public_input_count = 32;

    let program = CellProgram::new(deploy_descriptor.clone(), 1);
    let _real_vk_hash = program.vk_hash;

    let mut registry = ProgramRegistry::new();
    registry.deploy(program.clone()).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_program_registry(registry);

    let agent_pub_key = *blake3::hash(b"dsl-pipeline-agent-wrong-vk").as_bytes();
    let token_id = *blake3::hash(b"dsl-pipeline-domain-wrong-vk").as_bytes();
    let agent_cell = Cell::with_balance(agent_pub_key, token_id, 100_000);
    let agent_id = agent_cell.id;

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let sovereign_pub_key = *blake3::hash(b"dsl-pipeline-sov-wrong-vk").as_bytes();
    let sovereign_token_id = *blake3::hash(b"dsl-pipeline-sov-token-wrong-vk").as_bytes();
    let sovereign_cell_id = CellId::derive_raw(&sovereign_pub_key, &sovereign_token_id);

    let padded_len = 4u32;
    let mut old_commitment = [0u8; 32];
    old_commitment[0..4].copy_from_slice(&padded_len.to_le_bytes());
    old_commitment[4..].copy_from_slice(&blake3::hash(b"wrong-vk-old-rest").as_bytes()[..28]);

    // Register with a WRONG VK hash (not deployed in registry).
    let wrong_vk_hash = *blake3::hash(b"this-vk-does-not-exist").as_bytes();
    ledger
        .register_sovereign_cell_with_vk(
            sovereign_cell_id,
            old_commitment,
            0,
            1000,
            Some(wrong_vk_hash),
        )
        .unwrap();

    let new_commitment = *blake3::hash(b"wrong-vk-new-state").as_bytes();

    // Build turn.
    let mut turn_builder = TurnBuilder::new(agent_id, 0);
    turn_builder.set_fee(0);
    {
        let action = turn_builder.action(sovereign_cell_id, "temporal_check");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: sovereign_cell_id,
            index: 0,
            value: new_commitment,
        });
    }
    let mut turn = turn_builder.build();

    let effects_hash = compute_effects_hash(&turn);
    let cell_id_hash = *blake3::hash(sovereign_cell_id.as_bytes()).as_bytes();

    let mut full_pi: Vec<BabyBear> = Vec::with_capacity(32);
    full_pi.extend(bytes32_to_babybear(&old_commitment));
    full_pi.extend(bytes32_to_babybear(&new_commitment));
    full_pi.extend(bytes32_to_babybear(&effects_hash));
    full_pi.extend(bytes32_to_babybear(&cell_id_hash));

    // Generate a valid proof (using the real circuit).
    let values = vec![100u32, 100, 100];
    let threshold = 50u32;
    let (trace, _) = generate_temporal_trace(&values, threshold);

    let circuit = DslCircuit::new(deploy_descriptor);
    let proof = stark::prove(&circuit, &trace, &full_pi);
    let proof_bytes = stark::proof_to_bytes(&proof);

    turn.execution_proof = Some(proof_bytes);
    turn.execution_proof_cell = Some(sovereign_cell_id);
    turn.execution_proof_new_commitment = Some(new_commitment);

    let result = executor.execute(&turn, &mut ledger);

    match result {
        TurnResult::Rejected { reason, .. } => {
            let reason_str = format!("{:?}", reason);
            assert!(
                reason_str.contains("no matching program")
                    || reason_str.contains("verification_key_hash")
                    || reason_str.contains("ProofVerificationFailed"),
                "Expected VK-not-found rejection, got: {}",
                reason_str
            );
        }
        TurnResult::Committed { .. } => {
            panic!("Turn with wrong VK hash should have been rejected!");
        }
        other => panic!("Unexpected result: {:?}", other),
    }

    // Commitment should NOT have been updated.
    let reg = ledger
        .get_sovereign_registration(&sovereign_cell_id)
        .unwrap();
    assert_eq!(
        reg.commitment, old_commitment,
        "Commitment must not change on wrong VK"
    );
}
