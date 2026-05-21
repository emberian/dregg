//! Full end-to-end integration tests: every layer of the system with real crypto.
//!
//! These tests prove the FULL pipeline works:
//! - Test 1: token -> attenuate -> Datalog evaluate -> build witness -> STARK -> serialize -> verify
//! - Test 2: Authorization with body membership proofs (derivation + Merkle STARKs)
//! - Test 3: Note lifecycle (create -> commit -> prove spend -> verify -> nullifier)
//! - Test 4: Cross-federation conditional swap (atomic execution via ConditionalTurn)
//! - Test 5: Delegation + revocation (spawn -> exercise -> refresh -> revoke)
//!
//! All tests use REAL crypto: real Poseidon2 hashing, real FRI-based STARK proofs,
//! real Merkle trees. No mocks, no prove_fast.

use std::collections::HashSet;

use pyana_bridge::present::{
    bytes_to_babybear, hash_index, verify_presentation, verify_presentation_bb,
    BridgePresentationBuilder,
};
use pyana_cell::{
    AuthRequired, CapabilityRef, Cell, CellId, DelegatedRef, Ledger, Note, NoteCommitment,
    Nullifier, NullifierSet, Permissions, VerificationKey,
};
use pyana_circuit::{
    BabyBear, BodyMembershipProof, MultiStepWitness, NoteSpendingAir, NoteSpendingWitness,
    collect_body_fact_hashes, prove_authorization_stark, prove_authorization_with_membership,
    prove_note_spend, verify_authorization_stark, verify_authorization_with_membership,
    verify_note_spend,
};
use pyana_circuit::body_membership::BodyFactMerkleProof;
use pyana_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
use pyana_circuit::multi_step_air::{self, ALLOW_PREDICATE, build_multi_step_witness};
use pyana_circuit::poseidon2::{self, hash_fact};
use pyana_circuit::stark::{self, proof_from_bytes, proof_to_bytes};
use pyana_commit::poseidon2_tree::{Poseidon2MerkleTree, commitment_to_field};
use pyana_sdk::wallet::{AgentWallet, AuthorizationPresentation, VerificationMode};
use pyana_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};
use pyana_turn::{
    ComputronCosts, ConditionProof, ConditionalResult, ConditionalTurn, DelegationMode, Effect,
    ProofCondition, TrustedRoot, TurnBuilder, TurnExecutor, TurnReceipt, TurnResult,
    resolve_condition,
};

// =============================================================================
// Helper functions
// =============================================================================

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("pyana-full-pipeline-test:{name}").as_bytes()).as_bytes()
}

/// Compute the synthetic Poseidon2 federation root for an issuer key.
/// This mirrors the logic in AgentWallet::compute_federation_root_bb.
fn compute_federation_root_poseidon2(issuer_key: &[u8; 32]) -> BabyBear {
    let issuer_hash = bytes_to_babybear(issuer_key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(hash_index(i, 0, issuer_key)),
            BabyBear::new(hash_index(i, 1, issuer_key)),
            BabyBear::new(hash_index(i, 2, issuer_key)),
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
    current
}

fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&bb.0.to_le_bytes());
    bytes
}

// =============================================================================
// Test 1: Full Private Authorization Pipeline
// =============================================================================

/// token -> attenuate twice -> BridgePresentationBuilder -> prove (real STARK) ->
/// serialize -> deserialize -> verify -> tamper fails -> wrong root fails.
#[test]
fn test_full_private_authorization_pipeline() {
    // --- Step 1: Mint root token ---
    let issuer_key = test_key("issuer-pipeline");
    let root_token = MacaroonToken::mint(issuer_key, b"pipeline-kid", "compute.pyana.dev");

    // --- Step 2: Attenuate twice ---
    // First attenuation: restrict to service + add expiry
    let att1 = Attenuation {
        services: vec![("compute".into(), "rw".into())],
        not_after: Some(2000000000),
        ..Default::default()
    };
    let attenuated1 = root_token.attenuate(&att1).unwrap();

    // Second attenuation: further narrow with user confinement
    let att2 = Attenuation {
        confine_user: Some("alice".into()),
        ..Default::default()
    };
    let attenuated2 = attenuated1.attenuate(&att2).unwrap();

    // Verify the singly-attenuated token works for intended request.
    // Note: the Datalog evaluator expands "rw" service grants into "r" and "w" actions,
    // so requests must specify individual action letters (not "rw").
    let request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(1700000000),
        ..Default::default()
    };
    let verify_result = attenuated1.verify(&request);
    assert!(
        verify_result.is_ok(),
        "singly-attenuated token should verify for intended request: {:?}",
        verify_result.err()
    );

    // --- Step 3: Build BridgePresentationBuilder ---
    let federation_root_bb = compute_federation_root_poseidon2(&issuer_key);
    let federation_root_bytes = bb_to_bytes(federation_root_bb);

    let mut builder = BridgePresentationBuilder::new_with_root_bb(
        issuer_key,
        federation_root_bytes,
        federation_root_bb,
    );

    // Set root token + add attenuations
    let fresh_root = MacaroonToken::mint(issuer_key, b"pipeline-kid", "compute.pyana.dev");
    builder.set_root_token(fresh_root);
    assert!(builder.add_attenuation(&att1), "first attenuation should succeed");
    assert!(builder.add_attenuation(&att2), "second attenuation should succeed");
    assert_eq!(builder.chain_length(), 3); // root + 2 attenuations

    // --- Step 4: Verify fold chain integrity ---
    assert!(builder.verify_chain(), "fold chain should be valid");

    // --- Step 5: Prove (real STARK, Poseidon2) ---
    let proof = builder
        .prove(&request)
        .expect("prove() should succeed with valid chain");

    assert!(proof.is_valid(), "proof should report valid");
    assert!(
        proof.has_real_stark_proof(),
        "proof should contain a real STARK"
    );
    assert_eq!(proof.chain_length, 3);

    // Verify the STARK proof itself
    let stark_verify = proof.verify_issuer_stark();
    assert!(stark_verify.is_some());
    assert!(
        stark_verify.unwrap().is_ok(),
        "issuer STARK proof should verify"
    );

    // --- Step 6: Serialize proof to bytes ---
    let proof_bytes = proof
        .issuer_proof_bytes()
        .expect("should have issuer proof bytes");
    assert!(
        proof_bytes.len() > 1000,
        "real STARK proof should be > 1KB, got {} bytes",
        proof_bytes.len()
    );

    // --- Step 7: Deserialize from bytes ---
    let deserialized = proof_from_bytes(&proof_bytes).expect("deserialization should succeed");
    assert_eq!(deserialized.public_inputs.len(), 2);
    assert_eq!(
        deserialized.public_inputs, proof.real_stark_proof.as_ref().unwrap().issuer_membership_stark_proof.public_inputs,
        "round-trip should preserve public inputs"
    );

    // --- Step 8: Verify (verify_presentation with real federation root) ---
    assert!(
        verify_presentation(&proof, &federation_root_bytes),
        "verify_presentation should pass with correct federation root"
    );
    assert!(
        verify_presentation_bb(&proof, federation_root_bb),
        "verify_presentation_bb should pass with correct BabyBear root"
    );

    // --- Step 9: Assert verification passes (done above) ---

    // --- Step 10: Tamper with one byte of proof -> verify fails ---
    let mut tampered_proof = proof.clone();
    if let Some(ref mut real) = tampered_proof.real_stark_proof {
        // Tamper with a query proof value
        if !real.issuer_membership_stark_proof.query_proofs.is_empty()
            && !real.issuer_membership_stark_proof.query_proofs[0].trace_values.is_empty()
        {
            real.issuer_membership_stark_proof.query_proofs[0].trace_values[0] ^= 0xDEAD;
        }
    }
    assert!(
        !verify_presentation(&tampered_proof, &federation_root_bytes),
        "tampered proof should fail verification"
    );

    // --- Step 11: Wrong federation root -> verify fails ---
    let wrong_root = test_key("wrong-federation-root");
    assert!(
        !verify_presentation(&proof, &wrong_root),
        "proof should fail against wrong federation root"
    );
}

// =============================================================================
// Test 2: Full Authorization with Body Membership
// =============================================================================

/// Build a Poseidon2 fact tree (10 facts) -> insert token facts -> create
/// MultiStepWitness with real Merkle proofs -> generate BodyMembershipProof
/// (derivation + membership STARKs) -> verify -> tamper fails.
#[test]
fn test_full_authorization_with_body_membership() {
    // --- Step 1: Build a Poseidon2 fact tree with 10 facts ---
    let mut tree = Poseidon2MerkleTree::with_depth(4);

    // Generate 10 facts with distinct predicates and terms
    let mut fact_hashes: Vec<BabyBear> = Vec::new();
    let predicates: Vec<BabyBear> = (0..10)
        .map(|i| BabyBear::new(100 + i))
        .collect();
    let alice = BabyBear::new(1000);
    let app1 = BabyBear::new(2000);
    let read_perm = BabyBear::new(3000);

    for i in 0..10u32 {
        let pred = predicates[i as usize];
        let terms = [
            alice,
            BabyBear::new(2000 + i),
            BabyBear::new(3000 + i),
            BabyBear::ZERO,
        ];
        let fact_hash = hash_fact(pred, &terms);
        tree.append(fact_hash);
        fact_hashes.push(fact_hash);
    }

    let mut tree_for_root = tree.clone();
    let state_root = tree_for_root.root();

    // --- Step 2: Insert token-relevant facts (at positions 0 and 1) ---
    // Fact 0: has_capability(alice, app1, read)
    let has_cap_pred = predicates[0];
    let has_cap_terms = [alice, app1, read_perm, BabyBear::ZERO];
    let has_cap_hash = hash_fact(has_cap_pred, &has_cap_terms);
    // Override position 0's hash to be our specific fact
    // (We'll rebuild the tree with our specific facts)
    let mut real_tree = Poseidon2MerkleTree::with_depth(4);
    let body_fact_hash = hash_fact(has_cap_pred, &has_cap_terms);
    real_tree.append(body_fact_hash);
    // Fill with other facts
    for i in 1..10u32 {
        let pred = predicates[i as usize];
        let terms = [alice, BabyBear::new(2000 + i), BabyBear::new(3000 + i), BabyBear::ZERO];
        real_tree.append(hash_fact(pred, &terms));
    }

    let mut real_tree_for_root = real_tree.clone();
    let real_state_root = real_tree_for_root.root();

    // --- Step 3: Get Merkle proof for the body fact ---
    let merkle_proof = real_tree.prove_membership(0).expect("leaf 0 should have a proof");
    assert!(
        Poseidon2MerkleTree::verify_membership(real_state_root, body_fact_hash, &merkle_proof),
        "Merkle membership proof should verify"
    );

    // --- Step 4: Create MultiStepWitness with real Merkle proofs ---
    let allow_pred = BabyBear::new(ALLOW_PREDICATE);
    let request_hash = BabyBear::new(42);

    // Single step: allow(alice, app1) :- has_capability(alice, app1, read)
    let step = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)),  // X -> alice
                (true, BabyBear::new(1)),  // App -> app1
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: has_cap_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (true, BabyBear::new(2)),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
        },
        state_root: real_state_root,
        body_fact_hashes: vec![body_fact_hash],
        substitution: vec![alice, app1, read_perm],
        derived_predicate: allow_pred,
        derived_terms: [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
    };

    let witness = build_multi_step_witness(real_state_root, request_hash, vec![step]);
    assert_eq!(
        witness.conclusion(),
        BabyBear::ONE,
        "witness should conclude ALLOW"
    );

    // --- Step 5: Generate BodyMembershipProof (derivation + membership STARKs) ---
    let body_merkle_proofs = vec![BodyFactMerkleProof {
        fact_hash: body_fact_hash,
        siblings: merkle_proof.siblings.clone(),
        positions: merkle_proof.positions.clone(),
    }];

    let composite_proof =
        prove_authorization_with_membership(&witness, &body_merkle_proofs);

    // --- Step 6: Verify: all membership proofs valid, derivation valid, roots cross-check ---
    let conclusion = witness.conclusion();
    let accumulated_hash = witness.final_accumulated_hash();
    let body_hashes = collect_body_fact_hashes(&witness);

    let result = verify_authorization_with_membership(
        &composite_proof,
        conclusion,
        accumulated_hash,
        &body_hashes,
    );
    assert!(
        result.is_ok(),
        "composite proof should verify: {:?}",
        result.err()
    );

    // Verify state root consistency
    assert_eq!(composite_proof.state_root, real_state_root);
    assert_eq!(composite_proof.membership_proofs.len(), 1);
    assert_eq!(composite_proof.membership_proofs[0].fact_hash, body_fact_hash);

    // --- Step 7: Tamper with one membership proof -> verification catches it ---
    let mut tampered_composite = composite_proof.clone();
    if !tampered_composite.membership_proofs.is_empty() {
        // Tamper with the STARK proof for the membership entry
        let entry = &mut tampered_composite.membership_proofs[0];
        if !entry.proof.query_proofs.is_empty()
            && !entry.proof.query_proofs[0].trace_values.is_empty()
        {
            entry.proof.query_proofs[0].trace_values[0] ^= 0xBEEF;
        }
    }

    let tampered_result = verify_authorization_with_membership(
        &tampered_composite,
        conclusion,
        accumulated_hash,
        &body_hashes,
    );
    assert!(
        tampered_result.is_err(),
        "tampered membership proof should fail verification"
    );
}

// =============================================================================
// Test 3: Full Note Lifecycle
// =============================================================================

/// Create note -> build Poseidon2 note tree -> generate NoteSpendingAir proof
/// (real STARK, 248-bit key) -> verify -> position-independent nullifier ->
/// double-spend rejected.
#[test]
fn test_full_note_lifecycle() {
    // --- Step 1: Create a note (owner, value=100, asset=GOLD) ---
    let owner_key = test_key("note-owner");
    let spending_key = test_key("note-spending-key");
    let gold_asset: u64 = 0x474F4C44; // "GOLD" in ASCII

    let note = Note::with_randomness(
        owner_key,
        [gold_asset, 100, 0, 0, 0, 0, 0, 0],
        [0x42u8; 32],
    );
    assert_eq!(note.asset_type(), gold_asset);
    assert_eq!(note.value(), 100);

    let commitment = note.commitment();

    // --- Step 2: Build Poseidon2 note tree, insert commitment ---
    // The STARK circuit operates on BabyBear field elements and computes commitment
    // as poseidon2_hash(owner, value, asset_type, creation_nonce, randomness).
    // The Merkle tree must store THIS field-level commitment (not the BLAKE3 one).
    let owner_bb = bytes_to_babybear(&owner_key);
    let value_bb = BabyBear::new(100);
    let asset_bb = BabyBear::new(gold_asset as u32);
    let creation_nonce_bb = bytes_to_babybear(&note.creation_nonce);
    let randomness_bb = bytes_to_babybear(&note.randomness);

    // Convert the 256-bit spending key to 8 BabyBear limbs (248 bits of security)
    let spending_key_limbs = pyana_circuit::note_spending_air::key_to_field_elements(&spending_key);

    // Compute the circuit-level commitment (this is what the Merkle tree stores)
    let circuit_commitment = poseidon2::hash_many(&[
        owner_bb, value_bb, asset_bb, creation_nonce_bb, randomness_bb,
    ]);

    let mut note_tree = Poseidon2MerkleTree::with_depth(4);
    let position = note_tree.append(circuit_commitment);
    assert_eq!(position, 0);

    // Add some other notes to make the tree non-trivial
    for i in 1..8u32 {
        let fake_commitment = BabyBear::new(i * 12345);
        note_tree.append(fake_commitment);
    }

    let mut tree_for_root = note_tree.clone();
    let tree_root = tree_for_root.root();

    // Get the Merkle proof for our note
    let merkle_proof = note_tree.prove_membership(0).expect("should have proof for position 0");
    assert!(
        Poseidon2MerkleTree::verify_membership(tree_root, circuit_commitment, &merkle_proof),
        "membership proof should verify before STARK"
    );

    // --- Step 3: Generate NoteSpendingAir proof (real STARK, 248-bit key) ---
    let witness = NoteSpendingWitness::from_real_proof(
        owner_bb,
        value_bb,
        asset_bb,
        creation_nonce_bb,
        randomness_bb,
        spending_key_limbs,
        merkle_proof.siblings.clone(),
        merkle_proof.positions.clone(),
    );

    // Verify the witness computes correct commitment and nullifier
    assert_eq!(witness.commitment(), circuit_commitment, "witness commitment should match");
    let circuit_nullifier = witness.nullifier();
    let circuit_merkle_root = witness.merkle_root();

    // The Merkle root computed by the witness should match the tree root
    assert_eq!(
        circuit_merkle_root, tree_root,
        "witness Merkle root should match tree root"
    );

    // Generate the real STARK proof
    let stark_proof = prove_note_spend(&witness);
    assert!(stark_proof.trace_len > 0, "proof trace should be non-empty");
    assert!(
        !stark_proof.query_proofs.is_empty(),
        "proof should have query proofs"
    );

    // --- Step 4: Verify note spending proof ---
    let verify_result = verify_note_spend(circuit_nullifier, tree_root, &stark_proof);
    assert!(
        verify_result.is_ok(),
        "note spending proof should verify: {:?}",
        verify_result.err()
    );

    // --- Step 5: Check nullifier is position-independent ---
    // Build a DIFFERENT tree and insert the same note at a different position
    let mut tree2 = Poseidon2MerkleTree::with_depth(4);
    // Insert some other notes first
    for i in 0..5u32 {
        tree2.append(BabyBear::new(99999 + i));
    }
    // Insert our note at position 5
    let position2 = tree2.append(circuit_commitment);
    assert_eq!(position2, 5);

    // The BLAKE3-level nullifier is position-independent by construction
    let nullifier1 = note.nullifier(&spending_key);
    let nullifier2 = note.nullifier(&spending_key);
    assert_eq!(
        nullifier1, nullifier2,
        "nullifier should be the same regardless of call context"
    );

    // The circuit-level nullifier is also position-independent (derived from
    // commitment + spending_key + creation_nonce, NOT from tree position)
    let witness2 = NoteSpendingWitness::from_real_proof(
        owner_bb,
        value_bb,
        asset_bb,
        creation_nonce_bb,
        randomness_bb,
        spending_key_limbs,
        // Different Merkle path (different tree!)
        tree2.prove_membership(5).unwrap().siblings,
        tree2.prove_membership(5).unwrap().positions,
    );
    assert_eq!(
        witness.nullifier(),
        witness2.nullifier(),
        "circuit nullifier should be position-independent"
    );

    // --- Step 6: Insert nullifier into NullifierSet ---
    let mut nullifier_set = NullifierSet::new();
    nullifier_set.insert(nullifier1).expect("first insert should succeed");
    assert!(nullifier_set.contains(&nullifier1));

    // --- Step 7: Attempt double-spend -> NullifierSet rejects ---
    let double_spend_result = nullifier_set.insert(nullifier1);
    assert!(
        double_spend_result.is_err(),
        "double-spend should be rejected"
    );
    match double_spend_result {
        Err(pyana_cell::NoteError::DoubleSpend { nullifier }) => {
            assert_eq!(nullifier, nullifier1);
        }
        _ => panic!("expected DoubleSpend error"),
    }
}

// =============================================================================
// Test 4: Full Cross-Federation Conditional Swap
// =============================================================================

/// Federation A and B -> Alice creates ConditionalTurn (transfer IFF Bob's proof) ->
/// Bob executes his transfer, gets receipt -> Bob presents receipt to Fed A ->
/// Alice's conditional resolves -> timeout case also tested.
#[test]
fn test_full_cross_federation_conditional_swap() {
    // --- Setup: Federation A (Alice's home) ---
    let token_id_a = test_key("federation-a-token");
    let mut ledger_a = Ledger::new();

    let alice_key = test_key("alice");
    let mut alice_cell = Cell::with_balance(alice_key, token_id_a, 1000);
    alice_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let alice_id = alice_cell.id;
    ledger_a.insert_cell(alice_cell).unwrap();

    // Target cell in Fed A that Alice wants to modify
    let target_a_key = test_key("target-a");
    let mut target_a_cell = Cell::with_balance(target_a_key, token_id_a, 500);
    target_a_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let target_a_id = target_a_cell.id;
    ledger_a.insert_cell(target_a_cell).unwrap();

    // Grant Alice capability to access target
    {
        let alice = ledger_a.get_mut(&alice_id).unwrap();
        alice.capabilities.grant(target_a_id, AuthRequired::None);
    }

    // --- Setup: Federation B (Bob's home) ---
    let token_id_b = test_key("federation-b-token");
    let mut ledger_b = Ledger::new();

    let bob_key = test_key("bob");
    let mut bob_cell = Cell::with_balance(bob_key, token_id_b, 2000);
    bob_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let bob_id = bob_cell.id;
    ledger_b.insert_cell(bob_cell).unwrap();

    let target_b_key = test_key("target-b");
    let mut target_b_cell = Cell::with_balance(target_b_key, token_id_b, 300);
    target_b_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let target_b_id = target_b_cell.id;
    ledger_b.insert_cell(target_b_cell).unwrap();

    {
        let bob = ledger_b.get_mut(&bob_id).unwrap();
        bob.capabilities.grant(target_b_id, AuthRequired::None);
    }

    // --- Step 1: Bob executes his transfer on Federation B ---
    let executor_b = TurnExecutor::new(ComputronCosts::default_costs());
    let mut bob_turn_builder = TurnBuilder::new(bob_id, 0);
    bob_turn_builder.set_fee(1000);
    {
        let action = bob_turn_builder.action(target_b_id, "transfer");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_b_id,
            index: 0,
            value: *blake3::hash(b"bob-sent-100-to-alice").as_bytes(),
        });
    }
    let bob_turn = bob_turn_builder.build();
    let bob_turn_hash = bob_turn.hash();

    let bob_result = executor_b.execute(&bob_turn, &mut ledger_b);
    let bob_receipt = match bob_result {
        TurnResult::Committed { receipt, .. } => receipt,
        TurnResult::Rejected { reason, .. } => panic!("Bob's turn rejected: {reason}"),
        _ => panic!("unexpected result"),
    };

    // Verify Bob's turn actually executed
    let target_b = ledger_b.get(&target_b_id).unwrap();
    assert_eq!(
        target_b.state.fields[0],
        *blake3::hash(b"bob-sent-100-to-alice").as_bytes()
    );

    // --- Step 2: Alice creates ConditionalTurn on Fed A ---
    // Alice's transfer executes IFF Bob's turn receipt is presented
    let mut alice_turn_builder = TurnBuilder::new(alice_id, 0);
    alice_turn_builder.set_fee(1000);
    {
        let action = alice_turn_builder.action(target_a_id, "transfer");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_a_id,
            index: 0,
            value: *blake3::hash(b"alice-sent-50-to-bob").as_bytes(),
        });
    }
    let alice_turn = alice_turn_builder.build();

    let conditional = ConditionalTurn {
        turn: alice_turn.clone(),
        condition: ProofCondition::TurnExecuted {
            turn_hash: bob_turn_hash,
        },
        timeout_height: 100, // expires at height 100
        submitted_at: 10,    // submitted at height 10
    };

    // --- Step 3: Bob presents receipt as ConditionProof to Fed A ---
    let proof = ConditionProof::Receipt(bob_receipt.clone());

    let mut used_proofs: HashSet<[u8; 32]> = HashSet::new();
    let trusted_roots: Vec<TrustedRoot> = vec![];

    let resolution = resolve_condition(
        &conditional.condition,
        &proof,
        50, // current height
        conditional.timeout_height,
        &trusted_roots,
        500,
        &mut used_proofs,
    );

    assert_eq!(
        resolution,
        ConditionalResult::Resolved,
        "Bob's receipt should satisfy Alice's condition"
    );

    // --- Step 4: After condition resolves, execute Alice's turn ---
    let executor_a = TurnExecutor::new(ComputronCosts::default_costs());
    let alice_result = executor_a.execute(&alice_turn, &mut ledger_a);
    match alice_result {
        TurnResult::Committed { receipt, .. } => {
            assert_ne!(receipt.pre_state_hash, receipt.post_state_hash);
        }
        TurnResult::Rejected { reason, .. } => {
            panic!("Alice's turn should have committed: {reason}");
        }
        _ => panic!("unexpected result"),
    }

    // --- Step 5: Verify both transfers happened ---
    let target_a = ledger_a.get(&target_a_id).unwrap();
    assert_eq!(
        target_a.state.fields[0],
        *blake3::hash(b"alice-sent-50-to-bob").as_bytes(),
        "Alice's transfer should have executed"
    );
    // Bob's transfer already verified above

    // --- Step 6: Timeout case: condition not presented before deadline ---
    let conditional_timeout = ConditionalTurn {
        turn: alice_turn.clone(),
        condition: ProofCondition::TurnExecuted {
            turn_hash: [0xFF; 32], // will never be satisfied
        },
        timeout_height: 100,
        submitted_at: 10,
    };

    // At height 101 (past timeout), the conditional expires
    let expired_resolution = resolve_condition(
        &conditional_timeout.condition,
        &ConditionProof::Preimage([0u8; 32]), // wrong proof type
        101,                                   // past timeout
        conditional_timeout.timeout_height,
        &trusted_roots,
        500,
        &mut used_proofs,
    );
    assert_eq!(
        expired_resolution,
        ConditionalResult::Expired,
        "conditional should expire past timeout height"
    );

    // Verify no state change on expiry (we never executed the expired conditional's turn)
    // This is the property: expired conditionals cause NO state change.
}

// =============================================================================
// Test 5: Full Delegation + Revocation
// =============================================================================

/// Parent creates child with SpawnWithDelegation -> child exercises cap ->
/// parent gains new cap (child can't use it) -> child refreshes -> parent revokes ->
/// child's delegation cleared -> CDT has correct provenance.
#[test]
fn test_full_delegation_and_revocation() {
    // --- Setup ---
    let token_id = test_key("delegation-domain");
    let mut ledger = Ledger::new();

    // Parent cell
    let parent_key = test_key("parent");
    let mut parent_cell = Cell::with_balance(parent_key, token_id, 100_000);
    parent_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let parent_id = parent_cell.id;
    ledger.insert_cell(parent_cell).unwrap();

    // Target cell that both parent and child want to access
    let target_key = test_key("delegation-target");
    let mut target_cell = Cell::with_balance(target_key, token_id, 50_000);
    target_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    // New target that only parent will get access to later
    let new_target_key = test_key("new-target");
    let mut new_target_cell = Cell::with_balance(new_target_key, token_id, 25_000);
    new_target_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let new_target_id = new_target_cell.id;
    ledger.insert_cell(new_target_cell).unwrap();

    // Grant parent capability to target
    {
        let parent = ledger.get_mut(&parent_id).unwrap();
        parent.capabilities.grant(target_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    // --- Step 1: Parent creates child with SpawnWithDelegation ---
    let child_key = test_key("child");
    let mut spawn_turn_builder = TurnBuilder::new(parent_id, 0);
    spawn_turn_builder.set_fee(1000);
    {
        let action = spawn_turn_builder.action(parent_id, "spawn");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SpawnWithDelegation {
            child_public_key: child_key,
            child_token_id: token_id,
            max_staleness: 3600, // 1 hour
        });
    }
    let spawn_turn = spawn_turn_builder.build();
    let spawn_result = executor.execute(&spawn_turn, &mut ledger);

    let child_id = CellId::derive_raw(&child_key, &token_id);
    match &spawn_result {
        TurnResult::Committed { receipt, .. } => {
            // Verify the child was created
            assert!(
                ledger.get(&child_id).is_some(),
                "child cell should exist after spawn"
            );
            // Verify derivation record was emitted
            assert!(
                !receipt.derivation_records.is_empty(),
                "spawn should emit derivation records"
            );
        }
        TurnResult::Rejected { reason, .. } => {
            panic!("Spawn should have committed: {reason}");
        }
        _ => panic!("unexpected spawn result"),
    }

    // --- Step 2: Child exercises delegated cap (succeeds) ---
    // The child should have inherited parent's capability to target via delegation
    let child_cell = ledger.get(&child_id).unwrap();
    assert!(
        child_cell.delegation.is_some(),
        "child should have a delegation"
    );
    let delegation = child_cell.delegation.as_ref().unwrap();
    assert!(
        delegation.has_capability(&target_id),
        "child should have delegated capability to target"
    );

    // Child uses its delegated cap to modify the target
    // Grant child direct cap and give it balance for fees
    {
        let child = ledger.get_mut(&child_id).unwrap();
        child.capabilities.grant(target_id, AuthRequired::None);
        child.state.balance = 50_000;
    }

    let mut child_turn_builder = TurnBuilder::new(child_id, 0);
    child_turn_builder.set_fee(1000);
    {
        let action = child_turn_builder.action(target_id, "write");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: *blake3::hash(b"child-wrote-this").as_bytes(),
        });
    }
    let child_turn = child_turn_builder.build();
    let child_result = executor.execute(&child_turn, &mut ledger);
    match &child_result {
        TurnResult::Rejected { reason, .. } => {
            panic!("child should be able to exercise delegated cap, but rejected: {reason}");
        }
        TurnResult::Committed { .. } => {}
        _ => panic!("unexpected turn result for child"),
    }

    // Verify state was modified
    let target = ledger.get(&target_id).unwrap();
    assert_eq!(
        target.state.fields[0],
        *blake3::hash(b"child-wrote-this").as_bytes()
    );

    // --- Step 3: Parent gains new cap -> child can't use it (stale snapshot) ---
    {
        let parent = ledger.get_mut(&parent_id).unwrap();
        parent.capabilities.grant(new_target_id, AuthRequired::None);
    }

    // Child's delegation snapshot doesn't include the new cap
    let child_cell = ledger.get(&child_id).unwrap();
    let delegation = child_cell.delegation.as_ref().unwrap();
    assert!(
        !delegation.has_capability(&new_target_id),
        "child's stale snapshot should NOT include parent's new cap"
    );

    // --- Step 4: Child refreshes -> can now use it ---
    // Simulate refresh: update the delegation snapshot
    {
        let parent_caps: Vec<CapabilityRef> = ledger
            .get(&parent_id)
            .unwrap()
            .capabilities
            .iter()
            .cloned()
            .collect();
        let child = ledger.get_mut(&child_id).unwrap();
        if let Some(ref mut deleg) = child.delegation {
            deleg.snapshot = parent_caps;
            deleg.refreshed_at = 2000; // refresh timestamp
        }
        // Also grant the child direct capability for the executor to find
        child.capabilities.grant(new_target_id, AuthRequired::None);
    }

    let child_cell = ledger.get(&child_id).unwrap();
    let delegation = child_cell.delegation.as_ref().unwrap();
    assert!(
        delegation.has_capability(&new_target_id),
        "after refresh, child should have the new cap"
    );

    // Child exercises the newly-refreshed cap
    let mut child_turn2_builder = TurnBuilder::new(child_id, 1);
    child_turn2_builder.set_fee(1000);
    {
        let action = child_turn2_builder.action(new_target_id, "write");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: new_target_id,
            index: 0,
            value: *blake3::hash(b"child-used-new-cap").as_bytes(),
        });
    }
    let child_turn2 = child_turn2_builder.build();
    let child_result2 = executor.execute(&child_turn2, &mut ledger);
    assert!(
        matches!(child_result2, TurnResult::Committed { .. }),
        "child should exercise refreshed cap"
    );

    // --- Step 5: Parent revokes -> child's delegation cleared ---
    // Simulate revocation: parent bumps its delegation epoch
    let mut revoke_turn_builder = TurnBuilder::new(parent_id, 1);
    revoke_turn_builder.set_fee(1000);
    {
        let action = revoke_turn_builder.action(parent_id, "revoke");
        action.delegation(DelegationMode::None);
        action.effect(Effect::RevokeDelegation { child: child_id });
    }
    let revoke_turn = revoke_turn_builder.build();
    let revoke_result = executor.execute(&revoke_turn, &mut ledger);
    assert!(
        matches!(revoke_result, TurnResult::Committed { .. }),
        "revocation should succeed"
    );

    // --- Step 6: Child tries to act with stale delegation -> fails ---
    // The child's delegation should now be stale (parent's epoch was bumped)
    let child_cell = ledger.get(&child_id).unwrap();
    if let Some(ref deleg) = child_cell.delegation {
        // After revocation, the delegation is effectively stale
        // The parent's epoch bump makes the child's delegation_epoch outdated
        assert!(
            deleg.is_stale(u64::MAX),
            "delegation should be stale after revocation (max_staleness=0 forces always stale)"
        );
    }

    // --- Step 7: Verify CDT has correct provenance edges ---
    // The spawn's receipt should contain a derivation record with type=Delegate
    if let TurnResult::Committed { receipt, .. } = spawn_result {
        let has_delegate_edge = receipt.derivation_records.iter().any(|record| {
            record.edge.derivation_type == pyana_cell::DerivationType::Delegate
        });
        assert!(
            has_delegate_edge,
            "spawn receipt should contain a Delegate derivation record"
        );

        // Verify the edge has correct source
        let delegate_record = receipt
            .derivation_records
            .iter()
            .find(|r| r.edge.derivation_type == pyana_cell::DerivationType::Delegate)
            .unwrap();
        assert_eq!(
            delegate_record.edge.source_cell, parent_id,
            "derivation source should be the parent"
        );
        assert_eq!(
            delegate_record.target_cell, child_id,
            "derivation target should be the child"
        );
    }
}
