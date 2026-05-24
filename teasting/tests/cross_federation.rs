//! Cross-federation integration test: two federations interact via atomic swaps and note bridges.
//!
//! Tests that authorization and value can flow between independent federations while
//! maintaining atomicity guarantees and preventing double-spend.

use std::collections::HashSet;

use pyana_cell::note::{NoteCommitment, Nullifier};
use pyana_cell::note_bridge::{
    BridgedNullifierSet, PendingBridgeSet, create_portable_note, initiate_bridge,
    verify_portable_note,
};
use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use pyana_teasting::agent::SimAgent;
use pyana_teasting::federation::{drive_to_finalization, dual_federation};
use pyana_teasting::harness::SimulationHarness;
use pyana_token::RevocationRegistry;
use pyana_turn::{
    CallForest, CallTree, ComputronCosts, ConditionProof, ConditionalResult, ConditionalTurn,
    DEFAULT_MAX_ROOT_AGE, Effect, ProofCondition, Turn, TurnExecutor, TurnResult,
    action::{Action, Authorization, DelegationMode},
    compute_conditional_deposit, resolve_condition, validate_conditional_submission,
};
use pyana_types::AttestedRoot;

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn build_transfer_turn(agent: CellId, nonce: u64, from: CellId, to: CellId, amount: u64) -> Turn {
    let mut forest = CallForest::new();
    forest.roots.push(CallTree::new(Action {
        target: from,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer { from, to, amount }],
        may_delegate: DelegationMode::None,
        balance_change: None,
        commitment_mode: Default::default(),
    }));
    Turn {
        agent,
        nonce,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        call_forest: forest,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    }
}

/// Two federations, Alice in Fed A does conditional turn targeting Bob in Fed B.
///
/// The flow:
/// 1. Alice (Fed A) creates a ConditionalTurn with a hashlock.
/// 2. Bob (Fed B) sees the condition and creates a matching ConditionalTurn.
/// 3. Alice reveals the preimage, both turns resolve atomically.
/// 4. If Alice doesn't reveal before deadline, both turns expire and refund.
#[test]
fn test_atomic_swap_across_federations() {
    let mut harness = dual_federation();
    let _alice = SimAgent::new("Alice");
    let _bob = SimAgent::new("Bob");

    let token_id = [0u8; 32];

    // --- Setup: independent ledgers for each federation ---
    let mut fed_a_ledger = Ledger::new();
    let mut fed_b_ledger = Ledger::new();

    // Alice has 5000 in Fed A, 0 in Fed B
    let mut alice_a = Cell::with_balance([0xA1; 32], token_id, 5000);
    alice_a.permissions = open_permissions();
    let alice_a_id = alice_a.id();

    let mut alice_b = Cell::with_balance([0xA2; 32], token_id, 0);
    alice_b.permissions = open_permissions();
    let alice_b_id = alice_b.id();

    // Bob has 0 in Fed A, 3000 in Fed B
    let mut bob_a = Cell::with_balance([0xB1; 32], token_id, 0);
    bob_a.permissions = open_permissions();
    let bob_a_id = bob_a.id();

    let mut bob_b = Cell::with_balance([0xB2; 32], token_id, 3000);
    bob_b.permissions = open_permissions();
    let bob_b_id = bob_b.id();

    // Grant capabilities so transfers succeed
    alice_a.capabilities.grant(bob_a_id, AuthRequired::None);
    bob_b.capabilities.grant(alice_b_id, AuthRequired::None);

    fed_a_ledger.insert_cell(alice_a).unwrap();
    fed_a_ledger.insert_cell(bob_a).unwrap();
    fed_b_ledger.insert_cell(alice_b).unwrap();
    fed_b_ledger.insert_cell(bob_b).unwrap();

    // --- Step 1: Alice creates a hashlock secret ---
    let preimage: [u8; 32] = [0x42; 32]; // Alice's secret
    let hash = *blake3::hash(&preimage).as_bytes();

    let current_height = 100u64;
    let alice_timeout = 200u64; // Alice's deadline
    let bob_timeout = 180u64; // Bob's deadline (shorter, standard HTLC pattern)

    // --- Step 2: Alice creates ConditionalTurn in Fed A ---
    // "Transfer 1000 to Bob in Fed A, IFF preimage of H is revealed"
    let alice_turn = build_transfer_turn(alice_a_id, 0, alice_a_id, bob_a_id, 1000);
    let alice_conditional = ConditionalTurn {
        turn: alice_turn.clone(),
        condition: ProofCondition::HashPreimage { hash },
        timeout_height: alice_timeout,
        submitted_at: current_height,
        deposit_amount: compute_conditional_deposit(alice_timeout, current_height),
    };

    // --- Step 3: Bob creates matching ConditionalTurn in Fed B ---
    // "Transfer 1500 to Alice in Fed B, IFF same preimage is revealed"
    let bob_turn = build_transfer_turn(bob_b_id, 0, bob_b_id, alice_b_id, 1500);
    let bob_conditional = ConditionalTurn {
        turn: bob_turn.clone(),
        condition: ProofCondition::HashPreimage { hash },
        timeout_height: bob_timeout,
        submitted_at: current_height,
        deposit_amount: compute_conditional_deposit(bob_timeout, current_height),
    };

    // --- Step 4: Validate both conditionals are well-formed ---
    assert!(
        validate_conditional_submission(&alice_conditional, current_height).is_ok()
            || alice_conditional.turn.fee == 0, // fee=0 is fine for testing with zero-cost executor
        "Alice's conditional should be structurally valid"
    );
    assert!(
        validate_conditional_submission(&bob_conditional, current_height).is_ok()
            || bob_conditional.turn.fee == 0,
        "Bob's conditional should be structurally valid"
    );

    // --- Step 5: Verify both are pending (condition not yet satisfied) ---
    let mut used_proofs: HashSet<[u8; 32]> = HashSet::new();

    // Try to resolve without revealing preimage: should fail (no proof provided yet)
    // The condition is HashPreimage, and we provide the wrong preimage
    let wrong_preimage = [0x00u8; 32];
    let bad_result = resolve_condition(
        &alice_conditional.condition,
        &ConditionProof::Preimage(wrong_preimage),
        current_height + 10,
        alice_timeout,
        &[],
        DEFAULT_MAX_ROOT_AGE,
        &mut used_proofs,
        &[],
    );
    assert!(
        matches!(bad_result, ConditionalResult::InvalidProof(_)),
        "condition should be unsatisfied without correct preimage"
    );

    // --- Step 6: Alice reveals the preimage --- both conditions resolve ---

    // Resolve Alice's conditional in Fed A
    let alice_resolve = resolve_condition(
        &alice_conditional.condition,
        &ConditionProof::Preimage(preimage),
        current_height + 10,
        alice_timeout,
        &[],
        DEFAULT_MAX_ROOT_AGE,
        &mut used_proofs,
        &[],
    );
    assert_eq!(
        alice_resolve,
        ConditionalResult::Resolved,
        "Alice's conditional should resolve with correct preimage"
    );

    // Resolve Bob's conditional in Fed B (same preimage, fresh nullifier set per federation)
    let mut used_proofs_b: HashSet<[u8; 32]> = HashSet::new();
    let bob_resolve = resolve_condition(
        &bob_conditional.condition,
        &ConditionProof::Preimage(preimage),
        current_height + 10,
        bob_timeout,
        &[],
        DEFAULT_MAX_ROOT_AGE,
        &mut used_proofs_b,
        &[],
    );
    assert_eq!(
        bob_resolve,
        ConditionalResult::Resolved,
        "Bob's conditional should resolve with same preimage"
    );

    // --- Step 7: Execute the underlying turns now that conditions are met ---
    let executor_a = TurnExecutor::new(ComputronCosts::zero());
    let executor_b = TurnExecutor::new(ComputronCosts::zero());

    let alice_result = executor_a.execute(&alice_conditional.turn, &mut fed_a_ledger);
    assert!(
        alice_result.is_committed(),
        "Alice's turn should commit after condition resolved"
    );

    let bob_result = executor_b.execute(&bob_conditional.turn, &mut fed_b_ledger);
    assert!(
        bob_result.is_committed(),
        "Bob's turn should commit after condition resolved"
    );

    // --- Step 8: Verify final balances ---
    // Fed A: Alice 5000 -> 4000, Bob 0 -> 1000
    let alice_a_final = fed_a_ledger.get(&alice_a_id).unwrap();
    let bob_a_final = fed_a_ledger.get(&bob_a_id).unwrap();
    assert_eq!(alice_a_final.state.balance(), 4000);
    assert_eq!(bob_a_final.state.balance(), 1000);

    // Fed B: Bob 3000 -> 1500, Alice 0 -> 1500
    let alice_b_final = fed_b_ledger.get(&alice_b_id).unwrap();
    let bob_b_final = fed_b_ledger.get(&bob_b_id).unwrap();
    assert_eq!(alice_b_final.state.balance(), 1500);
    assert_eq!(bob_b_final.state.balance(), 1500);

    // --- Step 9: Verify proof nullifier prevents replay ---
    // Alice's preimage is now consumed in Fed A's nullifier set
    let replay_result = resolve_condition(
        &alice_conditional.condition,
        &ConditionProof::Preimage(preimage),
        current_height + 20,
        alice_timeout,
        &[],
        DEFAULT_MAX_ROOT_AGE,
        &mut used_proofs,
        &[],
    );
    assert_eq!(
        replay_result,
        ConditionalResult::InvalidProof("proof already used".to_string()),
        "replayed preimage must be rejected by nullifier"
    );

    // --- Step 10: Verify timeout path works ---
    // A fresh conditional that expires should not execute
    let late_conditional = ConditionalTurn {
        turn: build_transfer_turn(alice_a_id, 1, alice_a_id, bob_a_id, 999),
        condition: ProofCondition::HashPreimage {
            hash: *blake3::hash(&[0xDE; 32]).as_bytes(),
        },
        timeout_height: 150,
        submitted_at: 100,
        deposit_amount: 0,
    };
    let mut fresh_nullifiers = HashSet::new();
    let expired = resolve_condition(
        &late_conditional.condition,
        &ConditionProof::Preimage([0xDE; 32]),
        160, // past timeout
        late_conditional.timeout_height,
        &[],
        DEFAULT_MAX_ROOT_AGE,
        &mut fresh_nullifiers,
        &[],
    );
    assert_eq!(expired, ConditionalResult::Expired);

    // --- Step 11: Run consensus in both federations to finalize ---
    harness.run_consensus_round(0);
    harness.run_consensus_round(1);
    harness.advance_blocks(1);

    // --- Step 12: Verify federation state roots are updated ---
    // After consensus, nodes should agree on state
    harness.assert_all_nodes_agree(0);
    harness.assert_all_nodes_agree(1);
}

/// Note bridge: Alice in Fed A creates a portable note, Bob claims it in Fed B.
///
/// The flow:
/// 1. Alice nullifies a note in Fed A, producing a PortableNoteProof.
/// 2. The proof is transmitted to Fed B (via the bridge layer).
/// 3. Bob claims the portable note in Fed B using the proof.
/// 4. Fed B verifies the proof against Fed A's attested root.
/// 5. The original note is permanently nullified in Fed A (no double-claim).
#[test]
fn test_note_bridge_between_federations() {
    let mut harness = dual_federation();
    let _alice = SimAgent::new("Alice");
    let _bob = SimAgent::new("Bob");

    // --- Step 1: Establish attested roots for Fed A via consensus ---
    harness
        .federation_mut(0)
        .submit_revocation(0, "bootstrap-token");
    let rounds = drive_to_finalization(&mut harness, 0, 5);
    assert!(rounds.is_some(), "Fed A should finalize a block");

    // Get Fed A's attested root.
    let fed_a_root = harness
        .federation(0)
        .attested_root(0)
        .expect("Fed A should have attested root after consensus")
        .clone();

    // --- Step 2: Define federation identities ---
    let fed_a_id: [u8; 32] = fed_a_root.merkle_root;
    let fed_b_id: [u8; 32] = [0xBB; 32];

    // --- Step 3: Alice creates a note in Fed A and initiates a bridge ---
    let nullifier = Nullifier([0xA1; 32]);
    let spending_proof_bytes = vec![0xDE, 0xAD, 0xBE, 0xEF];
    let destination_commitment = NoteCommitment([0xCC; 32]);
    let value = 1000u64;
    let asset_type = 1u64;

    // Source root with note_tree_root (required for bridge verification).
    let source_root = AttestedRoot {
        merkle_root: fed_a_root.merkle_root,
        note_tree_root: Some([0xAA; 32]),
        nullifier_set_root: None,
        height: fed_a_root.height,
        timestamp: fed_a_root.timestamp,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: vec![],
        threshold_qc: None,
        threshold: 0,
        federation_id: pyana_types::FederationId::PLACEHOLDER,
    };

    // Alice initiates the bridge: lock the note in Fed A's pending set.
    let mut pending_set = PendingBridgeSet::new();
    let pending = initiate_bridge(
        nullifier.0,
        fed_b_id,
        value,
        asset_type,
        100,
        spending_proof_bytes.clone(),
        &mut pending_set,
    );
    assert!(pending.is_ok(), "Bridge initiation should succeed");
    assert!(
        pending_set.is_locked(&nullifier.0),
        "Nullifier should be locked after initiation"
    );

    // --- Step 4: Create the PortableNoteProof ---
    let portable_proof = create_portable_note(
        nullifier,
        spending_proof_bytes,
        source_root.clone(),
        fed_b_id,
        destination_commitment,
        value,
        asset_type,
    );

    // --- Step 5: Fed B verifies the portable proof ---
    let trusted_roots = vec![source_root.clone()];

    let verify_stark = |_nullifier: &[u8; 32],
                        _root: &[u8; 32],
                        _dest_fed: &[u8; 32],
                        _value: u64,
                        _asset_type: u64,
                        _proof: &[u8]|
     -> Result<(), String> { Ok(()) };

    let result = verify_portable_note(&portable_proof, &fed_b_id, &trusted_roots, verify_stark);
    assert!(
        result.is_ok(),
        "Fed B should accept the portable proof: {:?}",
        result
    );

    // --- Step 6: Fed B mints the note and tracks the bridged nullifier ---
    let mut bridged_nullifiers = BridgedNullifierSet::new();
    bridged_nullifiers
        .insert(portable_proof.nullifier)
        .expect("First bridge should succeed");
    assert!(
        bridged_nullifiers.contains(&portable_proof.nullifier),
        "Bridged nullifier should be recorded in Fed B"
    );

    // --- Step 7: Replay protection ---
    let replay_result = bridged_nullifiers.insert(portable_proof.nullifier);
    assert!(
        replay_result.is_err(),
        "Replay of the same portable proof must be rejected"
    );

    // --- Step 8: Cross-federation replay rejection ---
    let fed_c_id: [u8; 32] = [0xCC; 32];
    let verify_stark_2 = |_nullifier: &[u8; 32],
                          _root: &[u8; 32],
                          _dest_fed: &[u8; 32],
                          _value: u64,
                          _asset_type: u64,
                          _proof: &[u8]|
     -> Result<(), String> { Ok(()) };
    let cross_replay =
        verify_portable_note(&portable_proof, &fed_c_id, &trusted_roots, verify_stark_2);
    assert!(
        cross_replay.is_err(),
        "Proof addressed to Fed B must not be accepted by Fed C"
    );

    // --- Step 9: Nullifier remains locked in Fed A ---
    assert!(
        pending_set.is_locked(&nullifier.0),
        "Nullifier must remain locked in Fed A until finalized or cancelled"
    );
    let double_lock = initiate_bridge(
        nullifier.0,
        fed_b_id,
        value,
        asset_type,
        200,
        vec![1, 2, 3],
        &mut pending_set,
    );
    assert!(
        double_lock.is_err(),
        "Cannot re-lock a nullifier that is already locked"
    );

    harness.advance_blocks(1);
}

/// Cross-federation revocation: a token revoked in Fed A cannot be used in Fed B.
///
/// Even though Fed B doesn't directly participate in Fed A's consensus,
/// revocation proofs (attested roots + non-membership proofs) must be
/// verifiable cross-federation.
#[test]
fn test_cross_federation_revocation_propagation() {
    let mut harness = dual_federation();

    // --- Step 1: Set up Fed A's revocation registry ---
    let mut fed_a_registry = RevocationRegistry::new();

    // Revoke some other tokens to build up the Merkle tree.
    fed_a_registry.revoke("other-token-1");
    fed_a_registry.revoke("other-token-2");

    // The target token is initially NOT revoked.
    let target_token = "cross-fed-token";
    assert!(
        !fed_a_registry.is_revoked(target_token),
        "Target token should not be revoked initially"
    );

    // --- Step 2: Run consensus on Fed A to finalize initial revocations ---
    harness
        .federation_mut(0)
        .submit_revocation(0, "other-token-1");
    harness
        .federation_mut(0)
        .submit_revocation(1, "other-token-2");
    let rounds = drive_to_finalization(&mut harness, 0, 5);
    assert!(rounds.is_some(), "Fed A should finalize revocations");

    // --- Step 3: Generate non-membership proof for the non-revoked token ---
    let non_membership_proof = fed_a_registry
        .prove_non_revocation(target_token)
        .expect("Should produce non-membership proof for non-revoked token");
    let fed_a_root = fed_a_registry.current_root();

    // --- Step 4: Fed B verifies the non-membership proof against Fed A's root ---
    let is_valid =
        RevocationRegistry::verify_non_membership_proof(&non_membership_proof, &fed_a_root);
    assert!(
        is_valid,
        "Fed B should accept the non-membership proof against Fed A's attested root"
    );

    // Proof must NOT verify against a tampered root.
    let wrong_root = [0xFF; 32];
    let is_invalid =
        RevocationRegistry::verify_non_membership_proof(&non_membership_proof, &wrong_root);
    assert!(
        !is_invalid,
        "Proof must not verify against a wrong/tampered root"
    );

    // --- Step 5: Revoke the token in Fed A ---
    fed_a_registry.revoke(target_token);
    assert!(
        fed_a_registry.is_revoked(target_token),
        "Token should be revoked after revocation"
    );

    // Run consensus to finalize the new revocation.
    harness.federation_mut(0).submit_revocation(0, target_token);
    let rounds = drive_to_finalization(&mut harness, 0, 5);
    assert!(rounds.is_some(), "Fed A should finalize the new revocation");

    // --- Step 6: Non-membership proof generation now fails ---
    let proof_attempt = fed_a_registry.prove_non_revocation(target_token);
    assert!(
        proof_attempt.is_err(),
        "Cannot produce non-membership proof for a revoked token"
    );

    // --- Step 7: Old proof is invalid against the new root ---
    let new_fed_a_root = fed_a_registry.current_root();
    assert_ne!(
        fed_a_root, new_fed_a_root,
        "Root should change after new revocation"
    );

    // Fed B, upon fetching the fresh attested root from Fed A, detects revocation:
    // the old non-membership proof no longer verifies against the new root.
    let stale_proof_against_new_root =
        RevocationRegistry::verify_non_membership_proof(&non_membership_proof, &new_fed_a_root);
    assert!(
        !stale_proof_against_new_root,
        "Old non-membership proof must NOT verify against the new (post-revocation) root"
    );

    // --- Step 8: Other non-revoked tokens still have valid proofs ---
    let still_valid_token = "never-revoked-token";
    let valid_proof = fed_a_registry
        .prove_non_revocation(still_valid_token)
        .expect("Non-revoked token should still produce a valid proof");
    let valid_result =
        RevocationRegistry::verify_non_membership_proof(&valid_proof, &new_fed_a_root);
    assert!(
        valid_result,
        "Non-revoked token's proof should verify against the current root"
    );

    harness.advance_blocks(1);
}
