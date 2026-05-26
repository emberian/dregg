//! Escrow lifecycle integration test: create → release/refund.
//!
//! Tests the full escrow primitive: locking funds, releasing with a valid condition,
//! refunding after timeout, and rejecting release with bad proofs.

use dregg_cell::{Cell, CellId, Ledger, NoteCommitment};
use dregg_turn::builder::ActionBuilder;
use dregg_turn::executor::{ComputronCosts, ProofVerifier, TurnExecutor};
use dregg_turn::{Effect, EscrowCondition, TurnBuilder, TurnResult};

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// A deterministic proof verifier for testing.
/// Accepts proofs whose first byte matches a known "magic" value.
struct TestProofVerifier {
    magic: u8,
}

impl TestProofVerifier {
    fn new(magic: u8) -> Self {
        Self { magic }
    }
}

impl ProofVerifier for TestProofVerifier {
    fn verify(&self, proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
        !proof.is_empty() && proof[0] == self.magic
    }
}

/// Create a cell with a given balance and permissive permissions for testing.
fn create_funded_cell(ledger: &mut Ledger, seed: u8, balance: u64) -> CellId {
    use dregg_cell::permissions::{AuthRequired, Permissions};
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[1] = seed.wrapping_mul(7);
    let token_id = [seed; 32];
    let mut cell = Cell::with_balance(pk, token_id, balance);
    // Set all permissions to None (no auth required) for test simplicity.
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
    let id = cell.id();
    ledger.insert_cell(cell).unwrap();
    id
}

/// Build and execute a turn with a single action targeting the agent cell.
fn exec_turn(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    nonce: u64,
    fee: u64,
    effects: Vec<Effect>,
) -> TurnResult {
    let mut builder = TurnBuilder::new(agent, nonce);
    builder.set_fee(fee);
    if let Some(prev) = executor.get_last_receipt_hash(&agent) {
        builder.set_previous_receipt_hash(prev);
    }
    let mut ab = ActionBuilder::new_unchecked_for_tests(agent, "escrow-op", agent);
    for e in effects {
        ab = ab.effect(e);
    }
    builder.add_action(ab.build());
    let turn = builder.build();
    executor.execute(&turn, ledger)
}

/// Derive a deterministic escrow ID from a seed.
fn escrow_id(seed: u8) -> [u8; 32] {
    let mut id = [0u8; 32];
    id[0] = seed;
    id[31] = seed.wrapping_add(1);
    id
}

// ─── Tests ───────────────────────────────────────────────────────────────────

/// Happy path: create escrow, release with valid proof → funds go to recipient.
#[test]
fn test_escrow_create_and_release_happy_path() {
    let mut ledger = Ledger::new();
    let alice = create_funded_cell(&mut ledger, 1, 10_000);
    let bob = create_funded_cell(&mut ledger, 2, 0);

    let magic = 0xAB;
    let vk = [0xDE; 32];
    let executor = TurnExecutor::with_proof_verifier(
        ComputronCosts::zero(),
        Box::new(TestProofVerifier::new(magic)),
    );

    let eid = escrow_id(1);

    // Create escrow: Alice locks 500 for Bob, condition = proof with vk.
    let create = Effect::CreateEscrow {
        cell: alice,
        recipient: bob,
        amount: 500,
        condition: EscrowCondition::ProofPresented {
            verification_key: vk,
        },
        timeout_height: 100,
        escrow_id: eid,
    };

    let result = exec_turn(&executor, &mut ledger, alice, 0, 0, vec![create]);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "Escrow creation should succeed: {:?}",
        result
    );
    // Alice's balance decreased by 500.
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 9_500);

    // Release escrow: Bob presents a valid proof (first byte == magic).
    let valid_proof = vec![magic, 0, 0, 0];
    let release = Effect::ReleaseEscrow {
        escrow_id: eid,
        proof: Some(valid_proof),
    };

    let result = exec_turn(&executor, &mut ledger, alice, 1, 0, vec![release]);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "Escrow release should succeed: {:?}",
        result
    );
    // Bob received the escrowed 500.
    assert_eq!(ledger.get(&bob).unwrap().state.balance(), 500);
    // Alice balance unchanged (already deducted at creation).
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 9_500);
}

/// Adversarial: release with invalid proof is rejected.
#[test]
fn test_escrow_release_bad_proof_rejected() {
    let mut ledger = Ledger::new();
    let alice = create_funded_cell(&mut ledger, 3, 10_000);
    let bob = create_funded_cell(&mut ledger, 4, 0);

    let magic = 0xAB;
    let vk = [0xDE; 32];
    let executor = TurnExecutor::with_proof_verifier(
        ComputronCosts::zero(),
        Box::new(TestProofVerifier::new(magic)),
    );

    let eid = escrow_id(2);

    // Create escrow.
    let create = Effect::CreateEscrow {
        cell: alice,
        recipient: bob,
        amount: 300,
        condition: EscrowCondition::ProofPresented {
            verification_key: vk,
        },
        timeout_height: 100,
        escrow_id: eid,
    };
    let result = exec_turn(&executor, &mut ledger, alice, 0, 0, vec![create]);
    assert!(matches!(result, TurnResult::Committed { .. }));

    // Attempt release with WRONG proof (first byte != magic).
    let bad_proof = vec![0xFF, 0, 0, 0];
    let release = Effect::ReleaseEscrow {
        escrow_id: eid,
        proof: Some(bad_proof),
    };

    let result = exec_turn(&executor, &mut ledger, alice, 1, 0, vec![release]);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "Bad proof should be rejected: {:?}",
        result
    );
    // Bob should NOT have received funds.
    assert_eq!(ledger.get(&bob).unwrap().state.balance(), 0);
}

/// Timeout path: refund after timeout returns funds to creator.
#[test]
fn test_escrow_refund_on_timeout() {
    let mut ledger = Ledger::new();
    let alice = create_funded_cell(&mut ledger, 5, 10_000);
    let bob = create_funded_cell(&mut ledger, 6, 0);

    let magic = 0xAB;
    let vk = [0xDE; 32];
    let mut executor = TurnExecutor::with_proof_verifier(
        ComputronCosts::zero(),
        Box::new(TestProofVerifier::new(magic)),
    );
    executor.set_block_height(10);

    let eid = escrow_id(3);

    // Create escrow with timeout at height 50.
    let create = Effect::CreateEscrow {
        cell: alice,
        recipient: bob,
        amount: 800,
        condition: EscrowCondition::ProofPresented {
            verification_key: vk,
        },
        timeout_height: 50,
        escrow_id: eid,
    };
    let result = exec_turn(&executor, &mut ledger, alice, 0, 0, vec![create]);
    assert!(matches!(result, TurnResult::Committed { .. }));
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 9_200);

    // Advance past timeout.
    executor.set_block_height(51);

    // Refund escrow.
    let refund = Effect::RefundEscrow { escrow_id: eid };
    let result = exec_turn(&executor, &mut ledger, alice, 1, 0, vec![refund]);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "Refund should succeed after timeout: {:?}",
        result
    );
    // Alice's funds are returned.
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 10_000);
    // Bob received nothing.
    assert_eq!(ledger.get(&bob).unwrap().state.balance(), 0);
}

/// Adversarial: refund BEFORE timeout is rejected.
#[test]
fn test_escrow_refund_before_timeout_rejected() {
    let mut ledger = Ledger::new();
    let alice = create_funded_cell(&mut ledger, 7, 10_000);
    let bob = create_funded_cell(&mut ledger, 8, 0);

    let magic = 0xAB;
    let vk = [0xDE; 32];
    let mut executor = TurnExecutor::with_proof_verifier(
        ComputronCosts::zero(),
        Box::new(TestProofVerifier::new(magic)),
    );
    executor.set_block_height(10);

    let eid = escrow_id(4);

    // Create escrow with timeout at height 50.
    let create = Effect::CreateEscrow {
        cell: alice,
        recipient: bob,
        amount: 600,
        condition: EscrowCondition::ProofPresented {
            verification_key: vk,
        },
        timeout_height: 50,
        escrow_id: eid,
    };
    let result = exec_turn(&executor, &mut ledger, alice, 0, 0, vec![create]);
    assert!(matches!(result, TurnResult::Committed { .. }));

    // Attempt refund BEFORE timeout (block_height = 10 < 50).
    let refund = Effect::RefundEscrow { escrow_id: eid };
    let result = exec_turn(&executor, &mut ledger, alice, 1, 0, vec![refund]);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "Refund before timeout should be rejected: {:?}",
        result
    );
    // Alice's balance unchanged (still locked).
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 9_400);
}

/// Double-release: releasing an already-resolved escrow is rejected.
#[test]
fn test_escrow_double_release_rejected() {
    let mut ledger = Ledger::new();
    let alice = create_funded_cell(&mut ledger, 9, 10_000);
    let bob = create_funded_cell(&mut ledger, 10, 0);

    let magic = 0xAB;
    let vk = [0xDE; 32];
    let executor = TurnExecutor::with_proof_verifier(
        ComputronCosts::zero(),
        Box::new(TestProofVerifier::new(magic)),
    );

    let eid = escrow_id(5);

    // Create and release normally.
    let create = Effect::CreateEscrow {
        cell: alice,
        recipient: bob,
        amount: 200,
        condition: EscrowCondition::ProofPresented {
            verification_key: vk,
        },
        timeout_height: 100,
        escrow_id: eid,
    };
    exec_turn(&executor, &mut ledger, alice, 0, 0, vec![create]);
    let valid_proof = vec![magic, 1, 2, 3];
    let release = Effect::ReleaseEscrow {
        escrow_id: eid,
        proof: Some(valid_proof.clone()),
    };
    exec_turn(&executor, &mut ledger, alice, 1, 0, vec![release]);
    assert_eq!(ledger.get(&bob).unwrap().state.balance(), 200);

    // Attempt second release → should be rejected (already resolved).
    let release2 = Effect::ReleaseEscrow {
        escrow_id: eid,
        proof: Some(valid_proof),
    };
    let result = exec_turn(&executor, &mut ledger, alice, 2, 0, vec![release2]);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "Double release should be rejected: {:?}",
        result
    );
    // Bob still has only 200 (no double-credit).
    assert_eq!(ledger.get(&bob).unwrap().state.balance(), 200);
}

// ─── Obligation tests ────────────────────────────────────────────────────────

/// Happy path: create obligation, fulfill before deadline → stake returned.
#[test]
fn test_obligation_create_and_fulfill() {
    let mut ledger = Ledger::new();
    let alice = create_funded_cell(&mut ledger, 11, 10_000);
    let bob = create_funded_cell(&mut ledger, 12, 0);

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_block_height(10);

    let stake = NoteCommitment([0xAA; 32]);

    // Create obligation: Alice stakes 1000 for Bob, deadline at height 100.
    let create = Effect::CreateObligation {
        beneficiary: bob,
        condition: dregg_turn::conditional::ProofCondition::HashPreimage { hash: [0xCC; 32] },
        deadline_height: 100,
        stake,
        stake_amount: 1000,
    };

    let result = exec_turn(&executor, &mut ledger, alice, 0, 0, vec![create]);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "Obligation creation should succeed: {:?}",
        result
    );
    // Alice's balance decreased by stake_amount.
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 9_000);

    // Derive the obligation ID (same derivation as executor, including condition).
    let obligation_id = {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-obligation-id-v1");
        hasher.update(alice.as_bytes());
        hasher.update(bob.as_bytes());
        hasher.update(&100u64.to_le_bytes());
        hasher.update(&stake.0);
        // HashPreimage discriminant = 0, hash = [0xCC; 32] (matches CreateObligation above).
        hasher.update(&[0u8]);
        hasher.update(&[0xCCu8; 32]);
        *hasher.finalize().as_bytes()
    };

    // Fulfill obligation before deadline (block_height still 10 < 100).
    let fulfill = Effect::FulfillObligation {
        obligation_id,
        proof: dregg_turn::conditional::ConditionProof::Preimage([0xDD; 32]),
    };

    let result = exec_turn(&executor, &mut ledger, alice, 1, 0, vec![fulfill]);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "Obligation fulfillment should succeed: {:?}",
        result
    );
    // Alice's stake is returned.
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 10_000);
    // Bob did NOT receive the stake (obligation was fulfilled, not slashed).
    assert_eq!(ledger.get(&bob).unwrap().state.balance(), 0);
}

/// Adversarial: miss deadline + slash → stake transferred to beneficiary.
#[test]
fn test_obligation_slash_after_deadline() {
    let mut ledger = Ledger::new();
    let alice = create_funded_cell(&mut ledger, 13, 10_000);
    let bob = create_funded_cell(&mut ledger, 14, 0);

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_block_height(10);

    let stake = NoteCommitment([0xBB; 32]);

    let create = Effect::CreateObligation {
        beneficiary: bob,
        condition: dregg_turn::conditional::ProofCondition::HashPreimage { hash: [0xCC; 32] },
        deadline_height: 50,
        stake,
        stake_amount: 2000,
    };

    let result = exec_turn(&executor, &mut ledger, alice, 0, 0, vec![create]);
    assert!(matches!(result, TurnResult::Committed { .. }));
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 8_000);

    let obligation_id = {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-obligation-id-v1");
        hasher.update(alice.as_bytes());
        hasher.update(bob.as_bytes());
        hasher.update(&50u64.to_le_bytes());
        hasher.update(&stake.0);
        // HashPreimage discriminant = 0, hash = [0xCC; 32] (matches CreateObligation above).
        hasher.update(&[0u8]);
        hasher.update(&[0xCCu8; 32]);
        *hasher.finalize().as_bytes()
    };

    // Advance past deadline.
    executor.set_block_height(51);

    // Slash the obligation.
    let slash = Effect::SlashObligation { obligation_id };
    let result = exec_turn(&executor, &mut ledger, alice, 1, 0, vec![slash]);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "Slash should succeed after deadline: {:?}",
        result
    );
    // Bob received the slashed stake.
    assert_eq!(ledger.get(&bob).unwrap().state.balance(), 2000);
    // Alice does NOT get the stake back.
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 8_000);
}

/// Adversarial: slash BEFORE deadline is rejected.
#[test]
fn test_obligation_slash_before_deadline_rejected() {
    let mut ledger = Ledger::new();
    let alice = create_funded_cell(&mut ledger, 15, 10_000);
    let bob = create_funded_cell(&mut ledger, 16, 0);

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_block_height(10);

    let stake = NoteCommitment([0xCC; 32]);

    let create = Effect::CreateObligation {
        beneficiary: bob,
        condition: dregg_turn::conditional::ProofCondition::HashPreimage { hash: [0xCC; 32] },
        deadline_height: 100,
        stake,
        stake_amount: 500,
    };
    let result = exec_turn(&executor, &mut ledger, alice, 0, 0, vec![create]);
    assert!(matches!(result, TurnResult::Committed { .. }));

    let obligation_id = {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-obligation-id-v1");
        hasher.update(alice.as_bytes());
        hasher.update(bob.as_bytes());
        hasher.update(&100u64.to_le_bytes());
        hasher.update(&stake.0);
        // HashPreimage discriminant = 0, hash = [0xCC; 32] (matches CreateObligation above).
        hasher.update(&[0u8]);
        hasher.update(&[0xCCu8; 32]);
        *hasher.finalize().as_bytes()
    };

    // Attempt slash while deadline has NOT passed (block_height = 10 <= 100).
    let slash = Effect::SlashObligation { obligation_id };
    let result = exec_turn(&executor, &mut ledger, alice, 1, 0, vec![slash]);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "Slash before deadline should be rejected: {:?}",
        result
    );
    // Bob received nothing.
    assert_eq!(ledger.get(&bob).unwrap().state.balance(), 0);
}

/// Adversarial: fulfill AFTER deadline is rejected.
#[test]
fn test_obligation_fulfill_after_deadline_rejected() {
    let mut ledger = Ledger::new();
    let alice = create_funded_cell(&mut ledger, 17, 10_000);
    let bob = create_funded_cell(&mut ledger, 18, 0);

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_block_height(10);

    let stake = NoteCommitment([0xDD; 32]);

    let create = Effect::CreateObligation {
        beneficiary: bob,
        condition: dregg_turn::conditional::ProofCondition::HashPreimage { hash: [0xCC; 32] },
        deadline_height: 50,
        stake,
        stake_amount: 1500,
    };
    let result = exec_turn(&executor, &mut ledger, alice, 0, 0, vec![create]);
    assert!(matches!(result, TurnResult::Committed { .. }));

    let obligation_id = {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-obligation-id-v1");
        hasher.update(alice.as_bytes());
        hasher.update(bob.as_bytes());
        hasher.update(&50u64.to_le_bytes());
        hasher.update(&stake.0);
        // HashPreimage discriminant = 0, hash = [0xCC; 32] (matches CreateObligation above).
        hasher.update(&[0u8]);
        hasher.update(&[0xCCu8; 32]);
        *hasher.finalize().as_bytes()
    };

    // Advance past deadline.
    executor.set_block_height(51);

    // Attempt to fulfill after deadline → rejected.
    let fulfill = Effect::FulfillObligation {
        obligation_id,
        proof: dregg_turn::conditional::ConditionProof::Preimage([0xDD; 32]),
    };
    let result = exec_turn(&executor, &mut ledger, alice, 1, 0, vec![fulfill]);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "Fulfill after deadline should be rejected: {:?}",
        result
    );
}
