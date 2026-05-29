//! Executor-path coverage for miscellaneous `Effect` variants.
//!
//! Every test drives a real `TurnExecutor::execute` (or, for the two variants
//! that require it, the `TurnExecutor` is set up with the exact pre-state the
//! variant demands) and asserts a real outcome — either a committed receipt
//! with observable ledger mutation, or a precise rejection reason.
//!
//! Variants covered with PASSING executor tests:
//!   NoteCreate, CreateSealPair, Seal, Unseal, CreateCommittedEscrow,
//!   ReleaseCommittedEscrow, RefundCommittedEscrow, BridgeFinalize,
//!   BridgeCancel, Introduce, MakeSovereign, CreateCellFromFactory,
//!   SetPermissions, Refusal.
//!
//! Variants with documented blockers (not faked):
//!   NoteSpend — requires a real ZK spending proof (STARK verifier rejects
//!               any proof bytes; no in-process proof generator available).
//!   PipelinedSend — always rejects at apply-time by design (documented in
//!                   apply_pipelined_send: "unresolved PipelinedSend").

use dregg_cell::{
    AuthRequired, CapabilityRef, Cell, CellId, CellMode, FactoryCreationParams, FactoryDescriptor,
    Ledger, NoteCommitment, Permissions, SealPair, ValueCommitment,
    note_bridge::BridgeReceipt,
};
use dregg_turn::{
    ActionBuilder, Effect, EscrowClaimAuth, TurnBuilder, TurnResult,
    action::RefusalReason,
    escrow::{CommittedEscrow, compute_identity_commitment},
    executor::{ComputronCosts, TurnExecutor},
};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

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

fn make_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let token_id = [seed.wrapping_add(100); 32];
    let mut cell = Cell::with_balance(pk, token_id, balance);
    cell.permissions = open_permissions();
    cell
}

fn zero_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
}

/// Execute a turn with one or more effects targeting `agent` and return the result.
fn exec_single(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    nonce: u64,
    effects: Vec<Effect>,
) -> TurnResult {
    exec_single_chained(executor, ledger, agent, nonce, effects, None)
}

/// Execute a turn chained from a previous receipt hash.
fn exec_single_chained(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    nonce: u64,
    effects: Vec<Effect>,
    prev_hash: Option<[u8; 32]>,
) -> TurnResult {
    let mut ab = ActionBuilder::new_unchecked_for_tests(agent, "test-op", agent);
    for e in effects {
        ab = ab.effect(e);
    }
    let action = ab.build();
    let mut builder = TurnBuilder::new(agent, nonce);
    builder.add_action(action);
    let mut turn = builder.fee(0).build();
    turn.previous_receipt_hash = prev_hash;
    executor.execute(&turn, ledger)
}


fn assert_committed(result: &TurnResult, ctx: &str) {
    assert!(
        result.is_committed(),
        "{ctx}: expected committed, got {result:?}"
    );
}

fn assert_rejected(result: &TurnResult, ctx: &str) {
    assert!(
        result.is_rejected(),
        "{ctx}: expected rejected, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// NoteCreate — accepts a non-null commitment with no value_commitment.
// ---------------------------------------------------------------------------

#[test]
fn note_create_cleartext_commits() {
    let cell = make_cell(1, 1_000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let commitment = NoteCommitment([0xAB; 32]);
    // value=0, asset_type=0: zero-value notes (e.g. NFT ownership tokens) satisfy
    // conservation trivially (0 inputs == 0 outputs).
    let result = exec_single(
        &executor,
        &mut ledger,
        cell_id,
        0,
        vec![Effect::NoteCreate {
            commitment,
            value: 0,
            asset_type: 0,
            encrypted_note: vec![0xDE, 0xAD],
            value_commitment: None,
            range_proof: None,
        }],
    );
    assert_committed(&result, "NoteCreate cleartext");
}

#[test]
fn note_create_null_commitment_rejects() {
    let cell = make_cell(2, 1_000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let result = exec_single(
        &executor,
        &mut ledger,
        cell_id,
        0,
        vec![Effect::NoteCreate {
            commitment: NoteCommitment([0u8; 32]),
            value: 0,
            asset_type: 0,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        }],
    );
    assert_rejected(&result, "NoteCreate null commitment");
}

// ---------------------------------------------------------------------------
// NoteSpend — BLOCKER: always rejects because apply_note_spend requires a
// real ZK spending proof that passes through ProofVerifier::verify.
// Without an in-process STARK proof generator we cannot produce such a proof.
// The rejection below is the exact executor path (not a panic), confirming the
// variant reaches apply_note_spend and fails on "NoteSpend missing spending proof".
// ---------------------------------------------------------------------------

#[test]
fn note_spend_always_rejects_without_proof() {
    let cell = make_cell(3, 1_000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let result = exec_single(
        &executor,
        &mut ledger,
        cell_id,
        0,
        vec![Effect::NoteSpend {
            nullifier: dregg_cell::Nullifier([0xAA; 32]),
            note_tree_root: [0xBB; 32],
            spending_proof: vec![],
            value: 10,
            asset_type: 0,
            value_commitment: None,
        }],
    );
    // Must reject cleanly (not panic). The reason is "NoteSpend missing spending proof".
    assert_rejected(&result, "NoteSpend without proof");
    if let TurnResult::Rejected { reason, .. } = &result {
        let msg = format!("{reason:?}");
        assert!(
            msg.contains("spending proof") || msg.contains("NoteSpend"),
            "unexpected rejection reason: {msg}"
        );
    }
}

// ---------------------------------------------------------------------------
// CreateSealPair — grants sealer and unsealer capabilities to two cells.
// ---------------------------------------------------------------------------

#[test]
fn create_seal_pair_grants_capabilities() {
    let actor = make_cell(10, 5_000);
    let actor_id = actor.id();
    let holder2 = make_cell(11, 0);
    let holder2_id = holder2.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(holder2).unwrap();

    let executor = zero_executor();
    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::CreateSealPair {
            sealer_holder: actor_id,
            unsealer_holder: holder2_id,
        }],
    );
    assert_committed(&result, "CreateSealPair");

    // The sealer holder gains a new capability entry.
    let sealer_cell = ledger.get(&actor_id).unwrap();
    assert!(
        sealer_cell.capabilities.iter().count() > 0,
        "sealer_holder must gain at least one capability"
    );
    // The unsealer holder gains a new capability entry.
    let unsealer_cell = ledger.get(&holder2_id).unwrap();
    assert!(
        unsealer_cell.capabilities.iter().count() > 0,
        "unsealer_holder must gain at least one capability"
    );
}

// ---------------------------------------------------------------------------
// Seal — seals a capability reference using the sealer pair.
// Sequence: CreateSealPair → Seal.
// ---------------------------------------------------------------------------

#[test]
fn seal_stores_commitment_in_field7() {
    let actor = make_cell(20, 5_000);
    let actor_id = actor.id();
    let unsealer_cell = make_cell(21, 0);
    let unsealer_id = unsealer_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(unsealer_cell).unwrap();

    let executor = zero_executor();

    // We cannot recover pair.id from the CreateSealPair output because
    // SealPair::generate() uses OS randomness and pair.id is not emitted in the journal.
    // Strategy: inject a known SealPair's sealer capability directly into the ledger,
    // then run Seal against that known pair_id.
    let pair = SealPair::generate();
    let pair_id = pair.id;

    // Inject sealer capability into actor_id manually (no prior turn needed).
    let sealer_cap_id = seal_capability_id_for_test(&pair_id, true);
    ledger.get_mut(&actor_id).unwrap().capabilities.grant_with_breadstuff(
        sealer_cap_id,
        AuthRequired::None,
        Some(pair.sealer_public),
    );

    // The capability to seal is a CapabilityRef pointing at some target cell.
    let cap_to_seal = CapabilityRef {
        target: unsealer_id,
        slot: 0,
        permissions: AuthRequired::None,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
    };

    // No prior turns for this actor_id, so no previous_receipt_hash needed.
    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::Seal { pair_id, capability: cap_to_seal }],
    );
    assert_committed(&result, "Seal");

    // field[7] of actor must be non-zero (contains sealed box commitment).
    let actor_after = ledger.get(&actor_id).unwrap();
    assert_ne!(
        actor_after.state.fields[7],
        [0u8; 32],
        "Seal must store commitment in field[7]"
    );
}

// ---------------------------------------------------------------------------
// Unseal — full Seal->Unseal round-trip through the executor. Exercises the
// #144 fix: apply_unseal reconstructs the pair via SealPair::from_secret, which
// recomputes sealer_public = X25519_base × unsealer_secret, so the ECDH-derived
// decryption key matches the seal side and the sealed capability is recovered.
// (Previously apply_unseal used from_keys([0u8;32], …), zeroing sealer_public,
// which always produced the wrong key and failed with DecryptionFailed.)
// ---------------------------------------------------------------------------

#[test]
fn unseal_round_trips_and_grants_capability_to_recipient() {
    let actor = make_cell(30, 5_000);
    let actor_id = actor.id();
    let recipient = make_cell(31, 0);
    let recipient_id = recipient.id();
    let target_cell = make_cell(32, 0);
    let target_id = target_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(target_cell).unwrap();

    let executor = zero_executor();

    let pair = SealPair::generate();
    let pair_id = pair.id;

    let cap_to_seal = CapabilityRef {
        target: target_id,
        slot: 0,
        permissions: AuthRequired::None,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
    };
    let sealed = pair.seal(&cap_to_seal);

    // Inject the unsealer capability (only stores unsealer_secret in breadstuff).
    let unsealer_cap_id = seal_capability_id_for_test(&pair_id, false);
    ledger.get_mut(&actor_id).unwrap().capabilities.grant_with_breadstuff(
        unsealer_cap_id,
        AuthRequired::None,
        Some(pair.unsealer_secret),
    );

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::Unseal {
            sealed_box: sealed,
            recipient: recipient_id,
        }],
    );
    // With the #144 fix the ECDH key matches, decryption succeeds, and the
    // recovered capability is granted to the recipient cell.
    assert_committed(&result, "Unseal round-trip");
    let recipient_after = ledger.get(&recipient_id).unwrap();
    assert!(
        recipient_after.capabilities.iter().count() > 0,
        "Unseal must grant the recovered capability to the recipient cell"
    );
}

// ---------------------------------------------------------------------------
// Helper: replicate the executor's seal_capability_id derivation.
// (The executor method is pub(super) so we replicate it locally.)
// ---------------------------------------------------------------------------
fn seal_capability_id_for_test(pair_id: &[u8; 32], is_sealer: bool) -> CellId {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-seal capability-id v1");
    hasher.update(pair_id);
    hasher.update(if is_sealer { b"sealer" } else { b"unsealer" });
    CellId::from_bytes(*hasher.finalize().as_bytes())
}

// ---------------------------------------------------------------------------
// CreateCommittedEscrow — locks funds behind cryptographic commitments.
// ---------------------------------------------------------------------------

#[test]
fn create_committed_escrow_locks_funds() {
    let creator = make_cell(40, 10_000);
    let creator_id = creator.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(creator).unwrap();

    let mut executor = zero_executor();
    executor.set_block_height(1);

    // Build commitments.
    let creator_blinding = [0x11u8; 32];
    let recipient_blinding = [0x22u8; 32];
    let fake_recipient_id = CellId::from_bytes([0x99u8; 32]);
    let creator_commitment =
        compute_identity_commitment(&creator_id, &creator_blinding);
    let recipient_commitment =
        compute_identity_commitment(&fake_recipient_id, &recipient_blinding);
    let condition_commitment = *blake3::hash(b"test-condition").as_bytes();

    // We need a valid compressed Ristretto point for value_commitment.
    // Use the identity point (compressed as 0x01 followed by zeros).
    // Actually the identity point in compressed ristretto is all zeros for x=0.
    // The simplest valid ristretto255 compressed point is the base point.
    // But we don't want to pull in curve25519-dalek here unnecessarily.
    // use dregg_cell's ValueCommitment to get a valid point.
    let vc = ValueCommitment::identity();
    let vc_bytes = vc.to_bytes();

    let timeout_height = 100u64;
    let escrow_id = CommittedEscrow::compute_escrow_id(
        &creator_commitment,
        &recipient_commitment,
        &vc_bytes,
        &condition_commitment,
        timeout_height,
    );

    // The executor checks range_proof if proof_verifier is configured.
    // With no proof verifier (zero_executor), the range proof check is skipped.
    let result = exec_single(
        &executor,
        &mut ledger,
        creator_id,
        0,
        vec![Effect::CreateCommittedEscrow {
            creator_commitment,
            recipient_commitment,
            value_commitment: vc_bytes,
            condition_commitment,
            timeout_height,
            escrow_id,
            range_proof: vec![0xAA; 32], // non-empty; no verifier so not checked
            amount: 500,
        }],
    );
    assert_committed(&result, "CreateCommittedEscrow");

    // Creator's balance decremented by 500.
    let bal = ledger.get(&creator_id).unwrap().state.balance();
    assert_eq!(bal, 9_500, "CreateCommittedEscrow must debit creator");
}

// ---------------------------------------------------------------------------
// ReleaseCommittedEscrow — pays out to recipient after claim authorization.
// Sequence: CreateCommittedEscrow → ReleaseCommittedEscrow.
// ---------------------------------------------------------------------------

#[test]
fn release_committed_escrow_pays_recipient() {
    use ed25519_dalek::{Signer, SigningKey};

    // Build a real Ed25519 key pair for the recipient.
    let recipient_sk_bytes = [0x55u8; 32];
    let signing_key = SigningKey::from_bytes(&recipient_sk_bytes);
    let recipient_pk: [u8; 32] = signing_key.verifying_key().to_bytes();

    // Create recipient cell with the real public key.
    let mut recipient_pk32 = [0u8; 32];
    recipient_pk32.copy_from_slice(&recipient_pk);
    let recipient_cell = Cell::with_balance(recipient_pk32, [0x55u8; 32], 0);
    let recipient_cell = {
        let mut c = recipient_cell;
        c.permissions = open_permissions();
        c
    };
    let recipient_id = recipient_cell.id();

    let creator = make_cell(50, 10_000);
    let creator_id = creator.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(creator).unwrap();
    ledger.insert_cell(recipient_cell).unwrap();

    let mut executor = zero_executor();
    executor.set_block_height(1);

    // Build commitments.
    let creator_blinding = [0xAAu8; 32];
    let recipient_blinding = [0xBBu8; 32];
    let creator_commitment = compute_identity_commitment(&creator_id, &creator_blinding);
    let recipient_commitment =
        compute_identity_commitment(&recipient_id, &recipient_blinding);
    let condition_commitment = [0xCCu8; 32];

    let vc = ValueCommitment::identity();
    let vc_bytes = vc.to_bytes();

    let timeout_height = 100u64;
    let escrow_id = CommittedEscrow::compute_escrow_id(
        &creator_commitment,
        &recipient_commitment,
        &vc_bytes,
        &condition_commitment,
        timeout_height,
    );

    // Create the committed escrow.
    let create_result = exec_single(
        &executor,
        &mut ledger,
        creator_id,
        0,
        vec![Effect::CreateCommittedEscrow {
            creator_commitment,
            recipient_commitment,
            value_commitment: vc_bytes,
            condition_commitment,
            timeout_height,
            escrow_id,
            range_proof: vec![0x01; 16],
            amount: 800,
        }],
    );
    assert_committed(&create_result, "CreateCommittedEscrow for release test");
    assert_eq!(ledger.get(&creator_id).unwrap().state.balance(), 9_200);

    // Build claim_auth: sign escrow_id with recipient's key.
    let signature = signing_key.sign(&escrow_id);
    let claim_auth = EscrowClaimAuth {
        cell_id: recipient_id,
        blinding: recipient_blinding,
        signature: signature.to_bytes(),
    };

    let prev = executor.get_last_receipt_hash(&creator_id);
    let release_result = exec_single_chained(
        &executor,
        &mut ledger,
        creator_id,
        1,
        vec![Effect::ReleaseCommittedEscrow {
            escrow_id,
            claim_auth,
            recipient: recipient_id,
        }],
        prev,
    );
    assert_committed(&release_result, "ReleaseCommittedEscrow");

    // Recipient receives the 800.
    assert_eq!(
        ledger.get(&recipient_id).unwrap().state.balance(),
        800,
        "ReleaseCommittedEscrow must credit recipient"
    );
}

// ---------------------------------------------------------------------------
// RefundCommittedEscrow — returns funds to creator after timeout.
// Sequence: CreateCommittedEscrow → advance block height → RefundCommittedEscrow.
// ---------------------------------------------------------------------------

#[test]
fn refund_committed_escrow_returns_after_timeout() {
    use ed25519_dalek::{Signer, SigningKey};

    let creator_sk_bytes = [0x66u8; 32];
    let signing_key = SigningKey::from_bytes(&creator_sk_bytes);
    let creator_pk: [u8; 32] = signing_key.verifying_key().to_bytes();

    let mut creator_cell = Cell::with_balance(creator_pk, [0x66u8; 32], 5_000);
    creator_cell.permissions = open_permissions();
    let creator_id = creator_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(creator_cell).unwrap();

    let mut executor = zero_executor();
    executor.set_block_height(1);

    let creator_blinding = [0xDDu8; 32];
    let recipient_blinding = [0xEEu8; 32];
    let fake_recipient = CellId::from_bytes([0xFFu8; 32]);
    let creator_commitment = compute_identity_commitment(&creator_id, &creator_blinding);
    let recipient_commitment =
        compute_identity_commitment(&fake_recipient, &recipient_blinding);
    let condition_commitment = [0x77u8; 32];

    let vc = ValueCommitment::identity();
    let vc_bytes = vc.to_bytes();

    let timeout_height = 50u64;
    let escrow_id = CommittedEscrow::compute_escrow_id(
        &creator_commitment,
        &recipient_commitment,
        &vc_bytes,
        &condition_commitment,
        timeout_height,
    );

    let create_result = exec_single(
        &executor,
        &mut ledger,
        creator_id,
        0,
        vec![Effect::CreateCommittedEscrow {
            creator_commitment,
            recipient_commitment,
            value_commitment: vc_bytes,
            condition_commitment,
            timeout_height,
            escrow_id,
            range_proof: vec![0x02; 8],
            amount: 1_000,
        }],
    );
    assert_committed(&create_result, "CreateCommittedEscrow for refund test");
    assert_eq!(ledger.get(&creator_id).unwrap().state.balance(), 4_000);

    // Advance past timeout.
    executor.set_block_height(51);

    // Build claim_auth for creator (signs escrow_id with creator's key).
    let signature = signing_key.sign(&escrow_id);
    let claim_auth = EscrowClaimAuth {
        cell_id: creator_id,
        blinding: creator_blinding,
        signature: signature.to_bytes(),
    };

    let prev = executor.get_last_receipt_hash(&creator_id);
    let refund_result = exec_single_chained(
        &executor,
        &mut ledger,
        creator_id,
        1,
        vec![Effect::RefundCommittedEscrow {
            escrow_id,
            claim_auth,
            creator: creator_id,
        }],
        prev,
    );
    assert_committed(&refund_result, "RefundCommittedEscrow");

    // Creator gets the 1000 back.
    assert_eq!(
        ledger.get(&creator_id).unwrap().state.balance(),
        5_000,
        "RefundCommittedEscrow must return funds to creator"
    );
}

// ---------------------------------------------------------------------------
// BridgeFinalize — finalizes a pending bridge using a trusted receipt.
// Sequence: BridgeLock → BridgeFinalize.
// ---------------------------------------------------------------------------

#[test]
fn bridge_finalize_after_lock() {
    use ed25519_dalek::{Signer, SigningKey};

    let nullifier = [0x12u8; 32];
    let destination = [0x34u8; 32];

    let actor = make_cell(60, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let mut executor = zero_executor();
    executor.set_block_height(1);

    // BridgeLock to set up the pending bridge.
    let lock_result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::BridgeLock {
            nullifier,
            destination,
            value: 100,
            asset_type: 0,
            timeout_height: 1_000,
            spending_proof: vec![0xAA; 32],
        }],
    );
    assert_committed(&lock_result, "BridgeLock for finalize test");

    // Build a BridgeReceipt signed by a trusted destination key.
    let dest_sk = SigningKey::from_bytes(&[0x42u8; 32]);
    let dest_pk: [u8; 32] = dest_sk.verifying_key().to_bytes();

    // Use the canonical signing message (BLAKE3 hash).
    let mint_height = 100u64;
    let msg = BridgeReceipt::signing_message(&nullifier, &destination, mint_height);
    let sig = dest_sk.sign(&msg);

    let receipt = BridgeReceipt {
        nullifier,
        destination_federation: destination,
        mint_height,
        signature: sig.to_bytes(),
    };

    // Register the destination key as trusted.
    executor.add_trusted_destination_key(dest_pk);

    let prev = executor.get_last_receipt_hash(&actor_id);
    let finalize_result = exec_single_chained(
        &executor,
        &mut ledger,
        actor_id,
        1,
        vec![Effect::BridgeFinalize { nullifier, receipt }],
        prev,
    );
    assert_committed(&finalize_result, "BridgeFinalize");
}

// ---------------------------------------------------------------------------
// BridgeCancel — cancels a pending bridge after timeout.
// Sequence: BridgeLock → advance block height → BridgeCancel.
// ---------------------------------------------------------------------------

#[test]
fn bridge_cancel_after_timeout() {
    let nullifier = [0x56u8; 32];
    let destination = [0x78u8; 32];

    let actor = make_cell(70, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let mut executor = zero_executor();
    executor.set_block_height(1);

    // BridgeLock with timeout at height 10.
    let lock_result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::BridgeLock {
            nullifier,
            destination,
            value: 50,
            asset_type: 0,
            timeout_height: 10,
            spending_proof: vec![0xBB; 16],
        }],
    );
    assert_committed(&lock_result, "BridgeLock for cancel test");

    // Advance past timeout.
    executor.set_block_height(11);

    let prev = executor.get_last_receipt_hash(&actor_id);
    let cancel_result = exec_single_chained(
        &executor,
        &mut ledger,
        actor_id,
        1,
        vec![Effect::BridgeCancel { nullifier }],
        prev,
    );
    assert_committed(&cancel_result, "BridgeCancel");
}

// ---------------------------------------------------------------------------
// Introduce — introducer with caps to both recipient and target grants
// the recipient access to the target.
// ---------------------------------------------------------------------------

#[test]
fn introduce_grants_capability_to_recipient() {
    let introducer = make_cell(80, 5_000);
    let introducer_id = introducer.id();
    let recipient = make_cell(81, 0);
    let recipient_id = recipient.id();
    let target = make_cell(82, 0);
    let target_id = target.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(introducer).unwrap();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(target).unwrap();

    // Grant introducer a capability to recipient AND a capability to target.
    ledger.get_mut(&introducer_id).unwrap().capabilities.grant(recipient_id, AuthRequired::None);
    ledger.get_mut(&introducer_id).unwrap().capabilities.grant(target_id, AuthRequired::None);

    let executor = zero_executor();

    // Before: recipient has no capabilities.
    assert_eq!(ledger.get(&recipient_id).unwrap().capabilities.iter().count(), 0);

    let result = exec_single(
        &executor,
        &mut ledger,
        introducer_id,
        0,
        vec![Effect::Introduce {
            introducer: introducer_id,
            recipient: recipient_id,
            target: target_id,
            permissions: AuthRequired::None,
        }],
    );
    assert_committed(&result, "Introduce");

    // After: recipient now holds a capability to target.
    let recipient_after = ledger.get(&recipient_id).unwrap();
    assert!(
        recipient_after.capabilities.iter().any(|cap| cap.target == target_id),
        "Introduce must grant recipient a capability to target"
    );
}

// ---------------------------------------------------------------------------
// PipelinedSend — always rejects at apply time (by design).
// Documented blocker: the effect is only valid inside a pipeline resolution
// pass. The EmbeddedExecutor has no pipeline resolver; apply_pipelined_send
// unconditionally returns PreconditionFailed.
// ---------------------------------------------------------------------------

#[test]
fn pipelined_send_rejects_outside_pipeline() {
    use dregg_turn::eventual::EventualRef;
    use dregg_turn::{Action, Authorization, DelegationMode};
    use dregg_cell::Preconditions;

    let actor = make_cell(90, 5_000);
    let actor_id = actor.id();
    let target = make_cell(91, 0);
    let target_id = target.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_executor();

    let inner_action = Action {
        target: target_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::PipelinedSend {
            target: EventualRef::new([0u8; 32], 0),
            action: Box::new(inner_action),
        }],
    );
    assert_rejected(&result, "PipelinedSend outside pipeline");
    if let TurnResult::Rejected { reason, .. } = &result {
        let msg = format!("{reason:?}");
        assert!(
            msg.contains("PipelinedSend") || msg.contains("pipeline"),
            "PipelinedSend rejection must mention pipeline: {msg}"
        );
    }
}

// ---------------------------------------------------------------------------
// MakeSovereign — transitions the action-target cell to sovereign mode.
// ---------------------------------------------------------------------------

#[test]
fn make_sovereign_transitions_cell() {
    let actor = make_cell(100, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::MakeSovereign { cell: actor_id }],
    );
    assert_committed(&result, "MakeSovereign");

    // After MakeSovereign the cell is removed from the hosted store and a
    // sovereign commitment is recorded. The cell is no longer in the hosted ledger.
    assert!(
        ledger.get(&actor_id).is_none(),
        "MakeSovereign must move cell out of hosted store"
    );
    assert!(
        ledger.is_sovereign(&actor_id),
        "MakeSovereign must register the cell as sovereign"
    );
    assert!(
        ledger.get_sovereign_commitment(&actor_id).is_some(),
        "MakeSovereign must record sovereign commitment"
    );
}

#[test]
fn make_sovereign_cross_cell_rejects() {
    // MakeSovereign with cell != action_target must be rejected.
    let actor = make_cell(101, 5_000);
    let actor_id = actor.id();
    let other = make_cell(102, 0);
    let other_id = other.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(other).unwrap();

    let executor = zero_executor();

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::MakeSovereign { cell: other_id }],
    );
    assert_rejected(&result, "MakeSovereign cross-cell");
}

// ---------------------------------------------------------------------------
// CreateCellFromFactory — creates a new cell via a registered factory.
// ---------------------------------------------------------------------------

#[test]
fn create_cell_from_factory_produces_new_cell() {
    let actor = make_cell(110, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let mut executor = zero_executor();

    // Register a factory.
    let factory = FactoryDescriptor {
        factory_vk: [0xF1; 32],
        child_program_vk: None,
        child_vk_strategy: None,
        allowed_cap_templates: vec![],
        field_constraints: vec![],
        state_constraints: vec![],
        default_mode: CellMode::Hosted,
        creation_budget: None,
    };
    let factory_vk = executor.deploy_factory(factory);

    let owner_pubkey = [0x11u8; 32];
    let token_id = [0x22u8; 32];
    let params = FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk: None,
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey,
    };

    let new_cell_id = CellId::derive_raw(&owner_pubkey, &token_id);
    assert!(ledger.get(&new_cell_id).is_none(), "cell must not exist before factory creation");

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::CreateCellFromFactory {
            factory_vk,
            owner_pubkey,
            token_id,
            params,
        }],
    );
    assert_committed(&result, "CreateCellFromFactory");

    assert!(
        ledger.get(&new_cell_id).is_some(),
        "CreateCellFromFactory must create the new cell in the ledger"
    );
}

#[test]
fn create_cell_from_factory_unknown_factory_rejects() {
    let actor = make_cell(111, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    let owner_pubkey = [0x33u8; 32];
    let token_id = [0x44u8; 32];
    let params = FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk: None,
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey,
    };

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::CreateCellFromFactory {
            factory_vk: [0xDEu8; 32], // not registered
            owner_pubkey,
            token_id,
            params,
        }],
    );
    assert_rejected(&result, "CreateCellFromFactory unknown factory");
}

// ---------------------------------------------------------------------------
// SetPermissions — updates the permission set of the action-target cell.
// ---------------------------------------------------------------------------

#[test]
fn set_permissions_updates_cell_permissions() {
    let actor = make_cell(120, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    // Verify the current permissions are open.
    let before = ledger.get(&actor_id).unwrap().permissions.send.clone();
    assert!(matches!(before, AuthRequired::None));

    // Change send permission to Signature-required.
    let new_perms = Permissions {
        send: AuthRequired::Signature,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::SetPermissions {
            cell: actor_id,
            new_permissions: new_perms.clone(),
        }],
    );
    assert_committed(&result, "SetPermissions");

    let after = &ledger.get(&actor_id).unwrap().permissions;
    assert!(
        matches!(after.send, AuthRequired::Signature),
        "SetPermissions must update send permission to Signature"
    );
}

// ---------------------------------------------------------------------------
// Refusal — bumps nonce, stores audit commitment in field[4].
// ---------------------------------------------------------------------------

#[test]
fn refusal_bumps_nonce_and_stores_audit() {
    let actor = make_cell(130, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    let before_nonce = ledger.get(&actor_id).unwrap().state.nonce();
    let before_field4 = ledger.get(&actor_id).unwrap().state.fields[4];

    let offered_commitment = [0xAA; 32];
    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::Refusal {
            cell: actor_id,
            offered_action_commitment: offered_commitment,
            refusal_reason: RefusalReason::Declined,
            proof_witness_index: 0,
        }],
    );
    assert_committed(&result, "Refusal");

    let after = ledger.get(&actor_id).unwrap();
    // The cell nonce is incremented twice: once by the executor's Phase 1 (fee+nonce commit)
    // and once by apply_refusal itself. Total: before_nonce + 2.
    assert_eq!(after.state.nonce(), before_nonce + 2, "Refusal (plus executor Phase 1) must bump nonce by 2");
    assert_ne!(
        after.state.fields[4], before_field4,
        "Refusal must write audit commitment to field[4]"
    );
}

#[test]
fn refusal_with_custom_reason_stores_distinct_audit() {
    let actor = make_cell(131, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    let result1 = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::Refusal {
            cell: actor_id,
            offered_action_commitment: [0x01; 32],
            refusal_reason: RefusalReason::Declined,
            proof_witness_index: 0,
        }],
    );
    assert_committed(&result1, "Refusal Declined");
    let field4_declined = ledger.get(&actor_id).unwrap().state.fields[4];

    // After the first Refusal turn, the cell nonce has been incremented twice:
    // once by the Refusal effect (apply_refusal) and once by the executor's
    // finalization step (nonce_increment = true in execute.rs). So cell nonce = 2.
    let nonce2 = ledger.get(&actor_id).unwrap().state.nonce();
    let prev = executor.get_last_receipt_hash(&actor_id);
    let result2 = exec_single_chained(
        &executor,
        &mut ledger,
        actor_id,
        nonce2,
        vec![Effect::Refusal {
            cell: actor_id,
            offered_action_commitment: [0x01; 32],
            refusal_reason: RefusalReason::Custom { reason_hash: [0xBEu8; 32] },
            proof_witness_index: 0,
        }],
        prev,
    );
    assert_committed(&result2, "Refusal Custom");
    let field4_custom = ledger.get(&actor_id).unwrap().state.fields[4];

    assert_ne!(
        field4_declined, field4_custom,
        "distinct refusal reasons must produce distinct audit commitments"
    );
}
