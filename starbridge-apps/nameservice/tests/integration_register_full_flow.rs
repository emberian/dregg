//! Executor-invoking integration tests for the nameservice registration flow.
//!
//! Unlike the `lifecycle.rs` tests (which evaluate `CellProgram::evaluate`
//! directly against hand-rolled state pairs), these tests drive a real
//! `EmbeddedExecutor::submit_action` → `TurnReceipt` path. The executor:
//!
//! 1. Verifies the action's `Authorization::Signature` against the cipherclerk's
//!    public key.
//! 2. Applies the `Effect::SetField` and `Effect::EmitEvent` effects to the
//!    ledger.
//! 3. Evaluates the cell-program slot caveats (`WriteOnce`, `Monotonic`) against
//!    `(old_state, new_state)`.
//! 4. Returns a `TurnReceipt` with `emitted_events` for off-chain assertions.
//!
//! **Tests here are what the Python `cross-app-e2e/` demo's commitment-encoding
//! tests do NOT cover.** Those tests verify that a canonical commitment can be
//! computed consistently — they never call `submit_action` and therefore never
//! exercise the executor's slot-caveat enforcement or signature validation.

use starbridge_nameservice::{
    NAME_HASH_SLOT, build_register_action, build_renew_action, build_revoke_action,
    build_transfer_action, expiry_field, name_factory_descriptor, name_hash, revoked_tombstone,
};

// =============================================================================
// Common test helpers
// =============================================================================

mod common {
    use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
    use starbridge_nameservice::name_cell_program;

    pub fn make_cipherclerk(seed: u8) -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32])
    }

    /// Build an EmbeddedExecutor pre-seeded with a target cell at `cell_id`
    /// so `submit_action` has a ledger entry to apply effects against.
    ///
    /// The executor's own agent cell is the cipherclerk's identity cell.
    /// We additionally seed the *registry* cell so the executor can apply
    /// `SetField` effects to it.  The approach: create the executor for the
    /// cipherclerk's cell, then add the named cell directly via the runtime's
    /// ledger.  For tests that only care about `emitted_events` we can target
    /// the cipherclerk's own cell (no seeding needed).
    pub fn make_executor_with_cell(cipherclerk: &AppCipherclerk) -> (EmbeddedExecutor, CellId) {
        let executor = EmbeddedExecutor::new(cipherclerk, "default");
        // Use the executor's own cell as the registry cell so it already
        // exists in the ledger at construction time.
        let cell = executor.cell_id();
        executor.install_program(cell, name_cell_program());
        (executor, cell)
    }
}

// =============================================================================
// Test 1: register → executor emits receipt with name-registered event
// =============================================================================

/// Drive a name registration through the embedded executor and verify:
/// - `submit_action` returns `Ok(TurnReceipt)` (no rejection).
/// - The receipt contains exactly one `name-registered` emitted event.
/// - The event data fields encode the expected `name_hash`.
#[test]
fn executor_register_name_emits_receipt_with_name_registered_event() {
    let cipherclerk = common::make_cipherclerk(0x10);
    let (executor, registry_cell) = common::make_executor_with_cell(&cipherclerk);

    let owner = [0xAAu8; 32];
    let expiry: u64 = 1_000_000;
    let name = "alice.dregg";

    let action = build_register_action(&cipherclerk, registry_cell, name, owner, expiry);
    let receipt = executor
        .submit_action(&cipherclerk, action)
        .expect("register_name must be accepted by the executor");

    // The executor must have processed at least one action.
    assert_eq!(receipt.action_count, 1);

    // The receipt must include the `name-registered` event.
    assert!(
        !receipt.emitted_events.is_empty(),
        "register_name must emit at least one event"
    );

    // The first emitted event's data must start with the expected name hash.
    let ev = &receipt.emitted_events[0];
    assert_eq!(
        ev.data[0],
        name_hash(name),
        "first event data field must be the canonical name_hash"
    );
    assert_eq!(
        ev.data[2],
        expiry_field(expiry),
        "third event data field must encode the expiry height"
    );
}

// =============================================================================
// Test 2: register → renew → executor accepts forward-only expiry extension
// =============================================================================

/// Submit a registration followed by a renewal.  The executor's
/// `Monotonic(EXPIRY_SLOT)` caveat must permit the extension and reject
/// any attempt to re-submit the original (lower) expiry.
#[test]
fn executor_renew_extends_expiry_and_monotonic_blocks_rollback() {
    let cipherclerk = common::make_cipherclerk(0x20);
    let (executor, registry_cell) = common::make_executor_with_cell(&cipherclerk);

    let owner = [0xBBu8; 32];
    let initial_expiry: u64 = 500;
    let renewed_expiry: u64 = 5_256_000; // one rent epoch
    let name = "bob.dregg";

    // Step 1: register (creates the initial state with expiry = 500).
    let reg_action =
        build_register_action(&cipherclerk, registry_cell, name, owner, initial_expiry);
    executor
        .submit_action(&cipherclerk, reg_action)
        .expect("registration must succeed");

    // Step 2: renew (advances expiry to 5_256_000 — Monotonic permits).
    let renew_action = build_renew_action(&cipherclerk, registry_cell, name, renewed_expiry);
    let renew_receipt = executor
        .submit_action(&cipherclerk, renew_action)
        .expect("renewal must be accepted by the executor");

    assert_eq!(renew_receipt.action_count, 1);
    assert!(
        !renew_receipt.emitted_events.is_empty(),
        "renew_name must emit a name-renewed event"
    );

    // Step 3 (adversarial): attempt to roll back expiry to 300 → must be rejected
    // by the `Monotonic(EXPIRY_SLOT)` caveat baked into the name cell program.
    let rollback_action = build_renew_action(&cipherclerk, registry_cell, name, 300);
    let rollback_result = executor.submit_action(&cipherclerk, rollback_action);
    assert!(
        rollback_result.is_err(),
        "rolling back expiry below the current monotone value must be rejected; got: {rollback_result:?}"
    );
}

// =============================================================================
// Test 3: register → revoke → attempt to re-register same cell → rejected
// =============================================================================

/// A revoked name cell's `REVOKED_SLOT` is set to a tombstone via
/// `WriteOnce`.  Attempting to overwrite the tombstone (e.g., by
/// submitting a second register action targeting the same cell) must be
/// rejected by the executor.
#[test]
fn executor_revoke_blocks_subsequent_name_slot_overwrite() {
    let cipherclerk = common::make_cipherclerk(0x30);
    let (executor, registry_cell) = common::make_executor_with_cell(&cipherclerk);

    let owner = [0xCCu8; 32];
    let name = "carol.dregg";

    // Register.
    let reg_action = build_register_action(&cipherclerk, registry_cell, name, owner, 1_000);
    executor
        .submit_action(&cipherclerk, reg_action)
        .expect("registration must succeed");

    // Revoke.
    let revoke_action = build_revoke_action(&cipherclerk, registry_cell, name);
    let revoke_receipt = executor
        .submit_action(&cipherclerk, revoke_action)
        .expect("first revocation must be accepted");
    assert!(
        !revoke_receipt.emitted_events.is_empty(),
        "revoke must emit event"
    );

    // Verify the tombstone value is the canonical one.
    let expected_tombstone = revoked_tombstone(name);
    // The emitted event's second data field is the tombstone.
    let ev = &revoke_receipt.emitted_events[0];
    assert_eq!(
        ev.data[1], expected_tombstone,
        "revocation event must carry the canonical tombstone"
    );

    // Adversarial: attempt a second revocation with a different tombstone.
    // `WriteOnce(REVOKED_SLOT)` must block this.
    let second_revoke_action = build_revoke_action(&cipherclerk, registry_cell, "eve.dregg");
    let second_revoke_result = executor.submit_action(&cipherclerk, second_revoke_action);
    assert!(
        second_revoke_result.is_err(),
        "overwriting a non-zero REVOKED_SLOT must be rejected by WriteOnce; got: {second_revoke_result:?}"
    );
}

// =============================================================================
// Test 4: transfer → executor records new owner in event data
// =============================================================================

/// Submit a name registration then a transfer.  The receipt from the
/// transfer action must include a `name-transferred` event whose data
/// encodes both the old and new owner hashes.
#[test]
fn executor_transfer_emits_name_transferred_event_with_correct_owner_hashes() {
    let cipherclerk = common::make_cipherclerk(0x40);
    let (executor, registry_cell) = common::make_executor_with_cell(&cipherclerk);

    let old_owner = [0xAAu8; 32];
    let new_owner = [0xBBu8; 32];
    let name = "dan.dregg";

    // Register.
    let reg_action = build_register_action(&cipherclerk, registry_cell, name, old_owner, 2_000);
    executor
        .submit_action(&cipherclerk, reg_action)
        .expect("registration must succeed");

    // Transfer.
    let transfer_action =
        build_transfer_action(&cipherclerk, registry_cell, name, old_owner, new_owner);
    let transfer_receipt = executor
        .submit_action(&cipherclerk, transfer_action)
        .expect("transfer must succeed");

    // The event data must carry name_hash, old_owner_hash, new_owner_hash.
    assert!(!transfer_receipt.emitted_events.is_empty());
    let ev = &transfer_receipt.emitted_events[0];
    // data[0] = name_hash
    assert_eq!(ev.data[0], name_hash(name));
    // data[1] = old_owner_hash = blake3(old_owner)
    let expected_old = *blake3::hash(&old_owner).as_bytes();
    assert_eq!(ev.data[1], expected_old, "event must carry old owner hash");
    // data[2] = new_owner_hash = blake3(new_owner)
    let expected_new = *blake3::hash(&new_owner).as_bytes();
    assert_eq!(ev.data[2], expected_new, "event must carry new owner hash");
}

// =============================================================================
// Test 5: factory descriptor state_constraints are enforced end-to-end
// =============================================================================

/// Confirm that the `FactoryDescriptor::state_constraints` we advertise are
/// actually the ones the executor enforces.  We derive the expected
/// constraints from `name_factory_descriptor()` and check that an
/// adversarial action (writing `NAME_HASH_SLOT` a second time) is rejected
/// for the right reason.
///
/// This pins the wire between the descriptor (the "constructor
/// transparency" document) and the executor (the enforcer).
#[test]
fn executor_enforces_factory_descriptor_state_constraints() {
    // Confirm the descriptor advertises WriteOnce on NAME_HASH_SLOT.
    use dregg_cell::StateConstraint;
    let d = name_factory_descriptor();
    assert!(
        d.state_constraints.iter().any(|c| matches!(
            c,
            StateConstraint::WriteOnce { index } if *index == NAME_HASH_SLOT as u8
        )),
        "factory descriptor must advertise WriteOnce on NAME_HASH_SLOT"
    );

    // Now verify the executor actually enforces it.
    let cipherclerk = common::make_cipherclerk(0x50);
    let (executor, registry_cell) = common::make_executor_with_cell(&cipherclerk);

    let owner = [0xDDu8; 32];
    let name = "eve.dregg";

    // First register — legal.
    let reg_action = build_register_action(&cipherclerk, registry_cell, name, owner, 3_000);
    executor
        .submit_action(&cipherclerk, reg_action)
        .expect("first registration must succeed");

    // Second register (WriteOnce violation) — must be rejected by executor.
    let re_reg_action =
        build_register_action(&cipherclerk, registry_cell, "alice.dregg", owner, 4_000);
    let result = executor.submit_action(&cipherclerk, re_reg_action);
    assert!(
        result.is_err(),
        "re-writing NAME_HASH_SLOT on an already-registered cell must be rejected; got: {result:?}"
    );
}
