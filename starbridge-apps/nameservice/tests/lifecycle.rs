//! Integration tests for the `starbridge-nameservice` lifecycle.
//!
//! These exercise the public Rust surface end-to-end:
//!
//! - **Register → set-target → renew → transfer → revoke** as a single
//!   sequence, walking the per-slot state machine the factory descriptor
//!   pins.
//! - **Adversarial executions** that should be rejected by the slot
//!   caveats baked into the factory descriptor:
//!   - Duplicate-name registration (WriteOnce on NAME_HASH_SLOT)
//!   - Expiry decrement (Monotonic on EXPIRY_SLOT)
//!   - Double revocation (WriteOnce on REVOKED_SLOT)
//! - **Authorization adversarial**: an `Authorization::Unchecked` action
//!   does *not* round-trip through `build_*_action` — the AppCipherclerk path
//!   always carries a real Ed25519 signature. We exercise that here as
//!   the regression guard for the `[0u8; 64]` pattern.
//!
//! Tests in this file evaluate the factory's [`StateConstraint`] set
//! directly via `CellProgram::evaluate`. They do *not* spin up a full
//! `Ledger` + `TurnExecutor`, because the executor wires the same
//! `program.evaluate(..)` path on the post-state and the constraint
//! semantics are what these tests need to pin. Integrating against a
//! full `TurnExecutor` is the responsibility of the
//! `protocol-tests/` crate (which exercises the executor + program
//! together) — duplicating that wiring here would just couple this
//! crate to an executor it does not depend on.

use pyana_app_framework::{
    AgentCipherclerk, AppCipherclerk, Authorization, CellId, Effect, FieldElement,
};
use pyana_cell::{CellProgram, ProgramError, StateConstraint};
use starbridge_nameservice::{
    EXPIRY_SLOT, NAME_FACTORY_VK, NAME_HASH_SLOT, OWNER_HASH_SLOT, RESOLVE_TARGET_SLOT,
    REVOKED_SLOT, build_register_action, build_renew_action, build_revoke_action,
    build_set_target_action, build_transfer_action, expiry_field, factory_descriptors,
    name_factory_descriptor, name_hash, register, resolve_target, revoked_tombstone,
};

// =============================================================================
// Helpers
// =============================================================================

fn wallet_with_seed(seed_byte: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [seed_byte; 32])
}

fn registry_cell() -> CellId {
    CellId::from_bytes([0x42u8; 32])
}

fn fresh_program() -> CellProgram {
    CellProgram::Predicate(name_factory_descriptor().state_constraints.clone())
}

fn empty_state() -> pyana_cell::state::CellState {
    pyana_cell::state::CellState::new(0)
}

fn project_setfield(action: &pyana_app_framework::Action, slot: usize) -> Option<FieldElement> {
    for effect in &action.effects {
        if let Effect::SetField { index, value, .. } = effect {
            if *index == slot {
                return Some(*value);
            }
        }
    }
    None
}

// =============================================================================
// Round-trip lifecycle
// =============================================================================

/// Walk a name through its entire lifecycle and confirm each step's
/// post-state passes the factory's `StateConstraint` set when evaluated
/// against the prior state.
#[test]
fn lifecycle_register_set_target_renew_transfer_revoke_round_trips() {
    let program = fresh_program();
    let cipherclerk = wallet_with_seed(0x10);
    let cell = registry_cell();
    let owner = [0xAAu8; 32];
    let new_owner = [0xBBu8; 32];
    let name = "alice.pyana";

    // ── Step 1: register (creation; old = empty). ────────────────────
    let initial_expiry: u64 = 1_000;
    let register_action = build_register_action(&cipherclerk, cell, name, owner, initial_expiry);
    let mut state_after_register = empty_state();
    state_after_register.fields[NAME_HASH_SLOT] =
        project_setfield(&register_action, NAME_HASH_SLOT).unwrap();
    state_after_register.fields[OWNER_HASH_SLOT] =
        project_setfield(&register_action, OWNER_HASH_SLOT).unwrap();
    state_after_register.fields[EXPIRY_SLOT] =
        project_setfield(&register_action, EXPIRY_SLOT).unwrap();
    state_after_register.set_nonce(1);
    program
        .evaluate(&state_after_register, Some(&empty_state()), None)
        .expect("register: passes WriteOnce(name)+Monotonic(expiry)+WriteOnce(revoked)");
    assert_eq!(state_after_register.fields[NAME_HASH_SLOT], name_hash(name));

    // ── Step 2: set-target (no slot caveat applies). ────────────────
    let target = resolve_target("pyana://cell/alices-document");
    let set_target_action = build_set_target_action(&cipherclerk, cell, name, target);
    let mut state_after_set_target = state_after_register.clone();
    state_after_set_target.fields[RESOLVE_TARGET_SLOT] =
        project_setfield(&set_target_action, RESOLVE_TARGET_SLOT).unwrap();
    state_after_set_target.set_nonce(2);
    program
        .evaluate(&state_after_set_target, Some(&state_after_register), None)
        .expect("set_target: no caveat applies; transition must succeed");
    assert_eq!(state_after_set_target.fields[RESOLVE_TARGET_SLOT], target);

    // ── Step 3: renew (extend expiry forward — Monotonic permits). ──
    let new_expiry: u64 = 5_000;
    let renew_action = build_renew_action(&cipherclerk, cell, name, new_expiry);
    let mut state_after_renew = state_after_set_target.clone();
    state_after_renew.fields[EXPIRY_SLOT] = project_setfield(&renew_action, EXPIRY_SLOT).unwrap();
    state_after_renew.set_nonce(3);
    program
        .evaluate(&state_after_renew, Some(&state_after_set_target), None)
        .expect("renew: Monotonic permits expiry extension");
    assert_eq!(
        state_after_renew.fields[EXPIRY_SLOT],
        expiry_field(new_expiry)
    );

    // ── Step 4: transfer (owner change, no other slot moves). ───────
    let transfer_action = build_transfer_action(&cipherclerk, cell, name, owner, new_owner);
    let mut state_after_transfer = state_after_renew.clone();
    state_after_transfer.fields[OWNER_HASH_SLOT] =
        project_setfield(&transfer_action, OWNER_HASH_SLOT).unwrap();
    state_after_transfer.set_nonce(4);
    program
        .evaluate(&state_after_transfer, Some(&state_after_renew), None)
        .expect("transfer: only OWNER_HASH_SLOT moves; no caveat is violated");

    // ── Step 5: revoke (REVOKED_SLOT zero → tombstone — WriteOnce permits). ──
    let revoke_action = build_revoke_action(&cipherclerk, cell, name);
    let mut state_after_revoke = state_after_transfer.clone();
    state_after_revoke.fields[REVOKED_SLOT] =
        project_setfield(&revoke_action, REVOKED_SLOT).unwrap();
    state_after_revoke.set_nonce(5);
    program
        .evaluate(&state_after_revoke, Some(&state_after_transfer), None)
        .expect("revoke: WriteOnce permits the first revocation");
    assert_eq!(
        state_after_revoke.fields[REVOKED_SLOT],
        revoked_tombstone(name)
    );
}

// =============================================================================
// Adversarial: duplicate-name registration
// =============================================================================

#[test]
fn adversarial_duplicate_name_registration_rejected_by_write_once() {
    let program = fresh_program();
    // Active "alice.pyana" on the cell.
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.pyana");
    old.fields[EXPIRY_SLOT] = expiry_field(1_000);
    old.set_nonce(1);
    // Attacker tries to repurpose the cell with a different name.
    let mut new = empty_state();
    new.fields[NAME_HASH_SLOT] = name_hash("eve.pyana");
    new.fields[EXPIRY_SLOT] = expiry_field(1_000);
    new.set_nonce(2);
    let err = program
        .evaluate(&new, Some(&old), None)
        .expect_err("duplicate name registration must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::WriteOnce { index },
            ..
        } => assert_eq!(index, NAME_HASH_SLOT as u8),
        other => panic!("expected WriteOnce on NAME_HASH_SLOT, got {other:?}"),
    }
}

// =============================================================================
// Adversarial: expiry decrement
// =============================================================================

#[test]
fn adversarial_expiry_decrement_rejected_by_monotonic() {
    let program = fresh_program();
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.pyana");
    old.fields[EXPIRY_SLOT] = expiry_field(10_000);
    old.set_nonce(1);
    // Attacker tries to shorten the rental.
    let mut new = old.clone();
    new.fields[EXPIRY_SLOT] = expiry_field(5_000);
    new.set_nonce(2);
    let err = program
        .evaluate(&new, Some(&old), None)
        .expect_err("expiry decrement must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Monotonic { index },
            ..
        } => assert_eq!(index, EXPIRY_SLOT as u8),
        other => panic!("expected Monotonic on EXPIRY_SLOT, got {other:?}"),
    }
}

#[test]
fn adversarial_expiry_held_equal_is_permitted_by_monotonic() {
    // Monotonic permits `new == old`. A no-op renew (e.g., a paranoid
    // sweep where the executor re-emits the same expiry) must not be
    // rejected.
    let program = fresh_program();
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.pyana");
    old.fields[EXPIRY_SLOT] = expiry_field(10_000);
    old.set_nonce(1);
    let mut new = old.clone();
    new.set_nonce(2);
    program
        .evaluate(&new, Some(&old), None)
        .expect("no-op transition must pass all slot caveats");
}

// =============================================================================
// Adversarial: double revocation
// =============================================================================

#[test]
fn adversarial_double_revoke_rejected_by_write_once_on_revoked_slot() {
    let program = fresh_program();
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.pyana");
    old.fields[EXPIRY_SLOT] = expiry_field(10_000);
    old.fields[REVOKED_SLOT] = revoked_tombstone("alice.pyana");
    old.set_nonce(2);
    // Attacker tries to write a different tombstone (e.g., to pretend
    // a different name was revoked at this cell).
    let mut new = old.clone();
    new.fields[REVOKED_SLOT] = revoked_tombstone("eve.pyana");
    new.set_nonce(3);
    let err = program
        .evaluate(&new, Some(&old), None)
        .expect_err("second revocation must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::WriteOnce { index },
            ..
        } => assert_eq!(index, REVOKED_SLOT as u8),
        other => panic!("expected WriteOnce on REVOKED_SLOT, got {other:?}"),
    }
}

// =============================================================================
// Authorization: action carries a real Ed25519 signature (no [0u8;64])
// =============================================================================

#[test]
fn auth_register_action_carries_real_signature() {
    let cipherclerk = wallet_with_seed(0xAA);
    let action = build_register_action(
        &cipherclerk,
        registry_cell(),
        "alice.pyana",
        [3u8; 32],
        1_000,
    );
    match action.authorization {
        Authorization::Signature(a, b) => {
            assert!(
                a != [0u8; 32] || b != [0u8; 32],
                "the framework signing path must not emit [0u8; 64] placeholders"
            );
        }
        other => panic!("expected Signature variant, got {other:?}"),
    }
}

#[test]
fn auth_all_lifecycle_actions_carry_real_signatures() {
    // Every entry point must emit an Authorization::Signature.
    let cipherclerk = wallet_with_seed(0xCC);
    let cell = registry_cell();
    let name = "alice.pyana";
    let actions = vec![
        (
            "register",
            build_register_action(&cipherclerk, cell, name, [3u8; 32], 1_000),
        ),
        ("renew", build_renew_action(&cipherclerk, cell, name, 5_000)),
        (
            "transfer",
            build_transfer_action(&cipherclerk, cell, name, [3u8; 32], [4u8; 32]),
        ),
        ("revoke", build_revoke_action(&cipherclerk, cell, name)),
        (
            "set_target",
            build_set_target_action(&cipherclerk, cell, name, resolve_target("pyana://cell/x")),
        ),
    ];
    for (name, action) in actions {
        match action.authorization {
            Authorization::Signature(a, b) => assert!(
                a != [0u8; 32] || b != [0u8; 32],
                "{name} action signature must be non-zero"
            ),
            other => panic!("expected Signature for `{name}`, got {other:?}"),
        }
    }
}

#[test]
fn auth_different_wallets_produce_different_signatures_on_same_logical_action() {
    // Same federation_id, different wallets — signatures must diverge.
    let w1 = wallet_with_seed(0x01);
    let w2 = wallet_with_seed(0x01);
    let cell = registry_cell();
    let a1 = build_register_action(&w1, cell, "alice", [3u8; 32], 1_000);
    let a2 = build_register_action(&w2, cell, "alice", [3u8; 32], 1_000);
    let (Authorization::Signature(r1, _), Authorization::Signature(r2, _)) =
        (&a1.authorization, &a2.authorization)
    else {
        panic!("expected Signature variants");
    };
    assert_ne!(
        r1, r2,
        "different wallets must produce different signatures even for identical action data"
    );
}

// =============================================================================
// Adversarial: transfer attempted by a non-owner
// =============================================================================

/// Transfer authorship is bound to the wallet that signs the action. A
/// non-owner attempting the same logical transfer produces a different
/// `Authorization::Signature`, so the executor's signer-vs-owner check
/// can distinguish them — even though the cell-program slot caveats
/// alone are silent about *who* may write `OWNER_HASH_SLOT`.
///
/// This test pins the two halves of the property today:
///
/// 1. **Authorization differs by signer.** The legitimate owner's
///    transfer and a non-owner's transfer over the same `(name, old,
///    new)` tuple yield different signatures. An executor-side check
///    of `signer_pubkey == owner_pubkey` (or, equivalently, a
///    `StateConstraint::SenderAuthorized { set: AuthorizedSet::PublicRoot { set_root_index: OWNER_HASH_SLOT } }`
///    once the witness-blob plumbing is wired through
///    `AppCipherclerk::make_action`) refuses the impostor.
///
/// 2. **The slot caveats alone do not enforce owner-only writes.** The
///    `name_factory_descriptor` carries `WriteOnce(NAME_HASH_SLOT)`,
///    `Monotonic(EXPIRY_SLOT)`, and `WriteOnce(REVOKED_SLOT)`; none of
///    them gate `OWNER_HASH_SLOT`. The test asserts the program
///    *accepts* a state transition that moves `OWNER_HASH_SLOT`,
///    documenting that the rejection happens at the
///    authorization-layer (signature check on the action), not the
///    state-constraint layer.
///
/// TODO(owner-auth): install
/// `StateConstraint::SenderAuthorized { set: AuthorizedSet::PublicRoot { .. } }`
/// on `name_factory_descriptor()` once `AppCipherclerk::make_action`
/// emits the Merkle-membership witness blob the constraint requires.
/// Until then, owner-only enforcement is the action-authorization
/// layer's job (signature verification + caller-vs-owner equality
/// check), not the cell program's. See README §"Owner authorization".
#[test]
fn adversarial_transfer_from_non_owner_authorization_diverges() {
    let owner_wallet = wallet_with_seed(0xA1);
    let impostor_wallet = wallet_with_seed(0xB2);
    let cell = registry_cell();
    let name = "alice.pyana";
    let old_owner_pk = [0xAAu8; 32];
    let new_owner_pk = [0xCCu8; 32];

    // Both wallets produce the *same* effect payload (the data the
    // executor would write into OWNER_HASH_SLOT is identical) — but the
    // `Authorization::Signature(r, s)` diverges because each wallet's
    // Ed25519 key is distinct.
    let legit = build_transfer_action(&owner_wallet, cell, name, old_owner_pk, new_owner_pk);
    let impostor = build_transfer_action(&impostor_wallet, cell, name, old_owner_pk, new_owner_pk);

    let (Authorization::Signature(r_owner, s_owner), Authorization::Signature(r_imp, s_imp)) =
        (&legit.authorization, &impostor.authorization)
    else {
        panic!("expected Signature variants");
    };
    assert!(
        r_owner != r_imp || s_owner != s_imp,
        "non-owner's signature must diverge from the owner's"
    );

    // ...AND the projection of the impostor's action onto the cell's
    // post-state *would* pass the slot-caveat program (the program
    // does not yet know about OWNER_HASH_SLOT ownership). This is the
    // gap the TODO above tracks.
    let program = fresh_program();
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash(name);
    old.fields[OWNER_HASH_SLOT] = name_hash("legit-owner-cap");
    old.fields[EXPIRY_SLOT] = expiry_field(5_000);
    old.set_nonce(1);
    let mut new = old.clone();
    new.fields[OWNER_HASH_SLOT] = project_setfield(&impostor, OWNER_HASH_SLOT).unwrap();
    new.set_nonce(2);
    program.evaluate(&new, Some(&old), None).expect(
        "state-constraint layer alone does not reject the impostor — \
         authorization layer must (TODO(owner-auth))",
    );
}

// =============================================================================
// Factory descriptor stability
// =============================================================================

#[test]
fn factory_descriptors_publishes_exactly_one_factory_today() {
    let all = factory_descriptors();
    assert_eq!(
        all.len(),
        1,
        "today the nameservice publishes exactly the name factory; future expansions (dispute, registry) should update this assertion deliberately"
    );
    assert_eq!(all[0].factory_vk, NAME_FACTORY_VK);
}

#[test]
fn factory_descriptor_hash_is_deterministic_across_builds() {
    // The descriptor hash is the on-chain identity — two builds must
    // produce the same hash (no map iteration ordering, no rng,
    // no env-dependent fields).
    let h1 = name_factory_descriptor().hash();
    let h2 = name_factory_descriptor().hash();
    assert_eq!(h1, h2);
    assert_ne!(h1, [0u8; 32], "descriptor hash must not be zero");
}

#[test]
fn factory_descriptor_hash_changes_with_state_constraints() {
    // If a future commit adds or removes a slot caveat, the descriptor
    // hash *must* change — that is the constructor-transparency
    // guarantee. We exercise the property by building two descriptors:
    // the canonical one, and one with one fewer state constraint, and
    // checking they hash differently.
    let canonical = name_factory_descriptor();
    let mut weakened = canonical.clone();
    weakened.state_constraints.pop();
    assert_ne!(
        canonical.hash(),
        weakened.hash(),
        "dropping a state constraint must change the factory descriptor hash"
    );
}

#[test]
fn register_function_is_idempotent_across_repeated_calls() {
    let cipherclerk = wallet_with_seed(0x42);
    let executor = pyana_app_framework::EmbeddedExecutor::new(&cipherclerk, "default");
    let ctx = pyana_app_framework::StarbridgeAppContext::new(wallet, executor);
    let vk1 = register(&ctx);
    let vk2 = register(&ctx);
    let vk3 = register(&ctx);
    assert_eq!(vk1, vk2);
    assert_eq!(vk2, vk3);
    assert_eq!(
        ctx.factory_registry().len(),
        1,
        "repeated register() calls must not duplicate the factory entry"
    );
    // Inspectors: name, name-registry, name-register-form.
    assert_eq!(ctx.inspector_registry().len(), 3);
}
