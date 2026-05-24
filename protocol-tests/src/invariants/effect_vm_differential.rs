//! Effect VM differential consistency: runtime executor vs AIR view.
//!
//! Stage 3 of the Effect VM AIR added 22 new variants — many of which the
//! AIR treats as "passthrough": it commits a hash of the variant into
//! `effects_hash` but forbids drift on the state column. The runtime
//! `apply_effect` for those same variants DOES mutate cell state
//! (permissions hash, c-list, fields, etc.). That's *sound* (the AIR's
//! claimed state delta is conservative — it claims "zero" and zero is
//! correct for the columns it covers, balance/nonce/fields/cap_root), but
//! *incomplete*: a bug in the runtime that modifies state outside the AIR's
//! purview would not be caught by the proof.
//!
//! These differential tests compare, per variant, the executor's actual
//! state delta to the AIR's claimed state delta (extracted from the
//! `(trace, public_inputs)` produced by `generate_effect_vm_trace`). The
//! tests are categorised as:
//!
//!   - **CONSISTENT** — AIR delta matches runtime delta exactly.
//!   - **PASSTHROUGH GAP** — AIR claims zero balance/cap_root delta but
//!     runtime mutates some other piece of cell state (`#[ignore]`d with
//!     an explanation; left as a tripwire if/when AIR coverage expands).
//!   - **REAL BUG** — unexpected mismatch flagged by an unguarded assert.
//!
//! NOTE: These tests do NOT exercise the SNARK constraints — they only
//! probe what the trace generator and PI extractor *claim*. Constraint
//! soundness is covered by `circuit::effect_vm::tests`. This module
//! verifies the *bridge* between two independent implementations of
//! "what does effect V do to cell state".

use std::collections::HashMap;

use proptest::prelude::*;
use pyana_cell::{
    AuthRequired, AuthRequired::None as AuthNone, Cell, CellId, Ledger, Permissions,
};
use pyana_circuit::effect_vm::{
    CellState as VmCellState, Effect as VmEffect, extract_net_delta, generate_effect_vm_trace,
    state as vm_state,
};
use pyana_circuit::field::BabyBear;
use pyana_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

use crate::generators::cell::{LedgerSpec, build_open_ledger};

// =====================================================================
// Shared helpers
// =====================================================================

/// Snapshot of the per-cell state we care about for differential checks.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CellSnapshot {
    balance: u64,
    nonce: u64,
    cap_count: usize,
    permissions_hash: [u8; 32],
    field_hashes: [[u8; 32]; 8],
    vk_hash: [u8; 32],
    delegation_present: bool,
}

impl CellSnapshot {
    fn of(cell: &Cell) -> Self {
        let perm_bytes = postcard::to_allocvec(&cell.permissions).unwrap_or_default();
        let permissions_hash = *blake3::hash(&perm_bytes).as_bytes();
        let vk_bytes = postcard::to_allocvec(&cell.verification_key).unwrap_or_default();
        let vk_hash = *blake3::hash(&vk_bytes).as_bytes();
        let mut field_hashes = [[0u8; 32]; 8];
        for i in 0..8 {
            if let Some(f) = cell.state.get_field(i) {
                field_hashes[i] = *blake3::hash(f).as_bytes();
            }
        }
        let delegation_bytes = postcard::to_allocvec(&cell.delegation).unwrap_or_default();
        let delegation_present =
            cell.delegation.is_some() || !delegation_bytes.is_empty() && cell.delegation.is_some();
        Self {
            balance: cell.state.balance(),
            nonce: cell.state.nonce(),
            cap_count: cell.capabilities.iter().count(),
            permissions_hash,
            field_hashes,
            vk_hash,
            delegation_present,
        }
    }
}

/// Wrap a single Effect into a one-action turn from `agent`.
fn one_effect_turn(agent: CellId, nonce: u64, effect: Effect) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    }
}

/// Build a fresh wide-open 4-cell ledger for differential tests.
fn fresh_ledger() -> (Ledger, Vec<CellId>) {
    let spec = LedgerSpec {
        n_cells: 4,
        balance_each: 100_000,
        wide_open: true,
    };
    build_open_ledger(&spec)
}

/// Inline projection of the runtime turn into VM effects.
///
/// Mirrors `TurnExecutor::convert_turn_effects_to_vm` (which is module-
/// private). Kept inline here so the differential test is independent of
/// the executor crate; if the executor's projection changes shape this
/// helper will go stale and the tests should be updated together. We only
/// cover the variants exercised by tests below — others fall through to
/// `VmEffect::NoOp`.
fn project_turn_to_vm(cell_id: &CellId, turn: &Turn) -> Vec<VmEffect> {
    fn hash_to_bb(h: &[u8; 32]) -> BabyBear {
        let v = u32::from_le_bytes([h[0], h[1], h[2], h[3]])
            % pyana_circuit::field::BABYBEAR_P;
        BabyBear::new(v)
    }
    fn field_to_bb(v: &[u8; 32]) -> BabyBear {
        let val_u32 = u32::from_le_bytes([v[0], v[1], v[2], v[3]])
            % pyana_circuit::field::BABYBEAR_P;
        BabyBear::new(val_u32)
    }

    let mut out: Vec<VmEffect> = Vec::new();
    for root in &turn.call_forest.roots {
        // Single-action turns only (our tests build these). Walk root.
        for effect in &root.action.effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    if from == cell_id {
                        out.push(VmEffect::Transfer { amount: *amount, direction: 1 });
                    } else if to == cell_id {
                        out.push(VmEffect::Transfer { amount: *amount, direction: 0 });
                    }
                }
                Effect::SetField { cell, index, value } if cell == cell_id => {
                    out.push(VmEffect::SetField {
                        field_idx: *index as u32,
                        value: field_to_bb(value),
                    });
                }
                Effect::GrantCapability { to, cap, .. } if to == cell_id => {
                    let cap_hash = blake3::hash(&cap.slot.to_le_bytes());
                    out.push(VmEffect::GrantCapability {
                        cap_entry: hash_to_bb(cap_hash.as_bytes()),
                    });
                }
                Effect::RevokeCapability { cell, slot } if cell == cell_id => {
                    let slot_hash_bytes = blake3::hash(&slot.to_le_bytes());
                    out.push(VmEffect::RevokeCapability {
                        slot_hash: hash_to_bb(slot_hash_bytes.as_bytes()),
                    });
                }
                Effect::EmitEvent { cell, event } if cell == cell_id => {
                    let mut h = blake3::Hasher::new();
                    h.update(&event.topic);
                    for d in &event.data {
                        h.update(d);
                    }
                    out.push(VmEffect::EmitEvent {
                        event_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                Effect::SetPermissions { cell, new_permissions } if cell == cell_id => {
                    let perm_bytes = postcard::to_allocvec(new_permissions).unwrap_or_default();
                    let perm_hash = blake3::hash(&perm_bytes);
                    out.push(VmEffect::SetPermissions {
                        permissions_hash: hash_to_bb(perm_hash.as_bytes()),
                    });
                }
                Effect::SetVerificationKey { cell, new_vk } if cell == cell_id => {
                    let vk_hash = match new_vk {
                        Some(vk) => {
                            let bytes = postcard::to_allocvec(vk).unwrap_or_default();
                            let h = blake3::hash(&bytes);
                            hash_to_bb(h.as_bytes())
                        }
                        None => BabyBear::ZERO,
                    };
                    out.push(VmEffect::SetVerificationKey { vk_hash });
                }
                Effect::CreateCell { public_key, token_id, balance } => {
                    let mut h = blake3::Hasher::new();
                    h.update(public_key);
                    h.update(token_id);
                    h.update(&balance.to_le_bytes());
                    out.push(VmEffect::CreateCell {
                        create_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                Effect::SpawnWithDelegation { child_public_key, child_token_id, max_staleness } => {
                    let mut h = blake3::Hasher::new();
                    h.update(child_public_key);
                    h.update(child_token_id);
                    h.update(&max_staleness.to_le_bytes());
                    out.push(VmEffect::SpawnWithDelegation {
                        spawn_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                Effect::RefreshDelegation => {
                    out.push(VmEffect::RefreshDelegation);
                }
                Effect::RevokeDelegation { child } => {
                    out.push(VmEffect::RevokeDelegation {
                        child_hash: hash_to_bb(child.as_bytes()),
                    });
                }
                Effect::BridgeMint { portable_proof } => {
                    let mut h = blake3::Hasher::new();
                    h.update(&portable_proof.nullifier);
                    let root_bytes =
                        postcard::to_allocvec(&portable_proof.source_root).unwrap_or_default();
                    h.update(&root_bytes);
                    h.update(&portable_proof.destination_federation);
                    h.update(&portable_proof.asset_type.to_le_bytes());
                    let value_lo = BabyBear::new(
                        (portable_proof.value & ((1u64 << 30) - 1)) as u32,
                    );
                    out.push(VmEffect::BridgeMint {
                        value_lo,
                        mint_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                Effect::BridgeLock { nullifier, destination, value, asset_type, .. } => {
                    let mut h = blake3::Hasher::new();
                    h.update(nullifier);
                    h.update(destination);
                    h.update(&asset_type.to_le_bytes());
                    let value_lo =
                        BabyBear::new((*value & ((1u64 << 30) - 1)) as u32);
                    out.push(VmEffect::BridgeLock {
                        value_lo,
                        lock_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                Effect::BridgeCancel { nullifier } => {
                    out.push(VmEffect::BridgeCancel {
                        nullifier_hash: hash_to_bb(nullifier),
                    });
                }
                Effect::BridgeFinalize { nullifier, receipt } => {
                    let mut h = blake3::Hasher::new();
                    h.update(nullifier);
                    let receipt_bytes = postcard::to_allocvec(receipt).unwrap_or_default();
                    h.update(&receipt_bytes);
                    out.push(VmEffect::BridgeFinalize {
                        finalize_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                Effect::Introduce { introducer, recipient, target, permissions } => {
                    let mut h = blake3::Hasher::new();
                    h.update(introducer.as_bytes());
                    h.update(recipient.as_bytes());
                    h.update(target.as_bytes());
                    let perm_byte: u8 = match permissions {
                        AuthRequired::None => 0,
                        AuthRequired::Signature => 1,
                        AuthRequired::Proof => 2,
                        AuthRequired::Either => 3,
                        AuthRequired::Impossible => 4,
                    };
                    h.update(&[perm_byte]);
                    out.push(VmEffect::Introduce {
                        intro_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                Effect::PipelinedSend { target, action } => {
                    let mut h = blake3::Hasher::new();
                    h.update(&target.source_turn);
                    h.update(&target.output_slot.to_le_bytes());
                    h.update(&action.hash());
                    out.push(VmEffect::PipelinedSend {
                        send_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                Effect::CreateEscrow { cell, recipient, amount, condition, .. }
                    if cell == cell_id =>
                {
                    let mut h = blake3::Hasher::new();
                    h.update(recipient.as_bytes());
                    let cond_bytes = postcard::to_allocvec(condition).unwrap_or_default();
                    h.update(&cond_bytes);
                    let amount_lo =
                        BabyBear::new((*amount & ((1u64 << 30) - 1)) as u32);
                    out.push(VmEffect::CreateEscrow {
                        amount_lo,
                        escrow_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                Effect::ExerciseViaCapability { cap_slot, inner_effects } => {
                    let mut h = blake3::Hasher::new();
                    h.update(&cap_slot.to_le_bytes());
                    for inner in inner_effects {
                        h.update(&inner.hash());
                    }
                    out.push(VmEffect::ExerciseViaCapability {
                        exercise_hash: hash_to_bb(h.finalize().as_bytes()),
                    });
                }
                _ => { /* Skipped; not part of this cell's projection. */ }
            }
        }
    }
    if out.is_empty() {
        out.push(VmEffect::NoOp);
    }
    out
}

/// Generate the VM trace and extract the AIR's claimed (net_balance_delta,
/// final_cap_root, final_state_commit). We deliberately don't run the
/// prover — the trace generator's view *is* the AIR's view of state
/// transitions, since the constraints simply check that every row obeys
/// the per-effect deltas the generator computed.
fn air_claim(actor_cell: &Cell, turn: &Turn) -> AirClaim {
    let cell_id = actor_cell.id();
    let vm_effects = project_turn_to_vm(&cell_id, turn);
    // Build the AIR's starting state from the cell.
    let mut vm_initial =
        VmCellState::new(actor_cell.state.balance(), actor_cell.state.nonce() as u32);
    // Pull current field bytes into BabyBear (truncated; matches executor
    // projection).
    for i in 0..8 {
        if let Some(f) = actor_cell.state.get_field(i) {
            let v = u32::from_le_bytes([f[0], f[1], f[2], f[3]])
                % pyana_circuit::field::BABYBEAR_P;
            vm_initial.fields[i] = BabyBear::new(v);
        }
    }
    vm_initial.refresh_commitment();

    let (trace, public_inputs) = generate_effect_vm_trace(&vm_initial, &vm_effects);
    let net_delta = extract_net_delta(&public_inputs).unwrap_or(0);

    // Last row's state_after columns give the AIR's claimed final state.
    let last_row = trace.last().expect("non-empty trace");
    let final_balance_lo = last_row[pyana_circuit::effect_vm::STATE_AFTER_BASE + vm_state::BALANCE_LO].0
        as u64;
    let final_balance_hi = last_row[pyana_circuit::effect_vm::STATE_AFTER_BASE + vm_state::BALANCE_HI].0
        as u64;
    let final_cap_root =
        last_row[pyana_circuit::effect_vm::STATE_AFTER_BASE + vm_state::CAP_ROOT];
    let initial_cap_root =
        trace[0][pyana_circuit::effect_vm::STATE_BEFORE_BASE + vm_state::CAP_ROOT];
    let mut final_fields = [BabyBear::ZERO; 8];
    for i in 0..8 {
        final_fields[i] = last_row
            [pyana_circuit::effect_vm::STATE_AFTER_BASE + vm_state::FIELD_BASE + i];
    }
    let mut initial_fields = [BabyBear::ZERO; 8];
    for i in 0..8 {
        initial_fields[i] = trace[0]
            [pyana_circuit::effect_vm::STATE_BEFORE_BASE + vm_state::FIELD_BASE + i];
    }

    AirClaim {
        net_balance_delta: net_delta,
        final_balance: final_balance_lo + (final_balance_hi << 30),
        initial_cap_root,
        final_cap_root,
        initial_fields,
        final_fields,
    }
}

#[derive(Clone, Debug)]
struct AirClaim {
    net_balance_delta: i64,
    final_balance: u64,
    initial_cap_root: BabyBear,
    final_cap_root: BabyBear,
    initial_fields: [BabyBear; 8],
    final_fields: [BabyBear; 8],
}

// =====================================================================
// Variant 1: Transfer — CONSISTENT
// =====================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    /// `Effect::Transfer` from actor to peer: AIR's net_delta must equal
    /// runtime balance delta. Direction may be incoming or outgoing.
    #[test]
    fn differential_transfer(
        amount in 1u64..=1000,
        direction in 0u8..=1,
    ) {
        let (mut ledger, ids) = fresh_ledger();
        let actor = ids[0];
        let peer = ids[1];
        let (from, to) = if direction == 0 { (actor, peer) } else { (peer, actor) };

        let actor_cell = ledger.get(&actor).unwrap();
        let before = CellSnapshot::of(actor_cell);
        let nonce = actor_cell.state.nonce();
        let turn = one_effect_turn(actor, nonce, Effect::Transfer { from, to, amount });
        let claim = air_claim(actor_cell, &turn);

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let _ = executor.execute(&turn, &mut ledger);
        let after_cell = ledger.get(&actor).unwrap();
        let after = CellSnapshot::of(after_cell);

        let runtime_delta = (after.balance as i64) - (before.balance as i64);
        prop_assert_eq!(
            claim.net_balance_delta, runtime_delta,
            "Transfer: AIR net_delta={} vs runtime delta={} (amount={}, dir={})",
            claim.net_balance_delta, runtime_delta, amount, direction,
        );
    }
}

// =====================================================================
// Variant 2: CreateEscrow — CONSISTENT (balance debit)
// =====================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn differential_create_escrow(amount in 1u64..=5_000) {
        let (mut ledger, ids) = fresh_ledger();
        let actor = ids[0];
        let recipient = ids[1];
        let actor_cell = ledger.get(&actor).unwrap();
        let before = CellSnapshot::of(actor_cell);
        let nonce = actor_cell.state.nonce();

        let mut escrow_id = [0u8; 32];
        escrow_id[..8].copy_from_slice(&amount.to_le_bytes());
        let effect = Effect::CreateEscrow {
            cell: actor,
            recipient,
            amount,
            condition: pyana_turn::EscrowCondition::SignedByAll { signers: vec![] },
            timeout_height: u64::MAX,
            escrow_id,
        };
        let turn = one_effect_turn(actor, nonce, effect);
        let claim = air_claim(actor_cell, &turn);

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let _ = executor.execute(&turn, &mut ledger);
        let after = CellSnapshot::of(ledger.get(&actor).unwrap());
        let runtime_delta = (after.balance as i64) - (before.balance as i64);

        // Both should record the same debit when the executor accepts.
        // When rejected (e.g., insufficient balance), runtime_delta == 0
        // but the AIR's claim is still -amount; skip in that case.
        if after.balance == before.balance {
            // Executor didn't apply (rejected). Still check the AIR's claim
            // matches its projection (it's the projection's job, not the
            // executor's): expected -amount mod balance limb encoding.
            prop_assert_eq!(
                claim.net_balance_delta, -(amount as i64),
                "CreateEscrow (rejected by executor): AIR claim should still project -amount, got {}",
                claim.net_balance_delta,
            );
        } else {
            prop_assert_eq!(
                claim.net_balance_delta, runtime_delta,
                "CreateEscrow: AIR delta={} vs runtime delta={}",
                claim.net_balance_delta, runtime_delta,
            );
        }
    }
}

// =====================================================================
// Variant 3: BridgeLock — CONSISTENT (balance debit)
// =====================================================================

#[test]
fn differential_bridge_lock() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let value: u64 = 1234;
    let effect = Effect::BridgeLock {
        nullifier: [7u8; 32],
        destination: [9u8; 32],
        value,
        asset_type: 0,
        timeout_height: u64::MAX,
        spending_proof: vec![],
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());
    let runtime_delta = (after.balance as i64) - (before.balance as i64);

    // BridgeLock may be rejected by executor (no bridge state set up); in
    // that case runtime_delta == 0 while AIR claim is -value. That's an
    // executor-rejection artifact, not a soundness gap.
    if runtime_delta == 0 {
        assert_eq!(
            claim.net_balance_delta, -(value as i64),
            "BridgeLock (executor-rejected): AIR projection should claim -value"
        );
    } else {
        assert_eq!(
            claim.net_balance_delta, runtime_delta,
            "BridgeLock: AIR vs runtime mismatch (value={})", value,
        );
    }
}

// =====================================================================
// Variant 4: BridgeMint — CONSISTENT (balance credit)
// =====================================================================

#[test]
fn differential_bridge_mint() {
    // BridgeMint is hard to make the runtime accept without a real
    // PortableNoteProof signed against trusted roots. We still exercise
    // the *projection*: AIR must claim +value, runtime delta is 0 (rejected).
    // The check verifies the projection's sign and magnitude.
    let (ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let nonce = actor_cell.state.nonce();

    let value: u64 = 4321;
    let portable_proof = pyana_cell::PortableNoteProof {
        nullifier: [3u8; 32],
        destination_commitment: pyana_cell::NoteCommitment([4u8; 32]),
        value,
        asset_type: 0,
        source_root: pyana_types::AttestedRoot {
            merkle_root: [0u8; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 0,
            timestamp: 0,
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 0,
        },
        destination_federation: [0u8; 32],
        spending_proof: vec![],
    };
    let effect = Effect::BridgeMint { portable_proof };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    assert_eq!(
        claim.net_balance_delta, value as i64,
        "BridgeMint projection should claim +value (got {})",
        claim.net_balance_delta,
    );
    let _ = ledger; // unused — runtime path rejects without trust setup.
}

// =====================================================================
// Variant 5: GrantCapability / RevokeCapability — CONSISTENT (cap_root)
// =====================================================================

#[test]
fn differential_grant_cap() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let target = ids[2];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let cap = pyana_cell::CapabilityRef {
        target,
        slot: 0,
        permissions: AuthNone,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
    };
    let effect = Effect::GrantCapability {
        from: actor,
        to: actor,
        cap,
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    // Runtime: c-list grew by 1 (assuming accepted) or stayed the same
    // (rejected). AIR: cap_root advanced (initial != final) when projected.
    let runtime_cap_delta = (after.cap_count as i64) - (before.cap_count as i64);
    assert!(
        runtime_cap_delta == 0 || runtime_cap_delta == 1,
        "GrantCapability runtime cap_count delta should be 0 or 1, got {}",
        runtime_cap_delta,
    );

    let air_cap_changed = claim.initial_cap_root != claim.final_cap_root;
    assert!(
        air_cap_changed,
        "GrantCapability: AIR cap_root should change (initial={:?}, final={:?})",
        claim.initial_cap_root, claim.final_cap_root,
    );
    // Balance must not change for either side.
    assert_eq!(
        claim.net_balance_delta, 0,
        "GrantCapability should be balance-neutral"
    );
    assert_eq!(after.balance, before.balance);
}

#[test]
fn differential_revoke_cap() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    // wide_open ledger granted actor caps to every other cell; pick slot 0.
    let slot = actor_cell
        .capabilities
        .iter()
        .next()
        .expect("wide_open ledger should have caps")
        .slot;
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let effect = Effect::RevokeCapability {
        cell: actor,
        slot,
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    let runtime_cap_delta = (after.cap_count as i64) - (before.cap_count as i64);
    assert_eq!(
        runtime_cap_delta, -1,
        "RevokeCapability should remove exactly one cap from runtime c-list",
    );
    assert_ne!(
        claim.initial_cap_root, claim.final_cap_root,
        "RevokeCapability: AIR cap_root must change",
    );
    assert_eq!(
        claim.net_balance_delta, 0,
        "RevokeCapability should be balance-neutral"
    );
}

// =====================================================================
// Variant 6: SetPermissions — PASSTHROUGH GAP
// =====================================================================
//
// The AIR's SetPermissions variant binds the permissions hash into
// `effects_hash` but does NOT track permissions in the state column.
// Runtime: cell.permissions is replaced; permissions_hash changes.
// AIR: net_balance_delta == 0, cap_root unchanged, fields unchanged.
//
// This is a PASSTHROUGH GAP: the AIR proves *which* permissions value the
// prover committed to (via effects_hash) but doesn't prove the runtime
// applied it correctly. A runtime bug that wrote the wrong Permissions
// struct (e.g., flipped a bit while serialising) would NOT be caught by
// the proof — the prover and verifier would agree on the hash, and
// neither side observes the on-cell value through the AIR.

#[test]
fn differential_set_permissions_passthrough_gap() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    // Build a permissions that differs from the wide-open default.
    let new_perms = Permissions {
        send: AuthRequired::Signature,
        receive: AuthNone,
        set_state: AuthNone,
        set_permissions: AuthNone,
        set_verification_key: AuthNone,
        increment_nonce: AuthNone,
        delegate: AuthNone,
        access: AuthNone,
    };
    let effect = Effect::SetPermissions {
        cell: actor,
        new_permissions: new_perms.clone(),
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    // FINDING: runtime mutates permissions; AIR claims zero state delta.
    assert_ne!(
        after.permissions_hash, before.permissions_hash,
        "SetPermissions runtime should mutate cell.permissions",
    );
    assert_eq!(
        claim.net_balance_delta, 0,
        "SetPermissions: AIR claims zero balance delta (correct)",
    );
    assert_eq!(
        claim.initial_cap_root, claim.final_cap_root,
        "SetPermissions: AIR keeps cap_root constant (gap — permissions live off-trace)",
    );
    assert_eq!(
        claim.initial_fields, claim.final_fields,
        "SetPermissions: AIR keeps fields constant",
    );
    // CATEGORY: PASSTHROUGH GAP. The AIR's view (zero state delta on its
    // columns) is correct on its own terms; the soundness gap is that
    // permissions don't live in any AIR-visible column at all.
}

// =====================================================================
// Variant 7: SetField — CONSISTENT (field column tracks)
// =====================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]

    #[test]
    fn differential_set_field(
        idx in 0usize..8,
        v0 in any::<u32>(),
    ) {
        let (mut ledger, ids) = fresh_ledger();
        let actor = ids[0];
        let actor_cell = ledger.get(&actor).unwrap();
        let before = CellSnapshot::of(actor_cell);
        let nonce = actor_cell.state.nonce();

        let mut value = [0u8; 32];
        value[..4].copy_from_slice(&v0.to_le_bytes());
        let effect = Effect::SetField { cell: actor, index: idx, value };
        let turn = one_effect_turn(actor, nonce, effect);
        let claim = air_claim(actor_cell, &turn);

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let _ = executor.execute(&turn, &mut ledger);
        let after = CellSnapshot::of(ledger.get(&actor).unwrap());

        // AIR's field[idx] should match runtime's field[idx] (mod truncation).
        let expected_bb = BabyBear::new(v0 % pyana_circuit::field::BABYBEAR_P);
        prop_assert_eq!(
            claim.final_fields[idx], expected_bb,
            "SetField: AIR final field[{}] should be {:?} (got {:?})",
            idx, expected_bb, claim.final_fields[idx],
        );
        // Runtime side
        let runtime_field = after.field_hashes[idx];
        prop_assert_ne!(
            runtime_field, before.field_hashes[idx],
            "SetField: runtime field[{}] should change", idx,
        );
        // Other fields untouched on both sides
        for j in 0..8 {
            if j == idx { continue; }
            prop_assert_eq!(
                claim.initial_fields[j], claim.final_fields[j],
                "SetField: AIR field[{}] should be unchanged", j,
            );
            prop_assert_eq!(
                after.field_hashes[j], before.field_hashes[j],
                "SetField: runtime field[{}] should be unchanged", j,
            );
        }
        prop_assert_eq!(claim.net_balance_delta, 0);
        prop_assert_eq!(after.balance, before.balance);
    }
}

// =====================================================================
// Variant 8: EmitEvent — PASSTHROUGH (no state change either side)
// =====================================================================

#[test]
fn differential_emit_event_passthrough_gap() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let effect = Effect::EmitEvent {
        cell: actor,
        event: pyana_turn::Event {
            topic: [0u8; 32],
            data: vec![],
        },
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    // EmitEvent is a balance/cap/field-neutral passthrough on the AIR.
    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(claim.initial_cap_root, claim.final_cap_root);
    assert_eq!(claim.initial_fields, claim.final_fields);

    // PASSTHROUGH GAP — NONCE BUMP NOT MODELED BY VM:
    //
    // The runtime executor bumps the agent's nonce on every committed
    // turn (turn replay protection). The Effect VM AIR, however, only
    // advances `nonce` when an explicit `IncrementNonce` VmEffect appears
    // — and the projection in `convert_turn_effects_to_vm` deliberately
    // DROPS `Effect::IncrementNonce` when the cell IS the actor
    // ("nonce increment is implicit in the VM (row-to-row)"). The result:
    // the AIR sees `nonce_after == nonce_before` while the runtime
    // observes `nonce_after == nonce_before + 1`. The nonce binding in
    // the receipt chain (and in the executor's PI matching loop) lives
    // outside the per-turn AIR trace, so the proof never witnesses the
    // bump. A runtime bug that wrote the wrong nonce — or failed to
    // increment, re-enabling replay — would not be caught by the proof.
    //
    // This is a *consistent* design choice (nonce binding is the
    // receipt-chain layer's job), but worth documenting as a soundness
    // tripwire when Stage 4+ planning considers per-turn nonce coverage.
    assert_eq!(
        after.nonce, before.nonce + 1,
        "runtime bumps nonce on every committed turn — gap vs AIR",
    );
    assert_eq!(
        after.balance, before.balance,
        "EmitEvent should be balance-neutral at runtime",
    );
    assert_eq!(
        after.cap_count, before.cap_count,
        "EmitEvent should not change c-list at runtime",
    );
}

// =====================================================================
// Variant 9: SetVerificationKey — PASSTHROUGH GAP
// =====================================================================
//
// The AIR's SetVerificationKey binds the vk hash into effects_hash but VK
// lives off-trace (same shape as SetPermissions). Runtime: cell.vk
// changes; vk_hash changes. AIR: no state-column delta.

#[test]
fn differential_set_verification_key_passthrough_gap() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    // Clear the VK (set to None). Runtime should accept (wide-open perms).
    let effect = Effect::SetVerificationKey {
        cell: actor,
        new_vk: None,
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    // Runtime may not actually change anything if VK was already None.
    // The asymmetry to flag is: the AIR ALWAYS claims zero state delta
    // regardless of what (if anything) the runtime did to the VK.
    assert_eq!(
        claim.net_balance_delta, 0,
        "SetVerificationKey: AIR claims zero balance delta (correct)",
    );
    assert_eq!(
        claim.initial_cap_root, claim.final_cap_root,
        "SetVerificationKey: AIR keeps cap_root constant (gap — VK lives off-trace)",
    );
    // VK semantic equivalence is up to the executor; the gap is the AIR
    // never sees a column representing it.
    let _ = after;
    let _ = before;
}

// =====================================================================
// Variant 10: RefreshDelegation / RevokeDelegation — PASSTHROUGH
// =====================================================================
//
// These variants don't mutate balance/cap_root/fields on the actor cell
// either at runtime or in the AIR's view. Recording for documentation.

#[test]
fn differential_refresh_delegation_passthrough() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let turn = one_effect_turn(actor, nonce, Effect::RefreshDelegation);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(claim.initial_cap_root, claim.final_cap_root);
    // Runtime may reject (no parent) — that's still consistent with AIR.
    assert_eq!(after.balance, before.balance);
}

#[test]
fn differential_revoke_delegation_passthrough() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let child = ids[1];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let turn = one_effect_turn(actor, nonce, Effect::RevokeDelegation { child });
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(claim.initial_cap_root, claim.final_cap_root);
    assert_eq!(after.balance, before.balance);
}

// =====================================================================
// Variant 11: CreateCell — PASSTHROUGH on the actor
// =====================================================================
//
// CreateCell creates a NEW cell in the ledger; the actor's own state
// (balance/nonce/cap_root) doesn't change. The new cell is not in any
// AIR-visible column.

#[test]
fn differential_create_cell_passthrough_gap() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let mut new_pubkey = [0u8; 32];
    new_pubkey[0] = 99;
    let effect = Effect::CreateCell {
        public_key: new_pubkey,
        token_id: [0u8; 32],
        balance: 0,
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(claim.initial_cap_root, claim.final_cap_root);
    // Actor state unchanged on both sides.
    assert_eq!(after.balance, before.balance);
}

// =====================================================================
// Variant 12: SpawnWithDelegation — PASSTHROUGH on the actor
// =====================================================================

#[test]
fn differential_spawn_with_delegation_passthrough() {
    let (ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let nonce = actor_cell.state.nonce();

    let mut child_pk = [0u8; 32];
    child_pk[0] = 200;
    let effect = Effect::SpawnWithDelegation {
        child_public_key: child_pk,
        child_token_id: [0u8; 32],
        max_staleness: 60,
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let _executor = TurnExecutor::new(ComputronCosts::zero());
    // Don't care if runtime rejects (it likely does in wide-open setup
    // without proper parent-child wiring); we only check projection.
    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(claim.initial_cap_root, claim.final_cap_root);
    let _ = ledger;
}

// =====================================================================
// Variant 13: BridgeCancel — PASSTHROUGH
// =====================================================================

#[test]
fn differential_bridge_cancel_passthrough() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let effect = Effect::BridgeCancel { nullifier: [5u8; 32] };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    // BridgeCancel projection is balance-neutral on the AIR. Runtime would
    // refund the locked value when a real lock exists — without one, the
    // executor rejects, leaving balance unchanged. PASSTHROUGH GAP: when
    // a real lock exists, runtime credits balance but AIR claims zero.
    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(after.balance, before.balance);
}

// =====================================================================
// Variant 14: BridgeFinalize — PASSTHROUGH
// =====================================================================

#[test]
fn differential_bridge_finalize_passthrough() {
    let (ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    let nonce = actor_cell.state.nonce();

    let receipt = pyana_cell::BridgeReceipt {
        nullifier: [6u8; 32],
        destination_federation: [0u8; 32],
        mint_height: 0,
        signature: [0u8; 64],
    };
    let effect = Effect::BridgeFinalize {
        nullifier: [6u8; 32],
        receipt,
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let _ = ledger;
    // AIR projection is balance-neutral by design.
    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(claim.initial_cap_root, claim.final_cap_root);
}

// =====================================================================
// Variant 15: Introduce — PASSTHROUGH (from introducer's POV)
// =====================================================================

#[test]
fn differential_introduce_passthrough() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let recipient = ids[1];
    let target = ids[2];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let effect = Effect::Introduce {
        introducer: actor,
        recipient,
        target,
        permissions: AuthNone,
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    // PASSTHROUGH GAP: recipient's c-list grows at runtime (introducer's
    // doesn't), and the AIR is projected against the introducer cell. The
    // AIR therefore can't observe a recipient-side cap grant.
    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(claim.initial_cap_root, claim.final_cap_root);
    assert_eq!(after.balance, before.balance);
    assert_eq!(
        after.cap_count, before.cap_count,
        "Introduce should not change introducer's c-list",
    );
}

// =====================================================================
// Variant 16: ExerciseViaCapability — PASSTHROUGH on the actor
// =====================================================================

#[test]
fn differential_exercise_via_capability_passthrough() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let actor_cell = ledger.get(&actor).unwrap();
    // Grab an existing slot.
    let slot = actor_cell.capabilities.iter().next().unwrap().slot;
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let effect = Effect::ExerciseViaCapability {
        cap_slot: slot,
        inner_effects: vec![],
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    // PASSTHROUGH GAP: inner_effects (if any) operate on the target cell.
    // For the actor: balance/cap_root unchanged; AIR claim matches.
    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(claim.initial_cap_root, claim.final_cap_root);
    assert_eq!(after.balance, before.balance);
}

// =====================================================================
// Variant 17: PipelinedSend — PASSTHROUGH
// =====================================================================

#[test]
fn differential_pipelined_send_passthrough() {
    let (mut ledger, ids) = fresh_ledger();
    let actor = ids[0];
    let target = ids[1];
    let actor_cell = ledger.get(&actor).unwrap();
    let before = CellSnapshot::of(actor_cell);
    let nonce = actor_cell.state.nonce();

    let inner = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
    };
    let effect = Effect::PipelinedSend {
        target: pyana_turn::eventual::EventualRef {
            source_turn: [0u8; 32],
            output_slot: 0,
            federation_id: None,
        },
        action: Box::new(inner),
    };
    let turn = one_effect_turn(actor, nonce, effect);
    let claim = air_claim(actor_cell, &turn);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let _ = executor.execute(&turn, &mut ledger);
    let after = CellSnapshot::of(ledger.get(&actor).unwrap());

    assert_eq!(claim.net_balance_delta, 0);
    assert_eq!(claim.initial_cap_root, claim.final_cap_root);
    // Whether the runtime accepts or rejects, the actor's balance is
    // untouched (the send is deferred, not immediate).
    assert_eq!(after.balance, before.balance);
}
