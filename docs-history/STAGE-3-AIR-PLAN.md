# Stage 3 Effect VM AIR additions — implementation plan

**STATUS: COMPLETE (2026-05-24).** All 22 originally-shimmed Effect
variants now have real AIR coverage; `push_pending_shim` is fully
removed from `convert_turn_effects_to_vm`. NUM_EFFECTS grew from 24
to 46; EFFECT_VM_WIDTH 83 → 105. `test_stage3_multi_variant_compose`
exercises 23 variants in one trace and verifies end-to-end.

The plan below documents the per-variant decisions taken during
implementation. The recommended order was followed loosely; later
batches combined related variants when their constraint shape allowed
(e.g., the passthrough loop sweeps 14 selectors at once).

Implementation commits (in order):
- `ec9b2469` RevokeCapability
- `d4a66dbf` EmitEvent
- `5dc88065` SetPermissions
- `528aec6e` SetVerificationKey
- `8a64d81f` CreateSealPair, RefreshDelegation, RevokeDelegation
- `8d32aa42` CreateCell, SpawnWithDelegation, BridgeCancel, ExerciseViaCapability
- `845a4cc2` Introduce, PipelinedSend
- `3475bb64` CreateEscrow, BridgeLock (balance debit), CreateCommittedEscrow
- `d9d7687b` align compute_balance_delta_from_effects with new debit variants
- `bec93808` BridgeMint, BridgeFinalize, ReleaseEscrow, RefundEscrow, ReleaseCommittedEscrow, RefundCommittedEscrow
- `cea77c6c` remove unused push_pending_shim helper + multi-variant compose test
- `f2b84cb7` retire effect-vm-pending-shim feature

Produced 2026-05-24 from a read-only Explore investigation of the codebase
following the demo passing end-to-end (commit `0141c509`). This document is
the bridge between the current state (18 honest VM variants, 23 shimmed)
and Stage 3 of `EFFECT-VM-SHAPE-A.md`.

## Variants in scope

| Variant | Status | Recommended order |
|---|---|---|
| `IncrementNonce` | **Already complete** — implicit via row-to-row nonce continuity at `circuit/src/effect_vm.rs:1587-1590` and per-effect `new_state.nonce += 1`. The projection at `turn/src/executor.rs:1796-1799` correctly skips emitting an effect. | N/A (no work) |
| `RevokeCapability` | Safest first attempt; mirrors `GrantCapability` (already real) | **1** |
| `EmitEvent` | Stateless side effect; just commits event hash | **2** |
| `SetVerificationKey` | Needs old-state context threading; binding is effects-hash-only | **3** |

## What every Stage 3 addition shares

Adding any new VM `Effect` variant entails a single coordinated landing:

1. `circuit/src/effect_vm.rs`:
   - **Bump `NUM_EFFECTS`** from 24 → N (line 112)
   - **Bump `EFFECT_VM_WIDTH`** from 83 → 83 + (N-24) (line 109) and update
     the layout comment at lines 102-108
   - **Add a selector const** in `mod sel { ... }` (lines 115-158)
   - **Add the `Effect` enum variant** (around lines 510-731)
   - **Add selector encoding** in `generate_effect_vm_trace_ext` (around line 3218)
   - **Add per-row population** in the per-effect match arm (around line 3238)
   - **Add the AIR constraints** in the constraint emission code (search for
     other variants' constraint patterns)
   - **Add a unit test** at the bottom of the file

2. `turn/src/executor.rs::convert_turn_effects_to_vm`:
   - **Remove `push_pending_shim(vm_effects, 0xNNN)`** for the variant
   - **Replace with a real `VmEffect::<NewVariant> { ... }` push**

3. **Coordination risk**: adding a selector shifts the per-column layout
   (state_before starts at index `NUM_EFFECTS`, params at `NUM_EFFECTS + 14`,
   etc.). Any code that hardcodes column indices needs auditing. The verifier
   is in the same crate so it stays in sync automatically.

## RevokeCapability — concrete first attempt

### Files

- `circuit/src/effect_vm.rs`
- `turn/src/executor.rs`

### Diff sketch

```rust
// circuit/src/effect_vm.rs

// 1. Bump constants
pub const EFFECT_VM_WIDTH: usize = 84;  // was 83
pub const NUM_EFFECTS: usize = 25;       // was 24

// 2. Add selector
pub mod sel {
    // ... existing 24 ...
    /// RevokeCapability: remove a capability from the c-list (Merkle update).
    pub const REVOKE_CAPABILITY: usize = 24;
}

// 3. Add Effect variant (after GrantCapability around line 518)
RevokeCapability {
    /// Hash of the revoked slot (4-byte truncated BLAKE3 of u32 slot).
    slot_hash: BabyBear,
},

// 4. In generate_effect_vm_trace_ext selector mapping
Effect::RevokeCapability { .. } => sel::REVOKE_CAPABILITY,

// 5. Per-row population
Effect::RevokeCapability { slot_hash } => {
    row[PARAM_BASE + 0] = *slot_hash;
    // cap_root update: new_root = hash_2_to_1(old_root, slot_hash)
    new_state.capability_root = hash_2_to_1(current_state.capability_root, *slot_hash);
    new_state.nonce += 1;
}

// 6. AIR constraint: mirror GrantCapability's cap_root binding,
//    gated on sel::REVOKE_CAPABILITY.
```

```rust
// turn/src/executor.rs::convert_turn_effects_to_vm (lines 1775-1777)

Effect::RevokeCapability { cell, slot } if cell == cell_id => {
    let slot_bytes = slot.to_le_bytes();
    vm_effects.push(VmEffect::RevokeCapability {
        slot_hash: hash_to_bb(&blake3::hash(&slot_bytes).as_bytes()),
    });
}
```

### Verification checklist

- [ ] `cargo check --workspace --all-targets` clean
- [ ] `cargo test -p pyana-circuit effect_vm` — existing tests still pass
- [ ] New `test_revoke_capability` exercises a single-effect trace with
      non-zero starting cap_root and asserts it changes
- [ ] `bash demo/two-ai-handoff/run.sh` still PASS — the demo doesn't use
      RevokeCapability but the AIR width change might shift verifier
      expectations; both prover and verifier rebuild from the same crate
      so should stay consistent
- [ ] `cargo test -p pyana-protocol-tests --lib` still 11/11

### Risk specifics

- Selector width: 24 → 25 (one new selector column inserted)
- State_before now starts at index 25 (was 24); state_after at 39 (was 38); etc.
- Any test or code that hardcodes those base offsets needs updating
- The `EffectVmAir::new(trace_len)` signature is unchanged
- The proof's `air_name` stays "pyana-effect-vm-v1" — the verifier's VK hash
  is the SHA-256 of that string and stays the same

## EmitEvent — second attempt

After RevokeCapability lands and demo still passes:

```rust
// circuit/src/effect_vm.rs
pub const EFFECT_VM_WIDTH: usize = 85;
pub const NUM_EFFECTS: usize = 26;
pub mod sel {
    pub const EMIT_EVENT: usize = 25;
}
EmitEvent {
    cell_id: BabyBear,
    event_hash: BabyBear,
},

// turn/src/executor.rs (lines 1784-1786)
Effect::EmitEvent { cell, event } if cell == cell_id => {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&event.topic);
    for d in &event.data { hasher.update(d); }
    let event_hash = hasher.finalize();
    vm_effects.push(VmEffect::EmitEvent {
        cell_id: hash_to_bb(cell_id.as_bytes()),
        event_hash: hash_to_bb(event_hash.as_bytes()),
    });
}
```

EmitEvent's constraint is pure state-passthrough + event_hash into the
effects accumulator. No cap_root change.

## SetVerificationKey — third attempt

Requires threading the cell's current VK hash into `convert_turn_effects_to_vm`
so the AIR can bind `old_vk_hash → new_vk_hash`. The function signature
currently takes `(cell_id, turn)`; would need ledger or cell state too.
This is more invasive than the first two and warrants its own design pass.

## Why we didn't land this overnight

The selector-width expansion shifts every downstream column index. While
the diff is "small" by line count (~30 lines per variant), the *coordination*
across the 7000-line `effect_vm.rs` is non-trivial — any forgotten hardcoded
offset breaks the AIR silently (the trace looks right but the constraint
checks wrong columns).

The demo passes today with 10/10 post-conditions and 11/11 protocol-test
invariants. Stage 3 is the natural next milestone but should be a deliberate
landing during a session where the demo can be re-run after each step.

## What's NOT in scope here

- `SetPermissions` (D-style: changes a cell's permissions — would require
  adding permissions to the VM state)
- `CreateSealPair` (related to seal/unseal — Stage 3 candidate but harder)
- `Introduce` / `PipelinedSend` — Stage 7 CapTP work, needs
  `DESIGN-captp-integration.md`
- Bridge variants — Stage 6, needs `DESIGN-receipts.md`
- Escrow variants — Stage 5, needs escrow_root cell-state column
