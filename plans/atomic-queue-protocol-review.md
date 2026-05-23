# Atomic Queue Protocol Review: Distributed Protocol Bugs

**Date:** 2026-05-23
**Scope:** AtomicQueueTx (selector 22), QueueTransaction, MerkleQueue, TurnExecutor

---

## Summary

Seven distributed protocol issues analyzed. Found **3 real bugs**, **1 design gap worth documenting**, and **3 safely handled cases**. The most critical bug is a deposit accounting mismatch between the circuit and executor.

---

## Issue 1: Stale Root Attack (TOCTOU)

**Status: SAFELY HANDLED (with caveat)**

### Analysis

The circuit constrains:
```
old_f4 == combined_old_root (param)
new_f4 == combined_new_root (param)
```

For proof-carrying sovereign turns, `verify_and_commit_proof()` (executor.rs:928) checks:
1. Retrieves `old_commitment` from ledger (line 940)
2. Reconstructs public inputs including the old_commitment
3. Verifies STARK proof against those public inputs
4. Updates commitment only if proof passes

For hosted turns, `Effect::QueueAtomicTx` at executor.rs:5792 operates **directly on the ledger** with a journal for rollback.

### Why it's safe

- **Hosted path:** The executor takes an exclusive mutable reference to the ledger (`&mut Ledger`). The nonce check at line 1459 prevents replay. The journal provides atomicity. There is no concurrent access -- the executor processes turns sequentially.
- **Sovereign path:** The commitment comparison at line 940 (`get_sovereign_commitment`) reads the CURRENT stored commitment. If Bob's turn was ordered first by tau, the commitment has already changed, so Alice's proof (which binds to the OLD commitment via PI[OLD_COMMIT]) will fail verification because `old_commitment != stored_commitment`.
- **Tau ordering:** Turns are totally ordered. The executor processes them one at a time. No TOCTOU exists because check and use happen within the same synchronous call.

### Caveat

If the executor were ever made concurrent (e.g., speculative execution with rollback), a TOCTOU could emerge. The current design is safe because:
1. `execute()` takes `&mut Ledger` (exclusive borrow)
2. Sovereign commitment check and update are in the same function call

---

## Issue 2: Concurrent Atomic Transactions (Double Dequeue)

**Status: SAFELY HANDLED**

### Scenario
- Alice: AtomicTx { dequeue from A, enqueue to B }
- Bob: AtomicTx { dequeue from A, enqueue to C }
- Both read queue A's root at the same time

### Analysis

This is resolved by **tau ordering** (total order on turns):

1. Tau orders Alice before Bob (or vice versa).
2. Alice's turn executes first. In the hosted path, the executor mutates queue A (decrementing length, changing field[4]). In the sovereign path, the commitment updates.
3. When Bob's turn executes, queue A's state has changed. For hosted turns: if the queue now has length 0, the dequeue fails at line 5888 ("queue is empty"). For sovereign turns: Bob's proof binds to the OLD combined root (which no longer matches the stored commitment), so `verify_and_commit_proof` rejects at line 1022.
4. No livelock: the loser's turn is simply rejected with an error, and the agent must retry with a fresh root.

### Resolution mechanism
- First-in-wins (tau ordering determines "first")
- Loser gets turn rejected (fee still charged for hosted, since Phase 1 is never rolled back)
- No livelock because each rejected turn is terminal (nonce already incremented)

---

## Issue 3: Cross-Queue Deadlock

**Status: SAFELY HANDLED**

### Scenario
- Alice: AtomicTx { dequeue from A, enqueue to B }
- Bob: AtomicTx { dequeue from B, enqueue to A }

### Analysis

Sequential execution (guaranteed by `&mut Ledger`) prevents deadlock:
1. Tau orders one first (say Alice).
2. Alice's transaction executes atomically: dequeue A, enqueue B. Both succeed.
3. Bob's transaction now tries to dequeue from B (which has Alice's message) and enqueue to A.
4. This succeeds IF B is non-empty and A is not full.

There is no deadlock because:
- There is no locking. The executor runs ops sequentially within a single function call.
- Within `Effect::QueueAtomicTx` (executor.rs:5792), ops execute in order within the `for op in operations` loop.
- The journal provides rollback if any op fails.

The only potential issue: if both transactions were submitted "simultaneously" in the same block, the ordering is still determined by tau. No deadlock, just serialized execution.

---

## Issue 4: Proof Validity vs Execution Validity (Stale Proof Acceptance)

**Status: SAFELY HANDLED**

### Analysis

The concern: a prover produces a valid proof for a STALE state (roots that WERE valid at time T but not at time T+N).

The executor (`verify_and_commit_proof`, line 940-946) **always** reads the CURRENT stored commitment:
```rust
let old_commitment = if let Some(c) = ledger.get_sovereign_commitment(cell_id) {
    *c
} else if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
    reg.commitment
} else {
    return Err(TurnError::SovereignNotRegistered { cell: *cell_id });
};
```

Then at lines 1009-1055, it compares the proof's PI[OLD_COMMIT] against this stored value. If they don't match, the turn is rejected:
```rust
if got != *expected_bb {
    if i == effect_vm::pi::OLD_COMMIT {
        return Err(TurnError::SovereignCommitmentMismatch { ... });
    }
}
```

So: a valid proof for a stale state is ALWAYS rejected. The applicability check is in the executor, not just the circuit. This is correct.

---

## Issue 5: Pipeline Routing Conflicts (Same-Turn Double Dequeue)

**Status: SAFELY HANDLED**

### Analysis

Two PipelineStep effects in the same turn, both dequeuing from the same source.

The Effect VM uses **row-to-row state threading** (transition constraint, line 2179-2183):
```rust
// next_row.state_before == this_row.state_after
for i in 0..state::SIZE {
    let c = next[STATE_BEFORE_BASE + i] - local[STATE_AFTER_BASE + i];
    combined = combined + alpha_pow * c;
}
```

This means:
- Row N's state_after.field[4] = source_new_root_1
- Row N+1's state_before.field[4] = source_new_root_1 (chained)
- Row N+1's PipelineStep uses source_new_root_1 as its source_old_root

The second dequeue operates on the ALREADY-UPDATED root. The constraint at line 2074 enforces:
```
old_f4 == source_old (param)
```

So the prover MUST set the second PipelineStep's `source_old_root` param to the new root from the first step. If they use the stale root, the constraint fails.

This is correct: sequential within trace, state properly threaded.

---

## Issue 6: Partial Failure in AtomicQueueTx (Witness Generation Panic)

**Status: BUG -- Denial-of-Service Vector**

### Analysis

In the **hosted executor path** (executor.rs:5792), if a dequeue fails:
```rust
if current_len == 0 {
    return Err((TurnError::InvalidEffect { ... }, path.to_vec()));
}
```

This returns an error, and the journal rolls back. The agent pays the fee (Phase 1 committed). This is handled correctly.

In the **circuit witness generation** path (effect_vm.rs:2939-2962), the `generate_effect_vm_trace` function for `AtomicQueueTx`:
```rust
Effect::AtomicQueueTx { ... } => {
    new_state.fields[4] = *combined_new_root;
    let inner = hash_2_to_1(*combined_old_root, *combined_new_root);
    let binding_hash = hash_2_to_1(*tx_hash, inner);
    row[AUX_BASE + 0] = binding_hash;
    new_state.nonce += 1;
}
```

There is NO validation here. If the prover constructs an `AtomicQueueTx` effect where:
- `combined_old_root` does not actually match `state.fields[4]`

The witness generation will succeed (no panic), BUT the generated trace will fail the constraint:
```
s_atomic_tx * (old_f4 - combined_old) != 0
```

So the prover cannot generate a valid proof for an invalid atomic transaction. The circuit catches it.

**However**, the witness generation does NOT check feasibility before attempting proof generation. A malicious client could submit turns that require expensive proof generation only to fail at the constraint level. But this is no worse than any other invalid proof attempt -- the fee is already charged.

**Real concern:** In `convert_turn_effects_to_vm` (executor.rs:1254-1343), `QueueAtomicTx` falls through to the catch-all `_ => NoOp` branch. This means sovereign cells using proof-carrying turns CANNOT prove atomic queue transactions. The VM effects conversion silently drops the AtomicQueueTx semantics.

**Severity: Medium.** Sovereign cells cannot use AtomicQueueTx via proof-carrying turns. The circuit supports it, but the executor's conversion path does not. This is either an intentional limitation (atomic txs only for hosted cells) or a missing implementation.

---

## Issue 7: Deposit Accounting Across Atomic Operations

**Status: BUG -- Critical Mismatch Between Circuit and Executor**

### Analysis

**Circuit (effect_vm.rs:2016-2021):**
```rust
// Balance unchanged.
let c_atx_bal_lo = s_atomic_tx * (new_bal_lo - old_bal_lo);
let c_atx_bal_hi = s_atomic_tx * (new_bal_hi - old_bal_hi);
```

The circuit constrains that AtomicQueueTx does NOT change the balance.

**Executor (executor.rs:5833-5851):**
```rust
// For Enqueue ops within QueueAtomicTx:
ledger.get_mut(actor).unwrap().state.balance -= *deposit;
ledger.get_mut(queue).unwrap().state.balance += *deposit;

// For Dequeue ops: refund
ledger.get_mut(queue).unwrap().state.balance -= refund;
ledger.get_mut(action_target).unwrap().state.balance += refund;
```

The executor DOES transfer deposits during atomic transactions.

### The Bug

If a sovereign cell attempts to prove an AtomicQueueTx that involves deposits:
1. The circuit forces balance_unchanged
2. But the actual state transition involves deposit transfers
3. The proof cannot capture the real state transition

**Impact:**
- For **hosted cells** (majority of current usage): Not a bug. The executor handles deposit accounting directly in the ledger. The circuit proof is not used.
- For **sovereign cells** using proof-carrying turns: The circuit's AtomicQueueTx effect CANNOT capture deposit flows. A sovereign cell proving an atomic tx that moves deposits will produce a proof that doesn't match the real state change.

**This creates two sub-problems:**

1. **Net-zero deposit attack (hypothetical):** An attacker constructs an AtomicQueueTx where they enqueue with deposit X and dequeue with refund X (net zero). The circuit accepts this because balance is unchanged. But the TIMING matters -- the refund comes from the queue's balance pool, not the original deposit. If the attacker exploits this to claim a refund that exceeds what was actually deposited at the time of dequeue, they could drain the queue's deposit pool.

2. **Semantic mismatch:** The circuit says "atomic queue ops don't touch balance." The executor says "atomic queue ops DO transfer deposits." These cannot both be correct for the same operation. Either:
   - (a) The circuit is wrong and should include deposit handling, OR
   - (b) The circuit AtomicQueueTx is intentionally deposit-free (pure root transition) and deposits are handled by surrounding Transfer effects in the same turn

### Likely Intent

Looking at the design, option (b) seems intended: the circuit's AtomicQueueTx proves only the ROOT TRANSITION (combined_old -> combined_new), while separate Transfer effects in the same turn handle deposit flows. The row-to-row state threading would connect them.

However, this is NOT enforced. There is no constraint that an AtomicQueueTx MUST be accompanied by Transfer effects for deposits. A malicious prover could prove an atomic tx without the corresponding deposit transfers, effectively executing a "free" atomic transaction.

### Proposed Fix

Add deposit delta parameters to the circuit's AtomicQueueTx:
```rust
// New params needed:
pub const ATOMIC_TX_DEPOSIT_DELTA_LO: usize = 4;  // net deposit change (lo limb)
pub const ATOMIC_TX_DEPOSIT_DELTA_SIGN: usize = 5; // 0=credit, 1=debit

// New constraint:
// new_bal_lo = old_bal_lo - deposit_delta * (2*sign - 1)
// OR: new_bal_lo = old_bal_lo + deposit_delta * (1 - 2*sign)
```

Alternatively, document that AtomicQueueTx is a pure root transition and deposits MUST be handled by separate EnqueueMessage/DequeueMessage effects within the same turn.

---

## Additional Finding: `convert_turn_effects_to_vm` Missing Branches

**Status: BUG -- Incomplete Implementation**

The function at executor.rs:1254 that converts ledger-level effects to circuit-level effects has a catch-all:
```rust
_ => {
    vm_effects.push(VmEffect::NoOp);
}
```

This means the following effects are silently mapped to NoOp for proof-carrying sovereign cells:
- QueueAllocate
- QueueEnqueue
- QueueDequeue
- QueueResize
- QueueAtomicTx
- QueuePipelineStep
- GrantCapability (when target is not cell_id)
- BridgeLock, BridgeFinalize, BridgeCancel
- CreateEscrow, ReleaseEscrow, etc.

**Impact:** Sovereign cells using proof-carrying turns cannot prove storage queue operations. The proof will succeed (NoOp constraints are trivially satisfied), but it won't actually constrain the queue state transition. The executor will update the commitment without verifying that the queue operations were valid.

**Severity: High.** This effectively makes queue operations for sovereign cells unproven -- the executor accepts any claimed new_commitment without verifying the queue state transition is correct.

---

## Adversarial Tests Added

Tests added to `teasting/tests/storage_faults.rs` covering:
1. Stale root rejection for sovereign cells
2. Concurrent dequeue conflict resolution
3. Cross-queue deadlock non-occurrence
4. Deposit accounting mismatch detection
5. Witness generation with infeasible combined_old_root

---

## Recommendations

1. **P0 (Critical):** Fix deposit accounting in AtomicQueueTx circuit constraint. Either add deposit delta params or document+enforce that deposits are handled by separate effects.

2. **P0 (Critical):** Add proper branches for queue effects in `convert_turn_effects_to_vm` so sovereign cells' queue operations are actually constrained by the circuit.

3. **P1 (Important):** Add integration tests that verify a sovereign cell's proof-carrying AtomicQueueTx actually constrains the state transition (not just a NoOp pass-through).

4. **P2 (Defensive):** Add a runtime assertion in `verify_and_commit_proof` that checks whether the turn contains queue effects and warns/rejects if the sovereign cell's proof doesn't actually constrain them.
