# Turn Executor Audit — `turn/src/executor.rs` + neighborhood

**Auditor model:** Claude Opus 4.7
**Date:** 2026-05-23
**Scope:** `turn/src/executor.rs` (8558 lines) plus `turn.rs`, `journal.rs`, `verify.rs`, `fast_path.rs`, `conditional.rs`, `eventual.rs` (skimmed), `action.rs::Effect`, and the `apps/*` call-site sanity check.

## Verdict: **NEEDS-WORK** (one CRITICAL, multiple P0/P1).

The "classical" `execute()` path is mostly disciplined: nonce is checked, fee+nonce commit in a non-rollback Phase 1, the journal-based rollback is comprehensive, and `verify_authorization` is fail-closed on missing ProofVerifier. But several *peer* execution surfaces — `MixedAtomicTurn`, the fast path's "signatures," `execute_mixed_atomic`'s hosted effects, the proof-carrying sovereign commitment encoding, and the receipt-chain self-binding — are load-bearing and broken or aspirational.

## Summary

The executor sits at the EXECUTOR-TRUSTED ↔ TRUSTLESS boundary. For the classical path (`execute`), it owns: nonce monotonicity per agent cell, fee debit, capability/permission gating per action, balance conservation (`excess` + note-conservation), journal-based atomic rollback, and receipt emission. For the trustless path (`execute` with `Some(execution_proof)`, plus `execute_atomic_sovereign`, `execute_mixed_atomic`, `verify_and_commit_proof`), it owns: proof verification, mapping turn effects → circuit Effect VM PIs, and commitment updates.

The classical path is the most carefully written code in the crate. The two real issues there are scoped: (i) the executor records `previous_receipt_hash` from the *turn* into the *receipt* without comparing it against the agent's last-known head, so receipt-chain integrity is enforced only off-chain in `verify::verify_receipt_chain`; (ii) the `CellMigrationManager` is stored on the executor but never queried — a "frozen" cell can still be the agent or target of a turn.

The trustless paths are where the real damage is. (a) `MixedAtomicTurn::hosted_effects` are tuples `(CellId, Vec<Effect>)` that the executor *applies* (computing Transfer deltas and mutating balances) **without verify_authorization, capability, signature, or precondition checks** — anyone who can call `execute_mixed_atomic` can mutate any cell's balance subject only to a cross-domain conservation invariant balanced by a sovereign proof they control. (b) The fast path's `compute_turn_sign_signature` is a BLAKE3 keyed-hash whose "key" is the validator's *public* identity — `verify_turn_sign` checks `expected == sign.signature`, so anyone who knows a validator's public key can forge that validator's lock-ack. (c) The sovereign commitment is encoded as 32 bytes but `commitment_to_babybear` reads only the **first 4 bytes** (`u32::from_le_bytes`) — sovereign cell state commitments are effectively 31-bit. A trillion sovereign cells with identical first-4-bytes are indistinguishable to the proof-verification check.

The Effect VM bridging (`convert_turn_effects_to_vm`) also truncates 32-byte hashes to a single BabyBear via `% BABYBEAR_P` on the first 4 bytes — the same pattern flagged in AUDIT-cclerk.md P2-5, and bilaterally consistent (executor and cclerk both truncate), but this means many distinct turns map to the same effects-hash PI, so the proof "binds" to a coarse equivalence class rather than the turn.

## Findings by severity

### CRITICAL

**C1 — `execute_mixed_atomic` applies untrusted hosted effects with no authorization** (`turn/src/executor.rs:8123-8364`, in particular 8297-8314 + 8349-8357).
`MixedAtomicTurn::hosted_effects: Vec<(CellId, Vec<Effect>)>` is consumed by computing each cell's net Transfer delta and then directly mutating `cell.state.balance += delta` (or `-=`) on commit. No `verify_authorization`, no permission check, no precondition check, no capability check, no signature, no nonce on the affected cells. The only constraint is that the sum of sovereign (proven) deltas and hosted deltas is zero, which an adversary can satisfy by providing a sovereign proof whose `net_delta` complements their target hosted mutation. Effect kinds other than `Transfer` in `hosted_effects` are silently ignored (not applied), but `Transfer` alone is sufficient to drain or inflate any hosted cell.
**Fix**: route every effect in `hosted_effects` through `apply_effect` with full `verify_authorization` against the original signed turn (carry authorizations alongside the effects), or remove `MixedAtomicTurn` entirely until the proof model covers hosted side as well.

### P0

**P0-1 — Fast-path "signatures" are forgeable BLAKE3-keyed hashes keyed on public identities.** (`turn/src/fast_path.rs:516-536`). `compute_turn_sign_signature` keys a BLAKE3 hasher with `validator_key: &[u8;32]`. The same `validator_key` is the validator's public identity emitted in `TurnSign.validator_key` and used by `verify_turn_sign` to recompute the expected hash. Anyone who knows the public identity can forge a "signature" indistinguishable from the real one. Combined with the BFT-skipping fast path (which trusts 2f+1 of these "signatures"), a single attacker who knows the public keys of 2f+1 validators (which are *public*) can fabricate a certificate. The comment ("In production, this would be a proper Ed25519 signature") acknowledges this is unfinished, but the type, the verifier, and the certificate machinery all present as production-shaped. **Fix**: replace with Ed25519 over `turn_hash` using a validator signing key distinct from the public identity; gate `verify_turn_sign` and `execute_certified_turn` behind `#[cfg(test)]` until then.

**P0-2 — Sovereign commitment is only 32 bits of entropy (~31 after field reduction).** (`turn/src/executor.rs:1225-1228`, mirror of cclerk `bytes32_to_babybear` at 1175). `commitment_to_babybear` reads `u32::from_le_bytes(bytes[0..4])` and constructs a `BabyBear` (≈31-bit field). The stored 32-byte commitment is just a `u32` in the low bytes; the proof's `OLD_COMMIT`/`NEW_COMMIT` PIs are single BabyBears. Collisions across the entire sovereign state space happen with ~50% probability at ~50k cells (birthday). A targeted second-preimage on a specific cell's state requires ~2^31 work — feasible offline. **Fix**: encode the commitment as the full 8-BabyBear (`bytes32_to_babybear` at line 1175 is the right shape) and have the circuit's PI layout expose 8 elements for `OLD_COMMIT`/`NEW_COMMIT`. This is a circuit-side and executor-side change; see AUDIT-circuit.md for the matching prover gap.

**P0-3 — `execute` does not enforce `previous_receipt_hash` against any live head.** (`turn/src/executor.rs:1532-2062`, especially 1693 + 2033). The executor *records* `turn.previous_receipt_hash` into the emitted receipt but never compares it to the agent's last receipt hash (which it does not store). Consequence: a cclerk that hard-codes `previous_receipt_hash: None` (as `build_authorized_turn`, `allocate_queue`, `enqueue_message`, `dequeue_message`, `atomic_queue_tx` all do — see AUDIT-cclerk.md P3-6) produces turns that *look* like genesis turns; the executor cannot detect that the chain was broken. Off-chain `verify_receipt_chain` will catch this only if the verifier has the full chain. The receipt-chain "self-bound history" property in the rustdoc is therefore unenforced at write time. **Fix**: maintain a per-agent `last_receipt_hash` in the ledger (or on the cell), and reject any non-first turn whose `previous_receipt_hash != Some(last)`. Allow a one-time opt-in via cell state for new agents.

**P0-4 — `CellMigrationManager` is plumbed but never consulted.** (`turn/src/executor.rs:243-466` defines the manager; `563` stores it on the executor; `is_frozen` exists at 425; *no* call to `is_frozen` exists in `execute()`, `apply_effect()`, or any atomic/sovereign path). A cell marked "frozen for migration" is fully writable. Migration bundles can be sent while the cell continues to evolve, leading to divergent state at the destination federation. **Fix**: at the top of `execute()` and inside `apply_effect` for every effect that mutates a cell, check `cell_migrations.lock().unwrap().is_frozen(cell_id)` and reject with `TurnError::CellFrozen { cell }`. Add a corresponding error variant.

### P1

**P1-1 — `verify_and_commit_proof` does not validate `execution_proof_new_commitment` is bound to anything the cclerk signed.** (`turn/src/executor.rs:953` + `compute_turn_bytes` per AUDIT-cclerk P2-10). The new commitment comes from `turn.execution_proof_new_commitment`. The executor confirms it equals the PI in the proof, but `Turn::hash()` (turn.rs:132-164) does NOT include `execution_proof`, `execution_proof_cell`, or `execution_proof_new_commitment`. An attacker who intercepts a signed Turn in flight can swap the proof and the new commitment for a different, valid (proof, new_commitment) pair (proof is unauthenticated; only its internal PI structure is checked) — the executor will accept it because the turn hash and signature still verify against the old fields. **Fix**: include execution_proof/_cell/_new_commitment in `Turn::hash()` (bump version tag to `pyana-turn-v3:`); update the cipherclerk's `compute_turn_bytes` (AUDIT-cclerk P2-10) to match.

**P1-2 — `convert_turn_effects_to_vm` truncates every 32-byte hash to its first 4 bytes via `% BABYBEAR_P`.** (`turn/src/executor.rs:1266-1273`). Both `hash_to_bb` and `field_element_to_bb` read `u32::from_le_bytes(h[0..4])` and reduce mod `BABYBEAR_P` (≈31 bits). All `Effect::NoteSpend.nullifier`, `NoteCreate.commitment`, `QueueEnqueue.message_hash`, `SetField.value`, `pipeline_id`, etc. collapse to 31-bit identifiers in the circuit PIs. The cipherclerk's `convert_effects_to_vm` is identical (AUDIT-cclerk P2-5), so executor and cclerk *agree* — but the proof is bound to a small equivalence class rather than the turn. An attacker can construct two distinct turns whose circuit views are identical (collisions are trivially findable). Net effect: the proof verifies multiple turns simultaneously, so the cclerk/executor must still rely on the *un-shrunk* effects (via `compute_effects_hash`) for binding. Since `compute_effects_hash` is also a BLAKE3 of the original effects, the binding survives — but the proof PIs become decorative for any cross-checking that uses *only* the PI values. **Fix**: use `bytes32_to_babybear` (the 8-element encoding) for all `hash_to_bb` callers, and widen the circuit PI layout accordingly.

**P1-3 — `execute_atomic_sovereign` extracts `proven_delta` from a proof PI that is itself only 32 bits, then sums i64.** (`turn/src/executor.rs:7979-7984` + `8082`). `delta_magnitude` and `delta_sign` are single BabyBears (≈31-bit each). `extract_net_delta` collapses them to an `i64`. For a turn with a 2^31-1 inflow and a 2^31-1 outflow on the same cell, `net_delta` is computable correctly inside this range — but a turn whose true balance change is > 2^31 cannot be expressed in the proof PI. The conservation check `net_excess: i64 = proven_deltas.iter().sum() == 0` then holds vacuously for turns that exceed the field bound: the prover can prove `delta_mag = (real_value mod p)` while the true amount is `real_value`. This means a sovereign cell with balance > 2^31 cannot have its conservation proven correctly. **Fix**: encode magnitude as 2 BabyBears (lo/hi) and reconstruct as `u64`; check that hi*p + lo equals the true magnitude in-circuit.

**P1-4 — `verify_authorization` for `Authorization::Unchecked` paired with `AuthRequired::None` is silently OK.** (`turn/src/executor.rs:2710`). A target cell with `permissions.Access = AuthRequired::None` requires *no* signature; combined with `Authorization::Unchecked`, any turn against that cell with a valid agent+nonce+fee succeeds. The `for_action(Access)` path is the fallback when no effects produce a specific permission requirement (`required_actions.is_empty()`), and an empty effect list trivially meets this. Combined with the fact that `Turn::call_forest` can carry effects targeting other cells via `apply_effect`'s cross-cell permission checks, this is *probably* safe — but it means a cell created with default-permissive permissions accepts any anonymous Action::method invocation. **Fix**: require all cells to have at least one non-None permission, OR document this as a `Permissions::open()` configuration deliberately.

**P1-5 — Mutex `.unwrap()` on every shared map (poison panic = federation halt).** (`turn/src/executor.rs` has ~70 calls to `.lock().unwrap()` on `obligations`, `escrows`, `committed_escrows`, `committed_escrow_amounts`, `bridged_nullifiers`, `pending_bridges`, `cell_migrations`, `budget_gate`). Any panic that occurs inside *one* turn execution while holding any of these mutexes will poison the mutex and cause every subsequent turn to panic on `.lock().unwrap()`. The executor's panics are not localized — they bring down the whole node. **Fix**: use `.lock().unwrap_or_else(|e| e.into_inner())` consistently, or switch to `parking_lot::Mutex`.

**P1-6 — `process_fast_path_lock` says "signature validity assumed already verified upstream" (line 304) but no upstream check exists in this crate.** A caller that forgets the upstream verify gets validators locking cells for arbitrary unsigned turns. **Fix**: take a verified signature as input, not an `&Turn`; or perform the Ed25519 check at lock time.

**P1-7 — `execute_mixed_atomic` skips note-conservation, excess accounting, journal/rollback, and obligation/escrow registry interaction.** Even ignoring C1, `execute_mixed_atomic` writes to `cell.state.balance` directly without a journal, so if a later mutation in the same call panics, the partial state is permanent. There's also no `excess != 0` check on the hosted side beyond the Transfer-delta sum. **Fix**: same as C1 — route through the standard `execute`-shaped pipeline.

### P2

**P2-1 — `Turn::hash()` excludes `sovereign_witnesses`, `conservation_proof`, `custom_program_proofs`, `execution_proof*` fields.** (`turn.rs:132-164`). Same shape as AUDIT-cclerk P2-10. An attacker with write-access to the in-flight SignedTurn can swap any of these without invalidating the signature. The agent's signed claim is only over agent/nonce/forest/fee/memo/valid_until/depends_on/previous_receipt_hash. **Fix**: extend `Turn::hash()` to cover all semantically-load-bearing fields; bump version tag.

**P2-2 — `validate_without_apply` doesn't enforce `valid_until` is in the future *relative to a clock the executor controls*.** Already uses `self.current_timestamp`; OK. But `set_timestamp` is `pub fn` with no monotonicity check (executor.rs:690). A caller can set the clock backwards. **Fix**: require monotonic timestamps in `set_timestamp`.

**P2-3 — `TurnExecutor` fields are all `pub`** (`turn/src/executor.rs:492-585`). Any caller with `&mut TurnExecutor` can swap `proof_verifier`, `trusted_federation_roots`, `local_federation_id`, `proposer_cell`, `treasury_cell`, etc., or directly mutate the obligation/escrow maps. This is a same-process trust boundary issue; if any RPC surface ever ends up with a long-lived `&mut TurnExecutor` it becomes a full-takeover vector. **Fix**: make fields private with read-only accessors and explicit setters.

**P2-4 — `set_proof_verifier` accepts any `Box<dyn ProofVerifier>` including `AlwaysAcceptVerifier`.** The `turn::tests::AlwaysAcceptVerifier` is `struct AlwaysAcceptVerifier;` declared in `turn/src/tests.rs:125` — it is `#[cfg(test)]`-local, so production callers can't reach it. But the trait method has trivial implementations (e.g. `wire/src/server.rs::NoopVerifier`). The executor cannot tell a no-op verifier from a real one. **Fix**: document the trust assumption explicitly on `set_proof_verifier` and consider a `Verifier::is_production()` discriminator.

**P2-5 — Rollback semantics for partial sovereign-cell injection on classical path.** (`turn/src/executor.rs:1804-1822` + 1864-1867). If a sovereign witness is injected and the turn fails, the cells are `ledger.remove(cell_id)`'d on rollback — but the journal-replayed mutations during execution may have applied to the injected cell. The journal records old values that were set *after* injection; rollback applies them in reverse, then `ledger.remove` strips the cell entirely. The two-step rollback is correct but fragile: any future change that captures pre-injection state (e.g. for read-during-execution invariants) breaks the ordering. **Fix**: factor injection into the journal as a `CreateCell`-shaped entry so rollback is symmetric.

**P2-6 — `execute_certified_turn` releases locks after `executor.execute()` returns, regardless of result.** (`fast_path.rs:457-472`). If execution panics (mutex poison, OOM), the lock is leaked. **Fix**: wrap execution in `std::panic::catch_unwind` or use a guard pattern.

**P2-7 — `Turn::depends_on` is honored by `execute_pipeline` (line 7417-7436) but not by `execute()`.** A single-turn `execute()` ignores `depends_on` entirely — the agent can submit a turn claiming to depend on something that hasn't happened. Not a soundness issue at the executor (the dependency turns will produce no observable effect), but contracts assuming `depends_on` is enforced get less than they think. **Fix**: document, or enforce by lookup against committed turn hashes.

### P3

**P3-1 — `compute_signing_message` and `compute_partial_signing_message` use `self.local_federation_id` at verification time.** If `set_local_federation_id` is called between when the cclerk signs and when the executor verifies (e.g. due to operator config change), all in-flight turns become invalid. Not a security issue but a liveness footgun.

**P3-2 — `apply_effect`'s `Effect::PipelinedSend` is not handled.** Searching apply_effect's match for `PipelinedSend` returns nothing — it falls through to whatever the executor's last match arm is. Verify it doesn't silently no-op.

**P3-3 — `validate_without_apply` re-implements roughly the same checks as `execute` but without `verify_authorization`.** Callers relying on this for pre-flight will accept turns that `execute` rejects on auth.

**P3-4 — `TurnReceipt.executor_signature` is `Option<Vec<u8>>` and is `None` on every path I traced.** Receipts are never signed by the executor in this crate; the federation-exit verifiability claim in `verify_receipt_chain_with_keys` rests on a signature that nothing produces.

## Executor API trust table (selected)

| Function | line | Trust class |
|---|---|---|
| `TurnExecutor::new`, `with_budget_gate`, `with_proof_verifier` | 589/622/651 | Owner-only; sets verifier. |
| `set_*` (verifier, gate, timestamp, height, proposer, treasury, trusted_*) | 680-863 | Owner-only; `pub` + `&mut self`. |
| `execute(&self, turn, ledger)` | 1532 | **Trust-critical** — sole classical entry. |
| `execute_conditional` | 756 | Wraps `execute`; OK. |
| `validate_without_apply` | 2075 | Pre-flight; does NOT call `verify_authorization`. |
| `verify_and_commit_proof` | 928 | **Trust-critical** — sovereign commit. |
| `execute_atomic_sovereign` | 7894 | Multi-cell sovereign; per-cell proof check. |
| `execute_mixed_atomic` | 8123 | **CRITICAL** — hosted effects unauthorized. |
| `apply_effect` | 3454 | Internal; auth checked upstream. |
| `verify_authorization`, `verify_bearer_cap`, `verify_zk_proof`, `check_breadstuff` | 2564/3052/2887/2955 | Gatekeepers; fail-closed. |
| `compute_signing_message`, `compute_partial_signing_message` | 3292/3343 | Sig binding; nonce+federation included. |
| `apply_epoch_minting` | 739 | Owner-only; mints to treasury. |
| `execute_pipeline`, `execute_pipeline_result` | 7367/7574 | Composes `execute` over a DAG. |
| `resolve_eventual_ref`, `resolve_output_ref` | 7553/7566 | Read-only. |

## Effect-by-effect interpretation table

| Effect variant | Executor handler line | Circuit semantic match? |
|---|---|---|
| `SetField` | 3464 | yes (`VmEffect::SetField`, value truncated to 4B — see P1-2) |
| `Transfer` | 3496 | partial (Vm has `Transfer` only when from/to == proven cell) |
| `GrantCapability` | 3537 | partial (Vm only records hash, executor enforces attenuation) |
| `RevokeCapability` | 3592 | unverifiable (no Vm variant) |
| `EmitEvent` | 3613 | n/a (Vm has no event row) |
| `IncrementNonce` | 3622 | implicit row-to-row in Vm |
| `CreateCell` | 3641 | unverifiable (no Vm variant; classical only) |
| `SetPermissions` | 3664 | unverifiable |
| `SetVerificationKey` | 3686 | unverifiable |
| `NoteSpend` | 3707 | yes (Vm `NoteSpend`, nullifier truncated — P1-2) |
| `NoteCreate` | 3779 | yes (Vm `NoteCreate`, commitment truncated — P1-2) |
| `CreateSealPair`, `Seal`, `Unseal` | (search returned no apply arms) | unverifiable |
| `SpawnWithDelegation`, `RefreshDelegation`, `RevokeDelegation` | not in apply_effect search | unverifiable |
| `BridgeMint`, `BridgeLock`, `BridgeFinalize`, `BridgeCancel` | 3800/3878/3908/3930 | partial (nullifier set in Vm via NoteSpend, but bridge metadata only enforced in executor) |
| `Introduce` | apply_effect handles via `Effect::Introduce` (line 2175 comment) | unverifiable |
| `PipelinedSend` | not handled in apply_effect | **P3-2** |
| `CreateObligation`, `FulfillObligation`, `SlashObligation` | 3946/4051/4149 | unverifiable (Vm has no obligation rows) |
| `CreateEscrow`, `ReleaseEscrow`, `RefundEscrow` | 4213/4320/4508 | unverifiable |
| `CreateCommittedEscrow`, `ReleaseCommittedEscrow`, `RefundCommittedEscrow` | 4570/4743/4836 | unverifiable |
| `ExerciseViaCapability` | 4939 | unverifiable (recursive into apply_effect) |
| `MakeSovereign` | (search not shown but exists) | unverifiable |
| `CreateCellFromFactory` | (factory_registry) | unverifiable |
| `QueueAllocate`/`QueueEnqueue`/`QueueDequeue`/`QueueResize`/`QueueAtomicTx`/`QueuePipelineStep` | 5276+ | yes (Vm has matching variants, but executor encodes `queue_len: 0`, `old_capacity: 0`, deposit_refund: 0 as placeholders — see executor.rs:1342, 1352, 1363; the proof's circuit can't actually verify these against state) |

(24 rows including queue operations.)

## Cross-layer binding analysis

**Executor → Effect VM (sovereign proof-carrying path):**
- PIs reconstructed at `executor.rs:978-988`:
  1. `OLD_COMMIT` (1 BabyBear) — from stored commitment, **only 31 bits used** (P0-2).
  2. `NEW_COMMIT` (1 BabyBear) — same encoding.
  3. `NET_DELTA_MAG` (1 BabyBear) — magnitude only, **31 bits** (P1-3).
  4. `NET_DELTA_SIGN` (1 BabyBear) — sign flag.
  5. `EFFECTS_HASH_LO` / `EFFECTS_HASH_HI` (2 BabyBears) — Poseidon2 over `vm_effects`, but each `vm_effect` was already truncated (P1-2). So the effects hash is "Poseidon2 of the truncated effect list," not "Poseidon2 of the real effect list."
  6. `CUSTOM_EFFECT_COUNT` (1 BabyBear).
  7. Per custom effect, 4+4 BabyBears for `program_vk_hash` and `proof_commitment`.

The executor expects the proof's PI to match its reconstruction at lines 1018-1054. The circuit (verified separately in AUDIT-circuit.md) must enforce the same PI layout — the auditor cannot verify this without that report.

**Receipt-chain binding:** `TurnReceipt::receipt_hash()` (turn.rs:303-368) does include all the relevant fields, with version tag `pyana-receipt-v2`. But the receipt is never bound to the prior receipt at executor write time (P0-3); chain integrity is a verifier-side property only.

**Turn signature binding:** `compute_signing_message` (executor.rs:3292) and `compute_partial_signing_message` (3343) include `federation_id` and `turn_nonce`. The cipherclerk's signing message is computed via `compute_turn_bytes` (AUDIT-cclerk P2-10) which excludes `execution_proof*` fields — see P1-1 and P2-1.

## Open questions for the user

1. **`execute_mixed_atomic` (C1) — keep or kill?** The current implementation is dangerously incomplete. Is this intended to be the "cross-sovereign-hosted swap" primitive? If so, it needs full authorization for the hosted side. If not, gate it behind `#[cfg(test)]`.

2. **Fast path (P0-1) — is `compute_turn_sign_signature` known to be a stub?** The function comment says "in production, this would be Ed25519." If so, please mark the whole module `#[cfg(test)]` or `#[doc(hidden)]` until it's wired up.

3. **Commitment encoding (P0-2)** — switching from 4-byte to 32-byte encoding is a circuit-side change. Want me to draft the executor side to use `bytes32_to_babybear` (which already exists at line 1175) and flag the circuit-side change for the circuit auditor?

4. **`previous_receipt_hash` enforcement (P0-3)** — do you want me to add a `last_receipt_hash: Option<[u8; 32]>` to `CellState` and check it in `execute()`? The cclerk would also need to plumb this through `build_authorized_turn` and queue ops (currently hardcoded to `None`, see cclerk P3-6).

5. **CellMigrationManager (P0-4)** — should a frozen cell reject *all* turns, or only writes? Reads/balance-of-frozen-cell-as-Transfer-source are particularly concerning.

6. **Should `TurnExecutor` fields be private (P2-3)?** Currently `pub` everywhere; constructors/setters exist. Want me to lock them down?

7. **Mutex poisoning (P1-5)** — switch to `parking_lot::Mutex` (no poisoning), or keep `std::sync::Mutex` and use `.unwrap_or_else(|e| e.into_inner())` everywhere?

8. The audit found one CRITICAL (mixed-atomic hosted effects) and four P0s (fast-path forgery, 31-bit commitments, missing receipt-chain enforcement, ignored migration freeze). Are there adversarial scenarios you specifically had in mind that I should construct as failing tests?
