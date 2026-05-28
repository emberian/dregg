# Executor honesty audit — framework

**Date:** 2026-05-24. **Status:** framework + first pass of AIR-layer
answers from Stage 7 cont (commits `e80c4195` §A, `c4bd297c` §B,
`8b9a9093` §C). Several threats moved to **closed at AIR (single-cell)**.
Multi-cell binding remains a γ.2 concern.

## The question this audit answers

> If the executor is malicious (or buggy, or compromised, or coerced),
> what attacks does our system prevent, and *where* in the stack is
> each prevention enforced?

The executor sits between a signed turn and a receipt. It applies
effects, updates ledger state, produces a receipt, signs it. A
receiver of the receipt (or a verifier replaying the chain) must
detect any deviation from the protocol-specified semantics. This
document enumerates the deviations the executor could attempt and
points at the code that catches each one — or flags the gap.

## Defense surface (where soundness lives)

Three layers, in order of strength:

1. **AIR (Effect VM)** — the prover-side STARK constrains the
   *transition* itself. If the AIR enforces a property, no honest
   verifier will accept a proof that violates it. This is the
   strongest layer because it does not depend on the executor's
   honesty: a dishonest executor cannot produce a passing proof.
2. **Canonical-message signing** — the actor signs over a domain-
   separated hash of the turn (`dregg-turn-v3:` ‖ canonical body).
   The executor signs over a domain-separated receipt message
   (`executor-receipt-sig-v1:` ‖ turn_hash ‖ pre_state ‖ post_state ‖
   timestamp_le). Both signatures are checked by any verifier that
   holds the public keys.
3. **Verifier-side replay (witnessed-receipt chain)** — a verifier
   replays the chain, checking each STARK proof against its public
   inputs and (scope-2) re-deriving the post-state from witness data
   bound to the proof. This is the layer that turns "I have a
   proof" into "I have re-verified the entire history."

> **Soundness rule of thumb:** if a property is enforced at AIR
> level, it is impossible to violate. If it is enforced only at
> signature level, it is impossible to violate *without forging a
> key*. If it is enforced only at verifier level, it is impossible
> to violate *if every verifier on the path actually runs the
> check*. Each step down is a soundness reduction; we want as much
> at AIR level as we can afford.

## Threats and current status

For each threat: **(T)** description, **(D)** where defended,
**(C)** code pointer, **(G)** gap / open question. AIR-layer
answers marked `[stage7-cont]` are pending the in-flight agent.

### T1: Reorder effects within a turn
- (T) Executor applies a turn's effects in a different order than
  signed (e.g., apply Withdraw before Authorize).
- (D) `effects_hash` is computed over the *ordered* effect list and
  bound into the turn hash. AIR enforces sequential application via
  the EFFECT_INDEX column (effects are processed in trace order;
  `EFFECTS_HASH_GLOBAL` accumulates per-row).
- (C) `turn/src/action.rs::Turn::hash` (effects_hash via ordered
  list); `circuit/src/effect_vm.rs::EFFECTS_HASH_GLOBAL` (column
  layout); `circuit/src/effect_vm.rs` constraint enforcing
  hash-chain continuity across rows.
- (V) **Closed at AIR (single-cell)** via Stage 7 cont §B
  (`c4bd297c`): per-cell `EFFECTS_HASH_BASE` is row-0 aux-bound to
  in-trace effect bytes. Executor's PI-matching loop then enforces
  equality between AIR's `EFFECTS_HASH_BASE` and signed-turn
  effects_hash.
- (G) **Multi-cell γ.2**: `EFFECTS_HASH_GLOBAL_BASE` is *not*
  boundary-bound across cells. When N cells contribute to one
  aggregated proof, cross-cell agreement is a γ.2 (#60) concern.

### T2: Invent effects the actor did not sign
- (T) Executor adds an effect (e.g., extra Transfer to executor's
  own cell) not in the signed turn.
- (D) Same as T1: the actor's signature covers `turn.hash()` which
  covers `effects_hash`. An extra effect changes the hash → signature
  check fails.
- (C) `turn/src/verify.rs` signature verification; `turn/src/action.
  rs::Turn::hash`.
- (G) Verify the verify path is *the only* path into TurnExecutor.
  Search for any code path that constructs a Turn without
  signature check (the `Authorization::Unchecked` regressions —
  Stage 8 P2.F's CI guard prevents new ones; audit confirms
  none remain in production code).

### T3: Skip / omit effects from a signed turn
- (T) Executor applies fewer effects than signed (e.g., skip the
  fee deduction).
- (D) AIR: every signed effect must appear in the trace, in order.
  EFFECTS_HASH_GLOBAL chain anchors final hash to PI; if any effect
  is missing the chain doesn't terminate at the right value.
- (C) `circuit/src/effect_vm.rs` EFFECTS_HASH_GLOBAL termination
  constraint.
- (V) **Closed at AIR (single-cell)** by T1's resolution.
- (G) **Multi-cell γ.2**: same as T1.

### T4: Lie about pre/post state hash
- (T) Executor produces a receipt claiming `post_state =
  H(some-favorable-state)` when the actual post-state differs.
- (D) AIR: the Effect VM trace computes post-state from
  effects applied to pre-state; PI binds claimed pre/post to
  trace-computed pre/post.
- (C) `circuit/src/effect_vm.rs` state hash columns + PI binding.
- (G) **OPEN.** Stage 7 cont §B added a row-0 boundary for the
  NONCE column of `STATE_BEFORE_BASE` (closes T5) but did *not*
  explicitly bind the full pre/post state hash to trace. The rest
  of `STATE_BEFORE_BASE` / `STATE_AFTER_BASE` may already be
  row-0 / row-last aux-bound by the existing AIR — verify in
  `circuit/src/effect_vm.rs` and document. **High priority.**

### T5: Reuse a nonce
- (T) Executor accepts two different turns with the same
  `actor_nonce`, allowing replay attacks.
- (D) AIR: PI includes `ACTOR_NONCE`; the AIR enforces
  monotonicity at the boundary (current_nonce = previous + 1) by
  comparing the in-trace witness against the PI value.
- (C) `circuit/src/effect_vm.rs::ACTOR_NONCE` (PI position);
  `turn/src/executor.rs` nonce check.
- (V) **Closed at AIR (single-cell)** via Stage 7 cont §B
  (`c4bd297c`): BoundaryConstraint `(row=0, col=STATE_BEFORE_BASE +
  state::NONCE) == PI[ACTOR_NONCE]`. 3 unit tests cover positive,
  PI-mismatch reject, trace-mismatch reject.
- (G) **Multi-cell γ.2**: §B note documents that an `IS_AGENT_CELL`
  PI gate is needed for the multi-cell case. Tracked as #60.

### T6: Replay a turn from another federation / ledger
- (T) Executor takes Alice's grant turn signed for federation F1
  and applies it on federation F2's ledger.
- (D) Signature: the actor's signing message must include
  `federation_id` so the same turn is not valid in two federations.
- (C) `turn/src/verify.rs::canonical_signing_message` (verify
  federation_id is included).
- (G) **Open.** Confirm the canonical signing message includes
  federation_id. If not, this is a real vulnerability and not a
  Stage 7 question — it's a turn-canonical-message question.

### T7: Forge a receipt signature
- (T) Executor publishes a receipt with a signature from a key it
  does not control.
- (D) Signature: receipt signature is verified against the
  executor's published pubkey. Standard ed25519.
- (C) `turn/src/verify.rs::sign_receipt` / verify path; uses
  canonical message `executor-receipt-sig-v1:`.
- (G) Confirm: does the receipt explicitly name the executor
  whose key is checked, or is it inferred from federation
  membership? The latter is OK only if federation membership is
  on-chain / publicly verifiable.

### T8: Insert a fake `previous_receipt_hash` link
- (T) Executor claims the new receipt chains from a previous
  receipt that was never actually issued.
- (D) AIR: `PREVIOUS_RECEIPT_HASH_BASE[4]` is in PI (γ.0
  landed). Verifier checks that the new turn's claimed
  previous_receipt_hash matches the actual hash of the prior
  receipt in the chain.
- (C) `verifier/src/` replay-chain subcommand; chain-walk loop.
- (G) `[stage7-cont]` Trace-side binding of PREVIOUS_RECEIPT_HASH.
  And: confirm the verifier rejects on mismatch (not just logs).

### T9: Skip sovereign-witness verification
- (T) For a sovereign cell, executor skips the witness check and
  applies the effect anyway.
- (D) AIR: sovereign witness columns exist; the AIR enforces the
  witness verifies before the effect transition takes hold.
- (C) `turn/src/action.rs::sovereign_witnesses` (Turn::hash v3
  covers them); `circuit/src/effect_vm.rs` sovereign-witness
  constraints.
- (G) **Open.** Verify sovereign witnesses *algebraically constrain*
  the transition (not just decorate the receipt). This was queued
  as a Stage 9 polish item.

### T10: Skip a permission / capability check
- (T) Executor applies Transfer without the actor holding the
  required cap.
- (D) AIR: per-effect AIR enforces the cap-presence check. For
  Transfer, this is a Merkle-membership proof in the actor's
  capability list.
- (C) `circuit/src/effect_vm.rs` per-variant constraints.
- (G) `[stage7-cont]` P1.C is verifying that 4 CapTP variants
  (ExportSturdyRef, EnlivenRef, DropRef, ValidateHandoff) are
  *real* Merkle membership and not tautological. Stage 7 cont
  agent's first piece.

### T11: Submit a stale / cached proof for a new turn
- (T) Executor reuses an old valid proof, attaching it to a new
  receipt.
- (D) AIR: PI binds `TURN_HASH` (γ.0). Old proof's TURN_HASH
  doesn't match new receipt's claimed turn → verifier rejects.
- (C) `verifier/src/` PI-matching at verification time.
- (G) Confirm verifier *requires* TURN_HASH PI matches the
  receipt's claimed turn_hash. This is a single line of check;
  confirm it's there.

### T12: Lie about balance deltas
- (T) Executor reports a receipt with `balance_delta = +500` when
  the actual transfer was -500.
- (D) AIR: `compute_balance_delta_from_effects` derives the
  delta from the effect list and binds it into the trace.
- (C) `turn/src/executor.rs::compute_balance_delta_from_effects`;
  binding in AIR.
- (G) **Open.** Earlier session noted D-5: "gallery
  `balance_change` declarations don't match `Transfer` amounts."
  Stage 8 P2.D landed conservation derivation in the builder;
  verify the gallery file is now consistent.

### T13: Cross-cell aliasing (same cell ID in two federations)
- (T) Executor uses the same `cell_id` in two federations to apply
  conflicting state updates.
- (D) Cell ID derivation includes federation context; canonical
  signing message includes federation_id (see T6).
- (C) `cell/src/cell.rs::derive_raw`; verify federation_id is in
  the derivation.
- (G) **Open.** Cell::remote_stub_with_id was added as a deliberate
  escape hatch *breaking* the id == derive_raw invariant. Audit
  whether this escape hatch can be abused: a malicious node that
  controls `remote_stub_with_id` could mint cells with arbitrary
  IDs. What constrains this? (Should be: federation membership +
  CapTP origin attestation.)

### T14: Skip the AIR proof entirely
- (T) Executor publishes a receipt with no proof, or a
  syntactically-invalid proof.
- (D) Verifier: rejects receipts without valid proofs. Standalone
  `dregg-verifier` binary in `verifier/` enforces this.
- (C) `verifier/src/main.rs`.
- (G) Confirm the *protocol* requires proof attachment — i.e., a
  receipt without a proof is invalid at the wire level, not
  merely unverifiable.

### T15: Forge the effects_hash → make AIR pass over a different effect list
- (T) Executor constructs a trace with effects E' while the
  signed turn lists effects E, computing effects_hash(E') and
  publishing a proof over E'.
- (D) AIR: effects_hash is computed *in-trace* from the in-trace
  effects, so the proof attests to its own effects_hash. Then PI
  exposes effects_hash. Verifier checks PI effects_hash matches
  the signed turn's effects_hash.
- (C) `effect_vm.rs` EFFECTS_HASH_GLOBAL termination → PI;
  `turn/src/executor.rs::verify_proof_carrying_turn_bundle`.
- (G) `[stage7-cont]` Trace-side binding (the recurring Stage 7
  cont question).

## Cross-cutting open questions (highest priority)

1. **Trace-side binding completeness.** Five of the above threats
   collapse to: "is the trace-side binding for {ACTOR_NONCE,
   EFFECTS_HASH_GLOBAL, TURN_HASH, PRE/POST_STATE,
   PREVIOUS_RECEIPT_HASH} complete?" Stage 7 cont is doing the
   first two. The other three should be verified during this
   audit's followup pass.
2. **Canonical signing message audit.** T6 (federation replay) and
   T13 (cross-cell alias) both hinge on what is *actually*
   included in `canonical_signing_message`. Read the function;
   confirm domain separator + federation_id + actor_id +
   nonce + effects_hash + previous_receipt_hash are all in.
3. **Verifier completeness.** Several threats end with "verifier
   rejects on mismatch." Walk `verifier/src/main.rs` and confirm
   every PI is checked, not just deserialized.
4. **`Cell::remote_stub_with_id` escape hatch.** T13's tail. What
   prevents a malicious node from minting an arbitrary-id cell?
5. **Sovereign-witness algebraic teeth.** T9 — confirm the witness
   actually constrains the AIR transition, not just decorates.

## How to use this document

1. **Now:** This is the framework. Open questions are real; do not
   treat them as rhetorical.
2. **After Stage 7 cont lands:** Fill in the `[stage7-cont]`
   answers. Most should become "closed at AIR level."
3. **After verifier completeness pass:** Fill in the "verifier
   rejects on mismatch" gaps.
4. **Standing:** Whenever a new Effect variant is added, an
   Authorization mode is added, or the receipt format changes,
   re-walk this document and update.

## Cross-references

- `THOUGHTS-AND-DREAMS.md` — session-state snapshot
- `EFFECT-VM-SHAPE-A.md` — Effect VM plan
- `STAGE-7-PLUS-DESIGN.md` — proof-system trajectory
- `WITNESSED-RECEIPT-CHAIN-DESIGN.md` — replay semantics
- `SDK-REVIEW.md` — SDK gaps (relevant: queue methods still ship
  `Authorization::Unchecked`, exact regression this audit guards
  against)
