# zkpromise / zkawait / zk-continuation — Design (W3-I)

**Status:** design for review (do NOT implement until reviewed). Author: autonomous design pass, 2026-05-29.
**Grounding:** every "today" claim below is from a read of the actual tree at HEAD `16c4c62e`, file:line cited. This is the design for task #82 / lane W3-I, which was scoped but never dispatched.

## The problem, precisely (not extrapolated)

dregg has **three disjoint deferred-resolution mechanisms** and a **partial bridge**:

1. **CapTP E-promises** — `captp/src/pipeline.rs:137` `PipelineRegistry { queued, promises, next_id }`. A promise is a bare `u64` (`create_promise`, pipeline.rs:160). Resolved by the *remote federation* sending a `PipelineWireMessage::PromiseResolved { promise_id, resolved_cell }` (pipeline.rs:369) → `resolve_promise` (pipeline.rs:204). **No cryptographic binding, no proof; cross-federation wire only.**
2. **ConditionalTurn** — `turn/src/conditional.rs:88`. A `Turn` gated by a `ProofCondition` (conditional.rs:54) with `timeout_height`/`deposit_amount`. Four condition kinds: `HashPreimage`, `RemoteProof{federation_root,expected_air,expected_conclusion}`, `LocalProof{expected_air,expected_public_inputs}`, `TurnExecuted{turn_hash}`. `resolve_condition` (conditional.rs:191) verifies the matching `ConditionProof` and **nullifies the proof hash** in `used_proof_hashes` (conditional.rs:198,221) to stop reuse. **This is the only proof-gated await today.**
3. **EventualRef** — `turn/src/eventual.rs:24` `{ source_turn:[u8;32], output_slot:u32, federation_id:Option<..> }`. A forward reference to a *future turn's output slot*; `Target::Eventual` (eventual.rs:68). Resolved **inline** during topological pipeline execution by reading the source turn's receipt `TurnOutput` (eventual.rs:117). **No proof; receipt-availability only.**

**The bridge that already exists:** `turn/src/pending.rs:164` `PendingTurnRegistry { pending: HashMap<[u8;32], PendingEntry> }` with `ResolutionCondition` (pending.rs:58) = `AwaitReceipt{turn_hash,federation_id} | AwaitCondition(ProofCondition) | AwaitHeight(u64)`, `resolve(turn_hash, ResolutionOutcome)` cascading to `dependents` (pending.rs:241,274). **It already subsumes #2 and #3** (AwaitCondition = ConditionalTurn, AwaitReceipt = distributed EventualRef). It does **not** subsume #1 (CapTP promises).

**Two confirmed gaps (these are the actual new work):**
- **G-A. No ZK-resolution.** No `ResolutionCondition`/`ProofCondition` is satisfied by a *succinct proof of a computation's result* — `RemoteProof`/`LocalProof` verify a STARK against a *named AIR + public-input equality*, but there is no path where the resolution value itself is produced by per-action / IVC / recursive proofs (`circuit/src/effect_vm/per_action.rs`, `circuit/src/ivc.rs`, `circuit/src/stark_zk.rs`) and bound into the awaiting turn. These primitives exist and are unused by the await layer.
- **G-B. No capability-resolved continuation.** Nothing resolves by *exercising a local capability* (confirmed: all three resolve by cross-fed wire / preimage / STARK-vs-AIR / receipt / timeout). There is no "this promise resolves when capability X is exercised on cell C," which is the E-language `when`/`whenResolved` shape and the natural object-capability await.

## What "zkpromise / zkawait" should mean here

- **zkpromise** = a promise (deferred result) whose **resolution is witnessed by a zero-knowledge proof**: the resolver proves "I produced the awaited value / exercised the awaited authority" without revealing more than the bound public result. It is a `PendingTurnRegistry` entry whose `ResolutionCondition` is a new ZK variant.
- **zkawait** = an action/turn that **consumes** a zkpromise: its `Target` or an input slot is an `EventualRef`-like handle to the promise, and its execution is gated until the promise resolves — with the resolved value bound into the awaiting turn's PI so the dependency is itself provable.
- **zk-continuation** = a *chain* of zkawaits folded into **one recursively-verified proof** via the existing IVC accumulator (`circuit/src/ivc.rs` `IvcBuilder`/`prove_ivc`) — the continuation's whole resolution history is a single constant-size proof, not N independent ones.

(Note: "zkresidual"/"zkcontinuation" were the user's framing; the in-tree vocabulary is promise/await/conditional. "zk-continuation" above = the folded-chain case.)

## Core design — unify on `PendingTurnRegistry`, add two resolution variants

**Decision: do NOT invent a 4th registry.** Extend the existing bridge (`PendingTurnRegistry`) to be *the one* continuation primitive, and bring CapTP promises in as a *resolution source*, not a parallel store.

### 1. Extend `ResolutionCondition` (pending.rs:58) and `ProofCondition` (conditional.rs:54)

```rust
// turn/src/conditional.rs — new ProofCondition variants (additive)
pub enum ProofCondition {
    HashPreimage { hash: [u8; 32] },
    RemoteProof { .. },                      // existing
    LocalProof { .. },                       // existing
    TurnExecuted { turn_hash: [u8; 32] },    // existing
    // NEW — G-A: resolution witnessed by a result-bearing ZK proof
    ZkResult {
        /// Which prover produced the value.
        kind: ZkResultKind,                  // PerAction | Ivc | Recursive
        /// The committed result the awaiting turn binds to (e.g. a
        /// PerActionSummary.new_commit / IvcProof.final_root). Equality
        /// against the verified proof's extracted output is the gate.
        expected_output: [BabyBear; 4],
    },
    // NEW — G-B: resolution by exercising a local capability
    CapabilityExercised {
        /// The cell whose capability must be exercised.
        target: CellId,
        /// The capability/method that must be exercised against it
        /// (matches the c-list / Authorization machinery, not a new ACL).
        method: Symbol,
        /// Optional ZK-blinded exerciser: when set, the resolver proves
        /// "a holder of this capability exercised it" WITHOUT revealing
        /// who, reusing the W3-D BlindedSet / W3-F StarkDelegation path.
        anonymous: bool,
    },
}
```

`ResolutionCondition::AwaitCondition(ProofCondition)` (pending.rs:60) already carries these — **no change to `ResolutionCondition` needed**; the new power rides the existing `AwaitCondition` arm. CapTP promises fold in as a *third* `ResolutionCondition::AwaitCapTpPromise { promise_id, peer }` (the one genuinely new arm), so a single `PendingTurnRegistry::resolve` cascade covers all sources.

### 2. ZK-result resolution (G-A) — reuse, don't rebuild

In `resolve_condition` (conditional.rs:191) add the `(ProofCondition::ZkResult, ConditionProof::ZkResult{..})` arm. It dispatches by `ZkResultKind`:
- `PerAction` → `dregg_circuit::effect_vm::per_action::verify_action_proof(...)` → compare `PerActionSummary.new_commit` to `expected_output` (per_action.rs:187,79).
- `Ivc` → `dregg_circuit::ivc::verify_ivc(proof, None)` → compare `IvcProof.final_root` to `expected_output[0]` (ivc.rs:1105,90).
- `Recursive` → `dregg_circuit::stark_zk::verify_recursive_fri(...)` (stark_zk.rs) for an inner-proof-verifying outer proof.

Keep the existing **proof-hash nullifier** (`used_proof_hashes`, conditional.rs:198) so a zkpromise can't be resolved twice. The `expected_output` is what binds the resolved value to the awaiting turn — the same discipline `RemoteProof.expected_conclusion` uses (conditional.rs:348), but a full commitment rather than a scalar threshold.

### 3. Capability-resolved continuation (G-B) — the genuinely new semantics

This is the one part with no existing analogue. The promise resolves when a *later turn in the ledger* exercises `(target, method)`:
- The executor, on successfully applying an action whose `(target, method)` matches a registered `CapabilityExercised` condition, calls `PendingTurnRegistry::resolve(promise_hash, Resolved(receipt))` (pending.rs:241) as a post-effect hook in `turn/src/executor/execute_tree.rs` (where effects are applied and receipts formed).
- **Soundness:** resolution is driven by a *real, authorized* capability exercise (the action already passed `authorize.rs`), so "who may resolve" = "who holds the capability" — exactly the object-capability semantics, and the answer to G-B.
- **`anonymous: true`** routes the exerciser through the W3-F `StarkDelegation` / W3-D `BlindedSet` path so the resolver isn't deanonymized by resolving — i.e. an *anonymous* zkpromise resolution.

### 4. zk-continuation folding (the chain case)

When a turn awaits a promise that itself awaited a promise (a dependent chain in `PendingTurnRegistry.dependents`, pending.rs:50), fold the per-resolution proofs into one `IvcProof`:
- Each resolution emits a `FoldDelta` (ivc.rs:53); the chain is accumulated via `IvcBuilder::add_fold` → `finalize` (ivc.rs:1312) so the entire continuation is **one constant-size, recursively-checkable proof** instead of N. This reuses W3-A's recursion (CG-1) for the cross-proof binding.

## Phasing (land sound, partial-OK per the lane's "DEEP/design-heavy" tag)

- **P1 — ZkResult read path (G-A).** `ProofCondition::ZkResult` + `ConditionProof::ZkResult` + the `resolve_condition` arm for `PerAction` and `Ivc`. Adversarial: a proof whose extracted output ≠ `expected_output` is rejected; a replayed proof hash is rejected; honest resolves once. *No registry change beyond the enum.*
- **P2 — CapabilityExercised (G-B).** The executor post-effect hook in `execute_tree.rs` + the `CapabilityExercised` arm. Adversarial: an *unauthorized* exercise does NOT resolve (it never reaches the hook — authorize.rs rejects it first); the *authorized* exercise resolves exactly the matching promise and cascades to dependents; a non-matching `(target,method)` does not resolve.
- **P3 — Anonymous resolution.** `anonymous:true` via StarkDelegation/BlindedSet; resolver pubkey not in PI; two resolutions by the same holder unlinkable.
- **P4 — CapTP fold-in.** `ResolutionCondition::AwaitCapTpPromise` so `PipelineRegistry` resolutions cascade through the *same* `PendingTurnRegistry::resolve` path; the three registries become one continuation surface. Differential test: a CapTP `PromiseResolved` and a `PendingTurnRegistry` resolution produce the same dependent-cascade.
- **P5 — zk-continuation folding.** IVC-fold a dependent chain into one `IvcProof`; verify the folded proof equals the sequential resolution. Reuses W3-A CG-1.

## Honest soundness boundary / open questions

- **Determinism (consensus):** every new resolution must be a pure function of (proof, ledger-resolvable roots/keys, block height) — same rule the existing `RemoteProof` path follows (trusted-root age check, conditional.rs:295). No wall-clock; expiry stays `timeout_height`.
- **`expected_output` binding strength:** P1 binds a 4-felt commitment (`PerActionSummary.new_commit` / `IvcProof.final_root` = `AccumulatedHash` 124-bit, ivc.rs:189). That's the same width the rest of the system trusts post-W3 (256-bit effect binding); the awaiting turn must carry `expected_output` in *its* PI so the dependency is itself provable, else the gate is off-chain trust.
- **CapabilityExercised re-entrancy:** the post-effect resolve hook must run *after* the exercising action commits and must not let a resolved dependent re-enter the same turn (bound recursion depth; reuse the OneOf nested-rejection discipline from action.rs).
- **CapTP P4 is the riskiest:** CapTP promises are `u64` session-scoped with no cryptographic id (pipeline.rs:160); folding them into a `[u8;32]`-keyed registry needs a deterministic promise→hash derivation that both federations agree on. May stay a *bridge* (translate at the boundary) rather than a true merge.
- **What this does NOT make ZK:** the STARKs are already statistically-ZK after W3-A only for the proofs that use the `stark_zk` HidingFriPcs config; per-action/IVC proofs use the standard prover and are succinct-but-not-hiding. A zkpromise hides *the resolver* (P3) and binds *the result* (P1), but the result commitment itself is only as hiding as the underlying commitment — say so, don't oversell.

## Why this shape

It makes the *existing* `PendingTurnRegistry` the single continuation primitive instead of a 4th registry; the proof-gated await (`ConditionalTurn`) and its nullifier/timeout/deposit machinery are reused wholesale; the ZK primitives (per-action, IVC, recursive FRI) plug in as new `ProofCondition`/`ConditionProof` arms with no circuit rewrite; and the one genuinely new idea — capability-resolved continuation — is expressed in the object-capability terms the system already enforces, answering the "resolve by exercising a local capability" gap directly.
