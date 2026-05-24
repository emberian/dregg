# DSL Framework Layer Audit

**Verdict:** NEEDS-WORK

## Summary

The "DSL framework" of pyana — comprising `turn::builder::{TurnBuilder, ActionBuilder}`, the `intent/` crate's intent expression + solver surface, the `app-framework/` crate's lifecycle helpers, and `sdk::wallet::AgentWallet`'s authoring methods — is a thin, untyped envelope around the runtime `turn::action::Effect` enum. Compared to the 41 runtime `Effect` variants, the user-facing surface is broken in three structural ways: (1) **coverage is sparse and inconsistent** — fewer than 25% of effect variants are reachable through any typed helper; the rest require apps to hand-construct `Effect::*` literals, defeating the purpose of having a framework; (2) **authorization defaults to `Authorization::Unchecked` everywhere** — every helper in `app-framework/src/escrow.rs`, every `Action` constructed in `apps/gallery/`, and every helper in `intent/src/fulfillment.rs` that builds a payment turn ships with `Unchecked` auth, so the framework's "secure-by-default" claim does not hold; (3) **lowering is silently lossy and not injective** — `AgentWallet::convert_effects_to_vm` (sdk/src/wallet.rs:4322) truncates 32-byte field elements to 4 bytes mod the BabyBear prime and maps roughly half of all `Effect` variants to `VmEffect::NoOp`, so the STARK proof that allegedly attests to a turn's execution does not, in fact, attest to its `Effect` content. There are additional smaller hazards: the two unstaged files (`intent/src/solver.rs`, `intent/src/trustless.rs`) cohere with the rest of `intent/` but the solver's settlement-amount computation has a bug (`min(x).max(x)` collapse), `apps/gallery/src/settlement.rs:92,110` declares conservation-law `balance_change` values that violate the documented invariant, and several `nonce: 0` placeholders in turn-building helpers ship without a way to be overridden by callers. The `ActionBuilder` itself is largely clean but does not validate that mutually exclusive fields (e.g. `Authorization::Proof.bound_action` vs `method`) agree, and `effect()` accepts arbitrary `Effect` literals so it inherits all the runtime invariants without enforcing any of them.

## Findings table

| # | Sev | File:Line | Description |
|---|-----|-----------|-------------|
| 1 | P0 | `app-framework/src/escrow.rs:95,155,207` | `EscrowManager` ships every escrow lifecycle turn with `Authorization::Unchecked`; the framework's "managed escrow" is unauthenticated |
| 2 | P0 | `sdk/src/wallet.rs:4322-4448` | `convert_effects_to_vm` truncates 32-byte field elements to 4 bytes mod p and maps EmitEvent / CreateCell / SetPermissions / SetVerificationKey / Bridge* / RegisterName / Introduce / PipelinedSend / Queue* / Escrow* / SpawnWithDelegation / Refresh / Revoke / SealPair to `VmEffect::NoOp` — the proof cannot distinguish those effects |
| 3 | P1 | `turn/src/builder.rs:152` | `ActionBuilder::new` defaults `authorization: Authorization::Unchecked`; no compile-time path forces the builder to be authorized before `build_action()` |
| 4 | P1 | `apps/gallery/src/settlement.rs:92,110` | Two-action atomic settlement uses `balance_change: Some(-(winning_bid as i64))` on the payment and `Some(winning_bid as i64)` on the transfer, but neither side performs the conservation-required note motion (no `NoteSpend`/`NoteCreate` pair); the documented "conservation law" is hand-waved |
| 5 | P1 | `intent/src/solver.rs:328-332` | `validate_ring` settlement amount is `min(receiver.want_min).max(receiver.want_min)` which collapses to just `want_min`; min-takes-the-smaller is the obvious intent but the code as written silently throws away the `.min` clamp |
| 6 | P1 | `turn/src/builder.rs:38,257` | `TurnBuilder::action` / `ActionBuilder::child` returns `&mut ActionBuilder` for chaining but the lifetime of the parent borrow forbids any further `&mut self` call on the outer builder — apps cannot interleave actions; documented "fluent" API is single-use |
| 7 | P1 | `sdk/src/wallet.rs:2441,2807` | `build_authorized_turn` hardcodes `nonce: 0` with a comment "Caller should set appropriately or use a TurnBuilder", but returns `SignedTurn` already signed — caller has no way to set the nonce after signing |
| 8 | P1 | `intent/src/lib.rs:535-536` | `compute_stake_nullifier` shifts epoch by 31 bits (`epoch >> 31`), producing overlapping `epoch_lo`/`epoch_hi` decomposition: bit 31 appears in both halves and bits 62+ are silently dropped |
| 9 | P1 | `turn/src/builder.rs` (entire file) | The builder does not expose helpers for ~31 of the 41 `Effect` variants (Bridge*, PipelinedSend, Spawn/Refresh/Revoke delegation, ExerciseViaCapability, CreateSealPair/Seal/Unseal, CreateCommittedEscrow*, Queue*, NoteSpend/NoteCreate, CreateObligation/Fulfill/Slash, MakeSovereign, CreateCellFromFactory) — apps must use the typeless `.effect(Effect::…)` escape hatch |
| 10 | P2 | `app-framework/src/batch_executor.rs:24-31` | `ClientTurnRequest.turn_bytes: Vec<u8>` is opaque — the framework's batch executor doesn't enforce that those bytes are a serialized `Turn`; deserialization happens (or not) inside the app |
| 11 | P2 | `app-framework/src/escrow.rs:149,201` | `release_with_proof` and `refund_expired` use `CellId::from_bytes(escrow_id)` as the agent identity — a sentinel-CellId pattern that has no key, no balance, no entry in any ledger; this is a footgun if anyone tries to look up the agent |
| 12 | P2 | `intent/src/fulfillment.rs:787,807,1186,1200` | `create_fulfillment_turn` and `execute_committed_fulfillment_flow` build turns with `nonce: 0` and `Authorization::Unchecked` — the comments say "Caller should set the real nonce before submission" but the caller has no API to do so |
| 13 | P2 | `sdk/src/wallet.rs:4365` | `convert_effects_to_vm` for `GrantCapability` hashes only `cap.slot.to_le_bytes()`, dropping the `cap.target` field — two grants to different targets but the same slot hash identically into the VM |
| 14 | P2 | `app-framework/src/escrow.rs:244-251` | `compute_escrow_id` derives the ID from `(from, to, amount, timeout)` only — two escrows with the same parameters share the same ID and collide |
| 15 | P2 | `turn/src/builder.rs:122-128` | `compute_excess` uses `saturating_add` over `i64` — a malicious caller can craft balance_change values that saturate to `i64::MAX/MIN` without the validator noticing |
| 16 | P2 | `turn/src/action.rs:88-118` | `Authorization::Unchecked` is `#[serde(alias = "None")]` — wire compatibility with old `"None"` JSON tag is silent; reviewers grepping for `None` in JSON wire formats may miss it |
| 17 | P2 | `intent/src/trustless.rs:285-306` | `IntentBatch.seen_intent_ids` is an unbounded `HashMap` that grows for the life of the engine (only the batch resets, not the dedup set across the engine); long-running engines leak memory |
| 18 | P3 | `intent/src/solver.rs:439-457` | `IntentGraph::is_compatible` returns a score based on `want_min/offer_amount` ratio, but the docstring says "perfect match = 1.0" when `offer == want`; if `offer_amount == want_min` the ratio is 1.0 — fine — but if `offer_amount >> want_min` the score approaches 0, which is "worse" than a tighter match: this inverts the intuitive ordering |
| 19 | P3 | `intent/src/trustless.rs:425` | `MockProofVerifier` is `pub` and is the default verifier returned by `TrustlessIntentEngine::new`; production code that forgets `with_verifier` ends up accepting any non-empty `Vec<u8>` as a STARK proof |
| 20 | P3 | `turn/src/builder.rs:215,237` | `require_nonce` and `require_field_equals` accept `usize` for index — silently truncates on 32-bit platforms and accepts indices > `u32::MAX` which the executor cannot represent |

---

## Per-finding sections

### Finding 1 — `EscrowManager` produces unauthenticated turns

**Files:** `/Users/ember/dev/breadstuffs/app-framework/src/escrow.rs:91-108`, `:151-164`, `:203-213`

```rust
let action = Action {
    target: from,
    method: symbol("create_escrow"),
    args: vec![],
    authorization: Authorization::Unchecked,   // <-- always Unchecked
    preconditions: Default::default(),
    effects: vec![Effect::CreateEscrow {
        cell: from, recipient: to, amount,
        condition, timeout_height: timeout, escrow_id,
    }],
    may_delegate: DelegationMode::None,
    commitment_mode: CommitmentMode::Full,
    balance_change: None,
};
```

**Impact:** `EscrowManager` is documented as a "managed workflow" and is used by `apps/compute-exchange/src/state.rs`, `apps/gallery/src/handlers.rs`. Every escrow it creates depends on the underlying cell's permissions to be `AuthRequired::None` for the relevant `set_state`/`send` slot. If the cell ever requires a signature or proof, the turn is rejected at execution; apps have no way to instruct the manager to pre-sign. Worse: if a cell *does* permit `Unchecked` (test fixtures, dev cells), then any caller of `EscrowManager` can drain that cell — the manager is effectively a privilege escalator.

**Fix:** Take an `Authorization` (or, better, an `Authorizer` callback) as a constructor parameter or per-call argument. Refuse to construct an `EscrowManager` with `Unchecked` outside of `cfg(test)`.

### Finding 2 — VM effect lowering loses information

**Files:** `/Users/ember/dev/breadstuffs/sdk/src/wallet.rs:4322-4448`

```rust
fn field_element_to_bb(value: &[u8; 32]) -> BabyBear {
    let val_u32 = u32::from_le_bytes([value[0], value[1], value[2], value[3]]);
    BabyBear::new(val_u32 % pyana_circuit::field::BABYBEAR_P)
}
…
for effect in effects {
    match effect {
        Effect::Transfer { … } => { … }
        Effect::SetField { …, value } => vm_effects.push(VmEffect::SetField {
            field_idx: *index as u32,
            value: field_element_to_bb(value),
        }),
        Effect::GrantCapability { to, cap, .. } if to == cell_id => {
            let cap_hash = blake3::hash(&cap.slot.to_le_bytes());   // <-- target dropped
            vm_effects.push(VmEffect::GrantCapability {
                cap_entry: hash_to_bb(cap_hash.as_bytes()),
            });
        }
        …
        _ => {
            // Other effects … map to NoOp
            vm_effects.push(VmEffect::NoOp);
        }
    }
}
```

**Impact:** This is the *only* function that lowers user-visible `Effect`s into the circuit-level `VmEffect`s that the STARK proof actually constrains. It silently:

- Truncates every 32-byte `FieldElement` to its first 4 bytes mod `BABYBEAR_P` (≈3·10⁹). Two different field values that share their first 31 bits in the low 4 bytes hash to the same VM value. The proof does not constrain the high 28 bytes of any `SetField` value.
- Maps `EmitEvent`, `CreateCell`, `SetPermissions`, `SetVerificationKey`, all four `Bridge*` variants, `Introduce`, `PipelinedSend`, all four `Escrow*` variants, all six `Queue*` variants, `CreateSealPair`, `SpawnWithDelegation`, `RefreshDelegation`, `RevokeDelegation`, `RevokeCapability` to `VmEffect::NoOp`. The proof attests that *something happened* — not what.
- For `GrantCapability`, hashes only `cap.slot.to_le_bytes()` (4 bytes), dropping `cap.target` entirely: granting cap-slot-7-on-X is indistinguishable from cap-slot-7-on-Y in the proof.
- For `Seal { pair_id }`, derives `field_idx = pair_id[0] % 8` — collisions every 256 pair IDs.

**Fix:** Either (a) widen `VmEffect` to carry full field-element-width data (likely required because BabyBear is 31-bit and `FieldElement` is 256-bit, so requires multiple BabyBear limbs), (b) hash with a domain-separated Poseidon2 to a *single* BabyBear (irreversible but at least covers the full preimage), or (c) emit a separate non-VM "auxiliary" digest as a public input alongside the VM proof. Until then, the wallet's STARK proof should not be marketed as "proving turn execution" — it proves a digest of the turn's `Transfer` deltas and `SetField` low-4-bytes only.

### Finding 3 — Builder defaults to unauthenticated

**Files:** `/Users/ember/dev/breadstuffs/turn/src/builder.rs:145-160`

```rust
impl ActionBuilder {
    pub fn new(target: CellId, method: &str) -> Self {
        ActionBuilder {
            target,
            method: method.to_string(),
            args: Vec::new(),
            authorization: Authorization::Unchecked,   // <-- default
            preconditions: Preconditions::default(),
            effects: Vec::new(),
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            children: Vec::new(),
        }
    }
```

`Authorization` deliberately renamed `None` → `Unchecked` to be grep-able (good); but the builder's default makes it the path of least resistance. There's no `ActionBuilder::new_signed(…)` or `ActionBuilder::new_proof(…)` constructor, nor is there a state-machine builder where `build_action` is only callable on `ActionBuilder<Authorized>`.

**Impact:** Every demo app that uses the builder (none currently — they all hand-construct `Action` literals) would inherit `Unchecked` unless the author remembers to call `.authorize_*`. Combined with finding 1, the entire app stack ships with `Unchecked` authorization in practice.

**Fix:** Make the builder's constructor accept an `Authorization` and remove the no-arg form. Or split into `ActionBuilder::<NeedsAuth>` / `ActionBuilder::<Ready>` typestate so `build_action` requires `Ready`.

### Finding 4 — gallery settlement violates documented conservation

**Files:** `/Users/ember/dev/breadstuffs/apps/gallery/src/settlement.rs:73-111`

```rust
let payment_action = Action {
    …
    effects: vec![
        Effect::ReleaseEscrow { escrow_id: self.winner_escrow_id, proof: Some(self.artwork_id.to_vec()) },
        Effect::Transfer { from: self.winner, to: self.artist, amount: self.winning_bid },
    ],
    balance_change: Some(-(self.winning_bid as i64)),   // <-- negative
};

let transfer_action = Action {
    …
    effects: vec![Effect::Transfer { from: self.artist, to: self.winner, amount: 1 }],
    balance_change: Some(self.winning_bid as i64),       // <-- positive winning_bid
};
```

The `balance_change` documentation in `turn/src/action.rs:79-82` says:

> At turn end, the sum of all balance_change deltas must be zero (conservation law).

The two deltas here are `-winning_bid` and `+winning_bid`, which do sum to zero. But the *transfer* in the second action is for amount `1` (the NFT), not `winning_bid`. So the declared `balance_change: +winning_bid` is unrelated to the actual `Transfer` effect, and the validator at `TurnBuilder::validate_excess` (`turn/src/builder.rs:112-128`) will pass even though no actual debit/credit reconciles. Also `winning_bid as i64` is a silent truncation if `winning_bid > i64::MAX`.

**Impact:** The DSL's "conservation law" is opt-in metadata, not enforced. Apps can lie. The executor presumably re-derives this from effects, but app authors using `balance_change` for client-side validation get spurious confidence.

**Fix:** Either remove `balance_change` from the DSL (let the executor derive it) or enforce in `validate_excess` that the sum of `balance_change` matches the sum of debit/credit deltas implied by the contained `Effect::Transfer`/`Note*` operations.

### Finding 5 — Solver settlement amount logic collapses

**Files:** `/Users/ember/dev/breadstuffs/intent/src/solver.rs:323-339`

```rust
let mut settlements = Vec::new();
for k in 0..ring.len() {
    let next = (k + 1) % ring.len();
    let offerer = &ring[k];
    let receiver = &ring[next];
    let amount = offerer
        .exchange
        .offer_amount
        .min(receiver.exchange.want_min_amount)
        .max(receiver.exchange.want_min_amount);   // <-- collapses .min above
    settlements.push(Settlement {
        from: offerer.creator,
        to: receiver.creator,
        asset: offerer.exchange.offer_asset,
        amount,
    });
}
```

`x.min(y).max(y)` is equivalent to `if x >= y { x.min(y) } else { y } = y`. The `.min(offer_amount)` clamp is silently discarded. The earlier validation pass at `solver.rs:270` already established `offer_amount >= want_min_amount`, so in valid rings the produced amount happens to be correct (= `want_min_amount`). But the intent was clearly to settle at the smaller of offered/wanted: in `find_rings`'s settlement-builder at line 202-211, the code correctly writes `to_node.exchange.want_min_amount.min(from_node.exchange.offer_amount)`. The two builders disagree.

**Impact:** Subtle but real: if a future refactor weakens `validate_ring`'s ordering check or accepts partial fills, this collapse silently picks the wrong amount.

**Fix:** Drop the `.max(receiver.exchange.want_min_amount)` call, matching `find_rings`.

### Finding 6 — Builder forbids interleaving actions

**Files:** `/Users/ember/dev/breadstuffs/turn/src/builder.rs:38-42, 257-260`

```rust
pub fn action(&mut self, target: CellId, method: &str) -> &mut ActionBuilder {
    self.action_builders
        .push(ActionBuilder::new(target, method));
    self.action_builders.last_mut().unwrap()
}
```

The returned `&mut ActionBuilder` borrows the `TurnBuilder` mutably; while the user is chaining `.set_field(..).transfer(..)`, they cannot call any other `&mut self` method on the outer `TurnBuilder` (including `.action(..)` again to add a sibling). The documented "fluent" pattern works for a single action but is awkward for multi-action turns.

**Impact:** Users either build actions in scopes (verbose, hides intent) or build the actions externally and `.effect()` them in. In practice, no app uses the builder — every app hand-constructs `Action` literals.

**Fix:** Return an *owned* `ActionBuilder` from `.action(…)` and add `.add_action(ActionBuilder)` to TurnBuilder. Or use an index-based handle (`fn action(&mut self, …) -> ActionHandle`) and have `fn edit_action(&mut self, h: ActionHandle) -> &mut ActionBuilder`.

### Finding 7 — `build_authorized_turn` signs with `nonce: 0`

**Files:** `/Users/ember/dev/breadstuffs/sdk/src/wallet.rs:2385-2461`

```rust
pub fn build_authorized_turn(…) -> Result<SignedTurn, SdkError> {
    …
    let turn = Turn {
        agent: self.cell_id("default"),
        nonce: 0, // Caller should set appropriately or use a TurnBuilder
        fee,
        …
    };

    Ok(self.sign_turn(&turn))
}
```

The signature is over the turn body including the `nonce`. The caller cannot mutate the nonce post-signing without invalidating the signature, and the method exposes no parameter for nonce.

**Impact:** Replay protection at the executor level depends on a monotonic nonce. The first turn the wallet produces and submits is the only nonce-0 turn it can ever submit using this API; subsequent calls all sign the same (agent=default, nonce=0) prefix and produce identical replayable turns.

**Fix:** Add `nonce: u64` parameter; remove the misleading comment.

### Finding 8 — Stake nullifier epoch split has overlap

**Files:** `/Users/ember/dev/breadstuffs/intent/src/lib.rs:527-558`

```rust
pub fn compute_stake_nullifier(commitment: &[u8; 32], epoch: u64, counter: u32) -> [u8; 32] {
    …
    let epoch_lo = BabyBear::new((epoch & 0x7FFF_FFFF) as u32);
    let epoch_hi = BabyBear::new(((epoch >> 31) & 0x7FFF_FFFF) as u32);
    …
}
```

`epoch & 0x7FFF_FFFF` keeps bits 0..30; `(epoch >> 31) & 0x7FFF_FFFF` keeps bits 31..61. Bit 31 is in the high half only — fine. But bits 62..63 are silently discarded. More importantly, the BLAKE3 fallback at the bottom hashes the full `epoch.to_le_bytes()`, so the *final* 32-byte nullifier does cover all 64 bits of epoch. The Poseidon2 input to `hash_many` however does not, so the Poseidon2 nullifier digest is only sensitive to 62 bits of epoch. The blended BLAKE3+Poseidon2 nullifier is fine for collision resistance but the comment claims "epoch as 2 field elements (high/low 32 bits)" which is misleading (it's 31+31).

**Impact:** Minor; documentation/naming issue. The 2 missing bits cap usable epochs at 2^62, which is fine for any realistic federation.

**Fix:** Either use 3 field elements to cover the full 64 bits, or update the comment to reflect the 62-bit limit and the BLAKE3 backstop.

### Finding 9 — Builder coverage gap

**Files:** `/Users/ember/dev/breadstuffs/turn/src/builder.rs:299-416`

```rust
impl ActionBuilder {
    pub fn set_field(…)        { … }
    pub fn transfer(…)         { … }
    pub fn increment_nonce(…)  { … }
    pub fn emit_event(…)       { … }
    pub fn grant_capability(…) { … }
    pub fn revoke_capability(…){ … }
    pub fn create_cell(…)      { … }
    pub fn set_permissions(…)  { … }
    pub fn set_verification_key(…) { … }
    pub fn introduce(…)        { … }
}
```

10 helpers exist. The `Effect` enum (`turn/src/action.rs:220-619`) has 41 variants. The other 31 (`NoteSpend`, `NoteCreate`, `CreateSealPair`, `Seal`, `Unseal`, `BridgeMint`, `BridgeLock`, `BridgeFinalize`, `BridgeCancel`, `PipelinedSend`, `CreateObligation`, `FulfillObligation`, `SlashObligation`, `CreateEscrow`, `ReleaseEscrow`, `RefundEscrow`, `CreateCommittedEscrow`, `ReleaseCommittedEscrow`, `RefundCommittedEscrow`, `ExerciseViaCapability`, `MakeSovereign`, `CreateCellFromFactory`, `QueueAllocate`, `QueueEnqueue`, `QueueDequeue`, `QueueResize`, `QueueAtomicTx`, `QueuePipelineStep`, `SpawnWithDelegation`, `RefreshDelegation`, `RevokeDelegation`) require the user to construct `Effect::*` literals manually and pass through `.effect(e)`.

**Impact:** The "framework" provides no type-safety improvement over directly constructing the runtime structs; apps that need any non-trivial effect must import `pyana_turn::action::Effect` and assemble it themselves, defeating the abstraction.

**Fix:** Either (a) generate the builder via macro from the `Effect` enum, (b) accept that the builder is for the common-case effects only and document the lower-level path, or (c) split the framework into "high-level" (intent → action) and "low-level" (effect plumbing) crates so the inconsistency isn't hidden.

### Finding 10 — `ClientTurnRequest.turn_bytes` is opaque

**Files:** `/Users/ember/dev/breadstuffs/app-framework/src/batch_executor.rs:24-31`

```rust
pub struct ClientTurnRequest {
    pub client: CellId,
    pub turn_bytes: Vec<u8>,
    pub deadline_height: Option<u64>,
}
```

Apps implementing `BatchExecutor::execute_batch` are responsible for deserializing the bytes. If the app uses a different `Turn` schema than the wallet, requests silently fail to deserialize; if the schema matches but the wire format isn't versioned (it isn't), version drift between client and executor causes silent rejection.

**Impact:** Cross-app compatibility issues; no central place to validate the wire format before dispatching.

**Fix:** Either typed (`turn: Turn`) or versioned (`turn_bytes: Vec<u8>, schema_version: u32`).

### Finding 11 — Sentinel `CellId` as escrow agent

**Files:** `/Users/ember/dev/breadstuffs/app-framework/src/escrow.rs:147-150,200-202`

```rust
// We use a sentinel agent for the release turn (the executor validates
// the proof against the escrow condition, not the agent identity).
let agent = CellId::from_bytes(escrow_id);
```

`escrow_id` is a 32-byte hash; treating it as a `CellId` means any executor that looks up the agent (e.g., to charge fees, look up nonce, increment epoch) will look up a nonexistent cell. The current executor presumably handles this by skipping those checks for `Unchecked` auth, but the coupling is implicit.

**Impact:** Cross-cutting executor changes (e.g., fee charging) could break escrow release/refund without obvious test signal.

**Fix:** Take the caller's `CellId` and a key for the release authorization; do not invent an agent identity.

### Finding 12 — `create_fulfillment_turn` has unset nonce and unsigned auth

**Files:** `/Users/ember/dev/breadstuffs/intent/src/fulfillment.rs:783-832,1182-1216`

```rust
let action = Action {
    target: payer_cell,
    method: pyana_turn::action::symbol("fulfillment_payment"),
    args: Vec::new(),
    authorization: Authorization::Unchecked,
    …
};
…
let turn = Turn {
    agent: payer_cell,
    nonce: 0, // Caller should set the real nonce before submission.
    …
};
```

The comment says caller will set nonce, but `ConditionalTurn` exposes `pub turn: Turn` — a mutable field — so the only way to fix is for callers to know to do `cond.turn.nonce = …` before submitting. Apps that don't will be reverted at the executor's nonce check.

**Impact:** Footgun. Tests pass because nonce-0 succeeds on a fresh cell; production hits the second submission and fails.

**Fix:** Take `nonce: u64` as a parameter; remove the `pub` on `turn`.

### Finding 13 — `convert_effects_to_vm` drops cap target

**Files:** `/Users/ember/dev/breadstuffs/sdk/src/wallet.rs:4363-4369`

```rust
Effect::GrantCapability { to, cap, .. } if to == cell_id => {
    let cap_hash = blake3::hash(&cap.slot.to_le_bytes());
    vm_effects.push(VmEffect::GrantCapability {
        cap_entry: hash_to_bb(cap_hash.as_bytes()),
    });
}
```

`CapabilityRef` is `{ target: CellId, slot: u32 }`. The hash here covers only the slot. Two grants — `cap.target = X, slot = 5` and `cap.target = Y, slot = 5` — produce identical VM hashes.

**Impact:** STARK proof cannot distinguish granting different cells' caps; capability authority can be "swapped" between cells without changing the proof.

**Fix:** Hash both `cap.target.as_bytes()` and `cap.slot.to_le_bytes()`.

### Finding 14 — `compute_escrow_id` is collision-prone

**Files:** `/Users/ember/dev/breadstuffs/app-framework/src/escrow.rs:244-251`

```rust
fn compute_escrow_id(from: &CellId, to: &CellId, amount: u64, timeout: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-app-framework-escrow-id-v1");
    hasher.update(from.as_bytes());
    hasher.update(to.as_bytes());
    hasher.update(&amount.to_le_bytes());
    hasher.update(&timeout.to_le_bytes());
    *hasher.finalize().as_bytes()
}
```

Two escrows from the same payer to the same recipient with the same amount and timeout (a common pattern: e.g., a subscription payment) share the same ID. The executor's escrow registry presumably refuses to create a duplicate, so the second escrow is silently rejected.

**Impact:** Apps trying to create multiple equivalent escrows (perfectly reasonable) get a confusing "duplicate" error.

**Fix:** Include a caller-supplied salt or the current block height in the derivation.

### Finding 15 — `compute_excess` uses saturating arithmetic

**Files:** `/Users/ember/dev/breadstuffs/turn/src/builder.rs:121-128, 405-415`

```rust
fn compute_excess(&self) -> i64 {
    let mut total: i64 = 0;
    for ab in &self.action_builders {
        total = total.saturating_add(ab.compute_excess_recursive());
    }
    total
}
```

A caller that supplies `balance_change: i64::MIN` on one action and `i64::MAX` on another (or any combination that overflows in either direction) will get a non-zero `total` and `validate_excess` will reject — but a clever sequence can saturate intermediate sums to zero without the *true* arithmetic sum being zero.

**Impact:** Low (the executor presumably re-validates with its own arithmetic), but the client-side check is unsound for adversarial inputs.

**Fix:** Use `checked_add` and return `Err(Overflow)` instead of saturating.

### Finding 16 — Wire-format alias for `None` → `Unchecked`

**Files:** `/Users/ember/dev/breadstuffs/turn/src/action.rs:115-117`

```rust
/// No authorization provided (only valid if the cell's permissions allow it).
/// Named `Unchecked` rather than `None` to make it grep-able …
#[serde(alias = "None")]
Unchecked,
```

The grep-able rename is good defensive design; the `#[serde(alias = "None")]` undoes that defense at the wire boundary. A code reviewer searching for `Authorization::None` in JSON payloads, log lines, or test fixtures finds nothing — but those payloads are still accepted.

**Impact:** Mostly cosmetic / process; the alias itself is correctly handled.

**Fix:** Remove the alias after a deprecation window, or rename it `LegacyNoneAlias` so it's findable.

### Finding 17 — Trustless engine's dedup set grows without bound

**Files:** `/Users/ember/dev/breadstuffs/intent/src/trustless.rs:285-306, 770-776`

```rust
pub struct IntentBatch {
    …
    /// Content IDs of submitted intents (for deduplication).
    seen_intent_ids: HashMap<[u8; 32], ()>,
}
…
// In finalize():
self.current_batch = IntentBatch::new(new_batch_id);
```

The batch's dedup set is reset when a new batch starts, *but* there's no cross-batch dedup, so an attacker can replay an old encrypted intent in a new batch. Combined with `EncryptedIntent::content_id` including `submitted_at` (line 198), a replayed intent with a new `submitted_at` field gets a fresh content_id and is accepted — so dedup is per-(content, height), not per-(content). That's intentional (allows resubmission after expiry) but means the dedup map grows linearly with batch size, capped by `MAX_INTENTS_PER_BATCH = 256` — so finding is downgraded to P2 (bounded growth per batch, but unbounded `settled_batches`).

**Impact:** `settled_batches: HashMap<u64, CompoundTurn>` (line 411) never garbage-collects; in a long-running engine this is the actual leak.

**Fix:** Add a TTL/cap on `settled_batches`; expose a pruning API.

### Finding 18 — Compatibility score inverts intuitive ordering

**Files:** `/Users/ember/dev/breadstuffs/intent/src/solver.rs:439-457`

```rust
pub fn is_compatible(a: &IntentNode, b: &IntentNode) -> Option<f64> {
    if a.exchange.offer_asset != b.exchange.want_asset { return None; }
    if a.exchange.offer_amount < b.exchange.want_min_amount { return None; }

    let ratio = b.exchange.want_min_amount as f64 / a.exchange.offer_amount as f64;
    let score = ratio.min(1.0);
    Some(score)
}
```

If A offers 1000 and B wants 100, ratio = 0.1 (low score). If A offers 100 and B wants 100, ratio = 1.0 (high score). The comment says "Overshoot is slightly penalized (excess is wasted in the ring context)" — but ring trades don't actually "waste" the excess; the offer_amount is the *maximum* a participant will give, and the settlement amount is `min(offer, want)`. So a 10× excess is no worse than a 1× excess.

**Impact:** The greedy solver may prefer tightly-matched rings over loosely-matched ones, which can be socially suboptimal (a 100-want participant being matched against a 100-offer when a 10000-offer was also available isn't worse).

**Fix:** Score = 1.0 if `offer >= want`, else None. Or use a multi-criteria score.

### Finding 19 — `MockProofVerifier` is the default

**Files:** `/Users/ember/dev/breadstuffs/intent/src/trustless.rs:334-381, 416-429`

```rust
impl ProofVerifier for MockProofVerifier {
    fn verify(&self, proof: &[u8], …) -> Result<(), String> {
        if proof.is_empty() { return Err("empty proof".to_string()); }
        // … verify score consistency, no double-use, intents in batch …
        Ok(())
    }
}

impl TrustlessIntentEngine {
    pub fn new(decrypt_threshold: usize, num_validators: usize) -> Self {
        Self { …, verifier: Box::new(MockProofVerifier), … }
    }
}
```

`new()` is presumably the constructor most users will reach for. The mock accepts any non-empty bytes as proof. There's a `with_verifier` constructor, but no compiler enforcement that production code uses it.

**Impact:** A federation deployed with `TrustlessIntentEngine::new(...)` instead of `with_verifier(...)` would accept arbitrary solver submissions with non-empty proof bytes.

**Fix:** Remove the no-arg constructor in non-test builds; require `with_verifier` in production. Or document strongly and add a `cfg(debug_assertions)` warning.

### Finding 20 — `usize` for field index

**Files:** `/Users/ember/dev/breadstuffs/turn/src/builder.rs:211-218, 231-238, 302`

```rust
pub fn require_field_equals(&mut self, index: usize, value: FieldElement) -> &mut Self {
    let cell_pre = self.preconditions.cell_state.get_or_insert_with(Default::default);
    cell_pre.field_equals.push((index, value));
    self
}
…
pub fn set_field(&mut self, cell: CellId, index: usize, value: FieldElement) -> &mut Self {
    self.effects.push(Effect::SetField { cell, index, value });
    self
}
```

`Effect::SetField` and `Preconditions::cell_state.field_equals` use `usize` — host-platform-dependent. The 64-bit serialization (`(*index as u64).to_le_bytes()` at action.rs:746) won't lose information on 64-bit, but a 32-bit prover and a 64-bit executor disagree if the index exceeds `u32::MAX`.

**Impact:** Realistically nothing because nobody has 4B+ state fields, but the type leaks platform-dependence into the cross-network protocol.

**Fix:** Use `u32` consistently. Or `FieldIndex(NonZeroU32)`.

---

## Coverage matrix

Mapping runtime `Effect` variants (from `/Users/ember/dev/breadstuffs/turn/src/action.rs:220-619`) to DSL reachability:

| Effect variant | `ActionBuilder` helper | Used in `intent/` lowering | Used in `app-framework/` | Used in `apps/*` | Notes |
|----------------|------------------------|----------------------------|--------------------------|------------------|-------|
| `SetField` | `set_field` | no | no | no | Builder-only |
| `Transfer` | `transfer` | `fulfillment.rs:789` | (escrow indirectly) | `gallery/settlement.rs`, others | Most-used variant |
| `GrantCapability` | `grant_capability` | no | no | no | Builder-only |
| `RevokeCapability` | `revoke_capability` | no | no | no | Builder-only |
| `EmitEvent` | `emit_event` | no | no | no | Builder-only |
| `IncrementNonce` | `increment_nonce` | no | no | no | Builder-only |
| `CreateCell` | `create_cell` | no | no | no | Builder-only |
| `SetPermissions` | `set_permissions` | no | no | no | Builder-only |
| `SetVerificationKey` | `set_verification_key` | no | no | no | Builder-only |
| `NoteSpend` | **no** | `fulfillment.rs:1131` | no | no | Hand-built; appears via `execute_committed_fulfillment_flow` only |
| `NoteCreate` | **no** | `fulfillment.rs:1171` | no | no | Hand-built |
| `CreateSealPair` | **no** | no | no | no | **Unreachable through DSL** |
| `Seal` | **no** | no | no | no | **Unreachable through DSL** (lowered in `convert_effects_to_vm` only) |
| `Unseal` | **no** | no | no | no | **Unreachable through DSL** |
| `BridgeMint` | **no** | no | no | no | **Unreachable through DSL** |
| `BridgeLock` | **no** | no | no | no | **Unreachable through DSL** |
| `BridgeFinalize` | **no** | no | no | no | **Unreachable through DSL** |
| `BridgeCancel` | **no** | no | no | no | **Unreachable through DSL** |
| `Introduce` | `introduce` | no | no | no | Builder-only |
| `PipelinedSend` | **no** | no | no | no | **Unreachable through DSL** |
| `CreateObligation` | **no** | no | no | no | **Unreachable through DSL** (referenced as VM mapping only) |
| `FulfillObligation` | **no** | no | no | no | **Unreachable through DSL** |
| `SlashObligation` | **no** | no | no | no | **Unreachable through DSL** |
| `CreateEscrow` | **no** | no | `escrow.rs:97` | (orderbook tests) | Via `EscrowManager` (`Unchecked` auth, finding 1) |
| `ReleaseEscrow` | **no** | no | `escrow.rs:157` | `gallery/settlement.rs:80`, others | Via `EscrowManager` |
| `RefundEscrow` | **no** | no | `escrow.rs:209` | `gallery/settlement.rs:171`, `orderbook/lib.rs:225` | Via `EscrowManager` |
| `CreateCommittedEscrow` | **no** | no | no | no | **Unreachable through DSL** |
| `ReleaseCommittedEscrow` | **no** | no | no | no | **Unreachable through DSL** |
| `RefundCommittedEscrow` | **no** | no | no | no | **Unreachable through DSL** |
| `ExerciseViaCapability` | **no** | no | no | no | **Unreachable through DSL** |
| `MakeSovereign` | **no** | no | no | no | **Unreachable through DSL** (VM mapping only) |
| `CreateCellFromFactory` | **no** | no | no | no | **Unreachable through DSL** (VM mapping only) |
| `QueueAllocate` | **no** | no | no | no | **Unreachable through DSL** |
| `QueueEnqueue` | **no** | no | (queue_endpoint via storage layer) | no | The HTTP endpoint targets `ProgrammableQueue` directly, not via `Effect::QueueEnqueue` |
| `QueueDequeue` | **no** | no | (queue_endpoint) | no | Same |
| `QueueResize` | **no** | no | no | no | **Unreachable through DSL** |
| `QueueAtomicTx` | **no** | no | no | no | **Unreachable through DSL** |
| `QueuePipelineStep` | **no** | no | no | no | **Unreachable through DSL** |
| `SpawnWithDelegation` | **no** | no | no | no | **Unreachable through DSL** |
| `RefreshDelegation` | **no** | no | no | no | **Unreachable through DSL** |
| `RevokeDelegation` | **no** | no | no | no | **Unreachable through DSL** |

Summary: **10 of 41 variants (24%)** have a typed `ActionBuilder` helper. **3 of 41 variants (7%)** have a higher-level lifecycle helper in `app-framework`. **22 of 41 variants (54%)** are not reachable through any DSL surface — they exist only as runtime types and must be constructed manually via `Effect::*` literals.

Worse: the `intent` crate's "lowering" is essentially limited to `Effect::Transfer` (payments), `Effect::NoteSpend` / `Effect::NoteCreate` (committed payments), and `Effect::RefundEscrow` (cancellation). The trustless solver's "settlement turn" produces `SettlementAction` (`trustless.rs:253-264`) which is a *separate type* from `Effect::Transfer` — there is no code that converts a `CompoundTurn` (the trustless settle output) into an executable `Turn`. The output of `TrustlessIntentEngine::finalize` is structurally a settlement but operationally a payload that must be hand-translated by the federation node.

Conversely, the runtime's `Effect::CreateCellFromFactory`, `Effect::MakeSovereign`, the entire `Bridge*` family, the entire `QueueProgram` family, `ExerciseViaCapability`, and the bearer-cap delegation chain are not constructable from the high-level surface at all — apps that want these must reach into `pyana_turn::action::Effect` directly.

The `app-framework`'s `RingTradeParticipant` trait and `Settlement` type also do not produce `Effect`s — they delegate to app-specific `settle_leg` impls. So the framework's "ring trade" abstraction is not actually a turn-builder; it's a coordination protocol.

---

## Open questions for the designer

1. **Is the `ActionBuilder` intended to be the public DSL, or an internal convenience?** Currently no app uses it — every app hand-rolls `Action { … }` literals. If the builder is the intended surface, the coverage gap (finding 9) is critical; if it's internal, document it and provide app-shaped builders per pattern (escrow flow, NFT mint flow, AMM swap flow).

2. **Should `intent` lower to `Effect` at all, or is its job purely matching/discovery?** The current code lowers in three places (`fulfillment.rs:789`, `:1131`, `:1171`) — each builds a turn from scratch. If apps are expected to take a `Match` and translate to effects themselves, then `fulfillment.rs`'s embedded turn-builders are vestigial. If the intent layer is supposed to own the lowering, then the trustless engine's `CompoundTurn` → `Turn` translation is the missing piece.

3. **What is the relationship between `pyana-dsl` (the source-to-circuit DSL in `pyana-dsl/src/`) and the "DSL" of this audit?** The `pyana-dsl` crate has its own `gen_*` backends but does not appear to produce `Effect` values — it produces circuit definitions. Are these meant to converge?

4. **`Authorization::Unchecked` as the builder default is convenient but unsafe.** Should the builder require an authorization at construction time? Or should the executor's policy be tightened (forbid `Unchecked` outside of tests)?

5. **`balance_change` as advisory metadata** — finding 4 shows this is decoupled from the actual transfer effects. Is the field meant to be a denormalization for client-side ergonomics, or a normative constraint that the executor enforces? If the latter, the validator needs to cross-check declared deltas against effect contents.

6. **`CompoundTurn` (trustless) vs `Turn` (executor) vs `Settlement` (ring trade participant)** — three different "what to execute" types live in the framework, none of them losslessly convertible to the others. Should there be a unifying `Executable` type?

7. **VM lowering coverage** — the `convert_effects_to_vm` function (finding 2) silently no-ops the majority of effects. Is the intent that the proof only attests to the "balance arithmetic" portion, and that the executor separately validates the other effects with full preimage? If so, this needs documentation; if not, this is a soundness issue.

8. **Should `MockProofVerifier` be available outside of `#[cfg(test)]`?** Finding 19. Pragma question.

9. **Is `RegisterName` a planned `Effect` variant?** `sdk/src/names.rs:659` comments "Submit Effect::RegisterName to the federation" but no such variant exists in `turn::action::Effect`. Either the variant is missing or the comment is stale.

10. **The unstaged files (`intent/src/solver.rs`, `intent/src/trustless.rs`) cohere structurally with the rest of `intent/`** — same `Intent` / `CommitmentId` / `IntentId` types, same error-type-per-module style, similar `RingTrade` shape. The cohesion concern is the *opposite* — they are not yet integrated. The trustless engine produces `CompoundTurn` but no consumer translates it to `Turn`; the ring solver produces `RingTrade` and `Settlement` but only `RingTradeParticipant::settle_leg` (in `app-framework`) is wired to consume settlements. Should there be a `pyana_intent::lowering` module that converts `RingTrade` / `Settlement` / `CompoundTurn` into an executable `Turn`?
