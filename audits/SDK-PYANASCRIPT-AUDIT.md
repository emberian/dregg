# SDK-Pyanascript Audit — Bottom-Up Gap Walk

Written 2026-05-24 against `sdk/src/`, `cell/src/`, `storage/src/`,
`app-framework/src/` HEAD. Companion to `SDK-REVIEW.md` (task #58) — that
document audited the SDK *for its own sake*; this one is exclusively
the bottom-up walk that `pyanascript/README.md` §"Design discipline"
asks for: **imagine the runtime API pyanascript would compile to,
write each primitive as an ugly Rust method-chain, identify the SDK
gap.**

The discipline (`pyanascript/README.md`):

> Before designing the surface language, imagine the **runtime API** it
> would compile to. Implement (or design) every primitive as an ugly
> Rust method-chain. If the chain is awkward, the awkwardness is real
> and identifies what's missing in the SDK/runtime. Macro the chains
> once they work. Only then consider what the surface language should
> look like.

Reference shape from `pyanascript/README.md` §Q1:

```rust
let cell = Cell::new(wallet)
    .with_state(MyState::default())
    .with_behavior(handler);

cell.send(target_cap, MsgKind::Bid { amount: 100 })?;
let response = cell.exercise(cap, args).await?;
let attenuated = cell.attenuate_cap(cap, narrower_permissions)?;
cell.spawn_child_with_behavior(child_spec)?;
cell.on_receive(|state, msg, caps| { ... });
```

Augmented per task #61:

- `let inbox = CapInbox::new(...)` (post-storage-as-cell-programs migration)
- `cell.declare_slot_caveat(...)` (post-slot-caveats v1)
- `wallet.create_from_factory(descriptor)` (already exists; document SDK shape)

Plus the implicit primitives that walk-out reveals:

- `cell.handle(msg, ctx)` synchronous handler dispatch (the bridge between
  message arrival and `on_receive` body)
- `cell.append_caveat(predicate)` macaroon-style attenuation on a held cap
- `cell.fork()` / `cell.snapshot()` for replay-based persistence

## Status of the codebase relative to the audit

Lane H ("framework wallet refactor") and Lane SDK-REVIEW Phase 2 have
already landed:

- `AgentWallet::sign_action(action, federation_id)`
- `AgentWallet::make_action(target, method, effects, federation_id)`
- `AgentWallet::make_turn(action)` / `make_turn_for(domain, action)`
- `AgentWallet::make_turn_with_actions(..)`
- `AppWallet` framework wrapper (`app-framework/src/wallet.rs`) that
  carries a single `federation_id` and exposes the same three helpers
  without forcing apps to thread the id manually
- `SdkError::CapTpNotConfigured` + a `captp_mut()` private helper used
  by `share_capability`, `accept_capability`, `delegate_offline`
- `LiveRef::send` is no longer a stub — it allocates a target promise,
  resolves it to the bearer cell, enqueues a `WireMessage::PipelinedMsg`,
  and returns an `EventualRef` for the result. (SDK-REVIEW C-2 closed
  on the SDK side; the wire driver behaviour is now the load-bearing
  piece, not the SDK shape.)
- Queue methods (`allocate_queue`, `enqueue_message`, `dequeue_message`,
  `atomic_queue_tx`) take an explicit `federation_id: &[u8; 32]` and
  produce `Authorization::Signature(..)` via `make_action`/`make_turn`
  (Lane this-task; closes SDK-REVIEW C-3).

So most of "Phase 2" Tier-0 work in `SDK-REVIEW.md` is done. What
remains is the *bottom-up* layer — the `Cell::new(wallet)...`
method-chain that pyanascript would compile against. None of that
exists as a type. The rest of this document walks the chain primitive
by primitive and names the gaps.

## Method-chain walk

For each primitive, this section gives (a) the chain as pyanascript
would write it, (b) the closest current-day Rust expression, (c) what
breaks if you try to compile it today.

### 1. `Cell::new(wallet).with_state(state).with_behavior(handler)`

**Pyanascript shape:**
```rust
let cell = Cell::new(wallet)
    .with_state(MyAuctionState { bids: vec![], highest: None })
    .with_behavior(|state, msg, ctx| { /* … */ });
```

**Current closest (ugly):**
```rust
// Allocate a cell id off the wallet:
let cell_id = wallet.cell_id("auction-1");

// Build the cell via the low-level cell crate (NOT the SDK):
let mut cell = pyana_cell::Cell::new_hosted(
    wallet.public_key().0,
    /* token_id */ [0u8; 32],
);
// `state` here is field-shaped, not Rust-shaped:
let cell = cell
    .with_balance(0)
    .with_program(pyana_cell::CellProgram::Predicate(vec![
        // Slot constraints encoding "MyAuctionState fields are these:"
    ]));

// `with_behavior` has no analogue. The closest is:
let descriptor = pyana_cell::CircuitDescriptor { /* … */ };
// then later:
wallet.deploy_program(node_url, descriptor).await?;
// — but `deploy_program` requires a *deployed STARK program*, not a
// closure. There is no "in-process handler" concept.
```

**SDK gap:**

- *Missing.* No SDK type named `Cell` representing "this wallet's
  logical cell, with state and behaviour." `pyana_cell::Cell` is the
  on-ledger record, not the runtime handle. The SDK has `AgentWallet`
  and `AgentRuntime` (wallet + ledger + executor) but no `Cell`-shaped
  facade.
- *Missing.* `with_state(rust_value)` requires a state-encoding bridge
  from Rust types into the cell's slot fields (`Vec<u64>` keyed by
  `field_index`). No SDK helper exists. Apps today encode by hand into
  `(field_index, value)` pairs (`apps/nameservice/src/effects.rs:294`).
- *Missing entirely.* `with_behavior(closure)` has no analogue —
  closures cannot today be installed as cell behaviour. The only
  "behaviour" notion is `CellProgram::Predicate(Vec<StateConstraint>)`
  (perpetual invariants over field slots, predicate-shaped) or
  `CellProgram::Circuit { circuit_hash }` (deployed STARK program).
  Neither is a function from `(state, msg) → (new_state, effects)`.

**Verdict:** the closure-vs-circuit decision is the single biggest
unresolved design question for pyanascript. Two viable paths:

1. **Compile closure to circuit.** `pyana-dsl-runtime::CellProgram`
   already targets a DSL; pyanascript's `with_behavior(closure)` could
   compile the closure body to a `CircuitDescriptor` via the existing
   gen_* backends. **Cost:** the closure body is restricted to what
   the DSL/circuit can express.
2. **Run closure as host-side actor.** A new `pyana_runtime::Actor`
   type that holds an `Arc<RwLock<State>>` and a `Box<dyn Fn(...)>`,
   driven by a host event loop. **Cost:** loses provability — host
   actors are not part of the witnessed receipt chain.

Path 1 is the one consistent with the rest of pyana's philosophy
("witnessed everywhere"). Path 2 is the one consistent with how every
other actor system works. Resolving this is the prerequisite for
*any* pyanascript work; it cannot be punted.

### 2. `cell.send(target_cap, MsgKind::Bid { amount: 100 })`

**Pyanascript shape:**
```rust
let promise = cell.send(auctioneer_cap, MsgKind::Bid { amount: 100 })?;
```

**Current closest (ugly):**
```rust
// You need a CapTP client and a LiveRef to the target:
let live_ref: pyana_captp::LiveRef = wallet
    .accept_capability("pyana://auctioneer/...")?;

// Build a PipelinedAction (this is `cell.send`'s payload shape today):
let action = pyana_captp::pipeline::PipelinedAction {
    method: pyana_captp::symbol("bid"),
    args: postcard::to_allocvec(&BidArgs { amount: 100 })?,
    authorization: pyana_captp::action::Authorization::Signature(..),
};

// Send it (LiveRef::send was a stub until very recently; now it
// allocates a promise and enqueues a wire message):
let promise: EventualRef = live_ref.send(action);
```

**SDK gap:**

- *Partial.* `LiveRef::send` exists and now actually dispatches
  (`sdk/src/captp_client.rs:172`). But the payload shape is
  `PipelinedAction { method, args: Vec<u8>, authorization }` — there is
  no `MsgKind::Bid { amount }` enum-shaped wire format. Apps must
  hand-encode (postcard, serde_json, whatever) into `args: Vec<u8>` and
  hand-decode on the other side.
- *Missing.* No SDK helper "given a Rust message type that derives
  Serialize, build a `PipelinedAction` whose `args` are the encoded
  message and whose `method` is the variant name." Pyanascript needs
  this — every `cell.send(cap, msg)` call would emit it.
- *Missing.* No SDK type called `MsgKind` (this is pyanascript's
  abstraction; the SDK needs something concrete). The pattern is
  `enum MsgKind: Serialize { Bid {..}, Cancel, ... }` and a derive
  macro that maps each variant to a stable `symbol(&str)` method
  identifier. **Closest reference:** `pyana_captp::symbol("bid")` is
  blake3-of-name, used as the method id today.
- *Missing.* `send` is fire-and-forget plus promise; there is no
  *await-the-receipt* convenience. The promise resolves when the
  target federation produces a receipt, but the SDK has no
  `promise.await_receipt()` that blocks the caller. (See gap 3.)

**Verdict:** the wire mechanism exists; the **typed-message bridge** does
not. This is a tractable Tier-0/Tier-1 SDK addition (an SDK trait
`pub trait CapMessage: Serialize { fn method(&self) -> [u8; 32]; }` plus
a `wallet.send_typed(live_ref, msg)` helper).

### 3. `cell.exercise(cap, args).await`

**Pyanascript shape:**
```rust
let receipt: TurnReceipt = cell.exercise(escrow_cap, Args { ... }).await?;
```

**Current closest (ugly):**
```rust
// "Exercise a capability" today means "build an authorized turn,
// execute it, get the receipt." That is `build_authorized_turn` +
// `runtime.execute_turn`:
let signed_turn = wallet.build_authorized_turn(
    &held_token,
    target,
    vec![Effect::ReleaseEscrow { escrow_id, .. }],
    "release_escrow",
    "escrow",
    /* fee */ 100,
)?;
let receipt: TurnReceipt = runtime.execute_turn(&signed_turn.turn)?;
```

**SDK gap:**

- *Missing.* No single-call `exercise(cap, args).await` on any SDK
  type. The three pieces (build, sign, execute) are three separate
  steps on `AgentWallet` + `AgentRuntime`.
- *Async vs sync.* `runtime.execute_turn` is **synchronous** (the
  embedded executor runs in-process). `cell.exercise(cap, args).await`
  presumes an async path — which exists for remote federations
  (`deploy_program`, `register_with_federation`) but not for local
  execution. Pyanascript will need *both* — local
  `exercise.execute()` (sync) and remote `exercise.send().await`
  (async-via-CapTP).
- *Missing.* The bridge from `cap: HeldToken` (macaroon-bearer) or
  `cap: LiveRef` (CapTP-bearer) to "the action that exercises it" is
  not a single SDK call. Two cap surfaces (see gap 6) means two
  different exercise paths.

**Verdict:** a Tier-1 SDK helper `wallet.exercise(cap, method, args) ->
Result<TurnReceipt>` (sync) and an `EventualRef::await_receipt()` (async)
would close most of the gap. Both are mechanical.

### 4. `cell.attenuate_cap(cap, narrower_permissions)`

**Pyanascript shape:**
```rust
let read_only_cap = cell.attenuate_cap(
    full_cap,
    Permissions::READ_ONLY,
)?;
```

**Current closest (ugly):**
```rust
// Depends on which "cap" you mean — there are two parallel languages.

// (a) HeldToken (macaroon-style bearer cap):
let restrictions = pyana_token::Attenuation {
    services: vec![("storage".to_string(), "r".to_string())],
    ..Default::default()
};
let attenuated: HeldToken = wallet.attenuate(&full_token, &restrictions)?;

// (b) CapabilityRef (cell-resident cap):
let mut cap_set = pyana_cell::CapabilitySet::new();
let slot = cap_set.grant(target_cell, AuthRequired::Signature).unwrap();
let attenuated_cap: AttenuatedCap = cap_set
    .attenuate(slot, AuthRequired::Signature)
    .unwrap();
```

**SDK gap:**

- *Partial / fragmented* (SDK-REVIEW C-3, still open). Two parallel
  cap surfaces:
  - `pyana_sdk::HeldToken` / `pyana_token::Attenuation` (macaroon-bearer)
  - `pyana_cell::CapabilityRef` / `pyana_cell::AttenuatedCap` (cell-resident)
- *Missing.* No unified `Capability` type. Pyanascript can't have one
  signature for `cell.attenuate_cap(cap, narrower)` until the two
  notions converge — or until pyanascript explicitly compiles to two
  different methods (`attenuate_token` vs `attenuate_cell_cap`).
- *Documentation gap.* No doc says when to use which. Apps pick
  whichever their imports landed on.

**Verdict:** unifying the two cap languages is the largest research
gap. Both are correct for their respective scopes (macaroons for
bearer tokens, cell-resident for in-cell graph reachability); making
one wrap the other (or making one a *projection* of the other) is a
design problem, not an implementation problem. This is why SDK-REVIEW
calls it Tier-2 / "deferred."

### 5. `cell.spawn_child_with_behavior(child_spec)`

**Pyanascript shape:**
```rust
let child = cell.spawn_child_with_behavior(ChildSpec {
    name: "subagent-1",
    behavior: |state, msg, ctx| { /* … */ },
    initial_state: ChildState::default(),
})?;
```

**Current closest (ugly):**
```rust
// Three different mechanisms today, none composed:

// (1) AgentRuntime spawns a SubAgent (off the same wallet seed):
let runtime: AgentRuntime = wallet.into_runtime("parent");
let sub: SubAgent = runtime.spawn_sub_agent(
    "child-1",
    held_token,
    /* derive_index */ 1,
)?;

// (2) pyana_cell::Cell::spawn_child for ledger-level child cells:
let parent_cell: pyana_cell::Cell = /* … */;
let child_cell = parent_cell.spawn_child(child_pk, child_token_id);

// (3) wallet.create_from_factory for descriptor-bound creation:
let turn = wallet.create_from_factory(
    agent_cell, factory_vk, owner_pubkey, token_id,
    factory_params, nonce, fee,
);
// (note: create_from_factory still emits Authorization::Unchecked —
// SDK-REVIEW C-3 sibling, see "Other Authorization::Unchecked sites"
// below.)
```

**SDK gap:**

- *Partial / fragmented.* Three different "spawn" mechanisms, no
  composed call. Which one is the right backend for
  `spawn_child_with_behavior`?
  - `SubAgent` is for **off-chain delegation** (same wallet, different
    key); the child is not a separate cell.
  - `Cell::spawn_child` is **ledger-internal**; produces a child cell
    record but does not install behaviour.
  - `create_from_factory` is **constructor-transparency**; produces a
    cell from a deployed `FactoryDescriptor` (which can carry slot
    caveats and a program VK).
- *Missing.* No single API that ties (a) the parent cell, (b) the
  child's initial state, (c) the child's behaviour into one call. The
  closest is "deploy a factory descriptor that bakes in the program
  VK, then `create_from_factory`."

**Verdict:** the right answer is almost certainly **factory
descriptors**. `spawn_child_with_behavior(ChildSpec {..})` compiles to
"deploy a `FactoryDescriptor` (if not already deployed) + emit a
`CreateCellFromFactory` effect." This is consistent with constructor
transparency. Pyanascript's job is to surface the factory pattern
cleanly; the SDK already has the primitives.

### 6. `cell.on_receive(|state, msg, caps| { ... })`

**Pyanascript shape:**
```rust
cell.on_receive(|state, msg, caps| {
    match msg {
        MsgKind::Bid { amount } => {
            state.add_bid(amount);
            Effects::emit(Event::BidPlaced { amount })
        }
        MsgKind::Cancel => Effects::none(),
    }
});
```

**Current closest:**

*Does not exist.* The SDK has no event loop. A turn is built by the
agent, submitted to the executor, executed, and a receipt is appended
to the chain. There is no point at which the SDK *receives* a message
and dispatches it to a registered handler. The closest is the *server
side* of CapTP (`pyana_captp::CapTpServer::on_pipeline_message` in
`captp/src/server.rs`), which is per-promise and per-method, not
per-cell-handler.

**SDK gap:**

- *Missing entirely.* The runtime has no concept of "a cell is the
  locus of message receipt." Apps that need this pattern today run
  their own event loop (e.g. `apps/prediction-market/src/server.rs`
  uses axum + `pyana_app_framework::*` — not the SDK).
- *Missing.* No registry mapping `CellId → Box<dyn Fn(State, Msg) -> Effects>`.
- *Missing.* No dispatch loop that drains an inbox / waits on a
  channel / polls a queue and invokes the handler.

**Verdict:** this is the **runtime gap**, not a wrapping gap. Building
it requires deciding:

1. Where does the message come from? (CapTP wire, queue dequeue,
   storage poll, local channel?)
2. Where does the handler run? (Host process, sandbox, deployed
   circuit?)
3. How is the receipt produced? (Synchronously after handler returns,
   or in a separate "settle" turn?)

These are the same decisions as gap 1 (`with_behavior`). Pyanascript
needs them resolved before `on_receive` has a concrete compilation
target. Until then, apps run their own event loops in userspace.

### 7. `let inbox = CapInbox::new(...)` (post storage-as-cell-programs)

**Pyanascript shape:**
```rust
let inbox = cell.inbox()?;
let msg = inbox.read_next().await?;
```

**Current closest (ugly):**
```rust
// CapInbox lives in pyana_storage, NOT in pyana_sdk:
let mut inbox = pyana_storage::CapInbox::new(
    QuotaId(1),
    /* capacity */ 100,
    /* min_deposit */ 50,
);
// Receive a message (synchronous, no `.await`):
inbox.receive(InboxMessage::new(sender, content), current_height, ttl)?;
let (entry, proof) = inbox.read_next()?;
```

**SDK gap:**

- *Missing from SDK.* `CapInbox` is in `pyana_storage` and not
  re-exported through `pyana_sdk`. Apps that want an inbox must
  `use pyana_storage::CapInbox` directly — same "apps step around
  the SDK" pattern as elsewhere.
- *Missing.* No bridge from a wallet/cell to "the inbox for this
  cell." Inboxes are constructed standalone (`CapInbox::new(QuotaId,
  capacity, min_deposit)`) — there is no `wallet.inbox_for(cell_id)`.
- *Missing.* `read_next` is synchronous; pyanascript's `inbox.read_next().await`
  expects an async channel. No async wrapper exists. (Tokio
  integration story: an `async fn next() -> InboxMessage` that
  blocks on a `tokio::sync::Notify` until the storage operator's
  queue advances.)
- *Missing.* No SDK method analogous to "post a message to a target
  cell's inbox" — `enqueue_message` (queue API, NOT inbox API) is the
  closest, but queue messages are content-addressed deposits, not
  typed inbox payloads.
- *Inconsistency.* "Inbox" vs "queue" vs "CapTP promise inbox" are
  three different concepts in the codebase, all reasonable on their
  own, none unified. Pyanascript will need to pick one.

**Verdict:** post storage-as-cell-programs, `CapInbox` should be a
first-class SDK primitive. Tier-1 work: re-export from SDK, add
`AgentWallet::inbox(cell_id)` returning a handle, add an async
wrapper.

### 8. `cell.declare_slot_caveat(...)` (post-slot-caveats v1)

**Pyanascript shape:**
```rust
cell.declare_slot_caveat(SlotCaveat::WriteOnce { slot: EXPIRY_SLOT });
cell.declare_slot_caveat(SlotCaveat::Monotonic { slot: HEIGHT_SLOT });
```

**Current closest (ugly):**
```rust
// Slot caveats are baked into a FactoryDescriptor at deploy time,
// not declared on a running cell. The current shape:
let descriptor = FactoryDescriptor {
    factory_vk: blake3::hash(b"my-factory").into(),
    program_vk: program_vk_hash,
    initial_balance: 0,
    field_constraints: vec![
        FieldConstraint::Equality { field_index: NAME_SLOT, value: name_hash },
        FieldConstraint::NonZero { field_index: OWNER_SLOT },
    ],
    inspector: InspectorDescriptor::None,
    creation_budget: 1000,
    child_vk_strategy: ChildVkStrategy::Inherit,
};
```

**SDK gap:**

- *Missing.* `FactoryDescriptor` is in `pyana_cell`, not surfaced as a
  builder in the SDK. The fluent
  `.declare_slot_caveat(WriteOnce { slot })` shape requires a
  *FactoryDescriptor builder* with mutator methods, which does not
  exist.
- *Missing.* `FieldConstraint::WriteOnce` is not in the current enum —
  only `Equality`, `Range`, `NonZero`. The `StateConstraint::WriteOnce`
  exists in `pyana_cell::program::StateConstraint`, but it's a
  per-CellProgram-slot perpetual constraint, not a factory-deploy-time
  constraint. **The two concepts need to be merged or clearly
  named separately**, and the SDK needs a unified surface.
- *Partial.* `apps/starbridge-apps/nameservice/src/lib.rs` shows the
  pattern hand-written for the name-cell factory; it would be the
  reference for what a fluent builder needs to produce.

**Verdict:** Tier-1 SDK work: add a `FactoryDescriptorBuilder` (in SDK
or app-framework), expose slot caveats as method calls on it, hide
the field-index encoding. The cell-level mechanism already exists;
the surface does not.

### 9. `wallet.create_from_factory(descriptor)` (already exists)

**Pyanascript shape:**
```rust
let child_cell = wallet
    .create_from_factory(descriptor)
    .with_initial_state(state)
    .submit()
    .await?;
```

**Current SDK shape (`sdk/src/wallet.rs`):**
```rust
pub fn create_from_factory(
    &self,
    issuer_cell: CellId,
    factory_vk: [u8; 32],
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    params: pyana_cell::FactoryCreationParams,
    federation_id: &[u8; 32],
) -> Turn
```

**SDK gap:**

- *Partially closed.* The `Unchecked` regression is **fixed** (this
  task): `nonce`/`fee` removed, `federation_id` added, action now
  routes through `make_action`/`make_turn` — signature is real.
  Naming: `agent_cell` renamed to `issuer_cell` to clarify it is the
  *issuer* of the effect, not the new child cell. Two adversarial
  tests added (`create_from_factory_produces_real_signature`,
  `create_from_factory_signature_binds_to_federation_id`).
- *Remaining.* The pyanascript shape still wants:
  - One argument (a builder) instead of six positional args
  - The submission step embedded (`.submit()` through an `AgentRuntime`)
  - The async return (the receipt, when settled)

**Verdict:** the `Unchecked` regression is closed. What remains is a
Tier-1 ergonomics improvement (builder + submit). See Tier-0 gap list
entry #1 below — it is now updated to reflect that the signing fix
has landed.

## Prioritized gap list (for the next pyanascript work)

Each entry: **gap** → **SDK addition** → **research depth (Tier-0
mechanical / Tier-1 small design / Tier-2 deep design)**.

### Tier-0 (mechanical, do soon, no design risk)

| # | Gap | Addition | Notes |
|---|---|---|---|
| 1 | ~~`wallet.create_from_factory` still uses `Authorization::Unchecked`~~ | ~~Use `make_action` + `make_turn`; add `federation_id` parameter; collapse 7-arg sig into a builder~~ | **CLOSED** this task: `nonce`/`fee` removed, `federation_id` added, routes through `make_action`, two adversarial tests pinning it. Remaining: builder ergonomics (Tier-1). |
| 2 | `CapInbox` not re-exported from SDK | `pub use pyana_storage::CapInbox` in `sdk/src/lib.rs` | Trivial |
| 3 | No typed-message bridge for `LiveRef::send` | SDK trait `CapMessage` + `wallet.send_typed(live_ref, msg)` | Maps Rust enum to `PipelinedAction { method, args }` |
| 4 | No "await this promise's receipt" sync convenience | `EventualRef::await_receipt(&runtime) -> Result<TurnReceipt, _>` | Mechanical given the wire-side is plumbed |
| 5 | `domain: &str` threading everywhere | `wallet.default_domain()` getter + `cell_id_default()` | SDK-REVIEW P1 #6 — overlaps with `AppWallet::domain` already in framework |

### Tier-1 (small design, do next)

| # | Gap | Addition | Notes |
|---|---|---|---|
| 6 | No `FactoryDescriptorBuilder` in the SDK | `pub struct FactoryDescriptorBuilder { … }` with `.with_slot_caveat(..)`, `.with_initial_state(..)`, `.with_creation_budget(..)`, `.deploy(&wallet) -> [u8; 32]` | Wraps `pyana_cell::FactoryDescriptor` |
| 6b | `create_from_factory` still 6-arg positional; no submit/await | Collapse into `wallet.create_from_factory(builder, params, fed) -> Turn` then `wallet.deploy_cell(builder) -> impl Future<Receipt>` | Signing now correct; ergonomics gap remains |
| 7 | `wallet.exercise(cap, args)` not single-call | `wallet.exercise_token(token, method, args) -> Result<TurnReceipt>`; same for `exercise_cap` (LiveRef) | Closes the "build + sign + execute" 3-step |
| 8 | `WriteOnce` slot constraint missing from `FieldConstraint` | Add `FieldConstraint::WriteOnce { field_index }` mirroring `StateConstraint::WriteOnce`; or document the split clearly | The two concepts apply at different layers (factory-deploy-time vs cell-program-perpetual) |
| 9 | No SDK type wrapping "this wallet's logical cell" | `pub struct AgentCell<'w> { wallet: &'w mut AgentWallet, cell_id: CellId, domain: String }` with `send`/`exercise`/`attenuate_cap`/`spawn_child` methods | The actual "Cell::new(wallet)" facade |
| 10 | `SdkError::Wire` overloaded | Split into `Wire`, `Serialization`, `Configuration` | SDK-REVIEW P1 #7 |

### Tier-2 (research-grade, deferred — needs design pass)

| # | Gap | Notes |
|---|---|---|
| 11 | `with_behavior(closure)` — closure vs deployed circuit | Decides whether pyanascript's behaviour is provable (compile to circuit) or merely executable (host actor). The single biggest open question. |
| 12 | `on_receive(handler)` — runtime event loop | Where does the message come from? Where does the handler run? How is the receipt produced? |
| 13 | Unified `Capability` type (closes SDK-REVIEW C-3) | Merge or project `HeldToken` and `CapabilityRef` so `attenuate_cap` has one signature. |
| 14 | Async path for local execution | `AgentRuntime::execute_turn` is sync. Pyanascript's `.await` semantics need a thin async wrapper (mechanical) plus a coherent "when does this resolve" story (which depends on the answer to #11/#12). |
| 15 | Typed-state encoding bridge | `with_state(rust_value)` requires Rust↔field-slot serialization. The closest reference is how `apps/nameservice` does it by hand; the SDK has no helper. |

## Honest verdict

**The bottom-up walk produces three workable Tier-0 fixes, five small
Tier-1 designs, and five deep open questions.**

The **Tier-0/Tier-1** work is a quarter of focused SDK PRs — each
mechanical, each closes one of the audit's named gaps, none requires
language commitments. After that work lands, pyanascript would
compile against an SDK that supports the actor-shaped method chain
*except for* gaps 11/12/13 (closure-as-behaviour, event loop,
unified caps).

The **Tier-2** open questions are *the* design problems for
pyanascript. They cannot be deferred indefinitely: without an answer
to #11 (closures vs circuits), there is no way to write the compiler
backend, because there is nothing to compile *to*. Without #12 (event
loop), every "cell behaviour" is a stateless one-shot, which defeats
the actor model. Without #13 (unified caps), every cap operation
needs two SDK methods.

Per `SDK-REVIEW.md` honest verdict: **the SDK has the parts, they
are not yet composed into the layer pyanascript wants to sit on.**
This audit names what that composition would look like as a Rust
method chain and identifies, primitive by primitive, the exact
seams where composition currently breaks.

Pyanascript is *not* blocked on language design — it is blocked on
**SDK composition + three research questions**. The composition work
is roughly 4-6 PRs; the research questions are roughly three
multi-week design rounds.
