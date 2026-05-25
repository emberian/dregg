# SDK Review — `pyana-sdk` audit toward the pyanascript bottom-up surface

Written 2026-05-24 against `sdk/src/` HEAD. Scope: identify the API gap
between `pyana-sdk` as it stands today and the hypothetical method-chain
runtime API that `pyanascript` (the design in `pyanascript/`) would
compile to. See `THOUGHTS-AND-DREAMS.md` §6 (two-language model), §Q5
(bottom-up discipline), and `pyanascript/README.md` §Q1 (the method-chain
shape).

This is a design audit followed by a small bounded improvement pass.
The audit does the most useful thing — names the gap precisely — so
that further work (Phase 3+, beyond this review) can be scheduled
honestly. No `Cell::send` / `Cell::on_receive` primitives are
introduced here; those need a design pass beyond what this round can
absorb.

## Crate shape at a glance

`sdk/src/` (~17k lines across 16 files):

| File | LoC | Role |
|---|---|---|
| `cipherclerk.rs` | 7149 | `AgentCipherclerk` — identity, tokens, receipt chain, sovereign cells, queues, sealed dispatch onto `pyana_turn`/`pyana_cell`/`pyana_captp` |
| `captp_client.rs` | 1000 | `CapTpClient`, `LiveRef`, `EventualRef` — three-vat reference plumbing |
| `names.rs` | 1120 | `PetnameDb`, `NameResolver` — local petname mapping |
| `committed_turn.rs` | 665 | `CommittedTurnBuilder` — Pedersen-commitment transfers |
| `embed.rs` | 956 | `PyanaEngine`, `WireCodec` — no-IO embed layer for hosts |
| `privacy.rs` | 979 | Anonymous presentation / non-revocation / nullifier-set proofs |
| `verify.rs` | 936 | Standalone verifier entry points |
| `full_turn_proof.rs` | 833 | Composed full-turn proof types |
| `runtime.rs` | 662 | `AgentRuntime`, `SubAgent` — cclerk + local ledger orchestration |
| `client.rs` | 588 | `SiloClient` — HTTP client to a node |
| `discovery.rs` | 565 | Federation discovery |
| `mnemonic.rs` / `wordlist.rs` | 631 | BIP-39 derivation |
| `discharge.rs` | 316 | Third-party caveat discharge gateway |
| `error.rs` | 88 | `SdkError` — variant union |
| `lib.rs` | 171 | re-exports |

Two structural observations up front:

1. **`AgentCipherclerk` is 107 `pub` methods on one type**, spread across
   ~7150 lines. It is the *de facto* runtime surface — apps that don't
   reach past the SDK reach into `AgentCipherclerk`. Anything pyanascript
   compiles to lives here (or has to be put here).
2. **Apps mostly bypass the SDK.** Surveyed `apps/nameservice/src/`,
   `apps/orderbook/src/`, `apps/prediction-market/src/`: zero
   `use pyana_sdk` lines. They import `pyana_turn::action::{Effect,
   Action, Authorization}`, `pyana_turn::builder::ActionBuilder`,
   `pyana_cell::CellId`, `pyana_types::CellId`. The SDK is being
   stepped *around*, not *through*. This is the canonical signal that
   the SDK isn't currently expressing what apps want to express.

## `AgentCipherclerk` API surface inventory (categorized)

Categories follow the natural seams between concerns. Method names are
exact; types abbreviated.

**Identity / key material (12 methods)**
- `new()`, `from_key_bytes(secret)`, `from_mnemonic(s, p)`, `from_seed(seed)`
- `derive_sub_agent(index)`, `derivation_path()`
- `export_mnemonic(&mut)`, `export_seed(&mut)`
- `public_key()`, `cell_id(domain)`, `gossip_signing_key()`,
  `derive_symmetric_key(ctx)`

**Token holding / minting / attenuation (10 methods)**
- `mint_token(root_key, service)`, `tokens()`, `find_token(label)`,
  `find_token_by_id(id)`
- `attenuate(token, restrictions)`, `verify_token(token, request)`
- `delegate(token, to, restrictions)`, `delegate_with_parent(...)`,
  `delegate_with_tree(...)`, `delegate_with_tree_and_parent(...)`
- `receive_signed_delegation(...)`, `receive_local_delegation(...)`

**Receipt chain / IVC (8 methods)**
- `append_receipt(r)`, `receipt_head()`, `receipt_chain_length()`,
  `receipt_chain()`, `current_state_commitment()`, `verify_own_chain()`
- `enable_ivc(initial_root)`, `export_state_proof()`, `ivc_enabled()`

**Authorization proof generation (12 methods)**
- `authorize(token, request, mode)`,
  `authorize_with_disclosure(token, request, spec)`
- `prove_authorization(...)`, `prove_authorization_with_issuer_key(...)`,
  `prove_fast(...)`, `prove_with_chain(...)`
- `prove_predicate(...)`, `prove_arithmetic(...)`,
  `prove_relational(...)`, `prove_committed_threshold(...)`
- `prove_program(...)`, `prove_program_full(...)`,
  `prove_for_intent_predicates(...)`

**Turn construction (8 methods)**
- `sign_turn(turn)`, `sign_bytes(message)`
- `build_authorized_turn(token, target, effects, action, resource, fee)`
- `build_committed_transfer(notes, recipients, domain, nonce)`
- `allocate_queue(capacity, program_vk)`, `enqueue_message(...)`,
  `dequeue_message(queue)`, `atomic_queue_tx(operations)`
- `eventual_ref(turn, slot)` (associated fn)

**Pipelined / intent fulfillment (2 methods)**
- `submit_pipeline(pipeline, executor, ledger)`,
  `fulfill_and_collect(...)`

**Stealth / committed payments (4 methods)**
- `stealth_meta_address()`, `generate_stealth_address_for(...)`,
  `scan_notes(...)`, `private_transfer(...)`

**Sovereign cells (10 methods)**
- `make_sovereign(cell_id)`, `execute_sovereign_turn(...)`,
  `execute_sovereign_turn_with_proof(...)`
- `convert_effects_to_vm(effects)`, `apply_sovereign_effects(...)`,
  `store_sovereign_state(cell)`, `sovereign_state(cell_id)`
- `export_sovereign_state()`, `import_sovereign_state(data)`,
  `sovereign_cell_count()`
- `compress_sovereign_history(cell_id)`,
  `verify_compressed_history(...)`

**Peer exchange / factories / programs / intent (9 methods)**
- `peer_exchange_session(domain)`, `peer_exchange(domain)`,
  `send_peer_transition(...)`
- `deploy_factory(descriptor)`, `create_from_factory(...)`,
  `verify_provenance(...)`
- `deploy_program(node_url, ...)` (async, HTTP),
  `execute_with_program(...)`
- `post_encrypted_intent(...)`

**Federation (2 methods)**
- `register_with_federation(node_url, ...)` (async, HTTP),
  `deregister_from_federation(node_url)` (async, HTTP)

**CapTP (5 methods)**
- `set_captp_client(client)`, `captp_client()`, `captp_client_mut()`
- `share_capability(cell_id)`, `accept_capability(uri)`,
  `delegate_offline(cell_id, recipient_pk)`

107 pub methods on a single type. Verdict: not bad given the surface
this layer is asked to cover; bad as a *programming model* for
pyanascript to compile to. The grouping above is already the latent
shape of the SDK we want.

## Mapping to pyanascript's hypothetical `Cell::*` API

`pyanascript/README.md` §Q1 names the shape:

```rust
let cell = Cell::new(cclerk)
    .with_state(MyState::default())
    .with_behavior(handler);
cell.send(target_cap, MsgKind::Bid { amount: 100 })?;
let response = cell.exercise(cap, args).await?;
let attenuated = cell.attenuate_cap(cap, narrower)?;
cell.spawn_child_with_behavior(child_spec)?;
cell.on_receive(|state, msg, caps| { ... });
```

| pyanascript primitive | Today in `pyana-sdk` | Verdict |
|---|---|---|
| `Cell::new(cclerk)` | `cclerk.cell_id(domain)` + `pyana_cell::Cell::new_hosted(...)` separately | **partial.** Two-step, you build `CellId` from the cclerk and then `Cell` from `pyana_cell` directly. No SDK type that owns "this cipherclerk's logical cell". |
| `.with_state(s)` | `pyana_cell::Cell::with_balance/with_program/...` builder exists, but is on the *cell* type, not on a cclerk-bound handle | **partial.** Exists structurally on `Cell`, missing on the SDK handle. |
| `.with_behavior(handler)` | `deploy_program` (async, HTTP) lands a `CircuitDescriptor` against the federation; `execute_with_program` reuses it. There is no in-process handler concept. | **missing.** Behavior is "a deployed STARK program," not "a closure." Mapping closures onto programs is non-trivial — likely a CapTP-resolver pattern. |
| `cell.send(target_cap, msg)` | `LiveRef::send(action) -> EventualRef` exists on `captp_client::LiveRef`, but the `_action` parameter is *literally ignored* by the current implementation (returns a fresh promise without enqueuing). | **stub-shaped.** The shape is right, the implementation is a TODO. |
| `cell.exercise(cap, args).await` | `cclerk.fulfill_and_collect(...)` for intent fulfillment; no direct `exercise` on a capability ref | **missing.** There is no single-call "exercise this cap with these args, await the receipt" primitive. |
| `cell.attenuate_cap(cap, narrower)` | `cclerk.attenuate(token, restrictions)` (macaroon caps), `pyana_cell::AttenuatedCap`, `is_attenuation(...)` (cell caps) | **partial / fragmented.** Two parallel "cap" notions live side by side: macaroon-backed tokens vs `CapabilityRef`/`AttenuatedCap` from `pyana-cell`. No unified attenuation surface. |
| `cell.spawn_child_with_behavior(spec)` | `cclerk.create_from_factory(...)`, `Cell::spawn_child(...)` on the cell type, `cclerk.deploy_program(...)` for behavior | **partial.** Three different mechanisms; no composed spawn-with-behavior call. |
| `cell.on_receive(handler)` | nothing — there is no concept of a "handler the SDK runs when a message arrives" | **missing entirely.** The runtime today is one-shot: build turn, execute turn, append receipt. There is no event loop. |

## App-side pain points (real signals from real code)

### `apps/nameservice/src/effects.rs`

Goes straight to `pyana_turn::builder::ActionBuilder::new(...).signed_by([0u8; 64]).effect_emit_event(...).effect_set_field(...).build()`. Pain:
- `signed_by(placeholder_sig)` — the app *literally encodes a zero
  signature* and leaves a TODO because **the SDK has no
  "build-this-action-and-sign-it-with-my-cclerk" call.** `build_authorized_turn` exists but presumes a `HeldToken`. There is no equivalent "self-signed action" helper that fills `Authorization::Signature(sig)` with the cipherclerk's own key.
- The module-level note explicitly defers to "when the federation HTTP service gains a cclerk integration." That integration is *the SDK*. The SDK has no `cclerk.sign_action(action)` helper.

### `apps/orderbook/src/escrow.rs`

Builds `Effect::CreateEscrow {...}` and `Effect::RefundEscrow {...}` directly. Pain:
- Constructs `Effect` enum variants by struct literal. No builder for `CreateEscrow` despite five required fields (`cell`, `recipient`, `amount`, `condition`, `timeout_height`, `escrow_id`) and known good defaults (timeout = current + 1000).
- `EscrowCondition::ProofPresented { verification_key }` requires the
  caller to compute their own VK derivation. No helper.

### `apps/prediction-market/src/server.rs`

Server logic talks to `pyana_app_framework::*` and `pyana_storage::*` directly. Doesn't touch `pyana-sdk` at all. The framework crate has accumulated the "real app authoring layer" the SDK aspired to be. The SDK is currently relevant only to the *client-of-an-app* path (cclerk, signing, presentation), not the *authoring-an-app* path.

## Confusion / inconsistency findings

These are low-stakes but cumulatively expensive.

**C-1. Queue methods build Turns by struct-literal with `Authorization::Unchecked`.**
`allocate_queue`, `enqueue_message`, `dequeue_message`, `atomic_queue_tx` each contain ~50 lines of identical Turn-construction boilerplate ending in `authorization: Authorization::Unchecked`. This is exactly the regression Stage 8 P2.E-H is trying to grep out of the codebase. The SDK is currently shipping four `Unchecked` authorizations and four copies of the same skeleton. *Fix:* one private `build_self_signed_turn(action) -> Turn` and one `make_self_signed_action(target, method, effects) -> Action` helper; queue methods become 3-5 lines each.

**C-2. `LiveRef::send(action) -> EventualRef` discards its argument.**
`captp_client.rs:136` literally has `pub fn send(&self, _action: PipelinedAction) -> EventualRef` and creates an unrelated promise. `pipeline()` (next method) is defined as "the same as send() but signals intent to chain" — it also calls `send` with the same dropped argument. This is a footgun: tests pass because the return type is a fresh promise; in production no message is delivered. Should be either implemented or renamed `create_promise_for(_)` with an explicit `#[doc(hidden)] // stub`.

**C-3. Two parallel "cap" languages.**
- `HeldToken` / `MacaroonToken` / `Attenuation` (macaroon-backed bearer caps; cclerk methods: `mint_token`, `attenuate`, `delegate`)
- `CapabilityRef` / `AttenuatedCap` / `AuthRequired` (cell-resident caps; live in `pyana_cell::capability`)

Both are reachable through the SDK. Neither documents how to convert one to the other (or whether to). The pyanascript `cell.attenuate_cap` API can't be implemented without first deciding which one is the canonical "capability."

**C-4. `share_capability` / `accept_capability` / `delegate_offline` all start with the same five lines** — `let client = self.captp_client.as_mut().ok_or_else(|| SdkError::Wire("CapTP client not configured; call set_captp_client() first".into()))?;`. The `SdkError::Wire` variant is wrong — this is a configuration error, not a wire error. There should be a `SdkError::CapTpNotConfigured` variant, and probably a private `fn captp(&mut self) -> Result<&mut CapTpClient, SdkError>` helper.

**C-5. `SdkError::Wire(String)` is the catchall for non-wire failures.** Used in `share_capability` ("CapTP client not configured"), in `deploy_program` ("failed to serialize descriptor"), in HTTP response parsing ("missing vk_hash"), in federation registration. Two distinct error shapes are flattened into one. *Fix:* either rename `Wire → Misc` honestly, or split out `Configuration(String)` and `Serialization(String)` variants.

**C-6. `submit_pipeline` returns `Vec<Result<TurnReceipt, PipelineError>>` — not `Result<Vec<TurnReceipt>, _>` or `Vec<(idx, Result)>`.** The caller can't tell from the result which inputs failed without zipping with the original pipeline. *Fix:* return a struct `PipelineResults { receipts: Vec<TurnReceipt>, failures: Vec<(usize, PipelineError)> }`.

**C-7. `eventual_ref` is an associated `fn`, not a method.** Stylistically odd — why is it on `AgentCipherclerk`? It uses none of the cipherclerk's state. *Fix:* move to a free fn at module scope, or to `pyana_turn::EventualRef::for_slot(turn, slot)`.

**C-8. `domain: &str` is threaded through `cell_id(domain)`, `peer_exchange(domain)`, `peer_exchange_session(domain)`, `private_transfer(..., domain, ...)`, `build_committed_transfer(..., domain, ...)`.** A cclerk does not have a single "current domain" — every call has to know the string. *Default-domain convenience layer missing.* Internally `cell_id("default")` is the magic string used in `allocate_queue` et al. *Fix:* add `cclerk.default_domain()` getter and `cclerk.set_default_domain(s)`, then provide `cell_id_default()` and overloads that don't ask for a domain.

## Missing primitives (with proposed signatures)

### Tier 0 — true one-line wrappers (do now)

```rust
/// Sign an Action by replacing its Authorization with a real Signature
/// over the canonical signing-message bytes.
pub fn sign_action(&self, action: Action) -> Action;

/// Build a self-signed single-effect Action targeting one cell.
/// (Wraps the "method, target, effect, sign" boilerplate.)
pub fn make_action(&self, target: CellId, method: &str, effects: Vec<Effect>) -> Action;

/// Build a self-signed single-action Turn ready for submission.
/// (Subsumes the queue-method skeleton.)
pub fn make_turn(&self, action: Action) -> Turn;

/// Cipherclerk default domain, for the "cell_id(domain)" convenience layer.
pub fn default_domain(&self) -> &str;
pub fn set_default_domain(&mut self, domain: impl Into<String>);
pub fn cell_id_default(&self) -> CellId; // == cell_id(default_domain())
```

### Tier 1 — small additions

```rust
/// Build a CreateEscrow effect with named parameters and sensible defaults.
pub fn build_create_escrow(
    &self,
    recipient: CellId,
    amount: u64,
    condition: EscrowCondition,
    timeout_height: Option<u64>, // default: current_height + 1000
) -> (Effect, EscrowReceipt /* tracker */);

/// Verify the receipt chain *would* extend cleanly with a candidate
/// receipt before appending. (Today: append-or-error; no dry-run.)
pub fn would_extend_chain(&self, candidate: &TurnReceipt) -> Result<(), VerifyError>;
```

### Tier 2 — research-grade (deferred)

These are the ones the audit identifies as gaps but that **shouldn't be implemented in Phase 2** of this round — they need a design pass beyond what an audit can provide:

- `Cell::new(cclerk).with_state(...).with_behavior(...)` — needs the
  closure-vs-deployed-program decision and the in-process actor loop.
- `cell.send(target_cap, msg)` — needs the CapTP wire-actually-sends
  story, not the current stubbed `send`.
- `cell.on_receive(handler)` — needs an event loop and a notion of "a
  cell is the locus of message receipt" the SDK does not currently
  have.
- Unified capability surface (closes C-3): a single `Capability` type
  that subsumes `HeldToken` and `CapabilityRef`, with one
  `attenuate(narrower)` method.

## Prioritized improvement list

**P0 — land in Phase 2 of this review (low friction, no design risk):**
1. Add `cclerk.sign_action(action)` and `cclerk.make_action(target, method, effects)` (Tier 0).
2. Add `cclerk.make_turn(action)` — the Turn skeleton helper.
3. Refactor `allocate_queue`, `enqueue_message`, `dequeue_message`, `atomic_queue_tx` to use `make_turn` + a real `Authorization::Signature(...)` instead of `Authorization::Unchecked`. (This also closes one of Stage 8 P2.E-H's grep targets in the SDK.)
4. Add `SdkError::CapTpNotConfigured` variant; refactor the three CapTP cclerk methods to use it via a private `captp_mut()` helper.
5. Fix `LiveRef::send` to either actually enqueue the action or be renamed with a doc-hidden stub annotation, **whichever is non-disruptive** — if `send` is actually called by production paths we leave it and just doc it.

**P1 — small follow-up (defer to next round):**
6. `default_domain()` + `set_default_domain()` + `cell_id_default()`.
7. Split `SdkError::Wire` into `Wire`, `Configuration`, `Serialization`.
8. Restructure `submit_pipeline` return type for cleaner caller-side dispatch.
9. Move `eventual_ref` off `AgentCipherclerk`.

**P2 — research:**
10. Design pass on the unified `Capability` type (closes C-3).
11. Design pass on `Cell::send` / `Cell::on_receive` semantics (this is the pyanascript runtime, not a small fix).
12. Macro-layer prototype that wraps the Tier-0 helpers into `cell.send(cap, msg)`-shaped chains, validates on a re-implemented nameservice, *then* informs the pyanascript grammar.

## Honest verdict

**Yes-with-named-gaps.** The SDK is structurally well-positioned: 107
methods on `AgentCipherclerk` cover the right concerns (identity, tokens,
receipt chain, sovereign cells, queues, CapTP), and the categories
align with what pyanascript will want to compile to. But:

- The `Cell::*` shape pyanascript proposes does not exist as a type. Constructing it on top of `AgentCipherclerk` is a design exercise, not a wrapping exercise.
- Two parallel capability languages must be unified before `attenuate_cap` can have one signature.
- The CapTP send path is currently stubbed; production cell-to-cell messaging through the SDK is not yet there.
- Apps reach past the SDK into `pyana_turn` and `pyana_cell` because the SDK doesn't currently express what they want to express. This is the most diagnostic signal: the SDK should be the path of least resistance and is not.

None of this is a "rewrite the SDK" verdict. It is a "the SDK has the
parts, they are not yet composed into the layer pyanascript wants to
sit on" verdict. Phase 2 of this review lands four targeted helpers
that close some of the highest-friction gaps. The rest is honest
design work the audit could not preempt.
