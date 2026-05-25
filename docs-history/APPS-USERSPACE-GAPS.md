# Apps as Userspace — gap analysis + migration sketch

Written 2026-05-24. Companion to `SDK-REVIEW.md` and `AUDIT-protocol-composition.md` Seam 1.

## The reframe

Apps are *userspace*. They consume primitives the SDK/framework provides;
they do not reach past those layers into the kernel
(`pyana-turn::builder::ActionBuilder`, `pyana-cell::*`, `pyana-types::*`).

Two-layer composition:

```
apps/* (userspace)
   ↓ (narrow surface)
pyana-app-framework  (holds AppWallet, exposes Effect/Action/Turn re-exports)
   ↓
pyana-sdk           (holds AgentWallet, makes signed actions/turns)
   ↓
pyana-turn / pyana-cell / pyana-circuit  (kernel)
```

If an app needs something userspace can't express, the answer is *almost
never* "add a new `Effect::Foo` variant." It is one of:

1. **A missing framework method** — small, narrow, reviewable. Add it
   to `app-framework` (delegates to SDK).
2. **A missing SDK helper** — add to `AgentWallet` (Tier 0/1 list in
   `SDK-REVIEW.md`).
3. **A missing cell-program primitive** — a *caveat* on a state slot, a
   predicate the cell enforces. Documented below.
4. **Genuine pyana primitive gap** — the kernel can't express a
   property of state transitions that a class of apps need. Rare; should
   be a Stage-N design pass, not an app-side workaround.

Userspace policy ("register a name", "place an order", "cast a ballot")
should live in app code, composing `SetField` / `EmitEvent` / `Transfer`
/ `GrantCapability` primitives the kernel already understands.

---

## What landed this round (Lane: apps-userspace)

- **`pyana-app-framework::AppWallet`** — a narrow wallet handle
  wrapping `pyana_sdk::AgentWallet`. Exposes `make_action`, `sign_action`,
  `make_turn`, `cell_id`, `public_key`. Does *not* expose key export,
  receipt-chain mutation, token operations, or the 90+ other SDK
  methods. Cheap to clone (`Arc<AgentWallet>` internally).

- **`AppServer::with_wallet(wallet)`** — installs the wallet as an
  axum `Extension<AppWallet>`. Handlers extract it via
  `axum::Extension<AppWallet>` and build signed actions through it.

- **Framework re-exports** — `Action`, `Authorization`, `Effect`,
  `Event`, `symbol`, `Turn`, `CellId`, `FieldElement`. Apps no longer
  need `pyana-turn`, `pyana-cell`, `pyana-types` in their `Cargo.toml`
  for primitive-construction; they import from
  `pyana_app_framework::*`.

- **`apps/nameservice` migrated** — `effects.rs` no longer constructs
  `ActionBuilder::new(...).signed_by([0u8; 64])`. It calls
  `wallet.make_action(registry_cell, "register_name", effects)`. The
  produced `Authorization` is a real `Authorization::Signature(..)`
  with non-zero bytes. The placeholder-signature regression vector is
  closed in this app.

---

## Migration sketch for the other apps

All five remaining apps follow the same pattern:

1. Add `let wallet = AppWallet::new(AgentWallet::from_..., federation_id);`
   to the app's `main.rs`.
2. Add `wallet: AppWallet` to the app's shared state struct.
3. Add `.with_wallet(wallet)` to the `AppServer` builder chain.
4. In each handler, replace direct `pyana_turn::action::Effect::*`
   struct-literal construction with framework re-exports + signed
   actions via `state.wallet.make_action(...)`.
5. Delete the `[0u8; 64]` / `placeholder_sig` lines and any
   `Authorization::Unchecked` literals in app code.
6. Drop `pyana-turn`, `pyana-cell`, `pyana-types` from `Cargo.toml` if
   the framework re-exports cover all uses.

Per-app specifics:

### `apps/orderbook`

**Today:**
```rust
// apps/orderbook/src/escrow.rs:19-21, 120-150
use pyana_turn::action::Effect;
use pyana_turn::escrow::EscrowCondition;
use pyana_types::CellId;

pub fn build_order_escrow_effect(...) -> Effect {
    Effect::CreateEscrow {
        cell: registry_cell,
        recipient: trader,
        amount: locked,
        condition: EscrowCondition::ProofPresented { verification_key: vk },
        timeout_height: current_height + ESCROW_TIMEOUT_BLOCKS,
        escrow_id: derive_escrow_id(...),
    }
}
```

**Migration:**
```rust
use pyana_app_framework::{AppWallet, CellId, Effect};
use pyana_turn::escrow::EscrowCondition; // (a) re-export EscrowCondition from framework

pub fn build_order_escrow_action(
    wallet: &AppWallet,
    registry_cell: CellId,
    trader: CellId,
    locked: u64,
    vk: VerificationKey,
    current_height: u64,
) -> Action {
    let escrow_id = derive_escrow_id(...);
    let effect = Effect::CreateEscrow {
        cell: registry_cell,
        recipient: trader,
        amount: locked,
        condition: EscrowCondition::ProofPresented { verification_key: vk },
        timeout_height: current_height + ESCROW_TIMEOUT_BLOCKS,
        escrow_id,
    };
    wallet.make_action(registry_cell, "create_order_escrow", vec![effect])
}
```

**Userspace primitive gap (low):** `EscrowCondition` is currently in
`pyana-turn::escrow`. Framework should re-export it. Should
escrow-creation get a builder helper on `AppWallet`? Probably yes —
five required fields with one good default (timeout = height + 1000).
Tier-1 SDK helper per `SDK-REVIEW.md`.

### `apps/prediction-market`

**Today:** `apps/prediction-market/src/server.rs` doesn't touch
`pyana-sdk` at all; effects flow through `pyana_app_framework::ring_trade`
and `pyana_storage::blinded::BlindedQueue`. No direct
`ActionBuilder`, but also no signed actions emitted — the app sits
entirely off-ledger today.

**Migration:** when the on-chain side lands ("bet placement" as an
Action), it follows the nameservice pattern exactly. No special primitives needed beyond `SetField`/`EmitEvent`/`Transfer`.

### `apps/gallery`

**Today:** the heaviest case. `apps/gallery/src/settlement.rs:17-20`
imports `Action, Authorization, CommitmentMode, DelegationMode, Effect,
symbol`, `ActionBuilder`, `CallForest, CallTree`, `Turn` *all directly
from pyana_turn*. Lines 1325-1380 construct a `Turn { ... }` struct
literal carrying `Effect::RefundEscrow`. Allowlisted in
`scripts/no-unchecked-auth.sh` as a known-bad migration baseline.

**Migration steps:**
1. Add `state.wallet: AppWallet` to gallery's app state.
2. Replace each `Effect::CreateEscrow { ... }` / `Effect::RefundEscrow { ... }`
   struct literal with a framework-re-exported `Effect::*` *outside* a
   manually-built `Turn`.
3. For each `Turn { ... }` literal, replace with
   `state.wallet.make_turn(state.wallet.make_action(target, method, effects))`.
4. Remove the `Authorization::Unchecked` literals; remove from the
   `no-unchecked-auth.sh` allowlist.

**Userspace primitive gap (none).** Settlement is a sequence of
escrow-effects; the kernel primitives cover it.

### `apps/escrow` (or escrow-using apps)

**Today:** the `escrow` test scaffolding lives in `app-framework/src/escrow.rs`
(production helpers wrapping `PyanaEngine` escrow creation/release).
Production apps call into it; no migration of the framework module
itself needed except to gain a `wallet: &AppWallet` parameter to
optionally sign rather than going through `Authorizer::*`.

**Migration:** framework helpers in `app-framework/src/escrow.rs`
accept either an `Authorizer` (current) or an `AppWallet` (new).
Mechanical addition; no app-level changes once the framework offers
both.

### `apps/privacy-voting`

**Today:** `apps/privacy-voting/src/effects.rs:21-24` mirrors the
nameservice pattern: `ActionBuilder::new(...).signed_by([0u8; 64])
.effect_emit_event(...).effect_set_field(...)`. This is the simplest
migration — copy the nameservice diff verbatim.

**Migration:**
```rust
use pyana_app_framework::{Action, AppWallet, CellId, Effect, Event};

pub fn build_ballot_submit_action(
    wallet: &AppWallet,
    ballot_cell: CellId,
    proposal_id: [u8; 32],
    commitment: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::EmitEvent {
            cell: ballot_cell,
            event: Event::new(
                pyana_app_framework::symbol("ballot-submitted"),
                vec![proposal_id, commitment],
            ),
        },
        Effect::SetField {
            cell: ballot_cell,
            index: BALLOT_STORAGE_SLOT,
            value: commitment,
        },
    ];
    wallet.make_action(ballot_cell, "submit_ballot", effects)
}
```

**Userspace primitive gap (medium):** cast-commitment *uniqueness*
("commitment X has not been submitted previously by this voter") needs
a cell-program caveat — see the cell-side gap below.

---

## Identified userspace-gap primitives

These are *missing primitives* — places where userspace policy cannot
be expressed in terms of the current kernel surface. Each is a Stage-N
candidate, not a justification for ad-hoc `Effect::Foo` variants.

### Gap 1 — Cell-program caveat: "this slot may only be set if its prior value is zero"

**Symptom:** the nameservice wants to enforce that
`SetField(NAME_STORAGE_SLOT, name_hash)` *fails if the slot is already
non-zero*. Today the only way to do this from userspace is to read the
slot, check it in the app, and emit the action — racy. The kernel
primitive that would close this is a **cell program caveat**: a
predicate the cell's `CellProgram` enforces on the *new* value before
accepting the `SetField` effect.

**Current state:** `pyana_cell::Cell::with_program(CellProgram)` exists,
but `CellProgram` is a STARK verification key — it expresses a
predicate the action's proof must satisfy *globally*, not a per-slot
write-once invariant.

**Proposed primitive (Tier-2 cell extension):**
```rust
pub enum SlotCaveat {
    WriteOnce,  // slot may only be set if prior value is zero
    Monotonic,  // slot's value may only increase
    BoundedBy(usize), // slot may only be set if slot[other_index] != 0
    Any,        // no caveat (default)
}
pub struct CellSchema {
    pub caveats: BTreeMap<usize, SlotCaveat>,
}
```

`SetField` checks the caveat at apply time; violations reject the
effect (not the action — soft fail with a journal entry).

**Affected apps:** nameservice (write-once for name slots),
privacy-voting (write-once for ballot-commitment slots), gallery
(monotonic for artwork-id counter), orderbook (write-once for order-id
slots).

**Why this and not `Effect::RegisterName`:** the caveat is a property
of *the cell's storage schema*, not of *the action that touched it*.
Apps can compose `SetField` + caveat to express many invariants;
adding a dedicated `Effect::RegisterName` would couple the kernel to a
specific app domain.

### Gap 2 — Multi-effect transactional uniqueness ("see-then-set")

**Symptom:** apps want "if slot X is empty, set X *and* emit event Y
atomically." Today this is possible because effects within an action
are atomic, but the **read part** (verify X is empty) cannot be
expressed as an effect — the executor reads-then-writes, but
userspace has no way to assert the read precondition was satisfied.

**Current workaround:** `Action::preconditions` (currently underused;
default empty). Could carry "slot X is zero" assertions.

**Affected apps:** all of the above.

**Proposed primitive (Tier-1 turn extension):**
```rust
pub enum Precondition {
    SlotEquals { cell: CellId, index: usize, value: FieldElement },
    SlotNonZero { cell: CellId, index: usize },
    SlotZero { cell: CellId, index: usize },
    NonceAtLeast(u64),
}
```

Executor checks each precondition before applying any effects; failure
rejects the *action* (not the turn — surrounding actions continue).

### Gap 3 — Wallet-bound effect targeting

**Symptom:** `wallet.make_action(target, method, effects)` requires
the *caller* to specify a target `CellId`. For app-internal actions
(transferring between the app's own cells), the target is the
wallet's own cell — but the caller has to compute that with
`wallet.cell_id()`. Mechanically fine; ergonomically a small papercut.

**Proposed primitive (Tier-0 framework method):**
```rust
impl AppWallet {
    pub fn make_self_action(&self, method: &str, effects: Vec<Effect>) -> Action {
        self.make_action(self.cell_id(), method, effects)
    }
}
```

Trivial; add when a second app needs it.

### Gap 4 — Receipt-chain visibility for off-chain reads

**Symptom:** the nameservice handler emits a signed action but **drops
it on the floor** (today: `let _registration_action = ...;`) because
there is no executor in-process to apply it. The action is constructed
to prove the *path compiles*, but the federation HTTP routing layer
that would consume and replay these actions is downstream of this
lane.

**Current workaround:** apps either run their own embedded executor
(via `pyana_sdk::PyanaEngine`) or POST to a federation node. Neither
is currently wired through `AppServer`.

**Proposed primitive (Tier-1 framework method):**
```rust
impl AppServer {
    /// Install an embedded executor and ledger so handlers can submit
    /// actions through `wallet.submit(action)` and observe receipts.
    pub fn with_embedded_executor(self, engine: PyanaEngine) -> Self;
}
```

Or, alternatively, a "federation client" extension that POSTs the
signed action to a configured node URL.

**Affected apps:** all six. Today every app's on-ledger actions are
either (a) built and dropped (nameservice, privacy-voting) or (b)
sent via the app's own hand-rolled HTTP client (gallery, orderbook).

### Gap 5 — Cross-action consistency without a turn-level builder

**Symptom:** orderbook settlement needs to release one escrow *and*
create a counterparty escrow *in the same turn* so neither lands
without the other. Today the app has to build a `Turn { call_forest:
CallForest { roots: vec![tree1, tree2], ... }, ... }` literal
because `wallet.make_turn` only takes one action.

**Proposed primitive (Tier-0 framework method):**
```rust
impl AppWallet {
    /// Wrap N signed actions in one Turn (atomic group).
    pub fn make_turn_with_actions(&self, actions: Vec<Action>) -> Turn;
}
```

Trivial; add when orderbook or gallery migration starts.

---

## Anti-patterns the framework deliberately rejects

- **`Effect::RegisterName`, `Effect::CastBallot`, `Effect::PlaceOrder`,
  etc.** App-specific Effect variants couple the kernel to a userspace
  domain. The right answer is `SetField` + `EmitEvent` + caveat (Gap 1).
- **`Authorization::Unchecked` in app code.** Already forbidden by
  `scripts/no-unchecked-auth.sh`. Apps that need an "unauthorized"
  action are expressing a wire-layer concern (CapTP routing), which
  belongs in `wire/`.
- **`signed_by([0u8; 64])`.** The placeholder pattern is exactly what
  this lane retired. Closed in nameservice; the migration sketch above
  closes it in the remaining apps.
- **Reaching into `pyana_turn::builder::ActionBuilder` from app code.**
  Apps should call `wallet.make_action(...)`. If the builder's
  typestate offers a feature the framework method doesn't, that's a
  framework gap — add the missing method.

---

## What the framework still needs

Ranked by "what's the next migration blocked on":

1. **Re-export `pyana_turn::escrow::EscrowCondition` and `EscrowRecord`
   from the framework.** Unblocks orderbook + gallery.
2. **Add `AppWallet::make_turn_with_actions(Vec<Action>) -> Turn`.**
   Unblocks orderbook settlement.
3. **Add `Precondition` variants to `Action` and route them through
   the executor.** Closes the "see-then-set" gap for all apps.
4. **Design pass on `SlotCaveat` / `CellSchema`.** Closes the
   write-once / monotonicity gaps without leaking into the Effect enum.
5. **`AppServer::with_embedded_executor`** so apps can actually submit
   their signed actions to a ledger and observe receipts.

The Effect enum stays closed. Apps stay in userspace.
