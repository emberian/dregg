# AUDIT — protocol composition (cross-layer seams)

Written 2026-05-24 against HEAD plus the working-tree additions
(`wire/src/hardening.rs`, `intent/src/trustless.rs`). Scope: the *seams*
between pyana's protocol layers — not the layers themselves. Other
audits cover each crate; this one audits whether, when control crosses
a layer boundary, the contract is clear and the data carries what the
next layer needs.

The animating question is whether the layers compose. The honest
answer turns out to be: "the seams are present and roughly right at
the *type* level, but several of them are stubbed or partial at the
*invariant* level, and one of them (multi-cell binding) is structurally
incomplete by design pending Stage 7-γ.2." Verdict and ranked harden
list at the end.

Layer stack (top down):

```
apps/* (nameservice, privacy-voting, escrow, orderbook,
        prediction-market, gallery, ...)
   │
   ├── pyana-sdk (AgentWallet, CapTpClient)
   │       │
   │       ├── pyana-turn (Turn, Effect, TurnExecutor, ActionBuilder,
   │       │              TurnReceipt, WitnessedReceipt, EventualRef)
   │       │       │
   │       │       ├── pyana-cell (Cell, CellProgram, CapabilityRef)
   │       │       │
   │       │       ├── pyana-captp (sturdy refs, handoff certs,
   │       │       │                 PipelineRegistry)
   │       │       │
   │       │       └── pyana-circuit (Effect VM AIR, STARK prover,
   │       │                          Kimchi backend)
   │       │
   │       └── pyana-federation (BLS threshold sigs, AttestedRoot,
   │                              FederationReceipt)
   │
   └── pyana-blocklace (BFT consensus over `Payload::Turn(Vec<u8>)`)

pyana-wire (CapTP wire over QUIC/TLS, with new `hardening.rs`)
```

---

## Seam 1 — App → SDK

**What the seam should be:** apps call into `pyana-sdk` for the
identity / sign / build-turn / submit / receive-receipt flow. Apps
should not need to know about `pyana_turn::action::Effect` literals or
`ActionBuilder` typestate at all; they should think in terms of
"capabilities + intents."

**What it actually is:** apps reach *past* the SDK directly into
`pyana_turn` and `pyana_cell`. Surveyed all six in-scope apps; counted
the import lines that bypass `pyana_sdk` and call lower layers
directly. The pattern is consistent.

### Concrete sites

- `apps/nameservice/src/effects.rs:25-28` —
  ```rust
  use pyana_cell::state::FieldElement;
  use pyana_cell::CellId;
  use pyana_turn::action::Action;
  use pyana_turn::builder::ActionBuilder;
  ```
  `build_register_action` calls `ActionBuilder::new(...).signed_by([0u8; 64]).effect_emit_event(...).effect_set_field(...).build()`
  (`apps/nameservice/src/effects.rs:58-66`). The `signed_by` argument is
  a zero-byte placeholder (line 56): the action shape demands a 64-byte
  signature, but the app does not have a wallet handle to actually
  sign with. The module-level note (lines 19-23) defers to "when the
  federation HTTP service gains a wallet integration." That integration
  *is* the SDK.

- `apps/privacy-voting/src/effects.rs:21-24` — identical pattern.
  `build_ballot_submit_action` and `build_ballot_reveal_action`
  (lines 31-72) construct actions through `ActionBuilder` with
  `placeholder_sig = [0u8; 64]`. Same root cause.

- `apps/orderbook/src/escrow.rs:19-21` —
  ```rust
  use pyana_turn::action::Effect;
  use pyana_turn::escrow::EscrowCondition;
  use pyana_types::CellId;
  ```
  `build_order_escrow_effect` (line 120) constructs an
  `Effect::CreateEscrow {...}` struct literal with six explicit fields.
  There is no SDK helper for "build a collateral-escrow effect."
  Similarly `build_cancel_refund_effect` (line 153) literally constructs
  `Effect::RefundEscrow { escrow_id }`.

- `apps/orderbook/src/settlement.rs:10-12` — direct `pyana_turn::action::{CommitmentMode, Effect}`
  imports for the same reason.

- `apps/gallery/src/settlement.rs:17-20` — the heaviest example. Pulls
  `Action, Authorization, CommitmentMode, DelegationMode, Effect,
  symbol`, `ActionBuilder`, `CallForest, CallTree`, `Turn` *all
  directly from pyana_turn*. The gallery essentially re-implements the
  turn-construction pipeline inside its settlement module rather than
  routing through `AgentWallet::make_turn`. Line 163 builds a
  `Turn { ... }` struct literal carrying `Effect::RefundEscrow`.

### Contract apps are assuming

Every app is assuming **"if I construct an `Action` with a Signature
authorization and the right Effects, some out-of-band code will pick
it up, route it through TurnExecutor, and chain the receipt."** In
five of the six apps the "out-of-band code" is `apps/*/src/server.rs`
plus `pyana-app-framework`; the framework crate has accreted the
"authoring layer" the SDK aspired to be (`SDK-REVIEW.md` §App-side
pain points). The SDK is currently routed through only for
**client-of-an-app** flows (e.g. `apps/privacy-voting/src/eligibility.rs`
uses `pyana_sdk::wallet::AgentWallet` to attenuate a token — a
client-side operation).

### Where it breaks

- **Authorization placeholders are not authorization.** `[0u8; 64]`
  satisfies the `ActionBuilder` typestate "Signed" transition, and
  passes `matches!(action.authorization, Authorization::Signature(..))`
  in unit tests, **but cannot be verified by the executor**. The
  executor's `verify_action_signature` path
  (`turn/src/executor.rs::compute_signing_message` + Ed25519 verify)
  will reject a zero-signature in real federation runs. This is a
  silent regression vector: the test suite passes because nothing
  in the test suite actually runs `TurnExecutor::execute` against the
  apps' actions.

- **Effect-literal construction in apps couples apps to executor
  internals.** `Effect::CreateEscrow { cell, recipient, amount,
  condition, timeout_height, escrow_id }` has six fields and
  app-correct defaults are non-obvious (timeout = current_height +
  1000 from `apps/orderbook/src/escrow.rs:26`). Adding a field to
  `Effect::CreateEscrow` requires touching every app constructing it.

- **GAP:** SDK has `wallet.sign_action(action, federation_id)`
  (`sdk/src/wallet.rs:2403`), `wallet.make_action(target, method,
  effects, federation_id)` (`sdk/src/wallet.rs:2440`), and
  `wallet.make_turn(action)` (`sdk/src/wallet.rs:2475`), but no app
  uses them. Apps cannot, today, because they do not hold a wallet
  reference — they hold an HTTP request and a server state. Closing
  this seam requires server-side wallet plumbing (`SDK-REVIEW.md`
  Tier-0 helper).

- **GOOD:** `apps/privacy-voting/src/effects.rs:114-125` and
  `apps/nameservice/src/effects.rs:96-105` *do* explicitly test that
  the produced action's `authorization` is `Authorization::Signature(..)`
  rather than `Unchecked`. That is exactly the anti-regression
  posture that closes Stage 8 P2.E-H; the apps know the shape they
  should be in, they just don't have the SDK helper that produces
  the *real* signature variant of the shape.

---

## Seam 2 — SDK → Turn

**What the seam should be:** `AgentWallet` constructs `Turn` values
that the executor will accept on the first try. Invariants the SDK
must enforce locally so they're not the executor's problem at submit
time: agent matches signer, nonce is monotonic, previous_receipt_hash
points to the actual chain tail, forest_hash is computed (or zeroed
and computed in `compute_turn_bytes`).

**What it actually is:** the SDK has two parallel turn-construction
paths. The minor path (`wallet.make_turn`) is the new Tier-0 helper
from `SDK-REVIEW.md`. The major path (`AgentRuntime::execute`) builds
turns manually.

### `wallet.make_turn` (newly added)

`sdk/src/wallet.rs:2475-2506`:

```rust
pub fn make_turn(&self, action: pyana_turn::action::Action) -> Turn {
    self.make_turn_for("default", action)
}

pub fn make_turn_for(&self, domain: &str, action: pyana_turn::action::Action) -> Turn {
    use pyana_turn::forest::{CallForest, CallTree};
    let tree = CallTree { action, children: vec![], hash: [0u8; 32] };
    Turn {
        agent: self.cell_id(domain),
        nonce: 0,
        fee: 0,
        call_forest: CallForest { roots: vec![tree], forest_hash: [0u8; 32] },
        memo: None,
        valid_until: None,
        previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
        depends_on: Vec::new(),
        conservation_proof: None,
        sovereign_witnesses: Default::default(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    }
}
```

### Invariants the SDK enforces vs. delegates

| Invariant | Enforced where | Notes |
|---|---|---|
| `agent` matches signing identity | `make_turn` line 2488: `self.cell_id(domain)` | Sound — the agent is derived from the wallet's pubkey, not user input. |
| `forest_hash` and `tree.hash` populated | **NOT enforced.** Both zeroed (lines 2485, 2493). | **GAP:** the wallet relies on `compute_turn_bytes` (`sdk/src/wallet.rs:3832`) re-computing the forest hash on the fly for signing, and on the executor recomputing it again on receipt. The struct literal carries `[0u8; 32]` in two places that get recomputed downstream. This is *correct* given the SDK's `compute_turn_bytes` explicitly calls `turn.call_forest.compute_hash()`, but it is structurally fragile: a different caller path (e.g. someone submitting the `make_turn` output directly via wire without going through `sign_turn`) would ship a zeroed forest_hash. |
| `previous_receipt_hash` is current tail | Line 2497 — pulls from `self.receipt_chain.last()`. | Sound. **GOOD:** the SDK is the source of truth for the local chain. |
| `nonce` is correct | **NOT enforced.** Hard-coded to 0. | **GAP:** `make_turn` always returns a turn with `nonce: 0`. The caller must mutate the returned `Turn` to set the right nonce (or accept that only the first turn of a wallet ever submits successfully). `AgentRuntime::execute` does the right thing at line 257-262 (it owns the nonce counter); `make_turn` does not, so any direct user of `make_turn` is on their own. |
| Action authorization matches signer | Action signed by `sign_action` (line 2403) bound to `federation_id`. Wallet's signing key signs. | Sound *for action authorization*. The Turn-level `SignedTurn` then signs the canonical message via `sign_turn` (line 2361). |
| Turn-hash domain v3 covers all load-bearing fields | `compute_turn_bytes` lines 3823-3878 | **PARTIAL.** Lines 3866-3877 carry an explicit `AUDIT[P2-10]` comment noting that `conservation_proof`, `sovereign_witnesses`, `execution_proof`, `execution_proof_cell`, `execution_proof_new_commitment`, `custom_program_proofs` are **NOT** covered by the turn-hash signing message. The auditing comment is honest about this being a Stage 9 deferral. **GAP** — the SDK trusts that nobody in the network swaps these fields between the wallet's signing and the executor's reading. The threat model is "wire-side bit-flips and bit-rot," not "active in-flight attacker." |

### `AgentRuntime::execute` — the older path

`sdk/src/runtime.rs:215-307`. Builds the Turn manually (lines 272-287)
rather than going through `make_turn`. This is the path the
nameservice (and most servers) use indirectly via wallet-bound
`AgentRuntime`. It correctly:
- Computes signing message via `TurnExecutor::compute_signing_message`
  (line 234) — same canonical form executor uses.
- Owns the nonce counter (lines 257-262).
- Reads `previous_receipt_hash` from the wallet's chain (lines 264-270).
- Constructs `Turn { ... }` and runs `self.executor.execute(&turn, &mut ledger)` directly.

**GOOD:** this is the canonical "SDK builds turns that the executor
will accept" path. **GAP:** it duplicates `make_turn`'s skeleton
~70 lines later in the codebase. Two parallel implementations of the
same skeleton risk drift.

---

## Seam 3 — Turn → CapTP

**What the seam should be:** when a Turn carries a CapTP-routed
effect (export, enliven, drop, validate-handoff), the executor
should produce the same state transition the CapTP layer would
have produced if it had executed directly. The off-chain CapTP
mirror (`CapTpState` in `wire/src/server.rs`) and the on-chain
ledger should not drift.

**What it actually is:** the bridge is **`wire/src/captp_routing.rs`**,
not the executor itself. The wire layer's message handlers in
`wire/src/server.rs` construct `Turn` values via
`captp_routing::build_captp_turn` and push them onto
`captp_state.pending_captp_turns` for the node to drain.

### Sites

- **Effect variants** — `turn/src/action.rs:620-670` defines four
  CapTP runtime effects: `ExportSturdyRef`, `EnlivenRef`, `DropRef`,
  `ValidateHandoff`. Comment block (lines 620-632) explains the
  Stage 7 / P1.A rationale: each CapTP wire op becomes a
  turn-submitted Effect, projecting to AIR selectors 14..17.

- **Wire-side construction** —
  `wire/src/captp_routing.rs:43-75`:
  ```rust
  pub fn build_captp_turn(agent: CellId, target: CellId, effect: Effect, nonce: u64) -> Turn {
      let action = Action {
          target,
          method: symbol("captp.route"),
          args: vec![],
          authorization: Authorization::Unchecked,
          ...
      };
      ...
  }
  ```
  Authorization is **`Unchecked`** (line 48). The comment (lines
  34-37) explicitly justifies this: "the cryptographic legitimacy
  of the operation was already established off-band (swiss number
  presented, handoff signature verified, etc.). The receipt-chain
  and AIR proof carry the state-transition evidence forward."

- **Wire-side dispatch** —
  `wire/src/server.rs:2328-2455` (EnlivenSturdyRef → EnlivenRef effect),
  `wire/src/server.rs:2390-2456` (DropRemoteRef → DropRef effect),
  `wire/src/server.rs:2509-2607` (PresentHandoff → ValidateHandoff effect).
  Each path mutates `CapTpState` in-place *and* enqueues a Turn:
  ```rust
  let effect = captp_routing::enliven_ref_effect(uri.swiss, bearer_cell);
  let turn = captp_routing::build_captp_turn(agent_cell, bearer_cell, effect, 0);
  captp.pending_captp_turns.push(turn);
  ```

- **Executor-side handling** —
  `turn/src/executor.rs:7247-7325` (ExportSturdyRef, EnlivenRef, DropRef),
  `turn/src/executor.rs:7327-7346` (ValidateHandoff).
  Each effect handler:
  - bumps a state-field counter on the action target
    (export counter on `state.fields[7]`, use_count on `state.fields[6]`,
    refcount on `state.fields[5]`),
  - records the journal entry,
  - records the effect against the cell-projected `VmEffect` row
    (`turn/src/executor.rs:2389-2461`).

### The contract and where it breaks

- **GAP — the mirror and the chain are not the same source of truth.**
  The wire layer mutates `CapTpState` first (lines 2350 `enliven`,
  2429 `process_drop_with_session`) and *then* enqueues a Turn.
  The post-commit hook is meant to reconcile them, but if the node
  fails between the mirror mutation and the turn execution, the
  mirror has advanced and the chain has not. The executor's notes
  (`turn/src/executor.rs:7327-7338`) and the design doc
  (`DESIGN-captp-integration.md` §9.4) both flag this as the
  reconciliation gap.

- **GAP — Authorization::Unchecked at the wire boundary.** The
  CapTP-routed turn carries `Authorization::Unchecked`
  (`wire/src/captp_routing.rs:48`). The executor's Stage 8 P2.E-H
  grep-guard against Unchecked is supposed to ratchet down, but the
  wire-layer producer is a legitimate Unchecked source (the
  legitimacy comes from the upstream session handshake). This is a
  documented carve-out, not a regression — but it does mean the
  "no Unchecked anywhere" goal needs an exception list, and that
  list is `captp_routing::build_captp_turn` plus the queue methods
  that `SDK-REVIEW.md` C-1 named.

- **GAP — minimal field shapes.** The four CapTP effects carry only
  identifiers (swiss number, ref id, cert hash). The richer
  membership-witness types in `DESIGN-captp-integration.md`
  (SwissMembershipProof, RefcountMembershipProof, ApprovedHandoffProof)
  are not on the wire. Executor lines 7272-7273, 7280-7283,
  7298-7300, 7330-7338 each note this is P1.A scope and that P1.C
  tightens them to real Merkle proofs.

- **GAP — PipelinedMsg drops on the floor.**
  `wire/src/server.rs:2458-2507`: when a `PipelinedMsg` arrives, the
  handler validates session/epoch and then explicitly drops the
  payload: `let _ = (target_promise_id, method, args, authorization,
  result_promise_id);`. The comment (lines 2496-2499): "Silently
  accept and queue — pipeline delivery is async. In a full
  implementation, this would be dispatched to the
  CrossFedPipelineBridge for eventual delivery." Today there is no
  CrossFedPipelineBridge active; the message is acknowledged and
  discarded. The SDK side (`sdk/src/captp_client.rs:143-152`) is
  symmetric: `LiveRef::send` accepts an action and discards it.

- **GOOD — separation of concerns.** The wire crate depends on
  `pyana-captp` and `pyana-turn` but not vice versa
  (`wire/Cargo.toml:48`, `captp/Cargo.toml:11-13`). The CapTP crate
  has no wire knowledge. This means CapTP semantics can be tested
  in-memory and the wire is a transport overlay.

---

## Seam 4 — Turn → Cell

**What the seam should be:** every effect that mutates cell state
should leave a footprint in **both** the ledger (so the executor's
in-memory ledger is the post-state) and the cell's projected
`VmEffect` trace (so the AIR proves the transition).

**What it actually is:** the executor's `apply_effect`
(`turn/src/executor.rs:4607-4750+`) mutates the cell directly via
`ledger.get_mut(cell)`; the cell-projection happens in a separate
sweep `convert_turn_effects_to_vm`
(`turn/src/executor.rs:1827-2461`).

### What I verified

- **SetField** (`apply_effect` line 4617-4647, `convert_*` line 1875-1880):
  both sides apply only when `cell == cell_id`. The mutation writes
  `c.state.fields[*index] = *value` and journals; the projection
  emits `VmEffect::SetField { field_idx, value: field_element_to_bb(value) }`.
  **GAP** flagged in 1839-1849 review comment: 32-byte values
  truncate to 4 bytes via `field_element_to_bb`, so the AIR binds a
  coarse equivalence class.

- **Transfer** (`apply_effect` line 4649+, `convert_*` line 1862-1873):
  the projection emits `VmEffect::Transfer` per-cell with
  `direction=1` for `from` and `direction=0` for `to`. The mutation
  performs the balance change. **GAP** — see Seam 9.

- **CapTP effects** (`ExportSturdyRef`, `EnlivenRef`, `DropRef`,
  `ValidateHandoff`): executor lines 7247-7346 bump state fields[5..7]
  and journal; projection emits `VmEffect::ExportSturdyRef` /
  `EnlivenRef` / `DropRef` / `ValidateHandoff` (lines 2389-2461).
  Symmetric.

- **EmitEvent** (the apps' favourite): no projection — events do not
  modify state, so they emit no `VmEffect` row, only a receipt-side
  event log entry. **GOOD** — the AIR does not need to constrain
  events.

- **GrantCapability**: asymmetric. The projection emits a row only
  for the *recipient* (`to == cell_id`); the *donor*'s c-list
  decrement is *not* projected. This is the `Stage 7-γ` semantic gap
  (the cap_root advances on bob's side without algebraic proof that
  alice consumed a slot). Cited verbatim from
  `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` §1b.

### Verdict for seam 4

Cell-mutation primitives are **AIR-constrained for the
fields-of-this-cell-state-machine** but **not for the cross-cell
balance/c-list relations**. The executor side-effects on the cell
*are* mirrored into VmEffect projections, modulo the field-truncation
gap and the per-effect asymmetries called out in
`STAGE-7-GAMMA-AGGREGATION-DESIGN.md`. So: yes, the primitives are
AIR-constrained in the per-cell scope; no, the cross-cell relations
are not. That's seam 9, not seam 4.

**GAP — 32→4 byte truncation.**
`turn/src/executor.rs:1839-1849, 1850-1858`. Both `hash_to_bb` and
`field_element_to_bb` take the first 4 bytes of a 32-byte value.
The constraint binds the proof to a 32-bit equivalence class of the
real value. The fix is `bytes32_to_babybear` (8 BabyBears per
32-byte slot) — flagged but not implemented.

---

## Seam 5 — Turn → Circuit

**Site:** `node/src/mcp.rs:181-215` —
`fn generate_effect_vm_proof(initial_balance: u64, initial_nonce: u64,
vm_effects: &[pyana_circuit::effect_vm::Effect]) -> (String,
Vec<u64>, Vec<Vec<u32>>, String)`.

(Read only per scope. Do not modify.)

### What it does (verbatim from the source)

```rust
let initial_state = pyana_circuit::effect_vm::CellState::new(initial_balance, initial_nonce as u32);
let (trace, public_inputs) = pyana_circuit::effect_vm::generate_effect_vm_trace(&initial_state, vm_effects);
let air = pyana_circuit::effect_vm::EffectVmAir::new(trace.len());
let proof = pyana_circuit::stark::prove(&air, &trace, &public_inputs);
let proof_bytes = pyana_circuit::stark::proof_to_bytes(&proof);
let proof_hex = hex_encode(&proof_bytes);
...
let bundle = pyana_turn::WitnessBundle::inline_from_trace(&trace);
let trace_rows = bundle.trace_rows.clone();
let witness_hash_hex = hex_encode(&bundle.witness_hash());
(proof_hex, public_inputs_u64, trace_rows, witness_hash_hex)
```

### Guarantees provided

- **Scope-(1) verifiability.** Given `(proof_hex, public_inputs,
  WitnessHash)`, a standalone verifier
  (`pyana::verifier::verify_effect_vm_proof`) can verify the STARK
  proof against the AIR's constraint system at trace size
  `next_power_of_two(max(2, vm_effects.len()))`. The verifier needs no
  access to the trace itself.

- **Scope-(2) replayability.** Given the WitnessBundle (trace_rows +
  witness_hash), a replayer can re-derive the trace as
  `BabyBear::new_canonical(u32)` per cell, recompute `witness_hash`,
  and re-prove. This is the audit-export shape.

- **Cell-binding via public inputs.** Public inputs include
  `OLD_COMMIT[4]`, `NEW_COMMIT[4]`, `EFFECTS_HASH[4]`, balance
  bookkeeping, and per-CapTP cert/refcount fields
  (`STAGE-7-GAMMA-AGGREGATION-DESIGN.md` §1 lists the full PI shape).
  These bind the proof to *one cell's state transition under one
  effect sequence*.

- **Canonical encoding.** Lines 199-203 explicitly use
  `stark::proof_to_bytes` (the PYNA-prefixed wire format), not
  postcard, because the standalone verifier needs the magic header.

### Guarantees NOT provided

- **No turn-level binding.** Public inputs do not include
  `Turn::hash`, `Turn::nonce`, or `previous_receipt_hash`. The proof
  proves a state transition; it does not prove that this state
  transition came from a particular turn submission.
  (`STAGE-7-GAMMA-AGGREGATION-DESIGN.md` §1, paragraph "There is no
  field for `Turn::hash`...")

- **No cross-cell coherence.** Each per-cell proof is independent —
  see seam 9.

- **No fall-back on empty `vm_effects`.** Lines 186-188 short-circuit
  to `(String::new(), vec![], vec![], String::new())`. The caller in
  `mcp.rs:2705-2717` interprets empty proof_hex as "no proof was
  generated" and emits null on the wire. **GOOD** — no junk proof
  generated; the consumer side has to decide whether to demand a
  proof or accept its absence.

- **Trace-height padding.** Line 197 sizes the AIR via
  `EffectVmAir::new(trace.len())` *after* the trace generator has
  padded to `next_power_of_two ≥ 2`. The comment (lines 194-196)
  explicitly notes the original bug ("passing `vm_effects.len()`
  panics when it's less than 2 or not a power of two"); the fix is
  to size the AIR to the **actual trace height**, not the raw effect
  count. This is correct.

### Site-specific GAPs at the seam

- **GAP — only the `exercise_bearer_cap` path projects VM effects.**
  Search for `vm_effects.push(...)` in `node/src/mcp.rs`: lines
  1336-1341 (grant path) and 2681-2703 (transfer/set_field path) and
  3002-3015 (program-deploy path). Other MCP tools that submit Turns
  do **not** generate Effect-VM proofs. So the AIR coverage is
  pathwise selective; not every Turn produces a proof.

- **GAP — `pre_state` may be `None`.** Lines 2706-2716 carry an
  explicit handler: if the agent cell is not in the ledger at proof
  time, "skipping Effect VM proof." The MCP tool returns
  `effect_vm_proof_hex: null` in that case. A consumer that ignores
  null gets no soundness from the seam.

---

## Seam 6 — Turn → Federation

**What the seam should be:** after the executor commits a turn, the
federation runs a quorum and produces a `FederationReceipt` carrying
a BLS aggregate (or vote-list fallback) over the receipt body. The
`FederationReceiptBody.turn_hash` binds the receipt to the executed
turn; `body_hash()` is what the QC signs.

**What it actually is:** the types exist
(`federation/src/receipt.rs:41-227`); the trigger that lifts a
`TurnReceipt` into a `FederationReceipt` does *not* exist.

### Sites

- `federation/src/receipt.rs:41-89` —
  `FederationReceiptBody { turn_hash, block_height, block_hash,
  agent, nonce, pre_state_hash, post_state_hash, effects_hash,
  previous_receipt_hash }`. The body has the right fields to bind
  to a turn + chain link.

- `federation/src/receipt.rs:144-177` —
  `FederationReceipt::with_threshold_qc(...)` and
  `with_vote_signatures(...)` — constructors that take a body and a
  pre-aggregated QC.

- **Trigger search.** `grep -rn "FederationReceipt\|federation_receipt" --include="*.rs"`
  yields:
  - `federation/src/receipt.rs` — the definition
  - `federation/src/lib.rs:82` — the re-export
  - `cell/src/note_bridge.rs:594` — a doc-comment reference
  - **No `FederationReceipt::with_threshold_qc(...)` or
    `with_vote_signatures(...)` call site exists in the
    executor, node, or wire layers.**

### GAP — the lifting seam is unimplemented

`TurnReceipt` is produced by `TurnExecutor::execute`
(`turn/src/executor.rs:2598`), appended to the wallet
(`AgentWallet::append_receipt`,
`sdk/src/wallet.rs::append_receipt`), and surfaced over MCP
(`node/src/mcp.rs:2666`). But it does not get wrapped into a
`FederationReceipt` anywhere in the current code.

The closely related primitive *is* present: the consensus layer
(`federation/src/node.rs:846-867`) calls `update_attested_root` to
build an `AttestedRoot { merkle_root, height, threshold_qc,
quorum_signatures }`. **AttestedRoot is the revocation-root
attestation, not the turn receipt.** A `FederationReceipt` (over a
per-turn body) is structurally separate and is not produced today.

The `WitnessedReceipt` (`turn/src/witnessed_receipt.rs:129-149`)
sits between `TurnReceipt` and `FederationReceipt` in the design
stack: it adds proof bytes + witness bundle but no quorum
signature. It is constructed at `node/src/mcp.rs::generate_effect_vm_proof`'s
caller sites (e.g. `mcp.rs:2720-2735`).

### What's promised vs. delivered

- **GOOD** — the body shape covers all the right fields, including
  `previous_receipt_hash` to chain.
- **GOOD** — the QC verifier is correctly implemented for both BLS
  threshold and Ed25519 vote paths (`federation/src/receipt.rs:186-226`).
  Tests at lines 254-376 cover threshold-met, threshold-not-met,
  wrong-body, unknown-signer, duplicate-signer.
- **GAP** — no production code path wraps a `TurnReceipt` into a
  `FederationReceipt`. The type exists; the trigger does not. This
  is the "Turn → Federation" seam, and today it is empty.
- **GAP** — the design says (`DESIGN-receipts.md` §4) that the
  body's `pre_state_hash`/`post_state_hash`/`effects_hash` should
  match the executor's emitted receipt; but with no constructor
  call site, we cannot tell which of the executor's
  `TurnReceipt` fields the future wrapper will copy in. The
  `TurnReceipt` and `FederationReceiptBody` fields are not the same
  struct; a mapping function is missing.

---

## Seam 7 — Federation → Blocklace

**What the seam should be:** federation attestations (or receipts)
enter the BFT log via `Payload::Turn(Vec<u8>)` (or a richer
`BlockPayload` variant), get totally ordered, and surface back as
`BlocklaceTurnReceipt`s.

**What it actually is:** the blocklace consumes opaque turn-bytes
and produces opaque `BlocklaceTurnReceipt`s. It knows nothing about
the federation receipt type.

### Sites

- `blocklace/src/finality.rs:46-57` —
  ```rust
  pub enum Payload {
      Turn(Vec<u8>),
      Ack,
      Checkpoint { root: [u8; 32], height: u64 },
      MembershipVote { action: MembershipAction },
      Data(Vec<u8>),
  }
  ```
  `Payload::Turn(Vec<u8>)` is opaque — a serialized `Turn`, or could
  equally be anything else; the blocklace does not deserialize it.

- `blocklace/src/pyana_bridge.rs:165-167` —
  ```rust
  pub fn submit_turn(&self, blocklace: &mut Blocklace, turn_data: Vec<u8>) -> BlockId {
      let block = blocklace.add_block(Payload::Turn(turn_data));
      block.id()
  }
  ```
  Submission wraps opaque bytes into a `Payload::Turn` block.

- `blocklace/src/pyana_bridge.rs:175-201` —
  `process_finalized` walks newly-ordered blocks, inspects
  `block.payload`, and emits `BlocklaceTurnReceipt { block_id,
  submitter, seq, turn_data, tier, finality_height }` for each
  `Payload::Turn`.

- `blocklace/src/pyana_bridge.rs:115-132` — `BlocklaceTurnReceipt`
  carries `tier: ExecutionTier` (Sovereign / Optimistic / Ordered)
  and the **raw turn_data**. The pyana executor side picks this up
  and re-runs.

- `blocklace/src/cross_reference.rs:70-82` — a richer
  `BlockPayload` variant exists:
  ```rust
  pub enum BlockPayload {
      Turn(Vec<u8>),
      CrossGroupProof(DagDeliveredProof),
      TurnWithProofs { turn: Vec<u8>, proofs: Vec<DagDeliveredProof> },
  }
  ```
  but this is encoded as opaque `Vec<u8>` *inside* `Payload::Turn`,
  not as a separate `Payload` variant. The blocklace's outer enum
  has only the flat `Payload::Turn(Vec<u8>)`.

### GAPs

- **GAP — no FederationReceipt enters the blocklace.** A
  blocklace-finalized turn's `FederationReceipt` (which would carry
  the BLS aggregate over `body_hash`) does not get appended back
  into a follow-up block. The blocklace orders submissions, but the
  federation does not (today) emit a `FederationReceipt` post-quorum
  back to the DAG. So the audit trail "turn → block → finality →
  receipt → block carrying receipt" is the right shape *in theory*
  but the second-to-last hop is missing because seam 6 is empty.

- **GAP — classify_turn examines only the first byte.**
  `blocklace/src/pyana_bridge.rs:38-51`: `match turn_bytes[0] { 0x01
  => Sovereign, 0x02 => Optimistic, _ => Ordered }`. This is the
  documented "simplified classification" (line 43); a real
  classifier would deserialize the Turn. Today the classification is
  a magic-byte protocol that the rest of the codebase does not
  encode anywhere I could find — searched for `0x01` and `0x02` byte
  markers in turn-serialization; none observed. Implication: every
  turn classifies as `Ordered`. This may be intentional (conservative
  fallback) but it nullifies the Sovereign/Optimistic tiers in
  practice.

- **GOOD — blocklace separation of concerns is honest.** The
  module-level docs (`blocklace/src/lib.rs:13-23`) explicitly
  state: "The blocklace does NOT verify payload semantics (that is
  the executor's job). The blocklace DOES guarantee total ordering
  and finality." This is exactly the right division — the BFT layer
  doesn't care what bytes it orders.

- **GOOD — cross-references carry proofs through the DAG.**
  `blocklace/src/cross_reference.rs:55-82` and §7.2 of the design
  (referenced via the file's module doc) is the "CapTP-bypass"
  story: cross-federation proofs can ride on block payloads, not
  CapTP sessions. The shape is correct; whether anything actually
  uses `BlockPayload::CrossGroupProof` today (lines 70-82) is
  another question — I see the tests at line 447-471 round-tripping
  the encoding, but no production path emitting it.

---

## Seam 8 — CapTP → Wire

**What the seam should be:** the CapTP crate is a transport-agnostic
state machine for sturdy refs, handoff certs, and pipelines. The
wire crate (over QUIC/TLS, with TCP fallback) wraps each CapTP
operation in a `WireMessage` variant and enforces wire-level
guards: TLS, replay nonces, session-epoch validation, rate
limits, message-size limits, heartbeat liveness, backpressure.

**What it actually is:** `pyana-captp` has no wire dependency.
`pyana-wire` depends on `pyana-captp` and `pyana-turn`. The
`hardening` module (working-tree-new file) layers the
production-hardening guards on top of the existing `auth.rs`
rate-limiter.

### Sites

- `captp/Cargo.toml:6-13` — pyana-captp deps are blake3, serde,
  postcard, bs58, getrandom, pyana-types, pyana-cell. **No
  pyana-wire.** CapTP is wire-agnostic.

- `wire/Cargo.toml:39-48` — wire depends on `pyana_captp`,
  `pyana_cell`, `pyana_turn`, `pyana_types`. Correct direction.

- `wire/src/hardening.rs:108-121` — `message_cost(msg)` assigns
  tokens to expensive operations:
  ```rust
  match msg {
      WireMessage::SubmitRevocation { .. } => 5,
      WireMessage::PresentToken { .. } => 3,
      WireMessage::EnlivenSturdyRef { .. } => 2,
      WireMessage::PresentHandoff { .. } => 2,
      WireMessage::PipelinedMsg { .. } => 2,
      _ => 1,
  }
  ```
  CapTP-bearing variants get cost-2 or cost-3 budget, which
  is then deducted from a per-peer token bucket
  (`hardening.rs:43-102`).

- `wire/src/server.rs:1681-1836` — the connection loop runs
  *two* rate-limiters in series (the auth-tier limiter and the
  hardening token-bucket), then dispatches to `process_message`
  which holds the `CapTpState`.

- `wire/src/server.rs:1885-1893` — explicit CapTP gating:
  ```rust
  | WireMessage::EnlivenSturdyRef { .. }
  | WireMessage::PipelinedMsg { .. }
  | WireMessage::PresentHandoff { .. }
  ```
  pre-flighted into the dispatch.

### Verdict

- **GOOD — the dependency direction is right.** CapTP is a pure
  state machine; wire is the transport. The wire crate enforces
  TLS (rustls integration, `wire/src/connection.rs`), auth tiers
  (`wire/src/auth.rs:RateLimiter`), and hardening
  (`wire/src/hardening.rs:HardeningConfig`).

- **GOOD — defense in depth on rate limits.** Two limiters in
  series: an `AuthRateLimiter` (per-role limits) and a
  `hardening::RateLimiter` (per-peer token bucket on
  `message_cost`). A peer that bursts CapTP enlivens hits both.

- **GOOD — heartbeat liveness.**
  `wire/src/hardening.rs:197-200` defines `HEARTBEAT_INTERVAL =
  30s`, `HEARTBEAT_TIMEOUT = 90s`. The server loop
  (`wire/src/server.rs:1758-1763`) emits
  `ERROR_HEARTBEAT_TIMEOUT` when a peer goes silent. A wedged
  CapTP session does not survive forever.

- **GOOD — graceful shutdown coordinates CapGoodbye.**
  `hardening.rs:236-320` builds a `ShutdownCoordinator` that
  emits `WireMessage::CapGoodbye` to each open session on
  shutdown. CapTP-state cleanup follows naturally.

- **GAP — `PipelinedMsg` is rate-limited but not actually
  delivered.** As called out in seam 3: the wire handler at
  `wire/src/server.rs:2458-2507` validates session/epoch and then
  discards the payload. The hardening layer correctly charges 2
  tokens for the message; the CapTP layer correctly validates the
  session; the actual pipeline delivery is a TODO. The seam
  exists at the type level but is not load-bearing yet.

- **GAP — `EnlivenSturdyRef` returns synchronous; cross-federation
  swiss-table coherence is a single-node mirror.** The handler at
  `wire/src/server.rs:2328-2382` performs the enliven against the
  local `CapTpState::swiss_table` and immediately responds. If
  the federation has multiple nodes each holding their own mirror,
  the mirrors are not synchronized at the wire level — that's the
  reconciliation hook into the chain (seam 3's `pending_captp_turns`
  queue). The wire layer assumes a single-mirror model; the chain
  is the cross-mirror sync mechanism. This is fine *if* the chain
  reconciliation actually runs; see seam 3.

---

## Seam 9 — Multi-cell turn boundaries

**The Stage 7-γ.2 question:** when Alice transfers 100 to Bob, do
the two per-cell Effect-VM proofs algebraically agree on the
transfer amount, or are they independent?

**Answer: independent today.** Stage 7-γ.2 is queued but not
implemented; the work-in-progress that will close this seam is
the *aggregator AIR* described in
`STAGE-7-GAMMA-AGGREGATION-DESIGN.md`.

### What today actually does

1. `TurnExecutor::execute` runs `apply_effect` for every effect in
   the call forest, mutating *both* sides of a `Transfer` in the
   ledger atomically (`turn/src/executor.rs:4649+`).

2. For the proof side, `convert_turn_effects_to_vm` is called
   *per cell* in the touched-cells set
   (`turn/src/executor.rs:1827-1830`). Each cell's projection
   sweeps the same call forest and emits only the rows that touch
   that cell:
   - alice's projection emits `VmEffect::Transfer { amount: 100,
     direction: 1 }` (line 1864-1867).
   - bob's projection emits `VmEffect::Transfer { amount: 100,
     direction: 0 }` (line 1868-1872).

3. Each per-cell trace is then proven independently via
   `node/src/mcp.rs::generate_effect_vm_proof` (seam 5). Two
   independent STARK proofs result. **Neither proof carries the
   other cell's identity, balance, or NET_DELTA in its public
   inputs.**

### What this gives and what it doesn't

- **Per-cell soundness.** The AIR proves `bal_lo` decreased by 100
  on alice's side (assuming `direction=1` was witnessed) and
  increased by 100 on bob's side (`direction=0`). Within each
  cell's own state-machine, conservation holds.

- **Cross-cell coherence is *not* algebraic.** A prover with
  witness-generator access can:
  - emit alice's proof with `amount=100, direction=1`,
  - emit bob's proof with `amount=50, direction=0` (or even
    `direction=1`!),
  - and **both proofs independently verify**.

  The executor's ledger journal catches this today because the
  executor sees *one* `Effect::Transfer { amount: 100, from:
  alice, to: bob }` and runs both projections from the same
  source. *Strip the executor away* (bridge boundary, third-party
  verifier with just the two proofs) and the cross-cell binding
  evaporates.

- **GrantCapability is even worse** (cited from
  `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` §1b):
  the projection emits a row only for `to == cell_id` (line
  1881-1886). Alice's c-list slot consumption is **invisible**
  to the AIR. So bob's proof advances `cap_root` without any
  algebraic witness that alice had the slot to give. A prover
  controlling both sides could emit bob's grant proof without
  ever consuming anything on alice's side.

- **Introduce** (three cells, three projections, three
  independent proofs) suffers the same fate: each emits
  `VmEffect::Introduce { intro_hash }` over the same four-tuple,
  but no constraint forces the three `intro_hash` values to be
  equal across the three proofs.

### What Stage 7-γ.2 would add

The aggregator AIR (`STAGE-7-GAMMA-AGGREGATION-DESIGN.md` §2+)
proposes a turn-level AIR that:

- takes the N per-cell `WitnessedReceipt`s of a turn,
- proves their VmEffect rows are projections of one shared
  `Effect` list (the AIR has a column for the unprojected
  `Effect::Transfer { amount, from, to }` and checks that
  alice's row's `(amount, direction=1)` and bob's row's
  `(amount, direction=0)` came from the same source effect),
- proves the per-cell `OLD_COMMIT`/`NEW_COMMIT` agree pairwise
  on touched-cell membership in a turn-level commitment.

The `aggregate_membership` field on `WitnessedReceipt`
(`turn/src/witnessed_receipt.rs:43-52, 146-149`) is the hook
where this AIR's batch-root + leaf-index + Merkle siblings would
land. **In v1 it is always `None`** (line 38, 181). The struct is
shaped to be additively populatable.

### Verdict

- **GAP — today's state is "two independent proofs, executor-
  trusted glue."** The proofs algebraically agree only because
  the prover ran both projections from the same `Effect` literal.
  An attacker with proof-system access (third-party prover,
  malicious node, etc.) can produce diverging proofs that pass
  per-cell verification.

- **GAP — bridge boundary is precisely where this breaks.** A
  remote federation receiving alice's and bob's proofs (without
  trusting the source federation's executor) cannot verify that
  the two proofs describe a *consistent* transfer.

- **GOOD — the v1 shape is additive.** `aggregate_membership` on
  `WitnessedReceipt` plus the `STAGE-7-GAMMA-AGGREGATION-DESIGN.md`
  blueprint means landing γ.2 does not require breaking changes
  to the receipt or witness-bundle wire shape.

---

## Seam 10 — Apps → Effect variants (what should exist)

Apps emit `Effect::EmitEvent { topic, data }` because the `Effect`
enum has no app-specific variants. Each app threads two pieces of
information through `EmitEvent::data: Vec<FieldElement>`:
- a 32-byte hash of the relevant entity (name, proposal, etc.),
- and one or more parameters specific to the operation.

The executor doesn't constrain `EmitEvent` semantically beyond
"event was emitted with topic and data"; the data shape is
app-private. This is structurally fine — events are exactly
"opaque blob, indexed by topic" — but it means the AIR cannot
prove *semantic* properties of nameservice registrations,
ballot reveals, etc. (`EmitEvent` projects to a single
`VmEffect::EmitEvent { topic_bb }` row with only the topic
hash; data is dropped in the projection.)

### App-specific Effect variants the codebase wants

In order of grep-frequency and TODO-tracked-ness:

1. **`Effect::RegisterName { cell, name, owner, expires_at }`** —
   explicit TODO at `apps/nameservice/src/effects.rs:19-23`
   ("TODO(stage-7+): replace the `SetField`/`EmitEvent` pair with
   a dedicated `Effect::RegisterName` variant once Stage 7's
   Effect enum extension lands."). Mirror TODO at
   `apps/nameservice/src/main.rs:253-254`. Honest semantics need
   this so that:
   - the AIR can prove `name` was previously unbound (a
     non-membership witness over a registry-cell's name set),
   - the AIR can prove `expires_at > current_height`,
   - the receipt commits to `(name, owner)` as a checked tuple
     and not as opaque `EmitEvent` data.

2. **`Effect::CastBallot { proposal_id, commitment }`** and
   **`Effect::RevealBallot { proposal_id, commitment, option_index }`**
   — implicit in `apps/privacy-voting/src/effects.rs:31-72`. Same
   reasoning: cast-commitment uniqueness (non-double-vote) and
   reveal-binding (`option` came from a particular `commitment`
   opening) are app-specific predicates the AIR could encode
   with dedicated effects.

3. **`Effect::PlaceOrder { ... }` / `Effect::CancelOrder { id }` /
   `Effect::SettleMatch { ... }`** — `apps/orderbook/*` currently
   uses `CreateEscrow` + `ReleaseEscrow` plus app-side bookkeeping.
   The `CreateEscrow` with `EscrowCondition::ProofPresented {
   verification_key }` (`apps/orderbook/src/escrow.rs:131-135`)
   is the "right shape" but couples the order to escrow
   semantics. A dedicated order effect would let the AIR prove
   "price within book-tip ± slippage" without entangling escrow
   release.

4. **`Effect::PostBet { proposal_id, side, amount }` /
   `Effect::ResolveOracle { proposal_id, outcome }`** —
   prediction-market today threads its semantics through
   `pyana_storage::blinded::BlindedQueue` and
   `pyana_app_framework::ring_trade`. Effects could surface the
   bet-commitment and oracle-resolution as first-class.

5. **`Effect::MintArtwork { artwork_id, owner, metadata_hash }` /
   `Effect::PlaceBid { auction_id, commitment }` /
   `Effect::SettleVickrey { auction_id, winner_proof }`** — the
   gallery's `private_vickrey.rs` (cited at
   `apps/gallery/src/private_vickrey.rs:32-34`) is currently a
   STARK-proof-of-everything but is not first-class in the
   Effect enum.

### Verdict

- **GAP — `EmitEvent` is the codebase's "app effect" escape hatch.**
  This is OK as a transitional shape; it is *not* OK as the
  permanent surface, because every app's invariants then live
  outside the AIR. The Stage 7+ Effect-enum extension is the
  right place to surface 5-7 of these.

- **GOOD — apps are aware of the gap.** Two apps carry explicit
  `TODO(stage-7+)` notes that will retire this seam once the
  Effect enum opens up. The plan for Stage 7 is the right plan.

- **Cross-reference seam 1:** apps reaching past the SDK to
  build `EmitEvent` actions also reach past the SDK to build the
  dedicated effects once those land. Both seams want the same
  fix: a wallet-bound action-construction surface that maps
  app-level operations ("register name", "place order") to
  one-or-many `Effect` variants without exposing the enum
  shape.

---

## Composition health verdict

**Hopeful but uneven.** Six of ten seams are in good shape at the
type / direction level (1, 4, 5, 7, 8, 10); three are partial-but-
working (2, 3); one is empty (6); one is structurally incomplete
by design pending Stage 7-γ.2 (9).

Strengths:

- **Layering directions are correct.** Captp does not depend on
  wire; wire depends on both; circuit does not depend on turn;
  turn depends on cell+captp+circuit; sdk depends on everything
  below. No cycles; no upward dependencies.
- **Each layer's design docs are present and honest** about its
  next-stage work (Stage 7 plans for Effect enum, Stage 7-γ for
  aggregation, P1.C for richer CapTP membership witnesses, Stage
  8 P2.E-H for Unchecked grep-out, Stage 9 for turn-hash v3
  coverage).
- **Hardening (seam 8) is well-thought-out.** Two-layer rate
  limiting, heartbeat liveness, graceful shutdown with CapGoodbye,
  per-message cost weighting on CapTP-bearing variants.
- **Apps' anti-regression posture is right.** The
  `Authorization::Signature(..)` assert tests
  (`apps/nameservice/src/effects.rs:96-105`,
  `apps/privacy-voting/src/effects.rs:114-125`) show the apps know
  what shape they should be in, even when the SDK helper they need
  is downstream of where they are.

Weaknesses:

- **Seam 6 (Turn → Federation) is empty.** `FederationReceipt` type
  is fully defined and tested; nothing in the production code
  paths constructs one. The "turn committed → quorum-signed
  receipt" lift is a `with_threshold_qc(...)` call away but the
  call is not present.
- **Seam 9 (multi-cell binding) is non-algebraic today.** Two per-
  cell proofs of a Transfer or GrantCapability are independent;
  cross-cell consistency is executor-trusted, not proof-system-
  enforced. The bridge-boundary trust gradient slopes the wrong
  way.
- **Authorization::Unchecked has multiple legitimate producers.**
  CapTP routing (`wire/src/captp_routing.rs:48`), SDK queue
  methods (`SDK-REVIEW.md` C-1), and several internal turn
  builders. The "no Unchecked anywhere" grep-guard needs an
  explicit carve-out list.
- **PipelinedMsg drops on the floor.** Both the SDK side
  (`LiveRef::send`) and the wire side
  (`wire/src/server.rs:2458-2507`) accept-and-discard. The seam
  exists at the type level; the wire delivers nothing.
- **Apps reach past the SDK.** Six apps, 122 raw `use pyana_*`
  import lines, zero `use pyana_sdk::wallet::AgentWallet` in
  the effect-construction paths. The SDK has the helpers
  (`sign_action`, `make_action`, `make_turn`) but the apps can't
  use them because they don't hold a wallet at the right layer
  (the framework crate intercepts the boundary).

---

## Priority list of seams to harden

Ranked by "blast radius if left alone" × "amount of design risk
to land the fix."

1. **Seam 6 — Turn → Federation lift.** Land the
   `TurnReceipt → FederationReceiptBody` mapping function and
   call site. The crypto is done; the receipt body fields are
   defined; only the "wire it up" code is missing. Highest ROI:
   closes the entire "what does cross-federation evidence look
   like" question, and is a prerequisite for any kind of
   federation-receipt forwarding through the blocklace
   (closing seam 7's "no FederationReceipt enters the blocklace"
   GAP). Estimated: a few hundred lines in the executor or
   federation crate, plus a single call site at commit time.

2. **Seam 9 — Stage 7-γ.2 cross-cell binding.** The design doc
   (`STAGE-7-GAMMA-AGGREGATION-DESIGN.md`) is concrete; the
   `aggregate_membership` field is already shaped on
   `WitnessedReceipt`. This is the proof-system change that
   makes the bridge boundary's trust gradient slope correctly.
   Highest soundness gain. Estimated: substantial — this is the
   first turn-level AIR — but the per-cell substrate is ready.

3. **Seam 1 — SDK helpers used by apps.** Plumb a wallet handle
   into the app-framework's action-construction path so apps can
   call `wallet.make_action(target, method, effects, federation_id)`
   and `wallet.make_turn(action)` instead of holding zero-byte
   placeholders. This closes the `[0u8; 64]` regression vector
   across nameservice and privacy-voting (and the literal
   `Effect::*` struct construction across orderbook and gallery).
   Estimated: a Phase-3 SDK round per `SDK-REVIEW.md` P0
   list.

4. **Seam 3 — CapTP `PipelinedMsg` actually delivers.** Wire the
   `CrossFedPipelineBridge` referenced in
   `wire/src/server.rs:2498` and the matching SDK
   `LiveRef::send` body in `sdk/src/captp_client.rs:143-152`.
   The shape is right; the bytes need to move. Estimated:
   moderate — the routing primitive (`captp_routing.rs`) is
   in place.

5. **Seam 10 — Stage 7+ Effect enum extension.** Open up the
   Effect enum to accept app-specific variants
   (`Effect::RegisterName`, `Effect::CastBallot`, etc.) and
   retire the `EmitEvent` escape hatch in nameservice and
   privacy-voting. This is contingent on (3) above so apps
   have a sensible builder path. Estimated: per-app effect
   modules can land one app at a time once the enum-extension
   policy is in place.

6. **Seam 2 — Reconcile `make_turn` with `AgentRuntime::execute`.**
   Two parallel turn-builder skeletons risk drift. Pick one;
   delete or wrap the other. Estimated: small refactor.

7. **Seam 4 — Replace 32→4 byte truncation with `bytes32_to_babybear`.**
   The fix is named (`turn/src/executor.rs:1839-1849`); it widens
   per-effect PI slots from 1 BabyBear to 8. Coordinated with the
   AIR's domain constraints on those slots. Estimated: a coordinated
   landing in turn + circuit, ~500-1000 lines.

8. **Seam 3 (cont.) — Reconcile mirror and chain on CapTP.** The
   "mutate `CapTpState` first, queue the Turn second" pattern
   creates a window where a node crash leaves them inconsistent.
   The reconciliation hook is documented
   (`DESIGN-captp-integration.md` §9.4) but not in the code.

9. **Seam 7 — `classify_turn` deserializes the Turn.** Replace
   the first-byte heuristic in
   `blocklace/src/pyana_bridge.rs:38-51` with a real Turn
   deserialization to actually distinguish Sovereign / Optimistic /
   Ordered. Estimated: small, but requires defining what makes a
   Turn "Sovereign" in unambiguous bytes (probably presence of
   `sovereign_witnesses` and absence of cross-cell
   `Effect::Transfer { from, to }` with `from != to`).

10. **Seam 8 — None.** Wire hardening is in good shape. Maintain
    `message_cost` as new WireMessage variants are added.

---

*End of audit. ~660 lines. Companion docs: `SDK-REVIEW.md`,
`STAGE-7-GAMMA-AGGREGATION-DESIGN.md`,
`DESIGN-captp-integration.md`, `DESIGN-receipts.md`,
`AUDIT-turn-executor.md`, `EFFECT-VM-SHAPE-A.md`.*
