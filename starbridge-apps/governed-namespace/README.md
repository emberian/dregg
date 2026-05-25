# starbridge-governed-namespace

> **The governance-pattern reference for future apps.**
> A governance-bound atomic route table swap on a sovereign cell, composed
> from `pyana-dfa`'s `GovernedRouter` + `pyana-cell`'s slot caveats +
> `Authorization::Custom`'s threshold-signature predicate carrier.

## Overview

A **governed-namespace cell** is a sovereign cell whose state holds the
live `pyana_dfa::RouteTable` commitment, a monotonic version counter,
the constitutional committee, and the threshold. Route-table updates
require:

1. A committee member proposes a new table (`propose_table_update`).
2. The committee votes (`vote_on_proposal`). The pending-proposal root
   advances on each vote so the tally is auditable on-cell.
3. Once the threshold is met and the dispute window has elapsed, any
   committee member submits `commit_table_update` carrying the
   threshold-signature bytes under
   [`Authorization::Custom`][auth-custom] with
   [`WitnessedPredicate { kind: Custom { vk_hash: GOVERNANCE_VK } }`][pred].
   The executor dispatches to the registered governance verifier; on
   success, the atomic swap fires: `route_table_root := new_root`,
   `version += 1`, `pending_proposal_root := 0`.

This is the on-cell mirror of `pyana_dfa::GovernedRouter::update_routes`:
the CAS check (commitment must match) becomes a slot caveat
(`Immutable { index: 0 }` under propose / vote, `MonotonicSequence`
on version under commit); the threshold verification is lifted from
the in-memory `ThresholdVerifier::verify` to the executor's
`Authorization::Custom` dispatch; the kind-registry validation is
delegated to the `GOVERNANCE_VK` verifier's contract.

[auth-custom]: ../../turn/src/action.rs
[pred]: ../../cell/src/predicate.rs

## Slot layout

`STATE_SLOTS = 8`. Six slots used; two reserved.

| Slot | Name | Lifetime caveat | Operation-scoped caveats |
|---:|---|---|---|
| 0 | `route_table_root` | — | `Immutable` under propose / vote / register_service; advances under commit |
| 1 | `version` | `Monotonic` | `MonotonicSequence` under commit; `Immutable` everywhere else |
| 2 | `governance_committee_root` | `Immutable` | (frozen everywhere — constitutional) |
| 3 | `threshold` | `Immutable` | (frozen everywhere — constitutional) |
| 4 | `dispute_window_height` | `Monotonic` | `Monotonic` under propose; `Immutable` under vote / commit / register_service |
| 5 | `pending_proposal_root` | — | `Monotonic` under propose + vote; cleared under commit |
| 6, 7 | reserved | `Immutable` | (locked until a follow-on factory unlocks them) |

The factory descriptor flattens the lifetime invariants into its
`Vec<StateConstraint>`; the full operation-scoped shape lives in
`governance_program()` and is committed by the cell-program VK
(`GOVERNANCE_CHILD_PROGRAM_VK`).

## Operations

Five methods, default-deny on anything else (Cav-Codex Block 4):

### `propose_table_update` — [`build_propose_table_update_action`]

```rust
let action = build_propose_table_update_action(
    &cclerk,
    namespace_cell,
    &proposed_route_table,
    /* dispute_window_height */ current_height + 1000,
    "Add /public + /treasury routes",
);
```

Effects: two `SetField` (slots 5, 4) + one `EmitEvent`. Constraints:

- `route_table_root` and `version` frozen — no sneaky table-swap inside a proposal.
- `pending_proposal_root` advances monotonically.
- `dispute_window_height` pushes forward.
- `SenderAuthorized` against `governance_committee_root` (slot 2).

### `vote_on_proposal` — [`build_vote_on_proposal_action`]

```rust
let action = build_vote_on_proposal_action(
    &cclerk,
    namespace_cell,
    /* prior pending root */ prior_proposal_root,
    VoteKind::Approve,
    /* weight */ 1,
);
```

Effects: one `SetField` (slot 5) + one `EmitEvent`. Constraints:

- `route_table_root` and `version` frozen.
- `pending_proposal_root` advances (the voter's contribution is folded
  in via `compose_vote_update`).
- `dispute_window_height` frozen (extending the window would be a
  vote-burn attack).
- `SenderAuthorized` against the committee root.

The per-voter contribution is content-addressed by the voter's pk
hash, the vote kind, and the weight; replays produce the same advance
(commitment-level idempotency). Per-voter replay safety at the
cryptographic level is the responsibility of the proposal-side
nullifier the governance verifier consumes.

### `commit_table_update` — [`build_commit_table_update_action`]  (`Authorization::Custom`)

```rust
let action = build_commit_table_update_action(
    &cclerk,
    namespace_cell,
    &committed_route_table,
    /* new_version */ old_version + 1,
    /* threshold_sig_bytes */ aggregate_sig,
    /* governance_committee_root */ committee_root,
);
```

Effects: three `SetField` (slots 0, 1, 5) + one `EmitEvent`. The
swap is atomic: a single turn commits the new root, bumps version,
and clears the pending proposal.

**Authorization shape:**

```text
Authorization::Custom {
  predicate: WitnessedPredicate {
    kind: Custom { vk_hash: GOVERNANCE_VK },
    commitment: governance_committee_root,
    input_ref: InputRef::SigningMessage,
    proof_witness_index: 0,
  }
}
witness_blobs[0] = WitnessBlob::proof(threshold_sig_bytes)
```

The executor:

1. Resolves `InputRef::SigningMessage` to
   `compute_partial_signing_message(action, position, federation_id,
   turn_nonce)` (per `AUTHORIZATION-CUSTOM-DESIGN.md` §11.5).
2. Looks up `GOVERNANCE_VK` in the `WitnessedPredicateRegistry`.
3. Hands the verifier `(commitment=committee_root,
   input=signing_message, proof=witness_blobs[0].bytes)`.
4. Only accepts if the verifier returns `Ok`.

Cell-program constraints under commit:

- `version` advances by exactly +1 (`MonotonicSequence`) — closes the
  replay window where an attacker reuses an old threshold-sig at the
  same version.
- `route_table_root` may take any non-zero new value; the verifier
  binds the transition.
- `dispute_window_height` frozen.
- `governance_committee_root` and `threshold` frozen (constitutional).
- `SenderAuthorized` against the committee root (the submitter is a
  carrier; the threshold-sig is the actual authorization).

### `register_service` — [`build_register_service_action`]

```rust
let action = build_register_service_action(
    &cclerk,
    namespace_cell,
    "/treasury/main",
    treasury_cell_id,
);
```

Effects: one `EmitEvent`. No slot mutations — the service registration
rides the event stream, consumed by off-cell indexers. Constraints:
every governance slot is `Immutable` under this case (the registration
must not perturb the live route table or proposal state).

### `dispatch` (read-only) — [`dispatch`]

Not a turn. The read-side helper walks
`pyana_dfa::Router::classify_path(input)` against the live route
table. Used by the `<pyana-namespace-dispatch>` web component.

## DFA + `Authorization::Custom` composition

This crate is the canonical demonstration of how the two primitives
fit together:

| Primitive | Role |
|---|---|
| `pyana_dfa::RouteTable` | The route-table representation. Each cell's `slot[0]` holds the BLAKE3 commitment of the live table. |
| `pyana_dfa::Router::classify_path` | Read-side dispatch — the AIR-attestable accept/reject walk. |
| `pyana_dfa::GovernedRouter` | The in-memory mirror of "atomic table swap with CAS + threshold verification". We don't use it on the cell directly; instead, the cell-program + `Authorization::Custom` jointly enforce its invariants. |
| `pyana_dfa::KindRegistry` | The set of `RouteTarget::Userspace { kind: ... }` identifiers this app accepts. Today: `NAMESPACE_SERVICE_KIND` for the `register_service` flow. |
| `StateConstraint::MonotonicSequence` | The slot-shape mirror of the `GovernedRouter`'s "version strictly increases per commit". |
| `StateConstraint::Immutable` (committee, threshold) | The slot-shape mirror of "constitutional parameters bind across the cell's lifetime". |
| `StateConstraint::SenderAuthorized { PublicRoot { set_root_index: 2 } }` | The slot-shape sender-membership check; proves "the proposer / voter is in the committee" via a Merkle witness against the committee root. |
| `Authorization::Custom { predicate: WitnessedPredicate { kind: Custom { vk_hash: GOVERNANCE_VK }, .. } }` | The cryptographic authorization for the table swap. The registered verifier under `GOVERNANCE_VK` implements the threshold-signature scheme of the federation's choice (Ed25519 multisig, BLS aggregate, STARK threshold-sig AIR). |

The cell-program covers structural well-formedness; the
`Authorization::Custom` predicate covers cryptographic authorization;
together they produce the same end-state safety the in-memory
`GovernedRouter::update_routes` enforces, but as a turn the executor
runs and produces a `TurnReceipt` for.

## Dependency on the `Authorization::Custom` propagation lane

The structural code in this crate (slot layout, factory descriptor,
turn-builders, web components, adversarial tests) is correct and
ships independently. What gates on Phase 1's
`Authorization::Custom` propagation lane is the executor's
cryptographic acceptance of the `Custom` predicate at the auth-mode
dispatch.

- The cell-program enforces every slot-caveat on every turn.
- The Authorization::Custom variant exists (`turn::action::Authorization::Custom`).
- The verifier registry exists (`pyana_cell::predicate::WitnessedPredicateRegistry`).
- The propagation lane wires the registry into the executor's
  `Authorization::Custom` match arm so that when this crate's
  `build_commit_table_update_action` lands at the executor, the
  registered `GOVERNANCE_VK` verifier is consulted before the swap
  commits.

Until that lane lands, the executor's behavior for
`Authorization::Custom { predicate }` is conservative: the
slot-shape passes, and the auth-dispatch falls through to a
default-reject (so the swap does not commit without verifier
confirmation). The web component's `commit` flow surfaces the error
to the user.

Once Phase 1 lands, the verifier registration step is the only
remaining wiring — and that lives in the host's `register()` hook,
not in this crate.

## How it composes with the Starbridge platform

1. The wasm runtime (`wasm/src/runtime.rs`) preloads
   [`factory_descriptors()`] at startup. The browser-side
   `window.pyana.createFromFactory(GOVERNANCE_FACTORY_VK, committee_root, threshold, dispute_window)`
   resolves the string VK into the real descriptor and produces a
   sovereign governed-namespace cell.
2. The Starbridge page (`pages/index.html`) is a site fragment
   surfaced under `/starbridge-apps/governed-namespace/`, importing
   the shared inspector registry and this app's four web components
   (`<pyana-namespace>`, `<pyana-namespace-route-table>`,
   `<pyana-namespace-proposal>`, `<pyana-namespace-dispatch>`).
3. The extension cclerk (`extension/src/page.ts`) signs the `Action`
   produced by `build_propose_table_update_action` /
   `build_vote_on_proposal_action` / `build_register_service_action`
   via `signTurn`. The `commit_table_update` action's authorization
   is `Custom`, not `Signature` — the threshold-sig comes from the
   committee's off-cell signing flow, not the submitter's cclerk.

## Coexistence with `apps/governed-namespace/`

The legacy `apps/governed-namespace/` HTTP service (with its
in-process `GovernanceEngine` and `RoutingTable`) stays for now;
this crate is the canonical new implementation. The legacy app's
`GovernanceEngine::propose` / `::vote` / `::enact_amendment` map
directly onto this crate's `propose_table_update` / `vote_on_proposal`
/ `commit_table_update` turn-builders — with the crucial inversion
that the new implementation produces real `TurnReceipt`s on every
turn against the cell substrate, instead of mutating
operator-process state with no audit trail.

The dual-existence is documented in `../../STARBRIDGE-APPS-PLAN.md` §2.

## Standalone check

```sh
cargo check -p starbridge-governed-namespace
cargo test  -p starbridge-governed-namespace
```

(Per the lane's "no cargo invocations" constraint, the maintainer
runs these in their own loop; the lane ships structural code that
the test suite covers without an executor wiring dependency for the
slot-caveat regressions.)
