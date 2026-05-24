# pyana cell-model spec (TLA+)

A formal specification of pyana's cell-model invariants. The goal is an
honest, audit-against-Rust foundation — a reader should be able to point at
each TLA+ predicate and find the corresponding code in `cell/src/*` and
`turn/src/*`.

This is intentionally small (a few hundred lines of TLA+). It does not try to
model the whole system. The first increment covered identity, nonce, and the
attenuation lattice; the second increment adds **balance conservation** and
**receipt-chain causal soundness**.

### Where do the increments live?

Both the original increment (I1–I3) and the new increment (I4–I5) live in
one module, `spec/CellModel.tla`. The new properties are tightly coupled to
the existing turn actions (a successful turn must atomically increment the
nonce, transfer value, *and* append a receipt), so splitting into separate
modules would have meant duplicating the turn machinery or stitching
together state predicates across modules. Keeping it monolithic keeps the
"one successful turn = one atomic state transition" reading honest.

## What is modeled

### I1. Identity integrity

`cell.id == BLAKE3(cell.public_key || cell.token_id)`.

- Modeled by `DeriveId(pk, tid) == <<pk, tid>>` and using the derived value as
  the key of the `cells` function. The injectivity of BLAKE3 over a 64-byte
  input is abstracted as the injectivity of tuple construction.
- The invariant `IdentityIntegrity` asserts that every cell in the ledger
  satisfies `id == DeriveId(cells[id].pk, cells[id].tid)`.
- Because the actions only ever insert at `DeriveId(pk, tid)` and never
  update `pk` or `tid` after insertion, the invariant is maintained by
  construction. Rust analog: `Cell.id`, `Cell.public_key`, `Cell.token_id`
  are `pub(crate)` and only set via `Ledger::update_with` (see
  `cell/src/cell.rs` doc comment near `pub(crate) id: CellId`).

### I2. Nonce monotonicity

Per-cell nonce starts at 0, increments by exactly 1 per successful turn, and
wrong-nonce turns are rejected. The ledger nonce never regresses.

- `Init` sets every newly-created cell's nonce to 0 (`CreateCell` action).
- `SuccessfulTurn(id, providedNonce)` requires
  `providedNonce = cells[id].nonce` and updates `cells[id].nonce` to
  `cells[id].nonce + 1`.
- `RejectedTurn(id, providedNonce)` is enabled exactly when
  `providedNonce # cells[id].nonce`, and is a no-op on `cells`/`caps`.
- The action property `MonotonicNonce == [][NonceMonotonic]_vars` says that
  no transition decreases any existing cell's nonce.
- Rust analog: `Effect::IncrementNonce` in `turn/src/action.rs`, the nonce
  check in `turn/src/executor.rs`.

### I3. Capability attenuation lattice

For any granted capability `D` derived from a held capability `P`,
`is_attenuation(P.permissions, D.permissions)` must hold. The five-element
lattice is partial:

```
            Impossible      (top — most restrictive)
              /    \
        Signature  Proof
              \    /
             Either
                |
               None         (bottom — least restrictive)
```

- `IsNarrowerOrEqual(a, b)` mirrors
  `cell/src/permissions.rs::AuthRequired::is_narrower_or_equal` exactly.
- `IsAttenuation(parent, granted) == IsNarrowerOrEqual(granted, parent)`
  mirrors `cell/src/capability.rs::is_attenuation` exactly.
- Actions `GrantFromOwn` and `Redelegate` carry `IsAttenuation` as a
  precondition — they cannot fire with an amplifying permission.
- The state invariant `AttenuationSoundness` asserts that every capability
  in the c-list either was minted from a cell whose own perm attenuates to
  the cap's perm, or is an attenuation of some other capability already
  in `caps`.
- The action-level property `NoAmplificationProperty` is the strictly
  stronger statement: every freshly granted cap (in `caps' \ caps`) must
  be derivable by attenuation from the prior state.
- Rust analog: `pyana_cell::is_attenuation` callsites in
  `turn/src/executor.rs:4265` and `:5980`.

### I4. Balance conservation across a turn

Each cell carries a `balance : 0..MaxBalance`. A new symbolic sink
`burned : Nat` counts fees burned. Two flavors of successful turn exist:

- `SuccessfulTurnNop(id, nonce)` — nonce++ only, no value movement, appends
  a `<<"Nop">>` receipt.
- `SuccessfulTurnTransfer(id, nonce, to, amount, fee)` — debits
  `id.balance` by `amount + fee`, credits `to.balance` by `amount`, adds
  `fee` to `burned`, increments the nonce, appends a `<<"Transfer", to,
  amount, fee>>` receipt to `id`'s chain. Requires `cells[id].balance >=
  amount + fee` (no overdraft) and `cells[to].balance + amount <=
  MaxBalance` (model bound).

The state invariant `BalanceConservation` asserts that, at every reachable
state, `sum(cells[i].balance) + burned == |cells| * InitialEndowment`. The
companion action property `TurnConservesBalanceProperty` says the
conserved quantity (total balance + burned − endowments) is unchanged
across every step.

Rust analog: `pyana-protocol-tests/src/invariants/balance_conservation.rs`.

### I5. Receipt-chain causal soundness

Each cell carries a `receipts : Seq(Receipt)`. A receipt has fields:

- `seq` — 1-based position in the chain;
- `prev_hash` — `GenesisPrevHash = "0"` for the first receipt, otherwise
  the `Hash` of the immediately preceding receipt;
- `payload` — a tagged tuple identifying the turn shape (`<<"Nop">>` or
  `<<"Transfer", to, amount, fee>>`).

`Hash(r)` is modeled as the structural tuple `<<r.seq, r.prev_hash,
r.payload>>` — injective by construction, mirroring the BLAKE3
collision-resistance assumption that `node/src/mcp.rs` makes on
`previous_receipt_hash`.

State invariant `ReceiptChainIntegrity` requires both
`ChainSeqWellFormed` (`receipts[i].seq = i`) and `ChainWellLinked`
(`receipts[1].prev_hash = GenesisPrevHash` and, for `i > 1`,
`receipts[i].prev_hash = Hash(receipts[i-1])`).

Action property `ReceiptChainAppendOnlyProperty` requires that for every
cell that existed in the prior state, the new state's chain is a prefix
extension of the old chain — no insertion, removal, reorder, or rewrite.

Action property `TurnAppendsOneReceiptProperty` requires that every
successful turn appends exactly one receipt to exactly one cell's chain
and touches no other cell's chain.

Rust analogs: the `previous_receipt_hash` threading in `node/src/mcp.rs`
(commit `818bbd62`) and `verify_receipt_chain` in `turn/src/`.

## What is deliberately abstracted

This spec is the first increment. The following are not modeled here:

- **BLAKE3.** Treated as the injective tuple constructor `<<pk, tid>>`.
- **Cryptographic auth.** No signatures, no proofs. The lattice rule is
  about which auth would suffice, not about verifying any particular signature
  or proof.
- **The action axis of `Permissions`** (send / receive / set_state /
  set_permissions / set_verification_key / increment_nonce / delegate /
  access). Each action has its own `AuthRequired`, but they all use the same
  lattice — modeling one axis suffices for the lattice invariant. A future
  increment can split per-action.
- **Effect VM, journal, conflict / fast-path / eventual semantics.** These
  are large enough to deserve their own spec module(s). Receipts are now
  modeled (I5) but only as a per-cell append-only chain; the cross-cell
  journal is not.
- **Value commitments, notes, nullifiers, escrow, obligations, bridge
  effects.** Plain balances are now modeled (I4); the more elaborate
  zk-commitment and bridge structures are not.
- **Bearer-cap delegation temporal soundness.** The current `Redelegate`
  action requires the holder to hold the cap *now*, which gives most of
  the chain-of-attenuation property by induction. A stricter "exercised
  in turn T must originate from a turn T' < T" formulation would tag
  every cap with the turn it was minted in and require the chain to be
  monotone in turn-time. That is left to a next increment.
- **Facets (`EffectMask`), expiry, breadstuff tokens.** Faceted attenuation
  is a strictly stronger version of the same lattice rule and would extend
  `IsAttenuation` to a pair `(authNarrower, maskSubset)`.
- **Sovereign vs hosted mode, programs, verification keys.**
- **CapTP-level chaining, three-party introduction, delegated refs and
  staleness.** These are causal-soundness questions, not lattice questions.

The spec also abstracts the *checking* of identity integrity by treating
`DeriveId` as the canonical constructor: a Rust bug where `cell.id`
diverges from `derive_raw(pk, tid)` cannot be expressed in this model. To
catch such a bug, a later increment would model `id` as an independent
field and add an action `CorruptId(id, newId)` that the invariant must
forbid.

## How to run TLC

The deliverable is the spec text plus this README; running TLC is optional.
If you have the TLA+ tools installed:

```sh
# Get the tools (one-time):
#   https://github.com/tlaplus/tlaplus/releases
#   download tla2tools.jar

# Model-check (from the repo root):
java -cp /path/to/tla2tools.jar tlc2.TLC \
    -workers auto \
    -config spec/CellModel.cfg \
    spec/CellModel.tla
```

### Last clean run (this branch)

```
TLC2 Version 2.19 of 08 August 2024
Model checking completed. No error has been found.
47,142,403 states generated, 1,108,860 distinct states found,
0 states left on queue.
The depth of the complete state graph search is 12.
Finished in 02min 09s.
```

Config: `PublicKeys = {pk1,pk2}, TokenIds = {tA}, MaxNonce = 2,
MaxTurns = 2, MaxBalance = 2, InitialEndowment = 2, |caps| <= 3,
|cells| <= 2`. INVARIANT: `Invariant` (TypeOK ∧ IdentityIntegrity ∧
NonceWellFormed ∧ AttenuationSoundness ∧ BalanceConservation ∧
ReceiptChainIntegrity). PROPERTY: MonotonicNonce, NoAmplificationProperty,
TurnConservesBalanceProperty, ReceiptChainAppendOnlyProperty,
TurnAppendsOneReceiptProperty.

## Sanity check: showing the invariants bite

The following deliberate breaks were run on this branch, then reverted.
Each break is a one-line perturbation; TLC was invoked with the same cfg.

1. **Remove the precondition in `Redelegate`.** Delete the
   `IsAttenuation(fromPerm, narrowerPerm)` line. TLC reports
   `AttenuationSoundness` violated and produces a short counterexample
   where a `Signature`-restricted cap is re-delegated as a
   `None`-restricted (more permissive) cap. Counterexample depth ~3.
   (Verified against the previous spec increment.)

2. **Change `SuccessfulTurnNop` / `SuccessfulTurnTransfer` to allow
   `providedNonce <= cells[id].nonce`.** TLC reports `MonotonicNonce`
   violated; the counterexample replays the same nonce.

3. **(I4 break — balance leak.)** Edit `SuccessfulTurnTransfer` to debit
   the sender by `amount + fee` but *not* credit the recipient. TLC
   reports `Invariant` (specifically `BalanceConservation`) violated in
   under a second; counterexample depth 5 — two `CreateCell`s, then a
   single `SuccessfulTurnTransfer` with `amount = 1, fee = 0` makes total
   balance go from `4` to `3` while `burned` stays at `0`. Sample trace
   captured at `/tmp/tlc-break1.log` during validation.

4. **(I5 break — receipt linkage.)** Edit `NextReceipt` to always set
   `prev_hash := GenesisPrevHash` (i.e. forget to chain to the prior
   head). TLC reports invariant evaluation failure (an equality check
   between `"0"` and a tuple hash mismatches the type at the second
   receipt), which is the model-checker form of "the chain is broken at
   receipt 2." Counterexample depth 5.

5. **(I5 break — receipt truncation.)** Edit `SuccessfulTurnNop` to
   replace the chain (`receipts := <<r>>`) instead of appending
   (`Append(@, r)`). TLC reports `Invariant` (specifically
   `ChainSeqWellFormed`) violated in under a second; counterexample
   depth 5 — two successful nop turns on the same cell produce a final
   chain `<<[seq=2, ...]>>` whose seq does not match its position.

## Next spec increments

Increments 1 and 2 from the previous list are now landed (I4 balance
conservation, I5 receipt-chain causal soundness). Remaining priorities:

1. **Bearer-cap delegation temporal soundness.** Tag every cap with the
   turn it was minted in. Require that any cap exercised in turn `T` has
   a delegation chain originating from a cell that held the capability
   at some turn `T' < T`, with attenuation at every link. (The current
   `Redelegate` action enforces holding-now and attenuation-now; what is
   missing is the monotone-in-turn-time chain.)
2. **Per-action permission split.** Replace single `perm` with the full
   8-axis `Permissions` record; encode `Effect::SetPermissions`'s "applied
   last" rule and prove an action cannot weaken its own permission check.
3. **Facet attenuation.** Add `EffectMask` as a bitset over a small finite
   universe; extend `IsAttenuation` to require subset on the mask.
4. **CapTP three-party introduction.** Two cells already holding caps to
   each other; introduce a third. Show the introduction can only grant
   attenuated rights and cannot forge a cap to a cell the introducer
   doesn't hold.
5. **Sovereign cell upgrade.** Model `SetVerificationKey` with
   `AuthRequired = Proof` and assert that pre-image VK is bound to
   post-image VK by the upgrade proof statement.
6. **Cross-cell receipt journal.** I5 only models per-cell append-only
   chains. The real journal cross-links sender and receiver chains;
   modeling that would let us state "for every transfer there is a
   paired pair of linked receipts."
7. **Effect VM.** Once the above are stable, lift to a small operational
   semantics that processes an `Effect` list end-to-end. This is the
   biggest piece and probably wants its own module
   (`spec/EffectVM.tla`).

## File map

- `CellModel.tla` — the spec.
- `CellModel.cfg` — TLC configuration for the smallest reasonable model.
- `README.md` — this file.

## Reading the spec against the Rust

| TLA+                            | Rust                                                   |
|----------------------------------|---------------------------------------------------------|
| `DeriveId(pk, tid)`              | `CellId::derive_raw` in `types/src/lib.rs`              |
| `IsNarrowerOrEqual`              | `AuthRequired::is_narrower_or_equal` in `cell/src/permissions.rs` |
| `IsAttenuation`                  | `is_attenuation` in `cell/src/capability.rs`            |
| `CreateCell` action              | `Effect::CreateCell` in `turn/src/action.rs`            |
| `SuccessfulTurnNop` / `SuccessfulTurnTransfer` | `Effect::IncrementNonce` + transfer + receipt-emit path in `turn/src/executor.rs` |
| `GrantFromOwn` / `Redelegate`    | `Effect::GrantCapability`, `CapabilitySet::attenuate` in `cell/src/capability.rs` |
| `Revoke`                         | `Effect::RevokeCapability` in `turn/src/action.rs`      |
| `IdentityIntegrity` invariant    | `pub(crate) id`/`public_key`/`token_id` sealing in `cell/src/cell.rs` |
| `MonotonicNonce` property        | nonce-replay rejection in `turn/src/executor.rs`        |
| `AttenuationSoundness` invariant | `is_attenuation` callsites in `turn/src/executor.rs`    |
| `BalanceConservation` invariant  | `pyana-protocol-tests/src/invariants/balance_conservation.rs` |
| `ReceiptChainIntegrity` invariant| `verify_receipt_chain` in `turn/src/`, `previous_receipt_hash` threading in `node/src/mcp.rs` (commit `818bbd62`) |
| `Hash(r)` / `GenesisPrevHash`    | `BLAKE3` over receipt content / all-zero sentinel in `node/src/mcp.rs` |
