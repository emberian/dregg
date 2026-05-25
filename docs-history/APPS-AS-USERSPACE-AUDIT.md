# APPS-AS-USERSPACE-AUDIT — what each app reaches past the SDK for, and why

**Date:** 2026-05-24. **Status:** design-only synthesis from the existing
per-app `CLAUDIT.md` files plus a fresh adversarial pass on each. **Hard
rule from the designer:** *the answer is never "add `Effect::FooApp`".*
If we find ourselves wanting a `Effect::SubmitOrder`, the missing thing
is the *generic* primitive (effect, caveat, DSL surface, SDK helper)
that would let userspace compose the same workflow.

The question this document answers, per app:

1. **What domain semantics does the app encode?**
2. **What pyana primitives does it currently reach past the SDK to compose?** (file:line cites)
3. **What pyana primitives would let it be "pure userspace"?** —
   composing only `Effect::{SetField, EmitEvent, Transfer, Grant, Spend, Custom, …}`
   + cell-program caveats + DSL predicates.
4. **What primitives are missing?** Concrete, named, *generic*.

This complements `PYANA-FLAWS-FROM-APPS.md`: that doc catalogues *bugs*
caused by missing primitives; this one catalogues *the design-level holes
in the userspace surface area* — and prioritizes them by leverage.

The 6 apps the brief names (corrections from a quick inventory):

| App | Path | Status |
|---|---|---|
| nameservice | `apps/nameservice/` | exists, BROKEN |
| orderbook | `apps/orderbook/` | exists, BROKEN |
| prediction-market | `apps/prediction-market/` | exists, BROKEN |
| gallery | `apps/gallery/` | exists, BROKEN |
| escrow | (not a standalone app — see §5) | embedded in `orderbook::escrow`, `app-framework::escrow`, `turn::escrow::EscrowCondition` |
| privacy-voting | `apps/privacy-voting/` | exists, BROKEN |

The brief lists `apps/escrow/` but no such directory exists; the escrow
*pattern* is embedded as a primitive (`Effect::CreateEscrow / ReleaseEscrow
/ RefundEscrow` in `turn/src/action.rs:448-481`) and as orderbook's
`escrow.rs`. §5 audits this primitive directly as the de-facto "escrow
app" surface — it is a userspace pattern shipped as platform code.

---

## 1. `apps/nameservice/` — hierarchical names + rent + sub-delegation

### 1.1 Domain semantics

Maps human-readable names (`alice`, `alice.staging`, `metrics.alice`) to
target URIs (capabilities or cells), with:

- **Ownership.** A name belongs to a key/cell; only the owner can release,
  transfer, or sub-delegate.
- **Hierarchy.** `metrics.alice` is administered by `alice`'s owner via
  sub-delegation.
- **Rent / anti-squatting.** Names have an expiry epoch; rent must be
  paid (in fungible balance) to extend; expired names enter a grace
  period then become available.
- **Dispute / arbitration.** A challenger can stake a bond against a
  name; resolution either burns the stake or transfers the name.
- **Cross-federation resolution.** `alice@other-fed` resolves via a
  remote nameservice.
- **Reverse index.** Given a target URI, find names that point to it.

### 1.2 What it reaches past the SDK to compose

Effectively *nothing*. From `apps/nameservice/CLAUDIT.md` and a fresh grep:

- `apps/nameservice/src/registry.rs:18` — `pub type PyanaUri = String;`
  (the real `captp::uri::PyanaUri` is never imported).
- `apps/nameservice/Cargo.toml:9-10` — pulls in `pyana_cell` and
  `pyana_captp` as dead deps. `grep -rn "pyana_"` across `src/`
  returns only `use pyana_app_framework::server::{AppConfig, AppServer}`
  in `main.rs:36`.
- `main.rs:85` — `current_epoch: 1` hardcoded; no clock source.
- No `Effect::*`, no `Turn`, no `Authorization::*`, no `SwissTable`,
  no `Sovereign`, no `Wallet`.

The "Pyana app" is an in-memory `tokio::sync::RwLock<BTreeMap<String,
NameEntry>>` (`registry.rs`) plus an HTTP layer. Authentication is
"the caller sends their public key in the request body and we trust
them." Storage is process-local. Rent never expires. Cross-fed
resolution is a stub.

### 1.3 Pure-userspace version

A name in pure userspace is *a cell whose state carries the (name, target,
expiry) tuple* and whose access control is *a capability granted to the
owner*. Concretely:

- **Per-name cell.** Each registered name is a cell with state slots
  for `(name_hash, target_uri_commitment, expiry_height, parent_cap)`.
  Created via `Effect::CreateCell` with a program (see below).
- **Capability-bearer ownership.** Registering `alice` mints a
  `Capability` granted via `Effect::GrantCapability { from: registry,
  to: owner_cell, cap: name_owner_cap }`. Transfer is
  `Effect::RevokeCapability` (on old owner) + `Effect::GrantCapability`
  (to new owner). Sub-delegation is *attenuated delegation*: alice
  delegates a narrowed `name_owner_cap` (scope = `metrics.alice`
  prefix) to a child via the existing `wallet.delegate` machinery
  (`sdk/src/wallet.rs:682`).
- **Rent as `Effect::Transfer` + cell-program predicate.** The
  per-name cell has a `CellProgram::Predicate` constraint:
  `field[expiry_height] >= current_block_height` (an `Immutable`
  failing-into-grace check). Rent renewal is a turn that
  `(Transfer rent_amount → treasury) ∧ (SetField expiry_height = old + epoch_len)`.
  Cell-program enforces the link between payment and extension.
- **Cross-fed resolution via CapTP.** The remote nameservice cell
  exposes a sturdy ref; the local resolver calls into it via
  CapTP `EnlivenRef + Send(method="resolve", args=[name])`. The
  caveat machinery (`turn/src/cap_caveats.rs::Caveat`) bounds the
  remote call.
- **Reverse index as a sovereign cell.** A per-federation reverse-
  index cell holds `(target_uri, name)` pairs in its 8-slot state
  (Merkle-rooted if large) and is updated atomically with the
  forward registration via a multi-cell turn.

### 1.4 What's missing

The name-shaped workflow exposes these *generic* gaps:

**(a) Cell program caveat that reads the prior field value.**
The rent-extension turn needs: "the new `expiry_height` field equals
the old `expiry_height` plus `epoch_len`" — not a static comparison,
not an `Immutable` constraint, but a *transition predicate*. Today
`CellProgram::Predicate` (`cell/src/program.rs:48-65`) has
`FieldEquals`, `FieldGte`, `FieldLte`, `SumEquals`, `Immutable`, and
`Custom`. None expresses *transition* (`new[i] == old[i] + delta`,
or `new[i] >= old[i] + min_delta`). `Immutable` is the only one that
references `old_state`; everything else is a static post-state check.

The needed primitive: extend `StateConstraint` with
**transition** variants that take both `old` and `new`:
- `FieldDelta { index, delta: FieldElement }` — `new[i] == old[i] + delta`.
- `FieldDeltaInRange { index, min_delta, max_delta }`.
- `MonotoneIncreasing { index }` — `new[i] >= old[i]`.

These compose with the existing `SumEquals` to express "balance
conservation across the transition" (today only post-state).

**(b) Cell-program access to current_block_height.**
For "expiry_height ≥ current_block" the predicate needs the height
as an input. The PI already carries `CURRENT_BLOCK_HEIGHT`
(`circuit/src/effect_vm.rs:608`). Need a `StateConstraint` variant:
`FieldGteHeight { index, offset }` — `new[i] >= CURRENT_BLOCK_HEIGHT + offset`.

**(c) `Effect::RegisterName` — but as a generic name-directory primitive.**
The brief's hard rule: not `Effect::RegisterName` specifically, but the
*generic* primitive it would specialize. The right shape:
**a content-addressed authoritative registry primitive**:

- `Effect::RegistryInsert { registry_cell, key_hash, value_commitment, attestation }`
  — append `(key_hash → value_commitment)` to a Merkle-rooted registry
  cell, with `attestation` proving caller has the right to insert
  (a capability on `registry_cell`).
- `Effect::RegistryUpdate { registry_cell, key_hash, old_commitment, new_commitment, attestation }`
  — mutate an existing entry.
- `Effect::RegistryDelete { registry_cell, key_hash, attestation }`.

Nameservice would compose: registry root + per-name cells. The
Merkle root is on the registry cell's state; per-name cells dangle off
with full state. Same shape as `swiss_table_root` /
`approved_handoffs_root` already in flight for CapTP.

**(d) `SwissTable`-shaped state in userspace.**
CapTP's `SwissTable` (`captp/src/sturdy.rs`) is a swiss-number-keyed
table inside the federation; it has `make_uri / enliven / export`
and an AIR-bindable `swiss_table_root`. Userspace needs the *same
shape* for any keyed registry: nameservice's `BTreeMap<String,
NameEntry>` is the same problem. Promote the data structure to a
reusable `pyana-storage::CommittedMap<K, V>` with Merkle root and
the same AIR plumbing.

**(e) Sub-delegation as a userspace pattern.**
Today `wallet.delegate` works for *capability tokens* (DelegatedToken
in `sdk/src/wallet.rs:682`); it does Ed25519-signed envelope chains.
For a *name-owner cap*, attenuation needs: "the delegated cap only
controls names under prefix P." The `Attenuation.services`
(`token/src/traits.rs:97-133`) is a generic vocabulary; needs a
prefix-restriction caveat:

- `Caveat::NameScope { prefix: Vec<u8> }` (or, more generally,
  `Caveat::ResourcePrefix { key_prefix }`) that the executor
  evaluates against the target name.

This is a userspace-composable caveat (already the right shape — `Caveat`
is a generic kind, you just need a new variant).

---

## 2. `apps/orderbook/` — limit-order matching with commit-reveal + escrow

### 2.1 Domain semantics

- **Orders.** `(trader, side, price, amount, order_type, time_in_force)`.
- **Matching.** Price-time priority; aggressors match against passive
  resting orders.
- **Escrow.** Trader pre-locks collateral before submission.
- **Commit-reveal.** Trader commits to an order hash; reveals after
  N blocks to prevent frontrunning.
- **Settlement.** Match → release escrow → transfer between buyer and
  seller atomically.
- **Cancel.** Trader can withdraw an unmatched order; escrow refunds.
- **Dark pool.** Optional: amounts hidden via commitments.

### 2.2 What it reaches past the SDK to compose

The orderbook *imports* primitive types but never executes through them:

- `apps/orderbook/src/escrow.rs:19-20` — imports `Effect`, `EscrowCondition`.
- `apps/orderbook/src/escrow.rs:120-150` — `build_order_escrow_effect`
  *constructs* `Effect::CreateEscrow` and returns it to the caller.
  No caller submits it to a `TurnExecutor`.
- `apps/orderbook/src/settlement.rs:99-142` — `build_settlement_effects`
  constructs `Vec<Effect>` and returns it.
- `apps/orderbook/src/circuit.rs:152-322` — defines an AIR for match
  proofs (with the bugs documented in CLAUDIT P0-3, P0-4) — calls
  `stark::prove` directly; no executor wires it.
- `apps/orderbook/src/server.rs:220` — `let trader = CellId([0xAA; 32]);`
  (hardcoded sentinel; no authentication).

The HTTP server is a freestanding axum daemon doing in-memory matching
on a `BTreeMap<Price, VecDeque<Order>>` (`book.rs:119-138`). The Pyana
imports are decorative.

### 2.3 Pure-userspace version

Orderbook is the canonical *atomic-swap-as-userspace* shape. The pure
version:

- **Per-trader cell** holds the trader's open orders as state slots
  (or as a per-trader sub-cell tree if open-order count is large) and
  the trader's collateral as `bal_lo`/`bal_hi`.
- **Per-order cell.** Each open order is a sovereign cell with
  `CellProgram::Predicate(SumEquals { indices: [collateral_locked,
  collateral_remaining], value: total })` enforcing that the cell's
  locked + remaining collateral equals the original deposit.
  Cancellation is a turn `Effect::Spend collateral_locked → trader`
  + `Effect::Destroy this_cell` (or `MakeSovereign` equivalent).
- **Matching as a federation-mediated turn.** A "matcher cell"
  (anyone, with priority via stake) submits a turn that touches
  N order cells + 2 trader cells, performing:
  - `Effect::Transfer { from: buyer_locked, to: seller, amount: fill * price }`
  - `Effect::Transfer { from: seller_locked, to: buyer, amount: fill }`
  - `Effect::SetField` on each order cell (remaining amount, status).
  All atomic via the multi-cell call_forest.
- **Priority enforcement.** The match-circuit AIR needs to prove the
  matcher picked the right pair (best bid vs. best ask, FIFO at price
  level). This is `CellProgram::Circuit` on the orderbook *book cell*
  whose state slots include the Merkle root of resting orders by
  price level — the matcher submits a `Custom` effect with a
  STARK that opens the witness and proves priority.
- **Commit-reveal via `BlindedQueue`.** Already exists
  (`storage/src/blinded.rs`). Orderbook composes: `Effect::QueueAllocate
  (orders_queue) → Effect::QueueEnqueue (committed orders)`. Reveal
  publishes `Effect::QueueDequeue` + the cleartext order, which then
  enters the book. The `BlindedQueue`'s nullifier set prevents
  double-reveal.
- **Cancel as a `NoteSpend`-shaped operation.** The escrow is a
  `Note`; cancellation spends it back to the trader.

### 2.4 What's missing

**(a) Two-party atomic swap protocol primitive.**
The matching turn touches two trader cells in `Effect::Transfer` pairs.
γ.2's bilateral binding (`STAGE-7-GAMMA-2-PI-DESIGN.md`) is exactly
this. Until γ.2 lands, two-side atomic swap is executor-trusted; after,
it's algebraic.

The userspace pattern is "Lock + Witness + Claim" generalized: the
matcher cell *witnesses* both sides' locks (via WR per cell), produces
a claim turn touching both. This wants a **named SDK pattern**:

- `SwapSdk::compose_atomic_swap(side_a: SwapSide, side_b: SwapSide) -> Turn`
  where `SwapSide = { cell, lock_cap, release_cap, amount, asset }`.
  The SDK constructs a multi-cell turn with γ.2-binding ids, attaches
  the right authorizations on each side, and produces a single
  `SignedTurn` whose `call_forest` is the swap.

This is missing today; every app reinvents it.

**(b) Cell-program caveat that reads the prior value of a field.**
Same as §1.4(a). Order cancellation needs "post-cancel collateral
field is the pre-cancel value plus refund-amount." Today no transition
predicate exists; orderbook implements this in Rust outside the AIR.

**(c) Matching-priority reference circuit (G15 from PYANA-FLAWS).**
The match-AIR needs to prove "this maker was the head of its price
level." Today every orderbook-shaped app rolls its own (and gets it
wrong). The generic primitive: a *committed sorted-collection*
storage type with an AIR-bindable `head_proof(level) → (entry, witness)`.

In SDK terms: extend `pyana-storage::ProgrammableQueue` with a
**priority-ordered variant** (`PriorityQueue<K, V>`) whose AIR-side
constraint vocabulary includes `head(K, V_expected)` and
`pop_head_to(K, new_root)`.

**(d) Cancellation as `Effect::Cancel` is *not* what's needed.**
The brief's hard rule applies. What we want is the more general
**conditional release** primitive — a generalized `ReleaseEscrow`
where the release condition can be:

- A signed cancellation by the trader (already supported via
  `EscrowCondition::SignedByAll`).
- A timeout (already supported).
- A STARK proof (already supported via `EscrowCondition::ProofPresented`,
  but the verification key shape is broken — `EscrowCondition::
  ProofPresented { verification_key: [u8; 32] }` in `turn/src/escrow.rs:53-56`
  is the wrong shape per `PYANA-FLAWS-FROM-APPS.md` G3).
- A *predicate over cell state* — `EscrowCondition::PredicateSatisfied`
  is declared at `turn/src/escrow.rs:53` but **unimplemented in the
  executor** (G18). This is the missing piece: cancel-on-state =
  predicate fires when the trader's "cancellation request" field is
  set.

Implementing `PredicateSatisfied` as an executor-side `CellProgram::
Predicate`-evaluation closes a whole class of state-machine apps.

**(e) Subscription / streaming caps — for live order book.**
Orderbook frontends want push updates: "the price level at 100 USDC
changed; here's the new top-of-book". Today this is plain WebSocket
with no auth. The userspace primitive: **a subscription capability**
that bears the right to receive `Effect::EmitEvent` events from a
target cell, with:

- `Caveat::EventFilter { topics: Vec<TopicHash> }` — narrowing what
  events the subscriber sees.
- `Caveat::RateLimit { events_per_second }` — bounding flow.
- CapTP-side: a `PipelinedSend` shape that's *long-lived*; today
  pipelining is request-response. Need a `SubscriptionMessage`
  wire-level primitive or, equivalently, a cell program that
  delivers events to a subscriber's inbox queue.

Generic, not orderbook-specific: every app with live state (auction
bid count, voting tally, prediction-market resolution) wants this.

**(f) `BlindedQueue` payload return channel (G41 from PYANA-FLAWS).**
The orderbook's commit-reveal needs *the committed order's bytes* on
reveal. `BlindedQueue::consume` returns a nullifier; the order bytes
have to travel separately. Need a `BlindedQueue::Consumed { nullifier,
payload }` variant or a sibling "blinded mailbox" keyed by commitment.

---

## 3. `apps/prediction-market/` — bet on outcomes, resolve via oracle

### 3.1 Domain semantics

- **Markets.** `(market_id, question, outcomes[], resolution_time)`.
- **Bets.** `(market, outcome, stake, bettor)`. Stakes go into the
  market's pool.
- **Resolution.** An oracle posts the winning outcome after
  `resolution_time`. Winners split the pool pro-rata to stake.
- **Privacy.** Bets are committed before resolution (blinded queue);
  identities aren't tied to stakes until reveal.
- **Ring trades.** Bettors with offsetting positions on different
  outcomes can settle peer-to-peer.

### 3.2 What it reaches past the SDK to compose

Imports `pyana_storage::blinded::crypto` and `pyana_storage::commitment::
BlindedItemCommitment` (`apps/prediction-market/src/bets.rs:18-19`).
Uses `RingTradeParticipant` from `pyana_app_framework`. From the
`lib.rs` doc block, it claims:

1. Blinded queue of outcome commitments.
2. Positional oracle feed (Merkle-rooted; KZG-stand-in).
3. Ring-trade participant for offsetting positions.

The actual code paths still bypass the executor — no `Effect::Transfer`,
no `Effect::CreateEscrow` is *submitted*; the pool is a `HashMap<MarketId,
u64>` in `market.rs`.

### 3.3 Pure-userspace version

- **Per-market cell.** State holds `(pool_balance, outcomes_root,
  resolved_outcome, resolution_height, oracle_pubkey_commitment)`.
- **Per-bet cell** (or `Note`-shaped). Holds `(market, outcome, stake)`.
  Created by `Effect::CreateCell + Effect::Transfer (bettor → bet_cell)`.
- **Pool conservation.** `CellProgram::Predicate(SumEquals { indices:
  [pool_yes, pool_no, …], value: total_pool })` — enforce stakes by
  outcome sum to total pool.
- **Resolution turn.** Oracle (federation-recognized signer) submits
  a turn that sets `resolved_outcome` on the market cell. The market
  cell's program enforces: "resolved_outcome can only transition from
  `None` to `Some(o)` if `current_block_height >= resolution_height`
  and `oracle_signature_valid`".
- **Payout.** Each winning bet cell exercises a `claim_winnings`
  capability that the market cell holds, producing
  `Effect::Transfer (market → bettor, pro_rata_winnings)`. The
  market cell's `CellProgram` enforces the pro-rata formula.

### 3.4 What's missing

**(a) Oracle primitive (G7 from PYANA-FLAWS, reserved by user).**
Every market needs a trusted resolution source. The shape: a
*federation-attested signer registry* (`Effect::RegisterAttester
{ category: oracle, pubkey, scope }`) with on-chain rotation and
revocation. Prediction-market resolution turns are authorized only
if the oracle signature is from a registered attester for the
relevant category. This is G26 (trusted-attester registry).

**(b) Pro-rata payout as a cell-program primitive.**
The payout formula is `winnings = stake * total_pool / total_winning_stake`.
This is a multiplicative-divisive predicate. Today `CellProgram::
Predicate` has no `MulEquals` or `DivEquals`. Adding them is one
direction; **the better direction** is letting cell programs invoke a
named *math gadget* — `StateConstraint::ExpressionEquals { lhs:
ExprId, rhs: ExprId }` where `ExprId` references a registered
constraint expression. The expression registry sits in
`pyana-dsl::predicates`.

This generalizes: prediction-market's pro-rata, stablecoin's CDP
collateralization ratio, lending's interest accrual — all want
`StateConstraint::ExpressionEquals`.

**(c) Pool / `Note`-shaped value with ring-spend (existing).**
`NoteSpend / NoteCreate` already exist (`turn/src/action.rs:273-311`).
A prediction market's pool acts as a multi-source, multi-sink note
pool. The missing piece is *batched spend* — payouts are O(N_winners)
notes spent in one turn, but `NoteSpend` is one-at-a-time. A
`Effect::NoteSpendBatch { spends: Vec<NoteSpend> }` (or, equivalently,
allowing a turn to contain N `NoteSpend` effects with a shared
turn-level conservation check — γ.2-style binding) closes this.

**(d) Stake-and-reveal commit/reveal pattern (the brief lists this).**
A bettor commits `(market, outcome, stake)` blinded; reveals after
the market's commit window closes. SDK shape:

- `CommitRevealSdk::commit(secret, public_inputs) -> CommitmentHash`
- `CommitRevealSdk::reveal(secret, public_inputs) -> RevealMessage`
- Cell-program caveat: `Caveat::CommitWindow { open_height,
  close_height }` — fires on commit during the window.
- Cell-program caveat: `Caveat::RevealWindow { open_height,
  close_height }` — fires on reveal only after the commit window closed.

The window-bounded variants of caveats are the generic primitive;
prediction-market consumes them as one of many use cases.

**(e) Subscription / streaming caps for live odds.**
Same as orderbook §2.4(e); every market wants live-updating tallies.

---

## 4. `apps/gallery/` — NFT auction with commit-reveal bids

### 4.1 Domain semantics

- **Artworks.** Unique, ownership-transferable digital items with
  provenance chain.
- **Auctions.** Per-artwork, with phases (Commit → Reveal → Closed),
  commit-reveal of bids, winner determination (sealed-bid /
  Vickrey / Dutch / Private-Vickrey).
- **Settlement.** Winning bidder's escrow → artist; ownership cap
  → winner. Atomic.
- **Royalty splits.** Artist gets X%, platform Y%, prior owner Z%.
- **Anti-sniping.** Bids in the last K blocks extend the deadline.
- **Provenance.** Append-only chain of `(prior_owner, new_owner,
  block_height)` per artwork.

### 4.2 What it reaches past the SDK to compose

From `apps/gallery/CLAUDIT.md`:

- `apps/gallery/src/artwork.rs:60-64` — `Effect::Transfer { from:
  artist, to: artist, amount: 1 }` (a no-op self-transfer used as a
  pseudo-mint).
- `apps/gallery/src/settlement.rs:71-153` — composed turn with
  `Effect::ReleaseEscrow` + `Effect::Transfer`. Aborts because
  `PyanaEngine::new()` doesn't set a proof verifier
  (`sdk/src/embed.rs:223-265`).
- `handlers.rs:381-383` — uses `EscrowCondition::ProofPresented
  { verification_key: auction_id }` — semantically wrong (G3).
- `private_vickrey.rs` (4195 LOC) — entirely unwired.

Ownership is a `pub` `CellId` field on `Artwork` (a database row),
mutated by `ContentStore::update`. No `Effect::GrantCapability`.

### 4.3 Pure-userspace version

- **Per-artwork cell.** State holds `(artist_id_commit, creation_block,
  owner_cap_id, provenance_root, metadata_blob_hash)`.
- **Ownership = single capability.** Minting creates one
  `owner_cap` granted to the artist. Transfer is
  `Effect::RevokeCapability (old owner) + Effect::GrantCapability
  (new owner)`. Cell program enforces "at most one
  `owner_cap` is live" via `cap_table_root` and a
  uniqueness constraint.
- **Per-auction cell.** State holds `(artwork_cell, phase,
  commit_window, reveal_window, current_high_commit,
  escrow_cell)`. Cell program enforces phase transitions only at
  the right height.
- **Bids as escrows.** Bidder creates an
  `Effect::CreateEscrow` paying their bid amount into a per-bid
  escrow cell, with release condition = "I'm the winner" (a
  predicate over the auction cell's `winner` field).
- **Settlement turn.** Single atomic turn:
  - `Effect::ReleaseEscrow (winning_bid_escrow → artist + royalties)`
    — with `EscrowCondition::PredicateSatisfied (auction.winner == me)`.
  - `Effect::RevokeCapability (auction → owner_cap on artist)`.
  - `Effect::GrantCapability (winner gets owner_cap)`.
  - `Effect::SetField (artwork.provenance_root = append(...))`.

### 4.4 What's missing

**(a) NFT-shaped unique ownership (G21).** "Exactly one cell holds this
capability at a time." Today no primitive expresses this. The right
shape is *not* `Effect::TransferUniqueCap` (the brief's anti-pattern);
it's a **`CellProgram` constraint that enforces capability uniqueness**:

- `StateConstraint::CapabilityUniqueness { cap_kind: u32 }` —
  fires on the registry cell holding the uniqueness invariant.
- Plus the existing `Effect::GrantCapability / RevokeCapability`
  pair, *atomic in one turn*, satisfies it.

The bilateral binding from γ.2 (`STAGE-7-GAMMA-2-PI-DESIGN.md`) is
exactly what makes "revoke + grant in one turn = transfer" sound:
both sides bound to the same `grant_id`, no executor trust required.

**(b) Royalty split as a userspace pattern (G22).** Settlement needs
to split the payment 70% artist / 20% prior-owner / 10% platform.
Today this is several `Effect::Transfer` effects with no enforcement
that the splits sum to the input or match the artwork's declared
schedule.

**Not** `Effect::SplitTransfer` (anti-pattern). Instead:

- **Cell-program transition predicate** on the auction cell:
  `StateConstraint::SumEqualsAcross { input_fields, output_fields }`
  — relates the input value (winning bid) to a sum of output
  transfers from the same turn. This needs **inter-effect binding
  inside a turn** — currently AIR only constrains per-cell
  projections. γ.2 gives us cross-cell binding via `transfer_id`s;
  extending to "the sum of N transfer_ids from this cell equals the
  payment field" is one more accumulator constraint.

- Or: a generic **conservation-law cell program** that registers a
  set of input fields and output fields and proves equality. This
  is the math-gadget pattern from §3.4(b).

**(c) Blob primitive (G23).** Artwork images / metadata aren't on-chain.
Need `Effect::BindBlob { cell, blob_hash, storage_uri }` so the
artwork cell carries a content-addressed pointer with integrity
guarantees. The blob lives in `pyana-storage::BlobStore` (today does
not exist as a distinct primitive; the closest is the `ContentStore`
gallery rolls its own).

**(d) Anti-sniping = window-bounded caveat.** "Bids within the last K
blocks extend the deadline" requires:
- Reading `current_block_height` from PI (exists).
- A `CellProgram::Predicate(FieldDeltaInRange { index: deadline,
  min_delta: 0, max_delta: K })` — the deadline can only increase,
  by bounded amounts, triggered by bids near-current-deadline.

The transition variants from §1.4(a) cover this.

**(e) Provenance chain as IVC on the artwork cell.** Append-only chain
of transfers. Each transfer turn extends `provenance_root` via
`SetField (provenance_root = poseidon2(old_root, transfer_data))`.
The verification: an auditor can walk the chain backwards via the
WR stream. The IVC compression of the chain — already in flight per
`STAGE-7-PLUS-DESIGN.md` 7-ζ — gives this for free.

**(f) Multi-party protocol primitive (G24).** Private-Vickrey needs
the federation to threshold-decrypt the second-highest bid. The
4195 LOC of `private_vickrey.rs` reinvents this from scratch with a
non-existent `FederationGarblingNode`. The platform needs a
`coord::ThresholdDecryption` primitive (`coord/` has federation key
material today; expose it).

---

## 5. "Escrow" — Effect::CreateEscrow / ReleaseEscrow / RefundEscrow

There is no `apps/escrow/`. The escrow *pattern* ships as platform code:

- `turn/src/action.rs:448-481` — `Effect::CreateEscrow / ReleaseEscrow
  / RefundEscrow` definitions.
- `turn/src/escrow.rs` — `EscrowCondition` enum.
- `turn/src/executor.rs:4814-4990` — executor handling.
- `app-framework/src/escrow.rs` — `EscrowManager` SDK layer.

Treating it as a "userspace app": what does an escrow actually need
to do, and what does the current shape force a user to assume?

### 5.1 Domain semantics

- **Lock.** Party A deposits value into an escrow keyed on conditions.
- **Witness.** Some event/proof/timeout is observed.
- **Claim or refund.** Either the deposit moves to the
  beneficiary (claim) or returns to the depositor (refund), based
  on which condition fires first.

### 5.2 What the primitive currently composes

- `Effect::CreateEscrow { from, escrow_id, amount, conditions:
  EscrowCondition, beneficiary, timeout_height, … }` — debits
  `from`'s balance, creates an escrow record.
- `Effect::ReleaseEscrow { escrow_id, proof: Option<Vec<u8>> }` —
  if `conditions` are met, credits `beneficiary`.
- `Effect::RefundEscrow { escrow_id }` — if past `timeout_height`,
  credits `from` back.

### 5.3 Where the userspace shape leaks

**(a) `EscrowCondition::ProofPresented { verification_key: [u8; 32] }`
is the wrong shape (G3).** A 32-byte VK is not what STARK verifiers
consume. The verifier needs `(circuit_id, expected_public_inputs,
proof_bytes)`. Today every app that wants conditional release just
substitutes a placeholder VK and hopes.

**(b) `EscrowCondition::PredicateSatisfied` is unimplemented (G18).**
Declared at `turn/src/escrow.rs:53-56`; the executor only handles
`ProofPresented` and `SignedByAll` (`turn/src/executor.rs:4847-4988`).
This is the load-bearing missing variant — most app escrow conditions
are *predicates over cell state*, not proofs. Implementing it via
the existing `CellProgram::Predicate` evaluator closes a third of
the per-app escrow holes.

**(c) `Effect::ReleaseEscrow` has no default proof verifier (G2).**
`PyanaEngine::new()` doesn't set one; apps fall through to "no proof
verifier configured" rejection. The framework should refuse engine
construction without a verifier (or default to one and document
overrides).

**(d) Two-sided escrow for atomic swap (the brief's "Lock + Witness +
Claim" pattern).** Today escrow is single-sided: A locks, B claims.
Two-sided (A locks asset X, B locks asset Y, both release together
or refund together) requires two CreateEscrow effects linked by a
shared condition. Currently the link is *executor-trusted* (two
escrows happen to have the same condition; nothing forces them).

The needed primitive: **paired escrows**. Either:

- `Effect::CreatePairedEscrow { my_escrow, peer_escrow_id_commit, …  }`
  where the executor refuses release of one unless the paired one
  also releases (transactionally), and γ.2 binds the commitment.
- Or: a higher-level *swap cell program* whose state holds two
  embedded escrows and whose transition constraint enforces atomic
  joint release / refund.

This is the missing primitive that orderbook and gallery both want.
Generic, not orderbook-specific.

**(e) Time-locked escrow without external keeper.**
The current refund path is `Effect::RefundEscrow` submitted by the
depositor (or anyone) after timeout. There's no automatic firing.
The missing primitive: **scheduled effects** (G25). The depositor
schedules a refund at create-time; the federation fires it at the
appropriate block.

### 5.4 Pure-userspace escrow

Once the gaps above are closed, an escrow is just a sovereign cell
with:

- State: `(amount, beneficiary, refund_to, conditions_hash, timeout)`.
- Cell program: `CellProgram::Predicate([
    Conservation: SumEquals {indices: [released, refunded, balance], value: amount},
    AtMostOneRelease: Immutable {index: status} after release,
  ])`.
- Release/refund effects are turns invoking the cell's release/refund
  capabilities, which the cell program gates on the condition.

No `Effect::CreateEscrow` needed at the platform level — escrow
becomes a userspace pattern over `(CreateCell, Transfer, CellProgram)`.
That is the brief's hard rule applied to the escrow primitive itself.

---

## 6. `apps/privacy-voting/` — anonymous voting with commit-reveal

### 6.1 Domain semantics

- **Proposals.** `(proposal_id, options[], commit_window, reveal_window)`.
- **Eligibility.** Voters hold credentials proving membership in
  the electorate.
- **Commit.** Voter publishes `commit(option, randomness)` and a
  proof-of-eligibility.
- **Reveal.** Voter publishes `(option, randomness)`; the
  authority verifies `commit == hash(option, randomness)` and
  counts the vote.
- **Tally.** Sum of revealed votes per option.
- **Properties wanted.** Eligibility (only valid voters); uniqueness
  (one vote per voter); privacy (vote ⇏ voter); verifiability
  (anyone can recompute the tally); coercion-resistance (voter can
  fake compliance).

### 6.2 What it reaches past the SDK to compose

From `apps/privacy-voting/CLAUDIT.md`:

- `apps/privacy-voting/src/eligibility.rs:75-103` — uses
  `wallet::DelegatedToken` for credentials (bearer; replayable).
- `apps/privacy-voting/src/ballot.rs:39-49` — uses
  `blake3-derive("pyana-ballot-v1" || pid || opt || randomness)`
  for commitments (not Poseidon2, not in-circuit-able).
- `apps/privacy-voting/src/server.rs:62, 343-356` — server-private
  `HashSet<PublicKey>` for double-vote prevention; written in the
  same critical section as the commitment map (operator deanonymizes
  trivially).
- `BlindedQueue` is mounted but never consumed (`grep -n consume
  server.rs` → 0 hits).
- No `Effect::*`, no `TurnExecutor`, no STARK. Tally is `for entry in
  &entries { counts[entry.option_index] += 1 }` (`tally.rs:124-142`).

### 6.3 Pure-userspace version

- **Per-proposal cell.** State holds `(phase, commit_root,
  reveal_root, tally_root, eligibility_root,
  coordinator_pubkey_commit)`.
- **Voter eligibility = ZK presentation, not bearer token.** Voter
  holds a credential from the eligibility issuer (cell-issued
  capability with `Caveat::ProposalScope { proposal_id }`). To vote,
  voter presents a **STARK presentation proof** (via `bridge::present::
  BridgePresentationProof`, the existing right pattern per
  PYANA-FLAWS G31) proving they hold a non-revoked credential, without
  revealing which.
- **Nullifier per (voter, proposal).** `nullifier =
  Poseidon2(voter_secret, proposal_id)`. Published in the presentation.
  The proposal cell maintains `nullifier_root` (a Merkle root of
  spent nullifiers); the cell program enforces "every reveal turn
  must spend a fresh nullifier."
- **Commit via `BlindedQueue`.** `Effect::QueueEnqueue (commitments_queue,
  commitment)` with the eligibility proof as the authorization.
  Voter's identity never appears in the queue — only the nullifier.
- **Reveal via `BlindedQueue::consume_private`** publishing
  `(option, randomness, nullifier_opening_proof)`. Cell program
  on the proposal cell enforces the reveal's commitment matches a
  prior queued commitment.
- **Tally.** A STARK over the reveal_root that sums per-option counts.
  Reference circuit (G28).
- **Coercion-resistance / re-voting.** Voter can re-cast by burning
  the prior nullifier and minting a new one (MACI-style). Requires
  coordinator key (G29).

### 6.4 What's missing

**(a) `Presented<P>` extractor (G30).** Today's
`AgentWallet::DelegatedToken` is a bearer credential. For voting,
the credential should be *presented* as a ZK proof, not handed over.
The framework needs an axum extractor that consumes a
`BridgePresentationProof` and verifies it, exposing only the
presentation's *attested predicates* (e.g., "is a voter for proposal
P") and *nullifier* — never the underlying credential.

This generalizes: every privacy-preserving app wants
`Presented<EligibilityProof>` as a request extractor.

**(b) Nullifier set primitive (G17, `Effect::ClaimSlot`).** Pyana has
`NoteSpend` nullifiers and `BlindedQueue` nullifiers. They're per-
domain. Voting wants `(proposal_id, voter_secret) → spent` — same
shape, different keying. The generic primitive:

- `Effect::ClaimSlot { domain: [u8; 32], key: Commitment4, proof:
  ClaimProof }` — proves `key` ∈ slot-set under `domain`, marks
  spent atomically.

Generalizes `NoteSpend`, `BlindedQueue::consume`, subscription claim,
voting nullifier into one effect. This is G17.

**(c) Coordinator-key primitive (G29).** MACI-style anti-collusion:
voter encrypts their vote to a coordinator whose key is split among
the federation; the coordinator decrypts inside a STARK. Today
`coord/` has federation key material but no app-facing primitive.
Need:

- `Effect::EncryptedTo { coordinator_id, plaintext_commit, ciphertext }`
  — voter commits to a ciphertext.
- The federation, in a separate (delayed) turn, fires
  `Effect::CoordinatorDecrypt { commitment, decrypted_into_root }`
  — threshold-decrypts and absorbs the plaintext into a tally
  Merkle root. This is what `private_vickrey.rs` reinvents.

**(d) Tally reference circuit (G28).** A STARK that loops over a
Merkle tree of revealed votes and produces per-option counts.
Trivial circuit, prevalent need (voting, polling, prediction-market
resolution). Should live in `circuit/src/dsl/predicates::tally`.

**(e) Bulletin-board primitive (G27).** Append-only, federation-
attested, with per-leaf inclusion proofs. Voting's commitment list
*is* a bulletin board. `pyana-storage::BlindedQueue` is close but
lacks the federation-attested-root angle. Promote to a
`pyana-storage::BulletinBoard<L>` with explicit signed-root per
epoch.

---

## 7. Cross-cutting patterns

Across all six apps, the same generic primitives keep recurring. The
following is the **prioritized list of missing primitives**, ranked
by leverage (number of apps unblocked, severity of current
workarounds, structural alignment with existing pyana shapes).

### 7.1 Prioritized list of missing primitives

**Tier 1 — closes ≥3 apps, high leverage**

1. **Transition-aware `CellProgram` constraints.** Add
   `StateConstraint::FieldDelta`, `FieldDeltaInRange`,
   `MonotoneIncreasing`, `FieldGteHeight`, `SumEqualsAcross` — every
   one of nameservice (rent), orderbook (collateral), prediction-market
   (pool conservation), gallery (anti-sniping, royalty splits),
   privacy-voting (nullifier monotonicity), and escrow (timeout) is
   blocked on the *transition* version of constraints. Today's
   constraints are static-post-state checks.
   - **Affects:** every app.
   - **Where:** `cell/src/program.rs::StateConstraint`.
   - **Effort:** small. Requires extending the predicate evaluator with
     access to `old_state` (already in `evaluate`'s signature).

2. **`EscrowCondition::PredicateSatisfied` implementation (G18).**
   Declared, unimplemented. Implementing it via existing
   `CellProgram::Predicate` evaluator closes a third of all escrow
   bugs across apps.
   - **Affects:** gallery, orderbook, prediction-market, lending,
     compute-exchange, bounty-board.
   - **Where:** `turn/src/executor.rs:4847-4988` (escrow release path).
   - **Effort:** small-medium.

3. **`AuthenticatedRequest<C>` axum extractor (G1).** Already named
   in PYANA-FLAWS; this is the single highest-leverage fix.
   - **Affects:** all 6 apps + the other 4 audited.
   - **Where:** `app-framework/src/auth.rs`.
   - **Effort:** small.

4. **Federation clock (G16).** Universal dependency. Today every
   app rolls `SystemTime::now()` or accepts a request-body epoch.
   - **Affects:** nameservice (rent), orderbook (commit windows),
     prediction-market (resolution time), gallery (anti-sniping,
     phase advance), escrow (timeout), privacy-voting (phase advance).
   - **Where:** `app-framework/src/clock.rs` (new) +
     `node/src/clock.rs` (FederationClock impl reading committed
     `current_block_height`).
   - **Effort:** small.

5. **Generic claim-slot / nullifier-set primitive (G17,
   `Effect::ClaimSlot`).** Generalizes `NoteSpend`, `BlindedQueue::
   consume`, subscription claim, voting nullifier.
   - **Affects:** privacy-voting, prediction-market (bet uniqueness),
     orderbook (commit-reveal dedup), subscription.
   - **Where:** new `Effect::ClaimSlot { domain, key, proof }` in
     `turn/src/action.rs`; per-cell `nullifier_root` in `CellState`.
   - **Effort:** medium (AIR row + executor + state migration).

**Tier 2 — closes 2 apps, or single-app-but-fundamental**

6. **Paired-escrow / atomic swap pattern primitive.** Two `Effect::
   CreateEscrow` calls linked by a shared release/refund condition
   that the executor enforces atomically. γ.2's cross-cell binding
   provides the algebraic substrate; this primitive provides the
   userspace shape.
   - **Affects:** orderbook, gallery, prediction-market ring trades.
   - **Where:** new `Effect::CreatePairedEscrow` or a swap-cell
     program pattern in `app-framework::swap`.
   - **Effort:** medium.

7. **Promote `bridge::present` to `pyana-credentials` (G31).** The
   identity / eligibility / KYC pattern across apps is currently
   each reinventing a subset of `BridgePresentationBuilder` — badly.
   - **Affects:** privacy-voting, identity, gallery (gated auctions),
     prediction-market (KYC'd markets).
   - **Where:** lift `bridge/src/present.rs::BridgePresentationBuilder`
     to a top-level `pyana-credentials` crate; add
     `Presented<P>` axum extractor (G30).
   - **Effort:** small-medium (mostly refactor).

8. **Scheduled-effect primitive (G25, `Effect::FireAt`).** Auctions
   needing automatic phase advance, escrows needing automatic
   refund-on-timeout, subscriptions needing recurring debit.
   - **Affects:** gallery, escrow, prediction-market, subscription.
   - **Where:** federation-side scheduled-turn queue in
     `node/src/scheduler.rs` (new); cell-side
     `Effect::ScheduleEffect { at_height, effect, authorization }`.
   - **Effort:** medium.

9. **Cell-program `ExpressionEquals` (math gadget registry).** Today
   `CellProgram::Predicate` cannot express `winnings = stake *
   total_pool / total_winning_stake`. Need a registered-expression
   facility tied to the DSL.
   - **Affects:** prediction-market (pro-rata), stablecoin
     (collateralization), lending (interest), gallery (royalty).
   - **Where:** new `StateConstraint::ExpressionEquals { expr_id, args }`
     plus DSL registry of named expressions.
   - **Effort:** medium-large (depends on DSL maturity).

10. **`CommittedMap<K, V>` storage primitive (G33 sibling).** A
    Merkle-rooted key-value map with AIR-bindable membership and
    update proofs. Generalizes `SwissTable`, `approved_handoffs`,
    nameservice's `BTreeMap`, gallery's `ContentStore`.
    - **Affects:** nameservice, gallery, identity (revocation roots).
    - **Where:** new `pyana-storage::CommittedMap` + per-effect AIR
      bindings (the bilateral pattern from γ.2 mirrors here).
    - **Effort:** large (storage + AIR + migration).

**Tier 3 — single-app or aesthetic**

11. **Subscription / streaming caps.** Live updates with attenuation.
    Currently every app rolls naked WebSockets.
    - **Affects:** orderbook (live book), gallery (live bidding),
      prediction-market (live odds), privacy-voting (live tally
      after reveal).
    - **Where:** `captp` + new `Caveat::EventFilter` /
      `Caveat::RateLimit`.
    - **Effort:** medium.

12. **`BlindedQueue` payload return channel (G41).** When consuming,
    return the original committed payload, not just the nullifier.
    - **Affects:** orderbook commit-reveal, identity inbox, voting
      reveal.
    - **Where:** `storage/src/blinded.rs::Consumed { nullifier,
      payload }`.
    - **Effort:** small.

13. **Trusted-attester registry (G26, generalizes G7 oracle).**
    Categorized signer registry with rotation.
    - **Affects:** prediction-market (oracle), stablecoin (price feed),
      privacy-voting (eligibility issuer), identity.
    - **Where:** new `pyana-attesters` crate + per-category cells.
    - **Effort:** medium.

14. **Coordinator-key threshold-decrypt primitive (G29).** Federation
    decrypts inside a STARK.
    - **Affects:** privacy-voting (coercion-resistance), gallery
      (private-Vickrey).
    - **Where:** `coord/` extension + `Effect::CoordinatorDecrypt`.
    - **Effort:** large.

15. **Blob primitive (G23, `Effect::BindBlob`).** Content-addressed
    storage pointer with integrity.
    - **Affects:** gallery (artwork), identity (credential evidence),
      governance (proposal text).
    - **Where:** new `pyana-storage::BlobStore` +
      `Effect::BindBlob { cell, hash, uri }`.
    - **Effort:** small.

16. **Window-bounded caveats (`Caveat::CommitWindow`, `RevealWindow`).**
    Specialized variants for commit-reveal protocols.
    - **Affects:** prediction-market, orderbook, gallery, voting.
    - **Where:** `turn/src/cap_caveats.rs`.
    - **Effort:** small.

### 7.2 The top missing primitive

**Transition-aware `CellProgram` constraints (Tier 1, #1).**

This is the single primitive whose absence forces every app to leave
the AIR / executor / cell-program path and reinvent state-machine
semantics in Rust. The current `StateConstraint` vocabulary is
purely static (post-state checks); transition semantics — the heart
of every workflow (rent extension, collateral lock/unlock,
expiry advance, phase change, score increment) — must be encoded as
either:

- An out-of-band Rust check (every app does this), or
- A `Custom` constraint hash that no one implements, or
- A `CellProgram::Circuit` that requires a bespoke STARK per app.

Adding the four transition variants (`FieldDelta`, `FieldDeltaInRange`,
`MonotoneIncreasing`, `FieldGteHeight`) plus `SumEqualsAcross` for
multi-input/multi-output conservation, all evaluable by the existing
`evaluate` function with `old_state` already in its signature, would
turn every app's state-machine into expressible userspace.

This is the leverage point: small, local, and load-bearing.

### 7.3 Closing observation

The *cell + turn + capability* model is sound. The audited apps fail
not because the model is wrong but because:

- The **cell-program constraint vocabulary** is too thin for
  transitions (Tier 1, #1).
- The **escrow primitive** has half its variants unimplemented
  (Tier 1, #2).
- The **request-side framework** (auth extractors, clock, presented-
  credentials) doesn't exist (Tier 1, #3-4, #7).
- The **claim/nullifier vocabulary** is fragmented across per-effect
  variants instead of one generic slot-set (Tier 1, #5).

None of the gaps require `Effect::FooApp`. All require additions to
the *generic vocabulary* of cell programs, caveats, effects, and SDK
extractors. The brief's hard rule holds: the missing primitives are
horizontal, not vertical.

The path from the current "BROKEN, BROKEN, BROKEN" verdict to a
working app ecosystem is **Tier 1 in full + Tier 2 #6 (paired escrow,
which γ.2 enables) + Tier 2 #7 (`pyana-credentials` promotion)**.
That's roughly 4-6 weeks of platform work and unblocks all 6 apps
to be 80%+ pure userspace, with Pyana primitives carrying the
load that's currently rolled in app code.
