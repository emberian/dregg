# Cross-Cell Coordination Model

**Status:** design study; read-only on code. Companion to `STAGE-7-GAMMA-2-PI-DESIGN.md`,
`STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`, `STAGE-7-GAMMA-AGGREGATION-DESIGN.md`,
`AUTHORIZATION-CUSTOM-DESIGN.md`, `SLOT-CAVEATS-DESIGN.md`,
`WITNESSED-RECEIPT-CHAIN-DESIGN.md`, `DESIGN-captp-integration.md`,
`AUDIT-distributed-semantics.md`, and `FEDERATION-AS-CELL.md` (this doc's
deeper sibling).

The question this doc is for: **is pairwise γ.2 binding enough**, or do we
need a more general algebraic primitive for cross-cell coordination?

The TL;DR — written first so it can be read alone:

> γ.2 + `Authorization::Custom` (`WitnessedPredicate`) + slot caveats
> (`StateConstraint`) form an expressively complete primitive set for every
> cross-cell coordination pattern we have inventoried from the apps. The
> apparent gaps (N-party atomic, broadcast, quorum) are *encoding gaps*, not
> *algebraic gaps*: pairwise + Custom always reduces them, but reduction is
> verbose. The right next move is **a high-level macro / DSL surface that
> mints common multilateral patterns as compositions of pairwise edges + a
> Custom witness over the closure**, not a new AIR primitive. We do not
> need `Effect::MultilateralAtomic`. We do not need a broadcast accumulator
> primitive. We do not need a temporal-chain primitive at the AIR layer.
> What we *do* need is a sharper story for how the call_forest's role in
> γ.2's schedule reconstruction generalizes to "the call_forest is the
> multilateral binding."

The rest of the doc earns that conclusion.

---

## §1. What γ.2 Phase 1 actually solves (and how it composes)

γ.2 Phase 1 (`STAGE-7-GAMMA-2-PI-DESIGN.md`) closes one specific gap: when
a `Turn` touches two (or three) cells via a bilateral effect — `Transfer`,
`GrantCapability`, or `Introduce` — each cell produces an independent
per-cell STARK whose only cross-side join is the executor reading the same
`Effect` and feeding both projections. A cold verifier holding only the
two `WitnessedReceipt`s had no way to confirm they describe the same
effect. γ.2 adds PI fields whose canonical derivation is publicly
computable from the bilateral effect's surface data; the AIR binds the
in-trace effect data to the same id; the off-AIR verifier loop checks
agreement.

### 1.1 The three primitives, by shape

| Effect          | Cells touched | Topology                 | Id derivation                                      |
|-----------------|---------------|--------------------------|----------------------------------------------------|
| `Transfer`      | 2             | symmetric bilateral      | `H("dregg-transfer-id-v1", from, to, amount, n)`   |
| `GrantCapability`| 2            | asymmetric bilateral     | `H("dregg-grant-id-v1", from, to, cap_entry_hash, n)`|
| `Introduce`     | 3             | trilateral, 3 roles      | `H("dregg-intro-id-v1", introducer, recipient, target, perms, n)`|

Every binding is *publicly recomputable* from `(call_forest, actor_nonce)`,
which the verifier already has from γ.0's `TURN_HASH` agreement. The id
hash is folded into per-cell Poseidon2 accumulators on the AIR side
(`OUTGOING_TRANSFER_ROOT`, `INCOMING_TRANSFER_ROOT`, ...); the verifier
checks count + root agreement against a schedule it reconstructs.

### 1.2 Composition properties

The headline composition fact: **γ.2 bindings compose over graphs of
pairwise edges, with the call_forest serving as the *closure witness*.**
Concretely:

1. **Ring-of-N** — a settlement where N cells participate in a ring of
   transfers (cell `i` sends some quantity to cell `(i+1) mod N`) is N
   pairwise transfer bindings. Each cell's PI has `outbound = 1, inbound
   = 1`. The accumulator roots fall out independently. The verifier
   reconstructs the schedule from the single shared `call_forest`; if any
   edge's two sides disagree, the count/root check fails on at least one
   side.

2. **Star (1-to-N transfer fan-out)** — a payroll cell `P` sending to
   employees `E_1, ..., E_N` is N pairwise transfer bindings, all sharing
   `from = P`. `P`'s `OUTBOUND_TRANSFER_COUNT = N`; each `E_i` has
   `INBOUND_TRANSFER_COUNT = 1`. The Poseidon2 accumulator on `P` absorbs
   N entries in trace-row order; each receiver absorbs one.

3. **N-to-1 fan-in** — multiple senders all paying into a contract `C` is
   the dual. `C`'s `INBOUND_TRANSFER_COUNT = N`; each sender's `OUTBOUND
   = 1`. (Modulo: each sender produces a Turn of their own — fan-in
   crosses turn boundaries; see §3.)

4. **Mixed batches** — a single turn with several Transfers, a Grant,
   and an Introduce is the union of the above shapes. Each per-cell
   accumulator has entries from at most one effect kind per
   domain-separator class; the verifier reconstructs each class
   independently. There is no cross-class interaction in γ.2 Phase 1.

5. **Cross-class composition** is *additive in the PI surface but
   independent in the algebra*. Transfer roots don't talk to Grant roots
   even when they touch the same cells in the same turn. This is by
   design: each effect-class binding stands alone, which keeps the
   verifier's check loop a flat enumeration.

### 1.3 What the call_forest contributes

The call_forest is what makes pairwise composition collapse to a schedule
the verifier can check independently. It is the *public encoding of
which pairwise edges exist*. Three properties matter:

- It is **part of the Turn signature**, so its tampering is detectable
  via `TURN_HASH` mismatch (γ.0).
- It is **shared across all per-cell proofs of the turn**, so every cell
  agrees on which bilateral effects to expect.
- It is **deterministic in the schedule it produces**: per-cell
  projection is a pure function `(call_forest, cell_id, actor_nonce) →
  expected counts + expected roots`.

This is critical. The call_forest is *already* doing most of the
multilateral-coordination work. γ.2's PI bindings are the
algebraic-evidence layer over a coordination structure that is itself
declared in (and bound by) `Turn::hash`. **The hard question is whether
multilateral patterns are expressible as (a) a call_forest encoding plus
(b) pairwise PI bindings plus (c) optionally, a Custom witness over the
closure.** Most of the remainder of this doc argues *yes*.

---

## §2. Cross-cell pattern inventory from the apps

For each pattern: what shape it has, where it shows up, how the existing
primitives express it, and where it leaks.

### 2.1 2-party value swap — *Transfer pair*

**Where:** `apps/gallery` settlement, paired escrow, every `peer_exchange`
DM-style cell, `intent::exchange`, `commit_reveal_fulfillment`.

**Shape:** Alice's cell sends X to Bob; Bob's cell sends Y to Alice.

**Encoding:** Two `Effect::Transfer { from: A, to: B, amount: X }` and
`Effect::Transfer { from: B, to: A, amount: Y }` in *one Turn*. Both
transfers must succeed atomically — atomicity is from the Turn boundary,
not γ.2 (γ.2 is the *evidence*; atomicity is the *executor's commitment
rule*: a Turn either applies wholly or not at all).

**γ.2 evidence:** Two pairs of accumulator bindings. Alice's cell has
`OUTBOUND_TRANSFER_COUNT = 1, INBOUND_TRANSFER_COUNT = 1`, mirror on
Bob's. Verifier reconstructs schedule with both transfers from the
call_forest; checks roots.

**Adequate?** Yes. Pairwise composition is *exactly the shape* — two
unrelated edges in the same turn.

**Subtle:** the *value-equivalence* of the swap (X is worth Y to both
parties) is NOT bound by γ.2. That's a policy / pricing / intent matter,
handled by `intent::solver` and the cells' programs. γ.2 binds *what
happened*, not *whether the prices match*.

### 2.2 3-party introduce — *Introduce binding*

**Where:** CapTP three-party handoff (`captp/src/handoff.rs`,
`DESIGN-captp-integration.md`), `intent::trustless` matchmaking,
`Authorization::CapTpDelivered` flows.

**Shape:** Alice (`introducer`) shares with Bob (`recipient`) a
capability referencing Carol (`target`). Three cells are touched.

**Encoding:** `Effect::Introduce { introducer, recipient, target,
permissions }` in one Turn. γ.2 emits three per-cell proofs with role
selectors; each absorbs the same `intro_id` into a role-tagged
accumulator (`INTRO_AS_INTRODUCER_ROOT`, `INTRO_AS_RECIPIENT_ROOT`,
`INTRO_AS_TARGET_ROOT`).

**Adequate?** Yes. The three-way structure is encoded as three pairwise
bindings against the same `intro_id` — a "star" with the id at the
center. The verifier checks each role's accumulator independently
against the schedule.

**Subtle:** when introducer and recipient live on *different
federations*, the cross-fed binding is needed (the Phase 1 design flags
this as Phase 1.5: extending the preimage with `peer_federation_id`).
The transport (cross-fed CapTP) and the algebra (γ.2 with federation id)
remain factorable.

### 2.3 N-party ring trade — *N pairwise transfers*

**Where:** `apps/orderbook` ring fills, `OrderbookRingParticipant`
(`apps/orderbook/src/ring_trade.rs`), DEX cross-pair settlements.

**Shape:** Three or more orders that close on a ring (A→B at rate r1,
B→C at rate r2, ..., Z→A at rate rN). All-or-nothing: every leg fills
or none do.

**Encoding:** N `Effect::Transfer` instances in *one Turn*. Each cell
appears as both `from` (one outbound) and `to` (one inbound). γ.2:
`OUTBOUND_COUNT = 1, INBOUND_COUNT = 1` on every participant; ring
closure (every outbound flows to an inbound) is encoded in the
call_forest, *not* directly checked by γ.2 — it is implicit in the
schedule reconstruction.

**Adequate?** Yes, *with one caveat*. The "ring closes" property — the
fact that the inflows sum to the outflows around the cycle — is what
makes the ring a single economic event. γ.2 does not enforce this; the
*cell programs* of the participating cells enforce balance per-cell, and
the call_forest declares the ring structure. A malicious turn-builder
who proposed a "ring" that wasn't actually closed (e.g., a cell sends
out 10 but only 5 of inflows are routed back to it) would produce a
turn that the executor's effect-application step rejects (per-cell
balance underflow); γ.2 layers on top.

**Subtle:** the existing `OrderbookRingParticipant` enforces ring
closure at the Rust application layer with snapshot/rollback semantics.
It does not yet emit a γ.2-bound proof of ring closure as a single
binding. If we wanted "the ring closed atomically" to be an
algebraically-bound property in PI, we would add a custom `closure_id`
that all N legs share — but this is equivalent to checking N pairwise
transfer ids share a tag, which is already encodable as `Custom`
witnessed predicate + a closure-tag PI slot, *not* a new primitive.

### 2.4 1-to-N subscription — *publisher → many subscribers*

**Where:** `starbridge-apps/subscription`, `storage::pubsub::PubSubTopic`,
`storage::inbox::CapInbox`, `storage::operator::RelayOperator`, news
feeds, oracle update fanouts.

**Shape:** One publisher cell holds the source state; N subscriber cells
read from it. The publisher emits a message; each subscriber's cell
state evolves to consume it.

**Crucial framing distinction:** subscription is not a single *Turn*
that touches the publisher and all N subscribers. It is *N+1 separate
Turns*, one per cell, decoupled in time:

1. Publisher's Turn: writes message to the topic (mutates publisher's
   own state slot, e.g., `head` advances).
2. Each subscriber's Turn (later, possibly much later): reads the
   message from the topic cell (read-only on publisher; the publisher
   may not even be online), updates its own cursor.

The publisher's Turn touches *only the publisher cell* (or
optionally the topic cell, which it owns). γ.2 doesn't apply to step 1
in the multi-cell sense — there's nothing bilateral.

Each subscriber's Turn is a *unilateral read* against the topic's
state. The "binding" is the subscriber proving "this message I'm
recording was in the topic's state at commitment X." This is a
*membership proof against a state commitment*, not a pairwise binding.

**Encoding:** This is *not γ.2-shaped.* It is:

- Publisher emits a `StateConstraint::Monotonic` invariant on `head`
  + a `PubSubTopic` cell with append-only message slots, programmed via
  `CellProgram::Cases` (`cell::program::TransitionCase`) to enforce
  "send appends, dequeue advances cursor."
- Subscriber's Turn references the topic via a `WitnessedPredicate` of
  kind `MerkleMembership` against the topic's current
  `state_commitment` (or equivalently, a capability stamped with the
  message id), authorizing the subscriber's local update.

**Does γ.2 leak here?** No — because there's no bilateral effect to
bind. The pattern doesn't *want* γ.2's machinery; it wants a
*one-publisher, one-subscriber commitment-chain proof* per subscriber.
The fan-out is "many subscribers each individually prove against the
same commitment" — which is N independent membership proofs, not one
N-way binding.

**A subtler pattern — "guaranteed fan-out":** *if* we wanted "the
publisher cannot publish without simultaneously notifying all
subscribers," that *would* need either (a) a single Turn touching N+1
cells with N `Effect::Transfer` (or grant) edges from publisher to
each subscriber — pairwise composition handles it — or (b) a custom
broadcast effect with a `recipient_set_root` PI binding. We have not
seen this pattern in any app. The actual subscription apps use the
*decoupled* model: subscribers pull at their own pace.

**Verdict:** subscription is a *not-γ.2* pattern that pairs cleanly
with the existing primitives. The `WitnessedPredicate::MerkleMembership`
kind is the binding shape; there is no algebraic gap.

### 2.5 M-of-N quorum — *custom authorization predicate*

**Where:** `starbridge-apps/governed-namespace` (governance over a
namespace cell), multisig cipherclerks, threshold authorization on
sensitive caps.

**Shape:** M of N designated signers must endorse an action before it
applies. The "agreement" is over a property of the *whole set of
signers* (`|signers| >= threshold && all signers ∈ committee`), not
pairwise.

**Encoding:** `Authorization::Custom { predicate: WitnessedPredicate {
kind: BlindedSet, commitment: committee_root, ... } }` or
`kind: Custom { vk_hash: multisig_vk }`. The predicate's proof
witnesses "M valid signatures from the committee over the canonical
signing message." This is *not* γ.2 territory. γ.2 binds bilateral
effects; quorum binds *authorization*.

**Does this leak?** Only in the *naming* sense. We call γ.2 "bilateral
algebraic binding" and Custom auth "authorization predicate," but at
the level of trust, both are answering: "what evidence does the
verifier have that this action is legitimate?" Quorum is answered by
the WitnessedPredicate verifier; bilateral consistency is answered by
γ.2. They cover orthogonal facets.

**A subtle issue:** what if a quorum is *spread across multiple cells*?
E.g., "this transfer is authorized iff cells X, Y, Z each emit a
co-signing effect in the same Turn"? This *is* representable: the
Turn carries three `Effect::Custom` rows (one per co-signing cell)
plus the transfer; each co-signer cell's program enforces that its
co-sign matches the transfer's signing message; the transfer's
`Authorization::Custom` carries an aggregate proof that the three
co-signs were present.

This is verbose and currently DIY. It is *expressible*; it is not
*ergonomic*. See §7.

### 2.6 Causal chain — *bridge 4-phase Lock→Witness→Mint→Refund*

**Where:** `bridge::midnight` (lock-mint-burn-unlock cycle),
`intent::commit_reveal_fulfillment`, multi-phase escrow.

**Shape:** A multi-step protocol where step `i` presupposes step
`i-1`'s commitment. *Temporal* dependency, not symmetric pairwise
agreement.

**Encoding:** Each phase is a separate Turn (often on different
federations). The "presupposition" is encoded as:

- Phase `i`'s Turn's `Authorization::Custom` predicate witnesses
  phase `i-1`'s commitment (e.g., a Merkle membership proof against
  the source-chain's attested state root, or a witnessed receipt
  of phase `i-1`'s dregg turn).
- Phase `i`'s effect outputs commitments consumed by phase `i+1`.
- The blocklace's per-federation ordering guarantees ordering
  *within a federation*; cross-federation order is enforced by the
  presupposition predicates referencing prior `AttestedRoot`s.

**γ.2 role:** γ.2 binds *within* each phase's Turn (e.g., the Mint
phase's Turn touches the user cell and the minted-token cell — a
pairwise binding). γ.2 does *not* bind across phases; that's the
job of the `AttestedRoot` chain + `WitnessedReceipt` chain (see
`WITNESSED-RECEIPT-CHAIN-DESIGN.md`).

**Does this leak?** No. Causal chains are *the* place where
`AttestedRoot` + WR chains are the right primitive — they are
designed for "later step witnesses earlier step's commitment." γ.2
would be the wrong tool: γ.2 expects both sides of a binding to
exist *in the same Turn*, which is the opposite of what a causal
chain needs.

**Subtle:** within one Turn, multiple ordered effects also exist
(`Turn::call_forest` has ordering). But that ordering is *intra-turn*
and the AIR's trace-row order makes it constructive; no further
primitive is needed.

### 2.7 Pattern inventory summary

| Pattern              | App example                | Primitive used                       | γ.2 enough?  | Algebraic gap? |
|----------------------|----------------------------|--------------------------------------|--------------|----------------|
| 2-party value swap   | gallery, paired escrow     | γ.2 Transfer pair                    | Yes          | No             |
| 3-party introduce    | CapTP handoff              | γ.2 Introduce                        | Yes          | No             |
| N-party ring trade   | orderbook ring fills       | γ.2 N×Transfer + call_forest closure | Yes (modulo closure-id, encodable as Custom) | No |
| 1-to-N subscription  | PubSubTopic, CapInbox      | `StateConstraint::Monotonic` + `WitnessedPredicate::MerkleMembership` | N/A — not pairwise; this isn't γ.2 territory | No |
| M-of-N quorum        | governed-namespace, multisig | `Authorization::Custom` (`BlindedSet` or vk) | N/A — auth predicate, not γ.2 | No |
| Causal chain         | bridge 4-phase             | `AttestedRoot` chain + `WitnessedReceipt` references | N/A — temporal, not γ.2 | No |

**Bottom line of the inventory: no pattern is unrepresentable.** Every
pattern reduces to (γ.2 pairwise) + (Custom witnessed predicate) +
(slot caveat) + (AttestedRoot reference for causal cross-turn). The
algebra-layer gap is *zero*.

---

## §3. Where pairwise composition is sufficient — and where it leaks

The previous section is the empirical case ("we looked, and nothing
breaks"). This section is the analytical case.

### 3.1 Sufficient: any pattern reducible to a graph of pairwise edges

**Claim:** Any cross-cell coordination pattern whose semantics can be
described as a labeled graph `G = (V, E)` where:

- `V` is the set of cells touched,
- `E` is the set of bilateral effects (each edge has a fixed kind:
  Transfer, Grant, Introduce),
- the property to be coordinated is *local to each edge* (the two
  cells incident on the edge agree on the edge's parameters),

is **fully expressible as composed γ.2 bindings**, with the call_forest
declaring the edge set.

This covers:
- 2-party swap (`|E|=2`, two transfer edges).
- N-party ring (`|E|=N`, edge set forms a cycle).
- Fan-out 1-to-N (`|E|=N`, star with one center).
- Multi-effect mixed batches (edges of multiple kinds in one graph).
- Any DAG of bilateral effects within one Turn.

The verifier's algorithm in this regime is:

```
schedule = derive_schedule(call_forest, actor_nonce)  // pure
for cell c in turn.touched:
    check_count(c, schedule)
    check_root(c, schedule)
for effect e in schedule.bilateral:
    // implicit: matching counts + roots on both sides of e
    // ⇒ both per-cell proofs encoded the same edge parameters
```

### 3.2 Leaks (or *looks like* it leaks)

Patterns where the agreement is over a property of the *whole graph or
set*, not over each edge in isolation:

#### 3.2.1 N-party atomic ("all participants signed, none missed")

"All N participants emitted their leg of this ring, and exactly N legs
exist, and the ring closes."

Pairwise edges don't directly say "exactly these N edges and no
others." The schedule does: the call_forest is the closed declaration.
But γ.2 PI doesn't have a "this is the entire set" attestation per
cell; each cell's PI knows only its own neighborhood.

**However:** the call_forest is part of `TURN_HASH`, which every
per-cell PI binds via γ.0. A turn signed with one set of edges cannot
be partially-verified against a different set; the verifier's schedule
is the closed declaration. So the "whole-graph attestation" reduces to
"every per-cell proof agrees on `TURN_HASH`" — which is γ.0's job,
already done.

**No gap.** The whole-graph closure is established by `TURN_HASH`
agreement plus per-cell `OUTBOUND/INBOUND_COUNT` matching the
schedule's per-cell projection.

#### 3.2.2 Threshold over a set ("M-of-N participants sent")

"Of these N cells, at least M sent a transfer to the target."

Different from §3.2.1 because the "set" is *not the whole touched-cell
set*; it is a *subset* whose cardinality is the property.

γ.2 doesn't directly encode this. Encoding via composition:

- Each of the M senders has its own pairwise transfer binding with
  the target → target sees M inbound.
- Target's cell program (`CellProgram::Predicate` or `Cases`) enforces
  `inbound_count >= M` as a `StateConstraint`.

But `StateConstraint` operates over the cell's *post-state*, not its
γ.2 PI fields directly. Today: the cell's per-action precondition can
read `INBOUND_TRANSFER_COUNT` only if we expose it as a slot. We don't.

**This is a real ergonomic gap, but not an algebraic one.** The path
to closing it is to expose γ.2 PI counts as readable slots in the
cell's program, *or* to encode the M-of-N as a `Custom` predicate
witness that proves "the trace has ≥M `s_transfer * (1-direction)` rows"
— which the AIR can compute from sum-checks already present.

Recommendation: when an app needs M-of-N over a γ.2 count, lift the
count to a slot. Make `StateConstraint` able to consume γ.2 counts. No
new primitive at the algebraic layer.

#### 3.2.3 "Exactly one of N cells acted" (mutex / sentinel)

"Of these N candidates, exactly one is the actor for this turn."

γ.2 currently has `IS_AGENT_CELL` as the per-cell PI flag and a
sum-to-1 check in Phase 2's outer AIR (`STAGE-7-GAMMA-2-PHASE-2-SKETCH
§2.3 CG-4`). This is the in-AIR version of the mutex pattern.

The fact that this *already exists* in Phase 2 is evidence that
"whole-set predicates" are within reach of the existing primitives:
they appear as sum-cumulative constraints in the outer aggregation
AIR. The pattern generalizes — *any* whole-set predicate over the
N cells of a turn that can be expressed as a sum of per-cell
indicators is expressible in the same shape.

**This is the most important generalization.** §5 builds on it.

#### 3.2.4 Causal precedence ("B's transition presupposes A's commitment")

Already discussed in §2.6: this is `AttestedRoot` + WR chain
territory, not γ.2. No algebraic gap; the right primitive is
`WitnessedReceipt::previous_receipt_hash` + the AttestedRoot
membership predicate.

#### 3.2.5 1-to-N broadcast with mandatory delivery

"Publisher must publish, and every subscriber must mark-as-received
before the publisher's Turn finalizes."

This is the *coupled* variant of subscription (§2.4) that doesn't
actually appear in any current app. If it did appear, the encoding
would be: one Turn with N pairwise (publisher → subscriber)
`Effect::Transfer` (or grant) edges. Pairwise composition handles
it. No new primitive.

A claimed wishlist primitive — `StateConstraint::BroadcastBoundDelta
{ source_slot, recipient_set_root }` — would let a publisher cell
prove "I am committing the same delta to every cell in a set without
naming each one." This is a real architectural shape (it would allow
publisher work to be O(1) in the subscriber count), but it requires
either (a) a probabilistic membership-tree primitive (sparse Merkle
tree of subscribers + per-subscriber inclusion proofs) or (b) a
randomized-spot-check protocol. Neither is γ.2-shaped; both are
*algorithmic*, not algebraic.

**Recommendation:** if broadcast-with-cardinality-independent-cost
becomes a real need (it isn't today), introduce a `BroadcastEffect`
that emits a single signed commitment + a Merkle accumulator over
the recipient set, *as an effect kind*, separate from the bilateral
primitives. This is *additive*, not a redesign.

### 3.3 What this implies

Pairwise composition leaks only at the *ergonomic* layer:

- M-of-N over γ.2 counts is encodable but requires lifting counts
  into slots.
- Mutex/sum-to-1 is encodable in Phase 2's outer AIR and generalizes
  to "any sum-cumulative whole-set property."
- Cardinality-independent broadcast doesn't exist as a use case and
  would warrant a separate `BroadcastEffect`, not a γ.2 extension.

There is no pattern where pairwise + Custom + slot caveats is
*algebraically insufficient*. There are patterns where the
*composition is verbose*. That is a DSL-surface problem.

---

## §4. Composition with blocklace

### 4.1 Within a federation

Blocklace owns *total order of turns* within a federation
(`blocklace::ordering` realizes Cordial Miners block ordering).
γ.2 owns *cross-cell agreement* within ordered turns. The
composition is clean:

1. A turn `T` is produced by some federation member (the actor's
   federation) and signed.
2. The turn is included in a blocklace block; the block gets
   finality after a quorum acknowledges it (Cordial Miners
   supermajority).
3. The turn's per-cell proofs land in cells' WR chains; γ.2 binds
   the cross-cell effects across those proofs.
4. The blocklace's `ordered` linearization gives a total order over
   turns; γ.2 layered atop preserves per-turn algebraic agreement.

**Key invariant:** the blocklace orders turns; γ.2 binds across cells
*within* those ordered turns. There is no interaction between the two
layers' guarantees at the algebra level.

**Composition fact:** the same federation can serve N cells, all of
which produce turns ordered by the blocklace, all of which produce γ.2
bilateral bindings when they touch each other. The cross-cell algebra
is *within-federation* and is closed under the blocklace's ordering
prefix.

### 4.2 Across federations

When cells live on different federations:

- Each federation's blocklace orders only its own turns.
- The cross-federation hand-off is *not* a single turn; it is a
  sequence of turns where the receiving federation's turn references
  the sending federation's `AttestedRoot` (the federation-level state
  commitment).
- The bridge / cross-fed CapTP delivery (`Authorization::CapTpDelivered`)
  is the message carrier; once delivered, the receiving federation
  produces its own turn that ratifies the delivery (`AUDIT-distributed
  -semantics.md §3`).
- γ.2 binds within each federation's turn; *cross-federation* γ.2
  binding requires extending the canonical id preimage with
  `federation_id` (flagged Phase 1.5 in the γ.2 design).

**Composition fact:** the seam is the cross-fed CapTP delivery. The
sender's federation produces a turn `T_S` with the outbound effect;
the receiver's federation produces a turn `T_R` with the inbound
effect, presupposing `T_S`'s `WitnessedReceipt` via
`Authorization::CapTpDelivered`. γ.2's binding within each turn is
unchanged; the *cross-turn cross-fed* binding is the AttestedRoot
chain + the cert chain in `Authorization::CapTpDelivered`.

This is the same algebraic shape as the causal chain in §2.6 — and
unsurprisingly so, because cross-federation transfer *is* a causal
chain.

### 4.3 The "blocklace ordering as a StateConstraint" question

Open architectural question raised by the brief: are blocklace
ordering predicates expressible as `StateConstraint`s on a federation-
level state slot?

**Yes — at least conceptually.** A `StateConstraint::Monotonic` on a
slot `finality_round` says "this round only increases." That is the
same shape as "the blocklace's finality round only advances." If we
modeled the federation as having a slot for `finality_round` and
applied a `StateConstraint` to it, the blocklace's monotonicity
*would* be a slot caveat.

But the deeper blocklace invariants — "every finalized block is
included in the linearization," "no two leaders are simultaneously
finalized at the same round," etc. — are *process* invariants, not
*predicate* invariants. They are about *which sequence of operations
the federation members are running*, not about the state-at-rest of
a single slot.

This is the heart of the federation-as-cell question and gets a
full treatment in `FEDERATION-AS-CELL.md §3` and §7. Short version:
**static slot caveats can encode "the state respects an invariant";
they cannot encode "the state was produced by a particular process."**
For the static invariants, slot caveats are the right primitive.
For the process invariants, the blocklace's own machinery (Cordial
Miners supermajority logic) is the primitive, not a state predicate.

---

## §5. Composition with `peer_exchange`

`cell::peer_exchange` (the `PeerStateTransition` exchange) is the
federation-bypass path: two sovereign cells exchange signed state
transitions without involving the federation in the trust path.

### 5.1 The shape

Each peer holds a `PeerCellView` of the other (last known commitment,
last sequence). On a transition:

1. Producer signs `PeerStateTransition { cell_id, old_commitment,
   new_commitment, effects_hash, timestamp, sequence, signature,
   transition_proof: Option<Vec<u8>> }`.
2. Receiver checks signature, commitment continuity, sequence
   monotonicity.
3. *Optional*: receiver verifies the `transition_proof` (a STARK over
   `EffectVmAir`).

The `transition_proof` is the slot where γ.2-shaped bindings can
ride.

### 5.2 γ.2 in `peer_exchange`

Today, `transition_proof` is a generic `Option<Vec<u8>>` blob that
gets passed to `EffectVmAir`'s verifier. If the underlying turn was
a bilateral effect (Alice transferred to Bob), Alice's per-cell
proof carries her γ.2 PI accumulators; Bob's mirror does the same.
When Alice sends her `PeerStateTransition` to Bob, Bob has:

- Alice's signed PeerStateTransition (sequence-monotonic, signed).
- Alice's STARK transition_proof, which has γ.2 PI fields populated.

For Bob to *verify* the bilateral binding, Bob needs his *own*
matching STARK proof (which he produced when he applied the
inbound effect to his cell). The pair-check is exactly the γ.2
off-AIR verifier loop: it's just two `WitnessedReceipt`-shaped
inputs.

**Composition fact:** `peer_exchange` is *pairwise by construction
at the transport layer*. γ.2 PI bindings ride alongside in the
optional `transition_proof` field; the verifier can apply the same
γ.2 verifier algorithm to a pair of `PeerStateTransition.transition_proof`s
that it applies to a pair of `WitnessedReceipt`s.

### 5.3 Trust implications

`peer_exchange` skips the federation. The trust assumption shifts:

- *With* federation: blocklace ordering, threshold-attested roots,
  cross-cell consistency checked by anyone holding the WR pair.
- *Without* federation (peer_exchange): only the two parties' signed
  state transitions are evidence. The pair of γ.2-bound STARK proofs
  provides the same cross-cell algebraic agreement *between the two
  parties*, but no third party can verify what wasn't published.

This is fine and intentional. Peer-exchange is for "DM-style cells
that don't want a federation in the audit path." γ.2 bindings still
hold *for the two parties*; the federation just isn't a witness.

---

## §6. Open architectural questions

The brief lists four candidate primitives. I'll take each in turn
and give a verdict.

### 6.1 `Effect::MultilateralAtomic { participants, witnesses }`?

**Proposal:** an effect kind that names N cells and a multilateral
witness, declaring "this is one atomic event over N cells."

**Verdict: No.** Every multilateral atomic event we have inventoried
(ring trades, three-party introduces, M-of-N quorum coordinations)
factors into either:
- pairwise edges + call_forest closure (rings, introduces), or
- bilateral effects + a `Custom` auth predicate over the closure
  (quorum, threshold).

Adding `MultilateralAtomic` as an effect kind would force the AIR to
gain N-ary trace columns whose multiplicity is dynamic per effect.
This is a significant complexity addition with no expressivity gain.

The right path is: **the call_forest IS the multilateral witness.**
γ.2's existing pairwise edges plus the call_forest closure plus a
`Custom` authorization that proves "the call_forest declares exactly
this multilateral pattern" gives the same evidence at lower cost.

### 6.2 `StateConstraint::BroadcastBoundDelta { source_slot, recipient_set_root }`?

**Proposal:** a slot caveat saying "a delta to this slot is bound
to a fan-out commitment over a recipient set."

**Verdict: Defer.** This would be useful for *cardinality-independent
broadcast*, which is not a current need. When it becomes a need (e.g.,
oracle fanouts that scale beyond cell-touching-N), introduce it as a
*separate `BroadcastEffect` kind* with its own AIR, not as a
`StateConstraint`. Slot caveats are *predicates over state-at-rest*;
broadcast is *evidence of dissemination*, a different concept.

### 6.3 Temporal-chain primitive (A→B→C sequentially gated)?

**Proposal:** an AIR-level primitive for "step B's input is gated on
step A's commitment, step C's input is gated on step B's."

**Verdict: No.** This is precisely what `WitnessedReceipt::previous_
receipt_hash` + `AttestedRoot`-chain references encode at the
`WitnessedReceipt` level, and what `AUTHORIZATION-CUSTOM-DESIGN.md
§4`'s federation/nonce binding encodes at the predicate level. The
bridge 4-phase example is *the* concrete realization; the four phases
are four turns, each presupposing the prior via WR chain + AttestedRoot
membership.

Adding a temporal-chain primitive to the AIR layer would duplicate
existing machinery and force temporal logic into a regime (single-
turn AIR) that is not its natural fit (single-turn).

### 6.4 The general question: γ.2 + Custom + slot caveats — enough?

**Verdict: Yes.** Empirically (every app pattern factored), and
analytically (every leak case factored). The gaps are *ergonomic*,
not *algebraic*.

---

## §7. Proposed direction

(This is the opinionated part.)

### 7.1 Don't add algebraic primitives

The temptation is to look at "M-of-N quorum" or "broadcast" or
"three-party atomic" and reach for new effect kinds, new
authorization variants, new state-constraint variants. Resist.

The existing primitives — γ.2 bilateral + `Authorization::Custom`
(`WitnessedPredicate`) + `StateConstraint` slot caveats + `AttestedRoot`
chains + `peer_exchange` for federation-bypass — span the design
space we've explored. Every concrete need from the app inventory
factors through them.

Adding new algebraic primitives buys *fewer lines of Rust per use
case at the call site*, at the cost of:
- more AIR columns to audit,
- more soundness proofs to write,
- more verifier code paths,
- more chances for cross-primitive composition bugs.

The audits accumulating in the tree
(`AUDIT-circuit.md`, `AUDIT-cell.md`, `AUDIT-turn-executor.md`, etc.)
are evidence that algebraic-primitive proliferation has been
costly. The signal is *consolidation*, not *expansion*.

### 7.2 Do add ergonomic surface

The verbosity problem is real and worth solving. Common patterns
should have macro / DSL surfaces:

- **`ring_trade!(participants = [A, B, C, D], legs = [...])`** —
  emits N transfer effects in one Turn, declares the closure
  invariant in the call_forest, optionally emits a Custom witness
  over the closure tag.

- **`quorum!(committee = root, threshold = M, action = ...)`** —
  emits the action with `Authorization::Custom { predicate:
  WitnessedPredicate::BlindedSet { ... } }` and the right witness
  shape; computes the predicate input from the action.

- **`introduce!(introducer, recipient, target, perms)`** — already
  has a builder; the macro version unifies cross-federation and
  same-federation variants.

- **`broadcast_pull!(publisher, topic, payload)`** — emits the
  publisher's update with appropriate `Monotonic` constraints
  pre-checked; produces `WitnessedPredicate::MerkleMembership`
  shapes for subscribers' later pulls.

These are *Rust*, not new AIR. They lower to existing primitives.
The author of an app should not have to remember "for a ring trade,
emit N transfers with these specific call_forest annotations;" the
macro emits it.

### 7.3 Do expose γ.2 counts as slot-readable state

This closes the §3.2.2 ergonomic gap (M-of-N over γ.2 counts).

Mechanically: a cell's program can declare an *imported* slot whose
value is the γ.2 `INBOUND_TRANSFER_COUNT` (or any of the seven
counts) from this turn's per-cell PI. The slot is read-only from
the program's perspective. `StateConstraint` can then enforce
predicates over it (`Monotonic`, `Equals`, `RangeBound`).

This requires a small extension to `CellProgram::Cases`'s
`TransitionCase::constraints` vocabulary (or `Preconditions`) to
reference γ.2 PI fields by index. It is an additive change, *not* a
new primitive.

### 7.4 Do consolidate Custom-authorization composition

`Authorization::Custom { predicate }` is currently single-predicate.
For multi-predicate authorizations ("M-of-N AND time-locked AND
within governance window"), we today need `WitnessedPredicateKind::
Custom { vk_hash }` over a hand-rolled conjunction.

A `WitnessedPredicateKind::All(Vec<WitnessedPredicate>)` or
`WitnessedPredicateKind::Any(Vec<WitnessedPredicate>)` would
let app authors compose authorization predicates without writing
a new AIR. This is *also* ergonomic, not algebraic — the AIR
already supports conjunction via predicate-program composition
(see `circuit::compound_predicate_air` and `circuit::predicate_program`).

### 7.5 The single architectural recommendation

> **γ.2 pairwise + `Authorization::Custom` + `StateConstraint` + `AttestedRoot`
> chains are the right primitive set. The next investment is a high-level
> DSL macro surface that mints common multilateral patterns as
> compositions, plus surfacing γ.2 counts as slot-readable state for
> `StateConstraint` consumption. No new algebraic primitives at the AIR
> layer.**

This sets up the work in `FEDERATION-AS-CELL.md`: if the algebraic
primitive set is closed, then asking "is a federation a cell" becomes a
*structural* question (what abstraction unifies them?) rather than an
*algebraic* question (what new primitive do we need?). The structural
answer is the `Principal` shape proposed there.

---

## §8. Worked-example appendix

### 8.1 Atomic 3-party swap A↔B↔C

**Goal:** A sends 10 to B, B sends 20 to C, C sends 30 to A; all-or-
nothing.

**Turn body:**
```
Turn {
    agent: A,  // who signed
    effects: [
        Effect::Transfer { from: A, to: B, amount: 10 },
        Effect::Transfer { from: B, to: C, amount: 20 },
        Effect::Transfer { from: C, to: A, amount: 30 },
    ],
    authorization: Signature(...)  // A's; B and C are touched but didn't sign
    ...
}
```

But wait — B and C didn't authorize? This is the bilateral-authority
problem. Either:

- A holds *capabilities* over B and C that let A move their balances
  (uncommon; this is the "delegated agent" pattern), or
- The Turn is multi-actor — needs `Authorization::Custom` with three
  embedded signatures over the canonical message.

The second is the common pattern. Pseudo:
```
authorization: Authorization::Custom {
    predicate: WitnessedPredicate::Custom {
        vk_hash: THREE_PARTY_RING_VK,
        // proof: witness contains signatures from A, B, C
    }
}
```

γ.2 bindings emerge naturally: three pairwise edges in the call_forest;
each pair of incident cells produces matching `OUTBOUND/INBOUND_TRANSFER_*`
accumulator entries.

**Verifier check:** schedule has three transfer entries; each cell's
PI count = (1 outbound, 1 inbound); root match; auth witness verifies.

**Closure ("the ring closes")** is not γ.2's job — it's the call_forest's
declaration plus the per-cell program's balance invariant.

### 8.2 5-of-7 governance vote on a namespace

**Goal:** the governed-namespace cell only mutates if 5 of 7 committee
members co-sign.

**Turn:**
```
Turn {
    agent: governed_namespace_cell,
    effects: [Effect::Custom { ... mutation ... }],
    authorization: Authorization::Custom {
        predicate: WitnessedPredicate {
            kind: BlindedSet,
            commitment: committee_merkle_root,
            input_ref: SigningMessage,
            proof_witness_index: 0,
        }
    }
}
```

The witness blob at index 0 contains 5 signatures over the canonical
signing message; the AIR verifies each is from a committee member
and `count >= threshold`.

γ.2: not involved (single-cell turn). Pairwise binding has nothing to
bind.

### 8.3 Cross-federation bridge: dregg A → Midnight B

**Goal:** A on federation `F_p` sends 100 STARS to B on Midnight.

**Phase 1 (dregg side):** A's federation produces a turn locking 100
STARS in a bridge cell on `F_p`. γ.2: pairwise Transfer (A → bridge_cell).

**Phase 2 (witness):** federation `F_p` emits an `AttestedRoot`
including the lock event. `AttestedRoot::is_valid` over `F_p`'s
committee.

**Phase 3 (Midnight side):** Midnight contract sees the lock event
(via observer); mints 100 STARS to B. This is *off-dregg*, on
Midnight; no γ.2.

**Phase 4 (optional refund):** if Midnight mint fails, a refund turn
on `F_p` releases the lock. Causal chain via WR.

γ.2 binds only intra-dregg. Cross-fed binding is the AttestedRoot
chain + Midnight contract verification.

### 8.4 Publisher fans out to 1000 subscribers

**Goal:** publisher updates a PubSubTopic; 1000 subscribers eventually
pull the new entry.

**Publisher's Turn:** mutates the PubSubTopic cell's `head` slot
(`Monotonic` constraint). Single-cell turn (publisher owns the topic).
γ.2: not involved.

**Each subscriber's Turn (separate, async):** subscriber's cell
mutates its own cursor slot; carries `Authorization::Signature` plus
optionally a `WitnessedPredicate::MerkleMembership` over the topic's
state commitment proving "the entry I'm consuming was in the topic
at commitment X." γ.2: not involved (subscriber's turn touches only
their own cell).

Pairwise composition: zero pairs needed. The pattern is *not γ.2-shaped*.

---

## §9. Threats to the verdict

Honestly: where could the "no new primitive needed" claim be wrong?

### 9.1 Performance pressure on giant rings

If an app routinely produces ring trades over 100+ legs, the per-cell
Poseidon2 accumulator absorb cost dominates and the schedule
reconstruction in the verifier becomes large. γ.2 Phase 2's outer
aggregation AIR (`STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`) caps the
verifier cost to O(1) in N_cells but at the prover-side cost of a
recursive verifier per inner proof. At N=100+, this may push toward
a *dedicated ring-trade AIR* with a single trace.

**My read:** this is hypothetical until we see the workload. The
existing orderbook ring trades are 2-4 legs. Defer.

### 9.2 An app that genuinely needs sealed multilateral

If an app needs "M cells out of N committed to this multilateral
action, but the verifier should not learn which M," γ.2 doesn't
hide identities; the schedule reconstruction names every
participant. A privacy-preserving multilateral primitive would
need a *zero-knowledge set membership* shape, not γ.2.

**My read:** this is the territory of `BlindedSet` /
`MerkleMembership` predicates plus a sealed call_forest. The
seal layer exists (`cell::seal`) but isn't yet integrated with
γ.2; this is a *composition* exercise, not a new primitive.

### 9.3 Non-Turn-shaped coordination

If we found ourselves wanting "this coordination spans multiple
turns and isn't expressible as a causal chain" — e.g., a
synchronous multi-round protocol where each round's commitments
gate the next — the current model would strain. But this is what
intent matching (`intent::matcher`) and commit-reveal-fulfillment
(`intent::commit_reveal_fulfillment`) already handle as
multi-turn flows. The blocklace orders the turns; each turn
references the prior's commitments.

**My read:** the current shape covers it. No primitive gap.

---

## §10. Closing

γ.2 Phase 1 is enough algebra. The gap, where there is one, is
*ergonomics*: composing pairwise + Custom + slot caveats for
common multilateral patterns is verbose. The right next move is
the DSL macro surface in §7.2, not new primitives.

This sets up the deeper question: if the algebraic primitive set
is closed, what is the *structural* abstraction that unifies cells
and federations? That's `FEDERATION-AS-CELL.md`.

The one-line recommendation, restated:

> **γ.2 + Custom auth + slot caveats are the primitive set. Invest in
> DSL macros and `StateConstraint` access to γ.2 counts. Do not add
> algebraic primitives at the AIR layer.**
