# SLOT-CAVEATS-EVALUATION — critiquing Lane G's `StateConstraint` lift

**Date:** 2026-05-24. **Status:** evaluation, read-only on code. **Companion:**
`SLOT-CAVEATS-DESIGN.md` (Lane G).

The designer asks: *is the 14-variant proposal comprehensive enough?*
This document walks the question against (1) the temporal predicate
DSL that already exists, (2) every retained starbridge app, (3) the
non-cell-program surfaces in `turn/`, (4) candidate additional
variants, (5) the `Custom` escape, (6) the lifted-enum-first
decision, and (7) gives a final verdict. Throughout, I take the
opposite stance from the design where useful — my job is to find
what was missed.

The headline: **the 14 variants are a solid 80% of comprehensive.**
The set is **not yet sufficient for the retained app surface** as
written, and there are at least three load-bearing gaps. None of
them invalidate the lift — they're additions to it. Two also
involve renaming or re-shaping existing variants.

---

## §1. Coverage against the temporal predicate system

### 1.1 What `temporal_predicate_dsl.rs` actually expresses

The temporal DSL (`circuit/src/temporal_predicate_dsl.rs:1-922`) is a
**very narrow predicate**, narrower than its name suggests. It
proves a *single* claim:

> Given a sequence of `values[]` and matching `state_roots[]`,
> some `predicate_type` over `(values[i], threshold)` held at
> every step.

Mechanics:

- `predicate_type ∈ { Gte | Lte | Gt | Lt | Neq | InRangeLow |
  InRangeHigh }` (7 variants — line 200-209 of temporal_predicate_dsl.rs).
- Compiled to a 37-column AIR with `(value, threshold, diff,
  diff_bits[30], accumulator, step_index, …)`. Boundary constraints
  pin `accumulator = num_steps`.
- The proof is bound to `(initial_state_root, final_state_root,
  num_steps, threshold)` as public inputs.
- `TemporalPredicateRequirement` (lines 469-494) is the **intent-side
  shape**: `(attribute_name, predicate_type, threshold,
  min_duration_steps)` — what an intent-matcher's counterparty must
  prove.

**Crucial observation.** The temporal DSL is the *witness-supplied*
form of "over an N-step window, my values satisfied a predicate
against a fixed threshold." It is the proof a **counterparty
attaches to an intent match**, not a constraint a cell program
enforces. The state roots are *bindings to a receipt/IVC chain*
(`stark_proof` lines 396-411), not slots on a cell.

### 1.2 What this means for `StateConstraint` coverage

The 14 variants do not — and **should not** — express the temporal
DSL's claim. `StateConstraint` is per-transition; the temporal DSL
is per-window-of-transitions. These are different orders of binding:

- **`StateConstraint`** runs at `evaluate(new_state, old_state, ctx)`
  time. One pair of states, the most-recent step.
- **`TemporalPredicateProof`** runs across an N-step horizon and
  binds to the receipt chain root.

So §1's bullet point in the brief — "is everything the temporal
DSL can express covered by 14 variants?" — has a clean answer:
**no, and that's correct.** The temporal DSL operates at a different
scope. The audit calls out that some of the same shapes (Gte/Lte/Gt/Lt)
appear in both, but they're operating on different objects.

### 1.3 The actual coverage gap: `StateConstraint::TemporalDuration`

Where the temporal DSL *would* show up as a `StateConstraint` is
when an app wants to say: **"this cell's behavior over a sliding
window has satisfied a predicate, proven by attached witness."**

Today the `StateConstraint::Custom { hash, description }` escape
catches this, but it's the worst fit — the predicate isn't a state
test, it's a *proof-attached predicate* whose verification key and
public-input shape are well-known. The right shape is a *first-class
variant*:

```rust
TemporalPredicate {
    /// Witness slot — the cell's slot holding `Commitment(values[])`.
    values_commitment_index: u8,
    /// Predicate kind (mirror PredicateType).
    kind: PredicateKind,
    threshold_index: u8,
    /// Window length the cell program demands.
    min_duration_steps: u32,
    /// The verifying-key identifier (TemporalPredicateAir is fixed,
    /// so this could be a constant — but other DSL-authored windowed
    /// predicates would slot in here).
    proof_kind: TemporalProofKind,
}
```

Verification: at executor time, the action must carry the
`TemporalPredicateProof` matching this slot's claim. The executor
calls `verify_temporal_predicate(proof, threshold, num_steps,
initial_root, final_root)` (already exists — line 421-458).

**Apps that need this:** `compute-exchange` (the brief's headline
use case — temporal uptime predicates for SLA tier qualification),
`bounty-board` (worker standing proof), `gallery` (gated-auction
qualification), `identity` (IVC standing — "I have held this
credential for ≥N blocks").

**Verdict:** The 14 variants are missing the **witness-attached
predicate** family. `Custom` covers the *raw fallback*, but
witness-attached predicates with a known proof schema are
common enough they deserve their own variant — call it
`TemporalPredicate` or, more generally, `ProofAttached { circuit_id,
expected_pi: ProofPiSpec }`. Same shape as
`EscrowCondition::ProofPresented` (which is itself broken per
DREGG-FLAWS G3 — `verification_key: [u8;32]` is the wrong shape).
Adding it here fixes both surfaces simultaneously.

---

## §2. Coverage against the retained-apps audit and STARBRIDGE-APPS-PLAN

I walk each surviving starbridge-app and name (slot, rule, variant).

### 2.1 `nameservice`

| Slot | Rule | Variant |
|---|---|---|
| `NAME_HASH_SLOT` | write-once after first registration | `WriteOnce` ✓ |
| `EXPIRY_HEIGHT_SLOT` | monotonic (only extends) | `Monotonic` ✓ |
| `EXPIRY_HEIGHT_SLOT` | at write, must be in future | `FieldGteHeight` ✓ |
| rent extension | `expiry += epoch_len` exactly | `FieldDelta` ✓ |
| treasury balance | `balance == sum(rent_paid)` | `SumEquals` ✓ |
| **owner pubkey hash** | **set once on register, immutable afterward** | `Immutable` ✓ — but this also conflicts with `WriteOnce`. See §2.9. |
| **sub-delegation prefix** | **owner cap delegated only under prefix P** | **NOT COVERED.** This is the audit §1.4(e) `Caveat::ResourcePrefix` shape — a *capability-side* caveat, not a slot-state predicate. Out of scope for `StateConstraint`. |
| **rent payment ↔ extension link** | **"if `expiry` advanced by N epochs, then treasury balance advanced by N×epoch_rent"** | **PARTIAL** via `SumEqualsAcross` if the rent_paid and expiry_delta are in the same cell. If they're across two cells (treasury + per-name), this is the **cross-cell binding** problem (γ.2). Not covered. |

**Coverage: 6/8 slot-rules covered; 1 cross-cell, 1 capability-side.**

### 2.2 `identity`

| Slot | Rule | Variant |
|---|---|---|
| `SCHEMA_HASH` (issuer cell) | immutable post-creation | `Immutable` ✓ |
| `ISSUED_COUNT` | monotonic | `Monotonic` ✓ |
| `REVOCATION_ROOT` | monotonic (Merkle insertions only) | `Monotonic` ✓ |
| **credential issued by registered issuer** | sender ∈ issuer set | `SenderAuthorized` ✓ |
| **presentation = proof, not state** | not a slot at all | N/A — `Presented<P>` extractor |

**Coverage: 4/4 slot-rules covered.** Identity is the cleanest fit
because its on-chain state really is just a few monotone-updating
roots.

### 2.3 `subscription`

| Slot | Rule | Variant |
|---|---|---|
| `EPOCH_SLOT` | monotonic, increments by 1 | `MonotonicSequence` ✓ |
| `RATE_LIMIT` per subscriber | one debit per epoch | `RateLimit` ✓ |
| `TIER_SLOT` | immutable post-create | `Immutable` ✓ |
| **payment authorized by delegated token** | sender = subscriber-key OR delegated-from = subscriber-key | **PARTIAL.** `SenderAuthorized` covers single-key; delegation chains are not modeled. See §3 below. |
| **debit only during active window** | between subscribe and cancel | `TemporalGate` with `not_before`/`not_after` ✓ |

**Coverage: 4/5.** The delegation-chain authorization model is the
boundary between caveats and state constraints (see §3.1).

### 2.4 `governed-namespace`

| Slot | Rule | Variant |
|---|---|---|
| `PROPOSAL_ROOT` | monotonic | `Monotonic` ✓ |
| `CURRENT_EPOCH` | monotonic | `Monotonic` ✓ |
| `THRESHOLD` | immutable | `Immutable` ✓ |
| `VOTES_FOR/AGAINST` (per proposal) | monotonic | `Monotonic` ✓ |
| `PAYLOAD_HASH` | immutable | `Immutable` ✓ |
| **atomic enactment requires M-of-N vote-witnesses** | **NOT COVERED.** This is "M-of-N caveat discharge across multiple authorizations" — a turn-level conjunction over caveats, not a slot predicate. The cell program could approximate via `SenderAuthorized` against a *witness-set root that itself encodes the threshold*, but that's stretching the variant past its design. |
| **route-table swap is atomic with proposal-accepted flag flip** | **PARTIAL** — `BoundedBy { index: route_table_root, witness_index: accepted_flag }`. Fits, but the gating semantics are weak (the witness is just "non-zero," not "specifically Some(accept)"). |

**Coverage: 5/7.** Two gaps; the M-of-N witness pattern is
architecturally distinct from per-slot caveats and probably belongs
in a separate "discharge" vocabulary or in `Action::preconditions`.

### 2.5 `bounty-board`

| Slot | Rule | Variant |
|---|---|---|
| `QUALIFICATION_HASH` | immutable | `Immutable` ✓ |
| `DEADLINE` | future at write, fixed thereafter | `FieldGteHeight` then `Immutable` ✓ |
| `CLAIM_ROOT` | monotonic | `Monotonic` ✓ |
| `STATUS` | bounded state machine (Open→Claimed→Delivered→Paid) | **NOT COVERED.** Needs an **enum-transition predicate**: `new ∈ allowed_transitions(old)`. See §4 (`AllowedTransitions`). |
| **delivery proof verification** | escrow releases on `ProofPresented` | escrow-side, not slot — but the broken `verification_key: [u8;32]` (G3) bites here. |
| **payment to stealth address (private)** | not a slot rule | N/A |

**Coverage: 3/5.** The status state-machine gap is real — every app
with a phase variable (escrow, auction, dispute) wants
`AllowedTransitions`.

### 2.6 `gallery`

| Slot | Rule | Variant |
|---|---|---|
| `ARTIST_COMMIT` | immutable | `Immutable` ✓ |
| `PROVENANCE_ROOT` | monotonic (append-only chain) | `Monotonic` ✓ |
| `BID_AMOUNT` | strictly increasing | **PARTIAL.** `Monotonic` allows `new == old`; strict bids need `new > old`. See §4 (`StrictMonotonic`). |
| `DEADLINE` (auction anti-sniping) | extends by 0..K blocks per turn | `FieldDeltaInRange` ✓ |
| `PHASE` (Commit→Reveal→Closed) | bounded state machine | **NOT COVERED** (same as bounty `STATUS`) |
| **royalty split (winning bid → artist/platform/prior_owner)** | `winning_bid = artist + platform + prior_owner` | `SumEqualsAcross` ✓ (if input/output fields are slots; in practice they're transfer effects in the *same turn* on a different cell — see §3.4 cross-cell) |
| **unique ownership cap** | exactly one cell holds the owner cap | **NOT COVERED.** Audit §4.4(a) calls this `CapabilityUniqueness { cap_kind }`. Belongs in `StateConstraint`; missing from the 14. |
| **anti-replay on settlement** | turn fires at most once | `WriteOnce` on `settled_flag` ✓ |

**Coverage: 5/8.** Three gaps: strict monotonic, state-machine
transitions, capability-uniqueness.

### 2.7 `privacy-voting`

| Slot | Rule | Variant |
|---|---|---|
| `BALLOT_COMMITMENT` per voter | write-once | `WriteOnce` ✓ |
| `PROPOSAL_ID` per voter | immutable | `Immutable` ✓ |
| `NULLIFIER_SPENT` flag | one-shot zero→nonzero | `WriteOnce` ✓ |
| commit-window enforcement | `current_height ∈ [commit_open, commit_close]` | `TemporalGate` ✓ — but the bounds are read from a **separate cell's slot**. See §3.4. |
| reveal-window enforcement | `current_height ∈ [reveal_open, reveal_close]` | same; cross-cell or copied-to-voter-cell |
| **eligibility (membership in voter set)** | sender ∈ electorate | `SenderAuthorized` ✓ |
| **tally is sum of revealed votes** | not a slot rule (it's a STARK over reveal_root) | N/A |
| **nullifier set growth** | monotonic Merkle root | `Monotonic` ✓ |

**Coverage: 7/7 with one footnote.** The window-bounds-in-another-cell
issue is the parameterization gap (§3.5).

### 2.8 `compute-exchange`

| Slot | Rule | Variant |
|---|---|---|
| `JOB_SPEC_HASH` | immutable | `Immutable` ✓ |
| `MATCHED_SELLER` | write-once | `WriteOnce` ✓ |
| `DELIVERY_DEADLINE` | future at write | `FieldGteHeight` ✓ |
| `STATUS` (Open→Matched→Delivered→Settled→Disputed) | state machine | **NOT COVERED** (`AllowedTransitions`) |
| **temporal predicate proof: seller's 100-block uptime ≥ 0.95** | not a slot, a witness-attached proof | **NOT COVERED.** This is §1.3 — `TemporalPredicate` / `ProofAttached`. |
| **paired escrow: payment + SLA bond release/refund atomically** | not a slot rule; cross-cell | **NOT COVERED.** This is γ.2 territory. |
| **SLA penalty pro-rata** | `slash = bond × (overrun / deadline_window)` | **NOT COVERED** — `ExpressionEquals` (Tier-2 #9). |

**Coverage: 3/7.** Compute-exchange is **the integration test that
the 14 variants don't pass.** Four of seven slot-rules are missing
infrastructure. This is consistent with the apps audit §3.7 calling
it "the integration test that lights up every Tier-1 primitive" —
slot caveats alone are not enough.

### 2.9 Aggregate: what the apps say

| Variant | App-coverage |
|---|---|
| `FieldEquals` / `FieldGte` / `FieldLte` | every app uses ≥1 |
| `SumEquals` | nameservice, prediction-mkt (dropped), bounty |
| `WriteOnce` | nameservice, gallery, voting |
| `Immutable` | every app |
| `Monotonic` | every app |
| `BoundedBy` | bounty, gallery, governed-namespace (partial) |
| `FieldDelta` | nameservice (rent) |
| `FieldDeltaInRange` | gallery (anti-sniping), compute-exchange (deadline drift) |
| `FieldGteHeight` | nameservice, gallery, voting, bounty, compute-exchange |
| `FieldLteHeight` | voting (reveal window upper bound) |
| `SumEqualsAcross` | gallery (royalties — but cross-cell) |
| `SenderAuthorized` | gallery, voting, governed-namespace, identity |
| `RateLimit` | subscription |
| `TemporalGate` | voting, subscription |
| `PreimageGate` | voting (reveal), bounty (delivery), gallery (reveal) |
| `MonotonicSequence` | subscription, voting |
| `Custom` | currently *everywhere* there's a gap |

**Per-app gap count:**

- nameservice: 1 (sub-delegation — capability-side, not state)
- identity: 0
- subscription: 1 (delegation-chain auth)
- governed-namespace: 2 (M-of-N discharge, ambiguous BoundedBy)
- bounty-board: 1 (`AllowedTransitions`)
- gallery: 3 (strict mono, `AllowedTransitions`, capability-uniqueness)
- privacy-voting: 0 within slot scope (parameterization gap external)
- compute-exchange: 4 (`AllowedTransitions`, `TemporalPredicate`, paired-escrow, `ExpressionEquals`)

**Aggregate gaps that recur ≥2 apps and belong inside `StateConstraint`:**

1. `AllowedTransitions { index, transitions: Vec<(FieldElement, FieldElement)> }` — 3 apps (bounty, gallery, compute-exchange). State machines are the second-most-common pattern after monotonic counters.

2. `StrictMonotonic { index }` — gallery (and any auction-shape app); semantically distinct from `Monotonic`.

3. `CapabilityUniqueness { cap_kind_index }` — gallery NFT, but also identity (one credential of a kind per holder) and nameservice (one owner per name).

4. `TemporalPredicate { values_commitment_index, kind, threshold, min_duration }` — compute-exchange, bounty-board (standing). The audit's "witness-attached predicate" pattern.

These four are the *real* missing variants, in order of leverage.

---

## §3. Aspects of the `turn/` system the design under-covers

Slot caveats are about per-slot, intra-cell predicates over (old, new,
ctx). The design's scope is narrow on purpose. But several other
predicate primitives live elsewhere in `turn/` and the design's
relationship to them is ambiguous. I walk each.

### 3.1 `Action::preconditions` — Lane H's enrichment

`turn/src/preconditions.rs` (Lane H, just landed) gives
`Precondition::{SlotEquals, SlotZero, NonceAtLeast}` as see-then-set
guards on actions. The relationship to `StateConstraint`:

- **`Precondition`** is *read-only* — "before applying this action,
  assert the cell's current state matches X." Failing causes
  `TurnError::PreconditionFailed`. Evaluated by
  `dregg_cell::CellStatePrecondition::evaluate` before any effect runs.
- **`StateConstraint`** is *transition-checking* — "after applying
  this action, assert the new state passes program-declared invariants."
  Failing causes `ProgramError::ConstraintViolated`. Evaluated after
  state-modifying effects.

These are **distinct surfaces** with overlapping syntax. A
`Precondition::SlotEquals { index, value }` is semantically the
same predicate as a `StateConstraint::FieldEquals { index, value }`
evaluated against the *pre-state*; the difference is *when* and
*whose responsibility*. Preconditions are an action's request to the
cell ("only proceed if X"); state constraints are the cell's
declaration of invariants ("you may not leave me in state ¬Y").

**Should they share vocabulary?** I argue **yes for the predicate
atoms, no for the wrapper enum**. Both should ultimately compose
out of the same predicate language (slot, field, range, hash,
height, sender). But:

- `Precondition` is *per-action*, carried in the wire turn,
  signed-over by the submitter.
- `StateConstraint` is *per-cell*, carried in cell metadata,
  signed-over at cell creation.

Different lifetimes, different signing contexts, different
serialization stability requirements. The design's silence about
this is a defect: there is **no design note in `SLOT-CAVEATS-DESIGN.md`
about how `Precondition` and `StateConstraint` relate**. The two
will diverge unless explicit.

**Recommendation:** Add a §X to `SLOT-CAVEATS-DESIGN.md` clarifying
that `StateConstraint` does NOT subsume `Precondition`, and that
`Precondition` is the right shape for **action-side optimistic
concurrency** (see-then-set against race conditions) while
`StateConstraint` is the right shape for **cell-side invariants**.
The vocabulary atoms (slot-equals, height-bound, sender-membership)
can be co-defined, but the wrappers must stay distinct.

### 3.2 Effect sequencing within a Turn

Lane G doesn't address whether `StateConstraint` can express "this
effect must precede that effect." Today the executor applies effects
in turn order; there's no per-cell "effect E_a fired before E_b"
caveat.

Do any apps need this? Yes:

- **Gallery settlement.** The artist payment must precede the
  capability grant, so that if the payment fails the grant doesn't
  fire either. Today this is implicit (the executor short-circuits
  on effect error within a turn); a `StateConstraint::EffectsOrdered`
  would make it explicit.
- **Voting reveal.** The nullifier mark-spent must precede the
  tally increment. Same shape.

But on examination, this is **NOT a slot constraint** — it's a
turn-level ordering constraint, and the existing per-turn
`call_forest` already imposes an ordering. The right place is
probably `Action::preconditions` or a new `Action::sequencing` field.
Adding `EffectsOrdered` to `StateConstraint` would mix scopes.

**Verdict:** Out of scope for the lift. But Lane G should note it.

### 3.3 Conservation predicates beyond `SumEqualsAcross`

`SumEqualsAcross { input_fields, output_fields }` is the
single-cell, single-asset conservation primitive. Apps need more:

- **Multi-asset conservation.** Lending: `(borrow_a - repay_a) +
  (interest_accrued_a) = 0` simultaneously across N asset slots,
  not just a single sum. The design's variant uses `Vec<u8>` for
  both sides so multi-asset works syntactically, but the *meaning*
  is "sum across these indices" — there's no per-asset typing.

- **Cross-cell conservation.** Gallery royalty: the winning bid on
  the auction cell must equal the sum of transfers from the
  buyer's cclerk cell to artist + platform + prior_owner cells.
  This is the **γ.2 cross-cell binding problem**. `SumEqualsAcross`
  doesn't span cells; γ.2 introduces per-cell PI fields that bind a
  shared `swap_id`. The lift could grow a sibling variant:

  ```rust
  SumEqualsAcrossCells {
      this_cell_input_fields: Vec<u8>,
      shared_binding_id: BindingIdRef,    // → γ.2 PI field
      expected_external_sum: ExpectedSumRef,
  }
  ```

  This is large; probably belongs in a γ.2 follow-on, not the
  initial lift. But the design should call out that
  `SumEqualsAcross` is **intra-cell only**.

- **Ledger-root conservation.** A treasury cell could declare:
  "my balance equals the sum of all `Effect::Transfer` deltas
  bound to my cell-id, signed-rooted in this turn's ledger root."
  This is `BalanceConservation { ledger_root_witness }` from the
  §4 brief — it asks of the *whole ledger*, which is a different
  scope. I evaluate it in §4.

**Verdict:** `SumEqualsAcross` is correct, but the design should
add an explicit note that it does NOT cross cells. The cross-cell
variant is a γ.2 follow-on.

### 3.4 Sovereign-witness verification

Sovereign cells carry their own WR proof. Today the sovereign cell's
program is `CellProgram::Circuit { circuit_hash }` and the executor
verifies via a STARK proof in the action. The 14 variants are
`Predicate`-mode, not Circuit-mode. **Does the sovereign flow need
its own caveat shape?**

Looking at how sovereign cells are used (per `STARBRIDGE-APPS-PLAN.md`),
every retained app uses `Sovereign` via a **factory descriptor**
that bakes in the cell program at construction. The factory's
`field_constraints` are exactly the `StateConstraint` list. So
sovereign cells consume the same vocabulary as non-sovereign — no
separate variant needed.

The wrinkle: **WR replay (scope-2)**. When a sovereign cell's WR is
replayed in a downstream executor, the replay must re-evaluate the
caveat against the asserted (old, new, ctx). The current `evaluate`
signature accepts `Option<&CellState>` for `old_state`; for replay,
the replayer needs the asserted old. The design covers this
implicitly (replay supplies old_state), but it's worth a sentence
in §2 of the design: **"WR scope-2 replay re-evaluates all
StateConstraints using the WR's asserted (pre, post, ctx); failing
constraints reject the replay."**

### 3.5 Cross-cell binding (γ.2) — bilateral schedules

Brief's example: "this slot's delta on cell A equals minus this
slot's delta on cell B" — a bilateral conservation. Today the
γ.2 design (`STAGE-7-GAMMA-2-PI-DESIGN.md`) handles this via
per-cell public-input fields that share a `binding_id`; the
aggregate check happens at the cross-cell match loop in
`turn/src/executor.rs:1747+`.

A `StateConstraint` variant that expresses the per-cell side:

```rust
BoundDelta {
    index: u8,
    expected_delta: BindingIdRef,
    sign: DeltaSign,    // I add, peer subtracts
}
```

The cell program declares "my slot[index] delta in this turn must
match the binding_id's claimed value, with this sign." γ.2's
existing cross-cell match enforces the bilateral sum.

This is **the most under-served variant** in the apps audit:
gallery settlement, orderbook (deleted but the shape is real),
prediction-market ring trades, compute-exchange paired escrow —
every two-sided atomic-swap shape wants it. The design (§5) says
"Phase 6 (deferred) — Storage collapse." Cross-cell binding is
deferred even further. But the *variant* should exist *now* even
if AIR enforcement is later, because apps will declare the
constraint when they're written, and the executor can enforce it
trivially in turn-time given the binding_id field.

**Verdict:** Add `BoundDelta` (or equivalent) to the 14 *now*.
Executor enforcement is straightforward; AIR enforcement can wait.
This is the single most impactful addition.

### 3.6 WitnessedReceipt scope-2 replay

Beyond §3.4: does the replay path need a *slot-caveat replay
primitive* — i.e., a way for the replayer to assert "I re-checked
constraint C; here's the witness"? In principle no — the replay
re-runs `evaluate` and gets the same answer. But two edge cases:

- **`SenderAuthorized` against a slot-held Merkle root.** If the
  set root changed between original turn and replay, the constraint
  may evaluate differently. Solution: the WR snapshots the set root
  at original-turn time; replay uses the snapshotted root, not the
  current one. Design implication: `SenderAuthorized` must carry
  the snapshotted root in its witness, or the WR must include it.

- **`FieldGteHeight` with offset.** `current_height` advances; a
  replay at height H+10 of a turn originally at height H sees a
  different `ctx.current_height`. Solution: replay uses the WR's
  `original_height`, not the current chain height.

The design **does not mention either**. These are real correctness
holes for replay. Should be a §X under "Open questions" or, better,
"Replay semantics."

### 3.7 The Caveat surface (`token/`, `macaroon/`)

The non-state-constraint **caveat** vocabulary lives in
`token/src/dregg_caveats.rs` and `macaroon/`. It includes (per
grep): `Organization`, `App`, `Service`, `Feature`, `ValidityWindow`,
`ConfineUser`, `OauthProvider`, `OauthScope`, `FromMachine`,
`Command`, `FeatureGlob`, `Budget`, `Revocable`, … plus apps-audit-named
`ResourcePrefix`, `EventFilter`, `RateLimit`, `Bond`, `CommitWindow`,
`RevealWindow`, `SubscriptionActive`, etc.

**These are capability-side**, not slot-side. They attenuate **a
bearer's right to act**, not **a cell's state validity**. The two
are dual:

- Slot caveat: "this state transition is valid."
- Capability caveat: "this caller is allowed to attempt the
  transition."

The design's `SenderAuthorized` is the only variant that crosses
from "validity" toward "authorization." It belongs in
`StateConstraint` because the *cell* declares its sender-set;
not because the bearer's capability happens to have a
sender restriction.

**Recommendation:** Make this explicit in §1 of the design. Two
sentences:

> `SenderAuthorized` is the lone overlap with the capability-caveat
> vocabulary. It declares **the cell's accepted sender set** as a
> state invariant; the capability-side `Caveat::ResourcePrefix`
> and friends remain disjoint, attenuating *bearers*, not
> *states*.

Without this paragraph, future authors will be confused about
which variant belongs where.

---

## §4. The proposed additional variants — accept/reject/refine

The designer named 8 candidate additions. I evaluate each.

### 4.1 `FieldHash { index, hash_kind, witness_index }`

"Slot must hash to a published commitment."

**Reject as a separate variant.** This is `PreimageGate
{ commitment_index }` from the lift, read the other way: the
witness slot holds the preimage, the commitment slot holds the
hash. The design's `PreimageGate` covers this if the spec is
"new[witness_index] is the preimage of slot[commitment_index]."
The proposed `FieldHash` adds `hash_kind` parameterization
(Poseidon2 vs. BLAKE3); that's worth doing, but as a refinement
to `PreimageGate` (`PreimageGate { commitment_index, hash_kind:
HashKind }`), not a new variant.

**Refined recommendation:** `PreimageGate { commitment_index,
hash_kind: HashKind = Poseidon2 }`. Drop `FieldHash`.

### 4.2 `Conditional { if_constraint, then_constraint }`

"Gating constraints on other constraints."

**Reject.** Composability through `if/then` rapidly becomes a
mini-language; once you have `Conditional` you also want `Else`,
short-circuit eval semantics, fixpoint convergence rules. That's a
DSL. The right shape is to push complex conditionals into the
**DSL surface** (§3 of the design) and have the compiler emit
either a named variant if it matches, or `Custom` with a registered
expression. Apps that need conditional logic should author it as a
`#[dregg_caveat]` function, not as nested enum variants.

**Verdict: reject.** Push to DSL.

### 4.3 `OneOf { variants: Vec<StateConstraint> }`

"Disjunctive constraints."

**Refine — keep as `AnyOf`.** OR-of-predicates is genuinely useful
and not expressible in the current conjunction-only `Predicate`
shape. Example: voting commit window — "either we're in the commit
window (`TemporalGate(commit_open, commit_close)`) OR we're in the
reveal window (`TemporalGate(reveal_open, reveal_close)`); commits
allowed in former, reveals in latter, and a slot's transition
constraint depends on which window we're in." Without `AnyOf` this
is `Custom`.

But: `AnyOf` is a meta-operator over variants, which can recurse.
Bound it: `AnyOf { variants: Vec<StateConstraint>, depth: 0 }`
(only one level deep, no nested `AnyOf`). Or, cleaner:
`AnyOf { simple_variants: Vec<SimpleConstraint> }` where
`SimpleConstraint` is a flat subset (no `AnyOf`, no `Custom`).

**Verdict: accept as `AnyOf` with depth restriction.** Apps that
need deeper disjunction fall through to `Custom`.

### 4.4 `AllOf { variants }`

"Conjunctive (currently implicit; explicit might help)."

**Reject.** The current `CellProgram::Predicate(Vec<StateConstraint>)`
*is* `AllOf` by construction. Adding `AllOf` as a variant of
`StateConstraint` is redundant — you'd just have
`CellProgram::Predicate(vec![AllOf(vec![X, Y])])` instead of
`CellProgram::Predicate(vec![X, Y])`. Don't add ceremony.

If `AnyOf` is added (§4.3), the implicit conjunction at the outer
level still holds: a list of constraints means "all hold"; an
`AnyOf` inside means "this group requires only one."

**Verdict: reject as redundant.**

### 4.5 `WindowedSum { index, window_height, max_sum }`

"Rate-limit-by-sum."

**Accept, but rename.** This is `RateLimit` extended to sum
*values*, not count *occurrences*. Subscription's per-epoch
debit-amount cap, gallery's per-block bid-amount cap, lending's
per-day borrow-cap — all want this. The variant is genuinely
distinct from `RateLimit` (which counts events).

Rename to `RateLimitBySum { index, window_height, max_per_window }`.
The executor maintains a per-(cell, slot, window) running sum,
keyed to ctx.current_height.

**Verdict: accept.**

### 4.6 `EpochBoundary { transition_rule }`

"What's allowed at epoch boundaries."

**Reject.** The epoch boundary itself is a parameter of
`TemporalGate { not_before, not_after }` — for "only allowed in
epoch K" use `TemporalGate { not_before: epoch_k_start, not_after:
epoch_k_end }`. For "only allowed *at* the epoch transition" — that
is, exactly one block at the boundary — wrap `TemporalGate` with
narrow bounds. The `EpochBoundary` variant adds nothing beyond
naming convenience.

If epoch transitions need special semantics (e.g., "this transition
resets the rate-limit counter"), that's an *executor* property of
`RateLimit`'s `epoch_duration` field — already in the design.

**Verdict: reject as redundant.**

### 4.7 `BalanceConservation { ledger_root_witness }`

"At-the-ledger conservation."

**Accept, but defer.** This is the cross-cell conservation shape
from §3.3. Bound to the ledger root rather than to specific cell
fields. Useful for treasury cells that want to assert "my balance
equals the sum of all in-flight transfers to me, in this turn,
across the whole ledger."

But: this requires the *executor* to provide the ledger-root
witness, and the AIR side requires a Merkle-membership gadget that
opens N transfer commitments against the ledger root. That's a
larger lift than the rest of the 14, and the only apps that want it
are treasury / clearing-house shapes that aren't in the retained
app set.

**Verdict: accept conceptually, defer implementation until γ.2 lands
and an app demands it.** Document as a future variant.

### 4.8 `BlindedAuthorized { commitment }`

"Sender membership via blinded set."

**Reject as a separate variant.** This is `SenderAuthorized`
where the set is committed-blinded (the cell only knows the
commitment, not the membership). The variant already exists; the
difference is that the witness side carries a *non-revocation*
proof against the blinded commitment, not a Merkle membership
proof against an open root. The variant *should* support both, by
allowing `set_root_index` to point at either:

- a public Merkle root (existing behavior), or
- a Poseidon2-committed blinded set root, with the witness being
  a non-revocation DSL proof (`circuit::dsl::revocation`).

Add to `SenderAuthorized`'s spec: "the root may be blinded; the
authorization witness chooses the proof kind." Don't split the
variant.

**Verdict: refine `SenderAuthorized`, don't add new variant.**

### 4.9 Synthesis of §4

**Accept:** `AnyOf` (refined), `RateLimitBySum`.
**Refine:** `PreimageGate` (add `hash_kind`), `SenderAuthorized`
(allow blinded sets).
**Defer:** `BalanceConservation`.
**Reject:** `FieldHash`, `Conditional`, `AllOf`, `EpochBoundary`,
`BlindedAuthorized`.

Net: **+2 new variants beyond the 14, plus refinements to 2
existing.** Combined with the §2 gaps (`AllowedTransitions`,
`StrictMonotonic`, `CapabilityUniqueness`, `TemporalPredicate`)
and §3.5 (`BoundDelta`), the **comprehensive set is 20 variants,
not 14**.

---

## §5. The `Custom` escape hatch — audit and discipline

### 5.1 What the design says

§8 of `SLOT-CAVEATS-DESIGN.md`: dregg-dsl compiler "emits
`StateConstraint::Custom { constraint_hash, description }` and
registers the compiled expression in the runtime's expression
table (audit §3.4(b)'s 'ExpressionEquals')."

The current `cell::program::StateConstraint::Custom` only has
`constraint_hash: [u8; 32]`; the lift adds `description: String`,
mirroring `storage::programmable::QueueConstraint::Custom { expr:
String, description: String }`.

### 5.2 What `Custom` actually verifies

**Today (cell-program side):** Nothing. `evaluate_constraint`'s
`StateConstraint::Custom { constraint_hash }` arm returns
`Err(ProgramError::CustomConstraintUnevaluable { constraint_hash })`
— it cannot be evaluated locally (`cell/src/program.rs:267`).
Custom constraints today *fail closed*.

**Per the lift:** "the runtime's expression table (the dregg-dsl
runtime)." So `Custom` becomes evaluable via a runtime registry
keyed by `constraint_hash`, with the DSL providing the compiled
expression. This is the §3.4(b) `ExpressionEquals` audit shape.

### 5.3 The discipline problem

`Custom` is the junk drawer. Every gap above (state machines,
strict mono, capability uniqueness, temporal predicates) falls into
`Custom` if not given its own variant. That has three failure modes:

1. **Cross-implementation drift.** Two dregg implementations
   register different expressions under the same `constraint_hash`
   (or worse, *can't* register the expression and just trust the
   `description`). The hash is supposed to bind, but without a
   canonical compiler, "the hash of what?" is undefined per-app.

2. **AIR enforcement is impossible.** Per §4 of the design, "the
   `Custom` variant has no AIR shape regardless." So every
   `Custom` constraint is permanently executor-trusted. The more
   apps fall into `Custom`, the larger the trusted base.

3. **Audit-tool blindness.** A cclerk showing the user "this
   cell has constraints: WriteOnce on slot 0, Monotonic on slot 1,
   Custom (escrow_release_predicate_v3)" gives the user no real
   information about what `escrow_release_predicate_v3` actually
   does. The `description` is a string, not a proof of behavior.

### 5.4 Discipline proposals

To keep `Custom` from becoming the catch-all:

**(a) The "promotion rule."** Any `Custom` predicate used by ≥2
apps must be promoted to a named variant. The DSL compiler emits a
**diagnostic warning** when emitting `Custom { description }` whose
description matches another existing `Custom` in the registry —
prompting designers to add a named variant.

**(b) Expression table is content-addressed and canonical.** The
`constraint_hash` is **the hash of the compiled DSL IR**, not an
arbitrary blob. Two implementations must produce identical IRs from
identical source, or the lookup fails. The dregg-dsl compiler emits
a stable serialized IR; the hash is over that. (Implementation
note: this is what `dregg-dsl/src/ir.rs` should expose as a
canonical postcard schema.)

**(c) `Custom` must declare its read-set.** `Custom { hash,
description, reads: ReadSet { slots: Vec<u8>, ctx_fields: Vec<CtxField> } }`.
The read-set is the **subset of (state, old_state, ctx)** the
custom predicate touches. The executor can:
- Compute the AIR commitment to (old, new, ctx) restricted to the
  declared read-set.
- Verify the DSL runtime evaluates only what it declares.
- Show users "this custom predicate reads slots [0, 3, 5] and
  current_height; nothing else."

This gives `Custom` enough *structural transparency* that audit
tools can reason about it without executing the predicate.

**(d) Description field is not free-form.** Pin the format:
`description: CustomDescriptor` where `CustomDescriptor` is a small
struct with `(human_name: String, semver: SemVer,
authoring_package: PackageRef)`. Free-text descriptions invite
drift; structured descriptors enable indexing.

### 5.5 Verdict on `Custom`

**As designed, `Custom` is too permissive.** Specifically:
`constraint_hash: [u8; 32]` is opaque, no read-set declaration,
no IR-canonicality requirement, `description: String` is free-text.
This will become a junk-drawer unless §5.4(a-d) are adopted.

**Recommendation:** Adopt the four discipline proposals. The lift
should land with:

```rust
Custom {
    /// Hash of the canonical DSL IR (dregg-dsl).
    ir_hash: [u8; 32],
    /// Structured human/version descriptor.
    descriptor: CustomDescriptor,
    /// Declared read-set — what slots/ctx fields the predicate touches.
    reads: ReadSet,
}
```

This is a heavier shape but keeps `Custom` from being structurally
opaque.

---

## §6. The lifted-enum-first v1 decision

The designer (in the brief, not the design doc) proposes skipping
Lane G's predicate-shaped DSL for v1 and just exposing the enum
variants directly. The design doc itself argues *for* the DSL
surface (§3); the brief revisits.

**My critique.** I argue the lifted-enum-first decision is correct
for v1, with one caveat.

### 6.1 In favor of lifted-enum-first

- **The 14 named variants cover ≥80% of the apps.** §2 above
  showed that every retained app's slot-rules map to a small set
  of named variants. The DSL is mostly redundant — what the apps
  need is **direct enum-literal construction**, which is what
  factory descriptors do anyway.

- **`StateConstraint` is a stable wire format.** Cells carry their
  programs in metadata; the program is signed at cell-creation.
  Adding a DSL layer means cell programs are *compiled artifacts*
  whose stability depends on the compiler's stability. Today's
  vocabulary is a closed Rust enum with `Serialize/Deserialize` —
  trivially stable.

- **AIR enforcement is variant-keyed.** Per §4 of the design,
  per-variant AIR enforcement is the eventual path. That requires
  a closed enum, not a DSL. If we ship the DSL first, every
  predicate that compiles to `Custom` permanently bypasses AIR
  enforcement.

- **App devs already write Rust.** Every retained starbridge-app
  is a Rust crate. Writing `StateConstraint::WriteOnce { index: 0 }`
  directly is no harder than writing a `#[dregg_caveat]` function;
  the former is more explicit about what's being declared.

- **The DSL is unsound for v1 anyway.** §3 of the design admits
  the pattern-matcher is best-effort: "the compiler emits the
  most-specific named variant if the predicate pattern-matches a
  named one; otherwise emits `StateConstraint::Custom`." So the
  DSL is *already* a glorified named-variant constructor for the
  common case, plus an escape hatch. The construction syntax
  itself isn't load-bearing.

### 6.2 Against lifted-enum-first (mild)

The single argument for the DSL is **composition over multiple
slots in a single predicate**. The 14 enum variants are mostly
per-slot; a custom predicate like "(slot 0 == 0) AND (slot 1 > slot
2)" requires either `Custom` (lose AIR-enforceability) or a new
variant per pattern (lose closed enum). The DSL would let app devs
write composite predicates that compile to compositions of named
variants.

But — looking at the apps in §2 — **no retained app actually
needs cross-slot composite predicates beyond what `SumEquals`,
`SumEqualsAcross`, and `BoundedBy` already cover**. The composite
patterns that do exist (M-of-N discharge, state-machine
transitions, capability uniqueness) need new *variants*, not
multi-slot DSL expressions.

### 6.3 The caveat

**Ship the lifted enum directly; defer the DSL.** But include the
discipline of §5.4 — `Custom`'s shape — so that when the DSL lands,
it has somewhere to compile to.

Concretely:

- **v1 (this lift):** the 20-variant enum, plus a more-structured
  `Custom { ir_hash, descriptor, reads }`. App authors write
  `StateConstraint::*` literals directly. The Rust enum is the
  authoring surface.
- **v2 (later):** `dregg-dsl` adds the `#[dregg_caveat]` attribute
  macro, which **emits one of the 20 named variants** when the
  predicate pattern-matches, falling back to `Custom { ir_hash, … }`
  only for genuinely novel predicates. The DSL is **a sugar layer
  over the enum**, not a replacement.

This sequence matches Silver Vision's "make it run correct first,
make it pretty second." The enum-first decision is right.

---

## §7. Recommended additions — final verdict

The 14 variants are **necessary but not sufficient**. Order by
impact:

### 7.1 Must-add before v1 ships

**(impact: ≥3 retained apps blocked, currently fall through to
`Custom`)**

1. **`AllowedTransitions { index, transitions: Vec<(FieldElement,
   FieldElement)> }`** — state-machine variant. Used by bounty
   (`status`), gallery (`phase`), compute-exchange (`status`). Three
   apps that each end up using `Custom` today.

2. **`StrictMonotonic { index }`** — `new[i] > old[i]`, distinct
   from `Monotonic` (`>=`). Auction bids, sequence numbers in some
   regimes. Distinct enough from `Monotonic` to be a separate
   variant.

3. **`BoundDelta { index, expected_delta: BindingIdRef, sign }`** —
   cross-cell binding shape, paired with γ.2 PI. Critical for
   gallery settlement, paired escrow, prediction-market ring trades.
   Executor-side enforcement is trivial today; AIR enforcement
   follows γ.2.

### 7.2 Should-add before v1 ships

**(impact: 1-2 apps, but novel pattern unrepresented)**

4. **`TemporalPredicate { values_commitment_index, kind, threshold,
   min_duration_steps }`** — the witness-attached predicate. The
   only known consumer is compute-exchange's headline use case;
   bounty-board's worker-standing is similar. The shape is
   well-defined (`circuit/src/temporal_predicate_dsl.rs`) and the
   verifier exists. Adding this also clarifies that `Custom` is
   for unknown predicates, not common-but-windowed ones.

5. **`CapabilityUniqueness { cap_kind_index }`** — gallery NFT
   ownership, also nameservice "one owner per name" and identity
   "one credential of kind X per holder." The audit calls this
   `StateConstraint::CapabilityUniqueness { cap_kind: u32 }`
   directly.

6. **`AnyOf { variants: Vec<SimpleStateConstraint> }`** —
   single-level disjunction. Apps that mix commit/reveal windows
   need it; without it, the design over-relies on `Custom`.

7. **`RateLimitBySum { index, window_height, max_per_window }`** —
   sum-based rate limiting (distinct from event-count `RateLimit`).
   Subscription per-epoch debit cap, lending per-day borrow cap.

### 7.3 Refinements to the existing 14

8. **`PreimageGate`** should take `hash_kind: HashKind` (Poseidon2
   default; BLAKE3 supported for legacy commitments).

9. **`SenderAuthorized`** should support blinded sets (the
   `set_root_index` can point at either a public Merkle root or a
   committed blinded root; the witness-side proof selects the
   verifier).

10. **`Custom`** should grow to `Custom { ir_hash, descriptor:
    CustomDescriptor, reads: ReadSet }` per §5.4.

11. The `EvalContext` struct **must avoid the name collision** with
    `dregg_cell::preconditions::EvalContext` (which exists today
    and has `block_height: u64, timestamp: i64`). Either
    extend the existing struct, or name the new one
    `StateConstraintCtx`. Lane G missed this; it's a compile
    error waiting to happen.

### 7.4 Defer to v1.x

12. **`BalanceConservation { ledger_root_witness }`** — only
    treasury / clearing-house apps want it; none in the retained set.

13. **`SumEqualsAcrossCells`** — γ.2-dependent; ship after γ.2 lands.

14. **DSL surface** — defer per §6. Direct enum-literal
    construction is sufficient for v1.

### 7.5 What the design recovers from the queue side that the lift drops

Lane G's lift drops three storage-side `QueueConstraint` variants:

- `ContentPattern { required_prefix: Vec<u8> }` — content-byte
  pattern matching. The slot-side analog is *not* needed (slot
  values are fixed 32-byte fields, not variable-length payloads).
  Drop intentionally; document.
- `MinDeposit { amount: u64 }` — the queue requires per-message
  deposits. The slot-side analog is `FieldGte { index: deposit_idx,
  value: min_deposit }`. Already covered.
- `MaxSize { bytes: usize }` — message size cap. Cells have fixed
  STATE_SLOTS=8; no analog needed. Drop intentionally.

This is **correct dropping**, but Lane G's design doesn't
explicitly explain why these don't lift. One paragraph in §5
("Migration story") would close the question.

### 7.6 Final count

20 variants:

```
4 static post-state:    FieldEquals, FieldGte, FieldLte, SumEquals
3 immutability/once:    Immutable, WriteOnce, StrictMonotonic
3 transition:           Monotonic, FieldDelta, FieldDeltaInRange
2 height-bound:         FieldGteHeight, FieldLteHeight
1 cross-slot:           BoundedBy
1 conservation (intra): SumEqualsAcross
2 sender-bound:         SenderAuthorized, CapabilityUniqueness
2 rate/temporal:        RateLimit, RateLimitBySum, TemporalGate
1 preimage:             PreimageGate
1 sequence:             MonotonicSequence
1 state-machine:        AllowedTransitions
1 witness-attached:     TemporalPredicate
1 cross-cell:           BoundDelta
1 composition:          AnyOf
1 escape:               Custom { ir_hash, descriptor, reads }
```

(That's 21 by line count — `RateLimit + RateLimitBySum` share the
"rate" slot.)

**Is the 14-variant proposal comprehensive enough?** No —
**~80% comprehensive.** Closing the gaps in §7.1-7.3 brings it to
~95%. The remaining ~5% (γ.2, ledger-conservation, DSL composition)
is correctly deferred.

---

## §8. Open questions for the designer

Things the codebase doesn't unambiguously decide and that this
evaluation can't answer:

1. **Naming collision: `EvalContext`.** `dregg_cell::preconditions`
   already has `EvalContext { block_height, timestamp }` (used by
   `Preconditions::evaluate`). Lane G's proposed `EvalContext`
   adds `current_epoch`, `sender`, `sender_epoch_count`,
   `revealed_preimage`. **Should the new one extend the existing,
   or be a distinct type (`StateConstraintCtx`)?** The fields
   overlap (`block_height` ↔ `current_height`) but not fully. My
   recommendation: extend the existing — apps that use
   `Preconditions` and `StateConstraint` together benefit from a
   shared context type. But the merge requires evaluating ABI
   impact on `Preconditions::evaluate` signature.

2. **State-machine variant shape: enum vs. (from, to) pairs?**
   `AllowedTransitions { transitions: Vec<(FieldElement,
   FieldElement)> }` is fine for small state machines. For larger
   ones (10+ states), the `Vec<(from, to)>` becomes a denylist
   maintenance burden. Alternatives: `AllowedTransitions {
   adjacency_root: [u8; 32], witness_path }` for big state spaces.
   Pick before shipping.

3. **`Custom`'s `ReadSet` shape.** Is the read-set a `Vec<u8>` of
   slot indices, or also a `bool: reads_old / reads_new / reads_ctx`?
   The richer form helps AIR enforcement (the AIR knows what
   columns to bind); the simpler form is easier to author.
   Recommendation: rich form, but ship with a default builder
   that defaults `reads = ReadSet { reads_all: true }` for ease.

4. **AnyOf nesting depth.** Allow zero nested AnyOf? One level?
   Arbitrary? Recommendation: zero (the variants in an `AnyOf`
   may not themselves be `AnyOf`), with the option to relax later.

5. **`Monotonic` semantics for `FieldElement`.** The 32-byte field
   element compared "unsigned big-endian." For app-level signed
   semantics (e.g., a balance that could be negative — but
   `CellState` doesn't natively support signed) the lift must
   document that signed semantics require manual encoding (e.g.,
   bias by 2^255). This is a footgun otherwise.

6. **`FieldDelta` for decrements.** The design's `FieldDelta {
   index, delta: FieldElement }` is presumably "new == old +
   delta." For decrements (`new == old - amount`), the encoding
   uses field-element modular arithmetic — works correctly in the
   AIR but is unintuitive for app authors. Either expose a signed
   wrapper or document carefully.

7. **`BoundDelta` is the most ambitious addition.** It requires
   γ.2 PI fields to be exposed via `EvalContext` or the equivalent.
   The γ.2 design (`STAGE-7-GAMMA-2-PI-DESIGN.md`) doesn't currently
   wire binding_ids into the cell-program evaluator. Adding
   `BoundDelta` to v1 requires that wiring — or shipping the
   variant in executor-trusted mode and binding to AIR later. Pick.

8. **`TemporalPredicate` variant vs. fold-into-Custom.** The
   temporal DSL is one of several windowed-predicate shapes that
   exist (`predicate_air.rs`, the DSL's `prove_predicate_dsl`,
   etc.). Should `TemporalPredicate` be a named variant, or
   should it be one specific instance of `Custom` with a
   well-known IR-hash? Recommendation: named variant for the
   common `(values, threshold, kind, duration)` shape; `Custom`
   for novel windowed predicates.

9. **Replay semantics under `SenderAuthorized` and
   `FieldGteHeight`.** §3.6 above. Does the WR carry the
   snapshotted set root and original height, or does the executor
   re-evaluate against current chain state? Recommendation:
   snapshot at WR creation, replay against snapshot — but this
   needs to be declared.

10. **Is `Immutable` collapsing into `WriteOnce`?** The design's
    §1 identity claim — "`WriteOnce { index }` ≡ `BoundedBy
    { index, witness_index: index }`" — also makes `Immutable`
    look redundant with `WriteOnce` (both are "freeze after
    first write"). They differ only in the first-write semantics:
    `Immutable` says "you cannot change after init"; `WriteOnce`
    says "you can write once then it's frozen." For the first
    write, `Immutable` requires the value match the cell's
    creation-time init; `WriteOnce` allows any nonzero first
    value. Worth being explicit. Maybe merge into one variant
    with an `initial_value: Option<FieldElement>` field?

11. **The DSL question reframed.** If the lifted-enum-first
    approach is adopted (§6), what's the disposition of
    `dregg-dsl`? Stays as a separate crate for caveat-on-data
    (the original macaroon-shaped dregg-caveats), with the
    cell-program-side punted to direct enum-literal construction
    for v1? Or does `dregg-dsl` get extended for cell programs in
    v1.5, when patterns emerge that the enum can't express?

12. **Should `StateConstraint` and `Precondition` share atoms?**
    §3.1 above. Vocabulary atoms (slot, height, range) could be
    co-defined in a `dregg-predicates` crate. Worth it for
    coherence, or premature abstraction?

---

## §9. Closing posture

Lane G's design is **thorough and well-grounded**. The realization
that `QueueConstraint` and `StateConstraint` are siblings is
correct. The proposed lift closes the seam, the executor wiring is
right, and the migration story is sensible.

The shortfalls are all **gaps of comprehensiveness, not gaps of
correctness**:

- Four genuinely missing variants for the retained-app surface:
  `AllowedTransitions`, `StrictMonotonic`, `BoundDelta`,
  `TemporalPredicate`. Three more "should-have":
  `CapabilityUniqueness`, `AnyOf`, `RateLimitBySum`. (Total: +7
  variants, raising 14 → 21.)
- Refinements to three existing variants (`PreimageGate`,
  `SenderAuthorized`, `Custom`).
- Name collision with the existing `dregg_cell::EvalContext`.
- Under-stated relationship to `Action::preconditions`
  (Lane H's surface), to caveats (`token/`, `macaroon/`), and to
  γ.2 cross-cell binding.
- `Custom` discipline gaps (read-set declaration, IR-canonicality,
  structured descriptor).
- Silence about WR replay semantics under variants that depend on
  external state (set roots, current height).

**Verdict: 14 is not enough for v1.** Ship 20-21 variants, drop the
DSL surface for v1 (defer to v1.x sugar), and adopt the `Custom`
disciplines.

The ouroboros mostly closes; the design just needs to swallow
seven more variants and a few open questions on the way down.
