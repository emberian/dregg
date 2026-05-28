# SLOT-CAVEATS-DESIGN — closing the ouroboros

**Date:** 2026-05-24. **Status:** design-only. Read-only on code; one new
`.md`. **Scope:** lift the transition-aware constraint vocabulary that
already lives in `storage::programmable::QueueConstraint` (Rust enums in
operator-side memory) into `cell::program::StateConstraint` (turn-side,
AIR-adjacent, cell-program-bound), and let `dregg-dsl` author them.

## 0. The seam

Three components, designed years apart, now meet:

1. **macaroons / biscuits** — the very first dregg ancestor: caveat
   predicates over data. Today's `dregg-dsl` is the modern shape of
   that ancestry: `#[dregg_caveat]` functions with `require!()`
   predicates (`dregg-dsl/src/parse.rs:18` `parse_caveat`).

2. **`cell::program::StateConstraint`** — declares schemas for cell
   state and post-state predicates
   (`cell/src/program.rs:48-65`). Today's variants are
   `FieldEquals / FieldGte / FieldLte / SumEquals / Immutable /
   Custom`. Only `Immutable` references `old_state`; everything else
   is a static post-state check.

3. **`storage::programmable::QueueConstraint`** — already-built
   transition-aware constraints applied to message enqueue/dequeue
   (`storage/src/programmable.rs:60-86`): `SenderAuthorized`,
   `ContentPattern`, `MinDeposit`, `MaxSize`, `RateLimit`,
   `MonotonicSequence`, `TemporalGate`, `PreimageGate`, `Custom`. The
   evaluator (`storage/src/programmable.rs:454-580`) reads a
   `ValidationContext { sender, current_height, current_epoch,
   sender_epoch_count, preimage, sequence }`. **That context is
   exactly what cell-program transition predicates need.**

The designer's realization: `QueueConstraint` *is* the missing
transition-aware vocabulary that `StateConstraint` needs. The variants
were authored in the right shape, in the wrong crate. Lifting them —
with `old_state` access — closes the loop:

```
dregg-dsl  (caveat authoring, biscuit ancestry)
    │ compiles to
    ▼
cell::program::StateConstraint  (schema declared on the cell)
    │ enforced by
    ▼
turn::executor  (evaluates new_state, old_state, validation context)
    ┊ (optional, later)
    ▼
circuit::effect_vm AIR  (binds caveat to proof of transition)
```

Three components, one seam, each in its designed-for role. `dregg-dsl`
authors slot caveats; cells declare them as their schema; the executor
verifies the caveat on every state-modifying turn.

---

## §1. Schema

The unified `StateConstraint` enum after the lift. Combines:

- All current `cell::program::StateConstraint` variants (preserved).
- All `storage::programmable::QueueConstraint` variants, re-keyed for
  per-field semantics.
- The new variants the apps audit names: `WriteOnce`, `Monotonic`,
  `BoundedBy`, `FieldDelta`, `FieldDeltaInRange`, `FieldGteHeight`,
  `SumEqualsAcross`, `SenderAuthorized`.

Proposed Rust body (in `cell/src/program.rs`):

```rust
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StateConstraint {
    // ─── Static post-state predicates (existing) ───
    FieldEquals { index: u8, value: FieldElement },
    FieldGte    { index: u8, value: FieldElement },
    FieldLte    { index: u8, value: FieldElement },
    SumEquals   { indices: Vec<u8>, value: FieldElement },

    // ─── Transition predicates over (old, new) ───

    /// Slot must transition only from FIELD_ZERO to any non-zero value.
    /// After the first write, the slot is frozen. Generalizes Immutable
    /// for the common "register once, then read-only" pattern.
    WriteOnce { index: u8 },

    /// Slot value is read-only after initialization. (Existing variant,
    /// preserved; semantically: new[i] == old[i] for any nonzero old.)
    Immutable { index: u8 },

    /// Slot value may only increase (unsigned big-endian comparison).
    /// new[i] >= old[i]. Covers nameservice rent extension lower-bound,
    /// gallery anti-sniping (deadline only extends), nullifier-root
    /// growth, sequence numbers.
    Monotonic { index: u8 },

    /// Slot[index] may only be set if slot[witness_index] != 0.
    /// "BoundedBy" in the brief / APPS-USERSPACE-GAPS Gap 1.
    /// Composable form of see-then-set: encodes "you can't set the
    /// escrow_released field unless the escrow_funded field is non-zero".
    BoundedBy { index: u8, witness_index: u8 },

    /// new[index] == old[index] + delta. Exact-step transition.
    /// Nameservice rent extension: expiry_height += epoch_len exactly.
    FieldDelta { index: u8, delta: FieldElement },

    /// new[index] ∈ [old[index] + min_delta, old[index] + max_delta].
    /// Gallery anti-sniping: deadline can extend by 0..=K blocks.
    /// Stablecoin: collateral may grow by a bounded amount per turn.
    FieldDeltaInRange {
        index: u8,
        min_delta: FieldElement,
        max_delta: FieldElement,
    },

    /// new[index] >= CURRENT_BLOCK_HEIGHT + offset.
    /// Reads PI from the AIR. Nameservice expiry, escrow timeout,
    /// auction reveal-window gating.
    FieldGteHeight { index: u8, offset: i64 },

    /// new[index] <= CURRENT_BLOCK_HEIGHT + offset.
    /// Commit-window upper-bound, freshness checks.
    FieldLteHeight { index: u8, offset: i64 },

    /// Conservation across the transition.
    /// sum(new[input_fields]) == sum(old[input_fields]) + sum(new[output_fields]).
    /// Generalizes SumEquals to bind input flow to output flow.
    /// Gallery royalty split, prediction-market pro-rata, orderbook fills.
    SumEqualsAcross {
        input_fields: Vec<u8>,
        output_fields: Vec<u8>,
    },

    // ─── Sender-bound predicates (use ValidationContext) ───

    /// The turn's sender public-key must be in the set whose
    /// merkle root sits at slot[set_root_index].
    /// Subscription "only members may enqueue"; voting eligibility.
    SenderAuthorized { set_root_index: u8 },

    // ─── Rate / temporal predicates ───

    /// Sender may only mutate this cell at most max_per_epoch times
    /// per epoch_duration blocks. Backed by an executor-side counter
    /// keyed on (cell, sender, epoch).
    RateLimit {
        max_per_epoch: u32,
        epoch_duration: u64,
    },

    /// Mutation is rejected unless current_height ∈ [not_before, not_after].
    /// Auction commit/reveal windows. Replaces the proposed-but-not-yet
    /// `Caveat::CommitWindow / RevealWindow` (APPS-USERSPACE-GAPS Gap 16).
    TemporalGate {
        not_before: Option<u64>,
        not_after: Option<u64>,
    },

    /// The turn must reveal a preimage whose Poseidon2 hash equals
    /// the value at slot[commitment_index]. Implements commit-reveal
    /// natively on the cell instead of on a side-channel queue.
    PreimageGate { commitment_index: u8 },

    /// MonotonicSequence (re-keyed): the message's sequence number,
    /// stored at slot[seq_index], must equal old[seq_index] + 1.
    /// Replay-safe sequencing for messaging cells.
    MonotonicSequence { seq_index: u8 },

    // ─── Escape hatch ───

    /// DSL-authored predicate compiled to an opaque expression. The
    /// executor evaluates by name lookup against a registered
    /// expression table (the dregg-dsl runtime). Sibling to the audit's
    /// proposed StateConstraint::ExpressionEquals.
    Custom {
        constraint_hash: [u8; 32],
        description: String,
    },
}
```

**14 variants total** (4 static + 10 transition/contextual). Every
queue-side variant has a per-field cell-side counterpart. Every
apps-audit named variant is represented. The `Custom` escape carries
a description for transparency (storage's `Custom` already does this;
the current cell-program `Custom` does not).

**Identity claim:** `WriteOnce { index }` ≡ `BoundedBy { index, witness_index:
index }` taken from-the-old-side (the slot is its own witness against
itself). Both forms ship because `WriteOnce` is the *named, idiomatic*
shape apps reach for; `BoundedBy` is the *general* shape.

---

## §2. `old_state` access shape

Current signature (`cell/src/program.rs:124-128`):

```rust
pub fn evaluate(
    &self,
    new_state: &CellState,
    old_state: Option<&CellState>,
) -> Result<(), ProgramError>;
```

`old_state: Option<&CellState>` already works for every transition
variant above. The `Option` is correctly nullable for the
first-write case (nonce == 0 → `old_state` is `None`, and the cell
program either accepts the initial values or rejects, per the existing
`Immutable` fail-closed pattern).

**The minimal signature change** is to add a `ValidationContext` —
the queue side already has one — for sender, height, epoch, preimage,
and rate-limit counter:

```rust
pub struct EvalContext<'a> {
    pub current_height: u64,
    pub current_epoch: u64,
    pub sender: Option<&'a [u8; 32]>,        // None for system turns
    pub sender_epoch_count: u32,             // for RateLimit
    pub revealed_preimage: Option<&'a [u8; 32]>, // for PreimageGate
}

pub fn evaluate(
    &self,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: &EvalContext<'_>,
) -> Result<(), ProgramError>;
```

The executor already has all five fields at the call-site
(`turn/src/executor.rs:4024`): `current_height` is a top-level
parameter to action-application, `sender` is on the turn's
`Authorization::Signature`, the rate-limit counter sits in the
executor's per-cell metadata, and the preimage rides on the action's
optional witness field. The change is **purely additive** — existing
callers pass a default context, and only the new transition variants
read it.

For the static post-state variants (`FieldEquals` etc.), `ctx` is
ignored. The lift is backward-compatible.

---

## §3. DSL surface

**Choice:** **predicate-shaped, in the `#[dregg_caveat]` body, with
`require!()` macros, keyed by slot index.** Justified below.

**Rejected alternatives:**

- *`caveat write_once on slot 0 { ... }` block syntax* — would require a
  new DSL grammar layer. dregg-dsl is already an attribute-macro DSL
  parsed via `syn` (`dregg-dsl/src/parse.rs`). A new top-level keyword
  costs a parser fork.

- *`slot 0: WriteOnce` enum-listing syntax* — looks tidy but loses
  composability. The whole point of dregg-dsl is *predicates compose*;
  reducing to an enum literal throws that away.

**Chosen syntax — `#[dregg_caveat]` extension:**

```rust
#[dregg_caveat]
fn name_slot_write_once(old: CellState, new: CellState, ctx: EvalContext) {
    require!(slot(old, 0) == FIELD_ZERO || slot(new, 0) == slot(old, 0));
}
```

The parser learns three new param types: `CellState` (read access to
`fields[0..8]` and `nonce`), `EvalContext` (read `current_height`,
`current_epoch`, `sender`, `revealed_preimage`), and the `slot(state,
i)` accessor that produces a `FieldElement`. The compiler emits one
`StateConstraint::*` variant per `#[dregg_caveat]` function, picking
the most-specific named variant if the predicate pattern-matches a
named one (`WriteOnce`, `Monotonic`, etc.); otherwise emits
`StateConstraint::Custom { constraint_hash, description }` and
registers the compiled expression in the runtime's expression table
(audit §3.4(b)'s "ExpressionEquals").

**Worked example — nameservice "name_hash slot is write-once":**

```rust
// apps/nameservice/src/program.rs
use dregg_dsl::dregg_caveat;
use dregg_app_framework::{CellState, EvalContext, FIELD_ZERO};

const NAME_HASH_SLOT: u8 = 0;

#[dregg_caveat]
fn name_hash_write_once(old: CellState, new: CellState) {
    // Either it's the first write (old slot was zero),
    // or the new value matches the old (slot is frozen).
    require!(
        slot(old, NAME_HASH_SLOT) == FIELD_ZERO
            || slot(new, NAME_HASH_SLOT) == slot(old, NAME_HASH_SLOT)
    );
}
```

The dregg-dsl compiler pattern-matches this against the `WriteOnce`
shape and emits:

```rust
CellProgram::Predicate(vec![
    StateConstraint::WriteOnce { index: 0 },
])
```

If the predicate had been more general (e.g., "either zero or equal to
old, AND new < 2^128"), the compiler emits `Custom { constraint_hash,
description: "name_hash_write_once" }` and the predicate body lives in
the dregg-dsl-runtime expression table at the hash key.

**The slot caveat shows up at three layers:**

| Layer | Form |
|---|---|
| Author (app dev) | `#[dregg_caveat] fn name_hash_write_once(...) { require!(...) }` |
| Schema (cell metadata) | `CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: 0 }])` |
| Enforcement (executor) | `program.evaluate(new, old, ctx)?` on each state-modifying effect |

---

## §4. Verification path — recommendation

**Recommendation: executor-side only, as the default. Silver Vision is
"make it run correct"; cryptographic enforcement follows.**

### The two options

**Option A: Executor-side only.**
- Cell program is part of `Cell` metadata. The executor evaluates
  `program.evaluate(new_state, old_state, ctx)` on every state-modifying
  effect (`turn/src/executor.rs:4020-4024` already does this for the
  current variants).
- The AIR proves the pre-state, the post-state, the transition, and the
  cell's metadata hash — *but does not re-evaluate the caveat in-circuit*.
- Cost: zero new AIR rows.
- Trust assumption: the executor honestly evaluates the program. Since
  the executor is the federation, this is the same trust level as
  "the federation honestly applies the effect." A malicious executor
  could already bypass the program by skipping the call; the AIR
  doesn't catch that today.

**Option B: Executor + AIR.**
- Each variant gets per-variant AIR columns proving the predicate held
  under the bound (old_state_hash, new_state_hash, validation context).
- Cost: ~5-15 new selector/aux columns per variant. Static variants
  (`FieldEquals`, `FieldGte`) are cheap (one comparison gadget); transition
  variants (`FieldDelta`, `SumEqualsAcross`) are moderate; sender-bound
  (`SenderAuthorized`) needs a Merkle-membership gadget that already
  exists for `swiss_table_root`-style proofs.
- Trust assumption: no executor trust needed; the proof binds the
  caveat to the transition algebraically.

### Why executor-side is the right default

1. **The trust gradient is already executor-mediated.** The current
   `Predicate` evaluator runs in the executor; there's no AIR variant
   for `FieldEquals` etc. today. Adding 14 new in-AIR variants is a
   substantial circuit-engineering investment we don't yet need.

2. **The `Custom` variant has no AIR shape regardless.** DSL-authored
   custom predicates compile to opaque expression hashes; no
   per-predicate AIR is possible without per-predicate circuit
   compilation. So the AIR path can never fully replace the executor
   path for the DSL surface — both must exist.

3. **The Effect VM AIR already binds (old_state_hash, new_state_hash).**
   The infrastructure for AIR-side caveat enforcement is *present but
   unused*. Adding per-variant constraints later is purely additive: pick
   the named variants whose enforcement matters most (`SenderAuthorized`,
   `WriteOnce`, `FieldDelta`), constrain them in-AIR, leave the rest
   executor-side.

4. **Silver Vision priority.** Make it work; make it cryptographic. The
   STARK pipeline is healthy enough to ship caveats correctly under
   executor evaluation today, and adding AIR rows incrementally won't
   change any cell-program author's code.

**Recommendation: ship Option A. Reserve Option B as a per-variant opt-in
for the high-value cases (`SenderAuthorized` first — it's the closest
to swiss-table-membership, which has AIR support already).**

---

## §5. Migration story for `storage::programmable` consumers

### Current consumers

`grep -ln "QueueConstraint" /apps/ /app-framework/ /sdk/` finds three
live consumers:

- `apps/dao-treasury/src/governance.rs` — uses 8 `QueueConstraint`
  variants for proposal queue gating (`Custom`, `MinDeposit`).
- `apps/amm/src/twap_queue.rs` — imports `ProgrammableQueue` only.
- `apps/stablecoin/src/liquidation_queue.rs` — imports
  `ProgrammableQueue` only.
- `app-framework/src/queue_endpoint.rs` — wraps a `ProgrammableQueue`
  as an HTTP endpoint.
- `apps/subscription/` — *does not* use `QueueConstraint` (per the audit
  it consumes `CapInbox` directly).

### Three options

**Option A: storage re-exports from `cell::program`.** Slot caveats are
the canonical home; queues are one consumer. `storage::programmable`
becomes a thin wrapper that interprets `cell::program::StateConstraint`
variants in the queue context.

**Option B: keep both; mark storage as deprecated.** Two parallel
vocabularies; storage's becomes a `#[deprecated]` re-export of cell's.

**Option C: collapse — storage stops having its own constraint
vocabulary entirely.** All cell-program enforcement happens on the
underlying queue cell. The queue *is* a cell with slots; the slot
caveats enforce the same invariants the queue program did.

### Recommendation: **Option A**, with Option C as the eventual end-state

Phase 1 (this commit's sequel): **A**. Move the enum into
`cell::program`, leave `storage::programmable::QueueConstraint` as a
type alias / thin re-export for backward compatibility. The dao-treasury
imports keep working unchanged. The semantic split is preserved: queues
have a `ValidationContext` keyed on message sender; cell programs have
the same `EvalContext` keyed on turn sender. Same shape, same code.

Phase 2 (later): **C**. Once the cell-program enforcement is wired into
the queue executor's effect path, `storage::programmable::ProgrammableQueue`
becomes "a queue cell whose program is `CellProgram::Predicate(...)`".
The storage crate stops needing its own enforcement loop. This collapse
is the proper end-state because the storage queue and the cell program
are *the same algebraic object* viewed from two sides. But it requires
the Phase 2 work of folding `MerkleQueue::root` into the queue cell's
`fields[1]` (per the STORAGE-REFLECTIVITY audit Q4.2), which is a
larger lift.

Option B is rejected: parallel vocabularies that drift apart are how
ouroboroses come uncoupled.

---

## §6. Worked examples

### 6.1 Nameservice — `WriteOnce` on `name_hash` slot

The bug today (`APPS-USERSPACE-GAPS.md` Gap 1): nameservice wants to
enforce that `SetField(NAME_STORAGE_SLOT, name_hash)` fails if the slot
is already non-zero; today the only path is read-then-check-then-emit,
which races. With slot caveats:

```rust
// apps/nameservice/src/program.rs
const NAME_HASH_SLOT: u8 = 0;
const EXPIRY_HEIGHT_SLOT: u8 = 1;

pub fn nameservice_cell_program() -> CellProgram {
    CellProgram::Predicate(vec![
        StateConstraint::WriteOnce { index: NAME_HASH_SLOT },
        // expiry can only extend (no shortening rentals you've sold)
        StateConstraint::Monotonic { index: EXPIRY_HEIGHT_SLOT },
        // expiry must be in the future at write time
        StateConstraint::FieldGteHeight { index: EXPIRY_HEIGHT_SLOT, offset: 1 },
    ])
}
```

DSL form (authored via `dregg-dsl`):

```rust
#[dregg_caveat]
fn name_hash_write_once(old: CellState, new: CellState) {
    require!(
        slot(old, 0) == FIELD_ZERO || slot(new, 0) == slot(old, 0)
    );
}
```

This is "Nameservice is just `CreateCell` + `SetField` + a 3-line cell
program." The 4,500-LOC nameservice in `apps/nameservice/src/registry.rs`
collapses to a per-name cell with this program.

### 6.2 Gallery — `Monotonic` on `bid_amount` slot

Auction bids must be strictly increasing over the auction's lifetime;
the current top bid lives in the auction cell's `bid_amount` slot. With
slot caveats:

```rust
const BID_AMOUNT_SLOT: u8 = 0;
const DEADLINE_SLOT: u8 = 1;
const PHASE_SLOT: u8 = 2;

pub fn auction_cell_program() -> CellProgram {
    CellProgram::Predicate(vec![
        // bids only go up
        StateConstraint::Monotonic { index: BID_AMOUNT_SLOT },
        // anti-sniping: deadline may extend by 0..=K blocks per turn
        StateConstraint::FieldDeltaInRange {
            index: DEADLINE_SLOT,
            min_delta: field_from_u64(0),
            max_delta: field_from_u64(ANTI_SNIPE_EXTENSION),
        },
        // only the auction's escrow contract can advance the phase
        // (sender-authorized against an allow-list root sitting in slot 7)
        StateConstraint::SenderAuthorized { set_root_index: 7 },
    ])
}
```

DSL form:

```rust
#[dregg_caveat]
fn bid_monotonic(old: CellState, new: CellState) {
    require!(slot(new, 0) >= slot(old, 0));
}
```

Compiles to `StateConstraint::Monotonic { index: 0 }`.

### 6.3 Privacy-voting — `WriteOnce` on `ballot_commitment` per voter

Each voter cell holds the voter's ballot commitment in slot 0; once
committed, it can't change for the rest of the proposal. Each voter
also has a nullifier-spent flag in slot 1 (incremented on reveal):

```rust
const BALLOT_COMMITMENT_SLOT: u8 = 0;
const NULLIFIER_SPENT_SLOT: u8 = 1;
const PROPOSAL_ID_SLOT: u8 = 2;
const COMMIT_WINDOW_END_SLOT: u8 = 3;

pub fn voter_cell_program() -> CellProgram {
    CellProgram::Predicate(vec![
        // one-shot ballot
        StateConstraint::WriteOnce { index: BALLOT_COMMITMENT_SLOT },
        // proposal binding is immutable for the cell's lifetime
        StateConstraint::Immutable { index: PROPOSAL_ID_SLOT },
        // nullifier flag flips zero → one exactly once
        StateConstraint::WriteOnce { index: NULLIFIER_SPENT_SLOT },
        // commit happens only during the commit window
        StateConstraint::TemporalGate {
            not_before: None, // open from cell creation
            not_after: Some(/* read from PROPOSAL_ID_SLOT-keyed lookup */ 0),
        },
    ])
}
```

The commit-window upper bound is the wrinkle: it should be the
proposal's commit-window-end, not a constant. In the proposed lift,
this becomes `TemporalGate { not_after: Some(slot_value) }` once
`StateConstraint` learns to read parameters from slots — or stays as a
DSL `Custom` predicate today.

### 6.4 Bounty-board — `BoundedBy` on `escrow_locked` balance

A bounty cell holds a balance in slot 0 and an "escrow released" flag
in slot 1. The balance can drop only if the escrow has been released
(slot 1 non-zero); the released flag can only be set once.

```rust
const BALANCE_SLOT: u8 = 0;
const ESCROW_RELEASED_SLOT: u8 = 1;
const TOTAL_LOCKED_SLOT: u8 = 2;

pub fn bounty_cell_program() -> CellProgram {
    CellProgram::Predicate(vec![
        // balance may decrease only when escrow_released is non-zero
        StateConstraint::BoundedBy {
            index: BALANCE_SLOT,
            witness_index: ESCROW_RELEASED_SLOT,
        },
        // released is one-way
        StateConstraint::WriteOnce { index: ESCROW_RELEASED_SLOT },
        // conservation: balance + released_amount == total_locked
        StateConstraint::SumEquals {
            indices: vec![BALANCE_SLOT, ESCROW_RELEASED_SLOT],
            value: field_from_u64(TOTAL_LOCKED),
        },
    ])
}
```

Here `BoundedBy` is the general "see-then-set" — the new value of
`BALANCE_SLOT` is permitted only when the witness slot is "armed". The
witness can be a flag, a counter, or any non-zero field.

---

## §7. Open questions for designer

These are the things the codebase doesn't unambiguously decide. The
recommendations in §§1-6 take a position on each, but the designer
should explicitly confirm.

1. **Should `WriteOnce` be a primary variant, or just a compiled form
   of `BoundedBy { index: i, witness_index: i }`?** §1 ships both;
   the rationale is ergonomics. Designer may prefer single-variant
   minimality.

2. **`EvalContext::sender` — `Option<&[u8;32]>` or `&[u8;32]`?** System
   turns (genesis, scheduled effects) may have no sender. Today's
   executor treats system turns as a `[0u8;32]` placeholder. `Option`
   is more honest; the placeholder is convenient for the
   `SenderAuthorized` Merkle-membership check (the zero key won't be
   in any real allow-list).

3. **Sequence number storage — in `CellState.nonce` or in a dedicated
   slot?** `MonotonicSequence { seq_index }` as proposed reads from a
   slot, leaving `CellState.nonce` to remain the turn counter. The
   queue side uses a separate counter; cells could go either way.

4. **Should `RateLimit` live in `StateConstraint` or in
   `turn::cap_caveats::Caveat`?** Rate limits don't transition state —
   they gate writes. Caveats are about authorization; state constraints
   are about state validity. APPS-USERSPACE-AUDIT Tier-1 #1 lists rate
   limits under transition-aware constraints; APPS-USERSPACE-GAPS Gap 1
   lists them under cell-program caveats. §1 puts them in
   `StateConstraint` because the executor already calls `evaluate()`
   on every state-modifying turn; doubling that into a separate
   `Caveat::RateLimit` would create two enforcement loops.

5. **`Custom` description field — required or optional?** §1 makes
   it required (sibling to the storage side). Custom predicates
   without human-readable names defeat the "biscuit ancestry" — they
   should be inspectable in audit tools.

6. **AIR enforcement — opt-in per cell or opt-in per variant?**
   §4 says reserve for later. When it lands, the question is whether
   a cell *declares* it wants in-AIR enforcement of its caveats
   (per-cell), or whether some variants are *always* AIR-enforced
   (per-variant). Per-variant is the simpler design; per-cell
   matches the "branded constructor" factory shape and lets some
   apps opt in to higher assurance.

7. **Should `CellProgram::Predicate(Vec<StateConstraint>)` grow to
   `Predicate { constraints: Vec<StateConstraint>, all_must_hold:
   bool }`** so apps can express OR-of-predicates? §1 leaves the
   conjunction-only shape (current behavior). OR-of-predicates
   composes via `Custom` for now; native OR may be worth it later.

8. **Migration of `storage::programmable::QueueConstraint::Custom`
   `{expr: String}` — does its `expr` translate 1:1 to the
   `StateConstraint::Custom { description: String }` plus
   a separate hash table, or does it need its own dsl runtime?** §5
   Phase 1 keeps both forms; designer may want to unify earlier.

---

## §8. Implementation plan

Sequencing, with rough LOC estimates per phase. **Each phase is one
commit.**

### Phase 1 — Schema (~250 LOC)

Add the 10 new variants to `cell::program::StateConstraint`, update
`evaluate_constraint`, add the `EvalContext` struct. Pure additive in
`cell/src/program.rs`. Adds unit tests for each new variant (8 happy +
8 adversarial = 16 tests). No callers change yet.

- `cell/src/program.rs` +180 LOC enum + evaluator + tests
- `cell/src/lib.rs` +5 LOC re-exports

### Phase 2 — DSL surface (~200 LOC)

Extend `dregg-dsl` parser to recognize `CellState` and `EvalContext`
parameter types, and add a `slot(state, i)` pattern. Add a
`compile_to_state_constraint(ir) -> StateConstraint` pass that
pattern-matches common predicate shapes (`WriteOnce`, `Monotonic`,
`FieldDelta`, …) and falls back to `Custom`.

- `dregg-dsl/src/parse.rs` +60 LOC param types + slot accessor
- `dregg-dsl/src/ir.rs` +40 LOC IR additions
- `dregg-dsl/src/gen_state_constraint.rs` (new) +100 LOC compiler

### Phase 3 — Executor verification (~150 LOC)

Wire the new variants into `turn/src/executor.rs`'s existing
`program.evaluate(new, old)` call. Plumb `EvalContext` from the
executor's existing turn context (current_height, sender, epoch
counter, preimage). No new effects; no new AIR.

- `turn/src/executor.rs` +60 LOC ctx plumbing + per-variant
  enforcement branches in cases the evaluator can't handle alone
- `turn/src/lib.rs` +5 LOC export
- `tests/src/slot_caveats_executor.rs` (new) +85 LOC integration tests

### Phase 4 — One app fully migrated (~300 LOC removed, ~80 added)

Migrate `apps/nameservice` to express its WriteOnce + Monotonic +
FieldGteHeight constraints as a `CellProgram::Predicate`. Delete the
hand-rolled `BTreeMap` registry. Show end-to-end: register a name →
the cell's caveat rejects a second register on the same slot.

- `apps/nameservice/src/program.rs` (new) +80 LOC
- `apps/nameservice/src/registry.rs` −300 LOC (the BTreeMap and
  hand-rolled enforcement evaporate)
- `apps/nameservice/tests/slot_caveats.rs` (new) +60 LOC

### Phase 5 (deferred — not in initial sequence) — AIR enforcement for `SenderAuthorized`

Per §4 recommendation, ship AIR enforcement opt-in for the single
highest-value variant (`SenderAuthorized` against a slot-held Merkle
root). Reuses the swiss-table-membership gadget. ~400 LOC of circuit
work plus tests. Skipped in the initial implementation lane.

### Phase 6 (deferred) — Storage collapse (Option C from §5)

Fold `storage::programmable` into being a cell whose program is
expressed in the new vocabulary. Requires `MerkleQueue::root` to live
in `fields[1]` of the queue cell (the STORAGE-REFLECTIVITY audit's
named follow-on). Large; out of scope for this design pass.

### Total initial commit count: 4 (Phases 1-4)

- Phase 1: schema. ~250 LOC.
- Phase 2: DSL. ~200 LOC.
- Phase 3: executor. ~150 LOC.
- Phase 4: nameservice migration. net ~−220 LOC (deletion-heavy).

**Net code change: roughly +600 LOC of new infrastructure, ~−300 LOC
of nameservice cruft removed. The seam closes by deleting code, not
adding it.**

The ouroboros now eats its tail in the right shape: macaroons →
dregg-dsl → `StateConstraint` → executor → cell. Each component in
the role it was designed for. Three components, one seam.
