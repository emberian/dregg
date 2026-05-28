# Stage 7-γ.2 — Bilateral Cross-Cell Algebraic Binding (PI Layout, Phase 1)

**Status:** design only. Phase 1 = PI-only binding (shared public inputs +
off-AIR verifier algorithm); Phase 2 (joint aggregation AIR) is sketched at
the end. Companion to `STAGE-7-PLUS-DESIGN.md`,
`STAGE-7-GAMMA-AGGREGATION-DESIGN.md`, and `WITNESSED-RECEIPT-CHAIN-DESIGN.md`.

The animating problem is `STAGE-7-GAMMA-AGGREGATION-DESIGN.md §1a-c`: today,
when a turn touches two (or three) cells via a bilateral effect, each side
produces an independent per-cell STARK whose only cross-side join is the
executor reading the same `Effect` and feeding both projections. A receiver
who holds only the two `WitnessedReceipt`s — sender's and receiver's — and
runs the verifier from cold has no way to confirm that those two proofs
*describe the same effect*. The cross-side join evaporates the instant the
executor is removed from the trust path.

γ.0 (already landed) put `TURN_HASH`, `EFFECTS_HASH_GLOBAL`, `ACTOR_NONCE`,
`PREVIOUS_RECEIPT_HASH` into PI and made the verifier's PI-match loop
require all per-cell proofs of a single turn to agree. That closes the
*"are these proofs from the same turn"* question. **It does not close the
*"do these two proofs describe the same Transfer / Grant / Introduce"*
question** — and as soon as cells live on different federations, or are
shipped to a verifier weeks apart, the executor-side glue isn't reachable.

γ.2 Phase 1 closes that gap with new PI fields whose canonical derivation
is publicly computable from the bilateral effect's surface inputs. The
verifier, given two `WitnessedReceipt`s, can recompute the canonical
`transfer_id` (or `grant_id`, `introduce_id`) from one side, look it up
in the other side's PI, and confirm match. The AIR is extended to bind
the in-trace transfer-effect data to the same id, so the prover cannot
emit a proof whose claimed `transfer_id` is unrelated to the actual
amount/direction it wrote into `bal_lo`.

This document is concrete enough that an implementing agent can pick up
the keyboard without further design.

---

## 1. What's being bound

Three bilateral effects need cross-cell binding at Phase 1. Each has a
distinct topology.

### 1.1 `Transfer { from, to, amount }` — symmetric bilateral

**Two cells touched:** `from`, `to`. Each produces a per-cell proof.

**Data that must agree:**

- `amount` (u64, currently mediated by `bal_lo` 30-bit projection).
- The *peer cell id* (`from` sees `to`; `to` sees `from`).
- The *direction* (1 = outflow for `from`, 0 = inflow for `to`).
- A *transfer instance identifier* derived from `(from, to, amount, sender_nonce)`
  that uniquely names the act.

**Why direction is in the binding:** without it, a malicious prover holding
both sides could swap `direction` between sender and receiver, producing
`(from=A, to=B, dir=0)` on A and `(from=A, to=B, dir=1)` on B, which is
inconsistent but only catchable by the executor today.

### 1.2 `GrantCapability { from, to, cap }` — asymmetric bilateral

**Two cells touched:** grantor (`from`), grantee (`to`). Per-cell AIR
currently emits a `VmEffect::GrantCapability` row only on the `to` side
(`turn/src/executor.rs:1595-1599`). γ.2 widens this so grantor's per-cell
projection also emits a row binding the *consume-side* of the grant.

**Data that must agree:**

- `cap_entry_hash`: a 4-felt Poseidon2 of the (selector, payload, expiry,
  scope) of the capability being granted.
- `grant_id`: canonical hash binding `(from, to, cap_entry_hash, sender_nonce)`.
- A *parent slot* on the grantor side that's being consumed — represented
  by its slot index in `from`'s c-list (Phase 1: PI declares the index;
  Phase 2 elevates to a Merkle path against `cap_table_root`, see 7-ε).
- A *successor slot* on the grantee side that's being inserted — PI
  declares the index where `cap_entry_hash` lands in `to`'s c-list.

### 1.3 `Introduce { introducer, recipient, target, permissions }` — 3-cell trilateral

**Three cells touched.** Recipient gains a capability referencing `target`
that the introducer chose to share. Per-cell AIR currently emits a
passthrough `VmEffect::Introduce` row on each of the three with
`intro_hash` over `(introducer, recipient, target, permissions)` —
*coincidentally* equal across sides, never algebraically constrained.

**Data that must agree:**

- `intro_id`: canonical hash binding
  `(introducer, recipient, target, permissions, introducer_nonce)`.
- The permissions byte (its semantic content; γ.2 still treats this as a
  1-byte selector + per-effect AuthRequired mask packed into a felt).
- The `target` cell id (since it's not the proving cell, each of the
  three sides has the same target reference; equality is what we
  constrain).

This is the CapTP "Alice→Bob→Carol" topology (`AUDIT-distributed-semantics.md §1`).
At Phase 1 we constrain `intro_id` agreement across the three per-cell
proofs of an `Introduce` *within one federation*. The cross-federation
shape (where `introducer.federation ≠ recipient.federation`) is the same
PI layout plus a federation-id binding; called out at end of §1.

### 1.4 Out of scope for γ.2 Phase 1

- `RevokeCapability` — single-cell write, no cross-cell binding need.
- `BridgeMint / Lock / Finalize / Cancel` — cross-federation, handled by
  Stage 6 bridge phases.
- `NoteSpend → NoteCreate` chains — different topology (1-of-N value
  shielded notes, nullifier-keyed); their own design.
- Capability *exercise* (`ExerciseViaCapability`) — not bilateral; it's
  unilateral with a c-list membership query, see 7-ε.

---

## 2. PI layout additions

Today's `pi` module ends at slot 37 (last base entry: end of
`PREVIOUS_RECEIPT_HASH_BASE+4 = 38`, then `CUSTOM_PROOFS_BASE = 38`).
γ.2 extends `BASE_COUNT` to make room for bilateral-binding fields,
**preserving** custom-proof base offset semantics — `CUSTOM_PROOFS_BASE`
becomes a derived constant `BASE_COUNT` and is no longer a hard-coded
38.

### 2.1 New PI fields (slot offsets are post-γ.2)

```
//
// ---- γ.2 bilateral cross-cell binding (Phase 1) ----
//
// All bilateral fields default to the zero sentinel (Commitment4::empty()
// for 4-felt fields; 0 for scalars / counts) when the turn has no
// bilateral effects of that kind. The verifier's cross-cell match loop
// skips zero-sentinel entries when iterating peer proofs.

/// Per-cell bilateral-effect counts (sums sanity-check against trace
/// selectors — see §6.2 AIR work). All four are sum-checks the AIR
/// performs; the PI surfaces them for verifier cross-checking.

/// Count of Transfer rows in this cell's trace where direction = 1
/// (outflow). Together with INBOUND_TRANSFER_COUNT this lets the
/// verifier predict the number of expected entries in OUTGOING_*_ROOT.
pub const OUTBOUND_TRANSFER_COUNT: usize = 38;
/// Count of Transfer rows where direction = 0 (inflow).
pub const INBOUND_TRANSFER_COUNT: usize = 39;
/// Count of GrantCapability rows where this cell is the grantor
/// (consume side).
pub const OUTBOUND_GRANT_COUNT: usize = 40;
/// Count of GrantCapability rows where this cell is the grantee
/// (insert side).
pub const INBOUND_GRANT_COUNT: usize = 41;
/// Count of Introduce rows where this cell is the introducer.
pub const INTRO_AS_INTRODUCER_COUNT: usize = 42;
/// Count of Introduce rows where this cell is the recipient.
pub const INTRO_AS_RECIPIENT_COUNT: usize = 43;
/// Count of Introduce rows where this cell is the target.
pub const INTRO_AS_TARGET_COUNT: usize = 44;

/// 4-felt Poseidon2 accumulator over all outbound bilateral
/// transfer_ids in this turn (ordered by trace-row index). Each
/// row absorbs hash(transfer_id, peer_cell_id, amount_lo, amount_hi)
/// with direction baked into the domain separator.
/// Sentinel: Commitment4::empty() when count == 0.
pub const OUTGOING_TRANSFER_ROOT_BASE: usize = 45;
pub const OUTGOING_TRANSFER_ROOT_LEN: usize = 4;
/// Mirror of OUTGOING_TRANSFER_ROOT for the receive side. Same
/// shape; the verifier's match loop checks that for each pair of
/// per-cell proofs (sender, receiver) of one turn, every entry in
/// sender's OUTGOING_TRANSFER_ROOT corresponds to one entry in
/// receiver's INCOMING_TRANSFER_ROOT — see §4.
pub const INCOMING_TRANSFER_ROOT_BASE: usize = 49;
pub const INCOMING_TRANSFER_ROOT_LEN: usize = 4;

/// Grant-side accumulators: same shape. Domain-separated tags
/// distinguish from transfer.
pub const OUTGOING_GRANT_ROOT_BASE: usize = 53;
pub const OUTGOING_GRANT_ROOT_LEN: usize = 4;
pub const INCOMING_GRANT_ROOT_BASE: usize = 57;
pub const INCOMING_GRANT_ROOT_LEN: usize = 4;

/// Introduce 3-tuple: same shape, three roles. A cell can be
/// any of (introducer, recipient, target) for a given Introduce;
/// each role gets its own per-cell accumulator. The verifier's
/// match loop joins on intro_id across the three.
pub const INTRO_AS_INTRODUCER_ROOT_BASE: usize = 61;
pub const INTRO_AS_INTRODUCER_ROOT_LEN: usize = 4;
pub const INTRO_AS_RECIPIENT_ROOT_BASE: usize = 65;
pub const INTRO_AS_RECIPIENT_ROOT_LEN: usize = 4;
pub const INTRO_AS_TARGET_ROOT_BASE: usize = 69;
pub const INTRO_AS_TARGET_ROOT_LEN: usize = 4;

/// γ.2 Phase 1 closes here.
pub const BASE_COUNT: usize = 73;
```

(Today's `BASE_COUNT = 38`; γ.2 grows by 35 felts. Each per-cell PI
remains under ~120 felts for realistic turns, which is well within the
single-page Plonky3 PI budget.)

### 2.2 Field-shape choices: BabyBear vs. Poseidon2 hash

Two scalars (`*_COUNT`) are single BabyBear felts. Plain integer counts
fit comfortably in 31 bits (max touched cells per turn cap, see
`STAGE-7-GAMMA-AGGREGATION-DESIGN.md` open question 2, is 8;
max per-cell effects of a kind is bounded by trace length).

All `*_ROOT` accumulators are 4-felt Poseidon2 output. Reasons:

- We already use 4-felt Poseidon2 for `EFFECTS_HASH_BASE`, `OLD_COMMIT_BASE`,
  `NEW_COMMIT_BASE`, `APPROVED_HANDOFFS_BASE`, `TURN_HASH_BASE`,
  `EFFECTS_HASH_GLOBAL_BASE`, `PREVIOUS_RECEIPT_HASH_BASE` — keeps the
  hash family uniform. The Poseidon2 instance is already absorbed into
  the AIR (`circuit/src/poseidon2_air.rs`).
- 4 BabyBear felts give ~124-bit collision resistance, the design target
  inherited from Stage 1's commitment widening.
- The id hash itself (`transfer_id`, `grant_id`, `intro_id`) is a 4-felt
  Poseidon2 of the canonical preimage (§3). The accumulator absorbs
  this directly without intermediate bytes ↔ felts conversion.

`peer_cell_id` is *not* a separate PI — it's folded into the per-row
accumulator absorb. This is deliberate: surfacing peer cells in PI
would leak cross-cell topology to a public verifier even when the
witness is sealed. The accumulator is opaque; the witness-holder can
decompose it.

### 2.3 Sentinel handling

When a per-cell proof has no bilateral effects of a kind, the
corresponding root field is set to `Commitment4::empty()` (the same
zero sentinel used by `APPROVED_HANDOFFS_BASE` today, which is the
Poseidon2 of an empty input). The count fields are 0. The verifier's
cross-cell match loop short-circuits when both sides are sentinels;
when one side is non-zero and the other is sentinel for the matching
direction, that's a hard reject (a proof claims to have made a transfer
out but no proof of the receive-side exists).

---

## 3. Canonical id derivation

Every bilateral effect gets a deterministic *instance id* computable
from public surface data. The id is reproducible by both sides without
coordination, by a third-party verifier, and by an auditor replaying
a chain.

### 3.1 `transfer_id`

```
preimage = b"dregg-transfer-id-v1" 
        || from_cell_id (32 bytes)
        || to_cell_id   (32 bytes)
        || amount_be    (8 bytes)
        || sender_nonce_be (8 bytes)
```

`sender_nonce` is the **outer Turn::nonce** of the actor who signed
the turn (which is by definition `from`'s outer turn nonce, since
the actor authorizes the outflow). Already present in PI as
`ACTOR_NONCE` (γ.0), so the verifier can re-derive `transfer_id`
from `(from, to, amount, ACTOR_NONCE)` without additional witness
data.

```
transfer_id = Commitment4::from_poseidon2(preimage)  // 4 BabyBear felts
```

### 3.2 `grant_id`

```
preimage = b"dregg-grant-id-v1"
        || from_cell_id (grantor, 32 bytes)
        || to_cell_id   (grantee, 32 bytes)
        || cap_entry_hash (32 bytes — Poseidon2 of cap fields)
        || sender_nonce_be (8 bytes)
```

`cap_entry_hash` is the 4-felt Poseidon2 of `(selector, payload, expiry, scope)`
already used by today's per-cell `GrantCapability` row's cap_root chain
update — we name it explicitly here and surface it as part of the
preimage. (The current code computes this internally; γ.2 lifts it to a
named struct in `turn/src/cap_entry.rs::CapEntry::hash` for cross-cite
clarity.)

```
grant_id = Commitment4::from_poseidon2(preimage)
```

### 3.3 `intro_id`

```
preimage = b"dregg-intro-id-v1"
        || introducer_cell_id (32 bytes)
        || recipient_cell_id  (32 bytes)
        || target_cell_id     (32 bytes)
        || permissions_bits   (4 bytes — encoded AuthRequired mask)
        || introducer_nonce_be (8 bytes)
```

The `permissions_bits` encoding is the packed `AuthRequired` selector
already in `turn::action::Authorization`; γ.2 documents its bit layout
(spilled into `turn/src/action.rs::AuthRequired::to_bits / from_bits`
helpers, not yet existing).

```
intro_id = Commitment4::from_poseidon2(preimage)
```

### 3.4 Why include sender_nonce

A bilateral effect could in principle be replayed across two turns
(same `from`, `to`, `amount`). Without `sender_nonce`, both turns'
`transfer_id` would collide, and the verifier couldn't tell which
turn's sender-side proof matches which turn's receiver-side proof.
With `sender_nonce` in the preimage, ids are turn-scoped.

This also matches the constraint that *every Effect lives inside one
Turn* (the executor's invariant); the id naming the effect should be
that-Turn-scoped.

### 3.5 What about effects-hash binding

Couldn't we just use the per-effect hash from the existing
`effects_hash` chain? The bytes are similar. Three reasons we don't:

- `effects_hash` is a *running* accumulator over a per-cell projection,
  not a *named* id for a single effect. Extracting "the entry for
  transfer N" from a Poseidon2 chain requires walking the chain.
- `effects_hash` per-cell projections are not equal across sides of a
  bilateral effect (sender's projection omits the inflow row, etc.).
  An id derived from it would not match across sides.
- The canonical preimage above is *purely public* — no per-cell trace
  data needed — so a verifier with two `WitnessedReceipt`s and no other
  state can re-derive the id from the surface effect declaration in
  the turn's call_forest. (`Turn::hash` v3 covers the call_forest,
  and the WR carries the full Turn, so the verifier has the bytes.)

---

## 4. Off-AIR verifier algorithm

Given two `WitnessedReceipt`s (sender + receiver) — or three, for
`Introduce` — what does the verifier check?

### 4.1 Setup

The verifier already has, from γ.0:

- `TURN_HASH` agreement (rejection on mismatch).
- `EFFECTS_HASH_GLOBAL` agreement.
- `ACTOR_NONCE` agreement.
- `PREVIOUS_RECEIPT_HASH` agreement.

γ.2 layers the bilateral check on top, *only* over pairs (triples) that
have already passed the γ.0 match.

### 4.2 Pair construction

Given a turn touching N cells, the verifier knows from the turn's
`call_forest` exactly which bilateral effects to expect — `Transfer`,
`GrantCapability`, `Introduce` — and the role of each touched cell
in each. The verifier builds an *expected bilateral schedule*:

```
struct ExpectedBilateral {
    transfers: Vec<(from: CellId, to: CellId, amount: u64, transfer_id: Commitment4)>,
    grants:    Vec<(from: CellId, to: CellId, cap_entry_hash: Commitment4, grant_id: Commitment4)>,
    introduces: Vec<(introducer: CellId, recipient: CellId, target: CellId, intro_id: Commitment4)>,
}
```

This schedule is computable from `(call_forest, ACTOR_NONCE)` alone —
no per-cell PI needed.

### 4.3 Per-cell verification

For each touched cell `c` with proof `P[c]` and PI `pi[c]`:

1. **Count check.** From the expected schedule, the verifier computes:
   - `expected_outbound_transfer_count[c]` = number of transfers where
     `from == c`.
   - `expected_inbound_transfer_count[c]` = number where `to == c`.
   - (Same for grants and the three Introduce roles.)
   - Reject if `pi[c][OUTBOUND_TRANSFER_COUNT]` ≠ expected, etc.

2. **Root check.** The verifier computes the *expected root* for each
   direction by replaying the canonical absorb order over the schedule's
   entries restricted to cell `c`. The absorb order is:
   *trace-row-index order* in `c`'s per-cell projection. Since the
   projection is deterministic from `call_forest` + `c` (per
   `turn/src/executor.rs::convert_turn_effects_to_vm`), the verifier
   can predict it without consulting `c`'s actual trace. Reject if
   `pi[c][OUTGOING_TRANSFER_ROOT_BASE..+4]` ≠ expected.

3. (Same for `INCOMING_TRANSFER_ROOT`, the four grant/intro roots.)

The verifier needs no witness data for step (1) or (2) — they're
public-input checks against a public schedule. The witness becomes
necessary only if the per-cell *contributions* to the accumulator need
to be opened (auditor scope, not verifier scope).

### 4.4 Pair-level cross-check

After per-cell checks pass, the verifier confirms the bilateral
agreement directly:

```
for each Transfer(from, to, amount) in expected_schedule.transfers:
    transfer_id_F = derive_transfer_id(from, to, amount, ACTOR_NONCE)
    expected_outbound_absorb = poseidon2_step(prior_state[from], 
                                              transfer_id_F, to,
                                              amount_lo, amount_hi,
                                              domain="outbound")
    expected_inbound_absorb  = poseidon2_step(prior_state[to],
                                              transfer_id_F, from,
                                              amount_lo, amount_hi,
                                              domain="inbound")
    // The final accumulator state on each side is exposed in PI;
    // we already checked match in step (2) above. This loop is the
    // schedule-derivation phase; the actual cross-cell agreement is
    // step (2)'s reject-on-mismatch.
```

The pair-level check is *implicit* in the count + root checks: if both
sides' counts and roots match the schedule, and the schedule is derived
from a single `call_forest` shared via γ.0's `TURN_HASH` agreement,
then both sides describe the same Transfer.

### 4.5 What this catches

- **Sender claims to send 100, receiver records 50.** Outbound root
  absorbs `(transfer_id, to, 100)`; inbound root absorbs
  `(transfer_id, from, 50)`. Verifier's expected root for the receiver
  side is computed with `amount=100` (from the schedule), receiver's
  PI carries the `amount=50` root → mismatch, reject.
- **Sender invents a transfer to a non-existent cell.** Sender's
  count/root claims one outbound; the receiver is not a real cell ID
  in any other proof; no companion `WitnessedReceipt` exists. The
  γ.0 PI-match loop never sees a partner; the bundle has only one
  proof, but the schedule expects two. Reject for missing peer proof.
- **Receiver claims an inbound that the sender doesn't claim.** Mirror
  case. Receiver's count > 0; schedule's `expected_inbound_count[receiver]`
  computed from call_forest may also be > 0 if the call_forest declares
  the transfer; in that case both sides should agree. If the receiver
  claims an inbound the call_forest doesn't declare, count mismatch
  rejects.
- **Cross-turn replay.** Same `(from, to, amount)` reused across two
  turns. `transfer_id` differs (different `ACTOR_NONCE`), so the
  accumulators differ; the verifier reconstructs the schedule per
  turn from per-turn `ACTOR_NONCE`. No collision.
- **Permission tampering on Introduce.** `intro_id` includes the
  `permissions_bits`; an introducer who broadcasts one permission to
  the recipient's side and a different one to the target's side
  produces two distinct `intro_id` values; the verifier's schedule
  expects one; mismatch on at least one root.

### 4.6 What this does NOT catch (still executor-trusted at γ.2)

- **The actual c-list mutation on the grantor side.** Grant's outbound
  binding names the `cap_entry_hash` but does not algebraically prove
  the grantor *held* that cap pre-state. 7-ε (committed `cap_table_root`
  + AIR Merkle membership) closes this. Until then, the AIR proves the
  *consume row was emitted with this hash* but not *the row corresponded
  to a real prior slot*.
- **Signature on the bearer cap.** Stage 9 work (signature-in-circuit).
- **Cross-federation Introduce where introducer and recipient have
  different `federation_id`s.** Phase 1 PI doesn't include
  `peer_federation_id`; a malicious cross-fed introducer could
  fabricate a recipient proof from a different federation. Closed
  by promoting `federation_id` into the bilateral preimage (additive
  to §3.3) — flagged for Phase 1.5.

---

## 5. Outgoing / incoming Merkle sets vs. flat fields — tradeoffs

Two structural options for the per-cell accumulators:

### 5.1 Flat fields (single-binding case)

For a turn with at most one bilateral effect per kind per cell, we
could surface the id directly:

```
pub const OUTGOING_TRANSFER_ID_BASE: usize = ...;   // 4 felts
pub const OUTGOING_TRANSFER_PEER: usize = ...;      // 1 felt (cell-id projection)
```

Verifier comparison is byte-for-byte. No accumulator absorb needed.

**Pro:** simplest possible PI semantics; the id is right there.
**Con:** turns *routinely* batch multiple transfers — a payroll cell
sending to N employees, a settlement batching M trades. Flat fields
force one PI slot per transfer (5 felts each), and PI vector size
grows linearly with the batch.

### 5.2 Merkle / Poseidon2 accumulator (variable cardinality)

The recommended γ.2 shape (§2.1): one 4-felt root per direction, regardless
of how many transfers. Verifier reconstructs the expected absorbed sequence
from the schedule.

**Pro:** PI size is independent of batch size.
**Con:** verifier must know absorb order; per-effect detail isn't
extractable without witness data. A static analyzer or block explorer
that wants to display "this turn sent 5 transfers" can't read just the
root — they need to reconstruct from `call_forest`, but that's already
in `Turn`, so this is fine.

### 5.3 Recommendation

**Use Merkle/accumulator (5.2) uniformly.** Even for the single-binding
case (`Introduce`, which touches three cells with one effect each),
batching with `Transfer` and `Grant` in the same turn means a cell's
accumulator may have entries from multiple effect kinds — different
domain separators in the absorb, but same root field.

The "single-binding case" the brief mentions is really *single effect of
this kind per cell per turn* — even there, the accumulator with one
absorb is just `Poseidon2(empty, id, peer, amount)`, a one-step
computation. No measurable cost over a flat field.

### 5.4 Capacity / cap

A cell can be touched by at most `MAX_TOUCHED_CELLS = 8` (per
`STAGE-7-GAMMA-AGGREGATION-DESIGN.md` open question 2). Within one
cell's per-cell proof, how many bilateral effects can the accumulator
absorb before rows fill up? The trace length is dynamic per turn; the
prover pads to the next power of two. A single cell can be involved
in `O(trace_len)` transfers in principle — the accumulator scales
freely.

The per-cell `*_COUNT` PI fields exist precisely so the verifier can
predict the absorb sequence length before reconstructing.

---

## 6. AIR work

The AIR is extended so that the in-trace transfer-effect data is bound
to the bilateral PI. Today the per-cell AIR's `Transfer` row
(`circuit/src/effect_vm.rs::Transfer` selector — selector index 1)
constrains:

- `bal_lo` delta == `amount` (signed by `direction`).
- `effects_hash` chain absorbs `(amount, direction, peer_cell_id_truncated)`.

γ.2 adds two new constraint groups.

### 6.1 In-trace transfer_id binding

At each `s_transfer = 1` row, the AIR computes (as auxiliary trace
columns) the canonical `transfer_id` from the row's data:

```
new aux columns (one set per bilateral kind):
  bilat::TRANSFER_ID_BASE      : 4 felts — in-trace recomputed transfer_id
  bilat::TRANSFER_PREIMAGE_BASE: ? felts — packed preimage components
                                  (the AIR's Poseidon2 gadget consumes these)
```

Constraint (selector-gated by `s_transfer`):

```
TRANSFER_ID = Poseidon2(
    domain_separator("dregg-transfer-id-v1"),
    from_cell_id_felts,   // 8 felts, cell-id-decomposed
    to_cell_id_felts,     // 8 felts
    amount_lo, amount_hi, // 2 felts (full u64, requires W-6 widening — 
                          //  P1-18 from STAGE-7-PLUS-DESIGN.md)
    actor_nonce_felts,    // (already in PI as ACTOR_NONCE)
)
```

The `from`/`to` projections at the row come from existing transfer
params columns (today truncated to 4 bytes — `circuit/src/effect_vm.rs:421
DIRECTION`, neighboring columns). γ.2 requires lifting these to the
full 8-felt cell-id decomposition (mirror of `cclerk::bytes32_to_babybear`,
per AUDIT-circuit P1-2). This is the same column-widening the AUDIT-circuit
fix recommends; γ.2 makes it load-bearing.

### 6.2 Per-direction accumulator binding

After computing the row's `transfer_id`, the AIR absorbs it into a
running accumulator on the *correct direction's* PI:

```
new aux columns:
  bilat::OUTBOUND_ACC_BASE  : 4 felts — running outbound accumulator
  bilat::INBOUND_ACC_BASE   : 4 felts — running inbound accumulator
  bilat::OUTBOUND_COUNT_ACC : 1 felt  — running outbound count
  bilat::INBOUND_COUNT_ACC  : 1 felt  — running inbound count
```

Transition constraint (per row):

```
// Direction selector splits the absorb between outbound and inbound.
// `s_transfer * direction` is the outbound indicator;
// `s_transfer * (1 - direction)` is the inbound indicator.

OUTBOUND_ACC_next = if (s_transfer * direction) == 1 {
    Poseidon2_step(OUTBOUND_ACC_cur,
                   TRANSFER_ID_cur, peer_cell_id_felts, amount_lo, amount_hi,
                   domain="outbound")
} else {
    OUTBOUND_ACC_cur  // unchanged
}

OUTBOUND_COUNT_ACC_next = OUTBOUND_COUNT_ACC_cur + (s_transfer * direction)
```

(Symmetric for `INBOUND_*` and `direction == 0`.)

Boundary constraints:

- Row 0: `OUTBOUND_ACC = Commitment4::empty()`, `OUTBOUND_COUNT_ACC = 0`,
  same for `INBOUND_*`.
- Last row: `OUTBOUND_ACC == PI[OUTGOING_TRANSFER_ROOT_BASE..+4]`,
  `OUTBOUND_COUNT_ACC == PI[OUTBOUND_TRANSFER_COUNT]`, same for `INBOUND_*`.

This is *the* binding from in-trace transfer-effect data to PI.

### 6.3 Grant + Introduce mirror

Same constraint shape, different selectors (`s_grant`, `s_introduce`),
different domain separators, different aux column groups
(`bilat::GRANT_ID_BASE`, `bilat::OUTBOUND_GRANT_ACC_BASE`, etc.;
`bilat::INTRO_ID_BASE` and per-role accumulators for the three
Introduce roles).

For `Introduce`, the AIR row currently has a single `intro_hash`
column (`circuit/src/effect_vm.rs::Introduce` selector). γ.2 replaces
that with the proper `intro_id` Poseidon2 recomputation, and the
*role selector* (introducer / recipient / target) determines which
accumulator absorbs the id.

The role selector requires either:

- (a) Three new selectors: `s_intro_introducer`, `s_intro_recipient`,
  `s_intro_target`. Each row sets exactly one (mutual-exclusion
  constraint over the existing selector vocabulary). This keeps the
  AIR's per-effect-kind selector model.
- (b) One `s_introduce` selector plus a 2-bit role column with
  mutual-exclusion + role-determined accumulator routing.

**Recommendation: (a).** Adds 3 selectors to NUM_EFFECTS (46 → 49)
but is simpler to reason about; existing selector mutual-exclusion
infrastructure handles it.

### 6.4 Column budget

Current `EFFECT_VM_WIDTH = 105`. γ.2 adds:

```
Transfer:    TRANSFER_ID(4) + PREIMAGE_PACK(0, reusing existing) 
            + OUTBOUND_ACC(4) + INBOUND_ACC(4) + counts(2)            = 14 columns
Grant:       GRANT_ID(4) + OUTBOUND_GRANT_ACC(4) + INBOUND_GRANT_ACC(4) + 
            cap_entry_hash(4 — currently exists, reused) + counts(2)  = 14 columns
Introduce:   INTRO_ID(4) + 3 role accumulators (4 each) + counts(3) +
             3 role selectors (1 each)                                 = 18 columns
Total:                                                                   46 columns
```

`EFFECT_VM_WIDTH` grows from 105 to ~151. This is well within Plonky3's
practical column limit (low-thousands). FFT cost scales linearly in
column count, so a ~1.4× slowdown on prover side — same order as
γ.1's projected impact.

The aux columns can be deduplicated: `OUTBOUND_ACC` for transfer,
grant, and introduce-as-introducer all run in parallel on the same
trace, but their constraint groups are gated by disjoint selectors,
so they could in principle reuse the same physical columns with
multiplexed-by-selector update rules. Recommend NOT doing this in
γ.2 first cut — separate columns are easier to debug.

### 6.5 Sum-check sanity

The PI fields `OUTBOUND_TRANSFER_COUNT`, etc. are matched against the
trace's running count columns at the last row. The AIR enforces:

```
last_row.OUTBOUND_COUNT_ACC == PI[OUTBOUND_TRANSFER_COUNT]
last_row.OUTBOUND_ACC      == PI[OUTGOING_TRANSFER_ROOT_BASE..+4]
```

This is the same shape as today's `CUSTOM_COUNT_ACC` →
`CUSTOM_EFFECT_COUNT` sum-check (`circuit/src/effect_vm.rs:351`,
constraint at lines ~3195-3325). Already-paved-path.

---

## 7. Migration — coexistence with single-cell proofs

How do per-cell proofs that have no cross-cell binding (e.g., a turn
that only mutates one cell, or a CapTP-mirror Turn that doesn't touch
balances) interact with γ.2?

### 7.1 Sentinel defaults

When a cell has no bilateral effects of a kind in this turn:

- `OUTBOUND_TRANSFER_COUNT` = 0, `INBOUND_TRANSFER_COUNT` = 0.
- `OUTGOING_TRANSFER_ROOT` = `Commitment4::empty()`, `INCOMING_TRANSFER_ROOT` = same.
- Same for grant / introduce slots.

The AIR's bilateral aux columns initialize to empty and never update
(no `s_transfer`, `s_grant`, `s_introduce` rows in the trace). The
boundary constraint trivially passes (`empty == empty`).

The verifier's cross-cell loop *skips* a cell whose all-bilateral
counts are 0; no peer is expected.

### 7.2 `IS_AGENT_CELL` and its γ.2 generalization

The γ.0 `ACTOR_NONCE` field (`circuit/src/effect_vm.rs::pi::ACTOR_NONCE`)
is bound to row-0 of the agent cell's trace's `NONCE` column. Other
touched cells in the same turn don't have their nonce bound this way —
they participate without being the actor.

`EXECUTOR-HONESTY-AUDIT.md T5 (γ.2 note)` calls for an `IS_AGENT_CELL`
PI gate so the boundary constraint fires only on the agent's per-cell
proof. γ.2 should land this in conjunction:

```
pub const IS_AGENT_CELL: usize = 74;  // 1 felt, 0 or 1
```

When `IS_AGENT_CELL == 1`, all the γ.0 actor-nonce boundary checks
fire on this proof. When 0, they're suppressed (the cell participates
in the turn but isn't the signer). The verifier checks across the
bundle's N proofs that *exactly one* has `IS_AGENT_CELL == 1`.

This is *the* migration mechanism between today's single-cell shape
and γ.2's bundle shape: a single-cell turn touching only the agent
sets `IS_AGENT_CELL = 1` on its sole proof, all bilateral counts to
0, and behaves exactly as today (modulo the added PI slots whose
values are all sentinels). A multi-cell turn has one proof with
`IS_AGENT_CELL = 1` and N-1 with `IS_AGENT_CELL = 0`, each
contributing to the bilateral roots as appropriate.

### 7.3 Backward-compat: pre-γ.2 receipts

`TurnReceipt` doesn't carry PI directly; PI travels with the proof
on `Turn.execution_proof`. A pre-γ.2 receipt's proof has 38-felt PI;
a γ.2 receipt has 75-felt PI (BASE_COUNT = 73 + IS_AGENT_CELL + 1
spare). The verifier dispatches on PI length to select the version
of the matching loop.

For receipts on existing chains, the chain doesn't break: γ.2
verifiers run the legacy γ.0 matching loop on pre-γ.2 receipts.
New proofs use γ.2.

### 7.4 Custom proof base

`CUSTOM_PROOFS_BASE = BASE_COUNT = 73 (γ.2) + 1 (IS_AGENT_CELL) = 74`.

The custom-proof PI entries shift by 36 felts. The PI-decoding utilities
(`circuit/src/effect_vm.rs::custom_proof_entry_offset` etc.) are the
single source of truth — they already compute from `BASE_COUNT`, so the
shift is automatic. The constant `pi::BASE_COUNT` is the only thing
that changes; callers compute from it.

---

## 8. Phase 2 sketch: joint aggregation proof

γ.2 Phase 1 is PI-only — the verifier runs N per-cell proofs and a
*classical* cross-cell match loop in Rust. Phase 2 lifts the cross-cell
match itself into a STARK so that "the N proofs are bilaterally
consistent" is itself a single aggregation proof.

### 8.1 Inputs

The aggregation AIR takes as input:

- N inner Effect VM proofs (recursive verification — same shape as
  `STAGE-7-GAMMA-AGGREGATION-DESIGN.md §2A`).
- The expected bilateral schedule (derivable from `call_forest`, which
  is in `TURN_HASH` preimage and verifiable independently).

### 8.2 What it proves

```
∀ touched cell c:
  pi[c][OUTBOUND_TRANSFER_COUNT] == |outbound_transfers(c, schedule)|
  pi[c][OUTGOING_TRANSFER_ROOT]  == fold_canonical(outbound_transfers(c, schedule))
  ... (same for inbound, grant, introduce roles) ...

AND for each (sender, receiver) pair in the schedule:
  exists a Transfer in pi[sender].outbound and pi[receiver].inbound 
  with the same transfer_id, peer-fields aligned by role
```

The Rust loop in §4 becomes a circuit. The aggregation AIR's PI is the
*reduced* set: `TURN_HASH`, `EFFECTS_HASH_GLOBAL`, `ACTOR_NONCE`,
`PREVIOUS_RECEIPT_HASH`, `BILATERAL_CONSISTENT` (a single felt: 1 iff
all pair checks passed). The outer cclerk/verifier never sees N inner
PIs; it sees the single aggregation proof and the shared turn-level PI.

### 8.3 Why Phase 1 first

- Phase 1 PI fields are *also the inputs* to Phase 2's aggregation —
  the bilateral roots are precisely what an aggregation step folds.
  Phase 2 doesn't change the per-cell AIR; it only adds an outer AIR
  that consumes the existing per-cell PI.
- Phase 1's verifier algorithm (§4) is the spec for what Phase 2's
  aggregation AIR must constrain. Implementing it in Rust first, with
  full test coverage, lets us treat the AIR as a *recompilation* of a
  trusted reference.
- The recursive-verifier shell (`circuit/src/plonky3_verifier_air.rs::RecursiveIvcStep`)
  exists; the aggregation AIR is a specialization. Phase 2 = engineering
  on a known shape, not research. No folding scheme choice needed yet.

### 8.4 What Phase 2 unlocks

- **Constant-size verification.** A turn with 10 touched cells produces
  one outer proof; today γ.0 + γ.2 requires the verifier to run 10
  inner verifies.
- **`WitnessedReceipt` simplification.** Phase 2's aggregation proof
  is *the* proof on the receipt; per-cell witnesses move from
  "required for verify" to "required for replay/audit only."
- **Stage 7-ζ enablement.** Once Phase 2 lands, the chain-IVC step
  has a single proof per turn to fold — much smaller folding step,
  much smaller research bet on the IVC scheme.

### 8.5 Out of Phase 2 scope

Cross-federation aggregation (introducer on fed A, recipient on fed B,
target on fed C) requires per-federation snapshot consistency, which
is bridge work. Phase 2 stays single-federation.

---

## 9. Concrete implementation order

Recommended sub-stages:

### γ.2.0 — PI surface + sentinels (1 week)

- Add the constants in `circuit/src/effect_vm.rs::pi` per §2.1.
- Default all γ.2 PI to sentinels in the prover side
  (`turn/src/executor.rs::convert_turn_effects_to_vm` extends the PI
  vector but writes only sentinels for now — `BASE_COUNT` grows,
  custom-proof offsets shift, everything else passes through).
- Verifier accepts γ.2 PI with all-sentinel bilateral fields as
  equivalent to legacy γ.0 PI.
- Tests: existing differential tests pass with the PI grown.

### γ.2.1 — AIR bilateral constraints (3 weeks)

- Add the aux columns + selectors per §6.
- Wire row-level Poseidon2 gadget calls; reuse existing Poseidon2 AIR.
- Boundary constraints linking aux columns → γ.2 PI.
- Tests:
  - Honest 2-cell `Transfer` produces matching outbound/inbound roots.
  - Adversarial test: prover writes mismatched amount on one side →
    AIR rejects (boundary fail).
  - Adversarial test: prover swaps direction → wrong accumulator
    absorbs → boundary fail on at least one side.

### γ.2.2 — Verifier cross-cell match loop (1 week)

- Extend `verify_proof_carrying_turn_bundle` with §4's algorithm.
- The schedule reconstructor is a pure function over `call_forest +
  ACTOR_NONCE`; lives in `turn/src/bilateral_schedule.rs` (new file
  in scope but for design only).
- Tests:
  - Two honest WRs of a Transfer pair → verifier accepts.
  - WR pair with mismatched amount → verifier rejects.
  - WR pair where one side is missing → verifier rejects.
  - WR pair across replayed turns (same `(from,to,amount)`, different
    `ACTOR_NONCE`) → distinct transfer_ids, accepts both pairs
    independently.

### γ.2.3 — `IS_AGENT_CELL` + migration (1 week)

- Add the `IS_AGENT_CELL` PI slot and the agent-cell vs. non-agent-cell
  AIR gating.
- Verifier enforces exactly-one-IS_AGENT_CELL across the bundle.
- Document the migration path in code comments.

### γ.2 Phase 2 (deferred, ~4 weeks)

Per §8. Lands after γ.2.0-γ.2.3 are exercised in production.

---

## 10. Open questions for the architect

1. **`peer_federation_id` in the bilateral preimage** — when do we
   commit to cross-federation Transfer/Grant/Introduce, given that
   bridge work owns cross-fed token movement? Recommend: include
   `peer_federation_id` in §3's preimages now, even at zero for
   intra-fed effects, so future cross-fed extension is additive.
2. **Cell-id decomposition for the AIR** — 8 BabyBear felts per cell-id
   (per AUDIT-circuit P1-2 fix recommendation) vs. 4 felts. 8 gives
   collision resistance matching the 32-byte CellId; 4 saves columns.
   Lean to 8 to avoid yet another truncation footgun.
3. **`MAX_TOUCHED_CELLS = 8`** — confirmed for γ.2? Real turns rarely
   exceed 4; 8 leaves headroom. Above 8, what's the protocol —
   reject-as-too-large, or chain into a multi-bundle aggregation?
4. **Sum-check arithmetic at BabyBear** — counts are small (≤ 2^10
   in practice). The sum-check is a chained add, sound at BabyBear's
   31-bit modulus as long as count ≤ 2^30. Confirm AIR's count
   columns are range-checked to 2^20 say, by lookup or explicit
   decomposition. (See AUDIT-circuit P2-4 — range-check lookups.)
5. **Selector explosion** — γ.2 adds ~3 selectors (intro-as-introducer,
   intro-as-recipient, intro-as-target). At `NUM_EFFECTS = 46` today,
   this brings it to ~49. The mutual-exclusion polynomial degree
   scales; confirm it stays within Plonky3's degree budget (typically
   3-5).
6. **The `Introduce` 3-cell case where one cell is BOTH grantor and
   target** — e.g., a CapTP introduce where `introducer = target` (Alice
   introduces Bob to Alice herself). Two roles on one cell. The
   per-cell PI's per-role accumulators absorb under both roles; this
   is consistent but worth a test case.

---

## 11. Closing

γ.2 Phase 1 turns "the executor saw both sides of the Transfer" into
"the algebra binds both sides' proofs to the same canonical
`transfer_id`." It does so with strictly additive PI fields (existing
proofs continue to verify as sentinels), one new AIR constraint group
per bilateral kind, and a verifier-side schedule reconstruction that
needs no per-cell witness data. Phase 2 lifts the verifier's Rust loop
into a recursive aggregation AIR using the same PI; nothing about
Phase 1's PI surface changes.

The path is engineering, not research. The recursive-verifier shell
exists; the Poseidon2 gadget exists; the per-cell AIR's column-extension
pattern is established (γ.0 added 13 PI slots already). γ.2 is the
sibling work to γ.1 (projection totality) and 7-δ (witness packaging);
they compose orthogonally — γ.1 binds *which* effects appear in the
global hash, γ.2 binds *cross-cell* agreement on each bilateral effect,
7-δ packages witnesses so that an auditor can replay both.

The smallest first chunk that delivers a usable artifact: **γ.2.0 +
γ.2.1 (transfer-only)**. Once a single bilateral Transfer is bound
end-to-end (PI + AIR + verifier), grant and introduce are mechanical
extensions of the same pattern.
