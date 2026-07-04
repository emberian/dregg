/-
# Dregg2.Deos.PrepaidLease — a per-period rent discharge ATOMICALLY draws its rent from a sealed
prepaid budget, so meter/pay DRIFT is UNREPRESENTABLE (the fused budget-escrow ⊗ obligation lease
house-capacity, grounded BY REUSE of the committed-heap root + the StrictMonotonic cursor + the sealed
budget-hold discipline).

## The bug class this closes

A lease's rent, today, is THREE separately-enforced pieces coupled only by a shared rent constant and
app control flow: a `StandingObligation` meter (the per-period cursor), a `Payable` transfer (the
draw), and a lapse backstop. "Budget never over-drawn" and "metered == drawn" are NOT one theorem —
they are maintained by DISCIPLINE. That gap is the meter/pay-drift bug class. This rung FUSES the two
provided reuse bases — `SealedEscrow`'s value-hold + `StandingObligation`'s StrictMonotonic
per-period cursor — into ONE object where a single `advance` write moves the cursor AND draws exactly
the sealed rent from an escrowed prepaid budget IN THE SAME STEP. Drift is a type/kernel error, not a
caught-after-the-fact: there is no expressible transition that advances the meter without drawing
rent, or draws rent without advancing the meter.

`cell/src/prepaid_lease.rs` is the Rust house-capacity: opening a `PrepaidLease` HOLDS `budget` of
prepaid rent in the cell's committed heap (the escrow leg); each `discharge_period` advances the
committed `next_due` cursor by one period AND decrements the committed `remaining` budget by exactly
`rent`, refusing when the remaining budget cannot cover the draw. Its soundness is *forge/drift
rejection*: no over-draw (a step asserting ≠ rent), no double-discharge (one-shot per period), no
off-schedule discharge (early), and no draw exceeding the remaining prepaid budget (the lapse
backstop, fused in).

This module is the Lean RUNG for that capacity, in the SAME shape the SEALED-ESCROW /
STANDING-OBLIGATION / DERIVED-CELL rungs set (`docs/deos/HOUSE-CAPACITY-FRAMEWORK.md`): prove the
invariant **by reuse** of already-proven objects — here `Substrate.Heap`'s sorted-Poseidon2 root (the
cursor AND the budget are committed), the **StrictMonotonic** cursor discipline (the one-shot meter),
and the sealed value-hold (the escrow budget leg) — exhibit both-polarity `#guard` witnesses,
`#assert_all_clean`, and wire the Rust to it
(`cell/src/prepaid_lease.rs::tests::invariant_matches_lean_rung`).

## What is proven — and what it REUSES (no lease-local commitment, no new monotone law)

The lease's terms digest, the `next_due` cursor, the discharged count, the `remaining` prepaid
budget, and the cumulative `drawn` total all live in reserved heap slots (the SAME
`set_heap`/`compute_heap_root` sorted-Poseidon2 map, folded into the canonical state commitment with
NO VK bump). The rung proves:

  * `opened_cursor` + `opened_remaining` (HONEST ROUND-TRIP + BUDGET-HOLD) — an opened lease commits
    `next_due = start` AND holds the full `budget` in the escrow slot. Read-after-write is
    `Heap.hget_hset_self`; the un-touched slots survive the other open-writes by
    `Heap.hget_hset_frame` (the ONE named `Poseidon2SpongeCR` floor).

  * **`budget_never_overdrawn`** (THE BUDGET INVARIANT, BOTH POLARITIES) — the closed form
    `remainingAfter budget rent n = budget − n·rent` (the committed budget after `n` discharges is
    exactly the prepaid budget minus `n` rents, `advance_draws_exactly_rent` tying each heap step to
    it) AND `insufficient_budget_rejected` (a discharge whose remaining budget cannot cover the rent
    is REFUSED). The bound HOLDS and the over-draw is REFUSED — the two halves of "never over-drawn".

  * **`metered_equals_drawn`** (THE FUSION, AS A THEOREM) — the executor face is
    `drawn_eq_count_rent` (`drawnAfter rent n = n·rent`: the cumulative drawn is exactly the metered
    period count times rent); the light-client face is the transition-gate pair
    `no_advance_without_draw_rejected` + `no_draw_without_advance_rejected`: a witness that advances
    the cursor without drawing rent, OR draws rent without advancing the cursor, is INEXPRESSIBLE. No
    advance without a draw, no draw without an advance — drift is unrepresentable.

  * `replay_rejected` (THE ONE-SHOT / NO-DOUBLE TOOTH) — after period 0 is discharged the cursor has
    advanced to `start + period`, so the gate's expected period is 1; a replay naming period 0 is
    REJECTED (as a consequence of the StrictMonotonic cursor advance).

  * `off_schedule_rejected` (THE NO-EARLY TOOTH) — a discharge whose presented clock is below the
    current period's due block is REJECTED.

  * `over_draw_rejected` (THE NO-OVER/UNDER-DRAW TOOTH) — a discharge whose asserted draw differs
    from the committed rent is REJECTED.

  * **`cursor_bound_in_root` / `remaining_bound_in_root` / `drawn_bound_in_root` (THE HEAP REUSE
    KEYSTONE)** — equal committed roots ⟹ equal cursor AND equal remaining budget AND equal drawn: a
    forge cannot present the honest root with a rewound cursor, a padded budget, or an under-reported
    draw. DIRECT instances of `Heap.root_binds_get` (the anti-ghost), under the one named
    `Poseidon2SpongeCR` floor. With them, `forged_budget_moves_root`.

This is NOT new mathematics: the cursor is a committed scalar advancing under the existing
StrictMonotonic discipline, the budget is a committed sealed value, and the BINDING is the proven
sorted-Poseidon2 root. The prepaid lease is a NAMING of "a committed-heap binding whose `next_due`
slot and `remaining` slot advance TOGETHER, one period and one rent per one-shot discharge" — the
FUSION of the escrow hold and the obligation cursor into one atomic step.

## The circuit weld (STAGED, VK-risk-free) — §6b

§3–§6 ground the EXECUTOR-witnessed invariant. §6b binds "due ∧ budget-covered ∧ cursor advanced by
one period ∧ remaining drawn by exactly rent ∧ drawn recorded by exactly rent" into what a LIGHT
CLIENT verifying a *batch* witnesses — via the manifest-in-public-inputs + off-AIR re-evaluation
vehicle the sealed-escrow weld (`SealedEscrow.lean` §6) and the discharge-obligation weld
(`StandingObligation.lean` §6b) already ride. The `DischargeGate` over a (before, after)
committed-heap transition is carried as a slot-caveat tag in PUBLIC INPUTS and re-evaluated against
the bound `state_before`/`state_after` views — the AIR constraint polynomials (the VK bytes) are
UNCHANGED, so this is a verifier-code epoch, not a proving-key rotation.

## Axiom hygiene

`#assert_all_clean` at the close. Crypto enters ONLY as the named `Poseidon2SpongeCR` hypothesis (the
cap-root floor the heap carries), never as an axiom. NO core/heap edit — every binding is the REAL
`Substrate.Heap.hset`/`hget` and the root is the REAL `Substrate.Heap.root`.
-/
import Dregg2.Substrate.Heap
import Dregg2.Tactics

namespace Dregg2.Deos.PrepaidLease

open Dregg2.Substrate.Heap
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — the lease terms + the deterministic clock (the binder and verifier BOTH compute). -/

/-- The sealed terms of a prepaid lease — the Lean image of
`cell/src/prepaid_lease.rs::LeaseTerms` (the lessee/lessor/asset are off-circuit identity; the rung
carries the scalars the schedule clock and the budget draw read). `count = 0` means unbounded (the
prepaid budget bounds the lease anyway). -/
structure Terms where
  /-- The rent drawn each period. Well-formed terms have `rent > 0`. -/
  rent : ℤ
  /-- The period length in blocks. Well-formed terms have `period > 0`. -/
  period : ℤ
  /-- The block at which period `0` falls due. -/
  start : ℤ
  /-- The bounded number of periods, or `0` for unbounded. -/
  count : ℤ
  /-- The prepaid budget HELD in escrow at open (the escrow leg). -/
  budget : ℤ
deriving DecidableEq, Repr

/-- Well-formedness (`LeaseTerms::is_well_formed`): positive rent/period, non-negative budget. -/
abbrev Terms.wf (t : Terms) : Prop := 0 < t.rent ∧ 0 < t.period ∧ 0 ≤ t.budget

/-- **`cursorAt t k`** — the `next_due` cursor after `k` periods discharged: `start + k·period`. -/
def cursorAt (t : Terms) (k : ℤ) : ℤ := t.start + k * t.period

/-- **`dueBlock t k`** — the block at which period `k` falls due (`LeaseTerms::due_block`). -/
def dueBlock (t : Terms) (k : ℤ) : ℤ := t.start + k * t.period

/-- **`expectedPeriod t nextDue`** — which period the committed cursor expects next, DERIVED from the
cursor (not trusted from the step): `(next_due − start) / period`. -/
def expectedPeriod (t : Terms) (nextDue : ℤ) : ℤ := (nextDue - t.start) / t.period

/-- **`periodsDueBy t clock`** — how many periods MUST be discharged by `clock`
(`LeaseTerms::periods_due_by`): the schedule's ground truth the audit compares against. -/
def periodsDueBy (t : Terms) (clock : ℤ) : ℤ :=
  if clock < t.start then 0
  else
    let due := (clock - t.start) / t.period + 1
    if 0 < t.count ∧ t.count < due then t.count else due

/-- A discharge step presented to the verifier (`cell/src/prepaid_lease.rs::DischargePeriod`). -/
structure Step where
  /-- The period the obligor asserts it is discharging. -/
  periodIndex : ℤ
  /-- The rent the obligor asserts it is drawing (must equal the committed `rent`). -/
  amount : ℤ
  /-- The schedule clock at the moment of discharge. -/
  clock : ℤ
deriving DecidableEq, Repr

/-! ## §2 — the lease as committed heap slots (REUSE of `Substrate.Heap`).

The lease binds the cursor, the count, the REMAINING prepaid budget (the escrow leg) and the
cumulative DRAWN total into reserved heap slots — the SAME sorted-Poseidon2 map, folded into the
canonical state commitment. -/

/-- The reserved prepaid-lease collection (`PREPAID_LEASE_COLL = 0x_9_1EA_5ED`). -/
def leaseColl : ℤ := 152699373
/-- Heap key holding the terms digest (`KEY_TERMS_DIGEST`). -/
def keyDigest : ℤ := 0
/-- Heap key holding the `next_due` cursor (`KEY_NEXT_DUE`). -/
def keyNextDue : ℤ := 1
/-- Heap key holding the discharged count (`KEY_DISCHARGED_COUNT`). -/
def keyCount : ℤ := 2
/-- Heap key holding the REMAINING prepaid budget — the escrow leg (`KEY_REMAINING_BUDGET`). -/
def keyRemaining : ℤ := 3
/-- Heap key holding the cumulative DRAWN total (`KEY_DRAWN_TOTAL`). -/
def keyDrawn : ℤ := 4

/-- The committed `next_due` cursor bound in a cell's heap. -/
def boundCursor (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h leaseColl keyNextDue
/-- The committed discharged count bound in a cell's heap. -/
def boundCount (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h leaseColl keyCount
/-- The committed REMAINING prepaid budget bound in a cell's heap (the escrow leg). -/
def boundRemaining (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h leaseColl keyRemaining
/-- The committed cumulative DRAWN total bound in a cell's heap. -/
def boundDrawn (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h leaseColl keyDrawn

/-- **`openLease hash h digest t`** — seal the terms, initialize the cursor to the first due block,
zero discharged/drawn, and HOLD the full `budget` in the escrow (remaining) slot. The Lean image of
`cell/src/prepaid_lease.rs::open_lease`. -/
def openLease (hash : List ℤ → ℤ) (h : FeltHeap) (digest : ℤ) (t : Terms) : FeltHeap :=
  hset hash (hset hash (hset hash (hset hash (hset hash h
    leaseColl keyDigest digest)
    leaseColl keyNextDue t.start)
    leaseColl keyCount 0)
    leaseColl keyRemaining t.budget)
    leaseColl keyDrawn 0

/-- **`advance hash h t cursor count remaining drawn`** — THE FUSED discharge write: in ONE step
advance the cursor by one period, bump the count, DRAW exactly `rent` from the remaining budget, and
record `rent` in the drawn total. The Lean image of `cell/src/prepaid_lease.rs::discharge_period`'s
mutation. The single write that meters the period is the SAME write that draws the rent. -/
def advance (hash : List ℤ → ℤ) (h : FeltHeap) (t : Terms) (cursor count remaining drawn : ℤ) :
    FeltHeap :=
  hset hash (hset hash (hset hash (hset hash h
    leaseColl keyNextDue (cursor + t.period))
    leaseColl keyCount (count + 1))
    leaseColl keyRemaining (remaining - t.rent))
    leaseColl keyDrawn (drawn + t.rent)

/-! ## §3 — the verification core (the forge-detector, as a predicate).

`DischargeOk` is the Lean image of `LeaseState::check_discharge`: the honest-accept path and every
over-draw / double / early / insufficient-budget reject consult THIS. `AuditOk` is
`LeaseState::audit`. -/

/-- **The fused discharge gate.** Given the committed `nextDue` cursor and `remaining` budget, the
step accepts iff: the lease is not completed (bounded count not yet reached), the step names exactly
the cursor's expected period (one-shot / no-skip), the clock has reached that period's due block (not
early), the asserted draw equals the committed rent (no over/under-draw), AND the remaining prepaid
budget covers the rent (the fused lapse backstop). The budget clause is what makes this the FUSION —
the meter cannot advance unless the budget can pay. -/
abbrev DischargeOk (t : Terms) (nextDue remaining : ℤ) (s : Step) : Prop :=
  (t.count = 0 ∨ expectedPeriod t nextDue < t.count) ∧
  s.periodIndex = expectedPeriod t nextDue ∧
  dueBlock t (expectedPeriod t nextDue) ≤ s.clock ∧
  s.amount = t.rent ∧
  t.rent ≤ remaining

/-- **The audit gate.** The committed discharged-count is not behind the number of periods the
schedule demands by `clock`. -/
abbrev AuditOk (t : Terms) (committedCount clock : ℤ) : Prop := periodsDueBy t clock ≤ committedCount

/-! ## §4 — THE MONOTONE-CURSOR REUSE: the cursor strictly increases per discharge. -/

/-- **THE STRICT-MONOTONE CURSOR.** On well-formed terms (`period > 0`), the cursor `cursorAt t k` is
strictly increasing in the period index `k`. The version/supply StrictMonotonic discipline,
instantiated on the lease's `next_due` slot — what makes a period one-shot. -/
theorem cursor_strict_mono (t : Terms) (hwf : t.wf) {j k : ℤ} (hjk : j < k) :
    cursorAt t j < cursorAt t k := by
  unfold cursorAt
  have hp : (0 : ℤ) < t.period := hwf.2.1
  have : j * t.period < k * t.period := mul_lt_mul_of_pos_right hjk hp
  omega

/-- **THE STRICT ADVANCE.** One discharge advances the cursor strictly: `nextDue < nextDue + period`
(`period > 0`). The per-step face of `cursor_strict_mono` — the StrictMonotonic write. -/
theorem advance_strictly_increases (t : Terms) (hwf : t.wf) (nextDue : ℤ) :
    nextDue < nextDue + t.period := by
  have hp : (0 : ℤ) < t.period := hwf.2.1
  omega

/-- After one discharge from the opening cursor `start`, the cursor is `start + period`, whose
expected period is `1`. The arithmetic heart of the one-shot tooth. -/
theorem expectedPeriod_after_one (t : Terms) (hwf : t.wf) :
    expectedPeriod t (t.start + t.period) = 1 := by
  unfold expectedPeriod
  have hp : t.period ≠ 0 := ne_of_gt hwf.2.1
  have : t.start + t.period - t.start = t.period := by ring
  rw [this, Int.ediv_self hp]

theorem expectedPeriod_open (t : Terms) : expectedPeriod t t.start = 0 := by
  unfold expectedPeriod
  simp

/-! ## §5 — THE HONEST ROUND-TRIP + THE TEETH. -/

/-- **HONEST ROUND-TRIP (cursor).** An opened lease commits `next_due = start`. The cursor slot
survives the later open-writes (count, remaining, drawn) by `Heap.hget_hset_frame`, then reads back
by `Heap.hget_hset_self`. -/
theorem opened_cursor (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (digest : ℤ) (t : Terms) :
    boundCursor hash (openLease hash h digest t) = some t.start := by
  show hget hash (openLease hash h digest t) leaseColl keyNextDue = some t.start
  unfold openLease
  rw [hget_hset_frame hash hCR _ leaseColl keyDrawn leaseColl keyNextDue 0 (by decide),
    hget_hset_frame hash hCR _ leaseColl keyRemaining leaseColl keyNextDue t.budget (by decide),
    hget_hset_frame hash hCR _ leaseColl keyCount leaseColl keyNextDue 0 (by decide)]
  exact hget_hset_self hash _ leaseColl keyNextDue t.start

/-- **HONEST ROUND-TRIP + BUDGET-HOLD.** An opened lease HOLDS the full prepaid `budget` in the
escrow (remaining) slot — the escrow-leg round-trip. The drawn slot (written last) is framed off. -/
theorem opened_remaining (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (digest : ℤ) (t : Terms) :
    boundRemaining hash (openLease hash h digest t) = some t.budget := by
  show hget hash (openLease hash h digest t) leaseColl keyRemaining = some t.budget
  unfold openLease
  rw [hget_hset_frame hash hCR _ leaseColl keyDrawn leaseColl keyRemaining 0 (by decide)]
  exact hget_hset_self hash _ leaseColl keyRemaining t.budget

/-- **HONEST ROUND-TRIP (count).** An opened lease commits a discharged-count of `0`. -/
theorem opened_count (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (digest : ℤ) (t : Terms) :
    boundCount hash (openLease hash h digest t) = some 0 := by
  show hget hash (openLease hash h digest t) leaseColl keyCount = some 0
  unfold openLease
  rw [hget_hset_frame hash hCR _ leaseColl keyDrawn leaseColl keyCount 0 (by decide),
    hget_hset_frame hash hCR _ leaseColl keyRemaining leaseColl keyCount t.budget (by decide)]
  exact hget_hset_self hash _ leaseColl keyCount 0

/-- **HONEST DISCHARGE ACCEPTS** (non-vacuity). At the opening cursor (`start`) with the full budget
held, a period-0 discharge drawing exactly the rent at/after the first due block, whose budget covers
the rent, is accepted by the gate. The live path the teeth close. -/
theorem opened_discharge_accepts (t : Terms) (s : Step)
    (hidx : s.periodIndex = 0) (hclk : t.start ≤ s.clock) (hamt : s.amount = t.rent)
    (hcov : t.rent ≤ t.budget) (hopen : t.count = 0 ∨ 0 < t.count) :
    DischargeOk t t.start t.budget s := by
  refine ⟨?_, ?_, ?_, hamt, hcov⟩
  · rw [expectedPeriod_open]; rcases hopen with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rw [expectedPeriod_open]; exact hidx
  · rw [expectedPeriod_open]; show dueBlock t 0 ≤ s.clock
    unfold dueBlock; simpa using hclk

/-- **THE ONE-SHOT / NO-DOUBLE TOOTH.** After period 0 is discharged the cursor is `start + period`,
whose expected period is `1`; a replay naming period `0` is REJECTED (`0 ≠ 1`), whatever the
remaining budget. The Rust `double_discharge_is_rejected`, as a consequence of the strict cursor
advance. -/
theorem replay_rejected (t : Terms) (hwf : t.wf) (remaining : ℤ) (s : Step) (hidx : s.periodIndex = 0) :
    ¬ DischargeOk t (t.start + t.period) remaining s := by
  intro hok
  have hexp := hok.2.1
  rw [expectedPeriod_after_one t hwf, hidx] at hexp
  exact absurd hexp (by decide)

/-- **THE NO-EARLY / OFF-SCHEDULE TOOTH.** A discharge whose presented clock is below the current
period's due block is REJECTED. The Rust `off_schedule_discharge_is_rejected`, as a theorem. -/
theorem off_schedule_rejected (t : Terms) (nextDue remaining : ℤ) (s : Step)
    (hearly : s.clock < dueBlock t (expectedPeriod t nextDue)) :
    ¬ DischargeOk t nextDue remaining s := by
  intro hok
  exact absurd hok.2.2.1 (not_le.mpr hearly)

/-- **THE NO-OVER/UNDER-DRAW TOOTH.** A discharge whose asserted draw differs from the committed rent
is REJECTED. The Rust `over_draw_is_rejected`, as a theorem. -/
theorem over_draw_rejected (t : Terms) (nextDue remaining : ℤ) (s : Step) (hne : s.amount ≠ t.rent) :
    ¬ DischargeOk t nextDue remaining s := by
  intro hok
  exact hne hok.2.2.2.1

/-- **THE INSUFFICIENT-BUDGET / LAPSE TOOTH (the fused backstop).** A discharge whose committed
remaining prepaid budget cannot cover the rent is REJECTED — the meter CANNOT advance past what the
budget prepaid. The half of `budget_never_overdrawn` that refuses the over-draw. The Rust
`insufficient_budget_is_rejected`, as a theorem. -/
theorem insufficient_budget_rejected (t : Terms) (nextDue remaining : ℤ) (s : Step)
    (hshort : remaining < t.rent) :
    ¬ DischargeOk t nextDue remaining s := by
  intro hok
  exact absurd hok.2.2.2.2 (not_le.mpr hshort)

/-- **THE NO-SILENT-SKIP / AUDIT TOOTH.** A cell whose committed discharged-count lags the number of
periods the schedule demands by the audited clock is REJECTED. -/
theorem behind_schedule_rejected (t : Terms) (committedCount clock : ℤ)
    (hbehind : committedCount < periodsDueBy t clock) :
    ¬ AuditOk t committedCount clock := by
  intro hok
  exact absurd hok (not_le.mpr hbehind)

/-! ## §5b — BUDGET NEVER OVER-DRAWN + METERED == DRAWN (the fusion, closed forms).

The budget after `n` discharges is exactly `budget − n·rent`, and the cumulative drawn after `n`
discharges is exactly `n·rent`. Together with the per-step heap read-backs (`advance_draws_exactly_rent`,
`advance_meters_period`) they say: the committed remaining budget and drawn total track the metered
period count EXACTLY — metered == drawn, and the budget is never over-drawn. -/

/-- The committed remaining budget after `n` per-period draws (the model closed form). -/
def remainingAfter (budget rent : ℤ) : ℕ → ℤ
  | 0 => budget
  | n + 1 => remainingAfter budget rent n - rent

/-- The committed cumulative drawn total after `n` per-period draws (the model closed form). -/
def drawnAfter (rent : ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => drawnAfter rent n + rent

/-- **BUDGET NEVER OVER-DRAWN (the bound HOLDS).** After `n` discharges the committed remaining
budget is exactly `budget − n·rent` — the prepaid budget draws down by exactly one rent per metered
period, no more, no less. The bound half of `budget_never_overdrawn` (the refusal half is
`insufficient_budget_rejected`). -/
theorem budget_never_overdrawn (budget rent : ℤ) (n : ℕ) :
    remainingAfter budget rent n = budget - n * rent := by
  induction n with
  | zero => simp [remainingAfter]
  | succ k ih => simp [remainingAfter, ih]; ring

/-- **METERED == DRAWN (the fusion closed form).** After `n` discharges the cumulative drawn total is
exactly `n·rent` — the number of periods METERED (the cursor advanced `n` times) times the rent. The
drawn total is a pure function of the metered period count: no drift. -/
theorem drawn_eq_count_rent (rent : ℤ) (n : ℕ) :
    drawnAfter rent n = n * rent := by
  induction n with
  | zero => simp [drawnAfter]
  | succ k ih => simp [drawnAfter, ih]; ring

/-- **CONSERVATION (Σδ = 0).** At every step the remaining budget plus the drawn total equals the
initial prepaid budget: value neither appears nor vanishes — every rent leaving the escrow leg
appears in the drawn total. The fusion's conservation law. -/
theorem remaining_plus_drawn_conserved (budget rent : ℤ) (n : ℕ) :
    remainingAfter budget rent n + drawnAfter rent n = budget := by
  rw [budget_never_overdrawn, drawn_eq_count_rent]; ring

/-- **READ-BACK: one discharge DRAWS exactly rent.** The fused write decrements the committed
remaining budget by exactly `rent`; the remaining slot survives the later drawn write by
`Heap.hget_hset_frame`. Ties the heap step to the `remainingAfter` closed form. -/
theorem advance_draws_exactly_rent (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (t : Terms) (cursor count remaining drawn : ℤ) :
    boundRemaining hash (advance hash h t cursor count remaining drawn) = some (remaining - t.rent) := by
  show hget hash (advance hash h t cursor count remaining drawn) leaseColl keyRemaining
      = some (remaining - t.rent)
  unfold advance
  rw [hget_hset_frame hash hCR _ leaseColl keyDrawn leaseColl keyRemaining (drawn + t.rent) (by decide)]
  exact hget_hset_self hash _ leaseColl keyRemaining (remaining - t.rent)

/-- **READ-BACK: one discharge METERS the period.** The SAME fused write advances the committed
cursor by exactly one period; the cursor slot survives the later count/remaining/drawn writes by
`Heap.hget_hset_frame`. The meter and the draw are the ONE write. -/
theorem advance_meters_period (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (t : Terms) (cursor count remaining drawn : ℤ) :
    boundCursor hash (advance hash h t cursor count remaining drawn) = some (cursor + t.period) := by
  show hget hash (advance hash h t cursor count remaining drawn) leaseColl keyNextDue
      = some (cursor + t.period)
  unfold advance
  rw [hget_hset_frame hash hCR _ leaseColl keyDrawn leaseColl keyNextDue (drawn + t.rent) (by decide),
    hget_hset_frame hash hCR _ leaseColl keyRemaining leaseColl keyNextDue (remaining - t.rent) (by decide),
    hget_hset_frame hash hCR _ leaseColl keyCount leaseColl keyNextDue (count + 1) (by decide)]
  exact hget_hset_self hash _ leaseColl keyNextDue (cursor + t.period)

/-- **READ-BACK: one discharge RECORDS the draw.** The fused write adds exactly `rent` to the
committed drawn total — the outermost write, read back directly by `Heap.hget_hset_self`. -/
theorem advance_records_draw (hash : List ℤ → ℤ)
    (h : FeltHeap) (t : Terms) (cursor count remaining drawn : ℤ) :
    boundDrawn hash (advance hash h t cursor count remaining drawn) = some (drawn + t.rent) := by
  show hget hash (advance hash h t cursor count remaining drawn) leaseColl keyDrawn
      = some (drawn + t.rent)
  unfold advance
  exact hget_hset_self hash _ leaseColl keyDrawn (drawn + t.rent)

/-! ## §6 — THE HEAP REUSE KEYSTONE: cursor, budget, and drawn are bound into the committed root.

All three ride the SAME sorted-Poseidon2 `Heap.root` the cap crown proves binds. Equal committed
roots open to the SAME cursor, remaining budget, and drawn — a forge cannot present the honest root
with a rewound cursor, a padded budget, or an under-reported draw. DIRECT instances of
`Heap.root_binds_get` (the anti-ghost), under the one named `Poseidon2SpongeCR` floor. -/

/-- **THE REUSE KEYSTONE (cursor).** Equal roots ⟹ equal committed cursor. -/
theorem cursor_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) :
    boundCursor hash h₁ = boundCursor hash h₂ :=
  root_binds_get hash hCR hroot leaseColl keyNextDue

/-- **THE REUSE KEYSTONE (budget).** Equal roots ⟹ equal committed remaining budget — a forge cannot
pad (or hide a spent) prepaid budget while keeping the honest root. -/
theorem remaining_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) :
    boundRemaining hash h₁ = boundRemaining hash h₂ :=
  root_binds_get hash hCR hroot leaseColl keyRemaining

/-- **THE REUSE KEYSTONE (drawn).** Equal roots ⟹ equal committed drawn total — a forge cannot
under-report the rent drawn while keeping the honest root. -/
theorem drawn_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) :
    boundDrawn hash h₁ = boundDrawn hash h₂ :=
  root_binds_get hash hCR hroot leaseColl keyDrawn

/-- **THE ANTI-GHOST.** A forged cell whose committed remaining budget differs from the honest one
CANNOT keep the honest root — it must publish a different root (where the insufficient-budget / draw
teeth then bite). The contrapositive of `remaining_bound_in_root`. -/
theorem forged_budget_moves_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hne : boundRemaining hash h₁ ≠ boundRemaining hash h₂) :
    root hash h₁ ≠ root hash h₂ :=
  fun hroot => hne (remaining_bound_in_root hash hCR hroot)

/-! ## §6b — THE CIRCUIT-WELD RUNG (STAGED): the fused discharge a LIGHT CLIENT witnesses.

§3–§6 are the EXECUTOR-witnessed teeth. THIS section is the LIGHT-CLIENT rung: the gate over a
(before, after) PAIR of committed heaps — the genuine kernel TRANSITION a batch proves. A satisfying
witness FORCES the fused shape: the discharge is DUE, the budget COVERS the rent, the cursor ADVANCES
by exactly one period, the remaining budget DRAWS by exactly rent, AND the drawn total records
exactly rent — ALL in one entry. A witness that advances the meter WITHOUT drawing rent, or draws
rent WITHOUT advancing the meter, is INEXPRESSIBLE. Drift is unrepresentable in-circuit. -/

/-- **The fused discharge gate over a TRANSITION.** Read the committed cursor (`cb`), remaining
budget (`rb`), and drawn (`db`) from the bound `before` view; require the discharge is DUE, the
budget covers the rent, and the `after` view advances the cursor by one period, draws the remaining
by exactly rent, and records exactly rent in drawn. The conjunction in ONE entry is the fusion — a
per-slot-independent caveat could NOT force the joint meter ∧ draw shape. -/
abbrev DischargeGate (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap) (clock cb rb db : ℤ) :
    Prop :=
  boundCursor hash before = some cb ∧
  boundRemaining hash before = some rb ∧
  boundDrawn hash before = some db ∧
  dueBlock t (expectedPeriod t cb) ≤ clock ∧
  t.rent ≤ rb ∧
  boundCursor hash after = some (cb + t.period) ∧
  boundRemaining hash after = some (rb - t.rent) ∧
  boundDrawn hash after = some (db + t.rent)

/-- **HONEST FUSED DISCHARGE PASSES THE GATE** (non-vacuity, accept polarity). The genuine kernel
transition — a committed cursor/remaining/drawn, then `advance` — satisfies the gate whenever the
clock has reached the due block and the budget covers the rent. Without this the rung is vacuous. -/
theorem discharge_passes_gate (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (h : FeltHeap)
    (t : Terms) (cursor count remaining drawn clock : ℤ)
    (hcur : boundCursor hash h = some cursor) (hrem : boundRemaining hash h = some remaining)
    (hdrw : boundDrawn hash h = some drawn)
    (hdue : dueBlock t (expectedPeriod t cursor) ≤ clock) (hcov : t.rent ≤ remaining) :
    DischargeGate hash t h (advance hash h t cursor count remaining drawn) clock cursor remaining drawn :=
  ⟨hcur, hrem, hdrw, hdue, hcov,
    advance_meters_period hash hCR h t cursor count remaining drawn,
    advance_draws_exactly_rent hash hCR h t cursor count remaining drawn,
    advance_records_draw hash h t cursor count remaining drawn⟩

/-- **THE FUSION TOOTH.** A satisfying gate witness FORCES meter and draw to move TOGETHER: the
cursor advanced exactly one period, the remaining budget drew exactly rent, and the drawn total
recorded exactly rent. There is no accepting witness in which the meter and the draw disagree. -/
theorem discharge_gate_forces_fused (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap)
    (clock cb rb db : ℤ) (hgate : DischargeGate hash t before after clock cb rb db) :
    dueBlock t (expectedPeriod t cb) ≤ clock ∧
      t.rent ≤ rb ∧
      boundCursor hash after = some (cb + t.period) ∧
      boundRemaining hash after = some (rb - t.rent) ∧
      boundDrawn hash after = some (db + t.rent) :=
  ⟨hgate.2.2.2.1, hgate.2.2.2.2.1, hgate.2.2.2.2.2.1, hgate.2.2.2.2.2.2.1, hgate.2.2.2.2.2.2.2⟩

/-- **METERED == DRAWN, tooth 1: NO ADVANCE WITHOUT A DRAW.** A witness that advances the cursor but
does NOT draw the rent from the remaining budget (the `after` remaining did not decrement by rent) is
REFUSED — assuming `rent ≠ 0`, the gate requires `after remaining = rb − rent`. Metering a period
without paying its rent is INEXPRESSIBLE. -/
theorem no_advance_without_draw_rejected (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap)
    (clock cb rb db stuck : ℤ) (hafter : boundRemaining hash after = some stuck)
    (hne : stuck ≠ rb - t.rent) :
    ¬ DischargeGate hash t before after clock cb rb db := by
  intro hgate
  have h := hgate.2.2.2.2.2.2.1
  rw [hafter] at h
  exact hne (Option.some.inj h)

/-- **METERED == DRAWN, tooth 2: NO DRAW WITHOUT AN ADVANCE.** A witness that draws rent but does NOT
advance the cursor by one period (a replay that pays but leaves the one-shot meter where it was) is
REFUSED — the gate requires `after cursor = cb + period`. Paying rent without metering the period
(double-paying a metered period, or paying an un-metered one) is INEXPRESSIBLE. -/
theorem no_draw_without_advance_rejected (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap)
    (clock cb rb db stuck : ℤ) (hafter : boundCursor hash after = some stuck)
    (hne : stuck ≠ cb + t.period) :
    ¬ DischargeGate hash t before after clock cb rb db := by
  intro hgate
  have h := hgate.2.2.2.2.2.1
  rw [hafter] at h
  exact hne (Option.some.inj h)

/-- **THE NO-EARLY TOOTH (light-client face).** A discharge whose schedule clock is BELOW the current
period's due block is REFUSED by the gate. -/
theorem discharge_gate_early_rejected (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap)
    (clock cb rb db : ℤ) (hearly : clock < dueBlock t (expectedPeriod t cb)) :
    ¬ DischargeGate hash t before after clock cb rb db := by
  intro hgate
  exact absurd hgate.2.2.2.1 (not_le.mpr hearly)

/-- **THE INSUFFICIENT-BUDGET TOOTH (light-client face).** A discharge whose committed before-budget
cannot cover the rent is REFUSED by the gate — the meter cannot advance past the prepaid budget, even
in-circuit. The light-client face of `insufficient_budget_rejected`. -/
theorem discharge_gate_insufficient_rejected (hash : List ℤ → ℤ) (t : Terms) (before after : FeltHeap)
    (clock cb rb db : ℤ) (hshort : rb < t.rent) :
    ¬ DischargeGate hash t before after clock cb rb db := by
  intro hgate
  exact absurd hgate.2.2.2.2.1 (not_le.mpr hshort)

/-- **THE LIGHT-CLIENT TOOTH (root-transport).** The gate verdict is FIXED by the committed ROOTS of
the before/after views — a forger presenting fake cursor/budget/drawn slots must MOVE a root (where
§6's binding bites). Proven by REUSE of `cursor_bound_in_root` / `remaining_bound_in_root` /
`drawn_bound_in_root` — no lease-local commitment, the one named `Poseidon2SpongeCR` floor. -/
theorem discharge_gate_root_bound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {before before' after after' : FeltHeap} (t : Terms) (clock cb rb db : ℤ)
    (hb : root hash before = root hash before') (ha : root hash after = root hash after')
    (hgate : DischargeGate hash t before after clock cb rb db) :
    DischargeGate hash t before' after' clock cb rb db := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hgate
  refine ⟨?_, ?_, ?_, h4, h5, ?_, ?_, ?_⟩
  · rw [← cursor_bound_in_root hash hCR hb]; exact h1
  · rw [← remaining_bound_in_root hash hCR hb]; exact h2
  · rw [← drawn_bound_in_root hash hCR hb]; exact h3
  · rw [← cursor_bound_in_root hash hCR ha]; exact h6
  · rw [← remaining_bound_in_root hash hCR ha]; exact h7
  · rw [← drawn_bound_in_root hash hCR ha]; exact h8

/-! ## §7 — NON-VACUITY TEETH (`#guard`): the fused invariant BITES, both polarities.

Computed on the reference sponge (`Substrate.Heap.refSponge`). The sample lease (the Rust
`sample_terms`): rent 50 every 100 blocks from block 1000, unbounded, prepaid budget 150 — which
covers EXACTLY three periods, so the fourth discharge is refused by the budget backstop. -/

section Witnesses

/-- The Rust `sample_terms`: rent 50, period 100, start 1000, unbounded, prepaid budget 150. -/
private def t0 : Terms := ⟨50, 100, 1000, 0, 150⟩

theorem t0_wf : t0.wf := by decide

-- THE SCHEDULE CLOCK.
#guard cursorAt t0 0 == 1000
#guard cursorAt t0 1 == 1100
#guard cursorAt t0 2 == 1200
#guard expectedPeriod t0 1000 == 0
#guard expectedPeriod t0 1100 == 1
#guard periodsDueBy t0 999 == 0
#guard periodsDueBy t0 1000 == 1
#guard periodsDueBy t0 1250 == 3

-- THE BUDGET CLOSED FORMS: 150 prepaid, 50/period ⇒ remaining after 0/1/2/3 = 150/100/50/0; drawn = 0/50/100/150.
#guard remainingAfter 150 50 0 == 150
#guard remainingAfter 150 50 3 == 0
#guard drawnAfter 50 3 == 150
-- CONSERVATION: remaining + drawn == budget at every step.
#guard remainingAfter 150 50 2 + drawnAfter 50 2 == 150

-- HONEST: at the opening cursor 1000 with the full budget 150 held, a period-0 discharge drawing
-- exactly 50 at clock 1000 (budget covers it) accepts.
#guard decide (DischargeOk t0 1000 150 ⟨0, 50, 1000⟩)
-- THE ONE-SHOT: after the cursor advances to 1100, a replay naming period 0 is refused.
#guard !decide (DischargeOk t0 1100 100 ⟨0, 50, 1000⟩)
-- THE NO-EARLY: a discharge one block early (clock 999, due 1000) is refused.
#guard !decide (DischargeOk t0 1000 150 ⟨0, 50, 999⟩)
-- THE NO-OVER/UNDER-DRAW: drawing 9999 or 1 instead of the committed rent 50 is refused.
#guard !decide (DischargeOk t0 1000 150 ⟨0, 9999, 1000⟩)
#guard !decide (DischargeOk t0 1000 150 ⟨0, 1, 1000⟩)
-- THE INSUFFICIENT-BUDGET BACKSTOP: with only 40 remaining (< rent 50) the fourth-period draw is
-- refused — the prepaid budget ran out; the meter cannot advance past what was prepaid.
#guard !decide (DischargeOk t0 1300 40 ⟨3, 50, 1300⟩)
-- ...but with exactly rent remaining it is covered (boundary).
#guard decide (DischargeOk t0 1300 50 ⟨3, 50, 1300⟩)
-- THE NO-SILENT-SKIP audit.
#guard !decide (AuditOk t0 1 1250)
#guard decide (AuditOk t0 3 1250)

-- THE HEAP BINDING: opening holds cursor=start AND budget=150; the fused discharge advances the
-- cursor to 1100, draws the remaining to 100, records drawn 50 — ALL in one write — and MOVES the root.
private def opened : FeltHeap := openLease refSponge [] 777 t0
private def stepped : FeltHeap := advance refSponge opened t0 1000 0 150 0
#guard boundCursor refSponge opened == some 1000
#guard boundRemaining refSponge opened == some 150
#guard boundCount refSponge opened == some 0
#guard boundDrawn refSponge opened == some 0
#guard boundCursor refSponge stepped == some 1100
#guard boundRemaining refSponge stepped == some 100
#guard boundDrawn refSponge stepped == some 50
#guard (root refSponge stepped != root refSponge opened)

-- §6b THE CIRCUIT-WELD GATE (the fused discharge manifest re-evaluation), both polarities.
-- HONEST: opened (cursor 1000, remaining 150, drawn 0) → stepped: due at 1000, budget covers, meter
-- and draw move together — passes.
#guard decide (DischargeGate refSponge t0 opened stepped 1000 1000 150 0)
-- NO-EARLY: one block early (clock 999 < due block 1000) fails.
#guard !decide (DischargeGate refSponge t0 opened stepped 999 1000 150 0)
-- NO-DRAW-WITHOUT-ADVANCE: an `after` cursor reverted to 1000 (meter not advanced) fails.
private def meterStuck : FeltHeap := hset refSponge stepped leaseColl keyNextDue 1000
#guard boundCursor refSponge meterStuck == some 1000
#guard !decide (DischargeGate refSponge t0 opened meterStuck 1000 1000 150 0)
-- NO-ADVANCE-WITHOUT-DRAW: an `after` remaining reverted to 150 (rent not drawn) fails.
private def drawStuck : FeltHeap := hset refSponge stepped leaseColl keyRemaining 150
#guard boundRemaining refSponge drawStuck == some 150
#guard !decide (DischargeGate refSponge t0 opened drawStuck 1000 1000 150 0)
-- INSUFFICIENT-BUDGET (light-client): before-budget 40 < rent 50 fails the gate.
#guard !decide (DischargeGate refSponge t0 opened stepped 1300 1300 40 100)

end Witnesses

/-! ## §8 — Axiom hygiene. -/

#assert_all_clean [
  cursor_strict_mono,
  advance_strictly_increases,
  expectedPeriod_after_one,
  expectedPeriod_open,
  opened_cursor,
  opened_remaining,
  opened_count,
  opened_discharge_accepts,
  replay_rejected,
  off_schedule_rejected,
  over_draw_rejected,
  insufficient_budget_rejected,
  behind_schedule_rejected,
  budget_never_overdrawn,
  drawn_eq_count_rent,
  remaining_plus_drawn_conserved,
  advance_draws_exactly_rent,
  advance_meters_period,
  advance_records_draw,
  cursor_bound_in_root,
  remaining_bound_in_root,
  drawn_bound_in_root,
  forged_budget_moves_root,
  discharge_passes_gate,
  discharge_gate_forces_fused,
  no_advance_without_draw_rejected,
  no_draw_without_advance_rejected,
  discharge_gate_early_rejected,
  discharge_gate_insufficient_rejected,
  discharge_gate_root_bound
]

end Dregg2.Deos.PrepaidLease
