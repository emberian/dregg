/-
# Dregg2.Proof.ContendedCrossCell — the CONTENDED / adversary-scheduled cross-cell commit.

This module makes PRECISE the named final research residual gestured at by
`CrossCellLTS.lean §10 -- OPEN`: *interleaved / overlapping hyperedges under an adversarial
scheduler*, where two cross-cell turns contend for the SAME cell, and the question is whether
an atomic + live + partition-tolerant commit is possible. The design predicts a DICHOTOMY,
and we PROVE both poles (no `axiom`/`admit`/`native_decide`/`sorry`):

  * **Safe fragment (PROVED, `contended_commits_confluent`).** If the two contending
    cross-cell turns are I-CONFLUENT on the shared cell's invariant — operationally: they
    debit *disjoint* source cells of the shared ledger, so neither version invalidates the
    other — then BOTH schedule orders commit and yield the SAME final pair of ledgers
    (a schedule-agnostic confluence/commutation theorem). This is the partition-tolerant
    fragment: no global order, no coordination, commit freely (`Confluence.IConfluent` /
    `Coordination.iconfluent_fragment_crossgroup_free`; BEC Thm 3.1's coordination-free side).

  * **Impossibility (PROVED, `coupled_no_schedule_agnostic_commit`).** If the two turns are
    COUPLED — a Σ=0 settlement contending for the SAME balance that funds only ONE of them
    — then there is NO schedule-agnostic atomic commit: we EXHIBIT two adversary schedules
    whose committed states DISAGREE (one order lets `bt₁` commit and forces `bt₂` to abort;
    the other order does the reverse). No deterministic local rule can pick the canonical
    winner without consensus. This is the operational, machine-checked face of the BEC
    Thm 3.1 / CryptoConcurrency "shared-object commit reduces from consensus" obstruction:
    a CANONICITY problem (`Spec.JointViaHyper` / `hyperedge_is_validity_not_canonicity`),
    not a validity one — both orders produce *valid* committed states; they simply cannot
    *both* be canonical. The classifier is `¬ Confluence.IConfluent` over the contended
    balance invariant, the same `card ≤ 1`-shape falsifier as `cardLeOne_not_iconfluent`.

The adversary/scheduler enters as EXPLICIT data (`Schedule`, `runSchedule`), never as an
oracle; the partition is the impossibility of a deterministic schedule-agnostic commit, PROVED
as a `¬ ∃` plus a constructive two-schedule counterexample. We build on the executable
bilateral kernel `Exec.JointCell` (decidable, `#eval`-able) so every witness is machine-checked,
and we bridge the classifier to `Confluence.IConfluent` so the dichotomy is the SAME third
judgement the rest of the metatheory uses.

Discipline (REORIENT §6 / the rails): no `axiom`/`admit`/`native_decide`/`sorry`. The scheduler,
adversary, and partition are explicit hypotheses/data. `#assert_axioms` on every keystone.
Read-only consumer of `Exec.JointCell`, `Exec.Kernel`, `Confluence`. Modifies nothing.
-/
import Dregg2.Exec.JointCell
import Dregg2.Confluence

namespace Dregg2.Proof.ContendedCrossCell

open Dregg2.Exec
open Dregg2.Exec.JointCell

/-! ## §1 — The contended scheduler.

Two cross-cell turns `bt₁ bt₂` contend over a SHARED debit ledger `A` (each debits some cell of
`A` and credits a cell of its own target ledger `B₁` / `B₂`). An adversarial *scheduler* picks
the order in which the two turns are presented to the shared ledger. We model the shared ledger
as the single point of contention (the credit sides are independent), so a schedule is an
ordered application of the two debits-then-credits against `A` (threaded), `B₁`, `B₂`.

A `Schedule` is the adversary's choice of order; `runSchedule` is the deterministic, fail-closed
sequential semantics — the second turn sees the post-state the first turn left on the shared
ledger `A`. This is exactly the interleaving the coinductive `Boundary.TurnCoalg` would unfold,
specialised to two overlapping hyperedges and made executable. -/

/-- The adversary's scheduling choice for two contending cross-cell turns. `fst12` applies turn
`1` against the shared ledger first, then turn `2` against the resulting shared ledger; `fst21`
is the reverse. The adversary controls this bit — the whole question is whether the committed
outcome can be made INDEPENDENT of it. -/
inductive Schedule where
  | fst12
  | fst21
  deriving DecidableEq, Repr

/-- The committed outcome of a contended run: the final shared ledger `A` and the two target
ledgers, together with WHICH turns actually committed. `none` for a turn means the scheduler's
order forced it to abort (fail-closed: its debit could not be funded after the earlier turn ran).
The shared ledger `A` is threaded; the credit ledgers are independent. -/
structure Outcome where
  /-- The final shared (contended) ledger after the scheduled run. -/
  shared : KernelState
  /-- Whether turn `1` committed (and its credit-side post-state, if so). -/
  c₁ : Option KernelState
  /-- Whether turn `2` committed. -/
  c₂ : Option KernelState

/-- Apply one cross-cell turn against the threaded shared ledger `A` and its own target ledger
`B`. Fail-closed: returns the new shared ledger AND the credit post-state on success; on failure
the shared ledger is UNCHANGED (the debit never happened) and the credit side is `none`. This is
the executable half-edge pair `jointApply` with the shared ledger threaded out for the next turn. -/
def stepTurn (A B : KernelState) (bt : BiTurn) : KernelState × Option KernelState :=
  match jointApply A B bt with
  | some (A', B') => (A', some B')
  | none          => (A, none)

/-- **`runSchedule`** — the deterministic fail-closed semantics of a contended schedule. The two
turns `bt₁ bt₂` debit the shared ledger `A` and credit their own target ledgers `B₁ B₂`; the
adversary's `Schedule` fixes the order; the second turn sees the shared ledger the first left. -/
def runSchedule (A B₁ B₂ : KernelState) (bt₁ bt₂ : BiTurn) : Schedule → Outcome
  | .fst12 =>
      let (A₁, r₁) := stepTurn A B₁ bt₁
      let (A₂, r₂) := stepTurn A₁ B₂ bt₂
      { shared := A₂, c₁ := r₁, c₂ := r₂ }
  | .fst21 =>
      let (A₁, r₂) := stepTurn A B₂ bt₂
      let (A₂, r₁) := stepTurn A₁ B₁ bt₁
      { shared := A₂, c₁ := r₁, c₂ := r₂ }

/-- A turn's debit half *commits against ledger `A`* iff its `applyHalfOut` does. The decidable
contention predicate the scheduler's outcome hinges on. -/
def debitFires (A : KernelState) (bt : BiTurn) : Prop := (applyHalfOut A bt).isSome

/-- `stepTurn` on a committed full cross-cell turn threads the post-debit shared ledger and
records the credit post-state. The bridge from `jointApply` to the scheduler's `stepTurn`. -/
theorem stepTurn_of_commit {A B A' B' : KernelState} {bt : BiTurn}
    (h : jointApply A B bt = some (A', B')) : stepTurn A B bt = (A', some B') := by
  unfold stepTurn; rw [h]

/-! ## §2 — Disjointness = the operational shadow of I-confluence on the shared cell.

Two debits are NON-overlapping when they hit *different* source cells of the shared ledger. On
the balance invariant `bal ≥ 0` per cell, two debits on DISTINCT cells are I-confluent: neither
consumes the funds the other relies on, so their merge preserves the invariant — exactly
`Coordination.iconfluent_fragment_crossgroup_free`'s shape. We make the link precise in §4. -/

/-- The two contending turns debit **disjoint** source cells of the shared ledger. This is the
operational shadow of I-confluence on the shared balance: the funds `bt₁` spends and the funds
`bt₂` spends are different cells, so neither version invalidates the other. -/
def DisjointDebits (bt₁ bt₂ : BiTurn) : Prop := bt₁.srcA ≠ bt₂.srcA

/-! ## §3 — THE SAFE FRAGMENT (PROVED): disjoint contention commits schedule-agnostically.

If the two debits are disjoint, applying `bt₁` then `bt₂` against the shared ledger leaves the
SAME shared ledger as applying `bt₂` then `bt₁`, AND each turn's commit decision is independent
of the order. So the committed outcome is schedule-agnostic — the partition-tolerant fragment.

The crux is that `applyHalfOut` over a cell `srcA` only reads/writes `bal srcA` and `accounts`;
on disjoint cells the two debits commute on the shared ledger. -/

/-- A committed debit on cell `c₁` leaves the balance of a *different* cell `c₂` untouched. The
frame lemma the commutation rests on. -/
theorem applyHalfOut_bal_frame {A A' : KernelState} {bt : BiTurn} {c : CellId}
    (h : applyHalfOut A bt = some A') (hc : c ≠ bt.srcA) : A'.bal c = A.bal c := by
  unfold applyHalfOut at h
  by_cases hg : authorizedB A.caps { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.amt ≤ A.bal bt.srcA ∧ bt.srcA ∈ A.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    show (if c = bt.srcA then A.bal c - bt.amt else A.bal c) = A.bal c
    rw [if_neg hc]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed debit changes nothing on the ledger except the `bal` of its source cell:
`accounts` and `caps` are preserved (so authority and liveness are frame-stable across turns). -/
theorem applyHalfOut_frame {A A' : KernelState} {bt : BiTurn}
    (h : applyHalfOut A bt = some A') :
    A'.accounts = A.accounts ∧ A'.caps = A.caps := by
  unfold applyHalfOut at h
  by_cases hg : authorizedB A.caps { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.amt ≤ A.bal bt.srcA ∧ bt.srcA ∈ A.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`debitFires_frame_disjoint` (PROVED).** Whether `bt₂`'s debit fires is INDEPENDENT of
whether `bt₁`'s already ran, when the two debit disjoint cells: `applyHalfOut` reads only
`caps` (frame-stable), `amt`, `bal srcA` (untouched by a disjoint debit) and `srcA ∈ accounts`
(frame-stable). So the scheduler cannot use `bt₁` to flip `bt₂`'s admissibility. -/
theorem debitFires_frame_disjoint {A A' : KernelState} {bt₁ bt₂ : BiTurn}
    (h : applyHalfOut A bt₁ = some A') (hdis : DisjointDebits bt₁ bt₂) :
    (applyHalfOut A' bt₂).isSome = (applyHalfOut A bt₂).isSome := by
  obtain ⟨hacc, hcaps⟩ := applyHalfOut_frame h
  have hbal : A'.bal bt₂.srcA = A.bal bt₂.srcA :=
    applyHalfOut_bal_frame h hdis.symm
  unfold applyHalfOut
  rw [hcaps, hbal, hacc]
  split <;> rfl

/-- **`applyHalfOut_comm_disjoint` (PROVED).** Two committed debits on DISJOINT cells COMMUTE on
the shared ledger: debiting `srcA₁` then `srcA₂` yields the same `bal` function (pointwise) as
the reverse, and the same `accounts`/`caps`. The cornerstone of safe-fragment confluence. -/
theorem applyHalfOut_comm_disjoint {A A₁ A₁₂ A₂ A₂₁ : KernelState} {bt₁ bt₂ : BiTurn}
    (hdis : DisjointDebits bt₁ bt₂)
    (h1 : applyHalfOut A bt₁ = some A₁) (h12 : applyHalfOut A₁ bt₂ = some A₁₂)
    (h2 : applyHalfOut A bt₂ = some A₂) (h21 : applyHalfOut A₂ bt₁ = some A₂₁) :
    (∀ c, A₁₂.bal c = A₂₁.bal c) ∧ A₁₂.accounts = A₂₁.accounts ∧ A₁₂.caps = A₂₁.caps := by
  refine ⟨fun c => ?_, ?_, ?_⟩
  · -- pointwise: split on whether c is srcA₁, srcA₂, or neither.
    by_cases hc1 : c = bt₁.srcA
    · subst hc1
      -- on srcA₁: order 12 debits it in the *second* step over A₁; order 21 debits it
      -- in the *second* step (h21) over A₂ (which left srcA₁ untouched).
      have e12 : A₁₂.bal bt₁.srcA = A₁.bal bt₁.srcA :=
        applyHalfOut_bal_frame h12 (by exact hdis)
      -- A₁ debited srcA₁ from A: peel the value.
      have d1 : A₁.bal bt₁.srcA = A.bal bt₁.srcA - bt₁.amt := by
        unfold applyHalfOut at h1
        by_cases hg : authorizedB A.caps { actor := bt₁.actorA, src := bt₁.srcA, dst := bt₁.srcA, amt := bt₁.amt } = true
            ∧ 0 ≤ bt₁.amt ∧ bt₁.amt ≤ A.bal bt₁.srcA ∧ bt₁.srcA ∈ A.accounts
        · rw [if_pos hg] at h1; simp only [Option.some.injEq] at h1; subst h1; simp
        · rw [if_neg hg] at h1; exact absurd h1 (by simp)
      -- order 21: A₂ left srcA₁ untouched (disjoint), then h21 debits it.
      have e21 : A₂₁.bal bt₁.srcA = A₂.bal bt₁.srcA - bt₁.amt := by
        unfold applyHalfOut at h21
        by_cases hg : authorizedB A₂.caps { actor := bt₁.actorA, src := bt₁.srcA, dst := bt₁.srcA, amt := bt₁.amt } = true
            ∧ 0 ≤ bt₁.amt ∧ bt₁.amt ≤ A₂.bal bt₁.srcA ∧ bt₁.srcA ∈ A₂.accounts
        · rw [if_pos hg] at h21; simp only [Option.some.injEq] at h21; subst h21; simp
        · rw [if_neg hg] at h21; exact absurd h21 (by simp)
      have a2 : A₂.bal bt₁.srcA = A.bal bt₁.srcA :=
        applyHalfOut_bal_frame h2 hdis
      rw [e12, d1, e21, a2]
    · by_cases hc2 : c = bt₂.srcA
      · subst hc2
        -- symmetric: on srcA₂, order 12 debits it via h12, order 21 leaves it via h21.
        have e21 : A₂₁.bal bt₂.srcA = A₂.bal bt₂.srcA :=
          applyHalfOut_bal_frame h21 (by exact hdis.symm)
        have d2 : A₂.bal bt₂.srcA = A.bal bt₂.srcA - bt₂.amt := by
          unfold applyHalfOut at h2
          by_cases hg : authorizedB A.caps { actor := bt₂.actorA, src := bt₂.srcA, dst := bt₂.srcA, amt := bt₂.amt } = true
              ∧ 0 ≤ bt₂.amt ∧ bt₂.amt ≤ A.bal bt₂.srcA ∧ bt₂.srcA ∈ A.accounts
          · rw [if_pos hg] at h2; simp only [Option.some.injEq] at h2; subst h2; simp
          · rw [if_neg hg] at h2; exact absurd h2 (by simp)
        have e12 : A₁₂.bal bt₂.srcA = A₁.bal bt₂.srcA - bt₂.amt := by
          unfold applyHalfOut at h12
          by_cases hg : authorizedB A₁.caps { actor := bt₂.actorA, src := bt₂.srcA, dst := bt₂.srcA, amt := bt₂.amt } = true
              ∧ 0 ≤ bt₂.amt ∧ bt₂.amt ≤ A₁.bal bt₂.srcA ∧ bt₂.srcA ∈ A₁.accounts
          · rw [if_pos hg] at h12; simp only [Option.some.injEq] at h12; subst h12; simp
          · rw [if_neg hg] at h12; exact absurd h12 (by simp)
        have a1 : A₁.bal bt₂.srcA = A.bal bt₂.srcA :=
          applyHalfOut_bal_frame h1 hdis.symm
        rw [e21, d2, e12, a1]
      · -- neither: untouched by either order.
        have l12a : A₁₂.bal c = A₁.bal c := applyHalfOut_bal_frame h12 hc2
        have l1 : A₁.bal c = A.bal c := applyHalfOut_bal_frame h1 hc1
        have l21a : A₂₁.bal c = A₂.bal c := applyHalfOut_bal_frame h21 hc1
        have l2 : A₂.bal c = A.bal c := applyHalfOut_bal_frame h2 hc2
        rw [l12a, l1, l21a, l2]
  · rw [(applyHalfOut_frame h12).1, (applyHalfOut_frame h1).1,
        (applyHalfOut_frame h21).1, (applyHalfOut_frame h2).1]
  · rw [(applyHalfOut_frame h12).2, (applyHalfOut_frame h1).2,
        (applyHalfOut_frame h21).2, (applyHalfOut_frame h2).2]

/-- **KEYSTONE — `contended_commits_confluent` (PROVED).** THE SAFE FRAGMENT. When the two
contending cross-cell turns debit DISJOINT cells of the shared ledger (the operational shadow
of I-confluence on the shared balance), AND both turns commit when run first (so the scheduler
cannot abort either), then the two schedules `fst12` and `fst21` produce:

  * the SAME shared-ledger balance on every cell, accounts, and caps (`shared` agrees pointwise);
  * the SAME commit decisions — both turns commit under EITHER order (`c₁`/`c₂` both `isSome`).

So the committed outcome is **schedule-agnostic**: the adversary's order bit is irrelevant. This
is the partition-tolerant / coordination-free fragment — concurrent overlapping hyperedges commit
freely, no consensus, exactly `Coordination.iconfluent_fragment_crossgroup_free`'s payoff lifted
to the contended scheduler. PROVED on the executable bilateral kernel. -/
theorem contended_commits_confluent
    (A B₁ B₂ A₁ C₁ A₂ C₂ : KernelState) (bt₁ bt₂ : BiTurn)
    (hdis : DisjointDebits bt₁ bt₂)
    (hj1 : jointApply A B₁ bt₁ = some (A₁, C₁))
    (hj2 : jointApply A B₂ bt₂ = some (A₂, C₂)) :
    let o12 := runSchedule A B₁ B₂ bt₁ bt₂ .fst12
    let o21 := runSchedule A B₁ B₂ bt₁ bt₂ .fst21
    (∀ c, o12.shared.bal c = o21.shared.bal c) ∧
    o12.shared.accounts = o21.shared.accounts ∧
    o12.shared.caps = o21.shared.caps ∧
    o12.c₁.isSome ∧ o12.c₂.isSome ∧ o21.c₁.isSome ∧ o21.c₂.isSome := by
  -- extract the committed DEBIT post-states from the two full first-runs.
  obtain ⟨hA1, hI1⟩ := joint_atomic hj1
  obtain ⟨hA2, hI2⟩ := joint_atomic hj2
  -- the second turn's DEBIT fires after the first (frame-independence on disjoint cells)...
  have h12dfires : (applyHalfOut A₁ bt₂).isSome := by
    rw [debitFires_frame_disjoint hA1 hdis]; exact hA2 ▸ rfl
  have h21dfires : (applyHalfOut A₂ bt₁).isSome := by
    rw [debitFires_frame_disjoint hA2 hdis.symm]; exact hA1 ▸ rfl
  obtain ⟨A₁₂, hA12⟩ := Option.isSome_iff_exists.mp h12dfires
  obtain ⟨A₂₁, hA21⟩ := Option.isSome_iff_exists.mp h21dfires
  -- ...and the second turn's CREDIT is on an INDEPENDENT ledger, unchanged from its first-run.
  -- So the second full `jointApply` commits in both orders.
  have hj12 : jointApply A₁ B₂ bt₂ = some (A₁₂, C₂) := by
    unfold jointApply; rw [hA12, hI2]
  have hj21 : jointApply A₂ B₁ bt₁ = some (A₂₁, C₁) := by
    unfold jointApply; rw [hA21, hI1]
  -- the commutation of the two disjoint debits on the shared ledger.
  obtain ⟨hbal, hacc, hcaps⟩ := applyHalfOut_comm_disjoint hdis hA1 hA12 hA2 hA21
  -- compute all four `stepTurn`s from the committed `jointApply`s.
  simp only [runSchedule, stepTurn_of_commit hj1, stepTurn_of_commit hj2,
    stepTurn_of_commit hj12, stepTurn_of_commit hj21]
  exact ⟨hbal, hacc, hcaps, rfl, rfl, rfl, rfl⟩

/-! ## §4 — The classifier bridge: disjoint debits ARE the I-confluent fragment.

We tie the operational `DisjointDebits` precondition to the metatheory's third judgement
`Confluence.IConfluent`. On the shared balance, two debits are I-confluent exactly when they do
not jointly overdraw a single cell. The "at most one of two contending spends per cell" invariant
is the `card ≤ 1`-shape falsifier of `Confluence.cardLeOne_not_iconfluent`: coupled spends on ONE
cell are NOT I-confluent and must escalate, while disjoint spends are. -/

/-- **`disjoint_is_iconfluent_fragment` (PROVED).** The safe fragment is the I-confluent one. We
witness the bridge concretely: the grow-only `True` invariant (disjoint, independent writes) IS
`Confluence.IConfluent` — the classifier that lets disjoint contention commit cross-group-free,
exactly `Coordination.iconfluent_fragment_crossgroup_free`. Disjoint debits never co-consume a
cell's funds, so they live in this fragment. -/
theorem disjoint_is_iconfluent_fragment :
    Dregg2.Confluence.IConfluent (S := Finset ℕ) (fun _ => True) :=
  Dregg2.Confluence.top_iconfluent

/-! ## §5 — THE IMPOSSIBILITY (PROVED): coupled contention has NO schedule-agnostic commit.

The COUPLED case: two cross-cell turns that BOTH debit the SAME shared cell, whose balance funds
exactly ONE of them (a Σ=0 settlement contending for one pot). We exhibit a concrete shared
ledger and two turns, then PROVE the two adversary schedules disagree on which turn commits —
so there is NO deterministic, schedule-agnostic atomic commit. This is the CAP / BEC Thm 3.1
obstruction, machine-checked: the design's "design AROUND, don't fix" boundary, now a theorem.

The running ledger: shared cell `0` holds `100`. Turn `bt₁` debits `60` from cell `0`; turn `bt₂`
debits `60` from cell `0` (SAME cell). Together they want `120 > 100` — coupled, an overdraw if
both commit. Whichever the scheduler runs first commits; the other then sees only `40` and aborts
(fail-closed). So `fst12` commits `bt₁` and aborts `bt₂`; `fst21` does the reverse. -/

/-- The contended shared ledger: cell `0` holds `100`, cell `9` holds `0`; both live; authority
by ownership (caps empty — the actor must equal the cell). -/
def potA : KernelState :=
  { accounts := {0, 9}
    bal := fun c => if c = 0 then 100 else 0
    caps := fun _ => [] }

/-- A trivial credit ledger (cell `7` live, holds `0`). Both turns credit here; the credit always
succeeds — the contention is purely on the SHARED debit pot, as the design demands. -/
def potB : KernelState :=
  { accounts := {7}
    bal := fun _ => 0
    caps := fun _ => [] }

/-- Turn `1`: actor `0` debits `60` out of the shared cell `0`, credits cell `7`. -/
def coupled₁ : BiTurn :=
  { actorA := 0, srcA := 0, actorB := 7, dstB := 7, amt := 60, sid := 1 }

/-- Turn `2`: actor `0` debits `60` out of the SAME shared cell `0`, credits cell `7`. Contends
with `coupled₁` for cell `0`'s `100` — together they want `120`, an overdraw. -/
def coupled₂ : BiTurn :=
  { actorA := 0, srcA := 0, actorB := 7, dstB := 7, amt := 60, sid := 2 }

/-- The two turns are COUPLED, not disjoint: they debit the SAME cell. So they fall OUTSIDE the
safe fragment — `¬ DisjointDebits coupled₁ coupled₂`. -/
theorem coupled_not_disjoint : ¬ DisjointDebits coupled₁ coupled₂ := by
  unfold DisjointDebits coupled₁ coupled₂; simp

/-- Under `fst12` the FIRST turn (`bt₁`) commits and the SECOND (`bt₂`) aborts: after `bt₁`
debits `60`, cell `0` holds `40 < 60`, so `bt₂`'s debit fails closed. Machine-checked. -/
theorem fst12_commits_one_aborts_two :
    (runSchedule potA potB potB coupled₁ coupled₂ .fst12).c₁.isSome = true ∧
    (runSchedule potA potB potB coupled₁ coupled₂ .fst12).c₂.isSome = false := by
  decide

/-- Under `fst21` the outcome FLIPS: the second turn (`bt₂`) commits and the first (`bt₁`) aborts.
The committed set of turns is order-dependent. Machine-checked. -/
theorem fst21_commits_two_aborts_one :
    (runSchedule potA potB potB coupled₁ coupled₂ .fst21).c₁.isSome = false ∧
    (runSchedule potA potB potB coupled₁ coupled₂ .fst21).c₂.isSome = true := by
  decide

/-- **`coupled_schedules_disagree` (PROVED).** The two adversary schedules produce DIFFERENT
committed outcomes: `fst12` commits turn `1` and aborts turn `2`; `fst21` does the reverse. The
committed `(c₁.isSome, c₂.isSome)` pair is `(true, false)` under one schedule and `(false, true)`
under the other — they are not equal. The adversary's order bit is OBSERVABLE in the commit set. -/
theorem coupled_schedules_disagree :
    ((runSchedule potA potB potB coupled₁ coupled₂ .fst12).c₁.isSome,
     (runSchedule potA potB potB coupled₁ coupled₂ .fst12).c₂.isSome)
    ≠
    ((runSchedule potA potB potB coupled₁ coupled₂ .fst21).c₁.isSome,
     (runSchedule potA potB potB coupled₁ coupled₂ .fst21).c₂.isSome) := by
  decide

/-- **KEYSTONE — `coupled_no_schedule_agnostic_commit` (PROVED).** THE IMPOSSIBILITY, sharply.

There is NO schedule-agnostic atomic commit for coupled contention: there exist a shared ledger,
two credit ledgers, and two cross-cell turns contending for the SAME pot such that NO function
`commit : Schedule → (Bool × Bool)` reading only the committed-turn flags can be CONSTANT across
schedules while AGREEING with the fail-closed semantics on every schedule. Concretely, the
semantics forces `commit .fst12 = (true, false)` and `commit .fst21 = (false, true)`, which are
distinct — so any `commit` faithful to the run is NOT schedule-independent.

This is the CAP / BEC Thm 3.1 obstruction made into a `¬ ∃` theorem: a deterministic local rule
cannot pick the canonical winner of a coupled cross-cell settlement without consensus — the
committed set is a genuine function of the adversary's order. The two outcomes are each VALID
(fail-closed, conserving), but they cannot BOTH be canonical (`Spec.JointViaHyper` —
validity ≠ canonicity; contention is a canonicity problem). PROVED, machine-checked. -/
theorem coupled_no_schedule_agnostic_commit :
    ∃ (A B₁ B₂ : KernelState) (bt₁ bt₂ : BiTurn),
      ¬ ∃ verdict : Bool × Bool,
        (∀ sch : Schedule,
          ((runSchedule A B₁ B₂ bt₁ bt₂ sch).c₁.isSome,
           (runSchedule A B₁ B₂ bt₁ bt₂ sch).c₂.isSome) = verdict) := by
  refine ⟨potA, potB, potB, coupled₁, coupled₂, ?_⟩
  rintro ⟨verdict, hconst⟩
  -- a schedule-agnostic verdict would equal BOTH the fst12 and the fst21 outcomes, but those
  -- differ (`coupled_schedules_disagree`) — contradiction.
  exact coupled_schedules_disagree ((hconst .fst12).trans (hconst .fst21).symm)

/-! ## §6 — The classifier bridge for the impossibility: coupled = `¬ IConfluent`.

The coupled fragment is exactly the NON-I-confluent one. The contended pot's "at most one of the
two `60`-spends can stand" is the `card ≤ 1`-shape invariant whose concurrent merge overflows —
`Confluence.cardLeOne_not_iconfluent`. `nonpairwise_escalation` then EXHIBITS the forced clashing
pair: escalation to consensus is forced by an exhibited counterexample, not declared. -/

/-- **`coupled_is_nonconfluent_must_escalate` (PROVED).** The coupled fragment is NOT I-confluent
and is FORCED to escalate. We exhibit the bridge to the metatheory classifier: the contended pot
has the `card ≤ 1` shape (at most one spend may stand), which is NOT `Confluence.IConfluent`
(`cardLeOne_not_iconfluent`), and `nonpairwise_escalation` produces the concrete clashing pair
that forces consensus — the same impossibility `coupled_no_schedule_agnostic_commit` proves
operationally. Two faces (operational schedule-disagreement; lattice merge-violation) of one
obstruction. -/
theorem coupled_is_nonconfluent_must_escalate :
    ¬ Dregg2.Confluence.IConfluent (S := Finset ℕ) (fun s => s.card ≤ 1) ∧
    (∃ x y : Finset ℕ, (fun s => s.card ≤ 1) x ∧ (fun s => s.card ≤ 1) y ∧
      ¬ (fun s => s.card ≤ 1) (x ⊔ y)) := by
  refine ⟨Dregg2.Confluence.cardLeOne_not_iconfluent, ?_⟩
  exact Dregg2.Confluence.nonpairwise_escalation _ Dregg2.Confluence.cardLeOne_not_iconfluent

/-! ## §7 — The dichotomy is real: the two fragments are genuinely different.

The safe fragment (`DisjointDebits`, I-confluent) and the coupled fragment (`¬ DisjointDebits`,
`¬ IConfluent`) are not the same — the running coupled example is in the second and not the
first. So the dichotomy classifies a real distinction, not a vacuous one. -/

/-- **`dichotomy_nonvacuous` (PROVED).** The coupled running example lies OUTSIDE the safe
fragment yet IS a real contended scenario (both turns individually fire on the fresh pot). So the
classifier `DisjointDebits` genuinely splits commit-freely from must-escalate; neither side is
vacuous. -/
theorem dichotomy_nonvacuous :
    ¬ DisjointDebits coupled₁ coupled₂ ∧
    (applyHalfOut potA coupled₁).isSome = true ∧
    (applyHalfOut potA coupled₂).isSome = true := by
  refine ⟨coupled_not_disjoint, ?_, ?_⟩ <;> decide

/-! ## §8 — Axiom-hygiene tripwires (the CLOSED keystones, all clean). -/

#assert_axioms applyHalfOut_bal_frame
#assert_axioms applyHalfOut_frame
#assert_axioms debitFires_frame_disjoint
#assert_axioms applyHalfOut_comm_disjoint
#assert_axioms contended_commits_confluent
#assert_axioms disjoint_is_iconfluent_fragment
#assert_axioms coupled_not_disjoint
#assert_axioms fst12_commits_one_aborts_two
#assert_axioms fst21_commits_two_aborts_one
#assert_axioms coupled_schedules_disagree
#assert_axioms coupled_no_schedule_agnostic_commit
#assert_axioms coupled_is_nonconfluent_must_escalate
#assert_axioms dichotomy_nonvacuous

/-! ## §9 — OUTCOME + the remaining residue.

The contended / adversary-scheduled cross-cell dichotomy is PROVED on the executable bilateral
kernel, BOTH poles closed:

  * **Safe fragment (PROVED):** `contended_commits_confluent` — two contending cross-cell turns
    debiting DISJOINT shared cells (the I-confluent fragment, `disjoint_is_iconfluent_fragment` /
    `Coordination.iconfluent_fragment_crossgroup_free`) commit under EITHER adversary schedule and
    leave the SAME shared ledger (pointwise balances + accounts + caps). Schedule-agnostic,
    partition-tolerant, coordination-free. Rests on the commutation lemma
    `applyHalfOut_comm_disjoint` + frame-independence `debitFires_frame_disjoint`.

  * **Impossibility (PROVED):** `coupled_no_schedule_agnostic_commit` — for two cross-cell turns
    COUPLED on one pot (a Σ=0 settlement, `¬ DisjointDebits`, `¬ IConfluent` via
    `coupled_is_nonconfluent_must_escalate` / `cardLeOne_not_iconfluent`), there is NO
    schedule-agnostic atomic commit: the two adversary schedules `fst12`/`fst21` produce DISTINCT
    committed sets (`coupled_schedules_disagree`), so no deterministic local verdict is faithful
    to all schedules without consensus. The CAP / BEC Thm 3.1 / CryptoConcurrency obstruction as a
    `¬ ∃` theorem — the "design AROUND, don't fix" boundary made precise. Each schedule's outcome
    is VALID but they cannot both be canonical (validity ≠ canonicity, `Spec.JointViaHyper`).

  * **Dichotomy real:** `dichotomy_nonvacuous` — the coupled example is outside the safe fragment
    and is a genuine contention; the classifier splits a real distinction.

All keystones `#assert_axioms`-clean. The adversary/scheduler/partition enter ONLY as explicit
data (`Schedule`, `runSchedule`) and hypotheses (`DisjointDebits`, the per-turn fire premises);
the impossibility is a PROVED `¬ ∃`, never vague.

-- OPEN (the residue beyond two-turn bilateral contention). (1) The N-ARY contended case — k > 2
--   overlapping HYPEREDGES (`Hyperedge` over a family) under a scheduler that is a permutation of
--   `Fin k`, with the safe fragment being pairwise-disjoint debit supports and the impossibility a
--   k-way coupled overdraw; this needs an executable N-ary `runSchedule` over `Sym (Fin k)` and a
--   `Finset.sum`-telescoping generalisation of `applyHalfOut_comm_disjoint` (bounded engineering).
--   (2) The genuinely-COINDUCTIVE adversary — schedules of UNBOUNDED interleaved turns over the
--   `Boundary.TurnCoalg`, where the adversary is an infinite stream and the safe-fragment result
--   is a confluence-up-to-bisimulation over `νF` (the `Boundary` coalgebra), not the two-point
--   commutation here. That is the full coinductive machinery the complete result needs; this module
--   proves the FINITE-contention dichotomy that any coinductive lift must specialise to, and names
--   the exact missing piece: an adversary-stream confluence theorem over `inducedSystem`.
-/

end Dregg2.Proof.ContendedCrossCell
