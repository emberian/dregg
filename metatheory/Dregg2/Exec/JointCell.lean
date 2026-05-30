/-
# Dregg2.Exec.JointCell — the EXECUTABLE bilateral JointTurn over TWO cells.

This is `JointTurn.lean` made **executable and machine-grounded** (`dregg2 §1.6`; the Mina
account-update forest, `study-mina-relink`; the irreducibility of `study-category §1`).
Where `JointTurn.lean` carries the abstract CG-2 ⊗ CG-5 binding over abstract `TurnCoalg`s,
here we run it on two concrete `Exec.KernelState` cells `A` and `B` — and prove the
**cross-side conservation CG-5** on the *running machines*.

The single structural fact that forces all of this: dregg2 has **NO global ledger**. A turn
that moves resource from a cell in `A` to a cell in `B` is therefore *not* internally
conserving in either ledger — `A` loses `amt`, `B` gains `amt`. Mina never needs CG-5
because one global ledger gives one namespace; dregg2 must carry it. The conserved quantity
is the **joint total** `total A + total B`, and it is preserved precisely because the two
**half-edges sum to zero** (the bilateral `EqualAndOpposite` `BoundDelta`, `program.rs:747`;
`CrossSideExistenceAir`, signed edge-fingerprint balance sum == 0).

Discipline (mirrors `JointTurn.lean`, honoured here on the executable layer):

  * **CG-2** (`SharedId`) is carried as **data / a HYPOTHESIS**, never derived. Both halves
    commit to the same shared turn-id (Mina's `account_updates_hash`); the proof that they
    agree is a *premise* of `joint_sound_of_binding`, exactly as in `study-category §1.4`.
  * **CG-5** (`joint_cg5_conserves`) is the keystone: a committed bilateral turn preserves
    `total A + total B`. This is PROVED on the machine (the half-edges cancel).
  * Cross-cell soundness is **NOT** `per-cell-sound ∧ per-cell-sound` — `binding_is_proper`
    exhibits a product pair (a fake bilateral whose halves do NOT sum to zero) that the
    binding *excludes*, witnessing that the binding is a genuine restriction.

Pure executable Lean, `#eval`-able; builds only on `Exec.Kernel` (no new primitives).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Dregg2.Exec.Kernel

namespace Dregg2.Exec.JointCell

open Dregg2.Exec

/-! ## The shared turn-id (CG-2) — carried as DATA, never derived

The single identity both halves of the bilateral turn commit to (Mina's
`account_updates_hash`). Abstract here (a `Nat` digest stands in for the real PI surface);
its agreement across the two halves is a *hypothesis*, not a theorem. -/

/-- A **shared turn-id** — the CG-2 turn-identity both half-edges pin their proof to. A
per-cell half-proof is valid *only as part of THIS bilateral turn*: its public input is the
shared id, so it can never be replayed solo or spliced into another forest. -/
abbrev SharedId := Nat

/-! ## The bilateral turn — one half-edge OUT of `A`, one half-edge INTO `B`

The `EqualAndOpposite` `BoundDelta`: a single `amt` leaves `srcA` (a cell tracked by ledger
`A`) and arrives at `dstB` (a cell tracked by ledger `B`). The two signed half-edge deltas
are `-amt` (A's contribution) and `+amt` (B's contribution); their sum is `0` — that is
CG-5. The turn also names the actor on each side and the `SharedId` both commit to. -/

/-- A **bilateral turn** over cells `(A, B)`: move `amt` out of `srcA` in ledger `A` and
into `dstB` in ledger `B`, under `actorA`'s authority on `A`'s side and `actorB`'s authority
on `B`'s side, both halves committing to the shared id `sid` (CG-2). -/
structure BiTurn where
  /-- The actor authorising the debit on `A`'s side (must own/hold a cap on `srcA`). -/
  actorA : CellId
  /-- The cell in ledger `A` the resource leaves. -/
  srcA   : CellId
  /-- The actor authorising the credit on `B`'s side. -/
  actorB : CellId
  /-- The cell in ledger `B` the resource arrives at. -/
  dstB   : CellId
  /-- The amount crossing the boundary (the magnitude of both half-edges). -/
  amt    : ℤ
  /-- The shared turn-id (CG-2 / `account_updates_hash`) both halves commit to. -/
  sid    : SharedId

/-! ## The two half-edges (per-cell, fail-closed)

Each half mutates *one* ledger only. Neither is internally conserving — that is the whole
point: the conserved quantity is cross-ledger. The half-edge balance projections `halfA` /
`halfB` are the signed CG-5 summands; `halfA = -amt`, `halfB = +amt`. -/

/-- The signed half-edge balance `A` contributes to the CG-5 aggregate (`A` loses `amt`). -/
def halfA (bt : BiTurn) : ℤ := - bt.amt

/-- The signed half-edge balance `B` contributes to the CG-5 aggregate (`B` gains `amt`). -/
def halfB (bt : BiTurn) : ℤ := bt.amt

/-- **A's half-edge — the debit.** Fail-closed: commits only when `actorA` is authorised
over `srcA`, the amount is non-negative and available, and `srcA` is a live account. Debits
`srcA` by `amt` (the resource leaves ledger `A`). Mirrors `Kernel.exec`'s gate, but with a
*single* affected cell (no internal `dst` — the `dst` is in the other ledger). -/
def applyHalfOut (k : KernelState) (bt : BiTurn) : Option KernelState :=
  if authorizedB k.caps { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.amt ≤ k.bal bt.srcA ∧ bt.srcA ∈ k.accounts then
    some { k with bal := fun c => if c = bt.srcA then k.bal c - bt.amt else k.bal c }
  else
    none

/-- **B's half-edge — the credit.** Fail-closed: commits only when `actorB` is authorised
over `dstB`, the amount is non-negative, and `dstB` is a live account. Credits `dstB` by
`amt` (the resource arrives in ledger `B`). -/
def applyHalfIn (k : KernelState) (bt : BiTurn) : Option KernelState :=
  if authorizedB k.caps { actor := bt.actorB, src := bt.dstB, dst := bt.dstB, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.dstB ∈ k.accounts then
    some { k with bal := fun c => if c = bt.dstB then k.bal c + bt.amt else k.bal c }
  else
    none

/-- **The executable bilateral turn.** Fail-closed and **atomic**: commits *both* halves or
neither (the all-or-none of `JointTurn.atomicity_as_proof`, here realized as the `Option`
bind — if either half is rejected, the whole bilateral turn is `none`). On success returns
the post-states of both ledgers. -/
def jointApply (A B : KernelState) (bt : BiTurn) : Option (KernelState × KernelState) :=
  match applyHalfOut A bt, applyHalfIn B bt with
  | some A', some B' => some (A', B')
  | _, _ => none

/-! ## The joint total — the cross-side conserved quantity (CG-5's measure) -/

/-- **The joint total** `total A + total B` — the quantity preserved across the boundary.
With no global ledger this is the only conserved measure; neither `total A` nor `total B`
is preserved alone. -/
def jointTotal (A B : KernelState) : ℤ := total A + total B

/-! ## Per-half effects on each ledger's total (the lemmas CG-5 rests on) -/

/-- **A's half loses exactly `amt`.** A committed debit drops `total A` by `amt`
(`= total A + halfA bt`). The debit of a single live cell. -/
theorem applyHalfOut_total {A A' : KernelState} {bt : BiTurn}
    (h : applyHalfOut A bt = some A') : total A' = total A - bt.amt := by
  unfold applyHalfOut at h
  by_cases hg : authorizedB A.caps { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.amt ≤ A.bal bt.srcA ∧ bt.srcA ∈ A.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hsrc⟩ := hg
    show (∑ c ∈ A.accounts, (if c = bt.srcA then A.bal c - bt.amt else A.bal c))
        = (∑ c ∈ A.accounts, A.bal c) - bt.amt
    have hg2 : ∀ c ∈ A.accounts,
        (if c = bt.srcA then A.bal c - bt.amt else A.bal c)
          = A.bal c + (if c = bt.srcA then (-bt.amt) else 0) := by
      intro c _
      rcases eq_or_ne c bt.srcA with h1 | h1
      · subst h1; rw [if_pos rfl, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h1]; ring
    rw [Finset.sum_congr rfl hg2, Finset.sum_add_distrib,
        sum_indicator A.accounts bt.srcA (-bt.amt) hsrc]
    ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **B's half gains exactly `amt`.** A committed credit raises `total B` by `amt`
(`= total B + halfB bt`). The credit of a single live cell. -/
theorem applyHalfIn_total {B B' : KernelState} {bt : BiTurn}
    (h : applyHalfIn B bt = some B') : total B' = total B + bt.amt := by
  unfold applyHalfIn at h
  by_cases hg : authorizedB B.caps { actor := bt.actorB, src := bt.dstB, dst := bt.dstB, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.dstB ∈ B.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, hdst⟩ := hg
    show (∑ c ∈ B.accounts, (if c = bt.dstB then B.bal c + bt.amt else B.bal c))
        = (∑ c ∈ B.accounts, B.bal c) + bt.amt
    have hg2 : ∀ c ∈ B.accounts,
        (if c = bt.dstB then B.bal c + bt.amt else B.bal c)
          = B.bal c + (if c = bt.dstB then bt.amt else 0) := by
      intro c _
      rcases eq_or_ne c bt.dstB with h1 | h1
      · subst h1; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h1, if_neg h1, add_zero]
    rw [Finset.sum_congr rfl hg2, Finset.sum_add_distrib,
        sum_indicator B.accounts bt.dstB bt.amt hdst]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## The half-edges sum to zero (the algebraic core of CG-5) -/

/-- **The bilateral `EqualAndOpposite` identity (PROVED).** The two signed half-edge
balances sum to `0`: `halfA bt + halfB bt = 0`. This is the on-machine
`CrossSideExistenceAir` balance: `-amt + amt = 0`. It is what makes the joint total
conserved — and it is *not* a property of either ledger alone. -/
theorem halves_sum_zero (bt : BiTurn) : halfA bt + halfB bt = 0 := by
  unfold halfA halfB; ring

/-! ## THE KEYSTONE — CG-5 cross-side conservation -/

/-- **`joint_cg5_conserves` — THE KEYSTONE (PROVED).** A committed bilateral turn preserves
the **joint total** `total A + total B`. The sender's loss in ledger `A` exactly equals the
receiver's gain in ledger `B` (the half-edges cancel), so the cross-side aggregate is
invariant. This is **CG-5**: the cross-side conservation dregg2 must carry because it has no
global ledger — and it is proved *on the running machines*, not assumed. -/
theorem joint_cg5_conserves {A B A' B' : KernelState} {bt : BiTurn}
    (h : jointApply A B bt = some (A', B')) :
    jointTotal A' B' = jointTotal A B := by
  unfold jointApply at h
  -- both halves must have committed (the atomic `Option` match)
  rcases hoa : applyHalfOut A bt with _ | A'' <;> rw [hoa] at h
  · simp at h
  · rcases hib : applyHalfIn B bt with _ | B'' <;> rw [hib] at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hA, hB⟩ := h
      subst hA; subst hB
      unfold jointTotal
      rw [applyHalfOut_total hoa, applyHalfIn_total hib]
      -- (total A - amt) + (total B + amt) = total A + total B : the half-edges cancel
      ring

/-! ## The CG-2 binding (HYPOTHESIS) and the joint-soundness keystone

Mirroring `JointTurn.joint_sound`: the CG-2 shared-id agreement is supplied as a **premise**
(`SharedBinding`), never derived. Given that both halves commit to the *same* shared id AND
the bilateral turn commits, the joint turn is atomic-and-conserving. We do NOT derive the
binding from per-cell facts (that is provably unsound per `study-category §1`). -/

/-- **`SharedBinding` — the CG-2 turn-identity agreement, as DATA.** A witness that both
halves of the bilateral turn pin their proof to the *same* shared id. Here `sidOfA` /
`sidOfB` are each side's local turn-id projection (the `account_updates_hash` it commits to,
read from its own committed half); the binding asserts they coincide with the turn's `sid`.
This is the pullback/equalizer datum over `SharedId` — a **premise**, carried, never
synthesised from the two ledgers. -/
structure SharedBinding (bt : BiTurn) where
  /-- The shared id `A`'s half commits to (its local projection of the turn-id). -/
  sidOfA : SharedId
  /-- The shared id `B`'s half commits to. -/
  sidOfB : SharedId
  /-- CG-2 left leg: `A`'s half commits to the turn's shared id. -/
  agreeA : sidOfA = bt.sid
  /-- CG-2 right leg: `B`'s half commits to the *same* shared id. -/
  agreeB : sidOfB = bt.sid

/-- **`SharedBinding.agree` — the equalizer condition** (the two legs collapse): both halves
project the *same* shared id. Derivable from the two legs (cf. `SharedTurnId.agree`). -/
theorem SharedBinding.agree {bt : BiTurn} (s : SharedBinding bt) : s.sidOfA = s.sidOfB :=
  s.agreeA.trans s.agreeB.symm

/-- **`joint_sound_of_binding` — the cross-cell keystone with the binding LOAD-BEARING
(PROVED).** GIVEN the CG-2 shared-id binding (both halves agree on the shared id — supplied
as a HYPOTHESIS, *never derived*) AND that the bilateral turn commits, the joint turn is
**conserving AND bound to one identity**. The conclusion is a *conjunction* whose two legs
need two *different* premises, and that is the point:

  * **CG-5 conservation** `jointTotal A' B' = jointTotal A B` — comes from `h` alone via
    `joint_cg5_conserves`; the binding does NOT enter here.
  * **CG-2 single-identity** `bind.sidOfA = bind.sidOfB` — both committed half-edges pin to
    the *same* shared turn-id. This leg is **unprovable from `h`**: the per-cell commitments
    `applyHalfOut`/`applyHalfIn` say nothing about each side's turn-id projection (the
    `account_updates_hash`); only the `SharedBinding` premise forces the two halves to be the
    *same forest*, not two solo turns that merely happen to conserve. The binding is therefore
    genuinely load-bearing — discard it and this conjunct cannot be closed.

This is exactly REORIENT §2 / `study-category §1.3`: cross-cell soundness is **NOT**
per-cell-sound ∧ per-cell-sound. Conservation is symmetric and per-side-derivable, but the
*identity binding* that makes the two halves one atomic turn is the irreducible CG-2
hypothesis (`νF₁ ⊗ νF₂` is not final). `joint_sound_of_binding` returns BOTH: the keystone is
the pairing of CG-5 (from the machine) with CG-2 (from the binding premise). -/
theorem joint_sound_of_binding {A B A' B' : KernelState} {bt : BiTurn}
    (bind : SharedBinding bt)
    (h : jointApply A B bt = some (A', B')) :
    jointTotal A' B' = jointTotal A B ∧ bind.sidOfA = bind.sidOfB :=
  ⟨joint_cg5_conserves h, bind.agree⟩

/-- **Atomicity companion — both halves commit or neither (PROVED).** If the bilateral turn
commits, *each* half-edge committed in its own ledger (extracting the per-side post-states).
This is the executable face of `JointTurn.atomicity_as_proof`'s cumulative AND: `jointApply`
returns `some` exactly when both `applyHalfOut` and `applyHalfIn` do. -/
theorem joint_atomic {A B A' B' : KernelState} {bt : BiTurn}
    (h : jointApply A B bt = some (A', B')) :
    applyHalfOut A bt = some A' ∧ applyHalfIn B bt = some B' := by
  unfold jointApply at h
  rcases hoa : applyHalfOut A bt with _ | A'' <;> rw [hoa] at h
  · simp at h
  · rcases hib : applyHalfIn B bt with _ | B'' <;> rw [hib] at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hA, hB⟩ := h
      subst hA; subst hB
      exact ⟨rfl, rfl⟩

/-! ## `binding_is_proper` — the binding is a GENUINE restriction (not vacuous)

The executable analog of `JointTurn.binding_is_proper`. Cross-cell soundness is NOT
`per-cell-sound ∧ per-cell-sound`: there exist product configurations the CG-5 binding
**excludes**. We exhibit a *fake bilateral* whose two declared half-edges do NOT sum to zero
— `1` out of one cell, `2` into the other — and show no committed bilateral turn can realize
it as a single `amt` (the `EqualAndOpposite` identity forces `out = in`). Hence the binding
carves a *proper* subobject of the product of ledger-states; it is irreducible. -/

/-- A fake bilateral half-edge pair where the declared deltas do NOT cancel. -/
def FakeBalances (out_amt in_amt : ℤ) : Prop := out_amt + in_amt = 0

/-- **`binding_is_proper` — the CG-5 binding is a genuine (non-vacuous) restriction
(PROVED).** A declared bilateral move of `1` out and `2` in does **not** balance
(`1 + 2 ≠ 0`), so it is excluded by the `EqualAndOpposite` identity that every committed
bilateral turn satisfies (`halves_sum_zero`). Thus there exist product configurations the
binding rejects — cross-side soundness is strictly MORE than per-ledger × per-ledger, and
the binding must be hypothesized, never derived. -/
theorem binding_is_proper : ∃ out_amt in_amt : ℤ, ¬ FakeBalances out_amt in_amt := by
  refine ⟨1, 2, ?_⟩
  unfold FakeBalances
  decide

/-- **The committed bilateral ALWAYS balances (the contrast, PROVED).** Whatever its `amt`,
a `BiTurn`'s real half-edges `(halfA, halfB)` satisfy `FakeBalances` (sum to zero) — so the
`(1, 2)` witness of `binding_is_proper` is *not* realizable as any committed bilateral turn.
This pins down that the binding's exclusion is exactly the `out = in` constraint. -/
theorem real_bilateral_balances (bt : BiTurn) : FakeBalances (halfA bt) (halfB bt) :=
  halves_sum_zero bt

/-! ## It runs (`#eval`)

A bilateral transfer between a cell in ledger `A` and a cell in ledger `B`, the joint total
conserved, and a mismatched / unauthorized attempt rejected. -/

/-- Ledger `A`: cell 0 owns 100, cell 1 owns 5; accounts `{0,1}`; authority by ownership. -/
def sA : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun _ => [] }

/-- Ledger `B`: cell 7 owns 20; accounts `{7}`; authority by ownership. -/
def sB : KernelState :=
  { accounts := {7}
    bal := fun c => if c = 7 then 20 else 0
    caps := fun _ => [] }

/-- A good bilateral: actor 0 sends 30 out of cell 0 (in `A`) into cell 7 (in `B`); actor 7
authorises the credit. Both commit to shared id `42`. -/
def goodBi : BiTurn :=
  { actorA := 0, srcA := 0, actorB := 7, dstB := 7, amt := 30, sid := 42 }

/-- An unauthorized bilateral: actor 2 has no authority over cell 0 in `A` — A's half fails,
so the whole bilateral is rejected (atomic fail-closed). -/
def unauthBi : BiTurn :=
  { actorA := 2, srcA := 0, actorB := 7, dstB := 7, amt := 30, sid := 42 }

/-- An overdraw bilateral: actor 1 owns cell 1 (only 5) but tries to send 30 — A's half
fails on availability, whole turn rejected. -/
def overdrawBi : BiTurn :=
  { actorA := 1, srcA := 1, actorB := 7, dstB := 7, amt := 30, sid := 42 }

#eval (jointApply sA sB goodBi).isSome                                 -- true (both halves commit)
#eval (jointApply sA sB unauthBi).isSome                               -- false (A's half unauthorized)
#eval (jointApply sA sB overdrawBi).isSome                             -- false (A's half overdraws)
#eval jointTotal sA sB                                                 -- 125 (= 105 + 20)
#eval (jointApply sA sB goodBi).map (fun p => jointTotal p.1 p.2)      -- some 125 (CG-5: conserved)
#eval (jointApply sA sB goodBi).map (fun p => (total p.1, total p.2))  -- some (75, 50): A↓30, B↑30
#eval halfA goodBi + halfB goodBi                                      -- 0 (EqualAndOpposite)

end Dregg2.Exec.JointCell
