/-
# Dregg2.Exec.CrossCaveat — cross-cell state caveats as a FURTHER equalizer on the joint turn.

A **cross-cell caveat** is an authorization condition on cell `A` that READS another cell `B`'s
state — e.g. *"this capability on `A` is valid only if `B`'s balance ≥ 100."* dregg1 deliberately
REFUSED these (`authorize.rs:1608` rejects cross-cell key-refs: *"a macaroon is only sound where the
verifier legitimately holds the cell's secret"*) — the right call without a metatheory: a live read
of `B` to authorize `A` is a TOCTOU hole unless the read of `B` and the use on `A` are ONE atomic,
consistently-snapshotted observation. We now have exactly the structure to make it sound, and it is
already half-built in `JointCell`.

## What's going on (the universal property)

`JointCell.SharedBinding` is **the pullback/equalizer datum over `SharedId`** (its own words,
`JointCell.lean:218`): the two half-edges agree on one shared turn-id (`SharedBinding.agree` —
*"the equalizer condition"*, the two legs collapse). `binding_is_proper` proves the bound joint
turns are a PROPER SUBOBJECT of the product of ledger-states — cross-cell soundness is strictly
MORE than per-cell ∧ per-cell.

A cross-cell caveat `φ : KernelState → KernelState → Bool` is **one MORE equalizer condition layered
on that binding**: it further restricts the bound joint turns to the sub-object where `φ` holds (the
equalizer of `φ` against the constant `true`). Admissibility = `SharedBinding ⊓ {φ holds}`.

  * **It is an EQUALIZER (a limit), not a coequalizer.** A caveat *carves a sub-object* (a
    constraint); a coequalizer/pushout *glues/quotients* (that is FORK, the dual, the wrong
    direction). `crossCaveat_sound` returns CG-5 ∧ CG-2-equalizer ∧ `φ` — all limit-side.
  * **`φ` FACTORS THROUGH THE TURN — at the type level.** `φ : KernelState → KernelState → Bool`
    needs BOTH cells; it cannot even be *typed* over a single cell. So a caveat that reads `B`
    *forces* the turn to be a bilateral (joint) turn over `{A, B}` — that is the "factor-thru of
    turn." `φ` lives on the equalized (consistently-snapshotted) joint state, undefined on the
    unbound product.
  * **The adjoint you might sense (base-change `f^* ⊣ f_*` along the cross-cell channel) is the
    sheaf-theoretic PACKAGING — not built here, and decorative until it is.** The concrete,
    buildable structure is the equalizer below.

## Why it is sound now (no TOCTOU) — and the single-machine principle

`jointApply` is ATOMIC (both half-edges commit or neither — `joint_atomic`). The caveat is read on
the SAME pre-state `(A, B)` from which the turn commits (`caveated_check_eq_use`): time-of-check and
time-of-use are the IDENTICAL snapshot, indivisibly — no window for a concurrent turn to invalidate
`φ`. That is the soundness dregg1 lacked the machinery to guarantee.

The COST is topology-parametrized (the Agreement dial / ember's single-machine principle): on a
single machine forming the joint turn over `{A, B}` is free (both cells local, the consistent
snapshot just exists), so cross-cell caveats are cheap AND sound. Distributed (`A`, `B` on different
nodes) the CG-2 equalizer becomes a blocking bilateral agreement that blocks under partition — which
is *why* dregg1 refused it. The price of the pullback is the price of cross-cell consistency, which
collapses to zero on one machine.

Pure executable Lean, `#eval`-able; builds only on `Exec.JointCell` (no new primitives), reusing the
PROVED `joint_sound_of_binding` / `joint_cg5_conserves` / `joint_atomic` / `binding_is_proper`.
-/
import Dregg2.Exec.JointCell

namespace Dregg2.Exec.CrossCaveat

open Dregg2.Exec Dregg2.Exec.JointCell

/-- A **cross-cell caveat** `φ` — a predicate on the JOINT pre-state `(A, B)`. The TYPE alone is the
factoring: `φ` needs BOTH ledgers, so it cannot be evaluated within a single-cell turn; a caveat that
reads cell `B` forces the turn to be a bilateral (joint) turn over `{A, B}`. -/
abbrev CrossCaveat := KernelState → KernelState → Bool

/-- **A caveated bilateral turn.** Fail-closed: commits the atomic bilateral `jointApply` ONLY when
the cross-cell caveat `φ` holds on the pre-state `(A, B)`. Because the bilateral turn is atomic
(`jointApply` commits both halves or neither) and the caveat is read on the SAME pre-state, the
check and the use are one indivisible snapshot — no TOCTOU. -/
def jointApplyCaveated (φ : CrossCaveat) (A B : KernelState) (bt : BiTurn) :
    Option (KernelState × KernelState) :=
  if φ A B = true then jointApply A B bt else none

/-- **`caveated_check_eq_use` — NO TOCTOU (PROVED).** A committed caveated bilateral turn proves the
caveat held on EXACTLY the pre-state `(A, B)` from which the underlying atomic `jointApply` committed
— the time-of-check state and the time-of-use state are the IDENTICAL snapshot `(A, B)`. There is no
gap for a concurrent mutation: `φ` and the commit read the same `A`, `B`, and `jointApply` is atomic.
This is the precise content the cross-cell caveat needed to be sound. -/
theorem caveated_check_eq_use {φ : CrossCaveat} {A B A' B' : KernelState} {bt : BiTurn}
    (h : jointApplyCaveated φ A B bt = some (A', B')) :
    φ A B = true ∧ jointApply A B bt = some (A', B') := by
  unfold jointApplyCaveated at h
  by_cases hφ : φ A B = true
  · rw [if_pos hφ] at h; exact ⟨hφ, h⟩
  · rw [if_neg hφ] at h; exact absurd h (by simp)

/-- **`crossCaveat_sound` — THE KEYSTONE: cross-cell admissibility = equalizer ⊓ caveat (PROVED).**
GIVEN the CG-2 shared-id binding (carried as a HYPOTHESIS, *never derived* — exactly as
`joint_sound_of_binding` requires), a committed caveated bilateral turn is precisely the CONJUNCTION:

  * **CG-5 conservation** `jointTotal A' B' = jointTotal A B` — from the machine (`joint_cg5_conserves`);
  * **CG-2 single-identity** `bind.sidOfA = bind.sidOfB` — the `SharedBinding` equalizer (the two
    legs collapse), unprovable from the commit alone;
  * **the cross-cell caveat** `φ A B = true` — a FURTHER equalizer condition layered on the binding.

So cross-cell admissibility factors as `SharedBinding ⊓ {φ holds}`: the binding alone carves the
proper sub-object of the product (`binding_is_proper`); the caveat refines it by the equalizer of `φ`
against `true`. The caveat read of `B` is sound because (by `caveated_check_eq_use`) it is evaluated
on the same atomic snapshot the turn commits against. -/
theorem crossCaveat_sound {φ : CrossCaveat} {A B A' B' : KernelState} {bt : BiTurn}
    (bind : SharedBinding bt)
    (h : jointApplyCaveated φ A B bt = some (A', B')) :
    jointTotal A' B' = jointTotal A B ∧ bind.sidOfA = bind.sidOfB ∧ φ A B = true := by
  obtain ⟨hφ, hj⟩ := caveated_check_eq_use h
  obtain ⟨hcg5, hcg2⟩ := joint_sound_of_binding bind hj
  exact ⟨hcg5, hcg2, hφ⟩

/-- **`crossCaveat_atomic` — the check and BOTH half-commits are one indivisible step (PROVED).** A
committed caveated turn: `φ` held on `(A, B)`, AND both half-edges committed in their own ledgers
from that same `(A, B)`. So the caveat-check and the two-sided commit are atomic over one snapshot —
the executable face of "no concurrent turn can invalidate `φ` between check and use." -/
theorem crossCaveat_atomic {φ : CrossCaveat} {A B A' B' : KernelState} {bt : BiTurn}
    (h : jointApplyCaveated φ A B bt = some (A', B')) :
    φ A B = true ∧ applyHalfOut A bt = some A' ∧ applyHalfIn B bt = some B' := by
  obtain ⟨hφ, hj⟩ := caveated_check_eq_use h
  obtain ⟨ho, hi⟩ := joint_atomic hj
  exact ⟨hφ, ho, hi⟩

/-- **`crossCaveat_rejects` — THE TEETH (PROVED).** If the cross-cell caveat is FALSE on the
pre-state, the bilateral turn is rejected — EVEN IF the underlying joint turn would otherwise commit.
The caveat genuinely gates: a false `φ` fail-closes the whole turn (it is not a no-op overlay). -/
theorem crossCaveat_rejects {φ : CrossCaveat} {A B : KernelState} {bt : BiTurn}
    (hφ : φ A B = false) : jointApplyCaveated φ A B bt = none := by
  unfold jointApplyCaveated; rw [if_neg (by simp [hφ])]

/-! ## It runs (`#eval`) — a GENUINE cross-cell caveat that reads `B` and gates on it.

The covenant *"cell 0 in ledger `A` must hold at least cell 7's balance in ledger `B`"* — a
condition on `A`'s turn that READS `B`. It admits when `B` is low, rejects when `B` is high. The
contrast is the whole point: the RAW bilateral commits regardless of `B`'s balance (B just gains the
transfer), but the CAVEATED turn rejects when the cross-cell covenant is violated — the caveat read
`B`'s state and gated on it, non-vacuously. -/

/-- A genuine CROSS-CELL caveat: cell `0` in ledger `A` must hold AT LEAST cell `7`'s balance in
ledger `B`. It READS `B` — it cannot be evaluated on `A` alone (the type-level factoring). -/
def covenant : CrossCaveat := fun A B => decide (B.bal 7 ≤ A.bal 0)

/-- A `B`-ledger where cell 7 holds 200 — more than `A`'s cell 0 (100), so the covenant is VIOLATED. -/
def sBhigh : KernelState :=
  { accounts := {7}, bal := fun c => if c = 7 then 200 else 0, caps := fun _ => [] }

#eval covenant sA sB                                              -- true  (20 ≤ 100 — covenant holds)
#eval covenant sA sBhigh                                          -- false (200 ≤ 100 — violated)
#eval (jointApplyCaveated covenant sA sB goodBi).isSome           -- true  (bound + covenant ⇒ ADMITS)
#eval (jointApplyCaveated covenant sA sBhigh goodBi).isSome       -- false (covenant violated by B ⇒ REJECT)
#eval (jointApply sA sBhigh goodBi).isSome                        -- true  (RAW turn fine; only the caveat rejects)
#eval (jointApplyCaveated covenant sA sB goodBi).map (fun p => jointTotal p.1 p.2)  -- some 125 (CG-5 still conserved)

/-- **`covenant_rejects_high` — the cross-cell read genuinely gates (PROVED).** When `B`'s state
violates the covenant (cell 7 = 200 > cell 0 = 100), the caveated turn is rejected — a theorem, not
just an `#eval`. The caveat's dependence on `B`'s state is real and load-bearing. -/
theorem covenant_rejects_high : jointApplyCaveated covenant sA sBhigh goodBi = none := by
  apply crossCaveat_rejects
  show covenant sA sBhigh = false
  decide

/-! ## Axiom-hygiene tripwires — pin the cross-cell-caveat keystones kernel-clean. -/

#assert_axioms caveated_check_eq_use
#assert_axioms crossCaveat_sound
#assert_axioms crossCaveat_atomic
#assert_axioms crossCaveat_rejects
#assert_axioms covenant_rejects_high

end Dregg2.Exec.CrossCaveat
