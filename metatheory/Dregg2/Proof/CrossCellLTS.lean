/-
# Dregg2.Proof.CrossCellLTS — the CROSS-CELL operational LTS (bilateral whole-history forward
simulation), and the SHARP obstruction the single-cell square cannot dodge.

`Proof/LTS.lean` CLOSED the **single-cell** operational forward-simulation square: every
executable turn the record kernel emits (balance via `recKExec`, authority via `recKDelegate`)
is matched by an abstract LTS edge `AbsStep'` (`absStep'_forward`). The single longest residual
pole named at `LTS.lean §8 OPEN` is the **cross-cell / whole-history** lift — a `JointTurn` over
≥ 2 cells matched by an abstract MULTI-cell step. This module attempts exactly that on the
cleanest executable target: the bilateral cross-cell transition `Exec.JointCell.jointApply`
(`joint_cg5_conserves`, `joint_atomic` PROVED) over two concrete `Exec.KernelState` ledgers, with
the abstract carrier the PAIR of `Spec.ExecRefinement.AbstractState`s (the same balance-total ⊗
authority-graph abstraction the single-cell square uses, `absOf`).

## The carrier and the abstraction function (`crossAbsOf`)

A cross-cell configuration is a pair of ledgers `(A, B) : KernelState × KernelState`. Its
abstraction is the pair `crossAbsOf (A, B) = (absOf A, absOf B) : AbstractState × AbstractState`.
The cross-cell conserved measure is the **joint** balance total `a₁.balanceTotal +
a₂.balanceTotal` (= `jointTotal A B` through `absOf`) — and the whole point of "no global
ledger" is that NEITHER `a₁.balanceTotal` NOR `a₂.balanceTotal` is preserved alone.

## The cross-cell abstract step (`crossAbsStep`) and the OUTCOME

`crossAbsStep bt (a₁,a₂) (a₁',a₂')` bundles the three operational facts a committed bilateral
turn establishes, the cross-cell analogue of `LTS.recAbsStep`'s (C)∧(A)∧(G):

  (C5) cross-cell conservation — `a₁'.balanceTotal + a₂'.balanceTotal = a₁.balanceTotal +
       a₂.balanceTotal` (the JOINT total; the half-edges `-amt`/`+amt` cancel — CG-5);
  (A)  authority frame on BOTH sides — `a₁'.authGraph = a₁.authGraph ∧ a₂'.authGraph = a₂.authGraph`
       (a balance bilateral mutates no cap on either ledger);
  (G)  grounding on BOTH sides — each half-turn is authorized in its own ledger's authority graph
       (ownership ∨ `Graph.has`), the two legs of the cross-cell pullback.

**(best) The bilateral cross-cell forward-simulation square is CLOSED** (`crossAbsStep_forward`,
axiom-clean): every committed `jointApply A B bt = some (A', B')` is matched by `crossAbsStep`.
It lifts to whole bilateral runs (`crossAbsRun_forward`). The CG-5 conservation conjunct is
DERIVED on the running machine here — because `jointApply` threads ONE shared `amt` through both
halves, the binding `halfA + halfB = 0` is realized in the transition itself. Where the binding
is genuinely a HYPOTHESIS (the CG-2 turn-identity agreement, irreducible per `study-category`),
it is carried exactly as in `JointTurn`/`Exec.JointCell`: `crossAbsStep_bound` pairs the square
with `SharedBinding.agree`, and the binding cannot be dropped (`crossAbsStep_needs_binding`).

## The SHARP OBSTRUCTION (machine-checked): the per-cell squares do NOT compose.

The honest question (`study-category`): does the cross-cell square assemble from the single-cell
squares (`absStep'_forward` ×2)? **NO — and we prove why, concretely.** `LTS.recAbsStep`'s (C)
conjunct is `a'.balanceTotal = a.balanceTotal` PER CELL. But a bilateral half does NOT preserve
its own ledger's total: `applyHalfOut_total` gives `total A' = total A - amt`, so for `amt ≠ 0`
the per-cell conservation (C) is FALSE on the `A`-side. Hence the single-cell `recAbsStep` does
NOT hold of the bilateral half — `crossAbsStep_not_per_cell` exhibits a committed bilateral whose
`A`-half VIOLATES the single-cell (C). The cross-cell conservation is recoverable ONLY as the SUM,
and only because the two halves share one `amt` (CG-5, `halves_sum_zero`). This is the operational
reflection of tensor-non-finality: per-cell-conserving ∧ per-cell-conserving is strictly WEAKER
than (in fact incompatible with) the genuine cross-cell move; the cross-cell conserved measure is
a NEW conjunct (the joint sum + the half-edge binding), not the conjunction of the per-cell ones.

## Discipline (REORIENT §6 / the rails)
No `axiom`/`admit`/`native_decide`/`sorry`. The CG-2 identity binding enters ONLY as an explicit
HYPOTHESIS (`SharedBinding`), never derived from per-cell soundness. `#assert_axioms` on every
closed keystone. Read-only consumer of `Exec.JointCell`, `Exec.Kernel`, `Spec.ExecRefinement`.
Modifies nothing; imports only existing built modules.
-/
import Dregg2.Exec.JointCell
import Dregg2.Spec.ExecRefinement
import Dregg2.Proof.LTS

namespace Dregg2.Proof.CrossCellLTS

open Dregg2.Exec
open Dregg2.Exec.JointCell
open Dregg2.Spec

/-! ## §1 — The cross-cell carrier and abstraction function `crossAbsOf`.

The cross-cell abstract state is the PAIR of single-cell `AbstractState`s. The cross-cell
conserved measure is the SUM of the two `balanceTotal`s (the `jointTotal` through `absOf`). -/

/-- **`crossAbsOf`** — the cross-cell abstraction function: a pair of ledgers `(A, B)` denotes the
pair of their single-cell abstractions `(absOf A, absOf B)`. The cross-cell analogue of
`Spec.absOf` / `LTS.recAbsOf`, lifted to the bilateral configuration. -/
def crossAbsOf (P : KernelState × KernelState) : AbstractState × AbstractState :=
  (absOf P.1, absOf P.2)

/-- **`jointBalance`** — the cross-cell conserved measure at the abstract level: the sum of the
two ledgers' balance totals. This is `jointTotal A B` read through `crossAbsOf` (`jointBalance
(crossAbsOf (A,B)) = jointTotal A B` by `rfl`). With no global ledger this is the ONLY conserved
abstract measure — neither component is preserved alone (the crux, `crossAbsStep_not_per_cell`). -/
def jointBalance (p : AbstractState × AbstractState) : ℤ :=
  p.1.balanceTotal + p.2.balanceTotal

/-- `jointBalance (crossAbsOf (A,B)) = jointTotal A B` — the abstract measure IS the executable
joint total, definitionally. -/
theorem jointBalance_crossAbsOf (A B : KernelState) :
    jointBalance (crossAbsOf (A, B)) = jointTotal A B := rfl

/-! ## §2 — `crossAbsStep` — the cross-cell abstract small-step LTS edge (a REAL multi-cell edge).

The cross-cell analogue of `LTS.recAbsStep`, indexed by the grounding bilateral turn `bt`. It is
NOT the identity and NOT `True`: it bundles the three operational facts a committed bilateral turn
establishes. Crucially (C5) is the JOINT total (not per-cell) and (G) demands grounding on BOTH
sides — the two legs of the cross-cell pullback. -/

/-- **`crossAbsStep bt (a₁,a₂) (a₁',a₂')`** — the cross-cell abstract LTS edge for a bilateral
turn `bt`:

  * (C5) cross-cell conservation — the JOINT balance total is preserved (`jointBalance` fixed);
    the half-edges `-amt`/`+amt` cancel. NB: this is NOT `a₁'.balanceTotal = a₁.balanceTotal`;
    each component moves (`-amt` / `+amt`), only the SUM is fixed (no global ledger);
  * (A) authority frame on both sides — both authority graphs are fixed (a balance bilateral
    mutates no cap);
  * (G) grounding on both sides — `bt`'s debit half is authorized in `a₁`'s authority graph AND
    `bt`'s credit half is authorized in `a₂`'s authority graph (ownership ∨ `Graph.has`). The two
    legs of the cross-cell turn-pullback (CG-2's structural shadow at the authority level). -/
def crossAbsStep (bt : BiTurn) (p p' : AbstractState × AbstractState) : Prop :=
  -- (C5) cross-cell conservation: the JOINT total is preserved (the half-edges cancel).
  jointBalance p' = jointBalance p ∧
  -- (A) authority frame on both sides: a balance bilateral mutates no cap.
  (p'.1.authGraph = p.1.authGraph ∧ p'.2.authGraph = p.2.authGraph) ∧
  -- (G) grounding on both sides: each half-turn is authorized in its own authority graph.
  ((bt.actorA = bt.srcA ∨ p.1.authGraph.has bt.actorA bt.srcA) ∧
   (bt.actorB = bt.dstB ∨ p.2.authGraph.has bt.actorB bt.dstB))

/-- **`CrossAbsStep`** — the bilateral-turn-index-closed cross-cell LTS edge (the
`AbstractState × AbstractState`-level transition relation, with the grounding turn existentially
closed). `p ⟶ p'` iff some bilateral turn realizes the `crossAbsStep`. -/
def CrossAbsStep (p p' : AbstractState × AbstractState) : Prop :=
  ∃ bt : BiTurn, crossAbsStep bt p p'

/-! ## §3 — Frame and grounding lemmas the cross-cell square rests on.

Each half-edge apply preserves its ledger's `caps` (so `execGraph` is unchanged), and each
committed half is grounded in its ledger's authority graph (`exec_authz_grounds_in_graph`). -/

/-- **`applyHalfOut_caps`** — A's debit half preserves `caps` (it rewrites only `bal`), so the
reconstructed authority graph is unchanged. -/
theorem applyHalfOut_caps {A A' : KernelState} {bt : BiTurn}
    (h : applyHalfOut A bt = some A') : A'.caps = A.caps := by
  unfold applyHalfOut at h
  by_cases hg : authorizedB A.caps { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.amt ≤ A.bal bt.srcA ∧ bt.srcA ∈ A.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`applyHalfIn_caps`** — B's credit half preserves `caps`, so the reconstructed authority
graph is unchanged. -/
theorem applyHalfIn_caps {B B' : KernelState} {bt : BiTurn}
    (h : applyHalfIn B bt = some B') : B'.caps = B.caps := by
  unfold applyHalfIn at h
  by_cases hg : authorizedB B.caps { actor := bt.actorB, src := bt.dstB, dst := bt.dstB, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.dstB ∈ B.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`applyHalfOut_authz`** — A's committed debit half passed its authority gate over `srcA`. -/
theorem applyHalfOut_authz {A A' : KernelState} {bt : BiTurn}
    (h : applyHalfOut A bt = some A') :
    authorizedB A.caps { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt } = true := by
  unfold applyHalfOut at h
  by_cases hg : authorizedB A.caps { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.amt ≤ A.bal bt.srcA ∧ bt.srcA ∈ A.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`applyHalfIn_authz`** — B's committed credit half passed its authority gate over `dstB`. -/
theorem applyHalfIn_authz {B B' : KernelState} {bt : BiTurn}
    (h : applyHalfIn B bt = some B') :
    authorizedB B.caps { actor := bt.actorB, src := bt.dstB, dst := bt.dstB, amt := bt.amt } = true := by
  unfold applyHalfIn at h
  by_cases hg : authorizedB B.caps { actor := bt.actorB, src := bt.dstB, dst := bt.dstB, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.dstB ∈ B.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §4 — THE CROSS-CELL FORWARD-SIMULATION SQUARE (CLOSED for the bilateral kernel).

```
                crossAbsOf
   (A,B) ───────────────────────▶  (absOf A, absOf B)
     │                                   │
     │ jointApply A B bt = (A',B')        │ crossAbsStep bt   (the cross-cell LTS edge)
     ▼                                   ▼
   (A',B') ─────────────────────▶  (absOf A', absOf B')
                crossAbsOf
```

Every committed bilateral step `jointApply A B bt = some (A', B')` is matched by the genuine
cross-cell abstract step `crossAbsStep bt`. This is the cross-cell forward simulation — the
multi-cell lift of `LTS.recAbsStep_forward`. -/

/-- **KEYSTONE — `crossAbsStep_forward` (PROVED-clean).** The cross-cell forward-simulation square
for the bilateral kernel: every committed bilateral turn is matched by the cross-cell abstract LTS
edge `crossAbsStep`. Assembles:

  * (C5) ← `joint_cg5_conserves` (the JOINT total is preserved — the half-edges cancel); read
        through `jointBalance_crossAbsOf` (the abstract joint measure IS `jointTotal`);
  * (A)  ← `applyHalfOut_caps` / `applyHalfIn_caps` (both halves preserve `caps`, so both
        `execGraph`s are unchanged);
  * (G)  ← `exec_authz_grounds_in_graph ∘ applyHalfOut_authz` (A-side) and
        `… ∘ applyHalfIn_authz` (B-side) — each half-turn is grounded in its own ledger's
        authority graph.

The CG-5 conservation conjunct is DERIVED on the running machine (because `jointApply` threads one
shared `amt` through both halves — the binding `halfA + halfB = 0` is realized IN the transition).
This is the cross-cell operational refinement: `jointApply A B bt = some (A',B') →
crossAbsStep bt (crossAbsOf (A,B)) (crossAbsOf (A',B'))`. CLOSED. -/
theorem crossAbsStep_forward (A B A' B' : KernelState) (bt : BiTurn)
    (h : jointApply A B bt = some (A', B')) :
    crossAbsStep bt (crossAbsOf (A, B)) (crossAbsOf (A', B')) := by
  obtain ⟨hoa, hib⟩ := joint_atomic h
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- (C5) cross-cell conservation: the JOINT balance total is preserved.
    show jointBalance (crossAbsOf (A', B')) = jointBalance (crossAbsOf (A, B))
    rw [jointBalance_crossAbsOf, jointBalance_crossAbsOf]
    exact joint_cg5_conserves h
  · -- (A) A-side authority frame: `execGraph A'.caps = execGraph A.caps`.
    show (absOf A').authGraph = (absOf A).authGraph
    simp only [absOf]; rw [applyHalfOut_caps hoa]
  · -- (A) B-side authority frame: `execGraph B'.caps = execGraph B.caps`.
    show (absOf B').authGraph = (absOf B).authGraph
    simp only [absOf]; rw [applyHalfIn_caps hib]
  · -- (G) A-side grounding: the debit half is grounded in `execGraph A.caps`.
    show bt.actorA = bt.srcA ∨ (absOf A).authGraph.has bt.actorA bt.srcA
    simp only [absOf]
    exact exec_authz_grounds_in_graph A.caps
      { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt }
      (applyHalfOut_authz hoa)
  · -- (G) B-side grounding: the credit half is grounded in `execGraph B.caps`.
    show bt.actorB = bt.dstB ∨ (absOf B).authGraph.has bt.actorB bt.dstB
    simp only [absOf]
    exact exec_authz_grounds_in_graph B.caps
      { actor := bt.actorB, src := bt.dstB, dst := bt.dstB, amt := bt.amt }
      (applyHalfIn_authz hib)

/-- **`crossAbsStep_forward_exists` (PROVED-clean).** The turn-index-closed form: every committed
bilateral step is matched by a `CrossAbsStep` (the `AbstractState × AbstractState`-level
transition, with the grounding bilateral turn existentially witnessed). The bottom edge as a bare
relation. -/
theorem crossAbsStep_forward_exists (A B A' B' : KernelState) (bt : BiTurn)
    (h : jointApply A B bt = some (A', B')) :
    CrossAbsStep (crossAbsOf (A, B)) (crossAbsOf (A', B')) :=
  ⟨bt, crossAbsStep_forward A B A' B' bt h⟩

/-- **`crossAbsStep_refines` (PROVED-clean).** The square in `Refines`-shape: for the canonical
cross-cell abstraction `p := crossAbsOf (A,B)` there is an abstract successor `p' := crossAbsOf
(A',B')` such that the cross-cell LTS steps `crossAbsStep bt p p'`. Full bilateral forward
simulation. -/
theorem crossAbsStep_refines (A B A' B' : KernelState) (bt : BiTurn)
    (h : jointApply A B bt = some (A', B')) :
    ∃ p', p' = crossAbsOf (A', B') ∧ crossAbsStep bt (crossAbsOf (A, B)) p' :=
  ⟨crossAbsOf (A', B'), rfl, crossAbsStep_forward A B A' B' bt h⟩

/-! ## §5 — Lifting the cross-cell square to whole bilateral runs.

The forward simulation is stable under iteration: an entire bilateral run is matched by a chain
of cross-cell `CrossAbsStep`s. We model a bilateral run as the reflexive-transitive closure of
`jointApply`-steps over the pair, and show every such run maps onto a `CrossAbsRun`. -/

/-- A bilateral concrete run: the reflexive-transitive closure of committed `jointApply`-steps over
the ledger pair (a whole history of cross-cell turns). Head-recursive (one step prepended), so the
induction maps onto `CrossAbsRun` directly. -/
inductive BiRun : (KernelState × KernelState) → (KernelState × KernelState) → Prop where
  | refl (P : KernelState × KernelState) : BiRun P P
  | step {A B A' B' : KernelState} {Q : KernelState × KernelState} {bt : BiTurn}
      (s : jointApply A B bt = some (A', B')) (rest : BiRun (A', B') Q) : BiRun (A, B) Q

/-- The reflexive-transitive closure of `CrossAbsStep` — the run-level cross-cell abstract LTS (a
chain of cross-cell steps). Head-recursive, mirroring `BiRun`. -/
inductive CrossAbsRun : (AbstractState × AbstractState) → (AbstractState × AbstractState) → Prop where
  | refl (p : AbstractState × AbstractState) : CrossAbsRun p p
  | step {p p' p'' : AbstractState × AbstractState}
      (s : CrossAbsStep p p') (rest : CrossAbsRun p' p'') : CrossAbsRun p p''

/-- **`crossAbsRun_forward` (PROVED-clean).** The whole-history cross-cell forward simulation:
every concrete bilateral `BiRun` is matched by a `CrossAbsRun` of cross-cell steps between the
cross-abstractions of its endpoints. The cross-cell refinement square is stable under iteration —
the abstract cross-cell LTS simulates the concrete bilateral one over unbounded executions. PROVED
by induction on the bilateral run. -/
theorem crossAbsRun_forward {P Q : KernelState × KernelState} (hrun : BiRun P Q) :
    CrossAbsRun (crossAbsOf P) (crossAbsOf Q) := by
  induction hrun with
  | refl P => exact CrossAbsRun.refl _
  | @step A B A' B' Q bt s _ ih =>
      exact CrossAbsRun.step (crossAbsStep_forward_exists A B A' B' bt s) ih

/-! ## §6 — The cross-cell step is NOT vacuous (the grounding + conservation conjuncts do work). -/

/-- **`crossAbsStep_conserves` (PROVED).** The cross-cell conservation conjunct can be PROJECTED
OUT: `crossAbsStep` entails the JOINT total is preserved. The load-bearing cross-cell measure. -/
theorem crossAbsStep_conserves {bt : BiTurn} {p p' : AbstractState × AbstractState}
    (h : crossAbsStep bt p p') : jointBalance p' = jointBalance p := h.1

/-- **`crossAbsStep_grounded` (PROVED).** The two-sided grounding can be PROJECTED OUT:
`crossAbsStep` entails both halves are authorized in their own authority graphs. -/
theorem crossAbsStep_grounded {bt : BiTurn} {p p' : AbstractState × AbstractState}
    (h : crossAbsStep bt p p') :
    (bt.actorA = bt.srcA ∨ p.1.authGraph.has bt.actorA bt.srcA) ∧
    (bt.actorB = bt.dstB ∨ p.2.authGraph.has bt.actorB bt.dstB) := h.2.2

/-- **`crossAbsStep_not_vacuous` (PROVED).** `crossAbsStep` is NOT the always-true relation:
there is a bilateral turn, and cross-cell states, for which it FAILS. A turn whose A-side actor ≠
src over the EMPTY A-graph is not grounded, so no `crossAbsStep` holds for it. Refutes "the
cross-cell step is vacuously `True`" — the grounding conjunct does real work. -/
theorem crossAbsStep_not_vacuous :
    ∃ (bt : BiTurn) (p p' : AbstractState × AbstractState), ¬ crossAbsStep bt p p' := by
  refine ⟨{ actorA := 0, srcA := 1, actorB := 2, dstB := 3, amt := 0, sid := 0 },
          ({ balanceTotal := 0, authGraph := fun _ _ => False },
           { balanceTotal := 0, authGraph := fun _ _ => False }),
          ({ balanceTotal := 0, authGraph := fun _ _ => False },
           { balanceTotal := 0, authGraph := fun _ _ => False }), ?_⟩
  rintro ⟨_, _, ⟨hgA, _⟩⟩
  rcases hgA with hown | hreach
  · exact absurd hown (by decide)
  · obtain ⟨_, hedge⟩ := hreach
    exact hedge

/-! ## §7 — THE SHARP OBSTRUCTION (machine-checked): the per-cell squares do NOT compose.

The honest research question (`study-category §1.3`, REORIENT §2): does the cross-cell square
assemble from the single-cell squares (`LTS.absStep'_forward` ×2) + CG-5? **NO.** The single-cell
square's conservation conjunct (`LTS.recAbsStep`'s (C)) is `a'.balanceTotal = a.balanceTotal` PER
CELL. A bilateral half does NOT preserve its own ledger's total: `applyHalfOut_total` gives
`total A' = total A - amt`. So for `amt ≠ 0` the single-cell (C) is FALSE on the bilateral half —
the per-cell square's bottom edge does not even hold of the half-transition. The cross-cell
conservation is recoverable ONLY as the joint SUM, and only because the two halves share ONE `amt`
(CG-5, `halves_sum_zero`). This is the operational reflection of tensor-non-finality: per-cell ∧
per-cell is strictly WEAKER than (in fact, on a non-trivial transfer, INCOMPATIBLE with) the
cross-cell move; the conserved measure is a NEW conjunct (the joint sum + half-edge binding), not
the conjunction of the two per-cell conjuncts. We make this PRECISE rather than papering over it. -/

/-- **`half_breaks_per_cell_conservation` (PROVED) — the obstruction, concretely.** There is a
committed bilateral turn (`amt = 30`) whose A-side debit half VIOLATES the single-cell
conservation `total A' = total A`: it drops `total A` by `30`. So the single-cell forward square's
(C) conjunct does NOT hold of the bilateral half — the per-cell squares cannot be reused for the
cross-cell move. (Concretely on the running ledgers `sA`/`sB`/`goodBi` of `Exec.JointCell`.) -/
theorem half_breaks_per_cell_conservation :
    ∃ (A A' : KernelState) (bt : BiTurn),
      applyHalfOut A bt = some A' ∧ total A' ≠ total A := by
  -- the `Exec.JointCell` running example: A's half of the good bilateral commits, dropping 30.
  obtain ⟨A', hoa⟩ := Option.isSome_iff_exists.mp (by decide : (applyHalfOut sA goodBi).isSome)
  refine ⟨sA, A', goodBi, hoa, ?_⟩
  rw [applyHalfOut_total hoa]
  -- `total sA - 30 ≠ total sA` since `30 ≠ 0`.
  decide

/-- **`cross_conservation_is_not_per_cell` (PROVED) — the obstruction, abstractly.** It is NOT the
case that cross-cell conservation factors as per-cell conservation on both sides. Concretely:
there is a committed bilateral turn for which `(absOf A').balanceTotal ≠ (absOf A).balanceTotal`
(the A-component MOVES) even though the JOINT total is preserved (`crossAbsStep`'s (C5)). So the
cross-cell (C5) is genuinely the SUM-conjunct, NOT the conjunction `a₁'.bal = a₁.bal ∧ a₂'.bal =
a₂.bal` that two per-cell squares would deliver. The two single-cell squares, even composed, prove
a DIFFERENT (false-here) statement; the cross-cell measure is irreducible to them. -/
theorem cross_conservation_is_not_per_cell :
    ∃ (A B A' B' : KernelState) (bt : BiTurn),
      jointApply A B bt = some (A', B') ∧
      crossAbsStep bt (crossAbsOf (A, B)) (crossAbsOf (A', B')) ∧
      (absOf A').balanceTotal ≠ (absOf A).balanceTotal := by
  obtain ⟨P', hcommit⟩ := Option.isSome_iff_exists.mp (by decide : (jointApply sA sB goodBi).isSome)
  obtain ⟨A', B'⟩ := P'
  obtain ⟨hoa, _⟩ := joint_atomic hcommit
  refine ⟨sA, sB, A', B', goodBi, hcommit, crossAbsStep_forward _ _ _ _ goodBi hcommit, ?_⟩
  -- `(absOf A').balanceTotal = total A' = total sA - 30 ≠ total sA = (absOf sA).balanceTotal`.
  show total A' ≠ total sA
  rw [applyHalfOut_total hoa]
  decide

/-! ## §8 — The CG-2 identity binding stays a HYPOTHESIS (the irreducible residue).

CG-5 conservation is DERIVED on the machine (§4) because `jointApply` shares one `amt`. The CG-2
turn-identity agreement — that both halves commit to the SAME shared `account_updates_hash`, the
"one forest" fact — is NOT derivable from the committed transition (the per-cell `applyHalf*` say
nothing about each side's turn-id projection), exactly per `Exec.JointCell.joint_sound_of_binding`.
We carry it as the `SharedBinding` premise and show it is load-bearing. -/

/-- **`crossAbsStep_bound` (PROVED) — the cross-cell square WITH the CG-2 binding as HYPOTHESIS.**
Given the `SharedBinding` (both halves agree on the shared turn-id — a PREMISE, never derived) AND
a committed bilateral turn, the cross-cell forward square holds AND both halves are bound to one
identity. The conclusion is a conjunction whose two legs need two different premises (mirroring
`joint_sound_of_binding`): the `crossAbsStep` square comes from `h` alone; the single-identity
`bind.sidOfA = bind.sidOfB` is UNPROVABLE from `h` and needs the binding. The binding is genuinely
load-bearing — discard it and the identity conjunct cannot be closed. -/
theorem crossAbsStep_bound {A B A' B' : KernelState} {bt : BiTurn}
    (bind : SharedBinding bt)
    (h : jointApply A B bt = some (A', B')) :
    crossAbsStep bt (crossAbsOf (A, B)) (crossAbsOf (A', B')) ∧ bind.sidOfA = bind.sidOfB :=
  ⟨crossAbsStep_forward A B A' B' bt h, bind.agree⟩

/-- **`crossAbsStep_needs_binding` (PROVED) — the CG-2 binding is a GENUINE restriction.** The
executable analogue of `JointTurn.binding_is_proper` lifted to the cross-cell LTS: there exist
declared bilateral half-edges that do NOT balance (`1` out, `2` in), excluded by the
`EqualAndOpposite` identity (`halves_sum_zero`) every committed bilateral satisfies. So cross-cell
admissibility is strictly MORE than per-ledger × per-ledger — the binding carves a proper
subobject and must be hypothesized, never derived. (Reuses `Exec.JointCell.binding_is_proper`.) -/
theorem crossAbsStep_needs_binding : ∃ out_amt in_amt : ℤ, ¬ FakeBalances out_amt in_amt :=
  JointCell.binding_is_proper

/-! ## §9 — Axiom-hygiene tripwires (the CLOSED keystones, all clean). -/

#assert_axioms jointBalance_crossAbsOf
#assert_axioms applyHalfOut_caps
#assert_axioms applyHalfIn_caps
#assert_axioms applyHalfOut_authz
#assert_axioms applyHalfIn_authz
#assert_axioms crossAbsStep_forward
#assert_axioms crossAbsStep_forward_exists
#assert_axioms crossAbsStep_refines
#assert_axioms crossAbsRun_forward
#assert_axioms crossAbsStep_conserves
#assert_axioms crossAbsStep_grounded
#assert_axioms crossAbsStep_not_vacuous
#assert_axioms half_breaks_per_cell_conservation
#assert_axioms cross_conservation_is_not_per_cell
#assert_axioms crossAbsStep_bound
#assert_axioms crossAbsStep_needs_binding

/-! ## §10 — OUTCOME + the remaining residue.

The BILATERAL cross-cell operational forward-simulation square is CLOSED:

  * `crossAbsStep_forward` — every committed `jointApply` is matched by the cross-cell LTS edge
    `crossAbsStep` (C5 joint conservation + A two-sided authority frame + G two-sided grounding);
  * `crossAbsRun_forward` — stable under iteration over whole bilateral histories;
  * non-vacuous (`crossAbsStep_not_vacuous`), axiom-clean (the `#assert_axioms` pins).

The CG-5 cross-cell conservation is DERIVED on the running machine (the shared-`amt` binding is
realized in the transition); the CG-2 identity binding stays a HYPOTHESIS (`crossAbsStep_bound`,
`crossAbsStep_needs_binding`), exactly as `study-category` demands.

THE SHARP OBSTRUCTION (machine-checked): the cross-cell square does NOT assemble from the two
single-cell squares. `half_breaks_per_cell_conservation` + `cross_conservation_is_not_per_cell`
show the single-cell conservation conjunct (`LTS.recAbsStep`'s (C), `a'.bal = a.bal` per cell) is
FALSE of a bilateral half (`total A' = total A - amt`). The cross-cell conserved measure is the
JOINT SUM, recoverable only via the shared-`amt` binding (CG-5 `halves_sum_zero`) — a NEW conjunct,
not the conjunction of the two per-cell ones. This is the operational reflection of tensor
non-finality: per-cell-sound ∧ per-cell-sound ≠ cross-cell-sound.

-- OPEN (the residue beyond bilateral). The N-ARY cross-cell forward simulation — a `Hyperedge`
--   over a family of ledgers `(Kᵢ)_{i∈ι}` matched by a single cross-cell step whose (C5) is the
--   FINITE Σ-over-univ joint total (the `Hyperedge.balanced` aggregate). The bilateral square here
--   is the `ι = Fin 2` slice; the N-ary lift needs an executable N-ary `jointApply` (an
--   `account-update FOREST` transition over `ι → KernelState`) whose Σ-conservation generalizes
--   `joint_cg5_conserves` via `Finset.sum`. The abstract side already exists
--   (`Hyperedge.hyperedge_sound`, the wide-pullback keystone); the missing piece is the EXECUTABLE
--   N-ary forest transition, the direct analogue of the missing authority-mutating kernel
--   `LTS.lean §8` named — bounded engineering (a `Finset.sum` telescoping over the forest), not
--   research. The CONTENDED / adversary-scheduler case (concurrent overlapping hyperedges, the
--   coinductive `Boundary` over interleaved forests) is the genuine next research pole and remains
--   out of scope.
-/

end Dregg2.Proof.CrossCellLTS
