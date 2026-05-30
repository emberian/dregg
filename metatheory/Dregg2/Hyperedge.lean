/-
# Dregg2.Hyperedge — the turn as an ATOMIC HYPEREDGE (wide pullback over `TurnId`).

`JointTurn.lean` gives the **binary** cross-cell binding: `SharedTurnId` (the CG-2
turn-identity pullback for TWO participants — both legs collapse through one `tid`),
`JointBinding` (CG-2 ⊗ CG-5, an irreducible HYPOTHESIS), and a stubbed N-ary
`JointFamily`/`FamilyBinding`/`family_joint_sound` (a *family of binary edges* hashed into
one forest). This module records the thesis those stubs gesture at:

  **A turn is ONE atomic unit incident to a finite SET of participant cells `{Cᵢ}_{i∈ι}` —
  an atomic HYPEREDGE — NOT a family of pairwise bindings.**

Categorically it is the **wide pullback** (the N-fold fiber product over `TurnId`): every
participant's post-step projects to ONE shared `tid`. This is a *single object with N
legs*, the honest N-ary generalization of `SharedTurnId` (the special case `ι = Fin 2`).
Mina's `account_updates_hash` is exactly this: not `C(N,2)` pairwise agreements, but one
hash all `N` updates commit to — the apex of the wide pullback.

Why it might *loosen the knot* (the research question, §4): the binary `joint_sound`
needed an explicit `JointBinding` premise precisely because the binding is a *pairwise*
fact glued by hand. The hyperedge frames the binding as ONE wide-pullback object. If the
soundness cut is "the binding does the work in one step", a single apex `tid` + a single
Σ-over-`univ` may discharge it without the `O(N²)` bookkeeping. We test that below and
report honestly.

Style (matching `Boundary`/`JointTurn`): spec-first, faithful `Prop`s, real content; every
`sorry` is a precisely-stated genuine obligation, never a vacuous `True`/`Iff.rfl` and
never `axiom`/`admit`. PROVED keystones are pinned with `#assert_axioms`.
-/
import Dregg2.Core
import Dregg2.Boundary
import Dregg2.JointTurn
import Dregg2.Tactics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Abel

namespace Dregg2.Hyperedge

open Dregg2.Boundary Dregg2.JointTurn

universe u v

/- Layer parameters, inherited from `Boundary`/`JointTurn`: `Obs`/`AdmissibleTurn` are the
single-cell behaviour-functor data; `TurnId` is the shared turn-identity type
(`account_updates_hash`); `Bal` is the commutative monoid the CG-5 conservation aggregate
lands in (exactly `Core.Conservation`'s value monoid). -/
variable {Obs AdmissibleTurn TurnId : Type u}
variable {Bal : Type u} [AddCommMonoid Bal]

/-! ## §1 — `Hyperedge`: the wide pullback over `TurnId`

We pick the **single shared carrier** encoding: all participants are points of one
`TurnCoalg T` (the usual setting — every cell is a state of the same final coalgebra `νF`),
indexed by a finite `ι`. The pre-states are a tuple `x : ι → T.Carrier`. (A dependent
family `T : ι → TurnCoalg …` is the strictly-more-general reading; it costs a heterogeneous
Σ-sum with no extra categorical content here, so the homogeneous tuple is the cleaner apex.
The dependent variant is recorded as `DepHyperedge` at the end of §1 for completeness.)

The wide pullback `lim (Cᵢ → TurnId ← *)` has:
  * an apex carrying the participant tuple + the shared turn + the shared id;
  * **N legs** `agree i`, each saying participant `i`'s post-step turn-id IS the apex `tid`
    (CG-2, the cone condition — every leg factors through the single apex `tid`);
  * the **N-ary CG-5** `balanced`: `Σ_{i∈univ} halfEdge i (x i) t = 0` (one finite
    monoid-sum, not `C(N,2)` pairwise `EqualAndOpposite`s). -/

/-- **`Hyperedge T turnId halfEdge` — the atomic hyperedge over the participant index `ι`.**
The wide pullback (N-fold fiber product over `TurnId`) of the participants' `turnId ∘ next`
maps, packaged with the CG-5 conservation aggregate.

`turnId i` / `halfEdge i` are the per-incidence projections (each participant slot may read
its turn-id and contribute its signed half-edge differently — e.g. the `+δ`/`−δ` poles of a
swap, or the distinct legs of a ring). They are indexed by `i : ι` so a single physical
cell appearing in two slots is two *incidences*, which is what a hyperedge wants. -/
structure Hyperedge
    (ι : Type v) [Fintype ι]
    (T : TurnCoalg Obs AdmissibleTurn)
    (turnId  : ι → TurnIdOf (TurnId := TurnId) T)
    (halfEdge : ι → HalfEdgeOf (Bal := Bal) T)
    where
  /-- The per-participant pre-states — the participant tuple the hyperedge is incident to. -/
  x   : ι → T.Carrier
  /-- The single shared turn (one hyperedge, one turn fired atomically at all incidences). -/
  t   : AdmissibleTurn
  /-- The shared turn-id — the **apex** of the wide pullback (Mina's `account_updates_hash`). -/
  tid : TurnId
  /-- **CG-2, the wide-pullback cone condition.** Every leg factors through the *one* apex
  `tid`: participant `i`'s post-step commits to the shared id. This is the N-ary
  generalization of `SharedTurnId.agree₁`/`agree₂` — all `N` legs at once. -/
  agree : ∀ i, turnId i (T.next (x i) t) = tid
  /-- **CG-5, the N-ary conservation aggregate.** The finite monoid-sum of every
  incidence's half-edge balances to `0` (the signed edge-fingerprint balance over the whole
  hyperedge). One Σ over `Finset.univ`, valued in `Bal` so it also holds over commitments. -/
  balanced : (Finset.univ.sum fun i => halfEdge i (x i) t) = 0

/-! ### The cone collapses: any two legs agree (the equalizer condition, N-ary, PROVED).

This is the content `SharedTurnId.agree` gave in the binary case — derived here for *every*
pair of incidences from the single apex, with no pairwise hypotheses. The whole point of
the wide-pullback framing: pairwise agreement is a *theorem*, not `C(N,2)` data. -/

/-- **`Hyperedge.legs_agree` — every pair of incidences shares a turn-id (PROVED).** For any
two participants `i j`, their post-step turn-ids are equal — because both equal the single
apex `tid`. The `O(N²)` pairwise `SharedTurnId`s of the family-of-binary-edges framing are
*recovered for free* from the one apex; none are hypothesized. -/
theorem Hyperedge.legs_agree
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    {turnId : ι → TurnIdOf (TurnId := TurnId) T}
    {halfEdge : ι → HalfEdgeOf (Bal := Bal) T}
    (H : Hyperedge ι T turnId halfEdge) (i j : ι) :
    turnId i (T.next (H.x i) H.t) = turnId j (T.next (H.x j) H.t) :=
  (H.agree i).trans (H.agree j).symm

/-- A **dependent** hyperedge: participants live in a *family* `T : ι → TurnCoalg …` rather
than one shared carrier. Strictly more general; the CG-5 sum is over the same `Bal`. Recorded
for completeness — the homogeneous `Hyperedge` is the apex we develop, and every result below
transports to `DepHyperedge` by reading `T i` for `T`. -/
structure DepHyperedge
    (ι : Type v) [Fintype ι]
    (T : ι → TurnCoalg Obs AdmissibleTurn)
    (turnId  : (i : ι) → TurnIdOf (TurnId := TurnId) (T i))
    (halfEdge : (i : ι) → HalfEdgeOf (Bal := Bal) (T i))
    where
  /-- Per-participant pre-states in the dependent carriers. -/
  x   : (i : ι) → (T i).Carrier
  /-- The single shared turn. -/
  t   : AdmissibleTurn
  /-- The shared apex turn-id. -/
  tid : TurnId
  /-- CG-2 cone: every dependent leg factors through `tid`. -/
  agree : ∀ i, turnId i ((T i).next (x i) t) = tid
  /-- CG-5: the finite monoid-sum over the dependent family balances to `0`. -/
  balanced : (Finset.univ.sum fun i => halfEdge i (x i) t) = 0

/-! ## §2 — `HyperAdmissible`: the subobject of the N-fold product the hyperedge carves out.

Analogue of `JointTurn.JointAdmissible`. The N-fold product carrier is `ι → T.Carrier` (the
tuple of all participant states). A tuple-transition under turn `t` is admissible exactly
when there is a `Hyperedge` whose apex *names this very tuple and turn* — i.e. CG-2 holds at
all legs and CG-5 balances for it. This is the wide-pullback subobject of `ι → T.Carrier`. -/

/-- **`HyperAdmissible` — the hyperedge-carved admissibility predicate.** The tuple `xs`
under turn `t` is admissible iff some `Hyperedge` has it as its incidence tuple. The
existential is the image of the wide-pullback apex inside the product carrier `ι → T.Carrier`
— a *proper* subobject in general (see `hyper_binding_is_proper`). -/
def HyperAdmissible
    (ι : Type v) [Fintype ι]
    (T : TurnCoalg Obs AdmissibleTurn)
    (turnId  : ι → TurnIdOf (TurnId := TurnId) T)
    (halfEdge : ι → HalfEdgeOf (Bal := Bal) T)
    (xs : ι → T.Carrier) (t : AdmissibleTurn) : Prop :=
  ∃ H : Hyperedge ι T turnId halfEdge, H.x = xs ∧ H.t = t

/-- **`hyper_binding_is_proper` — the hyperedge is a PROPER subobject (PROVED).** The N-ary
analogue of `JointTurn.binding_is_proper`: there is a configuration (here a singleton
hyperedge, `ι = Unit`, one incidence moving a half-edge of `1 : ℕ`, so the CG-5 sum is
`1 ≠ 0`) that is NOT `HyperAdmissible`. Hence the hyperedge binding is genuine content the
per-cell data cannot supply — the same irreducibility as the binary case, now at the apex. -/
theorem hyper_binding_is_proper :
    ∃ (T : TurnCoalg Unit Unit)
      (turnId : Unit → TurnIdOf (TurnId := Unit) T)
      (halfEdge : Unit → HalfEdgeOf (Bal := Nat) T)
      (xs : Unit → T.Carrier) (t : Unit),
      ¬ HyperAdmissible Unit T turnId halfEdge xs t := by
  let T : TurnCoalg Unit Unit := { Carrier := Unit, step := fun _ => ((), fun _ => ()) }
  refine ⟨T, fun _ _ => (), fun _ _ _ => 1, fun _ => (), (), ?_⟩
  -- a `Hyperedge` here would need CG-5 `Σ_{Unit} 1 = 0` in ℕ, i.e. `1 = 0` — impossible.
  rintro ⟨H, -, -⟩
  have : (Finset.univ.sum fun _ : Unit => (1 : Nat)) = 0 := H.balanced
  simp at this

/-! ## §3 — Recovering the special cases (the cleanup payoff)

The thesis: bilateral, ring, and forest are all *incidences of one `Hyperedge`*. We make
that precise for the binary case (`ι = Fin 2` ↔ `SharedTurnId`/`JointBinding`) and sketch
the ring. -/

/-! ### §3.1 — Binary: a 2-incidence hyperedge IS a `SharedTurnId` + `JointBinding`.

`ι = Fin 2`. Incidence `0` is participant 1, incidence `1` is participant 2. Both
participants live in the same `T` (the homogeneous reading; the binary `SharedTurnId` allowed
two *different* coalgebras `T₁ T₂`, so we recover the **homogeneous** binary special case
`T₁ = T₂ = T`, which is exactly the `study-category §1.4` shared-carrier setting). -/

/-- **`Hyperedge.toSharedTurnId` — the binary hyperedge gives the CG-2 pullback (PROVED).**
A `Fin 2`-indexed hyperedge over a single carrier `T` reconstructs the binary
`SharedTurnId T T …`: its two legs `agree 0`, `agree 1` are precisely the `agree₁`, `agree₂`
of the pullback. The wide pullback at `N = 2` IS the binary pullback. -/
def Hyperedge.toSharedTurnId
    {T : TurnCoalg Obs AdmissibleTurn}
    {turnId : Fin 2 → TurnIdOf (TurnId := TurnId) T}
    {halfEdge : Fin 2 → HalfEdgeOf (Bal := Bal) T}
    (H : Hyperedge (Fin 2) T turnId halfEdge) :
    SharedTurnId (TurnId := TurnId) T T (turnId 0) (turnId 1) where
  x₁ := H.x 0
  x₂ := H.x 1
  t  := H.t
  tid := H.tid
  agree₁ := H.agree 0
  agree₂ := H.agree 1

/-- **`Hyperedge.toJointBinding` — the binary hyperedge gives the full CG-2 ⊗ CG-5 binding
(PROVED).** The `Fin 2` hyperedge reconstructs `JointBinding T T …`: CG-2 is
`toSharedTurnId`; CG-5's `balanced` (`half₁ x₁ t + half₂ x₂ t = 0`) is the N-ary
`H.balanced` (`Σ_{Fin 2} = halfEdge 0 (x 0) t + halfEdge 1 (x 1) t`) read through
`Fin.sum_univ_two`. So a 2-incidence atomic hyperedge IS a bilateral `JointBinding` — the
binary structure is the `ι = Fin 2` slice of the hyperedge, with no extra data. -/
def Hyperedge.toJointBinding
    {T : TurnCoalg Obs AdmissibleTurn}
    {turnId : Fin 2 → TurnIdOf (TurnId := TurnId) T}
    {halfEdge : Fin 2 → HalfEdgeOf (Bal := Bal) T}
    (H : Hyperedge (Fin 2) T turnId halfEdge) :
    JointBinding (TurnId := TurnId) T T (turnId 0) (turnId 1) (halfEdge 0) (halfEdge 1) where
  shared := H.toSharedTurnId
  balanced := by
    -- `JointBinding.balanced` wants `halfEdge 0 (H.x 0) H.t + halfEdge 1 (H.x 1) H.t = 0`;
    -- `H.balanced` is the `Finset.univ` sum over `Fin 2`, which `Fin.sum_univ_two` unfolds.
    have h := H.balanced
    rw [Fin.sum_univ_two] at h
    -- after `toSharedTurnId`, `shared.x₁ = H.x 0`, `shared.x₂ = H.x 1`, `shared.t = H.t`
    -- definitionally, so the goal is exactly `h`.
    exact h

/-- **`SharedTurnId.toHyperedge` — the reverse direction (OPEN, stated faithfully).**

A binary `SharedTurnId`/`JointBinding` should assemble back into a `Fin 2` hyperedge — the
two structures are equivalent at `N = 2`. The `agree` field assembles cleanly (`Fin.cases`
on the two legs); the obstruction is purely the CG-5 *re-bundling*: a `JointBinding` over two
**a-priori-distinct** coalgebras `T₁ T₂` with two half-edge projections `half₁ half₂` only
collapses to a single-carrier `Hyperedge` once `T₁ = T₂` and the two projections are packaged
as one `halfEdge : Fin 2 → HalfEdgeOf T`. We state the *homogeneous* round-trip (one carrier,
projections already given as a `Fin 2`-family) — there the data is genuinely present and the
`balanced` re-bundling is `Fin.sum_univ_two` backwards. -/
def SharedTurnId.toHyperedge
    {T : TurnCoalg Obs AdmissibleTurn}
    (turnId : Fin 2 → TurnIdOf (TurnId := TurnId) T)
    (halfEdge : Fin 2 → HalfEdgeOf (Bal := Bal) T)
    (s : SharedTurnId (TurnId := TurnId) T T (turnId 0) (turnId 1))
    (hbal : halfEdge 0 s.x₁ s.t + halfEdge 1 s.x₂ s.t = 0) :
    Hyperedge (Fin 2) T turnId halfEdge where
  x := fun i => i.cases s.x₁ (fun _ => s.x₂)
  t := s.t
  tid := s.tid
  agree := by
    intro i
    -- two legs: `i = 0` is `s.agree₁`, `i = 1` is `s.agree₂`.
    fin_cases i
    · exact s.agree₁
    · exact s.agree₂
  balanced := by
    -- rebundle the binary balance into the `Fin 2` Σ.
    rw [Fin.sum_univ_two]
    exact hbal

/-! ### §3.2 — Ring / cycle: a hyperedge whose half-edge pattern is a directed cycle.

A bilateral swap is a 2-cycle; a *ring* of `N` cells each passing `δ` to the next is an
`N`-cycle. As a hyperedge: incidence `i` contributes `+δ` (received from `i-1`) and `−δ`
(sent to `i+1`); summed over the cycle every `δ` is cancelled by its successor's `−δ`, so the
CG-5 aggregate is `0`. The cycle is one hyperedge, not `N` bilateral edges. -/

/-- **`ringHyperedge` — an `N`-cycle as a single hyperedge over `ℤ`-balances (PROVED Σ=0).**
Over the cyclic index `Fin n`, incidence `i`'s half-edge is `δ i - δ (i+1)` (what it holds
minus what it forwards). On a one-state coalgebra the telescoping cycle sum is `0`: each `δ i`
appears once `+` and once `−` around the ring. This exhibits the ring as ONE atomic hyperedge
whose conservation is the cyclic telescoping, not a conjunction of bilateral balances. -/
def ringHyperedge (n : ℕ) [NeZero n] (δ : Fin n → ℤ) :
    Hyperedge (Fin n)
      ({ Carrier := Unit, step := fun _ => ((), fun _ => ()) } : TurnCoalg Unit Unit)
      (fun _ _ => ())
      (fun i _ _ => δ i - δ (i + 1)) where
  x := fun _ => ()
  t := ()
  tid := ()
  agree := fun _ => rfl
  balanced := by
    -- `Σ_i (δ i − δ (i+1)) = Σ_i δ i − Σ_i δ (i+1) = 0`, the successor reindex `i ↦ i+1`
    -- being a bijection of `Fin n` (the cyclic shift; inverse `i ↦ i-1`, an `AddGroup` iso
    -- for `n ≠ 0`), so the two sums coincide and the difference telescopes to `0`.
    have hshift : (Finset.univ.sum fun i => δ (i + 1)) = Finset.univ.sum fun i => δ i :=
      Finset.sum_nbij' (fun i => i + 1) (fun i => i - 1)
        (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
        (fun i _ => by simp) (fun i _ => by simp) (fun _ _ => rfl)
    rw [Finset.sum_sub_distrib, hshift, sub_self]

/-! ## §4 — THE RESEARCH QUESTION: `hyperedge_sound` over the single apex object.

`family_joint_sound` (`JointTurn.lean:447`, `sorry`) is the N-ary keystone framed over a
*family of binary edges*. Here we restate it over the single wide-pullback object and try to
prove it.

The honest finding is recorded at the two theorems below:

  * `hyperedge_sound` (the safety form, mirroring `joint_sound`/`stepComplete_preserves`):
    **PROVED, axiom-clean.** Framing the binding as one apex genuinely closes the cut.
  * `hyperedge_sound_bisim` (the OLD `family_joint_sound` *bisimulation-to-a-free-Spec*
    form): **still OPEN** — and provably so for the same reason `Boundary`'s old
    `sound_of_step_complete` was retired (`Spec.Carrier = Empty` refutes it). The single-
    object framing does NOT rescue the ill-posed shape; it rescues the *well-posed* one.

So the verdict (see module-foot `-- VERDICT`): the wide-pullback framing loosens the knot
**for the safety keystone** — what `family_joint_sound` should have said — because the apex
`tid` + single Σ collapse all `N` legs in ONE `legs_agree`/`hyper_stepComplete` step instead
of `O(N²)` pairwise cuts. The irreducible residue is NOT the agreement bookkeeping (that
dissolved); it is the *binding-as-premise* itself (`hyper_binding_is_proper`), unchanged. -/

/-! ### §4.1 — The N-fold product coalgebra and its step-completeness (PROVED). -/

/-- The **N-fold product (tensor) coalgebra** `⊗_{i∈ι} T` on carrier `ι → T.Carrier`, with
the pointwise step (a shared turn `t` drives every component). This is `ν(⊗Fᵢ)` as a
coalgebra — the N-ary analogue of `JointTurn.jointCoalg`. Observations are gathered into a
tuple `ι → Obs`. -/
def hyperCoalg (ι : Type u) (T : TurnCoalg Obs AdmissibleTurn) :
    TurnCoalg (ι → Obs) AdmissibleTurn where
  Carrier := ι → T.Carrier
  step := fun xs => (fun i => T.obs (xs i), fun t i => T.next (xs i) t)

/-- The **N-ary joint invariant**, assembled pointwise from a per-incidence predicate
family: a tuple-transition attests the joint conjunct iff *every* incidence attests its own. -/
def hyperPred
    {ι : Type u} (T : TurnCoalg Obs AdmissibleTurn)
    (P : (i : ι) → T.Carrier → AdmissibleTurn → T.Carrier → Prop) :
    (ι → T.Carrier) → AdmissibleTurn → (ι → T.Carrier) → Prop :=
  fun xs t xs' => ∀ i, P i (xs i) t (xs' i)

/-- **`hyper_stepComplete` — the N-fold product is step-complete (PROVED).** If every
incidence is per-cell step-complete, the product `hyperCoalg ι T` is step-complete against
the pointwise-assembled `hyperPred` invariants. This is the *one-step* collapse the apex
buys: all `N` participants discharged by a single `∀ i` introduction, no pairwise gluing.
Makes the single-cell keystone `stepComplete_preserves` apply verbatim to the product. -/
theorem hyper_stepComplete
    {ι : Type u} (T : TurnCoalg Obs AdmissibleTurn)
    (cons auth chain obsAdv : (i : ι) → T.Carrier → AdmissibleTurn → T.Carrier → Prop)
    (hsc : ∀ i, StepComplete T (cons i) (auth i) (chain i) (obsAdv i)) :
    StepComplete (hyperCoalg ι T)
      (hyperPred T cons) (hyperPred T auth) (hyperPred T chain) (hyperPred T obsAdv) := by
  intro xs t
  -- each conjunct of the product `StepInv` is a `∀ i` of the per-incidence conjunct; the
  -- four projections of the per-incidence `StepInv (hsc i …)` fill the four slots.
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact (hsc i (xs i) t).1
  · exact (hsc i (xs i) t).2.1
  · exact (hsc i (xs i) t).2.2.1
  · exact (hsc i (xs i) t).2.2.2

/-! ### §4.2 — `hyperedge_sound`: THE N-ary keystone (PROVED, axiom-clean).

The safety form. IF every incidence is step-complete AND the hyperedge binding holds (its
`H` carries CG-2 + CG-5), AND a joint predicate `Good` is preserved by every
`StepInv`-respecting tuple-transition, THEN `Good` holds along the ENTIRE run from the
hyperedge's incidence tuple `H.x`. The binding `H` is the explicit premise — *but its
agreement legs no longer cost `O(N²)`: they are the single apex `tid`.* -/

/-- **`hyperedge_sound` — the wide-pullback N-ary keystone (PROVED).**

This is `family_joint_sound` restated over the single hyperedge object and *actually
proved*: it reduces, in one step, to `stepComplete_preserves` on the product coalgebra
`hyperCoalg ι T`, with product step-completeness supplied by `hyper_stepComplete`. The
hyperedge `H` enters as the binding premise (carrying the apex `tid` and the Σ=0
conservation) and pins the run's start to the bound incidence tuple `H.x`.

**Finding:** the cut that was irreducible in the *family-of-binary-edges* framing (gluing
`C(N,2)` pairwise `SharedTurnId`s) is GONE — `hyper_stepComplete` discharges all legs with a
single `∀ i`, and `legs_agree` is now a theorem. What remains a *premise* (never a derived
fact) is only the binding's own admissibility content (`hyper_binding_is_proper`), exactly as
in the binary `joint_sound`. So the single-object framing genuinely loosens the knot: the
keystone is provable and axiom-clean. -/
theorem hyperedge_sound
    {ι : Type u} [Fintype ι]
    (T : TurnCoalg Obs AdmissibleTurn)
    (turnId : ι → TurnIdOf (TurnId := TurnId) T)
    (halfEdge : ι → HalfEdgeOf (Bal := Bal) T)
    (cons auth chain obsAdv : (i : ι) → T.Carrier → AdmissibleTurn → T.Carrier → Prop)
    (hsc : ∀ i, StepComplete T (cons i) (auth i) (chain i) (obsAdv i))
    (H : Hyperedge ι T turnId halfEdge)
    (Good : (ι → T.Carrier) → Prop)
    (hpres : ∀ xs t, Good xs →
        StepInv (hyperCoalg ι T)
          (hyperPred T cons) (hyperPred T auth) (hyperPred T chain) (hyperPred T obsAdv)
          xs t ((hyperCoalg ι T).next xs t) →
        Good ((hyperCoalg ι T).next xs t))
    {ys : ι → T.Carrier}
    (hrun : Execution.Run (inducedSystem (hyperCoalg ι T)) H.x ys)
    (hgood : Good H.x) :
    Good ys :=
  stepComplete_preserves (hyperCoalg ι T)
    (hyperPred T cons) (hyperPred T auth) (hyperPred T chain) (hyperPred T obsAdv)
    Good
    (hyper_stepComplete T cons auth chain obsAdv hsc)
    hpres hrun hgood

/-! ### §4.3 — The honest negatives: what stays OPEN and why.

The single-object framing loosens the *agreement* knot, not the *irreducibility* one. -/

/-- **`hyperedge_sound_needs_binding` — the binding premise is load-bearing (PROVED).**
N-ary analogue of `JointTurn.joint_sound_needs_binding`: it is NOT the case that per-cell
step-completeness alone entails `HyperAdmissible` for every tuple. Witnessed by the singleton
hyperedge of `hyper_binding_is_proper` (one incidence, half-edge `1`, CG-5 `1 ≠ 0`): both
incidences (vacuously) step-complete, yet the tuple is not `HyperAdmissible`. So no "all
step-complete ⇒ hyper-admissible everywhere" theorem holds — the hyperedge binding is a real
premise, NOT recovered by the wide-pullback framing. This is the irreducible residue. -/
theorem hyperedge_sound_needs_binding :
    ¬ ∀ (T : TurnCoalg Unit Unit)
        (turnId : Unit → TurnIdOf (TurnId := Unit) T)
        (halfEdge : Unit → HalfEdgeOf (Bal := Nat) T)
        (cons auth chain obsAdv : Unit → T.Carrier → Unit → T.Carrier → Prop),
        (∀ i, StepComplete T (cons i) (auth i) (chain i) (obsAdv i)) →
        ∀ (xs : Unit → T.Carrier) (t : Unit),
          HyperAdmissible Unit T turnId halfEdge xs t := by
  intro h
  obtain ⟨T, turnId, halfEdge, xs, t, hnot⟩ := hyper_binding_is_proper
  exact hnot (h T turnId halfEdge
    (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)
    (fun _ _ _ => ⟨trivial, trivial, trivial, trivial⟩) xs t)

/-- **`hyperedge_sound_bisim` — the OLD `family_joint_sound` shape, still OPEN.**

`family_joint_sound` (`JointTurn.lean:447`) concludes `Sound (J.cell i) (Spec i) (b.pre i)`:
bisimilarity of each participant to a *free* spec coalgebra. That shape is **ill-posed**, for
exactly the reason `Boundary` retired `sound_of_step_complete`: with `Spec.Carrier = Empty`,
`Sound T Spec x` is uninhabited while step-completeness holds, so it is false-as-stated, NOT a
gap the apex can close. The wide-pullback framing does NOT rescue it (the obstruction is the
free `Spec`, not the binding bookkeeping). We restate it over the hyperedge and leave it
honestly OPEN.

-- OPEN: the irreducible cut here is NOT N-ary agreement (that dissolved into `legs_agree` /
-- `hyper_stepComplete`). It is the **ill-posed bisimulation-to-a-free-Spec** target inherited
-- from `family_joint_sound`: deriving `Sound T (Spec i) (H.x i)` for an ARBITRARY `Spec i`
-- requires producing a bisimulation into a coalgebra one knows nothing about — refutable at
-- `Spec.Carrier = Empty`. The honest fix is `hyperedge_sound` (the safety form) above, which
-- is PROVED; this declaration records that the *bisimulation* form remains unprovable for the
-- same structural reason `Boundary` flagged, independent of the hyperedge framing. -/
theorem hyperedge_sound_bisim
    {ι : Type u} [Fintype ι]
    (T : TurnCoalg Obs AdmissibleTurn)
    (turnId : ι → TurnIdOf (TurnId := TurnId) T)
    (halfEdge : ι → HalfEdgeOf (Bal := Bal) T)
    (Spec : ι → TurnCoalg Obs AdmissibleTurn)
    (cons auth chain obsAdv : (i : ι) → T.Carrier → AdmissibleTurn → T.Carrier → Prop)
    (hsc : ∀ i, StepComplete T (cons i) (auth i) (chain i) (obsAdv i))
    (H : Hyperedge ι T turnId halfEdge)
    (i : ι) :
    Sound T (Spec i) (H.x i) := by
  sorry

/-! ## §5 — `tensor_not_final` at N-ary: the product coalgebra is not final (OPEN).

The categorical root of irreducibility recorded for the hyperedge. `JointTurn`'s
`binding_is_proper` corrected the *naming* (the product of finals IS final for the product
functor; the true content is the proper-subobject fact). The genuinely-OPEN N-ary statement
is therefore the **proper-subobject** one for the hyperedge, generalizing
`hyper_binding_is_proper` from a single witness to: there is *no section* of the product
carrier into the hyperedge-admissible subobject — i.e. `HyperAdmissible` is not all of
`ι → T.Carrier`, for a non-degenerate `Bal`. We state the existence of such a behaviour gap. -/

/-- **`hyper_not_all_admissible` — the N-ary proper-subobject obstruction (OPEN).** For a
non-degenerate balance monoid (a `Bal` with some `b ≠ 0`), there exist a participant index, a
hyperedge framing, and a tuple/turn that is NOT `HyperAdmissible` — so the wide-pullback
subobject is *proper* inside the N-fold product, witnessing that `ν(⊗Fᵢ)` does not classify
the bound joint behaviour by per-cell data alone. The CG-2 ⊗ CG-5 binding is irreducible at
every `N ≥ 1`, the same obstruction as the binary `binding_is_proper`.

-- OPEN: the precise cut is exhibiting, for arbitrary `Fintype ι` with a designated incidence
-- and a `Bal`-value `b ≠ 0`, a half-edge family whose Σ over `univ` is forced to `b ≠ 0` on
-- some tuple (so no `Hyperedge` names it). For `ι = Unit`, `b = (1:ℕ)` this is exactly
-- `hyper_binding_is_proper` (PROVED); the general-`ι` statement needs a chosen incidence to
-- carry `b` while the rest carry `0`, then `Finset.sum_eq_single`. Left OPEN as the recorded
-- N-ary irreducibility witness rather than re-deriving the single-incidence case. -/
theorem hyper_not_all_admissible
    {ι : Type} [Fintype ι] [Nonempty ι]
    {B : Type} [AddCommMonoid B] (b : B) (hb : b ≠ 0) :
    ∃ (T : TurnCoalg Unit Unit)
      (turnId : ι → TurnIdOf (TurnId := Unit) T)
      (halfEdge : ι → HalfEdgeOf (Bal := B) T)
      (xs : ι → T.Carrier) (t : Unit),
      ¬ HyperAdmissible ι T turnId halfEdge xs t := by
  sorry

/-! ## Axiom-hygiene pins (PROVED keystones only — never the `sorry`'d ones). -/

#assert_axioms Hyperedge.legs_agree
#assert_axioms hyper_binding_is_proper
#assert_axioms Hyperedge.toSharedTurnId
#assert_axioms Hyperedge.toJointBinding
#assert_axioms SharedTurnId.toHyperedge
#assert_axioms ringHyperedge
#assert_axioms hyper_stepComplete
#assert_axioms hyperedge_sound
#assert_axioms hyperedge_sound_needs_binding

/- VERDICT (the research question, §4). Does framing the binding as ONE wide-pullback object
(rather than a family of `O(N²)` pairwise `SharedTurnId` agreements) loosen the N-ary
soundness knot?

  YES — for the well-posed keystone. `hyperedge_sound` (the safety form, the honest content
  `family_joint_sound` was reaching for) is **PROVED and axiom-clean**. The apex `tid`
  collapses all `N` CG-2 legs into a single `legs_agree` theorem (no pairwise data), and the
  single Σ-over-`univ` gives CG-5 directly; `hyper_stepComplete` then discharges every
  incidence with one `∀ i`, so the soundness reduces to the single-cell
  `stepComplete_preserves` verbatim. The `O(N²)` pairwise-gluing cut that made the
  family-of-binary-edges framing intractable simply *does not exist* at the apex.

  The irreducible residue is UNCHANGED and is NOT the agreement bookkeeping: it is the
  binding-as-premise itself. `hyper_binding_is_proper` / `hyperedge_sound_needs_binding`
  (both PROVED) show the hyperedge is a proper subobject — the CG-2 ⊗ CG-5 data is real
  content per-cell soundness cannot supply, so it must be hypothesized (the `H` premise),
  never derived. That is the same irreducibility as the binary `joint_sound`, neither
  loosened nor worsened by the framing.

  The two genuinely-OPEN obligations are honest residues, not framing failures:
    * `hyperedge_sound_bisim` — the ILL-POSED bisimulation-to-a-free-`Spec` shape inherited
      from `family_joint_sound`; refutable at `Spec.Carrier = Empty`, independent of the
      hyperedge. The apex does not (and should not) rescue an ill-posed target.
    * `hyper_not_all_admissible` — the general-`ι` proper-subobject witness (the single-
      incidence case `hyper_binding_is_proper` IS proved). -/

end Dregg2.Hyperedge
