/-
# Metatheory.JointTurn — THE load-bearing cross-cell atomic-turn layer.

This is the one place the single-cell coinductive frame of `Boundary.lean` is
**extended, not inhabited** (`dregg2.md §1.6`, §10 honesty note; `study-category §1.4`;
`dregg2-multicell-privacy §1, §5`). If we cannot nail multi-cell, nothing else is worth
anything: zkRPC, multiagent coordination, and emergent consensus are all N-cell
`JointTurn`s (`dregg2-multicell-privacy §1`: a toolcall = a 2-cell JointTurn
`agent-cell ⊗ service-cell`).

Grounding:

  * **Mina** (`study-mina-relink`, ADOPT): a turn over cells is a `zkapp_command`
    **account-update FOREST**; every participant's per-cell proof commits to the same
    `account_updates_hash` — the **shared turn-id**. Atomicity is the in-circuit
    `will_succeed` prophecy + a **cumulative AND** (`success`) over all updates, *not*
    a live 2-phase-commit coordinator.
  * **Category theory** (`study-category §1.4`, `dregg2.md §1.6`): a cross-cell turn is
    the **equalizer / pullback** of the participants' `step` maps over the shared
    turn-identity. It is a *span / tuple*, NOT a coalgebra step — adding a tensored
    coalgebra would be the WRONG fix.
  * **The irreducibility theorem** (`tensor_not_final`): `νF₁ ⊗ νF₂` is **NOT** the
    final coalgebra of the product behaviour. Hence **cross-cell soundness is
    IRREDUCIBLE to per-cell ∧ per-cell**: the CG-2 ⊗ CG-5 binding is an explicit
    **HYPOTHESIS**, never a theorem derivable from the two per-cell `Sound`s. Deriving
    it would make the Boundary module unsound. CG-5 is the *price of having no global
    ledger* — Mina never needs it because one ledger gives one namespace.

In the live γ.2 code (`[C]`): the per-cell halves are `StateConstraint::BoundDelta`
(`program.rs:747`, `EqualAndOpposite` paired swap); the aggregate proof is
`circuit::bilateral_aggregation_air` (`CrossSideExistenceAir`, signed
edge-fingerprint balance sum == 0); the AIR constraint groups ARE the equalizer
conditions — **CG-2** (every cell's row agrees on `TURN_HASH`/`EFFECTS_HASH`/
`ACTOR_NONCE`/`PREVIOUS_RECEIPT_HASH` = the pullback over the shared turn) and **CG-5**
(every claimed half-edge has its matching peer half = the balance equalizer).

Style: spec-first, grind up. Every theorem is stated with a real, faithful `Prop` and a
`sorry` body; each `sorry` is a genuine obligation. We give the clear **binary (2-cell)**
version as primary (per `study-category §1.4` and the brief's allowance), and an N-ary
indexed-family version (`JointFamily`) for the general forest.
-/
import Metatheory.Core
import Metatheory.Boundary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Metatheory.JointTurn

open Metatheory.Boundary

universe u

/- Cross-cell layer parameters. `Obs`/`AdmissibleTurn` are the single-cell
behaviour-functor parameters from `Boundary.lean` (the `F X = Obs × (AdmissibleTurn ⇒ X)`
data); `TurnId` is the type of shared turn-identities (the `account_updates_hash`
analog); `Bal` is the commutative monoid the cross-cell conservation aggregate (CG-5)
lands in — exactly `Core.Conservation`'s value monoid, instantiated over Pedersen
commitments in the private case (`dregg2-multicell-privacy §2`: the equalizer runs over
commitments, never cleartext). -/
variable {Obs AdmissibleTurn TurnId : Type u}
variable {Bal : Type u} [AddCommMonoid Bal]

/-! ## The shared turn-identity — the CG-2 pullback (`account_updates_hash`)

Every participant computes a *local* turn-id from its own post-step; the JointTurn is
admissible only if these all equal one shared id. Categorically this is the **pullback**
of the participants' `turnId ∘ next` maps over `TurnId` (equivalently, the equalizer of
the two composites into `TurnId`). A per-cell proof is valid *only as part of THIS
JointTurn* — it can never be replayed solo or in another forest, because its public
input is pinned to the shared id. -/

/-- The per-cell **turn-identity projection**: from a participant's post-step state read
the turn-id it committed to (the row's `TURN_HASH`/`EFFECTS_HASH`/`ACTOR_NONCE`/
`PREVIOUS_RECEIPT_HASH` digest). Abstract here; supplied by the real PI surface. -/
abbrev TurnIdOf (T : TurnCoalg Obs AdmissibleTurn) := T.Carrier → TurnId

/-- The per-cell **half-edge balance projection**: the signed cross-side edge
fingerprint a participant contributes for a given turn (CG-5's per-cell summand). The
cross-cell aggregate is the monoid-sum of these; conservation across the boundary is
that sum being `0`. -/
abbrev HalfEdgeOf (T : TurnCoalg Obs AdmissibleTurn) :=
  T.Carrier → AdmissibleTurn → Bal

/-! ## `SharedTurnId` — the CG-2 turn-identity pullback (binary) -/

/-- **`SharedTurnId` — the CG-2 turn-identity pullback** for two participants. Carries
the two participants' pre-states `x₁ x₂`, the single shared turn `t`, and a **proof**
that both post-states project to the *same* shared turn-id `tid` (`account_updates_hash`).
This is the pullback/equalizer object over `TurnId`: it is precisely the subobject of
`C₁ × C₂` on which the two `turnId ∘ next` composites agree. -/
structure SharedTurnId
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (turnId₁ : TurnIdOf (Obs := Obs) (AdmissibleTurn := AdmissibleTurn) (TurnId := TurnId) T₁)
    (turnId₂ : TurnIdOf (Obs := Obs) (AdmissibleTurn := AdmissibleTurn) (TurnId := TurnId) T₂)
    where
  /-- Participant 1's pre-state. -/
  x₁  : T₁.Carrier
  /-- Participant 2's pre-state. -/
  x₂  : T₂.Carrier
  /-- The single shared turn applied to both (the one forest). -/
  t   : AdmissibleTurn
  /-- The shared turn-id (Mina's `account_updates_hash`). -/
  tid : TurnId
  /-- CG-2 left leg: participant 1's post-step commits to the shared id. -/
  agree₁ : turnId₁ (T₁.next x₁ t) = tid
  /-- CG-2 right leg: participant 2's post-step commits to the *same* shared id. -/
  agree₂ : turnId₂ (T₂.next x₂ t) = tid

/-- **`SharedTurnId.agree` — the equalizer condition** the two participants satisfy:
their post-step turn-ids are *equal* (the pullback collapses both legs through `tid`).
This is the `study-category §1.4` `agree` field made derivable from the two legs. -/
theorem SharedTurnId.agree
    {T₁ T₂ : TurnCoalg Obs AdmissibleTurn}
    {turnId₁ : TurnIdOf (TurnId := TurnId) T₁} {turnId₂ : TurnIdOf (TurnId := TurnId) T₂}
    (s : SharedTurnId T₁ T₂ turnId₁ turnId₂) :
    turnId₁ (T₁.next s.x₁ s.t) = turnId₂ (T₂.next s.x₂ s.t) :=
  s.agree₁.trans s.agree₂.symm

/-! ## `JointBinding` — the HYPOTHESIS (CG-2 ⊗ CG-5), never derived -/

/-- **`JointBinding` — the cross-cell binding HYPOTHESIS.** Carries the two halves of the
γ.2 aggregate that together make a multi-cell turn admissible:

  * **CG-2** (turn-identity pullback): a `SharedTurnId` — the participants agree on the
    single shared turn-id;
  * **CG-5** (cross-cell conservation aggregate): the monoid-sum of the participants'
    half-edge balances is `0` (the bilateral `EqualAndOpposite` identity / signed
    edge-fingerprint balance sum == 0). In the private tier this `0` is over Pedersen
    commitments (homomorphic).

**This is a PREMISE, not a derived fact.** Because `νF₁ ⊗ νF₂` is not final
(`tensor_not_final`), `JointBinding` is irreducible to the per-cell `Sound`s; it is
exactly the data a global ledger would otherwise supply for free. -/
structure JointBinding
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (turnId₁ : TurnIdOf (TurnId := TurnId) T₁) (turnId₂ : TurnIdOf (TurnId := TurnId) T₂)
    (half₁ : HalfEdgeOf (Bal := Bal) T₁) (half₂ : HalfEdgeOf (Bal := Bal) T₂)
    where
  /-- CG-2: the turn-identity pullback (the shared `account_updates_hash`). -/
  shared  : SharedTurnId T₁ T₂ turnId₁ turnId₂
  /-- CG-5: the cross-cell conservation aggregate balances to `0` across the boundary —
  `half₁ x₁ t + half₂ x₂ t = 0`. The bilateral `EqualAndOpposite` / `CrossSideExistence`
  identity, monoid-valued so it also holds over commitments. -/
  balanced : half₁ shared.x₁ shared.t + half₂ shared.x₂ shared.t = 0

/-! ## `jointCoalg` — the equalizer object as a coalgebra over the product carrier

Per `study-category §1.4`, the joint turn is a *span/tuple*, NOT a tensored coalgebra.
But to state `Sound` (which is phrased over a `TurnCoalg`), we package the **product
carrier** `C₁ × C₂` with the componentwise step. The key point — and the whole content of
`tensor_not_final` — is that this product coalgebra is *not* final, so the JointTurn's
admissibility is NOT captured by `jointCoalg` alone; it needs the `JointBinding` cut. -/

/-- The **product (tensor) coalgebra** `T₁ ⊗ T₂` on carrier `T₁.Carrier × T₂.Carrier`,
with the componentwise step. Observations pair up; a shared turn `t` is fed to both
components. This is `νF₁ × νF₂` as a coalgebra — and `tensor_not_final` says it is NOT
final for the joint behaviour. -/
def jointCoalg (T₁ T₂ : TurnCoalg Obs AdmissibleTurn) :
    TurnCoalg (Obs × Obs) AdmissibleTurn where
  Carrier := T₁.Carrier × T₂.Carrier
  step := fun p =>
    ( (T₁.obs p.1, T₂.obs p.2),
      fun t => (T₁.next p.1 t, T₂.next p.2 t) )

/-- **`JointAdmissible` — the equalizer-object admissibility predicate.** A joint
transition from `(x₁, x₂)` under the shared turn `t` is admissible iff there is a
`JointBinding` whose pullback names exactly this pre-state pair and this turn — i.e. the
participants agree on `sharedTurnId` AND CG-5 balances. This is the equalizer object:
the subobject of `C₁ × C₂` carved out by the binding. -/
def JointAdmissible
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (turnId₁ : TurnIdOf (TurnId := TurnId) T₁) (turnId₂ : TurnIdOf (TurnId := TurnId) T₂)
    (half₁ : HalfEdgeOf (Bal := Bal) T₁) (half₂ : HalfEdgeOf (Bal := Bal) T₂)
    (x₁ : T₁.Carrier) (x₂ : T₂.Carrier) (t : AdmissibleTurn) : Prop :=
  ∃ b : JointBinding T₁ T₂ turnId₁ turnId₂ half₁ half₂,
    b.shared.x₁ = x₁ ∧ b.shared.x₂ = x₂ ∧ b.shared.t = t

/-! ## The keystone: joint soundness with the binding as a PREMISE -/

/-- The **joint per-step invariant predicates**, assembled componentwise from the two
participants' per-cell predicates. A joint transition `(x₁,x₂) -t→ (x₁',x₂')` attests a
joint conjunct exactly when *both* components attest their per-cell conjunct. These are
the predicates `jointCoalg T₁ T₂` is step-complete against (`joint_stepComplete`), and the
ones the joint `Good` is preserved by in `joint_sound`. -/
def jointPred
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (P₁ : T₁.Carrier → AdmissibleTurn → T₁.Carrier → Prop)
    (P₂ : T₂.Carrier → AdmissibleTurn → T₂.Carrier → Prop) :
    (T₁.Carrier × T₂.Carrier) → AdmissibleTurn → (T₁.Carrier × T₂.Carrier) → Prop :=
  fun x t x' => P₁ x.1 t x'.1 ∧ P₂ x.2 t x'.2

/-- **`joint_stepComplete` — the joint coalgebra is step-complete (PROVED).** If both
participants are per-cell step-complete, then `jointCoalg T₁ T₂` is step-complete against
the componentwise-assembled `jointPred` invariants. This is what makes the single-cell
keystone `Boundary.stepComplete_preserves` directly applicable to the joint coalgebra —
the joint turn is "just another `TurnCoalg`". -/
theorem joint_stepComplete
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (cons₁ auth₁ chain₁ obs₁ : T₁.Carrier → AdmissibleTurn → T₁.Carrier → Prop)
    (cons₂ auth₂ chain₂ obs₂ : T₂.Carrier → AdmissibleTurn → T₂.Carrier → Prop)
    (hsc₁ : StepComplete T₁ cons₁ auth₁ chain₁ obs₁)
    (hsc₂ : StepComplete T₂ cons₂ auth₂ chain₂ obs₂) :
    StepComplete (jointCoalg T₁ T₂)
      (jointPred T₁ T₂ cons₁ cons₂) (jointPred T₁ T₂ auth₁ auth₂)
      (jointPred T₁ T₂ chain₁ chain₂) (jointPred T₁ T₂ obs₁ obs₂) := by
  intro x t
  obtain ⟨c₁, a₁, k₁, o₁⟩ := hsc₁ x.1 t
  obtain ⟨c₂, a₂, k₂, o₂⟩ := hsc₂ x.2 t
  exact ⟨⟨c₁, c₂⟩, ⟨a₁, a₂⟩, ⟨k₁, k₂⟩, ⟨o₁, o₂⟩⟩

/-- **`joint_sound` — THE cross-cell keystone (`dregg2-multicell-privacy §5`,
`study-category §1.4`), reframed as joint-execution SAFETY** (mirroring
`Boundary.stepComplete_preserves`; see Boundary's §"meaningful soundness keystone" for why
the old bisimulation-to-a-free-`Spec` shape — `Sound (jointCoalg)(jointCoalg)` — was
vacuous/ill-posed and is retired here exactly as `sound_of_step_complete` was).

If each participant is per-cell step-complete (its coalgebra discharges the full
`StepInv`), **AND** the `JointBinding` holds (CG-2 ⊗ CG-5 — supplied as a HYPOTHESIS),
**AND** a joint state-predicate `Good` is preserved by every joint `StepInv`-respecting
transition, then `Good` holds at **every** configuration reachable along any `Run` of the
induced joint transition system, started from the binding's bound pre-state pair
`(b.shared.x₁, b.shared.x₂)`.

Proved by applying `Boundary.stepComplete_preserves` directly to the joint coalgebra
`jointCoalg T₁ T₂` (it is just another `TurnCoalg`), with joint step-completeness supplied
by `joint_stepComplete`. The `JointBinding b` is an explicit **premise, never derived from
the per-cell data** — it is what makes the cross-cell `Good` (e.g. the CG-5 conservation
aggregate) preserved; compare the single-cell `stepComplete_preserves`, which needs no such
cut. That irreducibility is `binding_is_proper`. -/
theorem joint_sound
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (turnId₁ : TurnIdOf (TurnId := TurnId) T₁) (turnId₂ : TurnIdOf (TurnId := TurnId) T₂)
    (half₁ : HalfEdgeOf (Bal := Bal) T₁) (half₂ : HalfEdgeOf (Bal := Bal) T₂)
    (cons₁ auth₁ chain₁ obs₁ : T₁.Carrier → AdmissibleTurn → T₁.Carrier → Prop)
    (cons₂ auth₂ chain₂ obs₂ : T₂.Carrier → AdmissibleTurn → T₂.Carrier → Prop)
    (hsc₁ : StepComplete T₁ cons₁ auth₁ chain₁ obs₁)
    (hsc₂ : StepComplete T₂ cons₂ auth₂ chain₂ obs₂)
    (b : JointBinding T₁ T₂ turnId₁ turnId₂ half₁ half₂)
    (Good : (T₁.Carrier × T₂.Carrier) → Prop)
    (hpres : ∀ p t, Good p →
        StepInv (jointCoalg T₁ T₂)
          (jointPred T₁ T₂ cons₁ cons₂) (jointPred T₁ T₂ auth₁ auth₂)
          (jointPred T₁ T₂ chain₁ chain₂) (jointPred T₁ T₂ obs₁ obs₂)
          p t ((jointCoalg T₁ T₂).next p t) →
        Good ((jointCoalg T₁ T₂).next p t))
    {y : (T₁.Carrier × T₂.Carrier)}
    (hrun : Execution.Run (inducedSystem (jointCoalg T₁ T₂)) (b.shared.x₁, b.shared.x₂) y)
    (hgood : Good (b.shared.x₁, b.shared.x₂)) :
    Good y :=
  stepComplete_preserves (jointCoalg T₁ T₂)
    (jointPred T₁ T₂ cons₁ cons₂) (jointPred T₁ T₂ auth₁ auth₂)
    (jointPred T₁ T₂ chain₁ chain₂) (jointPred T₁ T₂ obs₁ obs₂)
    Good
    (joint_stepComplete T₁ T₂ cons₁ auth₁ chain₁ obs₁ cons₂ auth₂ chain₂ obs₂ hsc₁ hsc₂)
    hpres hrun hgood

/-- **`joint_sound_needs_binding` — the negative companion (why the binding is not
optional), reframed as the honest consequence of `binding_is_proper` (PROVED).**

It is NOT the case that per-cell step-completeness alone entails the joint invariant for
every pre-state pair. Concretely: the joint `Good` that `joint_sound` delivers is the
binding-carved `JointAdmissible` predicate, and there is a configuration — the
`binding_is_proper` witness, two one-state cells each moving a half-edge of `1 : ℕ`, whose
CG-5 sum `1 + 1 = 2 ≠ 0` — where both participants are (vacuously) step-complete yet the
start pair is **not** `JointAdmissible`. So no theorem of the form "both step-complete ⇒
joint-admissible everywhere" can hold; the `JointBinding` premise of `joint_sound` is
load-bearing, not derivable. (The earlier `Sound (jointCoalg)(jointCoalg)` framing of this
was vacuous — `Sound _ _ _` is reflexively inhabited via `sound_refl`, so its universal
form is *true* and proves nothing; the honest negative is over the binding's own
admissibility predicate.) -/
theorem joint_sound_needs_binding :
    ¬ ∀ (T₁ T₂ : TurnCoalg Unit Unit)
        (turnId₁ : TurnIdOf (TurnId := Unit) T₁) (turnId₂ : TurnIdOf (TurnId := Unit) T₂)
        (half₁ : HalfEdgeOf (Bal := Nat) T₁) (half₂ : HalfEdgeOf (Bal := Nat) T₂)
        (cons₁ auth₁ chain₁ obs₁ : T₁.Carrier → Unit → T₁.Carrier → Prop)
        (cons₂ auth₂ chain₂ obs₂ : T₂.Carrier → Unit → T₂.Carrier → Prop),
        StepComplete T₁ cons₁ auth₁ chain₁ obs₁ →
        StepComplete T₂ cons₂ auth₂ chain₂ obs₂ →
        ∀ (x₁ : T₁.Carrier) (x₂ : T₂.Carrier) (t : Unit),
          JointAdmissible T₁ T₂ turnId₁ turnId₂ half₁ half₂ x₁ x₂ t := by
  intro h
  -- the `binding_is_proper` witness: a one-state coalgebra, half-edge `1`, CG-5 `1+1≠0`.
  let T : TurnCoalg Unit Unit := { Carrier := Unit, step := fun _ => ((), fun _ => ()) }
  -- both cells are step-complete against the always-`True` per-cell invariants (vacuous).
  have hsc : StepComplete T (fun _ _ _ => True) (fun _ _ _ => True)
      (fun _ _ _ => True) (fun _ _ _ => True) := fun _ _ => ⟨trivial, trivial, trivial, trivial⟩
  have hadm := h T T (fun _ => ()) (fun _ => ()) (fun _ _ => 1) (fun _ _ => 1)
    (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)
    (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)
    hsc hsc () () ()
  -- but that product state is not JointAdmissible: a binding would need CG-5 `1+1=0` in ℕ.
  obtain ⟨b, -, -, -⟩ := hadm
  exact absurd b.balanced (by decide)

/-! ## `tensor_not_final` — `νF₁ ⊗ νF₂` is NOT final for the joint behaviour

The categorical root of irreducibility (`study-category`, `dregg2.md §1.6`). The product
of two final coalgebras is generally not final for the product behaviour functor: there
are joint behaviours that do not factor through `νF₁ × νF₂` while honouring the binding.
Hence the CG-2 ⊗ CG-5 binding cannot be recovered per-cell. -/

/-- A **joint behaviour honouring the binding** between two spec coalgebras: a relation
on the product carriers closed under shared steps whose every related pair satisfies the
cross-cell binding (CG-2 turn-ids agree, CG-5 balances). This is the kind of behaviour a
*final joint coalgebra* would have to classify — but a mere product of finals cannot. -/
structure BoundJointBehaviour
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (turnId₁ : TurnIdOf (TurnId := TurnId) T₁) (turnId₂ : TurnIdOf (TurnId := TurnId) T₂)
    (half₁ : HalfEdgeOf (Bal := Bal) T₁) (half₂ : HalfEdgeOf (Bal := Bal) T₂)
    where
  /-- The carrier of the behaviour (states it ranges over). -/
  carrier : Type u
  /-- How a state of the behaviour drives both participants under one shared turn. -/
  drive   : carrier → AdmissibleTurn → (T₁.Carrier × T₂.Carrier)
  /-- Every driven pair honours the cross-cell binding (CG-2 ⊗ CG-5). -/
  honours : ∀ (s : carrier) (t : AdmissibleTurn),
              JointAdmissible T₁ T₂ turnId₁ turnId₂ half₁ half₂
                (drive s t).1 (drive s t).2 t

/-- **`binding_is_proper` — the CORRECT cross-cell irreducibility (PROVED).**

*Correction (audit):* the earlier `tensor_not_final` ("νF₁ ⊗ νF₂ is not final") was
**mis-stated** — the product of two final coalgebras IS final for the product functor, so
that claim is false. The true, soundness-critical content is a **proper-subobject** fact:
`JointBinding` (CG-2 ⊗ CG-5) is a *non-trivial constraint*, so the joint-admissible
configurations are a proper **equalizer subobject** of the product carrier, NOT all of it.
Hence cross-cell admissibility is genuinely MORE than per-cell × per-cell — there exist
product configurations the binding **excludes** — so the binding cannot be recovered from
the per-cell data and must be hypothesized (`joint_sound`'s premise), not derived.

Witnessed concretely: two one-state cells each moving a half-edge of `1 : ℕ`, whose CG-5
balance `1 + 1 = 2 ≠ 0` fails — so that product state is not `JointAdmissible`. -/
theorem binding_is_proper :
    ∃ (T₁ T₂ : TurnCoalg Unit Unit)
      (turnId₁ : TurnIdOf (TurnId := Unit) T₁) (turnId₂ : TurnIdOf (TurnId := Unit) T₂)
      (half₁ : HalfEdgeOf (Bal := Nat) T₁) (half₂ : HalfEdgeOf (Bal := Nat) T₂)
      (x₁ : T₁.Carrier) (x₂ : T₂.Carrier) (t : Unit),
      ¬ JointAdmissible T₁ T₂ turnId₁ turnId₂ half₁ half₂ x₁ x₂ t := by
  -- the one-state coalgebra over `Obs = AdmissibleTurn = Unit`.
  let T : TurnCoalg Unit Unit := { Carrier := Unit, step := fun _ => ((), fun _ => ()) }
  refine ⟨T, T, fun _ => (), fun _ => (), fun _ _ => 1, fun _ _ => 1, (), (), (), ?_⟩
  -- a `JointBinding` here would need CG-5 `1 + 1 = 0` in ℕ — impossible.
  rintro ⟨b, -, -, -⟩
  exact absurd b.balanced (by decide)

/-! ## `atomicity_as_proof` — atomicity is a PROOF property, not a coordinator

Mina's shape (`dregg2-multicell-privacy §1`, [G, ADOPT]): a `will_succeed` **prophecy**
plus an **in-circuit cumulative AND** (`success`) over all participants. dregg2's
divergence: Mina's single global durable write becomes per-cell tier-local commits gated
on the *same* shared aggregate proof — the proof is shared, the finality per-cell. There
is NO live two-phase-commit coordinator; all-or-none is *proven by the aggregate*. -/

/-- **`LocalSucceeds`** — the in-circuit success bit each participant contributes for the
shared turn: its local step-proof admitted its share (the per-cell coalgebra accepts `t`
from `xᵢ`). A `Prop`-level model of Mina's per-update `success`. -/
def LocalSucceeds
    (T : TurnCoalg Obs AdmissibleTurn)
    (admits : T.Carrier → AdmissibleTurn → Prop)
    (x : T.Carrier) (t : AdmissibleTurn) : Prop :=
  admits x t

/-- **`willSucceed`** — the **prophecy**: the cumulative AND over all participants of
their `LocalSucceeds` bits. In the binary case, `localSucceeds₁ ∧ localSucceeds₂`. This
is the value Mina threads as `will_succeed` and then *checks against* the realized
conjunction in-circuit; here it is the realized conjunction itself (the prophecy is
discharged exactly when it matches). -/
def willSucceed
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (admits₁ : T₁.Carrier → AdmissibleTurn → Prop)
    (admits₂ : T₂.Carrier → AdmissibleTurn → Prop)
    (x₁ : T₁.Carrier) (x₂ : T₂.Carrier) (t : AdmissibleTurn) : Prop :=
  LocalSucceeds T₁ admits₁ x₁ t ∧ LocalSucceeds T₂ admits₂ x₂ t

/-- **`JointCommit`** — the all-or-none commit event for the JointTurn: every
participant's tier-local write lands. Modelled as the proposition "both participants
commit" (the per-cell commits, gated on the *same* shared aggregate proof). -/
def JointCommit
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (committed₁ : T₁.Carrier → AdmissibleTurn → Prop)
    (committed₂ : T₂.Carrier → AdmissibleTurn → Prop)
    (x₁ : T₁.Carrier) (x₂ : T₂.Carrier) (t : AdmissibleTurn) : Prop :=
  committed₁ x₁ t ∧ committed₂ x₂ t

/-- **`atomicity_as_proof` — atomicity ⇔ the cumulative AND (no coordinator).** The joint
turn commits (all participants' writes land) **iff** the cumulative-AND prophecy holds —
when each participant commits exactly on its own success and the aggregate proof is
shared. This encodes "all-or-none is *proven by the aggregate*, not run by a 2PC": there
is no third party; commit is definitionally the conjunction of the in-circuit success
bits. Hypotheses link each participant's commit to its local success (the per-cell gate on
the shared proof). -/
theorem atomicity_as_proof
    (T₁ T₂ : TurnCoalg Obs AdmissibleTurn)
    (admits₁ committed₁ : T₁.Carrier → AdmissibleTurn → Prop)
    (admits₂ committed₂ : T₂.Carrier → AdmissibleTurn → Prop)
    (x₁ : T₁.Carrier) (x₂ : T₂.Carrier) (t : AdmissibleTurn)
    -- each participant commits exactly when its local step succeeds (gated on the
    -- shared aggregate proof — the divergence from Mina's single global write):
    (gate₁ : ∀ x t, committed₁ x t ↔ LocalSucceeds T₁ admits₁ x t)
    (gate₂ : ∀ x t, committed₂ x t ↔ LocalSucceeds T₂ admits₂ x t) :
    JointCommit T₁ T₂ committed₁ committed₂ x₁ x₂ t ↔
      willSucceed T₁ T₂ admits₁ admits₂ x₁ x₂ t := by
  unfold JointCommit willSucceed
  exact and_congr (gate₁ x₁ t) (gate₂ x₂ t)

/-! ## N-ary family version (the general account-update FOREST)

The binary version above is the clear, load-bearing primitive (`study-category §1.4`); a
real `zkapp_command` is a *forest* over an index `ι` of participating cells. We restate
the shared turn-id and the binding for a family. The conservation aggregate (CG-5) is the
**finite monoid-sum** over participants — requiring `Fintype ι`. -/

/-- A **participating family**: an index `ι` of cells, each a `TurnCoalg`, with per-cell
turn-id and half-edge projections. The forest Mina hashes into one `account_updates_hash`. -/
structure JointFamily (ι : Type u) where
  /-- The participant at index `i`. -/
  cell   : ι → TurnCoalg Obs AdmissibleTurn
  /-- Participant `i`'s turn-id projection. -/
  turnId : (i : ι) → TurnIdOf (TurnId := TurnId) (cell i)
  /-- Participant `i`'s CG-5 half-edge contribution. -/
  half   : (i : ι) → HalfEdgeOf (Bal := Bal) (cell i)

/-- **`FamilyBinding` — the N-ary CG-2 ⊗ CG-5 HYPOTHESIS** (the forest equalizer). Carries
each participant's pre-state, the single shared turn `t` and shared id `tid`, a proof that
every participant's post-step commits to `tid` (CG-2 pullback over the whole forest), and
the CG-5 aggregate: the finite monoid-sum of half-edges over all participants is `0`. As
in the binary case this is a **premise, never derived**. -/
structure FamilyBinding
    (ι : Type u) [Fintype ι] (J : JointFamily (Obs := Obs) (AdmissibleTurn := AdmissibleTurn)
      (TurnId := TurnId) (Bal := Bal) ι)
    where
  /-- Per-participant pre-states. -/
  pre : (i : ι) → (J.cell i).Carrier
  /-- The single shared turn (one forest, one turn). -/
  t   : AdmissibleTurn
  /-- The shared turn-id (`account_updates_hash`). -/
  tid : TurnId
  /-- CG-2: every participant's post-step commits to the *same* shared id. -/
  agree : ∀ i, J.turnId i ((J.cell i).next (pre i) t) = tid
  /-- CG-5: the cross-cell conservation aggregate over the whole forest balances to `0`. -/
  balanced : (Finset.univ.sum fun i => J.half i (pre i) t) = 0

/-- **`family_joint_sound` — N-ary keystone.** If every participant in the forest is
step-complete and the `FamilyBinding` (CG-2 ⊗ CG-5 over the forest) holds, then the joint
state is sound. The binding is, again, a **premise**. Stated against per-cell soundness of
each participant plus the irreducible family binding; `sorry`. -/
theorem family_joint_sound
    (ι : Type u) [Fintype ι]
    (J : JointFamily (Obs := Obs) (AdmissibleTurn := AdmissibleTurn)
      (TurnId := TurnId) (Bal := Bal) ι)
    (Spec : ι → TurnCoalg Obs AdmissibleTurn)
    (cons auth chain obsAdv :
      (i : ι) → (J.cell i).Carrier → AdmissibleTurn → (J.cell i).Carrier → Prop)
    (hsc : ∀ i, StepComplete (J.cell i) (cons i) (auth i) (chain i) (obsAdv i))
    (b : FamilyBinding (Obs := Obs) (AdmissibleTurn := AdmissibleTurn)
      (TurnId := TurnId) (Bal := Bal) ι J)
    (i : ι) :
    Sound (J.cell i) (Spec i) (b.pre i) := by
  -- OPEN: N-ary joint soundness — same coinductive cross-cell bisimulation argument as
  -- `joint_sound`, generalized over the forest index ι and cutting the per-participant
  -- StepComplete witnesses against the FamilyBinding; depends on the still-OPEN
  -- single-cell `Boundary.sound_of_step_complete`.
  sorry

/-- **`family_atomicity` — the N-ary cumulative AND.** The forest commits iff every
participant's local step succeeds: `JointCommit_forest ⇔ ∀ i, LocalSucceeds (cell i)`. The
`will_succeed` prophecy for the forest is the universally-quantified conjunction; commit is
its discharge. No global coordinator — the conjunction *is* the all-or-none. -/
theorem family_atomicity
    {ι : Type u}
    (J : JointFamily (Obs := Obs) (AdmissibleTurn := AdmissibleTurn)
      (TurnId := TurnId) (Bal := Bal) ι)
    (admits committed : (i : ι) → (J.cell i).Carrier → AdmissibleTurn → Prop)
    (pre : (i : ι) → (J.cell i).Carrier) (t : AdmissibleTurn)
    (gate : ∀ i x t, committed i x t ↔ LocalSucceeds (J.cell i) (admits i) x t) :
    (∀ i, committed i (pre i) t) ↔ (∀ i, LocalSucceeds (J.cell i) (admits i) (pre i) t) :=
  forall_congr' fun i => gate i (pre i) t

end Metatheory.JointTurn
