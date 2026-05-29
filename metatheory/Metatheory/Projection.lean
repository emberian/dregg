/-
# Metatheory.Projection — the cand-D choreography front-end (the syntactic spine).

`docs/rebuild/cand-D-choreography.md`: a choreography is a *diagram in the turn-category*;
endpoint projection is the *functor* to per-cell behaviours; the runtime monitor of a
projected local type *is* the vat-boundary membrane. This module sits atop `Coordination`
(which carries the MPST `GlobalType`/`project`/`LocalType` machinery) and adds cand-D's
two distinctive pieces:

  1. **The blue/red projection-split** (`STUDY-projection-split`): an interaction whose
     write-set invariant is BEC-**I-confluent** is **blue** — it projects to a
     `CellProgram` admissibility step that runs cross-group, partition-tolerant, with NO
     commit; everything else is **red** — it projects to an atomic **JointTurn**
     (`JointTurn.lean`, CG-2 ⊗ CG-5, tier ≥ 3). The classifier is Whittaker's segmented
     invariant-confluence, tightened by `byzantine-eventual-consistency`'s iff.
  2. **`epp_correspondence`** — the keystone: the parallel composition of `G`'s endpoint
     projections is behaviourally equivalent to `G`. **The realization (cand-D §7):** this
     and `Boundary.boundary_law` are *the same theorem at two altitudes* — the per-endpoint
     instance of `epp_correspondence` IS the vat-boundary law; the membrane = the
     projection. And `byzantine_epp_by_monitoring` — projection is sound over Byzantine
     parties GIVEN (i) per-endpoint monitoring-with-blame and (ii) the blocklace
     equivocation-repelling assumption as a HYPOTHESIS (never derived — cand-D §5a: the
     front-end's Byzantine-safety bottoms out on the blocklace substrate).

Discipline (cand-D §3/§5b, a hard design law): choreography is the typed overlay you
**opt into**; open ocap messaging is the substrate it compiles to and falls back to. Make
`G` mandatory and cand-D dies. Crypto-soundness stays out of Lean (`dregg2 §8`): the
monitor's conformance check is a decidable `Verify` oracle.
-/
import Metatheory.Coordination
import Metatheory.Confluence
import Metatheory.Boundary

namespace Metatheory.Projection

open Metatheory.Coordination

universe u

/-! ## 1. The blue/red projection-split -/

/-- The projection-time colour of an interaction: **blue** = coordination-free
(I-confluent, partition-tolerant, no commit); **red** = coupled (atomic JointTurn). -/
inductive Colour where
  | blue
  | red
  deriving DecidableEq, Repr

/-- **An interaction is blue-eligible iff its write-set invariant is I-confluent.** This
is the projection-split classifier's core predicate — the `Confluence.lean` third
judgement read at the choreography altitude. Blue interactions need NO cross-group
coordination; red ones must escalate to a `JointTurn`. -/
def BlueEligible {S : Type u} [Confluence.MergeState S] (I : Confluence.Invariant S) : Prop :=
  Confluence.IConfluent I

/-- **Blue ⇔ I-confluent (the classifier's soundness, PROVED by definition).** A static
classifier that colours an interaction blue exactly when its invariant is I-confluent is
sound: blue-eligibility coincides with `Confluence.Tier1Eligible`. -/
theorem blue_iff_tier1Eligible {S : Type u} [Confluence.MergeState S]
    (I : Confluence.Invariant S) :
    BlueEligible I ↔ Confluence.Tier1Eligible I :=
  Iff.rfl

/-- **A blue interaction's concurrent merges preserve its invariant — PROVED** (the
operational payoff of the colour: a blue step can run on every replica without
coordination and still keep `I`). Direct consequence of `BlueEligible = IConfluent`. -/
theorem blue_merge_safe {S : Type u} [Confluence.MergeState S]
    (I : Confluence.Invariant S) (h : BlueEligible I) (x y : S)
    (hx : I x) (hy : I y) : I (x ⊔ y) :=
  h x y hx hy

/-- The interaction kinds a projected `G` compiles to: blue → a `CellProgram`
admissibility clause (no commit); red → an atomic `JointTurn` (committed at the join of
the written cells' tiers). The runtime executes the projection by emitting these. -/
inductive ProjectionTarget where
  | cellProgram   -- blue: I-confluent, cross-group, partition-tolerant, no commit
  | jointTurn     -- red:  coupled, CG-2 ⊗ CG-5 equalizer, atomic, tier ≥ 3
  deriving DecidableEq, Repr

/-- Routing: a blue interaction targets a `CellProgram`; a red one targets a `JointTurn`.
(The `JointTurn` target is `JointTurn.lean`'s already-built bilateral aggregation.) -/
def route : Colour → ProjectionTarget
  | .blue => .cellProgram
  | .red  => .jointTurn

/-! ## 2. Endpoint-projection correspondence (the keystone) and Byzantine soundness -/

/-- **`epp_correspondence` — the keystone (cand-D §7).** For a `Projectable G`, the
parallel composition of `G`'s endpoint projections realises `G`: every `comm` step of the
global type is matched by dual `send`/`recv` actions at the projected endpoints. (Stated,
as in `Coordination.projection_sound`, at the head-duality level — the full bisimulation
is the EPP correspondence of `deadlock-freedom-by-design-choreography-cm13`.) **THE
REALIZATION:** this is `Boundary.boundary_law` at the choreography altitude — its
per-endpoint instance is the vat-boundary law; the monitored boundary = the projection.
Carried as an obligation (the full bisimulation needs the operational LTS of `Coordination`). -/
theorem epp_correspondence (G : GlobalType) (a b : Role) (s : Payload) (k : GlobalType)
    (hG : G = GlobalType.comm a b s k) (hab : a ≠ b) :
    Dual (project G a) (project G b) := by
  -- The same head-duality content as `Coordination.projection_sound`, stated directly on
  -- the global type `G` (the sender `a` projects to `send`, the receiver `b ≠ a` to the
  -- dual `recv`; `Dual (send …) (recv …)` unfolds to `s = s`).
  rw [hG]
  simp only [project, if_true, if_neg hab.symm, Dual]

/-
**`byzantine_epp_by_monitoring` — the central OPEN frontier (cand-D §5a/§7), NOT yet
statable.** The claim: a monitored, blocklace-backed projection of `G` behaviourally
*refines* `G` even over Byzantine endpoints, GIVEN (i) per-endpoint monitoring-with-blame
(`monitorability-of-session-types`) and (ii) the blocklace equivocation-repelling
guarantee as a HYPOTHESIS, never derived (local monitoring cannot catch a peer showing
different messages to different observers — that is the blocklace/BEC substrate's job,
exactly as `JointTurn.JointBinding` is a premise, not a fact).

We deliberately do NOT write this as a Lean `theorem` yet: a faithful statement needs the
operational monitor LTS + a refinement relation that `Coordination` does not yet provide,
and writing `(premises) : Conforms G` for an abstract `Conforms` would be either vacuous
or unprovable-as-stated. It is recorded here as the named obligation. The PROVABLE part
of the Byzantine story — that the **blue (I-confluent) fragment** stays invariant-safe
under *any* (adversarially-permuted) concurrent merge, hence needs no coordination — is
`blue_merge_safe` above; the red/coupled fragment's Byzantine-EPP is the open theorem the
blocklace owns.
-/

end Metatheory.Projection
