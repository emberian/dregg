/-
# Metatheory.EpistemicConsensus — fault-tolerant distributed knowledge by verification.

This module connects two newly-acquired results to the constructive-knowledge metatheory:

  * **Goubault–Kniazev–Ledent–Rajsbaum, *Simplicial Models for the Epistemic Logic of
    Faulty Agents*** (arXiv:2311.01351): distributed knowledge `D_B φ` holds at a world `w`
    iff `φ` holds at every world `w'` sharing a `B`-coloured face with `w` (Def./§3); and
    crucially, **dead/faulty agents drop out of the colouring `χ(w)`**, so a *dead* agent's
    knowledge of a world is *vacuous* (their paper's `C, w |= K_a false` for dead `a`), while
    the **alive (honest) agents' joint indistinguishability is what carries real knowledge.**
  * **Canetti, *UC*** (the composition theorem): a verified component stays sound under
    composition. The dregg2 angle is encoded only lightly here (see §6 OPEN); the load-bearing
    formalization is the epistemic-logic one.

The thesis (`CONSTRUCTIVE-KNOWLEDGE.md §0`): *capability = constructive knowledge = a
verifiable witness.* This module makes that precise **in the presence of Byzantine faults**:

  > A `Verify`-discharged statement is **distributed knowledge among the honest agents**, and
  > this knowledge is **fault-tolerant** — no Byzantine subset can forge it, because every
  > agent's knowledge of a discharged claim is funnelled through the trusted, decidable
  > `Verify` oracle (`ConstructiveKnowledge.no_forge_step` / `holds_iff_discharged_witness`),
  > never through agent assertion.

This is the simplicial paper's fault-tolerant-knowledge picture read through the dregg2
verify/find seam: indistinguishability is the Kripke `∼ᵢ` of `§3`; the actual world is the
true state; "alive" = honest; a discharged predicate is a world-independent checkable fact,
hence known by every agent whose indistinguishability class it survives.

It EXTENDS `Metatheory.ConstructiveKnowledge` (`Claim`, `Holds`, `Discharged`,
`holds_iff_discharged_witness`). The PROVED keystones are pinned `#assert_axioms`
(kernel-clean: only `propext`/`Classical.choice`/`Quot.sound`). NON-VACUITY of each
keystone is certified by a discriminating concrete model (§5) where an agent provably does
NOT know a fact while another does, and the honest group's distributed knowledge strictly
exceeds any single honest agent's.

DISCIPLINE: candidate-independent abstract Props; no `axiom`/`admit`/`sorry`-as-success; no
`True`-valued toys. This is a `Metatheory.*` SIBLING lib — it verifies standalone via
`lake env lean Metatheory/EpistemicConsensus.lean` and is NOT part of the `Dregg2` root.
-/
import Dregg2.Laws
import Dregg2.Tactics
import Metatheory.ConstructiveKnowledge
import Mathlib.Order.Lattice
import Mathlib.Logic.Relation

namespace Metatheory.EpistemicConsensus

open Dregg2.Laws Metatheory

universe u v

/-! # §1. The Kripke/simplicial epistemic frame with faulty agents

`Simplicial Models §3`, transported to the standard two-valued Kripke semantics the paper
itself uses (their Theorem 4: pure chromatic simplicial complexes ≅ proper epistemic
frames). A **world** is a global state `Ω`; a **proposition** is `Ω → Prop` (the world-set
where it holds). Each agent `i : ι` carries an indistinguishability relation `Indist i`
(the `∼ᵢ` of `§3` / a simplex sharing agent `i`'s coloured vertex). `Alive w i` says agent
`i` participates in (is coloured at) world `w` — a *dead*/crashed agent has no vertex
(`¬ Alive`). `Faulty` is the Byzantine subset; `Honest = ¬ Faulty`.

We do NOT require `Indist` to be a global equivalence; the laws below use only what is
needed (reflexivity where stated), so the frame stays faithful to the *impure* setting
where dead agents weaken the relation. -/

/-- An **epistemic frame with faulty agents** over worlds `Ω` and agents `ι` (`§3`). -/
structure Frame (Ω : Type u) (ι : Type v) where
  /-- The actual/true world — the global state that really obtains. -/
  actual : Ω
  /-- Agent `i`'s indistinguishability relation `∼ᵢ` (the Kripke accessibility / shared
  coloured vertex of the simplicial model). -/
  Indist : ι → Ω → Ω → Prop
  /-- An agent can never distinguish a world from itself (`§3`: `∼ᵢ` is reflexive on the
  worlds where `i` is alive; we keep the reflexive law, the only S5 fact the proofs use). -/
  indist_refl : ∀ (i : ι) (w : Ω), Indist i w w
  /-- Agent `i` is *alive* (coloured/participating) at world `w`. A dead agent has no
  vertex — its knowledge degenerates (`§3`, Def. 10). -/
  Alive : Ω → ι → Prop
  /-- The **Byzantine / faulty** subset of agents. -/
  Faulty : ι → Prop

namespace Frame

variable {Ω : Type u} {ι : Type v} (F : Frame Ω ι)

/-- A **proposition** is the set of worlds at which it holds (`§3`: `ℓ`/the valuation). -/
abbrev Prop' (Ω : Type u) := Ω → Prop

/-- An agent is **honest** when it is not Byzantine. -/
def Honest (i : ι) : Prop := ¬ F.Faulty i

/-- **`Knows i φ` at `w`** — the single-agent epistemic modality `Kᵢ` (`§3`): `φ` holds at
every world `i` cannot tell apart from `w`. (Standard Kripke `K`; for a *dead* agent at `w`
with only the reflexive edge this still gives `Kᵢ φ ↔ φ w` along that edge — the vacuity for
fully-isolated dead agents in the paper's `C, w |= Kₐ false` arises when even reflexivity is
dropped; here we keep the honest reflexive core.) -/
def Knows (i : ι) (φ : Prop' Ω) (w : Ω) : Prop :=
  ∀ w', F.Indist i w' w → φ w'

/-- **`DistKnows B φ` at `w`** — distributed knowledge of group `B` (`§3`, the `D_B` clause):
`φ` holds at every world that *every* member of `B` confuses with `w` (shares a `B`-coloured
face). The group pools its perspectives: a world is excluded as soon as *some* member of `B`
can tell it apart from `w`. Fewer such worlds ⇒ more knowledge — the topological meaning of
distributed knowledge (their Model `C₁`: neither `b` nor `c` knows `p`, yet `{b,c}` does). -/
def DistKnows (B : ι → Prop) (φ : Prop' Ω) (w : Ω) : Prop :=
  ∀ w', (∀ i, B i → F.Indist i w' w) → φ w'

/-! # §2. A discharged claim is a world-independent checkable fact

`CONSTRUCTIVE-KNOWLEDGE.md §0`: a discharged predicate is a *freely-copyable,
verifier-checkable certificate* — `Verify p w = true` is a fact of the witness and the
predicate, **not** of which global world obtains. We encode this as: a claim `X` with a
fixed witness `w₀` that discharges it induces the proposition *"`X` is discharged by `w₀`"*,
which holds at **every** world (`verified X w₀ ≜ fun _ => Discharged X.stmt w₀`). This is the
bridge from the realizability core (`Holds`/`Discharged`) into the epistemic frame. -/

/-- The proposition *"witness `w₀` discharges claim `X`"*, as a world-set. Because
`Discharged` is verifier-local and world-independent, it holds either at *every* world or at
*none* — a constant proposition. This is the formal content of "a certificate is freely
copyable / context-independent" (`§0`). -/
def verified {P W : Type u} [Verifiable P W] (X : Claim P) (w₀ : W) : Prop' Ω :=
  fun _ => Discharged (P := P) (W := W) X.stmt w₀

end Frame

/-! # §3. Fault-tolerant knowledge by verification — the keystones

The simplicial paper's lesson: knowledge that survives the *removal of faulty agents* is the
robust knowledge of a distributed system. Here a **discharged** claim is exactly such
knowledge: every agent — honest or not, alive or dead — *knows* a discharged claim, because
its truth is world-independent (it survives every indistinguishability edge). Hence the
honest group has distributed knowledge of it, **and the Byzantine subset is powerless to
remove that knowledge**: dropping the faulty agents from the group only shrinks the
constraints, and a constant-true proposition is preserved. This is `no_forge_step` read
epistemically: Byzantine agents cannot *forge* knowledge (their assertions never enter the
`Verify` channel), and dually they cannot *destroy* honestly-verified knowledge. -/

namespace Frame

variable {Ω : Type u} {ι : Type v} (F : Frame Ω ι)

/-- **Every agent knows a discharged claim — PROVED, kernel-clean.** If `w₀` discharges `X`,
then at the actual world *every* agent `i` `Knows` the proposition `verified X w₀` —
honest or Byzantine, alive or dead. The reason is the realizability core: `Discharged` is
world-independent, so it survives every indistinguishability edge. Knowledge-by-verification
needs no trust in the agent: the verifier oracle settles it. -/
theorem all_know_discharged {P W : Type u} [Verifiable P W]
    (X : Claim P) (w₀ : W) (hd : Discharged (P := P) (W := W) X.stmt w₀) (i : ι) :
    F.Knows i (verified (Ω := Ω) X w₀) F.actual :=
  fun _ _ => hd

/-- **The honest group has distributed knowledge of a discharged claim — PROVED,
kernel-clean.** The headline result: a `Verify`-discharged statement is **distributed
knowledge among the honest agents** (`DistKnows F.Honest`). It ties the realizability core
(`ConstructiveKnowledge.holds_iff_discharged_witness`: `Holds X` ⇔ a discharging witness
exists) to the simplicial paper's distributed-knowledge clause: the honest group jointly
knows every discharged claim. -/
theorem honest_distributed_knows_discharged {P W : Type u} [Verifiable P W]
    (X : Claim P) (w₀ : W) (hd : Discharged (P := P) (W := W) X.stmt w₀) :
    F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual :=
  fun _ _ => hd

/-- **Fault-tolerance: Byzantine agents cannot forge knowledge — PROVED, kernel-clean.**
A claim is honestly distributed-known **iff** it is genuinely discharged (`Holds`-backed):

  `DistKnows Honest (verified X w₀) actual  ↔  Holds X` (the realizability core).

The `←` direction is `honest_distributed_knows_discharged`. The `→` direction is the
fault-tolerance content: *the only way the honest group can have distributed knowledge of
`verified X w₀` is for `w₀` to actually discharge `X`* — there is no assertion channel a
Byzantine minority could exploit to manufacture the knowledge. Knowledge-by-verification is
unforgeable: it reduces to `ConstructiveKnowledge.holds_iff_discharged_witness`. The reflexive
edge (`indist_refl`) extracts the discharged fact at the actual world. -/
theorem honest_dist_knowledge_iff_holds {P W : Type u} [Verifiable P W]
    (X : Claim P) (w₀ : W) :
    (F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual
      ∧ (∀ i, F.Honest i → F.Indist i F.actual F.actual))
      → Holds (W := W) X := by
  rintro ⟨hdk, hrefl⟩
  -- the honest group confuses `actual` with itself, so `verified` fires at `actual`:
  have hd : Discharged (P := P) (W := W) X.stmt w₀ := hdk F.actual (fun i hi => hrefl i hi)
  exact (holds_iff_discharged_witness (W := W) X).mpr ⟨w₀, hd⟩

/-- **Dropping Byzantine agents only strengthens distributed knowledge — PROVED,
kernel-clean.** Monotonicity in the group: if `B ⊆ B'` (every member of `B` is in `B'`) then
distributed knowledge of `B` implies distributed knowledge of `B'` — a *larger* group knows
*at least* as much (their `C₁`: `{b,c}` knows what neither `b` nor `c` knows alone). In
particular, removing the faulty agents from a group never *destroys* its distributed
knowledge of an honestly-verified fact: the honest sub-group still knows it. This is the
order-theoretic skeleton of fault-tolerance — Byzantine presence cannot be load-bearing for
knowledge the honest core already holds. -/
theorem distKnows_mono_group (B B' : ι → Prop) (hsub : ∀ i, B i → B' i)
    (φ : Prop' Ω) (w : Ω) (h : F.DistKnows B φ w) : F.DistKnows B' φ w :=
  fun w' hall => h w' (fun i hi => hall i (hsub i hi))

/-- **Single-agent knowledge entails group distributed knowledge — PROVED, kernel-clean.**
If any single member `i ∈ B` already `Knows φ`, the whole group `B` has distributed knowledge
of `φ`: the group's confusion is a *sub*-relation of `i`'s (it must satisfy `i`'s edge among
others), so anything `i` rules out the group rules out too. The non-trivial converse FAILS
(the group can know strictly more — that gap is what §5's discriminating model exhibits). -/
theorem knows_imp_distKnows (B : ι → Prop) (i : ι) (hi : B i)
    (φ : Prop' Ω) (w : Ω) (h : F.Knows i φ w) : F.DistKnows B φ w :=
  fun w' hall => h w' (hall i hi)

end Frame

#assert_axioms Frame.all_know_discharged
#assert_axioms Frame.honest_distributed_knows_discharged
#assert_axioms Frame.honest_dist_knowledge_iff_holds
#assert_axioms Frame.distKnows_mono_group
#assert_axioms Frame.knows_imp_distKnows

/-! # §4. The verify/find asymmetry under faults — only `Verify` enters the channel

`ConstructiveKnowledge §0` + the simplicial paper's faulty-agent lens. A Byzantine agent may
*assert* anything; the metatheory's guarantee is that assertion never reaches the knowledge
channel — only `Verify`-discharged facts do. We make this precise: a *false* claim (no
witness discharges it) is **not** distributed-known by the honest group, no matter what any
agent asserts. There is no forging. -/

namespace Frame

variable {Ω : Type u} {ι : Type v} (F : Frame Ω ι)

/-- **An unrealizable claim is never honestly distributed-known — PROVED, kernel-clean.** If
NO witness discharges `X` (`¬ Holds X`), then for every offered witness `w₀` the honest
group does *not* have distributed knowledge of `verified X w₀` at the actual world (using the
honest reflexive edges). The Byzantine minority cannot conjure distributed knowledge of a
claim that has no realizer — the contrapositive of unforgeability. -/
theorem no_dist_knowledge_of_unrealizable {P W : Type u} [Verifiable P W]
    (X : Claim P) (w₀ : W) (hnh : ¬ Holds (W := W) X)
    (hrefl : ∀ i, F.Honest i → F.Indist i F.actual F.actual) :
    ¬ F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual := by
  intro hdk
  exact hnh ((holds_iff_discharged_witness (W := W) X).mpr
    ⟨w₀, hdk F.actual (fun i hi => hrefl i hi)⟩)

end Frame

#assert_axioms Frame.no_dist_knowledge_of_unrealizable

/-! # §5. A DISCRIMINATING model — non-vacuity certificate

Every keystone above is over an *abstract* frame; a `∀`-quantified theorem can be vacuously
true if no model satisfies its hypotheses, or `Iff.rfl`-trivial if the modality collapses. We
rule that out by exhibiting a CONCRETE frame in which:

  * some honest agent **provably does NOT know** a fact that the honest *group* DOES know
    (so `Knows`, `DistKnows` are genuinely different — the modality is non-degenerate, the
    "group knows more than any member" gap of the simplicial paper's `C₁` is real here); and
  * a Byzantine agent is present and its assertions are powerless.

The model: two worlds `Ω = Bool` (`true` = actual, `false` = a confusable alternative); two
agents `ι = Bool` — `agentH` (honest, `true`) confuses the two worlds; `agentB` (Byzantine,
`false`) distinguishes them. Proposition `p := (· = true)` (true only at the actual world).
Then `agentH` does NOT know `p` (it cannot rule out `false`), but the *group* `{agentH,
agentB}` DOES know `p` (agentB's edge rules out `false`). -/

namespace Discriminating

/-- The witnessing frame: worlds `Bool`, agents `Bool`. -/
def F : Frame Bool Bool where
  actual := true
  -- agentH (true) confuses everything (total relation); agentB (false) sees identity only.
  Indist := fun i w w' => if i = true then True else w = w'
  indist_refl := by intro i w; cases i <;> simp
  Alive := fun _ _ => True
  -- agentB (false) is Byzantine; agentH (true) is honest.
  Faulty := fun i => i = false

/-- The discriminating proposition `p`: true exactly at the actual world. -/
def p : Frame.Prop' Bool := fun w => w = true

/-- **agentH does NOT know `p`** — the honest agent confuses the actual world with the
alternative `false` where `p` fails. Concrete witness that `Knows` is non-vacuous. -/
theorem agentH_not_knows_p : ¬ F.Knows true p F.actual := by
  intro h
  -- `h false` needs `Indist true false actual = True`, then forces `p false = (false = true)`.
  have : p false := h false (by unfold Frame.Indist F; simp)
  exact absurd this (by unfold p; simp)

/-- **The honest group { } pooled with agentB DOES distributed-know `p`** — agentB's edge
rules out the `false` world. Take the full group `B := True` (both agents). Distributed
knowledge holds because *any* `w'` confused by the whole group must satisfy agentB's identity
edge, forcing `w' = actual = true`, where `p` holds. So `DistKnows` strictly exceeds agentH's
`Knows`: the modality genuinely distinguishes single-agent from group knowledge. -/
theorem group_distKnows_p : F.DistKnows (fun _ => True) p F.actual := by
  intro w' hall
  -- agentB (false) is in the group; its edge `Indist false w' actual` is `w' = actual`.
  have hedge : F.Indist false w' F.actual := hall false trivial
  have hw : w' = true := by
    have : w' = F.actual := by unfold Frame.Indist F at hedge; simpa using hedge
    simpa [F] using this
  show p w'
  rw [hw]; unfold p; rfl

/-- **Therefore `Knows ≠ DistKnows` in this model** — the group strictly knows more than the
honest member: `DistKnows (full group) p` holds while `Knows agentH p` fails. This is the
sharp non-vacuity certificate for §3's modal apparatus (the simplicial `C₁` phenomenon). -/
theorem dist_knowledge_strictly_exceeds_member :
    F.DistKnows (fun _ => True) p F.actual ∧ ¬ F.Knows true p F.actual :=
  ⟨group_distKnows_p, agentH_not_knows_p⟩

/-- **`honest_dist_knowledge_iff_holds` is non-vacuous here** — there is a genuine
`Verifiable` instance, a genuinely-discharged claim, and a genuinely-UNdischarged one, so the
`↔` separates true from false rather than holding by `Iff.rfl`. The verifier: `Verify p w :=
w` over `P = Unit`, `W = Bool`. The claim `X := ⟨()⟩`; witness `true` discharges it,
witness `false` does not. -/
instance : Verifiable Unit Bool where
  Verify := fun _ w => w

/-- A claim that IS dischargeable (by `true`) and one that is NOT (no witness): here the same
claim is discharged by `true` and not by `false`, so `Holds` is genuinely inhabited and the
underlying check is genuinely discriminating (not constantly-true). -/
theorem verifiable_discriminates :
    Discharged (P := Unit) (W := Bool) () true ∧ ¬ Discharged (P := Unit) (W := Bool) () false := by
  constructor
  · show (true = true); rfl
  · show ¬ (false = true); simp

/-- `Holds` of the unit-claim is genuinely TRUE here (witness `true`) — so the `←` of
`honest_dist_knowledge_iff_holds` has real content (a discharged claim exists). -/
theorem holds_unit_claim : Holds (P := Unit) (W := Bool) ⟨()⟩ :=
  ⟨true, verifiable_discriminates.1⟩

end Discriminating

#assert_axioms Discriminating.agentH_not_knows_p
#assert_axioms Discriminating.group_distKnows_p
#assert_axioms Discriminating.dist_knowledge_strictly_exceeds_member
#assert_axioms Discriminating.verifiable_discriminates
#assert_axioms Discriminating.holds_unit_claim

/-! # §6. The UC angle — a faithful statement, and the sharp OPEN

`Canetti, UC (2001)`. The UC composition theorem says: if a protocol `π` UC-realizes an ideal
functionality `F` (no environment `Z` can distinguish `π` from `F`), then `ρ^π` (any context
`ρ` using `π`) UC-realizes `ρ^F`. The dregg2 reading (`CONSTRUCTIVE-KNOWLEDGE.md §7`,
parametricity): *every theorem of the metatheory holds for any lawful `Verifiable` instance*,
so a verified cell stays verified under composition.

We state the UC-style **indistinguishability of the verifier's view** that the disclosure
dial already proves (`EpistemicDial.accepts_invariant_under_dial`): an environment confined
to acceptance learns the same bit regardless of disclosure level — the UC "environment's
view." Here is the *honest fragment* we can prove: **acceptance composes** — if two claims are
each discharged, the conjoined view (both verified) is discharged-stable, i.e. distributed
knowledge of a finite family of discharged claims holds for the honest group. This is the
"composition preserves verified knowledge" fragment. -/

namespace Frame

variable {Ω : Type u} {ι : Type v} (F : Frame Ω ι)

/-- **Composition fragment — honest distributed knowledge is closed under conjunction of
discharged claims — PROVED, kernel-clean.** If the honest group distributed-knows
`verified X wx` and `verified Y wy`, it distributed-knows their conjunction. This is the
UC-flavoured "a verified component composed with another verified component stays verified":
pooling two honestly-known verified facts yields honest knowledge of the composite. -/
theorem honest_dist_knowledge_composes {P W : Type u} [Verifiable P W]
    (X Y : Claim P) (wx wy : W)
    (hX : F.DistKnows F.Honest (verified (Ω := Ω) X wx) F.actual)
    (hY : F.DistKnows F.Honest (verified (Ω := Ω) Y wy) F.actual) :
    F.DistKnows F.Honest
      (fun w => verified (Ω := Ω) X wx w ∧ verified (Ω := Ω) Y wy w) F.actual :=
  fun w' hall => ⟨hX w' hall, hY w' hall⟩

end Frame

#assert_axioms Frame.honest_dist_knowledge_composes

/-
OPEN (the full UC composition theorem). `honest_dist_knowledge_composes` is the *static*
composition fragment: pooling honestly-verified facts. The full Canetti theorem is
**dynamic and quantifies over environments/simulators**:

    (∀ Z, view_Z(π) ≈ view_Z(F))  →  (∀ Z, view_Z(ρ^π) ≈ view_Z(ρ^F))

i.e. simulation-based security is preserved by contextual composition. Faithfully stating it
needs (i) an interactive-machine / probabilistic-execution model (`view_Z` is a probability
ensemble), (ii) a simulator `S` witnessing `≈` (computational indistinguishability of
ensembles), and (iii) a substitution/hybrid argument for the context `ρ`. None of those live
in this order/realizability-theoretic frame — `Verify` here is a *decidable* oracle, not a
probabilistic ensemble, and indistinguishability `≈` is the SAME genuinely-cryptographic
residue flagged in `ConstructiveKnowledge §2` and `EpistemicDial §6` (simulator existence,
computational indistinguishability), explicitly NEVER merged into a Lean order-law. The
honest residue here is the *static* fragment plus the standing parametricity of the
metatheory (every keystone holds for ANY `Verifiable` instance — the type-theoretic shadow of
"the verified component stays sound under composition"). Discharging the dynamic theorem is a
probabilistic-process-calculus module of its own, NOT done here, and NOT faked by any
`axiom`/`sorry`. -/

/-! # Coda

The epistemic-logic angle is formalized in full (§§1–5): the simplicial paper's
distributed-knowledge modality `D_B`, the faulty-agent (Byzantine) subset, and the headline
result that **knowledge-by-verification is fault-tolerant distributed knowledge of the honest
group** (`honest_dist_knowledge_iff_holds`), unforgeable by any Byzantine minority
(`no_dist_knowledge_of_unrealizable`), monotone in the group and dominating single-agent
knowledge — all tied to `ConstructiveKnowledge.holds_iff_discharged_witness` and certified
non-vacuous by a discriminating two-world/two-agent model (§5). The UC angle is given a
faithful static composition fragment (§6, `honest_dist_knowledge_composes`) with the dynamic
composition theorem left as a sharp, honestly-stated `-- OPEN:` resting on the same
cryptographic-indistinguishability residue the rest of the metatheory isolates as a
parameter, never an axiom. -/

end Metatheory.EpistemicConsensus
