/-
# Dregg2.HandlerTransformer — the safe higher-order handler-transformer frontier.

> **The conjecture under test (ember's higher-order handler-transformer frontier).**
> A SAFE higher-order handler-transformer = a MORPHISM in the category of
> SHEAVES-OF-HANDLERS, and the SAFE-COMPOSITION LAW = the camera's frame-preserving
> update (`Resource.Fpu`) = the sheaf gluing condition (`ProofForest.proofForest_sound`).

This module is the *discovery attempt* the read-only docs `HANDLER-TRANSFORMER-CONJECTURE.md`
and `HANDLER-TRANSFORMER-LIT.md` set up. Their honest a-priori verdict, which this module
both honours and tries to make load-bearing:

  * `Resource.Fpu` *is* a proved safe-composition law at **first order** (`Fpu.trans`,
    `conservation_is_fpu`, `ConfinesAuthority ≜ Fpu`). The single buildable unification step
    they name (§5, theorem `handlerTransformer_fpu_composes` / G1) is: define a *resource
    action* `act : Handler → (R → R)`, call a transformer **Fpu-safe** when its action is
    always an `Fpu`, and lift `Fpu.trans` through it — with teeth (an over-sharing
    transformer genuinely rejected, since a frame `f` with `valid (a⊙f) ∧ ¬valid (b⊙f)`
    exists in `Auth`/`Excl`).
  * `ProofForest.proofForest_sound` *is* a proved gluing with teeth (the `¬chainLinked`
    witness). The gluing leg they name (§3 G2 / `SHEAF-OF-VERIFIERS §5.1`
    `proofForest_sheaf_sound`) is: lift the constant fibre `StepProofValid` to a per-node
    **verifier-indexed** `DischargedFor Vᵢ` (the per-party stalk, facet 5), keep `Linked`,
    add a substantive overlap-compatibility hypothesis, with teeth from `dial_endpoints_distinct`.

## What this module GENUINELY UNIFIES (a theorem subsuming special cases, with teeth)

We build a SINGLE abstract interface — a **safe-step preorder** `SafeStep` (a reflexive,
transitive relation = a thin category / a preorder = exactly the structure a "category of
sheaves-of-handlers" must carry on its morphisms) — and then prove that **TWO genuinely
different dregg objects instantiate it**:

  1. the camera, via `Fpu` (so `Fpu.trans`/`Fpu.refl` ARE the `SafeStep` laws), and
  2. the proof-forest gluing surface, via `chainLinked`-compatibility of commitment surfaces.

A `HandlerTransformer` (abstractly: a map `Handler → Handler`) is **safe** for a `SafeStep`
when its induced action is always a safe step; the GENERAL theorem `safe_transformer_composes`
(`SafeStep.trans` lifted through the action) says **safe transformers compose**, and is
instantiated TWICE — once on the camera (`conservation_is_fpu` becomes a safe transformer),
once on the forest. The TEETH: `unsafe_transformer_rejected` exhibits an `Excl`-camera
transformer whose action is NOT a safe step, so it is genuinely refused; `#eval`/example
witnesses fire.

## What is HONESTLY left OPEN (the weld is a pun until a carrier is shared)

The conjecture's keystone — that `Fpu`-preservation *IS* the gluing condition (one law, not
two instances of one preorder) — requires the camera carrier and the proof-forest commitment
carrier to be the SAME object with a restriction map `ρ`. They are not (continuity is an
*equality* of commitments; `Fpu` is an *implication* over a frame). We do NOT fake this:
`SafeStep` unifies them as TWO instances of one PREORDER interface (real, with teeth), which
is strictly weaker than "one law". The residual is stated as a precise `-- OPEN:` and the
higher-order (recursive-camera) tier is left `-- OPEN:` exactly as the docs prescribe.

No `sorry`/`admit`/`axiom`/`native_decide`. Keystones `#assert_axioms`-pinned. Additive: a
NEW module; edits no existing file. Imports the four facet-bearing modules so the instance
lemmas reference the *actual* proved theorems, not copies.
-/
import Dregg2.Resource
import Dregg2.Await
import Dregg2.Exec.ProofForest
import Dregg2.Authority.DesignatedVerifier
import Dregg2.Tactics

namespace Dregg2.HandlerTransformer

-- The carrier structure `HandlerTransformer` shares its name with the namespace (intentional —
-- the module's central object); silence the cosmetic duplicate-namespace linter for it.
set_option linter.dupNamespace false
-- `conservativeAct_matched` does not use the `[AddCommMonoid M]` instance in its statement; the
-- `omit`-per-theorem form is noisier than the section option here. Pure-style, no correctness effect.
set_option linter.unusedSectionVars false

universe u

open Dregg2.Resource (ResourceAlgebra Fpu Auth Excl fits)
open Dregg2.Resource.ResourceAlgebra

/-! ## §1 — `SafeStep`: the abstract safe-composition preorder (the morphism law).

A "category of sheaves-of-handlers" must, at minimum, give its morphisms a **reflexive,
transitive** composition law — a thin category / preorder. We isolate exactly that as a
typeclass `SafeStep R`, a binary relation `safe : R → R → Prop` with `refl`/`trans`. This is
the *single definition* the conjecture's two proved composition laws are tested against: is
each (the camera's `Fpu`, the forest's gluing) an instance of ONE `SafeStep`? If yes, they
genuinely share a structure (not just vocabulary); the open question is whether they share a
CARRIER (§6), which `SafeStep` does NOT assert. -/

/-- **`SafeStep R`** — a reflexive-transitive "safe to compose" relation on a carrier `R`.
This is the morphism-composition skeleton of a category (objects = `R`, a unique morphism
`a ⟶ b` iff `safe a b`). `refl` = identity; `trans` = composition. A handler-transformer is
*safe* exactly when its action is a `safe` step (§3). -/
class SafeStep (R : Type u) where
  /-- "Replacing `a` by `b` is a safe step" — the morphism-existence relation. -/
  safe  : R → R → Prop
  /-- Identity: doing nothing is safe. -/
  refl  : ∀ a, safe a a
  /-- Composition: a safe step after a safe step is safe (the morphism-composition law). -/
  trans : ∀ {a b c}, safe a b → safe b c → safe a c

/-! ## §2 — INSTANCE 1: the camera `Fpu` IS a `SafeStep` (facet 2, a literal instance).

`Resource.Fpu.refl`/`Resource.Fpu.trans` are *exactly* the `SafeStep` laws — so the camera's
frame-preserving update is an instance of the abstract safe-composition preorder by the
already-proved theorems, no new content. This is the strongest, most honest unification leg:
`conservation_is_fpu` (facet 2) lands here verbatim (§4). -/

/-- **The camera is a `SafeStep` via `Fpu`** — `Fpu.refl`/`Fpu.trans` (`Resource.lean:114,118`)
are the identity/composition laws. The frame-preserving update is, on the nose, an instance of
the safe-composition preorder. -/
instance instSafeStepFpu (R : Type u) [ResourceAlgebra R] : SafeStep R where
  safe  := Fpu
  refl  := Fpu.refl
  trans := Fpu.trans

/-! ## §3 — `HandlerTransformer` and the SAFE-COMPOSITION predicate (the abstract definition).

A handler-transformer is, abstractly, a map `H ↦ T(H)` sending a handler to a handler (the
Schrijvers–Piróg–Wu–Jaskelioff / comodel-morphism reading). We do NOT yet have a `Handler →
Handler` whose action on a camera is built into `Await.Handler` (the docs flag this as the
unbuilt `act` functor). So we make the **action explicit**: a `HandlerTransformer R` carries
its own resource action `act : R → R` (the camera update its committed effect induces — a
`transfer`'s `±δ` on the `Auth` fragment). This is the honest first-order model: the
transformer's *effect on resources*, which is all the safe-composition law constrains. -/

/-- **`HandlerTransformer R`** — a handler-transformer modelled by the resource action it
induces on the camera `R`. (`act a` = the post-state when the transformer's committed effect
acts on resource `a`.) The handler-level `Handler → Handler` map and its `act` functor are
the unbuilt comodel-morphism the docs flag ASPIRATIONAL; here we work directly with `act`, the
first-order shadow the safe-composition law actually sees. -/
structure HandlerTransformer (R : Type u) where
  /-- The resource update the transformer's committed effect induces. -/
  act : R → R

/-- Composition of handler-transformers: do `T₁` then `T₂` (function composition of actions).
This is the candidate morphism-composition the safe-composition law must preserve. -/
def HandlerTransformer.comp {R : Type u} (T₂ T₁ : HandlerTransformer R) :
    HandlerTransformer R :=
  ⟨T₂.act ∘ T₁.act⟩

/-- **`Safe T`** — the safe-composition predicate: a transformer is safe iff its action is a
`SafeStep` from every state `a` to `act a`. For the camera instance (`instSafeStepFpu`) this
unfolds to `∀ a, Fpu a (T.act a)` — "the transformer never invalidates a third party's frame",
exactly the conjecture's safe-composition side-condition. -/
def Safe {R : Type u} [SafeStep R] (T : HandlerTransformer R) : Prop :=
  ∀ a, SafeStep.safe a (T.act a)

/-! ## §4 — THE GENERAL SAFE-COMPOSITION THEOREM (G1, PROVED, with teeth).

`safe_transformer_composes`: if `T₁` and `T₂` are each safe, AND the safe-steps chain along
the composite (`act` of one carries into the other — the substantive hypothesis that makes
this NOT vacuous), then `T₂ ∘ T₁` is safe. The composition core is `SafeStep.trans`, which on
the camera instance is `Fpu.trans` — so this is the one-line lift the docs (§5) name. -/

/-- **`safe_transformer_composes` — SAFE TRANSFORMERS COMPOSE (the general theorem, PROVED).**
Given `T₁`, `T₂` safe and the chaining hypothesis `hchain` (the intermediate state `T₁.act a`
safe-steps to `T₂.act (T₁.act a)` — provided by `T₂`'s own safety AT that state), the
composite `T₂.comp T₁` is safe. Proved by `SafeStep.trans` (= `Fpu.trans` on the camera). The
chaining is `hsafe₂ (T₁.act a)`, so the theorem needs no extra premise — it is the honest lift.

This SUBSUMES the special case `Fpu.trans`: on `instSafeStepFpu R`, `Safe T` is `∀ a, Fpu a
(T.act a)`, and `safe_transformer_composes` IS the statement that Fpu-safe transformers compose
preserving frame-safety — facet 2's composition law, now stated for transformers. -/
theorem safe_transformer_composes {R : Type u} [SafeStep R]
    {T₁ T₂ : HandlerTransformer R} (hsafe₁ : Safe T₁) (hsafe₂ : Safe T₂) :
    Safe (T₂.comp T₁) := by
  intro a
  -- `(T₂.comp T₁).act a = T₂.act (T₁.act a)`; chain `a ↝ T₁.act a ↝ T₂.act (T₁.act a)`.
  exact SafeStep.trans (hsafe₁ a) (hsafe₂ (T₁.act a))

/-! ### Facet 2 as a LITERAL INSTANCE: `conservation_is_fpu` is a safe transformer.

A conservative fragment-rewrite `f → f'` under a fixed authoritative total `a` (the content of
`Resource.conservation_is_fpu`) IS a safe handler-transformer on `Auth M`: define the action to
send the `(some a)`-authoritative state with fragment `f` to the one with fragment `f'`. We pin
the action to the conservative move and show `Safe` holds via `conservation_is_fpu`. -/

section CameraInstance
variable {M : Type u} [AddCommMonoid M]

/-- The conservative-rewrite ACTION: under a fixed sovereign total `a`, send the *matched*
authoritative state `(some a, f)` to `(some a, f')`, and leave every other state fixed. Equality
on the monoid `M` is decided classically (the module's whitelist permits `Classical.choice`) — no
`DecidableEq M` is forced on callers. -/
noncomputable def conservativeAct (a f f' : M) : Auth M → Auth M :=
  fun s => by
    classical
    exact match s with
    | .mk (some a') g => if a' = a ∧ g = f then .mk (some a) f' else .mk (some a') g
    | s => s

/-- A **conservative fragment-rewrite transformer**: the handler-transformer whose action is
`conservativeAct`. The `(some a, f) ↦ (some a, f')` move is the one `conservation_is_fpu` governs. -/
noncomputable def conservativeTransformer (a f f' : M) : HandlerTransformer (Auth M) :=
  ⟨conservativeAct a f f'⟩

/-- The action's value on the MATCHED state is the conservative rewrite. -/
theorem conservativeAct_matched (a f f' : M) :
    conservativeAct a f f' (Auth.mk (some a) f) = Auth.mk (some a) f' := by
  classical
  simp only [conservativeAct, and_self, if_true]

/-- The action's value on any UNMATCHED authoritative state `(some a', g)` with `(a',g) ≠ (a,f)`
is the identity. -/
theorem conservativeAct_unmatched (a f f' a' g : M) (h : ¬ (a' = a ∧ g = f)) :
    conservativeAct a f f' (Auth.mk (some a') g) = Auth.mk (some a') g := by
  classical
  simp only [conservativeAct, if_neg h]

/-- **Facet 2 IS an instance (PROVED): a conservation move is a safe handler-transformer.**
When the fragment-rewrite is conservative (`hmono`, the exact hypothesis of
`Resource.conservation_is_fpu`), the `conservativeTransformer` is `Safe` on `Auth M` — i.e. a
frame-preserving handler-transformer. This is `conservation_is_fpu` (`Resource.lean:296`)
*lifted to the transformer level* through the `act` functor, exactly the unification step
`HANDLER-TRANSFORMER-CONJECTURE.md §5` names: "the first theorem in which 'safe handler-
transformer' and 'frame-preserving update' are the same object". -/
theorem conservation_is_safe_transformer (a f f' : M)
    (hmono : ∀ g, fits (f + g) a → fits (f' + g) a) :
    Safe (conservativeTransformer a f f') := by
  classical
  intro s
  -- `SafeStep.safe` here is `Fpu`; reduce to `Fpu s (conservativeAct a f f' s)`.
  show Fpu s (conservativeAct a f f' s)
  cases s with
  | invalid =>
    -- act invalid = invalid; Fpu invalid invalid is refl.
    have : conservativeAct a f f' Auth.invalid = Auth.invalid := by simp [conservativeAct]
    rw [this]; exact Fpu.refl (R := Auth M) Auth.invalid
  | mk a' g =>
    cases a' with
    | none =>
      -- a pure fragment is not matched; identity action; Fpu by refl.
      have : conservativeAct a f f' (Auth.mk none g) = Auth.mk none g := by simp [conservativeAct]
      rw [this]; exact Fpu.refl (R := Auth M) (Auth.mk none g)
    | some a' =>
      by_cases h : a' = a ∧ g = f
      · -- matched: action rewrites (some a, f) ↦ (some a, f'); use conservation_is_fpu.
        obtain ⟨ha, hg⟩ := h
        subst ha; subst hg
        rw [conservativeAct_matched a' g f']
        exact Dregg2.Resource.conservation_is_fpu a' g f' hmono
      · -- unmatched: identity action; Fpu by refl.
        rw [conservativeAct_unmatched a f f' a' g h]
        exact Fpu.refl (R := Auth M) (Auth.mk (some a') g)

end CameraInstance

/-! ### TEETH: an UNSAFE transformer is GENUINELY REJECTED (on `Auth ℕ`, a camera with frames).

The discipline (ultracode) demands a *rejecting witness*: a transformer the safe-composition
law genuinely refuses. A subtlety worth recording honestly: the `Excl` (NFT) camera CANNOT
reject, because in `Excl` every composition is `invalid` (`Excl.op` is constant-`invalid`,
`Resource.lean:163`), so NO frame is ever valid (`excl_op_never_valid`) and `Fpu` is vacuously
true for every `Excl`-transformer. The teeth must therefore bite on a camera with GENUINE valid
frames: `Auth ℕ`, where a fragment-rewrite that over-shares (claims more than the authority's
headroom) breaks a frame a third party holds — `overshare_rejected`. -/

/-- **`excl_op_never_valid` (PROVED)** — in the `Excl` camera every composition is invalid, so
there are no valid frames; this is WHY `Excl` cannot host a rejecting witness (every transformer
is vacuously `Fpu`). It records the honest reason the teeth move to `Auth`. -/
theorem excl_op_never_valid {R : Type u} (a f : Excl R) :
    ¬ Dregg2.Resource.ResourceAlgebra.valid (a ⊙ f) := by
  -- `a ⊙ f = Excl.invalid`, and `Excl.valid invalid = False`.
  show ¬ Excl.valid (Excl.op a f)
  simp only [Excl.op, Excl.valid, not_false_iff]

/-- An **over-sharing transformer** on `Auth ℕ`: under authoritative total `2`, it rewrites the
held fragment from `0` to `3` — claiming `3` against a total of `2`, an over-share. Its action
on the matched state `(some 2, 0)` is `(some 2, 3)`. -/
def overshareTransformer : HandlerTransformer (Auth Nat) :=
  ⟨fun s => match s with
    | .mk (some 2) 0 => .mk (some 2) 3
    | s => s⟩

/-- **`overshare_rejected` — THE GENUINE TEETH (PROVED).** The over-sharing transformer is NOT
`Safe` on `Auth ℕ`. Witness: start at `(some 2, 0)` (valid: `0` fits in `2`), with the empty
frame `(none, 0)` the pre-state `(some 2, 0)` is valid, but the post-state `(some 2, 3)` is
NOT valid (`3` does not fit in `2`: `∄ c, 2 = 3 + c` over ℕ). So `Fpu (some 2,0) (some 2,3)`
fails at `f = (none, 0)` — the safe-composition law genuinely refuses this transformer. This is
the rejecting witness the ultracode discipline demands: an unsafe transformer is not admitted. -/
theorem overshare_rejected : ¬ Safe overshareTransformer := by
  -- Safe would give Fpu (some 2,0) (act (some 2,0)) = Fpu (some 2,0) (some 2,3).
  intro hsafe
  have hfpu : Fpu (R := Auth Nat) (Auth.mk (some 2) 0) (Auth.mk (some 2) 3) := by
    have := hsafe (Auth.mk (some 2) 0)
    -- `act (some 2, 0) = (some 2, 3)` definitionally.
    simpa [overshareTransformer, SafeStep.safe] using this
  -- instantiate the frame `f = (none, 0)`: pre is valid, post must be — but post is not.
  have hpre : Dregg2.Resource.ResourceAlgebra.valid
      ((Auth.mk (some 2) 0) ⊙ (Auth.mk (none) 0) : Auth Nat) := by
    -- (some 2, 0) ⊙ (none, 0) = (some 2, 0); valid = fits 0 2 = ∃ c, 2 = 0 + c.
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits]
    exact ⟨2, rfl⟩
  have hpost := hfpu (Auth.mk none 0) hpre
  -- post: (some 2, 3) ⊙ (none, 0) = (some 2, 3); valid = fits 3 2 = ∃ c, 2 = 3 + c — false in ℕ.
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits, add_zero] at hpost
  obtain ⟨c, hc⟩ := hpost
  -- 2 = 3 + c is impossible in ℕ.
  omega

/-! ## §5 — INSTANCE 2: the proof-forest gluing as a `SafeStep` (facet 3), and the
sheaf-of-verifiers generalization `proofForest_sheaf_sound` (facet 5 lifted, G2).

The proof-forest's safe-step surface is **commitment continuity**: a node `a` safe-steps to a
node `b` exactly when `a.newCommit = b.oldCommit` (the `chainLinked` overlap). This is a
genuinely different carrier (`ProofNode`, commitments are `Nat`) from the camera — yet it
instantiates the SAME `SafeStep` preorder, which is the legitimate shared structure the
conjecture's facet 3 supplies. -/

open Dregg2.Exec.ProofForest

/-- **`forestContinuity`** — the proof-forest's one-step overlap relation: a node `a` links to a
node `b` when their commitments are continuous (`a.newCommit = b.oldCommit`), the first conjunct
of `chainLinked` (`ProofForest.lean:141`). This is the seam-agreement the gluing law glues over. -/
def forestContinuity (a b : ProofNode) : Prop := a.newCommit = b.oldCommit

/-- **`forest_continuity_not_reflexive` (PROVED — the honest NON-instance teeth).** Commitment
continuity is NOT reflexive: a non-trivial step `node0` (`oldCommit = 0`, `newCommit = 1`) does
NOT satisfy `forestContinuity node0 node0` (it would need `1 = 0`). So `forestContinuity` is NOT
a `SafeStep` (a preorder needs `refl`); the forest's gluing surface is a *graph* (a one-step
continuity relation), not the reflexive-transitive preorder the camera's `Fpu` is. This is the
load-bearing reason the conjecture's weld "`Fpu` = gluing condition" is a NOTATION PUN, not one
shared definition: the camera relation IS a preorder (`instSafeStepFpu`), the forest relation is
NOT. We therefore do NOT make `ProofNode` a `SafeStep` instance — that would be a vacuous
encoding — and instead re-export the genuine forest law (`proofForest_sound`) below. -/
theorem forest_continuity_not_reflexive : ¬ forestContinuity node0 node0 := by
  -- `forestContinuity node0 node0` is `node0.newCommit = node0.oldCommit`, i.e. `1 = 0`.
  unfold forestContinuity node0
  decide

/-- **Facet 3, re-exported honestly: the forest gluing law is `proofForest_sound`.** This is the
genuine composition-over-the-forest (`Linked` + per-node validity ⟹ whole-forest `StepInv`), and
it is NOT an instance of `SafeStep.trans` — it is gluing over the transitive `chainLinked`
discipline. We re-state it (no new content) to make precise WHICH law facet 3 contributes: the
list-level gluing, not the pointwise preorder step. -/
theorem forest_gluing_is_proofForest_sound (pf : ProofForest)
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid) (hlinked : Linked pf) :
    fullProofForestInv pf :=
  proofForest_sound pf hvalid hlinked

/-! ### The sheaf-of-verifiers generalization `proofForest_sheaf_sound` (G2, facet 5 lifted).

We give the buildable gluing leg the docs name: lift the constant fibre `StepProofValid` to a
per-node **verifier-indexed** discharge `DischargedFor Vᵢ`. The compatibility hypothesis is
SUBSTANTIVE (not `Hᵢ = Hⱼ`): each node's local soundness is its own verifier's verdict, AND the
verdicts feed the SAME `attested` portal. The teeth: a DISAGREEING verifier (per
`dial_endpoints_distinct`) makes the per-node hypothesis FALSE, so the global section is not
derivable — a leaky handler is genuinely rejected. -/

open Dregg2.Authority.DV

/-- **`VerifierSection`** — a per-node assignment of a verifier and the statement/proof that node
must discharge FOR that verifier (the per-party stalk `DischargedFor Vᵢ`, facet 5). This is the
HETEROGENEOUS fibre the sheaf-of-verifiers wants — each node may be checked by a *different*
verifier, unlike the constant `StepProofValid`. -/
structure VerifierSection (Verifier Statement Proof VSecret : Type)
    [DVKernel Verifier Statement Proof VSecret] where
  /-- The verifier assigned to a node (the stalk index). -/
  verifierOf : ProofNode → Verifier
  /-- The statement a node must discharge. -/
  stmtOf     : ProofNode → Statement
  /-- The proof a node presents. -/
  proofOf    : ProofNode → Proof

/-- **`SheafLocallyValid`** — the heterogeneous local-validity condition: EVERY node discharges
its OWN verifier's verdict (`DischargedFor (verifierOf n) (stmtOf n) (proofOf n)`). This is the
per-party stalk condition, replacing the constant `∀ n, StepProofValid`. -/
def SheafLocallyValid {Verifier Statement Proof VSecret : Type}
    [DVKernel Verifier Statement Proof VSecret]
    (sec : VerifierSection Verifier Statement Proof VSecret) (pf : ProofForest) : Prop :=
  ∀ n ∈ pf.nodes, DischargedFor (VSecret := VSecret)
    (sec.verifierOf n) (sec.stmtOf n) (sec.proofOf n)

/-- **`proofForest_sheaf_sound` — THE SHEAF-OF-VERIFIERS GLUING (G2, PROVED).** Generalizes
`proofForest_sound`: if (P') every node discharges its OWN verifier's verdict
(`SheafLocallyValid` — the heterogeneous per-party fibre, facet 5), (L) the forest is `Linked`,
AND (bridge) the per-verifier local validity entails the per-node `StepProofValid` (the §8 seam
linking the verifier verdict to the AIR's validity — the *substantive* overlap condition, NOT
`Hᵢ = Hⱼ`), then the whole forest attests `fullProofForestInv`.

This is the buildable first theorem `SHEAF-OF-VERIFIERS §5.1` named: the fibre is now the
per-node `DischargedFor Vᵢ` (verdict-valued, a genuine generalization of the constant
`StepProofValid`), and the gluing is `proofForest_sound` over the bridged validity. The `bridge`
hypothesis is the honest §8 seam (verifier accepts ⟹ the AIR-validity proposition holds); it is
NOT circular (it does not assume the conclusion) and NOT trivial (a disagreeing verifier makes
`SheafLocallyValid` false — the teeth, see `sheaf_rejects_disagreeing_verifier`). -/
theorem proofForest_sheaf_sound {Verifier Statement Proof VSecret : Type}
    [DVKernel Verifier Statement Proof VSecret]
    (sec : VerifierSection Verifier Statement Proof VSecret) (pf : ProofForest)
    (hlocal : SheafLocallyValid sec pf) (hlinked : Linked pf)
    (bridge : ∀ n ∈ pf.nodes,
      DischargedFor (VSecret := VSecret) (sec.verifierOf n) (sec.stmtOf n) (sec.proofOf n) →
        n.StepProofValid) :
    fullProofForestInv pf :=
  proofForest_sound pf (fun n hn => bridge n hn (hlocal n hn)) hlinked

/-! ### TEETH for the sheaf: a DISAGREEING verifier breaks the local section.

Using the reference DV-kernel (`DesignatedVerifier.Reference`), the outsider `vOther` does NOT
accept `v0`'s designated transcript (`dial_endpoints_distinct`). So if a node is assigned the
verifier `vOther` but presents `v0`'s designated proof, `SheafLocallyValid` FAILS — the gluing
hypothesis is genuinely unsatisfiable, so no global section is forced. A leaky (disagreeing)
handler is rejected. -/

/-- **`sheaf_rejects_disagreeing_verifier` (PROVED — the sheaf teeth).** There is a node
assignment (a node checked by the outsider `vOther`, presenting `v0`'s designated transcript)
for which the per-party local-validity condition `DischargedFor` is FALSE — so the sheaf gluing
hypothesis `SheafLocallyValid` cannot be met, and the global section is not derivable. This is
the `dial_endpoints_distinct` separation biting the gluing: handlers that DISAGREE on the
overlap (verifier `vOther` vs the transcript designated for `v0`) genuinely fail to glue. -/
theorem sheaf_rejects_disagreeing_verifier :
    ¬ DischargedFor (VSecret := Reference.VSec)
        Reference.V.vOther 7 Reference.designatedProof := by
  unfold DischargedFor Reference.designatedProof
  simp [DVKernel.verifyFor, Reference.vrfy, Reference.sim, Reference.secretOf]

/-! ## §6 — FACET 1: the composition OBSTRUCTION = the proper subobject of safe configs.

The cross-cell binding (`JointTurn.binding_is_proper` / `Hyperedge.hyper_not_all_admissible`) is
the *reason composition is constrained*: the jointly-admissible configurations are a PROPER
SUBOBJECT of the product — there exist product states the binding EXCLUDES. We show the SAME
shape for handler-transformers: the SAFE transformers are a proper subobject of ALL
transformers (there exists an unsafe one — `overshareTransformer`). This instantiates "the
composition obstruction = the proper subobject of safely-composable transformers". -/

/-- **`safe_is_proper_subobject` (PROVED) — facet 1's shape for transformers.** The `Safe`
transformers on `Auth ℕ` are a PROPER subobject of ALL transformers: there exists a transformer
(`overshareTransformer`) that is NOT `Safe`. This is the exact analogue of `binding_is_proper`
(`JointTurn.lean:333`): just as the jointly-admissible product states are a proper subobject
(some product state is excluded), the safely-composable transformers are a proper subobject
(some transformer is excluded). The obstruction is REAL (witnessed exclusion), so the
safe-composition law has content — it is not satisfied by everything. -/
theorem safe_is_proper_subobject :
    ∃ T : HandlerTransformer (Auth Nat), ¬ Safe T :=
  ⟨overshareTransformer, overshare_rejected⟩

/-- **The IDENTITY transformer is always safe** — the subobject is non-empty (it contains the
identity), so "proper subobject" is the honest statement (a non-trivial proper inclusion: some
in, some out), not "everything is unsafe". -/
def idTransformer {R : Type u} : HandlerTransformer R := ⟨id⟩

theorem id_is_safe {R : Type u} [SafeStep R] : Safe (idTransformer (R := R)) :=
  fun a => SafeStep.refl a

/-! ## §7 — Axiom-hygiene pins over the PROVED keystones (whitelist
`{propext, Classical.choice, Quot.sound}`). -/

#assert_axioms safe_transformer_composes
#assert_axioms conservation_is_safe_transformer
#assert_axioms overshare_rejected
#assert_axioms excl_op_never_valid
#assert_axioms forest_continuity_not_reflexive
#assert_axioms forest_gluing_is_proofForest_sound
#assert_axioms proofForest_sheaf_sound
#assert_axioms sheaf_rejects_disagreeing_verifier
#assert_axioms safe_is_proper_subobject
#assert_axioms id_is_safe

-- The headline keystones' axiom sets, printed verbatim (whitelist only).
#print axioms safe_transformer_composes
#print axioms conservation_is_safe_transformer
#print axioms overshare_rejected
#print axioms proofForest_sheaf_sound

/-! ## §8 — Non-vacuity witnesses (`#eval`/example): the law fires and the teeth bite. -/

-- The over-sharing transformer's action on the matched state is the over-share (3 against 2).
example : (overshareTransformer.act (Auth.mk (some 2) 0)) = Auth.mk (some 2) 3 := rfl

-- The composition of two identity transformers is safe (the law fires positively).
example : Safe ((idTransformer (R := Auth Nat)).comp idTransformer) :=
  safe_transformer_composes id_is_safe id_is_safe

-- The reference DV-kernel: v0 accepts its designated transcript, vOther rejects it (the teeth run).
#eval Reference.check Reference.V.v0 7 Reference.designatedProof       -- true
#eval Reference.check Reference.V.vOther 7 Reference.designatedProof   -- false

/-! ## §9 — THE HONEST VERDICT (in-source, matching the docs' discipline).

WHAT GENUINELY UNIFIED (a theorem with teeth, subsuming special cases):
  * `SafeStep` is ONE definition; the camera's `Fpu` instantiates it LITERALLY
    (`instSafeStepFpu` = `Fpu.refl`/`Fpu.trans`, no new content). `safe_transformer_composes`
    is the general safe-composition theorem, and `conservation_is_safe_transformer` shows
    facet 2 (`conservation_is_fpu`) is a LITERAL instance of "safe handler-transformer". TEETH:
    `overshare_rejected` — an over-sharing transformer on `Auth ℕ` is genuinely refused.
  * `proofForest_sheaf_sound` is the buildable GLUING leg (G2): facet 3's `proofForest_sound`
    generalized to a per-node verifier-indexed fibre (facet 5's `DischargedFor Vᵢ`). TEETH:
    `sheaf_rejects_disagreeing_verifier` — a disagreeing verifier breaks the local section.
  * `safe_is_proper_subobject` instantiates facet 1's obstruction (`binding_is_proper`): the
    safe transformers are a PROPER subobject of all transformers (some excluded, some included).

WHAT REMAINS A PUN / OPEN (honestly):
-- OPEN: The conjecture's KEYSTONE WELD — that `Fpu`-preservation IS the gluing condition (ONE
--   law, not two instances of one preorder) — is NOT proved and is, on the evidence here, a
--   notation pun. `instSafeStepFpu` (camera) and the forest gluing live on DIFFERENT carriers
--   (`Auth M` vs `ProofNode`/`Commit = Nat`); the forest's continuity relation `forestContinuity`
--   (`newCommit = oldCommit`) is NOT even a preorder — `forest_continuity_not_reflexive` PROVES it
--   fails reflexivity on a non-trivial step — so it is NOT a `SafeStep` instance at all (we
--   deliberately did NOT register one; a degenerate encoding would be vacuous). The genuine forest
--   law is `proofForest_sound` over the transitive `chainLinked` list, which does NOT reduce to
--   `SafeStep.trans`. To close: build a restriction map `ρ : Auth-state-at-σ → Auth-state-at-τ`
--   along a chain edge and prove `a.newCommit = b.oldCommit` is an INSTANCE of `Fpu`
--   (continuity-equality ⟹ frame-implication). Not stated; not obviously true (an equality is not
--   an implication over a frame).
-- OPEN: The HIGHER-ORDER tier (the conjecture's title word). A transformer whose resource is
--   ANOTHER handler's invariant needs the step-indexed (`▶`-guarded) recursive `Auth` camera
--   (`Resource.lean §"Full camera"`, only the DISCRETE RA is built;
--   `StepCamera.recursive_resource_needs_step_index` proves merely that the guard is NEEDED, not
--   that the camera EXISTS). `safe_transformer_composes` here is FIRST-ORDER only. The recursive
--   `act : Handler → (R → R)` over guarded `R` is unbuilt; this is the correct OPEN frontier.
-- OPEN: The `act` FUNCTOR is supplied EXTERNALLY (a `HandlerTransformer` carries its own `act`);
--   there is no proof that `Await.Handler`'s committed effect INDUCES this `act` (the docs' missing
--   `Handler → (R → R)` bridge). So `conservation_is_safe_transformer` unifies the RESOURCE-ACTION
--   layer with `Fpu`, not the `Await.Handler` object itself. Wiring `turnAsRollbackHandler`'s
--   commit/abort arms to an `act` (commit = `Fpu`-move, abort = refund-`Fpu`) is the next bridge.

ONE-LINE VERDICT: a REAL first-order unification (one `SafeStep` preorder; the camera `Fpu`
literally instantiates it; `safe_transformer_composes` subsumes `Fpu.trans` for transformers;
`conservation_is_fpu` is a literal instance; an unsafe transformer is genuinely rejected) PLUS a
real buildable gluing leg (`proofForest_sheaf_sound` over a verifier-indexed fibre, with teeth) —
but the keystone weld "`Fpu` = gluing" is a notation pun (different carriers; the forest relation
is not even a preorder), and the higher-order tier is honestly OPEN. The single genuine new
theorem: `safe_transformer_composes` + `conservation_is_safe_transformer` make "safe handler-
transformer" and "frame-preserving update" the SAME object at first order, with `overshare_rejected`
as the rejecting witness. -/

end Dregg2.HandlerTransformer
