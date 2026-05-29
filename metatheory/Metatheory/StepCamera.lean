/-
# Metatheory.StepCamera — the step-indexed Iris camera: promoting the discrete RA.

`Resource.lean` builds the **discrete** resource-algebra tier: a partial commutative
monoid `(op, valid, core)` carving out NFTs, fractional permissions, the
authoritative↔fragment split. A discrete RA suffices as long as a resource's validity
talks only about *itself* (a field sum, a `≤ 1` share, a `f ≼ a` fit). It does NOT
suffice the moment a resource makes a statement about *another cell's* state.

## Why dregg2 needs step-indexing (the motivation)
A dregg2 cell can hold a capability whose validity quantifies over a **different cell's
invariant** — "this cap is valid only while cell `Y` maintains property `Q`", where `Q`
itself ranges over resources (including, transitively, caps back into this cell). That is
**higher-order / recursive ghost state**: the domain of resources `R` would have to
contain predicates over `R`, a negative self-reference (`R ≅ … → Prop R …`) with no
solution in plain `Set`/`Type` (cardinality / Reynolds). A *discrete* RA cannot host it.

Iris's resolution (Jung et al., *Iris from the Ground Up*, JFP 2018, §3–4) is to give the
resource carrier the structure of an **OFE** — an ordered family of equivalences,
`x ≡{n}≡ y` ("equal for `n` steps of observation") — and to make `op`/`core` and validity
**step-indexed and non-expansive**. The recursive domain equation is then solved as a
**guarded fixpoint** (`iProp ≅ ▶ (… → iProp …)`), where every recursive occurrence sits
under a *later* `▶`. The step-index decrement at `▶` is what makes the otherwise-circular
definition well-founded: at index `n` a resource only ever inspects its recursive parts at
index `< n` (Birkedal et al., *guarded dependent type theory* / the `▷` modality;
América–Rutten metric-space fixpoints).

**This `▶` is the SAME "later" as `Boundary.lean`'s guard.** `Boundary.Later` guards the
tail of a cell's coinductive unfold (productivity over unbounded time, typed off
`previous_receipt_hash`); the camera's `▶` guards the recursive occurrence of resources
inside that unfold (well-definedness of higher-order ghost state). They are one modality —
which is exactly how Iris builds `iProp` as a guarded fixpoint *over the camera of
resources*: the coinductive cell (`νF`) and the recursive resource live under the same
`▷`. A `dregg2` cell that reasons about another cell's future is reasoning one `▶`-step
out, and the resource it holds about that future is one `▶`-step "smaller" — the two
decrements are the same decrement.

## What is here
* `OFE` — the step-indexed equivalence structure (the metric/ultrametric on resources).
* `Later` — `x ≡{n}≡ y` "one step later" (`▷`), tied to `Boundary.Later`.
* `NonExpansive` — maps that preserve `≡{n}≡` (the morphisms of OFEs).
* `Camera` — `ResourceAlgebra` + `OFE` + step-indexed `validN` + non-expansive
  `op`/`core` + the **extension axiom** (the laws beyond the discrete RA).
* `discrete_camera_of_RA` — every discrete RA is a camera under the trivial OFE
  (`≡{n}≡` = `=`); the discrete tier of `Resource.lean` is the `n`-collapsed special case.
* a design note pinning the higher-order obligation that forces all of the above.

Style: spec-first, grind up — faithful Props, `sorry` bodies; data defined where cheap.
-/
import Metatheory.Resource
import Metatheory.Boundary

namespace Metatheory.StepCamera

universe u v

/-! ## `OFE` — ordered family of equivalences (the step-indexing) -/

/-- **An ordered family of equivalences (OFE)** on `α`: a family of equivalence relations
`Eqv n : α → α → Prop` indexed by an observation depth `n : Nat`, the discrete analogue of
an (ultra)metric. `x ≡{n}≡ y` reads "`x` and `y` are indistinguishable by any observer that
runs for `n` steps". The four laws make this an OFE in the sense of Jung et al. (JFP 2018,
§3.1):

* each `Eqv n` is an **equivalence relation** (refl/symm/trans) — at every depth,
  indistinguishability is a genuine equivalence;
* **downward closure** (`Eqv (n+1) x y → Eqv n x y`) — more observation steps is a finer
  relation; coarser at shallower depth;
* the **limit property** (`(∀ n, Eqv n x y) → x = y`) — indistinguishable at *every* depth
  ⇒ equal (the OFE is *separated*; the only "ideal points" are real points).

Note: there is deliberately **no `Eqv 0`-totality axiom**. Iris's `dist 0` is total only in
the *step-indexed* OFE construction (where `dist n` is built by a decreasing approximation),
not as a law of the OFE structure itself: an OFE requires only that each `dist n` be an
equivalence, downward closure, and the limit (Jung et al. JFP 2018, §3.1, Def. 3.1 — the
`dist`-laws are reflexivity-as-equivalence + mono + limit). Demanding `Eqv 0 x y` for *all*
`x y` would exclude the **discrete OFE** (`Eqv n := Eq` at every depth), which is the very
embedding `discrete_camera_of_RA` builds — and would force the camera's raw-`Eq`
conclusions (`core_nonExpansive`, `extend`) to fail at `n = 0`. So the totality is dropped
as the non-axiom it is; `Later 0 := True` (below) still gives the contractive base case.

This step-indexing is precisely what makes recursive / higher-order resources
well-defined: a resource at depth `n` may inspect its recursive sub-resources only at
depth `< n`, so the would-be-circular domain equation is solved as a guarded fixpoint. -/
class OFE (α : Type u) where
  /-- `Eqv n x y` — `x ≡{n}≡ y`, indistinguishable by an `n`-step observer. -/
  Eqv : Nat → α → α → Prop
  /-- Each `Eqv n` is reflexive. -/
  eqv_refl  : ∀ n x, Eqv n x x
  /-- Each `Eqv n` is symmetric. -/
  eqv_symm  : ∀ n {x y}, Eqv n x y → Eqv n y x
  /-- Each `Eqv n` is transitive. -/
  eqv_trans : ∀ n {x y z}, Eqv n x y → Eqv n y z → Eqv n x z
  /-- Downward closure: finer at greater depth. -/
  eqv_mono  : ∀ n {x y}, Eqv (n + 1) x y → Eqv n x y
  /-- Separation / the limit property: agreement at every depth is equality. -/
  eqv_limit : ∀ {x y}, (∀ n, Eqv n x y) → x = y

namespace OFE
@[inherit_doc] scoped notation:50 x " ≡{" n "}≡ " y => OFE.Eqv n x y
end OFE

open OFE

/-- `Later n x y` — `x ≡{n}≡ y` **"one step later"** (`▷`): equality "now" at depth `n`
demands agreement at depth `n - 1`. At `n = 0` it is trivially true (the future beyond a
zero-step observer is unconstrained — the contractive base case); at `n + 1` it is `Eqv n`.
Decrementing the index is what gives a *contractive* (well-founded) recursive occurrence.

This is the camera-tier reflection of `Boundary.Later`: that `▶` guards the tail of a
cell's coinductive unfold; this `▶` guards the recursive occurrence of resources inside
that unfold. The decrement here (`n + 1 ↦ n`) is the SAME `▶`-step as the guard that makes
`Boundary`'s `IsBisim`/`BoundaryRespecting` productive — Iris's one `▷`, shared by the
coinductive cell `νF` and the recursive resource living in it. -/
def Later {α : Type u} [OFE α] : Nat → α → α → Prop
  | 0,     _, _ => True
  | n + 1, x, y => Eqv n x y

/-- `▷` agreement is implied by present agreement: if `x ≡{n}≡ y` then `x` and `y` also
agree one step later (the future is no more demanding than the present — `▷`-introduction,
monotonicity of `Later` against `Eqv`). -/
theorem later_of_eqv {α : Type u} [OFE α] (n : Nat) {x y : α}
    (h : Eqv n x y) : Later n x y := by
  -- PROVED: case on `n`; `Later 0` is `True`, `Later (n+1)` is `Eqv n` (use `eqv_mono`).
  cases n with
  | zero => simp [Later]
  | succ m => simpa [Later] using OFE.eqv_mono m h

/-! ## `NonExpansive` — the morphisms of OFEs -/

/-- **`f` is non-expansive**: it preserves `n`-step indistinguishability for every `n`
(`x ≡{n}≡ y → f x ≡{n}≡ f y`). Non-expansive maps are the morphisms of the category of
OFEs; in a camera, `op` (in each argument) and `core` must be non-expansive so that the
guarded fixpoint that builds `iProp` lands in OFEs at every stage (Jung et al. §3.1,
§4.2). Intuitively: an operation cannot let an observer *gain* distinguishing power it did
not already have on the inputs. -/
def NonExpansive {α : Type u} {β : Type v} [OFE α] [OFE β] (f : α → β) : Prop :=
  ∀ n x y, Eqv n x y → Eqv n (f x) (f y)

/-- A non-expansive map respects the `▷` modality too: `Later`-agreement of inputs gives
`Later`-agreement of outputs (`f` commutes with `▶`). Used when threading non-expansive
operations through guarded recursive definitions. -/
theorem nonExpansive_later {α : Type u} {β : Type v} [OFE α] [OFE β]
    {f : α → β} (hf : NonExpansive f) (n : Nat) {x y : α}
    (h : Later n x y) : Later n (f x) (f y) := by
  -- PROVED: case on `n`; `Later 0` is `True`, `Later (n+1)` is `Eqv n` (apply `hf`).
  cases n with
  | zero => simp [Later]
  | succ m => exact hf m x y h

/-! ## `Camera` — the FULL Iris camera (discrete RA + OFE + step-indexed validity) -/

/-- **A camera (Iris `cmra`)** — the FULL resource structure: a discrete
`ResourceAlgebra` *and* an `OFE`, glued by a **step-indexed validity** `validN n a`
(`✓{n} a`, "`a` is valid for `n` observation steps") plus the non-expansiveness and
extension laws that the discrete RA lacks. This is the tier dregg2 needs for higher-order /
recursive ghost state (caps that quantify over another cell's invariant); the discrete RA
of `Resource.lean` is the `n`-collapsed special case (`discrete_camera_of_RA`).

The fields beyond the discrete RA (Jung et al. JFP 2018, §4.1, Def. of `CMRA`):

* `validN_mono` — `✓{n}` is **downward-closed in `n`**: validity for more steps implies
  validity for fewer (a resource cannot become valid by observing it *longer*);
* `valid_iff_validN` — the discrete `valid` is the **limit** of `validN`: `✓ a ↔ ∀ n, ✓{n} a`
  (a resource is "really" valid iff it is valid at every finite depth);
* `validN_eqv` — `✓{n}` respects `≡{n}≡` (validity is itself non-expansive: `n`-equal
  resources are `n`-equally valid);
* `op_nonExpansive_r` / `core_nonExpansive` — `op` (in its right argument; left follows by
  commutativity of the underlying RA) and `core` are **non-expansive**;
* `extend` — the **EXTENSION axiom**, the camera's keystone and the one law with no
  discrete analogue: if `a` is `n`-valid and looks (at depth `n`) like a composite
  `op b1 b2`, then `a` *actually decomposes* as `op c1 c2` with `c1 ≡{n}≡ b1`,
  `c2 ≡{n}≡ b2`. It lets you split a resource along an approximate (step-`n`) decomposition
  into a *real* one — the property that makes the later-eliminated `iProp` separation
  conjunction commute with the step-index, and without which the guarded fixpoint would
  not respect `op`. -/
class Camera (R : Type u) extends
    Metatheory.Resource.ResourceAlgebra R, OFE R where
  /-- Step-indexed validity `✓{n} a`. -/
  validN : Nat → R → Prop
  /-- `✓{n}` is downward-closed in `n`. -/
  validN_mono : ∀ n a, validN (n + 1) a → validN n a
  /-- The discrete `valid` is the limit of `validN`. -/
  valid_iff_validN : ∀ a : R, toResourceAlgebra.valid a ↔ ∀ n, validN n a
  /-- `✓{n}` respects `≡{n}≡` (validity is non-expansive). -/
  validN_eqv : ∀ n (a b : R), toOFE.Eqv n a b → validN n a → validN n b
  /-- `op` is non-expansive in its right argument (left by RA-commutativity):
  `b ≡{n}≡ b' → op a b ≡{n}≡ op a b'`. -/
  op_nonExpansive_r : ∀ (a : R) n (b b' : R),
    toOFE.Eqv n b b' → toOFE.Eqv n (toResourceAlgebra.op a b) (toResourceAlgebra.op a b')
  /-- `core` is non-expansive (as a map `R → Option R`, pointwise `Eqv` on the option). -/
  core_nonExpansive : ∀ n (a b : R), toOFE.Eqv n a b →
    (toResourceAlgebra.core a = none ↔ toResourceAlgebra.core b = none) ∧
    (∀ ca cb, toResourceAlgebra.core a = some ca →
      toResourceAlgebra.core b = some cb → toOFE.Eqv n ca cb)
  /-- **The extension axiom.** An `n`-valid resource matching an approximate decomposition
  has a genuine one refining it (Jung et al. §4.1). -/
  extend : ∀ n (a b1 b2 : R), validN n a →
    toOFE.Eqv n a (toResourceAlgebra.op b1 b2) →
    ∃ c1 c2, a = toResourceAlgebra.op c1 c2 ∧
      toOFE.Eqv n c1 b1 ∧ toOFE.Eqv n c2 b2

/-! ## The discrete embedding: a discrete RA is the `n`-collapsed camera -/

/-- **The trivial (discrete) OFE on any type**: `x ≡{n}≡ y ≜ x = y` at **every** depth,
including `n = 0`. Every OFE law holds: each `Eqv n` is `Eq` (an equivalence); downward
closure is immediate (`Eq → Eq`); and the limit is trivial (any single `Eqv n` already
gives `x = y`). This is the faithful discrete OFE (Jung et al. JFP 2018, §4.1 "discrete
cmra"): with no `Eqv 0`-totality axiom (see `OFE`), `Eqv := Eq` is admissible at all
depths, which is exactly what makes the camera's raw-`Eq` conclusions (`core_nonExpansive`,
`extend`) discharge at `n = 0`. Used to embed `Resource.lean`'s discrete RAs as cameras. -/
def discreteEqv {α : Type u} : Nat → α → α → Prop
  | _, x, y => x = y

/-- **Every discrete resource algebra is a camera** under the discrete OFE
(`x ≡{n}≡ y` ≜ `discreteEqv n x y`) with `validN n a ≜ valid a` for `n ≥ 1`. This is the
*discrete embedding* (Jung et al. §4.1: every "discrete cmra"/RA is a cmra): the
step-index does nothing, `validN` collapses to `valid`, non-expansiveness is by
substitution, and the extension axiom is just associativity/decomposition with the
`≡{n}≡` read as `=`. It exhibits `Resource.lean`'s discrete tier as the `n`-collapsed
special case of the full camera — the bottom rung of the same ladder.

`sorry`'d: the discharge is bookkeeping (the `n = 0` totality split of `discreteEqv`, then
`Eq`-substitution for the remaining laws), but it requires constructing the full `OFE` and
`Camera` instance fields, which we leave as the obligation. -/
theorem discrete_camera_of_RA (R : Type u)
    [Metatheory.Resource.ResourceAlgebra R] :
    Nonempty (Camera R) := by
  -- PROVED (no restriction on `R`). With the `eqv_zero`-totality non-axiom dropped from
  -- `OFE`, the faithful discrete OFE `Eqv n := Eq` (`discreteEqv`) is admissible at EVERY
  -- depth, including `n = 0`. Then every camera field reads through `=`:
  --   * the OFE laws are `Eq` refl/symm/trans/mono/limit (the last from any single `n`);
  --   * `validN _ := valid` makes `validN_mono`/`valid_iff_validN`/`validN_eqv` trivial;
  --   * `op_nonExpansive_r`/`core_nonExpansive` are `Eq`-congruence (substitute `b = b'`,
  --     `a = b`) — NO constant-core assumption needed, the raw-`Eq` conclusion holds because
  --     the hypothesis IS the equality;
  --   * `extend` at depth `n` has hypothesis `a = op b1 b2`, so `c1 := b1`, `c2 := b2`
  --     witnesses it directly — NO unit / decomposition needed, the approximate
  --     decomposition is already exact under `Eqv := Eq`.
  -- The previous swarm's blocker was entirely the `eqv_zero := True` totality (now removed),
  -- which had forced `Eqv 0 := True` and unguarded the two raw-`Eq` conclusions at `n = 0`.
  refine ⟨{
    -- inherited `ResourceAlgebra R` fields:
    op    := Metatheory.Resource.ResourceAlgebra.op
    valid := Metatheory.Resource.ResourceAlgebra.valid
    core  := Metatheory.Resource.ResourceAlgebra.core
    op_comm  := Metatheory.Resource.ResourceAlgebra.op_comm
    op_assoc := Metatheory.Resource.ResourceAlgebra.op_assoc
    valid_op_left := Metatheory.Resource.ResourceAlgebra.valid_op_left
    core_id   := Metatheory.Resource.ResourceAlgebra.core_id
    core_idem := Metatheory.Resource.ResourceAlgebra.core_idem
    core_mono := Metatheory.Resource.ResourceAlgebra.core_mono
    -- the discrete OFE (`Eqv n := Eq` at every depth):
    Eqv := discreteEqv
    eqv_refl  := fun _ _ => rfl
    eqv_symm  := fun _ {_ _} h => h.symm
    eqv_trans := fun _ {_ _ _} h1 h2 => h1.trans h2
    eqv_mono  := fun _ {_ _} h => h
    eqv_limit := fun {_ _} h => h 0
    -- step-indexed validity collapses to `valid`:
    validN := fun _ a => Metatheory.Resource.ResourceAlgebra.valid a
    validN_mono := fun _ _ h => h
    valid_iff_validN := fun _ => ⟨fun h _ => h, fun h => h 0⟩
    validN_eqv := fun _ _ _ (h : _ = _) hv => h ▸ hv
    -- non-expansiveness is `Eq`-congruence:
    op_nonExpansive_r := fun _ _ _ _ (h : _ = _) => h ▸ rfl
    core_nonExpansive := fun _ a b (h : a = b) => by
      subst h
      refine ⟨Iff.rfl, fun ca cb hca hcb => ?_⟩
      rw [hca] at hcb
      exact (Option.some.injEq _ _ ▸ hcb : ca = cb)
    -- extension is exact under `Eqv := Eq`: the hypothesis already gives the decomposition.
    extend := fun _ a b1 b2 _ (h : a = _) => ⟨b1, b2, h, rfl, rfl⟩
  }⟩

/-! ## The higher-order obligation that forces step-indexing -/

/-- **`recursive_resource_needs_step_index` — the design obligation in one Prop.** A dregg2
resource is *higher-order* when its validity quantifies over a predicate on resources of
the *same* algebra (a cap whose validity asserts another cell maintains an invariant `Q`,
where `Q : R → Prop`). This statement says: for such a validity predicate to be
**non-expansive** (hence to live in a camera and admit a guarded fixpoint), the inner
quantification must be guarded — it may only inspect the argument *one `▶`-step later*
(`Later n`), never `Eqv n` directly.

Concretely: if `v : R → Prop` is built from an invariant `Q` over `R` (`hbuilt`), then `v`
is non-expansive at depth `n` only when `Q` is fed `▶`-guarded (later) inputs — i.e. a
self-referential validity is well-defined ONLY under the OFE's `Later`. A *discrete* RA
(where `Later n` would collapse to `Eqv n` with no decrement) cannot satisfy this for a
genuinely recursive `Q`: that is the precise sense in which "a cell making statements about
another cell's state needs step-indexing." The `sorry` marks the obligation to exhibit such
a guarded `v` (the guarded fixpoint construction) for dregg2's actual cross-cell-invariant
caps. -/
theorem recursive_resource_needs_step_index {R : Type u} [OFE R]
    (Q : R → Prop)
    (v : R → Prop)
    (hbuilt : ∀ x, v x ↔ ∀ y, Later (α := R) 0 x y → Q y) :
    (∀ n x y, Eqv n x y → (v x ↔ v y)) := by
  -- PROVED: `Later 0` is `True` by definition, so `hbuilt` makes `v x ↔ ∀ y, Q y`, an
  -- x-independent proposition; hence `v` is constant and `v x ↔ v y` for all x, y.
  -- (This is the degenerate base case: with the guard collapsed to `True`, `v` cannot
  -- depend on its argument, which is exactly why a genuine recursive `Q` needs a real
  -- `Later n` decrement — the obligation flagged in the docstring lives at `n ≥ 1`.)
  intro n x y _hxy
  rw [hbuilt x, hbuilt y]
  simp only [Later]

end Metatheory.StepCamera
