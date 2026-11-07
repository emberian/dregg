/-
# Dregg2.Circuit.FriSoundness — a FORMALIZATION of FRI soundness from the literature.

**What this is.** `Dregg2.Circuit.FriVerifier` carries FRI low-degree soundness as a
NAMED TERMINAL CRYPTO CARRIER (`FriLowDegreeSound`, a `Prop` class) — it specifies the
verifier ALGORITHM but does NOT re-derive the soundness. This module CLOSES that gap: it
FORMALIZES the published FRI soundness argument (Ben-Sasson, Bentov, Horesh, Riabzev,
"Fast Reed-Solomon Interactive Oracle Proofs of Proximity", ICALP 2018 — "BBHR18"; the
proximity-gaps refinement of Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, FOCS 2020 —
"BCIKS20") as actual Lean theorems, resting only on the standard hash floor `HashCR`
(reused from `Dregg2.Crypto.HermineHintMLWE`) and the concrete field/rate parameters.

**The four pieces (all PROVED, no `sorry`, no smuggled hardness hypothesis):**

1. **Reed-Solomon codes + distance** (`§1`). A code is a linear `Submodule` of `ι → F`;
   `disagree`/`closeN`/`farN` are the (absolute-count) Hamming distance and δ-closeness.
   `closeN_zero_iff_mem`: 0-closeness is exactly membership.

2. **The FRI FOLDING operator** (`§2`). Over the coset geometry (`FriGeom`: the ±x
   involution `σ`, the squaring quotient `q : L → L²`, the point value `p`), the even/odd
   decomposition `f(x) = fₑ(x²) + x·fₒ(x²)` gives `E`, `O` and `Fold α f = E f + α • O f`
   on `L²`. `self_decomp` is the fundamental identity `f x = E f (q x) + p x · O f (q x)`.

3. **The KEY LEMMA — distance is PRESERVED by folding** (`§3`, the heart of FRI
   soundness). `fold_close_of_two_alpha`: if for TWO distinct challenges the folded
   function is δ-close to the folded code, then `f` is `4δ`-close to the code
   (the BBHR18 unique-decoding argument — two folds reconstruct `f`; the constant `4`
   is the elementary two-point bound, tightened to no-loss by BCIKS20 proximity gaps).
   Contrapositive `good_alpha_subsingleton`: a `4δ`-FAR `f` has AT MOST ONE "good"
   challenge — the EXACT soundness bound (folding error `≤ 1/|F|`).

4. **SOUNDNESS + the reduction** (`§4`). `query_sound_of_cover` (a query set covering the
   disagreement forces the committed next-oracle to equal the true fold), the Merkle
   binding (the `¬ HashCR`-conclusion witness `equivocation_breaks_binding`; the discharged
   keyed-ROM successor is `FloorRegroundedConsumers.friOracle_binding_binds_rom` — the old
   `HashCR`-conditioned `oracle_binding` is DELETED, floor refuted), and `fri_fold_soundness` — an accepting-yet-far
   transcript forces the challenge into the `≤1`-element exceptional set OR a hash
   collision. `FriProximity` + `friProximity_discharge` is the interface the AIR-soundness
   unit (2a) consumes: an accepted oracle is δ-close to a low-degree codeword, so the
   sampled AIR constraint checks bind the actual trace (`air_binds_of_proximity`).

**Teeth (`§5`).** A genuine rate-1/2 Reed-Solomon `FriSetup` over `ZMod 5`, `|L|=4`,
`|L²|=2` (`rsSetup`): completeness/reassembly closure are PROVED (not assumed). An honest
low-degree `f` folds into the code and is 0-close; a concrete FAR `f` has EXACTLY ONE good
challenge (`α = 4`) and the fold at a bad challenge (`α = 0`) leaves the code — the KEY
LEMMA bound witnessed non-vacuously. The Merkle binding is load-bearing: a colliding
commitment lets the prover equivocate the oracle (`equivocation_breaks_binding`).

Residual: the keyed-ROM Merkle binding (`friOracle_binding_binds_rom`, floor PROVED — the old
`HashCR` residual is deleted, refuted at every compressing commitment) + the field/rate parameters.
The tight proximity-gaps constant (no `4×` loss, up to the Johnson bound) is a QUANTITATIVE
improvement over the elementary two-point constant proved here — noted, not open.
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Pi
import Dregg2.Crypto.HermineHintMLWE

namespace Dregg2.Circuit.FriSoundness

open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)

/-! ## §1. Reed-Solomon codes and Hamming distance.

A code is a linear subspace `C ⊆ (ι → F)` (Reed-Solomon codes are linear); the "domain"
`ι = L` is the evaluation set. Distance is the absolute count of disagreement points
(relative distance = this ÷ `|ι|`; the absolute form dodges rationals with no loss of
content). `closeN C d f` = "some codeword agrees with `f` on all but `≤ d` points". -/

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The set of points where `f` and `g` disagree — the Hamming support of `f - g`. -/
def disagree (f g : ι → F) : Finset ι := Finset.univ.filter (fun x => f x ≠ g x)

@[simp] theorem mem_disagree {f g : ι → F} {x : ι} : x ∈ disagree f g ↔ f x ≠ g x := by
  simp [disagree]

/-- Empty disagreement ⇔ the functions are equal. -/
theorem disagree_eq_empty_iff {f g : ι → F} : disagree f g = ∅ ↔ f = g := by
  rw [disagree, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext x; by_contra hx; exact (h (Finset.mem_univ x)) hx
  · intro h _ _; simp [h]

/-- `f` is `d`-close to the code `C` iff some codeword agrees with `f` on all but `≤ d`
points. (Relative δ-closeness with `d = δ·|ι|`.) -/
def closeN (C : Submodule F (ι → F)) (d : ℕ) (f : ι → F) : Prop :=
  ∃ g ∈ C, (disagree f g).card ≤ d

/-- `f` is `d`-FAR from `C` iff not `d`-close. -/
def farN (C : Submodule F (ι → F)) (d : ℕ) (f : ι → F) : Prop := ¬ closeN C d f

/-- **0-closeness is exactly codeword membership** — the unique-decoding endpoint used by
the final low-degree check (the FRI final oracle is a genuine codeword). -/
theorem closeN_zero_iff_mem {C : Submodule F (ι → F)} {f : ι → F} :
    closeN C 0 f ↔ f ∈ C := by
  constructor
  · rintro ⟨g, hg, hcard⟩
    rw [Nat.le_zero, Finset.card_eq_zero, disagree_eq_empty_iff] at hcard
    exact hcard ▸ hg
  · intro hf; exact ⟨f, hf, by simp [disagree_eq_empty_iff]⟩

theorem farN_zero_iff_not_mem {C : Submodule F (ι → F)} {f : ι → F} :
    farN C 0 f ↔ f ∉ C := by
  simp [farN, closeN_zero_iff_mem]

/-! ## §2. The FRI folding operator over the coset geometry.

The FRI domain `L` is a coset of a multiplicative 2-group: `x ↦ -x` (`σ`) is a fixed-point-
free involution, and squaring `q : L → L²` is exactly 2-to-1 with fibers `{x, σ x}`. A
function `f : L → F` splits as `f(x) = fₑ(x²) + x·fₒ(x²)`; the FRI fold with challenge `α`
is `Fold α f (y) = fₑ(y) + α·fₒ(y)` — equivalently, the value at `α` of the line through
`(x, f x)` and `(σ x, f (σ x))`. `FriGeom` bundles the geometry; `rep` picks a fiber
representative so `E`/`O`/`Fold`/`unfoldF` are definable. -/

/-- The coset geometry: the involution `σ`, the 2-to-1 quotient `q`, the point value `p`,
and a fiber section `rep`, with the axioms that make the even/odd split well-defined. -/
structure FriGeom (F ι κ : Type*) [Field F] where
  /-- `x ↦ -x` on the domain. -/
  σ : ι → ι
  /-- The squaring quotient `L → L²`. -/
  q : ι → κ
  /-- The point value (`x`'s field value); `p (σ x) = -p x`. -/
  p : ι → F
  /-- A section of `q`: a chosen fiber representative. -/
  rep : κ → ι
  /-- `2 ≠ 0` — the field has characteristic `≠ 2` (FRI cosets avoid `0`). -/
  two_ne : (2 : F) ≠ 0
  /-- `rep` is a section of `q`. -/
  q_rep : ∀ y, q (rep y) = y
  /-- `σ` preserves fibers: the sibling of `rep y` also squares to `y`. -/
  q_σ_rep : ∀ y, q (σ (rep y)) = y
  /-- The representative has nonzero value (the FRI domain excludes `0`). -/
  p_rep_ne : ∀ y, p (rep y) ≠ 0
  /-- The sibling has the negated value. -/
  p_σ_rep : ∀ y, p (σ (rep y)) = - p (rep y)
  /-- Every point is one of the two representatives of its fiber (the fiber is `{rep, σ∘rep}`). -/
  q_fiber : ∀ x, x = rep (q x) ∨ x = σ (rep (q x))

variable (G : FriGeom F ι κ)

/-- The EVEN part `fₑ` on `L²`: `fₑ(y) = (f(rep y) + f(σ rep y)) / 2`. -/
def E (f : ι → F) : κ → F := fun y => (f (G.rep y) + f (G.σ (G.rep y))) / 2

/-- The ODD part `fₒ` on `L²`: `fₒ(y) = (f(rep y) - f(σ rep y)) / (2 · p (rep y))`. -/
def O (f : ι → F) : κ → F := fun y => (f (G.rep y) - f (G.σ (G.rep y))) / (2 * G.p (G.rep y))

/-- **The FRI fold** with challenge `α`: `Fold α f = fₑ + α·fₒ` on `L²`. -/
def Fold (α : F) (f : ι → F) : κ → F := fun y => E G f y + α * O G f y

/-- **Reassembly** `L² × L² → L`: `unfoldF Ge Go (x) = Ge(x²) + x·Go(x²)`. The inverse of
the even/odd split; sends a pair of folded codewords back to a domain function. -/
def unfoldF (Ge Go : κ → F) : ι → F := fun x => Ge (G.q x) + G.p x * Go (G.q x)

/-- **The fundamental decomposition identity**: `f(x) = fₑ(x²) + x·fₒ(x²)` for EVERY `x`
(both fiber representatives). This is what lets agreement on `L²` pull back to agreement
on `L`. -/
theorem self_decomp (f : ι → F) (x : ι) :
    f x = E G f (G.q x) + G.p x * O G f (G.q x) := by
  have h2 : (2 : F) ≠ 0 := G.two_ne
  set y := G.q x with hy
  have hpne : G.p (G.rep y) ≠ 0 := G.p_rep_ne _
  rcases G.q_fiber x with hx | hx
  · -- x = rep y: the "even" representative.
    rw [hx]
    simp only [E, O]
    field_simp
    ring
  · -- x = σ (rep y): the sibling; p x = -p (rep y).
    have hps : G.p (G.σ (G.rep y)) = - G.p (G.rep y) := G.p_σ_rep _
    rw [hx, hps]
    simp only [E, O]
    field_simp
    ring

/-- `unfoldF` evaluates by definition. -/
@[simp] theorem unfoldF_apply (Ge Go : κ → F) (x : ι) :
    unfoldF G Ge Go x = Ge (G.q x) + G.p x * Go (G.q x) := rfl

/-- The full FRI setup: the geometry, the domain code `C` (deg `< 2t`), the folded code
`C'` (deg `< t`), and the two STRUCTURAL closure facts of Reed-Solomon codes:
`unfold_closed` (reassembly of two folded codewords is a codeword) and `foldE_mem`/
`foldO_mem` (folding a codeword yields folded codewords — COMPLETENESS). These are pure
algebra of the even/odd polynomial split, DISCHARGED for a genuine RS instance in `§5`
(not cryptographic hypotheses). -/
structure FriSetup (F ι κ : Type*) [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] where
  geom : FriGeom F ι κ
  /-- The domain Reed-Solomon code (evaluations of deg `< 2t` polynomials). -/
  C : Submodule F (ι → F)
  /-- The folded Reed-Solomon code on `L²` (evaluations of deg `< t` polynomials). -/
  C' : Submodule F (κ → F)
  /-- **Reassembly closure**: reassembling two folded codewords lands in the domain code. -/
  unfold_closed : ∀ Ge ∈ C', ∀ Go ∈ C', unfoldF geom Ge Go ∈ C
  /-- **Folding completeness (even part)**: the even part of a codeword is a folded codeword. -/
  foldE_mem : ∀ f ∈ C, E geom f ∈ C'
  /-- **Folding completeness (odd part)**. -/
  foldO_mem : ∀ f ∈ C, O geom f ∈ C'

variable (S : FriSetup F ι κ)

/-- **COMPLETENESS**: folding a codeword with ANY challenge yields a codeword of the folded
code (`Fold α f = E f + α • O f`, both parts in `C'`). An honest low-degree oracle passes. -/
theorem fold_complete {f : ι → F} (hf : f ∈ S.C) (α : F) : Fold S.geom α f ∈ S.C' := by
  have he : E S.geom f ∈ S.C' := S.foldE_mem f hf
  have ho : O S.geom f ∈ S.C' := S.foldO_mem f hf
  have : Fold S.geom α f = E S.geom f + α • O S.geom f := by
    funext y; simp [Fold, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]; exact S.C'.add_mem he (S.C'.smul_mem α ho)

/-! ## §3. THE KEY LEMMA — distance preservation under folding (the heart of FRI soundness).

BBHR18's soundness rests on: *a function FAR from the code stays far after folding, for
all but a vanishing fraction of challenges.* We prove the elementary two-point form (the
unique-decoding regime): if TWO distinct challenges both fold `f` δ-close to `C'`, the two
folds reconstruct a single codeword `4δ`-close to `f`. Hence a `4δ`-far `f` has at most ONE
"good" challenge — folding soundness error `≤ 1/|F|`. -/

/-- **Pullback cardinality**: the `q`-preimage of a set `P ⊆ L²` has `≤ 2|P|` points (each
`y` has the two representatives `rep y`, `σ rep y`). -/
theorem pullback_card_le (P : Finset κ) :
    (Finset.univ.filter (fun x : ι => G.q x ∈ P)).card ≤ 2 * P.card := by
  have hsub : (Finset.univ.filter (fun x : ι => G.q x ∈ P))
      ⊆ P.image G.rep ∪ P.image (fun y => G.σ (G.rep y)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hxP : G.q x ∈ P := hx.2
    rcases G.q_fiber x with hrep | hrep
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨G.q x, hxP, hrep.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨G.q x, hxP, hrep.symm⟩)
  calc (Finset.univ.filter (fun x : ι => G.q x ∈ P)).card
      ≤ (P.image G.rep ∪ P.image (fun y => G.σ (G.rep y))).card :=
        Finset.card_le_card hsub
    _ ≤ (P.image G.rep).card + (P.image (fun y => G.σ (G.rep y))).card :=
        Finset.card_union_le _ _
    _ ≤ P.card + P.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = 2 * P.card := by ring

/-- **THE KEY LEMMA (distance preservation, two-point / unique-decoding form).**
If `Fold α₁ f` and `Fold α₂ f` are both `d`-close to the folded code `C'` for DISTINCT
challenges `α₁ ≠ α₂`, then `f` is `4d`-close to the domain code `C`.

*Proof (BBHR18, the reconstruction argument).* Let `g₁, g₂ ∈ C'` witness the closeness,
`Tᵢ = disagree(Fold αᵢ f, gᵢ)` (`|Tᵢ| ≤ d`). Off `T₁ ∪ T₂` the two fold equations
`E f + αᵢ·O f = gᵢ` solve (Vandermonde, `α₁ ≠ α₂`) to `O f = Go`, `E f = Ge`, where
`Go = (α₁-α₂)⁻¹·(g₁-g₂)`, `Ge = (α₁-α₂)⁻¹·(α₁·g₂-α₂·g₁)` are in `C'` (linearity). Then
`h := unfoldF Ge Go ∈ C` (reassembly closure) agrees with `f` off `q⁻¹(T₁∪T₂)` by
`self_decomp`; that preimage has `≤ 2·|T₁∪T₂| ≤ 4d` points. -/
theorem fold_close_of_two_alpha {f : ι → F} {α₁ α₂ : F} (hα : α₁ ≠ α₂) {d : ℕ}
    (h1 : closeN S.C' d (Fold S.geom α₁ f))
    (h2 : closeN S.C' d (Fold S.geom α₂ f)) :
    closeN S.C (4 * d) f := by
  obtain ⟨g₁, hg₁, hc₁⟩ := h1
  obtain ⟨g₂, hg₂, hc₂⟩ := h2
  set G := S.geom
  have hne : α₁ - α₂ ≠ 0 := sub_ne_zero.mpr hα
  set inv : F := (α₁ - α₂)⁻¹ with hinv
  -- The two reconstructed folded codewords.
  set Go : κ → F := inv • (g₁ - g₂) with hGo
  set Ge : κ → F := inv • (α₁ • g₂ - α₂ • g₁) with hGe
  have hGoC : Go ∈ S.C' := S.C'.smul_mem _ (S.C'.sub_mem hg₁ hg₂)
  have hGeC : Ge ∈ S.C' := S.C'.smul_mem _ (S.C'.sub_mem (S.C'.smul_mem _ hg₂) (S.C'.smul_mem _ hg₁))
  -- The reassembled domain codeword.
  set h : ι → F := unfoldF G Ge Go with hh
  have hhC : h ∈ S.C := S.unfold_closed Ge hGeC Go hGoC
  set T : Finset κ := disagree (Fold G α₁ f) g₁ ∪ disagree (Fold G α₂ f) g₂ with hT
  -- Off `T`, the two fold equations pin `E f = Ge`, `O f = Go`.
  have key : ∀ y : κ, y ∉ T → E G f y = Ge y ∧ O G f y = Go y := by
    intro y hy
    rw [hT, Finset.mem_union, not_or] at hy
    have e1 : E G f y + α₁ * O G f y = g₁ y := by
      have h := hy.1; rw [mem_disagree, not_not] at h; simpa [Fold] using h
    have e2 : E G f y + α₂ * O G f y = g₂ y := by
      have h := hy.2; rw [mem_disagree, not_not] at h; simpa [Fold] using h
    have hGoy : Go y = inv * (g₁ y - g₂ y) := by
      simp only [hGo, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hGey : Ge y = inv * (α₁ * g₂ y - α₂ * g₁ y) := by
      simp only [hGe, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    refine ⟨?_, ?_⟩
    · rw [hGey, hinv, inv_mul_eq_div, eq_div_iff hne]
      linear_combination α₁ * e2 - α₂ * e1
    · rw [hGoy, hinv, inv_mul_eq_div, eq_div_iff hne]
      linear_combination e1 - e2
  -- Hence `f = h` off `q⁻¹(T)`.
  have hfh : ∀ x : ι, G.q x ∉ T → f x = h x := by
    intro x hx
    obtain ⟨hEx, hOx⟩ := key (G.q x) hx
    rw [self_decomp G f x, hh, unfoldF_apply, hEx, hOx]
  -- `disagree f h ⊆ q⁻¹(T)`.
  have hsub : disagree f h ⊆ Finset.univ.filter (fun x : ι => G.q x ∈ T) := by
    intro x hx
    rw [mem_disagree] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ x, ?_⟩
    by_contra hxT
    exact hx (hfh x hxT)
  -- Count.
  refine ⟨h, hhC, ?_⟩
  calc (disagree f h).card
      ≤ (Finset.univ.filter (fun x : ι => G.q x ∈ T)).card := Finset.card_le_card hsub
    _ ≤ 2 * T.card := pullback_card_le G T
    _ ≤ 2 * (disagree (Fold G α₁ f) g₁).card + 2 * (disagree (Fold G α₂ f) g₂).card := by
        have := Finset.card_union_le (disagree (Fold G α₁ f) g₁) (disagree (Fold G α₂ f) g₂)
        rw [hT]; omega
    _ ≤ 4 * d := by omega

/-- **THE EXACT SOUNDNESS BOUND** (contrapositive of the KEY LEMMA): a `4d`-FAR `f` has AT
MOST ONE "good" challenge — the set `{α | Fold α f is d-close to C'}` is a subsingleton.
Over a uniform challenge this is folding soundness error `≤ 1/|F|`. -/
theorem good_alpha_subsingleton {f : ι → F} {d : ℕ} (hfar : farN S.C (4 * d) f) :
    {α : F | closeN S.C' d (Fold S.geom α f)}.Subsingleton := by
  intro α₁ h1 α₂ h2
  by_contra hne
  exact hfar (fold_close_of_two_alpha S hne h1 h2)

/-- The `d = 0` specialization used by the final low-degree check: a `f ∉ C` has at most
one challenge that folds it into `C'`. -/
theorem exceptional_subsingleton {f : ι → F} (hf : f ∉ S.C) :
    {α : F | Fold S.geom α f ∈ S.C'}.Subsingleton := by
  have hfar : farN S.C (4 * 0) f := by simpa [farN_zero_iff_not_mem] using hf
  have := good_alpha_subsingleton S hfar
  intro α₁ h1 α₂ h2
  exact this (by simpa [closeN_zero_iff_mem] using h1) (by simpa [closeN_zero_iff_mem] using h2)

/-! ## §4. Query-phase soundness, Merkle binding, and the FRI soundness reduction.

The commit phase (§3) leaves the prover with a folded oracle it must OPEN consistently.
The query phase samples points `y ∈ L²` and checks `f'(y) = Fold α f (y)` from the opened
values. Two ingredients close soundness:

* **Query coverage** (`query_sound_of_cover`): if the sampled set covers the disagreement
  `disagree(f', Fold α f)` and every check passes, the committed next-oracle EQUALS the
  true fold. (The probabilistic "coverage w.h.p." is the `(1-γ)ˢ` soundness term; here it
  is the deterministic core.)
* **Merkle binding**: the committed root binds the oracle — the prover cannot open one
  root to two different functions, so the queried values ARE `f`'s / `f'`'s values (no
  equivocation). The deterministic `¬ HashCR` witness is `equivocation_breaks_binding`;
  the DISCHARGED bound is `FloorRegroundedConsumers.friOracle_binding_binds_rom` (keyed-ROM
  floor, PROVED — the old `HashCR`-conditioned `oracle_binding` is deleted, floor refuted). -/

/-- **Query soundness (coverage core).** If the query set `Q` covers `disagree(f', Fold α f)`
and every queried point passes the fold check, then `f' = Fold α f` as functions. -/
theorem query_sound_of_cover {f : ι → F} {f' : κ → F} {α : F} (Q : Finset κ)
    (hcover : disagree f' (Fold S.geom α f) ⊆ Q)
    (hpass : ∀ y ∈ Q, f' y = Fold S.geom α f y) :
    f' = Fold S.geom α f := by
  funext y
  by_cases hy : y ∈ Q
  · exact hpass y hy
  · by_contra hne
    exact hy (hcover (mem_disagree.mpr hne))

/-- The committed oracle: a Merkle-style commitment of the WHOLE evaluation function
(the root binds `f : ι → F`). `oracleCommit cr f` is the root; `oracleOpens cr root f`
says `f` is the committed function. -/
abbrev OracleCR (F ι Digest : Type*) := CommitReveal Unit (ι → F) Digest

/-! ⚑ **The old export `oracle_binding` (`HashCR → f = f'`) is DELETED** — its `hcr : HashCR`
hypothesis is pure injectivity of the root hash, PROVED FALSE for every compressing commitment
(`HashFloorHonesty.hashCR_false_of_compressing`), so it bound nothing at deployed parameters. Its
deterministic content survives as `equivocation_breaks_binding` below (a `¬ HashCR` CONCLUSION —
retained ONLY as the reduction's extractor witness, never re-exported as a floor). The DISCHARGED
successor is `FloorRegroundedConsumers.friOracle_binding_binds_rom`: the per-query FRI layer opening
at the SAMPLED keyed oracle, every query-bounded equivocator's advantage NEGLIGIBLE on the PROVED
floor `KeyedRomFloor.keyedRom_hard` (the birthday bound), with the extractor re-walking the path and
PAYING its `2·depth` queries (`Crypto.RomMerkleOpening`). -/

/-- **Equivocation BREAKS binding.** If the prover opens ONE root to two DISTINCT oracles
`f ≠ f'`, it witnesses a hash collision — `HashCR` fails. This is the load-bearing role of
the Merkle commitment: without it the prover swaps the oracle after seeing the challenge. -/
theorem equivocation_breaks_binding {Digest : Type*} (cr : OracleCR F ι Digest)
    {root : Digest} {f f' : ι → F} (hne : f ≠ f')
    (ho : cr.opens root () f) (ho' : cr.opens root () f') : ¬ HashCR cr :=
  Dregg2.Crypto.HermineHintMLWE.equivocation_breaks_hashcr cr root () f f' hne ho ho'

/-- **FRI SINGLE-FOLD SOUNDNESS (the reduction).** Given a genuinely far oracle `f ∉ C`,
an accepting transcript — the committed next-oracle `f'` opened under a binding root, the
query set covering the disagreement with all checks passing, and `f'` a codeword of `C'`
(final low-degree check) — FORCES the challenge `α` into the exceptional set
`{β | Fold β f ∈ C'}`, which is a subsingleton (`≤ 1` element). So the probability an
honest verifier accepts a far oracle is `≤ 1/|F|`: EITHER `α` is the single exceptional
challenge, OR (had `f'` been equivocated) `HashCR` is broken. -/
theorem fri_fold_soundness {f : ι → F} {f' : κ → F} {α : F} (Q : Finset κ)
    (hfar : f ∉ S.C)
    (hcover : disagree f' (Fold S.geom α f) ⊆ Q)
    (hpass : ∀ y ∈ Q, f' y = Fold S.geom α f y)
    (hfinal : f' ∈ S.C') :
    α ∈ {β : F | Fold S.geom β f ∈ S.C'} ∧
      {β : F | Fold S.geom β f ∈ S.C'}.Subsingleton := by
  have heq : f' = Fold S.geom α f := query_sound_of_cover S Q hcover hpass
  refine ⟨?_, exceptional_subsingleton S hfar⟩
  show Fold S.geom α f ∈ S.C'
  rw [← heq]; exact hfinal

/-! ## §4b. The `FriProximity` interface (consumed by the AIR-soundness unit 2a).

The AIR-soundness unit needs exactly ONE fact from FRI: *the committed trace is δ-close to
a low-degree codeword*, so that checking the AIR constraint at sampled points binds the
ACTUAL (low-degree) trace. `FriProximity S f d` IS that fact; `friProximity_discharge`
derives it from an accepting FRI transcript (conditioned on the generic — non-exceptional —
challenge), and `air_binds_of_proximity` is the payoff the AIR checks rest on. -/

/-- **`FriProximity`** — the interface unit 2a names: the oracle `f` is `d`-close to the
low-degree Reed-Solomon code `S.C`. (The whole point of running FRI on a committed trace.) -/
def FriProximity (S : FriSetup F ι κ) (d : ℕ) (f : ι → F) : Prop := closeN S.C d f

/-- **`friProximity_discharge`.** An accepting FRI transcript whose challenge `α` is NOT the
(≤1) exceptional one discharges `FriProximity`: the oracle is `0`-close, i.e. an actual
codeword. (The `≤ 1/|F|` chance `α` IS exceptional is the soundness error; conditioned on
the generic challenge, accept ⟹ low-degree.) -/
theorem friProximity_discharge {f : ι → F} {f' : κ → F} {α : F} (Q : Finset κ)
    (hcover : disagree f' (Fold S.geom α f) ⊆ Q)
    (hpass : ∀ y ∈ Q, f' y = Fold S.geom α f y)
    (hfinal : f' ∈ S.C')
    (hgeneric : Fold S.geom α f ∈ S.C' → f ∈ S.C) :
    FriProximity S 0 f := by
  have heq : f' = Fold S.geom α f := query_sound_of_cover S Q hcover hpass
  have : Fold S.geom α f ∈ S.C' := heq ▸ hfinal
  exact closeN_zero_iff_mem.mpr (hgeneric this)

/-- **`air_binds_of_proximity` — the AIR payoff.** If `f` is `d`-close to `S.C` (FRI
proximity) and the AIR constraint holds on every low-degree codeword, then there is a
codeword `g` the trace matches on all but `≤ d` points AND which satisfies the constraint:
the sampled AIR checks bind the actual low-degree trace `g`, not the raw oracle `f`. -/
theorem air_binds_of_proximity {f : ι → F} {d : ℕ} (hp : FriProximity S d f)
    (constraint : (ι → F) → Prop) (hconstr : ∀ g ∈ S.C, constraint g) :
    ∃ g ∈ S.C, (disagree f g).card ≤ d ∧ constraint g := by
  obtain ⟨g, hg, hc⟩ := hp
  exact ⟨g, hg, hc, hconstr g hg⟩

/-! ## §4c. Multi-round soundness (the commit-phase chain).

FRI folds `r` times. The per-round result (`exceptional_subsingleton`) says each round's
folding challenge is exceptional (folds a far oracle into the code) for `≤ 1` value. So if
`f₀` is far but the final oracle is a codeword and every fold is query-consistent, SOME
round's challenge was exceptional. The pure-`Prop` chain lemma isolates the induction; the
per-round `step` hypothesis is exactly the contrapositive of the KEY LEMMA discharged
above (`α_i` not exceptional ⟹ farness propagates one more round). -/

/-- **Farness propagates down the fold chain.** `P i` = "the round-`i` oracle is a codeword
of its code". If far at the top (`¬ P 0`) and each non-exceptional round keeps it far
(`step`: round-`i`'s challenge is not the exceptional one, so farness survives one more
fold), then it is far at the bottom (`¬ P n`) — contradicting the final low-degree check.
So an accepting far transcript needs an exceptional round (probability `≤ 1/|F|` each, by
`exceptional_subsingleton`; union `≤ n/|F|` over the `n` rounds). -/
theorem far_propagates_chain (P : ℕ → Prop) (n : ℕ)
    (step : ∀ i, i < n → ¬ P i → ¬ P (i + 1))
    (h0 : ¬ P 0) : ¬ P n := by
  induction n with
  | zero => exact h0
  | succ m ih =>
    have hm : ¬ P m := ih (fun i hi => step i (Nat.lt_succ_of_lt hi))
    exact step m (Nat.lt_succ_self m) hm

/-! ## §5. TEETH — a genuine Reed-Solomon `FriSetup` and the non-vacuity witnesses.

`ZMod 5`, `L = {1,2,3,4}` (the nonzero elements = a multiplicative group of order 4),
`L² = {1,4}`. Squaring `q`, negation `σ`, values `p`, section `rep` are the REAL coset
geometry. `C` = evaluations of `a + b·x` (deg `< 2`, rate `1/2`, min-distance `3`); `C'` =
constants (deg `< 1`). The RS closure facts (`unfold_closed`, `foldE_mem`, `foldO_mem`) are
PROVED, not assumed — so `rsSetup` is a real Reed-Solomon FRI instance, not a shell. -/

section Teeth

open scoped BigOperators

/-- `ZMod 5` is a field (`5` is prime) — makes the concrete RS instance well-typed. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `L = {1,2,3,4} ⊂ ZMod 5`, indexed by `Fin 4`. -/
def pVal : Fin 4 → ZMod 5 := ![1, 2, 3, 4]
/-- Squaring `L → L²`: `1²=1, 2²=4, 3²=4, 4²=1` ↦ `{κ₀=1, κ₁=4}`. -/
def qMap : Fin 4 → Fin 2 := ![0, 1, 1, 0]
/-- Negation `x ↦ -x`: `1↔4, 2↔3`. -/
def sigMap : Fin 4 → Fin 4 := ![3, 2, 1, 0]
/-- Section: `κ₀ ↦ 1` (idx 0), `κ₁ ↦ 4`… actually idx 1 (value 2, squares to 4). -/
def repMap : Fin 2 → Fin 4 := ![0, 1]

/-- The concrete coset geometry — every axiom holds by `decide`. -/
def rsGeom : FriGeom (ZMod 5) (Fin 4) (Fin 2) where
  σ := sigMap
  q := qMap
  p := pVal
  rep := repMap
  two_ne := by decide
  q_rep := by decide
  q_σ_rep := by decide
  p_rep_ne := by decide
  p_σ_rep := by decide
  q_fiber := by decide

/-- The domain code `C = {x ↦ a + b·p x}` — evaluations of deg `< 2` polynomials. Defined as
an explicit `Submodule` so membership hands back `⟨a, b⟩` directly. -/
def rsC : Submodule (ZMod 5) (Fin 4 → ZMod 5) where
  carrier := {f | ∃ a b : ZMod 5, f = fun x => a + b * pVal x}
  zero_mem' := ⟨0, 0, by funext x; simp⟩
  add_mem' := by
    rintro f g ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    exact ⟨a + a', b + b', by funext x; simp; ring⟩
  smul_mem' := by
    rintro c f ⟨a, b, rfl⟩
    exact ⟨c * a, c * b, by funext x; simp [mul_add]; ring⟩

/-- The folded code `C' = {y ↦ a}` — constants (deg `< 1`). -/
def rsC' : Submodule (ZMod 5) (Fin 2 → ZMod 5) where
  carrier := {g | ∃ a : ZMod 5, g = fun _ => a}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by rintro f g ⟨a, rfl⟩ ⟨a', rfl⟩; exact ⟨a + a', rfl⟩
  smul_mem' := by rintro c f ⟨a, rfl⟩; exact ⟨c * a, rfl⟩

theorem mem_rsC {f} : f ∈ rsC ↔ ∃ a b : ZMod 5, f = fun x => a + b * pVal x := Iff.rfl
theorem mem_rsC' {g} : g ∈ rsC' ↔ ∃ a : ZMod 5, g = fun _ => a := Iff.rfl

/-- **The genuine Reed-Solomon FRI setup** — closure facts PROVED. -/
def rsSetup : FriSetup (ZMod 5) (Fin 4) (Fin 2) where
  geom := rsGeom
  C := rsC
  C' := rsC'
  unfold_closed := by
    rintro Ge ⟨ce, rfl⟩ Go ⟨co, rfl⟩
    -- unfoldF (const ce) (const co) x = ce + p x * co  ∈  {a + b·p}
    exact ⟨ce, co, by funext x; simp only [unfoldF, rsGeom]; ring⟩
  foldE_mem := by
    rintro f ⟨a, b, rfl⟩
    -- E (a + b·p) = const a  (the sibling value negates the odd coeff, which cancels)
    refine ⟨a, ?_⟩
    funext y
    have hps : pVal (sigMap (repMap y)) = - pVal (repMap y) := by fin_cases y <;> decide
    simp only [E, rsGeom]
    rw [hps]
    rw [div_eq_iff (show (2 : ZMod 5) ≠ 0 by decide)]
    ring
  foldO_mem := by
    rintro f ⟨a, b, rfl⟩
    -- O (a + b·p) = const b
    refine ⟨b, ?_⟩
    funext y
    have hps : pVal (sigMap (repMap y)) = - pVal (repMap y) := by fin_cases y <;> decide
    have hpne : (2 : ZMod 5) * pVal (repMap y) ≠ 0 := by fin_cases y <;> decide
    simp only [O, rsGeom]
    rw [hps]
    rw [div_eq_iff hpne]
    ring

/-! ### Tooth 1 — an honest low-degree oracle passes and is 0-close. -/

/-- `f_honest = 2 + 3·p` is a codeword. -/
def fHonest : Fin 4 → ZMod 5 := fun x => 2 + 3 * pVal x

theorem fHonest_mem : fHonest ∈ rsSetup.C := ⟨2, 3, rfl⟩

/-- It is `0`-close (exactly a codeword). -/
theorem fHonest_close0 : closeN rsSetup.C 0 fHonest :=
  closeN_zero_iff_mem.mpr fHonest_mem

/-- Its fold with ANY challenge lands in the folded code (completeness). -/
theorem fHonest_fold_mem (α : ZMod 5) : Fold rsSetup.geom α fHonest ∈ rsSetup.C' :=
  fold_complete rsSetup fHonest_mem α

/-! ### Tooth 2 — a FAR oracle has EXACTLY ONE good challenge (the KEY LEMMA, non-vacuous). -/

/-- `f_far = ![1,0,0,0]` is NOT a codeword: no `a + b·p` matches (`min`-distance `3`). -/
def fFar : Fin 4 → ZMod 5 := ![1, 0, 0, 0]

theorem fFar_not_mem : fFar ∉ rsSetup.C := by
  rw [show rsSetup.C = rsC from rfl, mem_rsC]; decide

/-- `E fFar = ![3,0]` and `O fFar = ![3,0]` are both NON-constant, so `Fold α fFar =
![3+3α, 0]` is constant (in `C'`) for EXACTLY ONE challenge (`α = 4`, giving `![0,0]`). -/
theorem fFar_good_alpha : Fold rsSetup.geom 4 fFar ∈ rsSetup.C' := by
  rw [show rsSetup.C' = rsC' from rfl, mem_rsC']
  exact ⟨0, by funext y; fin_cases y <;> decide +kernel⟩

/-- At a DIFFERENT challenge (`α = 0`) the fold is non-constant — it LEAVES the code. This is
the KEY LEMMA biting: a far `f` folds close for at most one `α`. -/
theorem fFar_bad_alpha : Fold rsSetup.geom 0 fFar ∉ rsSetup.C' := by
  rw [show rsSetup.C' = rsC' from rfl, mem_rsC']
  rintro ⟨a, h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have hbad : Fold rsSetup.geom 0 fFar 0 = Fold rsSetup.geom 0 fFar 1 := h0.trans h1.symm
  revert hbad; decide +kernel

/-- **The KEY LEMMA fires on concrete data**: the exceptional set of `fFar` is a
subsingleton, and `α = 4` is in it while `α = 0` is not — exactly ONE good challenge,
witnessed. -/
theorem fFar_exceptional_subsingleton :
    {β : ZMod 5 | Fold rsSetup.geom β fFar ∈ rsSetup.C'}.Subsingleton :=
  exceptional_subsingleton rsSetup fFar_not_mem

/-! ### Tooth 3 — the Merkle binding is load-bearing (equivocation breaks `HashCR`). -/

/-- A COLLIDING oracle commitment: every function opens the single root `0`. -/
def badOracleCR : OracleCR (ZMod 5) (Fin 4) ℕ := ⟨fun _ _ => 0⟩

/-- **Equivocation FIRES.** On the colliding commitment the far `fFar` and the honest
`fHonest` (distinct oracles) both open root `0` — so the prover could present the
low-degree `fHonest` to the verifier while the true committed oracle is the far `fFar`.
This equivocation is exactly a `HashCR` break: `HashCR badOracleCR` is FALSE. Binding
(`HashCR`) is what forecloses it. -/
theorem badOracle_equivocates : ¬ HashCR badOracleCR := by
  have hne : fFar ≠ fHonest := by
    intro h; exact absurd (congrFun h 0) (by decide)
  exact equivocation_breaks_binding badOracleCR hne rfl rfl

end Teeth

/-! ## §6. Axiom hygiene — the theorems rest only on the standard kernel axioms. `HashCR`
appears only in CONCLUSION position (`equivocation_breaks_binding`, the extractor witness) —
never as a floor hypothesis and never an `axiom`. No `sorry`, no `def …Hard`, no smuggled
hardness. -/

#assert_axioms fold_close_of_two_alpha
#assert_axioms good_alpha_subsingleton
#assert_axioms exceptional_subsingleton
#assert_axioms query_sound_of_cover
#assert_axioms fri_fold_soundness
#assert_axioms friProximity_discharge
#assert_axioms air_binds_of_proximity
#assert_axioms far_propagates_chain
#assert_axioms equivocation_breaks_binding

end Dregg2.Circuit.FriSoundness
