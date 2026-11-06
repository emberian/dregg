/-
Canonical arity-16 inputs for the route collision residual. An integer pair that
aliases after field reduction is not advertised as a cryptographic collision:
both named blocks here consist of canonical BabyBear representatives, have the
admitted width, and occur in the two actual route computations.
-/
import Dregg2.Circuit.Emit.RouteChain8Refine
namespace Dregg2.Circuit.Emit.RouteChain8Canonical
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.RouteChain8
open Dregg2.Circuit.Emit.RouteChain8Refine
open Dregg2.Circuit.Emit.RouteChain8Binding
set_option autoImplicit false

/-- Canonical field representatives, before any cryptographic reasoning. -/
def CanonicalBlock (xs : List ℤ) : Prop :=
  ∀ x ∈ xs, 0 ≤ x ∧ x < 2013265921

theorem seed_width (c : Config) (t : VmTrace) : (seed c t).length = 8 := by
  simp [seed, lanes]

theorem seed_canonical (c : Config) (t : VmTrace) (hc : Canonical t) :
    CanonicalBlock (seed c t) := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  cases hs : c.seed with
  | none => simp
  | some k => exact hc.pub (k+j)

/-- Domain tags, like trace cells, must be canonical; a large tag is not silently reduced. -/
theorem trace_payloads_canonical (c : Config) (t : VmTrace) (hc : Canonical t)
    (hdomain : c.domain < 2013265921) :
    ∀ p ∈ payloads c t, CanonicalBlock p := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  intro x hx
  simp only [payload, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by omega, by exact_mod_cast hdomain⟩
  · exact hc.row i hi (index c)
  · exact hc.row i hi c.current
  · exact hc.row i hi c.symbol
  · exact hc.row i hi c.next

/-- Canonical output lanes propagate canonicality through the actual preimage sequence. -/
theorem preimages_canonical (H : List ℤ → List ℤ)
    (hH : ∀ input, CanonicalBlock (H input))
    (ps : List (List ℤ)) (s : List ℤ) (hs : CanonicalBlock s)
    (hp : ∀ p ∈ ps, CanonicalBlock p) :
    ∀ input ∈ preimages H s ps, CanonicalBlock input :=
  preimages_all (fun x => 0 ≤ x ∧ x < 2013265921) (by omega) H hH ps s hs hp

/-- A named route collision uses canonical representatives on both sides. -/
theorem collision_inputs_canonical (H : List ℤ → List ℤ)
    (hH : ∀ input, CanonicalBlock (H input))
    (ps₁ ps₂ : List (List ℤ)) (s₁ s₂ : List ℤ)
    (hs₁ : CanonicalBlock s₁) (hs₂ : CanonicalBlock s₂)
    (hp₁ : ∀ p ∈ ps₁, CanonicalBlock p) (hp₂ : ∀ p ∈ ps₂, CanonicalBlock p)
    (hc : Collision H (find H s₁ s₂ ps₁ ps₂)) :
    CanonicalBlock (find H s₁ s₂ ps₁ ps₂).1 ∧
    CanonicalBlock (find H s₁ s₂ ps₁ ps₂).2 := by
  have hm := find_mem H ps₁ ps₂ s₁ s₂ hc.1
  exact ⟨preimages_canonical H hH ps₁ s₁ hs₁ hp₁ _ hm.1,
    preimages_canonical H hH ps₂ s₂ hs₂ hp₂ _ hm.2⟩

/-- Full provenance of the residual: two arity-16 canonical blocks, each on its
own computation. This rules out padding and modular-representation aliases. -/
theorem collision_inputs_admitted (H : List ℤ → List ℤ)
    (hw : ∀ input, (H input).length = 8)
    (hH : ∀ input, CanonicalBlock (H input))
    (ps₁ ps₂ : List (List ℤ)) (s₁ s₂ : List ℤ)
    (hsw₁ : s₁.length = 8) (hsw₂ : s₂.length = 8)
    (hs₁ : CanonicalBlock s₁) (hs₂ : CanonicalBlock s₂)
    (hpw₁ : ∀ p ∈ ps₁, p.length = 5) (hpw₂ : ∀ p ∈ ps₂, p.length = 5)
    (hp₁ : ∀ p ∈ ps₁, CanonicalBlock p) (hp₂ : ∀ p ∈ ps₂, CanonicalBlock p)
    (hc : Collision H (find H s₁ s₂ ps₁ ps₂)) :
    (find H s₁ s₂ ps₁ ps₂).1.length = 16 ∧
    (find H s₁ s₂ ps₁ ps₂).2.length = 16 ∧
    CanonicalBlock (find H s₁ s₂ ps₁ ps₂).1 ∧
    CanonicalBlock (find H s₁ s₂ ps₁ ps₂).2 ∧
    (find H s₁ s₂ ps₁ ps₂).1 ∈ preimages H s₁ ps₁ ∧
    (find H s₁ s₂ ps₁ ps₂).2 ∈ preimages H s₂ ps₂ := by
  have ha := find_arity H hw ps₁ ps₂ s₁ s₂ hsw₁ hsw₂ hpw₁ hpw₂ hc
  have hm := find_mem H ps₁ ps₂ s₁ s₂ hc.1
  have hcan := collision_inputs_canonical H hH ps₁ ps₂ s₁ s₂ hs₁ hs₂ hp₁ hp₂ hc
  exact ⟨ha.1, ha.2, hcan.1, hcan.2, hm.1, hm.2⟩

/-- A field alias is rejected as a noncanonical block, independently of the hash. -/
theorem field_alias_refused :
    (0 : ℤ) ≡ 2013265921 [ZMOD 2013265921] ∧
    CanonicalBlock [0] ∧ ¬ CanonicalBlock [2013265921] := by
  constructor
  · decide
  constructor
  · simp [CanonicalBlock]
  · simp [CanonicalBlock]

/-- The canonical premise is inhabited by every payload in the two-row splice example. -/
theorem example_inputs_canonical :
    CanonicalBlock exampleSeed ∧
    (∀ p ∈ exampleA, CanonicalBlock p) ∧
    (∀ p ∈ exampleB, CanonicalBlock p) := by
  simp [CanonicalBlock, exampleSeed, exampleA, exampleB]

/-- info: 'Dregg2.Circuit.Emit.RouteChain8Canonical.trace_payloads_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms trace_payloads_canonical
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Canonical.collision_inputs_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms collision_inputs_admitted
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Canonical.field_alias_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms field_alias_refused
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Canonical.example_inputs_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms example_inputs_canonical
end Dregg2.Circuit.Emit.RouteChain8Canonical
