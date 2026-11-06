/-
# Full-width ordered route binding with explicit collision witnesses

The compression result is a list of felts: no projection to lane zero occurs.
The served consumer uses five payload lanes (domain,index,current,symbol,next),
eight digest lanes and three zero pads: an admitted arity-16 chip call. Fixed
payload width excludes structural aliases before any cryptographic reasoning.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic

namespace Dregg2.Circuit.Emit.RouteChain8Binding
set_option autoImplicit false

/-- Exact padded chip input. -/
def preimage (seed payload : List ℤ) : List ℤ := payload ++ seed ++ [0, 0, 0]

/-- Full-width running route commitment. -/
def fold (H : List ℤ → List ℤ) : List ℤ → List (List ℤ) → List ℤ
  | seed, [] => seed
  | seed, p :: ps => fold H (H (preimage seed p)) ps

/-- Actual input blocks absorbed along a run. -/
def preimages (H : List ℤ → List ℤ) : List ℤ → List (List ℤ) → List (List ℤ)
  | _, [] => []
  | seed, p :: ps => preimage seed p :: preimages H (H (preimage seed p)) ps

/-- Equality of FULL outputs at two distinct inputs. -/
def Collision (H : List ℤ → List ℤ) (pair : List ℤ × List ℤ) : Prop :=
  pair.1 ≠ pair.2 ∧ H pair.1 = H pair.2

/-- Linear forward walk; the latest distinct input pair wins. Under equal final
outputs, the binding theorem proves this particular pair is a collision. -/
def find (H : List ℤ → List ℤ) :
    List ℤ → List ℤ → List (List ℤ) → List (List ℤ) → List ℤ × List ℤ
  | s₁, s₂, p₁ :: ps₁, p₂ :: ps₂ =>
    let pair := find H (H (preimage s₁ p₁)) (H (preimage s₂ p₂)) ps₁ ps₂
    if pair.1 ≠ pair.2 then pair else (preimage s₁ p₁, preimage s₂ p₂)
  | _, _, _, _ => ([], [])

/-- Padding and fixed payload width are injective without any hash hypothesis. -/
theorem preimage_injective {s₁ s₂ p₁ p₂ : List ℤ}
    (hlen : p₁.length = p₂.length)
    (h : preimage s₁ p₁ = preimage s₂ p₂) : p₁ = p₂ ∧ s₁ = s₂ := by
  have h' : p₁ ++ s₁ = p₂ ++ s₂ := List.append_cancel_right h
  exact List.append_inj h' hlen

/-- Replaying the same route never produces distinct inputs. -/
theorem find_self (H : List ℤ → List ℤ) : ∀ (seed : List ℤ) (ps : List (List ℤ)),
    (find H seed seed ps ps).1 = (find H seed seed ps ps).2
  | _, [] => rfl
  | seed, p :: ps => by
    have ih := find_self H (H (preimage seed p)) ps
    simp only [find, ne_eq, ih, not_true_eq_false, if_false]

/-- Equal-length routes bind both seed and payload sequence, or name a collision
on these two runs. No global injectivity or collision-freedom premise occurs. -/
theorem fold_binds_or_collides (H : List ℤ → List ℤ) (n : Nat) :
    ∀ (ps₁ ps₂ : List (List ℤ)) (s₁ s₂ : List ℤ),
      (∀ p ∈ ps₁, p.length = n) → (∀ p ∈ ps₂, p.length = n) →
      ps₁.length = ps₂.length → fold H s₁ ps₁ = fold H s₂ ps₂ →
      (s₁ = s₂ ∧ ps₁ = ps₂) ∨ Collision H (find H s₁ s₂ ps₁ ps₂)
  | [], [], _, _, _, _, _, h => Or.inl ⟨h, rfl⟩
  | [], _ :: _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _ => by simp at hl
  | p₁ :: ps₁, p₂ :: ps₂, s₁, s₂, hw₁, hw₂, hl, h => by
    have h' : fold H (H (preimage s₁ p₁)) ps₁ =
        fold H (H (preimage s₂ p₂)) ps₂ := h
    rcases fold_binds_or_collides H n ps₁ ps₂ _ _
        (fun p hp => hw₁ p (List.mem_cons_of_mem _ hp))
        (fun p hp => hw₂ p (List.mem_cons_of_mem _ hp)) (by simpa using hl) h'
        with ⟨hs, hr⟩ | hc
    · subst hr
      have hself := find_self H (H (preimage s₁ p₁)) ps₁
      rw [hs] at hself
      by_cases hp : preimage s₁ p₁ = preimage s₂ p₂
      · have he := preimage_injective
          ((hw₁ p₁ List.mem_cons_self).trans (hw₂ p₂ List.mem_cons_self).symm) hp
        exact Or.inl ⟨he.2, by rw [he.1]⟩
      · right
        simp only [find, hs, ne_eq, hself, not_true_eq_false, if_false]
        exact ⟨hp, hs⟩
    · right
      simp only [find, if_pos hc.1]
      exact hc

/-- The extractor's distinct pair belongs to the two ACTUAL input sequences. -/
theorem find_mem (H : List ℤ → List ℤ) :
    ∀ (ps₁ ps₂ : List (List ℤ)) (s₁ s₂ : List ℤ),
      (find H s₁ s₂ ps₁ ps₂).1 ≠ (find H s₁ s₂ ps₁ ps₂).2 →
      (find H s₁ s₂ ps₁ ps₂).1 ∈ preimages H s₁ ps₁ ∧
      (find H s₁ s₂ ps₁ ps₂).2 ∈ preimages H s₂ ps₂
  | [], _, _, _, h => False.elim (h rfl)
  | _ :: _, [], _, _, h => False.elim (h rfl)
  | p₁ :: ps₁, p₂ :: ps₂, s₁, s₂, h => by
    by_cases hn :
        (find H (H (preimage s₁ p₁)) (H (preimage s₂ p₂)) ps₁ ps₂).1 ≠
        (find H (H (preimage s₁ p₁)) (H (preimage s₂ p₂)) ps₁ ps₂).2
    · simp only [find, if_pos hn]
      have ih := find_mem H ps₁ ps₂ (H (preimage s₁ p₁)) (H (preimage s₂ p₂)) hn
      exact ⟨List.mem_cons_of_mem _ ih.1, List.mem_cons_of_mem _ ih.2⟩
    · simp only [find, if_neg hn]
      exact ⟨List.mem_cons_self, List.mem_cons_self⟩

/-- Consumer-facing same-seed specialization. -/
theorem chain_binds_or_collides (H : List ℤ → List ℤ) (n : Nat)
    (seed : List ℤ) (ps₁ ps₂ : List (List ℤ))
    (hw₁ : ∀ p ∈ ps₁, p.length = n) (hw₂ : ∀ p ∈ ps₂, p.length = n)
    (hl : ps₁.length = ps₂.length) (he : fold H seed ps₁ = fold H seed ps₂) :
    ps₁ = ps₂ ∨ Collision H (find H seed seed ps₁ ps₂) := by
  rcases fold_binds_or_collides H n ps₁ ps₂ seed seed hw₁ hw₂ hl he with h | h
  · exact Or.inl h.2
  · exact Or.inr h

/-- Honest self-refutation needs no property of H. -/
theorem no_self_collision (H : List ℤ → List ℤ) (seed : List ℤ) (ps : List (List ℤ)) :
    ¬ Collision H (find H seed seed ps ps) := fun h => h.1 (find_self H seed ps)

/-! Kernel-evaluated inhabited examples. The toy compression is NOT Poseidon2. -/
def exampleSeed : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0]
def exampleA : List (List ℤ) := [[17, 1, 0, 1, 0], [17, 2, 0, 2, 0]]
def exampleB : List (List ℤ) := [[17, 1, 0, 2, 0], [17, 2, 0, 1, 0]]
def exampleHash (input : List ℤ) : List ℤ :=
  [3 * input.getD 5 0 + input.getD 3 0, 1, 2, 3, 4, 5, 6, 7]

theorem exampleHash_width (input : List ℤ) : (exampleHash input).length = 8 := rfl

theorem example_payload_widths :
    (∀ p ∈ exampleA, p.length = 5) ∧ (∀ p ∈ exampleB, p.length = 5) := by
  simp [exampleA, exampleB]

theorem honest_route_inhabited :
    fold exampleHash exampleSeed exampleA = [5, 1, 2, 3, 4, 5, 6, 7] ∧
    ¬ Collision exampleHash (find exampleHash exampleSeed exampleSeed exampleA exampleA) :=
  ⟨by decide, no_self_collision _ _ _⟩

/-- Equal transition multisets, different ordered commitments. -/
theorem order_splice_separated :
    (exampleA.map (fun p => [p.getD 2 0, p.getD 3 0, p.getD 4 0])).Perm
      (exampleB.map (fun p => [p.getD 2 0, p.getD 3 0, p.getD 4 0])) ∧
    fold exampleHash exampleSeed exampleA ≠ fold exampleHash exampleSeed exampleB := by
  constructor
  · exact List.Perm.swap _ _ []
  · decide

/-- A colliding eight-lane function inhabits the other branch, with both inputs
located on these runs, so the reduction does not conceal a vacuous assumption. -/
theorem collision_branch_inhabited :
    Collision (fun _ => exampleSeed) (find (fun _ => exampleSeed)
      exampleSeed exampleSeed exampleA exampleB) ∧
    (find (fun _ => exampleSeed) exampleSeed exampleSeed exampleA exampleB).1 ∈
      preimages (fun _ => exampleSeed) exampleSeed exampleA ∧
    (find (fun _ => exampleSeed) exampleSeed exampleSeed exampleA exampleB).2 ∈
      preimages (fun _ => exampleSeed) exampleSeed exampleB := by
  have hc : Collision (fun _ => exampleSeed) (find (fun _ => exampleSeed)
      exampleSeed exampleSeed exampleA exampleB) := by
    unfold Collision
    decide
  exact ⟨hc, find_mem _ _ _ _ _ hc.1⟩

/-- The deployed five-plus-eight-plus-three encoding is exactly arity sixteen. -/
theorem preimage_arity {seed payload : List ℤ}
    (hs : seed.length = 8) (hp : payload.length = 5) :
    (preimage seed payload).length = 16 := by
  simp [preimage, hs, hp]

/-- Full-width outputs stay full-width throughout the running fold. -/
theorem fold_width (H : List ℤ → List ℤ) (hw : ∀ input, (H input).length = 8) :
    ∀ (ps : List (List ℤ)) (seed : List ℤ), seed.length = 8 →
      (fold H seed ps).length = 8
  | [], _, hs => hs
  | p :: ps, seed, _ => fold_width H hw ps (H (preimage seed p)) (hw _)

/-- Every actual absorbed block has the admitted arity, provided all squeezed
outputs have eight lanes and every payload has the five declared lanes. -/
theorem preimages_arity (H : List ℤ → List ℤ) (hw : ∀ input, (H input).length = 8) :
    ∀ (ps : List (List ℤ)) (seed : List ℤ), seed.length = 8 →
      (∀ p ∈ ps, p.length = 5) → ∀ input ∈ preimages H seed ps, input.length = 16
  | [], _, _, _, _, h => by simp [preimages] at h
  | p :: ps, seed, hs, hp, input, hi => by
    simp only [preimages, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact preimage_arity hs (hp p List.mem_cons_self)
    · exact preimages_arity H hw ps (H (preimage seed p)) (hw _)
        (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) input hi

/-- A reported collision's two blocks have arity sixteen on the eight-lane rail. -/
theorem find_arity (H : List ℤ → List ℤ) (hw : ∀ input, (H input).length = 8)
    (ps₁ ps₂ : List (List ℤ)) (s₁ s₂ : List ℤ)
    (hs₁ : s₁.length = 8) (hs₂ : s₂.length = 8)
    (hp₁ : ∀ p ∈ ps₁, p.length = 5) (hp₂ : ∀ p ∈ ps₂, p.length = 5)
    (hc : Collision H (find H s₁ s₂ ps₁ ps₂)) :
    (find H s₁ s₂ ps₁ ps₂).1.length = 16 ∧
    (find H s₁ s₂ ps₁ ps₂).2.length = 16 := by
  have hm := find_mem H ps₁ ps₂ s₁ s₂ hc.1
  exact ⟨preimages_arity H hw ps₁ s₁ hs₁ hp₁ _ hm.1,
    preimages_arity H hw ps₂ s₂ hs₂ hp₂ _ hm.2⟩

/-- Any per-felt representation invariant (in particular canonical field
representatives) propagates to the actual absorbed input blocks. -/
theorem preimages_all (P : ℤ → Prop) (hzero : P 0) (H : List ℤ → List ℤ)
    (hH : ∀ input, ∀ x ∈ H input, P x) :
    ∀ (ps : List (List ℤ)) (seed : List ℤ), (∀ x ∈ seed, P x) →
      (∀ p ∈ ps, ∀ x ∈ p, P x) →
      ∀ input ∈ preimages H seed ps, ∀ x ∈ input, P x
  | [], _, _, _, _, hi, _, _ => by simp [preimages] at hi
  | p :: ps, seed, hs, hp, input, hi, x, hx => by
    simp only [preimages, List.mem_cons] at hi
    rcases hi with rfl | hi
    · simp only [preimage, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (hx | hx) | hx
      · exact hp p List.mem_cons_self x hx
      · exact hs x hx
      · rcases hx with rfl | rfl | rfl <;> exact hzero
    · exact preimages_all P hzero H hH ps (H (preimage seed p)) (hH _)
        (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) input hi x hx

/-- Dropping fixed payload width really would permit a structural alias. -/
theorem variable_width_alias :
    preimage [1] [] = preimage [] [1] ∧
    ([] : List ℤ) ≠ [1] ∧ ([1] : List ℤ) ≠ [] := by decide

/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.preimage_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms preimage_injective
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.fold_binds_or_collides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fold_binds_or_collides
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.find_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms find_mem
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.chain_binds_or_collides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chain_binds_or_collides
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.no_self_collision' depends on axioms: [propext] -/
#guard_msgs in
#print axioms no_self_collision
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.honest_route_inhabited' depends on axioms: [propext] -/
#guard_msgs in
#print axioms honest_route_inhabited
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.order_splice_separated' depends on axioms: [propext] -/
#guard_msgs in
#print axioms order_splice_separated
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.collision_branch_inhabited' depends on axioms: [propext] -/
#guard_msgs in
#print axioms collision_branch_inhabited
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.preimage_arity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms preimage_arity
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.fold_width' does not depend on any axioms -/
#guard_msgs in
#print axioms fold_width
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.variable_width_alias' does not depend on any axioms -/
#guard_msgs in
#print axioms variable_width_alias

/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.preimages_arity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms preimages_arity
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.find_arity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms find_arity
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Binding.preimages_all' depends on axioms: [propext] -/
#guard_msgs in
#print axioms preimages_all
end Dregg2.Circuit.Emit.RouteChain8Binding
