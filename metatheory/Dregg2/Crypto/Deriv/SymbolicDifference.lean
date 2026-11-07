/-
# Dregg2.Crypto.Deriv.SymbolicDifference — finite DBM minterms for step predicates

This module extends the existing `MintermCover` plug-in seam; it does not create another
derivative, reachability, or similarity tower.  A scalar coordinate is a `(field, frame-slot)`
pair, with `old` and `new` slots, and a minterm region is cut by integer difference constraints
`xᵢ - xⱼ ≤ c`.  Axis-aligned thresholds are the special case where one endpoint is the fixed
zero coordinate.  Each Boolean region is represented as a difference-bound graph.  Feasibility
is characterized by absence of a negative cycle, and shortest simple-path potentials construct
an integer point in every feasible region.  Those points, together with finite presence and
full-value equality partitions, form `coverOfDifference` and feed the existing generic
`predRE_emptiness_decidable_cover` / `predRE_equivalence_decidable_cover` assemblies.

## Semantic boundary

The regex alphabet is still `Value`.  Reactive leaves use `PredRE.transitionSymbol old new`, the
reserved transition envelope introduced in `Core`; ordinary record symbols continue to mean an
empty old frame plus that record as new.  A singleton transition symbol therefore evaluates the
actual step predicate exactly.  A word of several transition symbols, however, does **not** impose
`newᵢ = oldᵢ₊₁`.  Multi-symbol regex emptiness consequently over-approximates trace feasibility.
The result here decides whether step rules are satisfiable/equivalent; it is not invariant
model-checking over linked executions.  This is the intended boundary for dregg's single-turn
guards.

General affine atoms (`affineLe`, `affineEq`, `affineDeltaLe`, and other linear combinations) are
outside the fragment.  DBMs cover coefficients `+1` and `-1` on two coordinates only.

No decision below kernel-reduces a transported `Decidable` instance.  Demonstrations at the end
are direct, cheap Boolean evaluations of the cover and `emptyFix`.
-/
import Dregg2.Crypto.Deriv.SymbolicIntervals
import Mathlib.Data.List.Sections
import Mathlib.Data.List.Dedup

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (der null derives leaf bot derList derives_eq_null_derList
  predBEq RigidFull rigidRE)

/-! ## §1 A finite, executable difference-bound graph -/

namespace DBM

/-- A DBM edge `src → dst` of weight `bound` denotes `x(dst) - x(src) ≤ bound`. -/
structure Edge (n : Nat) where
  src : Fin n
  dst : Fin n
  bound : Int
  deriving DecidableEq, Repr

/-- A connected edge word starting at `s`, using only graph edges. -/
def IsWalk {n : Nat} (G : List (Edge n)) : Fin n → List (Edge n) → Prop
  | _, [] => True
  | s, e :: es => e ∈ G ∧ e.src = s ∧ IsWalk G e.dst es

instance {n : Nat} (G : List (Edge n)) (s : Fin n) (es : List (Edge n)) :
    Decidable (IsWalk G s es) := by
  induction es generalizing s with
  | nil => exact isTrue trivial
  | cons e es ih =>
      letI : Decidable (IsWalk G e.dst es) := ih e.dst
      simp only [IsWalk]
      infer_instance

/-- Endpoint of an edge word, relative to its starting vertex. -/
def walkEnd {n : Nat} : Fin n → List (Edge n) → Fin n
  | s, [] => s
  | _, e :: es => walkEnd e.dst es

/-- Visited vertices, including the start. -/
def walkVertices {n : Nat} (s : Fin n) (es : List (Edge n)) : List (Fin n) :=
  s :: es.map Edge.dst

/-- Total edge weight. -/
def walkWeight {n : Nat} (es : List (Edge n)) : Int := (es.map Edge.bound).sum

/-- A negative directed cycle in the constraint graph. -/
def NegativeCycle {n : Nat} (G : List (Edge n)) : Prop :=
  ∃ s es, es ≠ [] ∧ IsWalk G s es ∧ walkEnd s es = s ∧ walkWeight es < 0

/-- A potential satisfying every DBM edge. -/
def Satisfies {n : Nat} (G : List (Edge n)) (x : Fin n → Int) : Prop :=
  ∀ e ∈ G, x e.dst - x e.src ≤ e.bound

/-- Edge inequalities telescope along a walk. -/
theorem walk_bound {n : Nat} {G : List (Edge n)} {x : Fin n → Int} (hx : Satisfies G x) :
    ∀ {s es}, IsWalk G s es → x (walkEnd s es) - x s ≤ walkWeight es := by
  intro s es
  induction es generalizing s with
  | nil => simp [walkEnd, walkWeight]
  | cons e es ih =>
      intro hw
      simp only [IsWalk] at hw
      have he := hx e hw.1
      have ht := ih hw.2.2
      rw [hw.2.1] at he
      simp only [walkWeight] at ht
      simp only [walkEnd, walkWeight, List.map_cons, List.sum_cons]
      omega

/-- Every feasible DBM has no negative cycle. -/
theorem noNegativeCycle_of_satisfies {n : Nat} {G : List (Edge n)} {x : Fin n → Int}
    (hx : Satisfies G x) : ¬ NegativeCycle G := by
  rintro ⟨s, es, -, hw, hend, hneg⟩
  have h := walk_bound hx hw
  rw [hend] at h
  omega

/-- All edge words of length at most `fuel`; used to enumerate the finite simple paths. -/
def edgeWords {n : Nat} (G : List (Edge n)) : Nat → List (List (Edge n))
  | 0 => [[]]
  | k + 1 => edgeWords G k ++ G.flatMap (fun e => (edgeWords G k).map (fun es => e :: es))

theorem nil_mem_edgeWords {n k : Nat} (G : List (Edge n)) : [] ∈ edgeWords G k := by
  induction k with
  | zero => simp [edgeWords]
  | succ k ih => exact List.mem_append.mpr (Or.inl ih)

theorem edgeWords_mono {n k : Nat} {G : List (Edge n)} {es : List (Edge n)}
    (h : es ∈ edgeWords G k) : es ∈ edgeWords G (k + 1) :=
  List.mem_append.mpr (Or.inl h)

theorem cons_mem_edgeWords {n k : Nat} {G : List (Edge n)} {e : Edge n} {es : List (Edge n)}
    (he : e ∈ G) (hes : es ∈ edgeWords G k) : e :: es ∈ edgeWords G (k + 1) := by
  simp only [edgeWords, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨e, he, es, hes, rfl⟩

theorem mem_edgeWords_of_length_le {n : Nat} {G : List (Edge n)} :
    ∀ {es : List (Edge n)} {k : Nat}, (∀ e ∈ es, e ∈ G) → es.length ≤ k →
      es ∈ edgeWords G k := by
  intro es
  induction es with
  | nil => intro k _ _; exact nil_mem_edgeWords G
  | cons e es ih =>
      intro k hall hlen
      cases k with
      | zero => simp at hlen
      | succ k =>
          apply cons_mem_edgeWords (hall e (by simp))
          apply ih (fun e' he' => hall e' (List.mem_cons_of_mem _ he'))
          simp only [List.length_cons] at hlen
          omega

/-- Simple paths from `s` to `v`, represented by their edge words. -/
def simplePathsTo {n : Nat} (G : List (Edge n)) (s v : Fin n) : List (List (Edge n)) :=
  (edgeWords G n).filter fun es =>
    decide (IsWalk G s es ∧ walkEnd s es = v ∧ (walkVertices s es).Nodup)

/-- Their finite weight list. -/
def pathWeights {n : Nat} (G : List (Edge n)) (s v : Fin n) : List Int :=
  (simplePathsTo G s v).map walkWeight

/-- The computable shortest simple-path weight (zero only when the path set is empty). -/
def shortest {n : Nat} (G : List (Edge n)) (s v : Fin n) : Int :=
  (pathWeights G s v).min?.getD 0

theorem mem_simplePathsTo_iff {n : Nat} {G : List (Edge n)} {s v : Fin n}
    {es : List (Edge n)} : es ∈ simplePathsTo G s v ↔
      es ∈ edgeWords G n ∧ IsWalk G s es ∧ walkEnd s es = v ∧ (walkVertices s es).Nodup := by
  simp [simplePathsTo]

theorem walkEnd_append {n : Nat} (s : Fin n) (as bs : List (Edge n)) :
    walkEnd s (as ++ bs) = walkEnd (walkEnd s as) bs := by
  induction as generalizing s with
  | nil => rfl
  | cons e es ih => simp only [List.cons_append, walkEnd, ih]

theorem walkWeight_append {n : Nat} (as bs : List (Edge n)) :
    walkWeight (as ++ bs) = walkWeight as + walkWeight bs := by
  simp [walkWeight]

theorem walkVertices_append {n : Nat} (s : Fin n) (as bs : List (Edge n)) :
    walkVertices s (as ++ bs) = walkVertices s as ++ bs.map Edge.dst := by
  simp [walkVertices]

theorem walkVertices_length {n : Nat} (s : Fin n) (es : List (Edge n)) :
    (walkVertices s es).length = es.length + 1 := by
  simp [walkVertices]

theorem isWalk_edges {n : Nat} {G : List (Edge n)} {s : Fin n} {es : List (Edge n)}
    (h : IsWalk G s es) : ∀ e ∈ es, e ∈ G := by
  induction es generalizing s with
  | nil => simp
  | cons e es ih =>
      simp only [IsWalk] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact h.1
      · exact ih h.2.2 e' he'

theorem isWalk_append_edge {n : Nat} {G : List (Edge n)} {s : Fin n} {es : List (Edge n)}
    (hw : IsWalk G s es) {e : Edge n} (he : e ∈ G) (hsrc : e.src = walkEnd s es) :
    IsWalk G s (es ++ [e]) := by
  induction es generalizing s e with
  | nil =>
      simp only [walkEnd] at hsrc
      simp [IsWalk, he, hsrc]
  | cons a as ih =>
      simp only [IsWalk] at hw
      simp only [List.cons_append, IsWalk]
      exact ⟨hw.1, hw.2.1, ih hw.2.2 he hsrc⟩

/-- Split a walk at any visited vertex. -/
theorem walk_split_at_vertex {n : Nat} {G : List (Edge n)} {s v : Fin n} {es : List (Edge n)}
    (hw : IsWalk G s es) (hv : v ∈ walkVertices s es) :
    ∃ pre post, es = pre ++ post ∧ IsWalk G s pre ∧ walkEnd s pre = v ∧ IsWalk G v post := by
  induction es generalizing s with
  | nil =>
      simp only [walkVertices, List.map_nil, List.mem_singleton] at hv
      subst v
      exact ⟨[], [], rfl, trivial, rfl, trivial⟩
  | cons e es ih =>
      simp only [IsWalk] at hw
      by_cases hvs : v = s
      · subst v
        exact ⟨[], e :: es, rfl, trivial, rfl, by simpa [IsWalk] using hw⟩
      · have htail : v ∈ walkVertices e.dst es := by
          simp only [walkVertices, List.map_cons, List.mem_cons] at hv ⊢
          rcases hv with h | h
          · exact absurd h hvs
          · exact h
        obtain ⟨pre, post, hes, hpre, hend, hpost⟩ := ih hw.2.2 htail
        refine ⟨e :: pre, post, ?_, ?_, ?_, hpost⟩
        · simp [hes]
        · simp only [IsWalk]
          exact ⟨hw.1, hw.2.1, hpre⟩
        · simpa only [walkEnd] using hend

theorem shortest_spec {n : Nat} {G : List (Edge n)} {s v : Fin n}
    (hne : pathWeights G s v ≠ []) :
    shortest G s v ∈ pathWeights G s v ∧
      ∀ w ∈ pathWeights G s v, shortest G s v ≤ w := by
  unfold shortest
  cases hmin : (pathWeights G s v).min? with
  | none =>
      exact absurd ((List.min?_eq_none_iff.mp hmin)) hne
  | some m =>
      simpa only [Option.getD_some] using (List.min?_eq_some_iff.mp hmin)

theorem shortest_path {n : Nat} {G : List (Edge n)} {s v : Fin n}
    (hne : pathWeights G s v ≠ []) :
    ∃ es, IsWalk G s es ∧ walkEnd s es = v ∧ (walkVertices s es).Nodup ∧
      walkWeight es = shortest G s v := by
  obtain ⟨hm, -⟩ := shortest_spec hne
  rw [pathWeights, List.mem_map] at hm
  obtain ⟨es, hes, hweight⟩ := hm
  have hs := (mem_simplePathsTo_iff.mp hes)
  exact ⟨es, hs.2.1, hs.2.2.1, hs.2.2.2, hweight⟩

theorem shortest_le_path {n : Nat} {G : List (Edge n)} {s v : Fin n}
    (hne : pathWeights G s v ≠ []) {es : List (Edge n)}
    (hes : es ∈ simplePathsTo G s v) : shortest G s v ≤ walkWeight es := by
  exact (shortest_spec hne).2 _ (List.mem_map.mpr ⟨es, hes, rfl⟩)

theorem mem_simplePathsTo_of_walk {n : Nat} {G : List (Edge n)} {s v : Fin n}
    {es : List (Edge n)} (hw : IsWalk G s es) (hend : walkEnd s es = v)
    (hnod : (walkVertices s es).Nodup) : es ∈ simplePathsTo G s v := by
  apply mem_simplePathsTo_iff.mpr
  refine ⟨mem_edgeWords_of_length_le (isWalk_edges hw) ?_, hw, hend, hnod⟩
  have hcard := hnod.length_le_card
  rw [walkVertices_length] at hcard
  simp only [Fintype.card_fin] at hcard
  omega

/-- Shortest simple-path distances relax across every edge when the DBM has no negative cycle.
If appending the edge repeats no vertex, the extended path is a candidate. If it repeats the
destination, the repeated suffix plus the edge is a cycle; deleting that nonnegative cycle leaves
a no-heavier prefix candidate. -/
theorem shortest_relax {n : Nat} {G : List (Edge n)} {s : Fin n}
    (hno : ¬ NegativeCycle G) (hne : ∀ v, pathWeights G s v ≠ [])
    {e : Edge n} (he : e ∈ G) :
    shortest G s e.dst ≤ shortest G s e.src + e.bound := by
  obtain ⟨es, hw, hend, hnod, hweight⟩ := shortest_path (hne e.src)
  by_cases hv : e.dst ∈ walkVertices s es
  · obtain ⟨pre, post, hes, hpre, hpreend, hpost⟩ := walk_split_at_vertex hw hv
    have hpostend : walkEnd e.dst post = e.src := by
      have h := hend
      rw [hes, walkEnd_append, hpreend] at h
      exact h
    have hcycleWalk : IsWalk G e.dst (post ++ [e]) :=
      isWalk_append_edge hpost he (by rw [hpostend])
    have hcycleEnd : walkEnd e.dst (post ++ [e]) = e.dst := by
      rw [walkEnd_append, hpostend]
      simp [walkEnd]
    have hcycleNonneg : 0 ≤ walkWeight (post ++ [e]) := by
      by_contra hneg
      apply hno
      exact ⟨e.dst, post ++ [e], by simp, hcycleWalk, hcycleEnd, by omega⟩
    have hpreNodup : (walkVertices s pre).Nodup := by
      have h := hnod
      rw [hes, walkVertices_append] at h
      exact h.of_append_left
    have hpreMem := mem_simplePathsTo_of_walk hpre hpreend hpreNodup
    have hle := shortest_le_path (hne e.dst) hpreMem
    have hcycleWeight : 0 ≤ walkWeight post + e.bound := by
      rw [walkWeight_append] at hcycleNonneg
      simpa [walkWeight] using hcycleNonneg
    have hwes : walkWeight es = walkWeight pre + walkWeight post := by
      rw [hes, walkWeight_append]
    rw [hweight] at hwes
    omega
  · have happWalk : IsWalk G s (es ++ [e]) :=
      isWalk_append_edge hw he (by rw [hend])
    have happEnd : walkEnd s (es ++ [e]) = e.dst := by
      rw [walkEnd_append, hend]
      simp [walkEnd]
    have happNodup : (walkVertices s (es ++ [e])).Nodup := by
      rw [walkVertices_append]
      rw [List.nodup_append]
      refine ⟨hnod, by simp, ?_⟩
      intro a ha b hb
      have hb' : b = e.dst := List.mem_singleton.mp hb
      subst hb'
      intro h
      subst a
      exact hv ha
    have happMem := mem_simplePathsTo_of_walk happWalk happEnd happNodup
    have hle := shortest_le_path (hne e.dst) happMem
    have hone : walkWeight [e] = e.bound := by simp [walkWeight]
    rw [walkWeight_append, hweight, hone] at hle
    exact hle

/-! ### Super-source and the constructive feasibility theorem -/

/-- Embed an original vertex below a fresh final super-source. -/
def liftEdge {n : Nat} (e : Edge n) : Edge (n + 1) :=
  ⟨e.src.castSucc, e.dst.castSucc, e.bound⟩

/-- The zero-weight edge from the super-source to `i`. -/
def sourceEdge {n : Nat} (i : Fin n) : Edge (n + 1) :=
  ⟨Fin.last n, i.castSucc, 0⟩

/-- Add a fresh super-source with an outgoing edge to every original vertex. It has no incoming
edge, so it changes reachability of shortest paths but not the graph's directed cycles. -/
def withSource {n : Nat} (G : List (Edge n)) : List (Edge (n + 1)) :=
  G.map liftEdge ++ List.ofFn sourceEdge

theorem liftEdge_mem_withSource {n : Nat} {G : List (Edge n)} {e : Edge n} (he : e ∈ G) :
    liftEdge e ∈ withSource G := by
  apply List.mem_append.mpr
  exact Or.inl (List.mem_map.mpr ⟨e, he, rfl⟩)

theorem sourceEdge_mem_withSource {n : Nat} {G : List (Edge n)} (i : Fin n) :
    sourceEdge i ∈ withSource G := by
  apply List.mem_append.mpr
  exact Or.inr (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- A large enough value for the fresh source, used only to prove that adding source edges
preserves feasibility. -/
def sourceValue {n : Nat} (x : Fin n → Int) : Int :=
  (List.ofFn fun i => |x i|).sum

private theorem sum_abs_nonneg (l : List Int) : 0 ≤ (l.map fun y => |y|).sum := by
  induction l with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons]
      have hy := abs_nonneg y
      omega

private theorem abs_le_sum_abs {x : Int} : ∀ {l : List Int}, x ∈ l →
    |x| ≤ (l.map fun y => |y|).sum := by
  intro l hx
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.map_cons, List.sum_cons]
        have hnonneg := sum_abs_nonneg ys
        omega
      · simp only [List.map_cons, List.sum_cons]
        have htail := ih hx
        have hy := abs_nonneg y
        omega

theorem le_sourceValue {n : Nat} (x : Fin n → Int) (i : Fin n) : x i ≤ sourceValue x := by
  apply le_trans (le_abs_self (x i))
  refine le_trans
    (abs_le_sum_abs (x := x i) (l := List.ofFn x) (List.mem_ofFn.mpr ⟨i, rfl⟩)) (le_of_eq ?_)
  simp [sourceValue, Function.comp_def]

/-- Extend a potential to the super-source. -/
def extendPotential {n : Nat} (x : Fin n → Int) : Fin (n + 1) → Int :=
  Fin.lastCases (sourceValue x) x

@[simp] theorem extendPotential_last {n : Nat} (x : Fin n → Int) :
    extendPotential x (Fin.last n) = sourceValue x := by
  simp [extendPotential]

@[simp] theorem extendPotential_castSucc {n : Nat} (x : Fin n → Int) (i : Fin n) :
    extendPotential x i.castSucc = x i := by
  simp [extendPotential]

/-- A feasible DBM remains feasible after the source is added. -/
theorem satisfies_withSource {n : Nat} {G : List (Edge n)} {x : Fin n → Int}
    (hx : Satisfies G x) : Satisfies (withSource G) (extendPotential x) := by
  intro e he
  rw [withSource, List.mem_append] at he
  rcases he with he | he
  · rw [List.mem_map] at he
    obtain ⟨e, he, rfl⟩ := he
    simpa [liftEdge] using hx e he
  · rw [List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    simp only [sourceEdge, extendPotential_castSucc, extendPotential_last]
    have := le_sourceValue x i
    omega

/-- Every target has at least one simple path from the fresh source (empty at the source itself,
one direct edge everywhere else). -/
theorem source_pathWeights_nonempty {n : Nat} (G : List (Edge n)) :
    ∀ v : Fin (n + 1), pathWeights (withSource G) (Fin.last n) v ≠ [] := by
  apply Fin.lastCases
  · intro hnil
    have hp : ([] : List (Edge (n + 1))) ∈
        simplePathsTo (withSource G) (Fin.last n) (Fin.last n) :=
      mem_simplePathsTo_of_walk (by trivial) rfl (by simp [walkVertices])
    have : (0 : Int) ∈ pathWeights (withSource G) (Fin.last n) (Fin.last n) :=
      List.mem_map.mpr ⟨[], hp, by simp [walkWeight]⟩
    rw [hnil] at this
    exact List.not_mem_nil this
  · intro i hnil
    have hw : IsWalk (withSource G) (Fin.last n) [sourceEdge i] := by
      simp only [IsWalk]
      exact ⟨sourceEdge_mem_withSource i, rfl, trivial⟩
    have hend : walkEnd (Fin.last n) [sourceEdge i] = i.castSucc := by
      simp [walkEnd, sourceEdge]
    have hnod : (walkVertices (Fin.last n) [sourceEdge i]).Nodup := by
      simp only [walkVertices, List.map_singleton, sourceEdge]
      rw [List.nodup_cons]
      refine ⟨?_, by simp⟩
      simp only [List.mem_singleton]
      exact fun h => i.castSucc_ne_last h.symm
    have hp := mem_simplePathsTo_of_walk hw hend hnod
    have : (0 : Int) ∈ pathWeights (withSource G) (Fin.last n) i.castSucc :=
      List.mem_map.mpr ⟨[sourceEdge i], hp, by simp [walkWeight, sourceEdge]⟩
    rw [hnil] at this
    exact List.not_mem_nil this

/-- Constructive shortest-path potential for an original DBM. -/
def potential {n : Nat} (G : List (Edge n)) (i : Fin n) : Int :=
  shortest (withSource G) (Fin.last n) i.castSucc

/-- Absence of a negative cycle in the source-augmented graph constructs a satisfying potential. -/
theorem potential_satisfies {n : Nat} {G : List (Edge n)}
    (hno : ¬ NegativeCycle (withSource G)) : Satisfies G (potential G) := by
  intro e he
  have hrelax := shortest_relax hno (source_pathWeights_nonempty G)
    (liftEdge_mem_withSource he)
  change potential G e.dst - potential G e.src ≤ e.bound
  simp only [potential, liftEdge] at hrelax ⊢
  omega

/-- **DBM feasibility theorem.** A finite integer difference-bound graph has a satisfying point
iff its standard source augmentation has no negative cycle. The forward witness is the executable
shortest-path potential above. -/
theorem feasible_iff_noNegativeCycle {n : Nat} (G : List (Edge n)) :
    (∃ x, Satisfies G x) ↔ ¬ NegativeCycle (withSource G) := by
  constructor
  · rintro ⟨x, hx⟩
    exact noNegativeCycle_of_satisfies (satisfies_withSource hx)
  · intro hno
    exact ⟨potential G, potential_satisfies hno⟩

end DBM

/-! ## §2 Difference coordinates, cuts, and fragment extraction -/

/-- Which side of a transition a coordinate reads. -/
inductive FrameSlot where
  | old
  | new
  deriving DecidableEq, Repr

/-- A scalar coordinate `(field, frame-slot)`. -/
structure DiffCoord where
  slot : FrameSlot
  field : FieldName
  deriving DecidableEq, Repr

/-- DBM variables include a distinguished zero coordinate for axis thresholds. -/
inductive DiffVar where
  | zero
  | coord (q : DiffCoord)
  deriving DecidableEq, Repr

/-- A cut `lhs - rhs ≤ bound`. -/
structure DiffCut where
  lhs : DiffVar
  rhs : DiffVar
  bound : Int
  deriving DecidableEq, Repr

/-- Finite observations required by one predicate: scalar presence, difference cuts, and genuine
full-`Value` equalities. The equality pairs are retained because `fieldEqField` is not scalar-only. -/
structure DifferenceSpec where
  coords : List DiffCoord := []
  cuts : List DiffCut := []
  valueEqs : List (FieldName × FieldName) := []
  deriving Repr

namespace DifferenceSpec

def empty : DifferenceSpec := {}

def append (A B : DifferenceSpec) : DifferenceSpec where
  coords := A.coords ++ B.coords
  cuts := A.cuts ++ B.cuts
  valueEqs := A.valueEqs ++ B.valueEqs

instance : Append DifferenceSpec := ⟨append⟩

def Subset (A B : DifferenceSpec) : Prop :=
  A.coords ⊆ B.coords ∧ A.cuts ⊆ B.cuts ∧ A.valueEqs ⊆ B.valueEqs

theorem subset_append_left (A B : DifferenceSpec) : Subset A (A ++ B) := by
  exact ⟨fun _ h => List.mem_append.mpr (Or.inl h),
    fun _ h => List.mem_append.mpr (Or.inl h),
    fun _ h => List.mem_append.mpr (Or.inl h)⟩

theorem subset_append_right (A B : DifferenceSpec) : Subset B (A ++ B) := by
  exact ⟨fun _ h => List.mem_append.mpr (Or.inr h),
    fun _ h => List.mem_append.mpr (Or.inr h),
    fun _ h => List.mem_append.mpr (Or.inr h)⟩

end DifferenceSpec

private def oldQ (f : FieldName) : DiffCoord := ⟨.old, f⟩
private def newQ (f : FieldName) : DiffCoord := ⟨.new, f⟩
private def qv (q : DiffCoord) : DiffVar := .coord q

private def axisLe (q : DiffCoord) (c : Int) : DiffCut := ⟨qv q, .zero, c⟩
private def axisGe (q : DiffCoord) (c : Int) : DiffCut := ⟨.zero, qv q, -c⟩
private def diffLe (lhs rhs : DiffCoord) (c : Int) : DiffCut := ⟨qv lhs, qv rhs, c⟩
private def eqCuts (lhs rhs : DiffCoord) (d : Int) : List DiffCut :=
  [diffLe lhs rhs d, diffLe rhs lhs (-d)]

/-- Extract the DBM vocabulary of the supported simple atom. -/
def simpleDifference? : SimpleConstraint → Option DifferenceSpec
  | .fieldEquals f v => some ⟨[newQ f], [axisLe (newQ f) v, axisGe (newQ f) v], []⟩
  | .fieldGe f v => some ⟨[newQ f], [axisGe (newQ f) v], []⟩
  | .fieldLe f v => some ⟨[newQ f], [axisLe (newQ f) v], []⟩
  | .inRangeTwoSided f lo hi =>
      some ⟨[newQ f], [axisGe (newQ f) lo, axisLe (newQ f) hi], []⟩
  | .memberOf f set =>
      some ⟨[newQ f], set.flatMap (fun v => [axisLe (newQ f) v, axisGe (newQ f) v]), []⟩
  | .immutable f => some ⟨[oldQ f, newQ f], eqCuts (newQ f) (oldQ f) 0, []⟩
  | .writeOnce f => some ⟨[oldQ f, newQ f],
      [axisLe (oldQ f) 0, axisGe (oldQ f) 0] ++ eqCuts (newQ f) (oldQ f) 0, []⟩
  | .monotonic f => some ⟨[oldQ f, newQ f], [diffLe (oldQ f) (newQ f) 0], []⟩
  | .strictMono f => some ⟨[oldQ f, newQ f], [diffLe (oldQ f) (newQ f) (-1)], []⟩
  | .fieldDelta f d => some ⟨[oldQ f, newQ f], eqCuts (newQ f) (oldQ f) d, []⟩
  | .deltaBounded f d => some ⟨[oldQ f, newQ f],
      [diffLe (newQ f) (oldQ f) d, diffLe (oldQ f) (newQ f) d], []⟩
  | .not c => simpleDifference? c
  | _ => none

/-- Lift the vocabulary to the DBM-shaped `StateConstraint` arms. -/
def constraintDifference? : StateConstraint → Option DifferenceSpec
  | .simple c => simpleDifference? c
  | .fieldLeField l r => some ⟨[newQ l, newQ r], [diffLe (newQ l) (newQ r) 0], []⟩
  | .fieldDeltaInRange f lo hi => some ⟨[oldQ f, newQ f],
      [diffLe (oldQ f) (newQ f) (-lo), diffLe (newQ f) (oldQ f) hi], []⟩
  | _ => none

/-- Extract a whole leaf, including Boolean closure and general full-value field equality. -/
def predDifference? : Pred → Option DifferenceSpec
  | .tt => some .empty
  | .ff => some .empty
  | .atom c => constraintDifference? c
  | .fieldEqField f g => some ⟨[newQ f, newQ g], eqCuts (newQ f) (newQ g) 0, [(f, g)]⟩
  | .and l r | .or l r =>
      match predDifference? l, predDifference? r with
      | some A, some B => some (A ++ B)
      | _, _ => none
  | .not p => predDifference? p
  | _ => none

/-! ## §3 Observable signatures and leaf factoring -/

/-- Read one coordinate from a transition symbol. -/
def coordScalar (a : Value) (q : DiffCoord) : Option Int :=
  match q.slot with
  | .old => (PredRE.symbolOld a).scalar q.field
  | .new => a.scalar q.field

/-- Read a DBM variable; zero is always present and fixed. -/
def varScalar (a : Value) : DiffVar → Option Int
  | .zero => some 0
  | .coord q => coordScalar a q

/-- Truth of a cut, fail-closed when either scalar coordinate is absent/ill-typed. -/
def cutTruth (a : Value) (c : DiffCut) : Bool :=
  match varScalar a c.lhs, varScalar a c.rhs with
  | some x, some y => decide (x - y ≤ c.bound)
  | _, _ => false

/-- Genuine full-value equality in the new frame. -/
def valueEqTruth (a : Value) (p : FieldName × FieldName) : Bool :=
  leaf (.fieldEqField p.1 p.2) a

/-- Two symbols agree on every observation in a difference specification. -/
def SameDifference (S : DifferenceSpec) (a b : Value) : Prop :=
  (∀ q ∈ S.coords, (coordScalar a q).isSome = (coordScalar b q).isSome) ∧
  (∀ c ∈ S.cuts, cutTruth a c = cutTruth b c) ∧
  (∀ p ∈ S.valueEqs, valueEqTruth a p = valueEqTruth b p)

theorem SameDifference.mono {A B : DifferenceSpec} {a b : Value}
    (hsub : DifferenceSpec.Subset A B) (h : SameDifference B a b) : SameDifference A a b :=
  ⟨fun q hq => h.1 q (hsub.1 hq),
   fun c hc => h.2.1 c (hsub.2.1 hc),
   fun p hp => h.2.2 p (hsub.2.2 hp)⟩

private theorem bool_eq_of_iff {p q : Bool} (h : p = true ↔ q = true) : p = q := by
  cases p <;> cases q <;> simp_all

private theorem option_present_agree {x y : Option Int} (h : x.isSome = y.isSome) :
    (x = none ∧ y = none) ∨ ∃ a b, x = some a ∧ y = some b := by
  cases x <;> cases y <;> simp_all

private theorem coord_present_agree {S : DifferenceSpec} {a b : Value}
    (h : SameDifference S a b) {q : DiffCoord} (hq : q ∈ S.coords) :
    (coordScalar a q = none ∧ coordScalar b q = none) ∨
      ∃ x y, coordScalar a q = some x ∧ coordScalar b q = some y :=
  option_present_agree (h.1 q hq)

private theorem cut_iff_of_same {S : DifferenceSpec} {a b : Value}
    (h : SameDifference S a b) {c : DiffCut} (hc : c ∈ S.cuts)
    {x y x' y' : Int} (haL : varScalar a c.lhs = some x)
    (haR : varScalar a c.rhs = some y) (hbL : varScalar b c.lhs = some x')
    (hbR : varScalar b c.rhs = some y') :
    (x - y ≤ c.bound ↔ x' - y' ≤ c.bound) := by
  have hs := h.2.1 c hc
  simp only [cutTruth, haL, haR, hbL, hbR, decide_eq_decide] at hs
  exact hs

private theorem contains_congr_int {x y : Int} : ∀ {l : List Int},
    (∀ s ∈ l, ((x == s) = (y == s))) → l.contains x = l.contains y
  | [], _ => rfl
  | s :: rest, h => by
      simp only [List.contains_cons]
      rw [h s (by simp), contains_congr_int (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))]

private theorem axisLe_agree {S : DifferenceSpec} {a b : Value} (h : SameDifference S a b)
    {q : DiffCoord} {t x y : Int} (hc : axisLe q t ∈ S.cuts)
    (ha : coordScalar a q = some x) (hb : coordScalar b q = some y) :
    (x ≤ t ↔ y ≤ t) := by
  have hs := h.2.1 (axisLe q t) hc
  simp [cutTruth, axisLe, qv, varScalar, ha, hb, decide_eq_decide] at hs
  omega

private theorem axisGe_agree {S : DifferenceSpec} {a b : Value} (h : SameDifference S a b)
    {q : DiffCoord} {t x y : Int} (hc : axisGe q t ∈ S.cuts)
    (ha : coordScalar a q = some x) (hb : coordScalar b q = some y) :
    (t ≤ x ↔ t ≤ y) := by
  have hs := h.2.1 (axisGe q t) hc
  simp [cutTruth, axisGe, qv, varScalar, ha, hb, decide_eq_decide] at hs
  omega

private theorem diffLe_agree {S : DifferenceSpec} {a b : Value} (h : SameDifference S a b)
    {l r : DiffCoord} {t xl xr yl yr : Int} (hc : diffLe l r t ∈ S.cuts)
    (hal : coordScalar a l = some xl) (har : coordScalar a r = some xr)
    (hbl : coordScalar b l = some yl) (hbr : coordScalar b r = some yr) :
    (xl - xr ≤ t ↔ yl - yr ≤ t) := by
  have hs := h.2.1 (diffLe l r t) hc
  simp [cutTruth, diffLe, qv, varScalar, hal, har, hbl, hbr, decide_eq_decide] at hs
  constructor
  · intro hle
    have := hs.mp (by omega)
    omega
  · intro hle
    have := hs.mpr (by omega)
    omega

private theorem new_present_agree {S : DifferenceSpec} {a b : Value}
    (h : SameDifference S a b) {f : FieldName} (hf : newQ f ∈ S.coords) :
    (a.scalar f = none ∧ b.scalar f = none) ∨
      ∃ x y, a.scalar f = some x ∧ b.scalar f = some y := by
  simpa [coordScalar, newQ] using coord_present_agree h hf

private theorem old_present_agree {S : DifferenceSpec} {a b : Value}
    (h : SameDifference S a b) {f : FieldName} (hf : oldQ f ∈ S.coords) :
    ((PredRE.symbolOld a).scalar f = none ∧ (PredRE.symbolOld b).scalar f = none) ∨
      ∃ x y, (PredRE.symbolOld a).scalar f = some x ∧
        (PredRE.symbolOld b).scalar f = some y := by
  simpa [coordScalar, oldQ] using coord_present_agree h hf

/-- Every supported simple atom factors through its extracted DBM observations. -/
theorem simpleDifference?_reads {c : SimpleConstraint} {S : DifferenceSpec}
    (hS : simpleDifference? c = some S) {a b : Value} (hs : SameDifference S a b) :
    evalSimple c (PredRE.symbolOld a) a = evalSimple c (PredRE.symbolOld b) b := by
  induction c generalizing S with
  | fieldEquals f v =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases new_present_agree hs (f := f) (by simp) with ⟨ha, hb⟩ | ⟨x, y, ha, hb⟩
      · simp [evalSimple, ha, hb]
      · have hle := axisLe_agree hs (q := newQ f) (t := v) (by simp)
            (by simpa [coordScalar, newQ] using ha) (by simpa [coordScalar, newQ] using hb)
        have hge := axisGe_agree hs (q := newQ f) (t := v) (by simp)
            (by simpa [coordScalar, newQ] using ha) (by simpa [coordScalar, newQ] using hb)
        simp only [evalSimple, ha, hb]
        apply bool_eq_of_iff
        simp only [beq_iff_eq, Option.some.injEq]
        omega
  | fieldGe f v =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases new_present_agree hs (f := f) (by simp) with ⟨ha, hb⟩ | ⟨x, y, ha, hb⟩
      · simp [evalSimple, ha, hb]
      · have hge := axisGe_agree hs (q := newQ f) (t := v) (by simp)
            (by simpa [coordScalar, newQ] using ha) (by simpa [coordScalar, newQ] using hb)
        simp only [evalSimple, ha, hb]
        apply bool_eq_of_iff
        show decide (v ≤ x) = true ↔ decide (v ≤ y) = true
        simp only [decide_eq_true_eq]
        exact hge
  | fieldLe f v =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases new_present_agree hs (f := f) (by simp) with ⟨ha, hb⟩ | ⟨x, y, ha, hb⟩
      · simp [evalSimple, ha, hb]
      · have hle := axisLe_agree hs (q := newQ f) (t := v) (by simp)
            (by simpa [coordScalar, newQ] using ha) (by simpa [coordScalar, newQ] using hb)
        simp only [evalSimple, ha, hb]
        apply bool_eq_of_iff
        show decide (x ≤ v) = true ↔ decide (y ≤ v) = true
        simp only [decide_eq_true_eq]
        exact hle
  | inRangeTwoSided f lo hi =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases new_present_agree hs (f := f) (by simp) with ⟨ha, hb⟩ | ⟨x, y, ha, hb⟩
      · simp [evalSimple, ha, hb]
      · have hlo := axisGe_agree hs (q := newQ f) (t := lo) (by simp)
            (by simpa [coordScalar, newQ] using ha) (by simpa [coordScalar, newQ] using hb)
        have hhi := axisLe_agree hs (q := newQ f) (t := hi) (by simp)
            (by simpa [coordScalar, newQ] using ha) (by simpa [coordScalar, newQ] using hb)
        simp only [evalSimple, ha, hb]
        apply bool_eq_of_iff
        show (decide (lo ≤ x) && decide (x ≤ hi)) = true ↔
          (decide (lo ≤ y) && decide (y ≤ hi)) = true
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact and_congr hlo hhi
  | memberOf f set =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases new_present_agree hs (f := f) (by simp) with ⟨ha, hb⟩ | ⟨x, y, ha, hb⟩
      · simp [evalSimple, ha, hb]
      · simp only [evalSimple, ha, hb]
        apply contains_congr_int
        intro s hmem
        have hle := axisLe_agree hs (q := newQ f) (t := s)
          (List.mem_flatMap.mpr ⟨s, hmem, by simp⟩)
          (by simpa [coordScalar, newQ] using ha) (by simpa [coordScalar, newQ] using hb)
        have hge := axisGe_agree hs (q := newQ f) (t := s)
          (List.mem_flatMap.mpr ⟨s, hmem, by simp⟩)
          (by simpa [coordScalar, newQ] using ha) (by simpa [coordScalar, newQ] using hb)
        apply bool_eq_of_iff
        simp only [beq_iff_eq]
        omega
  | immutable f =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases old_present_agree hs (f := f) (by simp) with ⟨hoa, hob⟩ | ⟨x, y, hoa, hob⟩
      · simp [evalSimple, hoa, hob]
      · rcases new_present_agree hs (f := f) (by simp) with ⟨hna, hnb⟩ | ⟨u, v, hna, hnb⟩
        · simp [evalSimple, hoa, hob, hna, hnb]
        · have h1 := diffLe_agree hs (l := newQ f) (r := oldQ f) (t := 0) (by simp [eqCuts])
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hnb)
              (by simpa [coordScalar, oldQ] using hob)
          have h2 := diffLe_agree hs (l := oldQ f) (r := newQ f) (t := 0) (by simp [eqCuts])
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hob)
              (by simpa [coordScalar, newQ] using hnb)
          simp only [evalSimple, hoa, hob, hna, hnb]
          apply bool_eq_of_iff
          simp only [beq_iff_eq, Option.some.injEq]
          omega
  | writeOnce f =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases old_present_agree hs (f := f) (by simp) with ⟨hoa, hob⟩ | ⟨x, y, hoa, hob⟩
      · simp [evalSimple, hoa, hob]
      · have hle := axisLe_agree hs (q := oldQ f) (t := 0) (by simp)
            (by simpa [coordScalar, oldQ] using hoa) (by simpa [coordScalar, oldQ] using hob)
        have hge := axisGe_agree hs (q := oldQ f) (t := 0) (by simp)
            (by simpa [coordScalar, oldQ] using hoa) (by simpa [coordScalar, oldQ] using hob)
        have hzero : (x = 0 ↔ y = 0) := by omega
        by_cases hx : x = 0
        · have hy := hzero.mp hx
          subst x; subst y
          simp [evalSimple, hoa, hob]
        · have hy : y ≠ 0 := fun hy => hx (hzero.mpr hy)
          rcases new_present_agree hs (f := f) (by simp) with ⟨hna, hnb⟩ | ⟨u, v, hna, hnb⟩
          · simp [evalSimple, hoa, hob, hna, hnb, hx, hy]
          · have h1 := diffLe_agree hs (l := newQ f) (r := oldQ f) (t := 0) (by simp [eqCuts])
                (by simpa [coordScalar, newQ] using hna)
                (by simpa [coordScalar, oldQ] using hoa)
                (by simpa [coordScalar, newQ] using hnb)
                (by simpa [coordScalar, oldQ] using hob)
            have h2 := diffLe_agree hs (l := oldQ f) (r := newQ f) (t := 0) (by simp [eqCuts])
                (by simpa [coordScalar, oldQ] using hoa)
                (by simpa [coordScalar, newQ] using hna)
                (by simpa [coordScalar, oldQ] using hob)
                (by simpa [coordScalar, newQ] using hnb)
            simp only [evalSimple, hoa, hob, hna, hnb]
            apply bool_eq_of_iff
            simp only [beq_iff_eq, Option.some.injEq]
            omega
  | monotonic f =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases old_present_agree hs (f := f) (by simp) with ⟨hoa, hob⟩ | ⟨x, y, hoa, hob⟩
      · simp [evalSimple, hoa, hob]
      · rcases new_present_agree hs (f := f) (by simp) with ⟨hna, hnb⟩ | ⟨u, v, hna, hnb⟩
        · simp [evalSimple, hoa, hob, hna, hnb]
        · have hd := diffLe_agree hs (l := oldQ f) (r := newQ f) (t := 0) (by simp)
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hob)
              (by simpa [coordScalar, newQ] using hnb)
          simp only [evalSimple, hoa, hob, hna, hnb]
          apply bool_eq_of_iff
          show decide (x ≤ u) = true ↔ decide (y ≤ v) = true
          simp only [decide_eq_true_eq]
          omega
  | strictMono f =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases old_present_agree hs (f := f) (by simp) with ⟨hoa, hob⟩ | ⟨x, y, hoa, hob⟩
      · simp [evalSimple, hoa, hob]
      · rcases new_present_agree hs (f := f) (by simp) with ⟨hna, hnb⟩ | ⟨u, v, hna, hnb⟩
        · simp [evalSimple, hoa, hob, hna, hnb]
        · have hd := diffLe_agree hs (l := oldQ f) (r := newQ f) (t := -1) (by simp)
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hob)
              (by simpa [coordScalar, newQ] using hnb)
          simp only [evalSimple, hoa, hob, hna, hnb]
          apply bool_eq_of_iff
          show decide (x < u) = true ↔ decide (y < v) = true
          simp only [decide_eq_true_eq]
          omega
  | fieldDelta f d =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases old_present_agree hs (f := f) (by simp) with ⟨hoa, hob⟩ | ⟨x, y, hoa, hob⟩
      · simp [evalSimple, hoa, hob]
      · rcases new_present_agree hs (f := f) (by simp) with ⟨hna, hnb⟩ | ⟨u, v, hna, hnb⟩
        · simp [evalSimple, hoa, hob, hna, hnb]
        · have h1 := diffLe_agree hs (l := newQ f) (r := oldQ f) (t := d) (by simp [eqCuts])
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hnb)
              (by simpa [coordScalar, oldQ] using hob)
          have h2 := diffLe_agree hs (l := oldQ f) (r := newQ f) (t := -d) (by simp [eqCuts])
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hob)
              (by simpa [coordScalar, newQ] using hnb)
          simp only [evalSimple, hoa, hob, hna, hnb]
          apply bool_eq_of_iff
          simp only [beq_iff_eq]
          omega
  | deltaBounded f d =>
      simp only [simpleDifference?, Option.some.injEq] at hS
      subst S
      rcases old_present_agree hs (f := f) (by simp) with ⟨hoa, hob⟩ | ⟨x, y, hoa, hob⟩
      · simp [evalSimple, hoa, hob]
      · rcases new_present_agree hs (f := f) (by simp) with ⟨hna, hnb⟩ | ⟨u, v, hna, hnb⟩
        · simp [evalSimple, hoa, hob, hna, hnb]
        · have h1 := diffLe_agree hs (l := newQ f) (r := oldQ f) (t := d) (by simp)
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hnb)
              (by simpa [coordScalar, oldQ] using hob)
          have h2 := diffLe_agree hs (l := oldQ f) (r := newQ f) (t := d) (by simp)
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hob)
              (by simpa [coordScalar, newQ] using hnb)
          simp only [evalSimple, hoa, hob, hna, hnb]
          apply bool_eq_of_iff
          show (decide (-d ≤ u - x) && decide (u - x ≤ d)) = true ↔
            (decide (-d ≤ v - y) && decide (v - y ≤ d)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
  | not c ih =>
      simp only [simpleDifference?] at hS
      have h := ih hS hs
      rw [evalSimple_not, evalSimple_not, h]
  | prefixOf _ _ => simp [simpleDifference?] at hS
  | senderIs _ => simp [simpleDifference?] at hS
  | senderInField _ => simp [simpleDifference?] at hS
  | balanceGe _ => simp [simpleDifference?] at hS
  | balanceLe _ => simp [simpleDifference?] at hS
  | preimageGate _ => simp [simpleDifference?] at hS
  | delegationEpochEquals _ => simp [simpleDifference?] at hS
  | countGe _ _ => simp [simpleDifference?] at hS
  | senderMemberOf _ => simp [simpleDifference?] at hS
  | balanceDeltaLe _ => simp [simpleDifference?] at hS
  | balanceDeltaGe _ => simp [simpleDifference?] at hS
  | balanceDeltaLeField _ => simp [simpleDifference?] at hS
  | wakeOnResolve _ _ _ => simp [simpleDifference?] at hS

/-- State-constraint factoring for the simple embedding and the two native DBM arms. -/
theorem constraintDifference?_reads {c : StateConstraint} {S : DifferenceSpec}
    (hS : constraintDifference? c = some S) {a b : Value} (hs : SameDifference S a b) :
    evalConstraint c (PredRE.symbolOld a) a = evalConstraint c (PredRE.symbolOld b) b := by
  cases c with
  | simple sc =>
      simp only [constraintDifference?] at hS
      simp only [evalConstraint]
      exact simpleDifference?_reads hS hs
  | fieldLeField l r =>
      simp only [constraintDifference?, Option.some.injEq] at hS
      subst S
      rcases new_present_agree hs (f := l) (by simp) with ⟨hla, hlb⟩ | ⟨x, y, hla, hlb⟩
      · simp [evalConstraint, hla, hlb]
      · rcases new_present_agree hs (f := r) (by simp) with ⟨hra, hrb⟩ | ⟨u, v, hra, hrb⟩
        · simp [evalConstraint, hla, hlb, hra, hrb]
        · have hd := diffLe_agree hs (l := newQ l) (r := newQ r) (t := 0) (by simp)
              (by simpa [coordScalar, newQ] using hla)
              (by simpa [coordScalar, newQ] using hra)
              (by simpa [coordScalar, newQ] using hlb)
              (by simpa [coordScalar, newQ] using hrb)
          simp only [evalConstraint, hla, hlb, hra, hrb]
          apply bool_eq_of_iff
          show decide (x ≤ u) = true ↔ decide (y ≤ v) = true
          simp only [decide_eq_true_eq]
          omega
  | fieldDeltaInRange f lo hi =>
      simp only [constraintDifference?, Option.some.injEq] at hS
      subst S
      rcases old_present_agree hs (f := f) (by simp) with ⟨hoa, hob⟩ | ⟨x, y, hoa, hob⟩
      · simp [evalConstraint, hoa, hob]
      · rcases new_present_agree hs (f := f) (by simp) with ⟨hna, hnb⟩ | ⟨u, v, hna, hnb⟩
        · simp [evalConstraint, hoa, hob, hna, hnb]
        · have hlo := diffLe_agree hs (l := oldQ f) (r := newQ f) (t := -lo) (by simp)
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hob)
              (by simpa [coordScalar, newQ] using hnb)
          have hhi := diffLe_agree hs (l := newQ f) (r := oldQ f) (t := hi) (by simp)
              (by simpa [coordScalar, newQ] using hna)
              (by simpa [coordScalar, oldQ] using hoa)
              (by simpa [coordScalar, newQ] using hnb)
              (by simpa [coordScalar, oldQ] using hob)
          simp only [evalConstraint, hoa, hob, hna, hnb]
          apply bool_eq_of_iff
          show (decide (x + lo ≤ u) && decide (u ≤ x + hi)) = true ↔
            (decide (y + lo ≤ v) && decide (v ≤ y + hi)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
  | sumEquals _ _ => simp [constraintDifference?] at hS
  | sumEqualsAcross _ _ => simp [constraintDifference?] at hS
  | allowedTransitions _ _ => simp [constraintDifference?] at hS
  | anyOf _ => simp [constraintDifference?] at hS
  | boundDelta _ _ _ _ => simp [constraintDifference?] at hS
  | clearanceGe _ _ _ => simp [constraintDifference?] at hS
  | affineLe _ _ => simp [constraintDifference?] at hS
  | affineEq _ _ => simp [constraintDifference?] at hS
  | reachable _ _ _ => simp [constraintDifference?] at hS
  | affineDeltaLe _ _ => simp [constraintDifference?] at hS
  | affineDeltaLeField _ _ => simp [constraintDifference?] at hS
  | observedFieldEquals _ _ _ => simp [constraintDifference?] at hS
  | anyOfBound _ => simp [constraintDifference?] at hS
  | countFieldsEq _ _ _ => simp [constraintDifference?] at hS

private def predMeasure : Pred → Nat
  | .and l r | .or l r => predMeasure l + predMeasure r + 1
  | .not p => predMeasure p + 1
  | _ => 1

/-- Every supported `Pred` leaf factors through the finite difference signature. -/
theorem predDifference?_reads : ∀ {p : Pred} {S : DifferenceSpec},
    predDifference? p = some S → ∀ {a b : Value}, SameDifference S a b → leaf p a = leaf p b
  | .tt, _, _, _, _, _ => rfl
  | .ff, _, _, _, _, _ => rfl
  | .atom c, S, hS, a, b, hs => by
      simp only [predDifference?] at hS
      show Pred.eval (.atom c) (PredRE.symbolOld a) a =
        Pred.eval (.atom c) (PredRE.symbolOld b) b
      simp only [Pred.eval]
      exact constraintDifference?_reads hS hs
  | .fieldEqField f g, S, hS, a, b, hs => by
      simp only [predDifference?, Option.some.injEq] at hS
      subst S
      exact hs.2.2 (f, g) (by simp)
  | .and l r, S, hS, a, b, hs => by
      simp only [predDifference?] at hS
      cases hl : predDifference? l with
      | none => rw [hl] at hS; simp at hS
      | some A =>
        cases hr : predDifference? r with
        | none => rw [hl, hr] at hS; simp at hS
        | some B =>
          rw [hl, hr, Option.some.injEq] at hS
          subst S
          have il := predDifference?_reads hl (hs.mono (DifferenceSpec.subset_append_left A B))
          have ir := predDifference?_reads hr (hs.mono (DifferenceSpec.subset_append_right A B))
          simp only [leaf, Pred.eval] at il ir ⊢
          rw [il, ir]
  | .or l r, S, hS, a, b, hs => by
      simp only [predDifference?] at hS
      cases hl : predDifference? l with
      | none => rw [hl] at hS; simp at hS
      | some A =>
        cases hr : predDifference? r with
        | none => rw [hl, hr] at hS; simp at hS
        | some B =>
          rw [hl, hr, Option.some.injEq] at hS
          subst S
          have il := predDifference?_reads hl (hs.mono (DifferenceSpec.subset_append_left A B))
          have ir := predDifference?_reads hr (hs.mono (DifferenceSpec.subset_append_right A B))
          simp only [leaf, Pred.eval] at il ir ⊢
          rw [il, ir]
  | .not p, S, hS, a, b, hs => by
      simp only [predDifference?] at hS
      have ih := predDifference?_reads hS hs
      simp only [leaf, Pred.eval] at ih ⊢
      rw [ih]
  | .allOf _, _, hS, _, _, _ => by simp [predDifference?] at hS
  | .anyOf _, _, hS, _, _, _ => by simp [predDifference?] at hS
  | .symEq _ _, _, hS, _, _, _ => by simp [predDifference?] at hS
  | .symMemberOf _ _, _, hS, _, _, _ => by simp [predDifference?] at hS
  | .digEq _ _, _, hS, _, _, _ => by simp [predDifference?] at hS
  | .digFieldEq _ _, _, hS, _, _, _ => by simp [predDifference?] at hS
  | .symUnchanged _, _, hS, _, _, _ => by simp [predDifference?] at hS
  | .symChanged _, _, hS, _, _, _ => by simp [predDifference?] at hS
  | .digUnchanged _, _, hS, _, _, _ => by simp [predDifference?] at hS
  | .digChanged _, _, hS, _, _, _ => by simp [predDifference?] at hS
termination_by p S hS a b hs => predMeasure p
decreasing_by all_goals simp [predMeasure] <;> omega

/-! ## §4 From Boolean cut regions to finite shortest-path representatives -/

/-- The finite DBM vertex list. Cut endpoints are included explicitly, so the graph construction
does not rely on a well-formedness side condition from extraction. -/
def specVars (S : DifferenceSpec) : List DiffVar :=
  (.zero :: (S.coords.map DiffVar.coord ++
    S.cuts.flatMap (fun c => [c.lhs, c.rhs]))).dedup

theorem zero_mem_specVars (S : DifferenceSpec) : .zero ∈ specVars S := by
  simp [specVars]

theorem coord_mem_specVars {S : DifferenceSpec} {q : DiffCoord} (hq : q ∈ S.coords) :
    .coord q ∈ specVars S := by
  simp only [specVars, List.mem_dedup, List.mem_cons, List.mem_append, List.mem_map]
  exact Or.inr (Or.inl ⟨q, hq, rfl⟩)

theorem cut_lhs_mem_specVars {S : DifferenceSpec} {c : DiffCut} (hc : c ∈ S.cuts) :
    c.lhs ∈ specVars S := by
  simp only [specVars, List.mem_dedup, List.mem_cons, List.mem_append, List.mem_flatMap]
  exact Or.inr (Or.inr ⟨c, hc, by simp⟩)

theorem cut_rhs_mem_specVars {S : DifferenceSpec} {c : DiffCut} (hc : c ∈ S.cuts) :
    c.rhs ∈ specVars S := by
  simp only [specVars, List.mem_dedup, List.mem_cons, List.mem_append, List.mem_flatMap]
  exact Or.inr (Or.inr ⟨c, hc, by simp⟩)

/-- Index of a known vertex in the deduplicated vertex list. -/
def varFin (S : DifferenceSpec) (v : DiffVar) (hv : v ∈ specVars S) : Fin (specVars S).length :=
  ⟨(specVars S).idxOf v, List.idxOf_lt_length_of_mem hv⟩

theorem get_varFin (S : DifferenceSpec) (v : DiffVar) (hv : v ∈ specVars S) :
    (specVars S).get (varFin S v hv) = v := by
  apply List.getElem_idxOf

/-- The positive edge for a cut. -/
def positiveEdge (S : DifferenceSpec) (c : DiffCut) (hc : c ∈ S.cuts) :
    DBM.Edge (specVars S).length :=
  ⟨varFin S c.rhs (cut_rhs_mem_specVars hc),
   varFin S c.lhs (cut_lhs_mem_specVars hc), c.bound⟩

/-- The integer complement of `lhs-rhs ≤ c` is `rhs-lhs ≤ -c-1`. -/
def negativeEdge (S : DifferenceSpec) (c : DiffCut) (hc : c ∈ S.cuts) :
    DBM.Edge (specVars S).length :=
  ⟨varFin S c.lhs (cut_lhs_mem_specVars hc),
   varFin S c.rhs (cut_rhs_mem_specVars hc), -c.bound - 1⟩

/-- Enumerate absent / true / false orientations for every cut. -/
def cutRegions (S : DifferenceSpec) :
    ∀ cs : List DiffCut, (∀ c ∈ cs, c ∈ S.cuts) → List (List (DBM.Edge (specVars S).length))
  | [], _ => [[]]
  | c :: cs, hsub =>
      let tail := cutRegions S cs (fun d hd => hsub d (List.mem_cons_of_mem _ hd))
      let hp : c ∈ S.cuts := hsub c (by simp)
      tail ++ tail.map (fun G => positiveEdge S c hp :: G) ++
        tail.map (fun G => negativeEdge S c hp :: G)

/-- All DBM regions induced by the specification. -/
def allRegions (S : DifferenceSpec) : List (List (DBM.Edge (specVars S).length)) :=
  cutRegions S S.cuts (fun _ h => h)

/-- The region selected by a concrete symbol: absent cut endpoints contribute no edge; present
endpoints contribute exactly the true edge or its integer complement. -/
def regionOf (S : DifferenceSpec) (a : Value) :
    ∀ cs : List DiffCut, (∀ c ∈ cs, c ∈ S.cuts) → List (DBM.Edge (specVars S).length)
  | [], _ => []
  | c :: cs, hsub =>
      let hp : c ∈ S.cuts := hsub c (by simp)
      let tail := regionOf S a cs (fun d hd => hsub d (List.mem_cons_of_mem _ hd))
      match varScalar a c.lhs, varScalar a c.rhs with
      | some _, some _ => if cutTruth a c then positiveEdge S c hp :: tail
                          else negativeEdge S c hp :: tail
      | _, _ => tail

def selectedRegion (S : DifferenceSpec) (a : Value) : List (DBM.Edge (specVars S).length) :=
  regionOf S a S.cuts (fun _ h => h)

/-- Every concrete symbol selects one of the finitely enumerated regions. -/
theorem regionOf_mem_cutRegions (S : DifferenceSpec) (a : Value) :
    ∀ (cs : List DiffCut) (hsub : ∀ c ∈ cs, c ∈ S.cuts),
      regionOf S a cs hsub ∈ cutRegions S cs hsub := by
  intro cs
  induction cs with
  | nil => intro hsub; simp [regionOf, cutRegions]
  | cons c cs ih =>
      intro hsub
      simp only [regionOf, cutRegions]
      let hp : c ∈ S.cuts := hsub c (by simp)
      let ht : ∀ d ∈ cs, d ∈ S.cuts := fun d hd => hsub d (List.mem_cons_of_mem _ hd)
      have hi := ih ht
      cases hl : varScalar a c.lhs <;> cases hr : varScalar a c.rhs
      all_goals simp only [hl, hr]
      · apply List.mem_append.mpr; apply Or.inl
        apply List.mem_append.mpr; apply Or.inl
        simpa only using hi
      · apply List.mem_append.mpr; apply Or.inl
        apply List.mem_append.mpr; apply Or.inl
        simpa only using hi
      · apply List.mem_append.mpr; apply Or.inl
        apply List.mem_append.mpr; apply Or.inl
        simpa only using hi
      · by_cases hcut : cutTruth a c = true
        · rw [if_pos hcut]
          apply List.mem_append.mpr; apply Or.inl
          apply List.mem_append.mpr; apply Or.inr
          apply List.mem_map.mpr
          exact ⟨_, by simpa only using hi, rfl⟩
        · rw [if_neg (by simpa using hcut)]
          apply List.mem_append.mpr; apply Or.inr
          apply List.mem_map.mpr
          exact ⟨_, by simpa only using hi, rfl⟩

theorem selectedRegion_mem (S : DifferenceSpec) (a : Value) :
    selectedRegion S a ∈ allRegions S :=
  regionOf_mem_cutRegions S a S.cuts (fun _ h => h)

/-- Concrete assignment on the finite vertex list; absent vertices get an irrelevant zero. -/
def concretePotential (S : DifferenceSpec) (a : Value) (i : Fin (specVars S).length) : Int :=
  (varScalar a ((specVars S).get i)).getD 0

theorem concretePotential_var (S : DifferenceSpec) (a : Value) (v : DiffVar)
    (hv : v ∈ specVars S) :
    concretePotential S a (varFin S v hv) = (varScalar a v).getD 0 := by
  unfold concretePotential
  rw [get_varFin]

/-- The concrete symbol satisfies every edge of its selected region. -/
theorem concrete_satisfies_regionOf (S : DifferenceSpec) (a : Value) :
    ∀ (cs : List DiffCut) (hsub : ∀ c ∈ cs, c ∈ S.cuts),
      DBM.Satisfies (regionOf S a cs hsub) (concretePotential S a) := by
  intro cs
  induction cs with
  | nil => intro hsub e he; simp [regionOf] at he
  | cons c cs ih =>
      intro hsub
      let hp : c ∈ S.cuts := hsub c (by simp)
      let ht : ∀ d ∈ cs, d ∈ S.cuts := fun d hd => hsub d (List.mem_cons_of_mem _ hd)
      have hit := ih ht
      simp only [regionOf]
      cases hl : varScalar a c.lhs with
      | none => simpa [hl] using hit
      | some x =>
        cases hr : varScalar a c.rhs with
        | none => simpa [hl, hr] using hit
        | some y =>
          by_cases hcut : cutTruth a c = true
          · rw [if_pos hcut]
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · simp only [positiveEdge]
              rw [concretePotential_var S a c.rhs (cut_rhs_mem_specVars hp),
                  concretePotential_var S a c.lhs (cut_lhs_mem_specVars hp), hl, hr]
              simp only [Option.getD_some]
              simpa [cutTruth, hl, hr] using hcut
            · exact hit e he
          · rw [if_neg (by simpa using hcut)]
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · simp only [negativeEdge]
              rw [concretePotential_var S a c.lhs (cut_lhs_mem_specVars hp),
                  concretePotential_var S a c.rhs (cut_rhs_mem_specVars hp), hl, hr]
              simp only [Option.getD_some]
              have hn : ¬ x - y ≤ c.bound := by
                intro hxy
                apply hcut
                simp [cutTruth, hl, hr, hxy]
              omega
            · exact hit e he

theorem concrete_satisfies_selectedRegion (S : DifferenceSpec) (a : Value) :
    DBM.Satisfies (selectedRegion S a) (concretePotential S a) :=
  concrete_satisfies_regionOf S a S.cuts (fun _ h => h)

/-- Normalize a region's shortest-path potential so the distinguished zero variable is exactly 0. -/
def regionValue (S : DifferenceSpec) (G : List (DBM.Edge (specVars S).length))
    (v : DiffVar) (hv : v ∈ specVars S) : Int :=
  DBM.potential G (varFin S v hv) -
    DBM.potential G (varFin S .zero (zero_mem_specVars S))

/-- Finite pool containing every coordinate of every region witness. -/
def differenceValues (S : DifferenceSpec) : List Int :=
  (allRegions S).flatMap fun G =>
    (List.ofFn fun i : Fin (specVars S).length =>
      DBM.potential G i - DBM.potential G (varFin S .zero (zero_mem_specVars S)))

theorem regionValue_mem (S : DifferenceSpec) {G : List (DBM.Edge (specVars S).length)}
    (hG : G ∈ allRegions S) (v : DiffVar) (hv : v ∈ specVars S) :
    regionValue S G v hv ∈ differenceValues S := by
  apply List.mem_flatMap.mpr
  refine ⟨G, hG, ?_⟩
  rw [List.mem_ofFn]
  exact ⟨varFin S v hv, rfl⟩

/-- The normalized shortest-path witness satisfies every selected-region edge. -/
theorem selectedRegion_regionValue_satisfies (S : DifferenceSpec) (a : Value) :
    DBM.Satisfies (selectedRegion S a)
      (fun i => DBM.potential (selectedRegion S a) i -
        DBM.potential (selectedRegion S a) (varFin S .zero (zero_mem_specVars S))) := by
  have hno : ¬ DBM.NegativeCycle (DBM.withSource (selectedRegion S a)) :=
    (DBM.feasible_iff_noNegativeCycle _).mp ⟨_, concrete_satisfies_selectedRegion S a⟩
  have hp := DBM.potential_satisfies hno
  intro e he
  have := hp e he
  change (DBM.potential (selectedRegion S a) e.dst -
      DBM.potential (selectedRegion S a) (varFin S .zero (zero_mem_specVars S))) -
    (DBM.potential (selectedRegion S a) e.src -
      DBM.potential (selectedRegion S a) (varFin S .zero (zero_mem_specVars S))) ≤ e.bound
  omega

/-! ## §5 Finite transition symbols -/

/-- Fields occurring at an OLD scalar coordinate. -/
def differenceOldFields (S : DifferenceSpec) : List FieldName :=
  ((specVars S).filterMap fun
    | DiffVar.coord ⟨FrameSlot.old, f⟩ => some f
    | _ => none).dedup

/-- Fields occurring at a NEW scalar coordinate, or in a full-value equality probe. -/
def differenceNewFields (S : DifferenceSpec) : List FieldName :=
  (((specVars S).filterMap fun
      | DiffVar.coord ⟨FrameSlot.new, f⟩ => some f
      | _ => none) ++ S.valueEqs.flatMap (fun p : FieldName × FieldName => [p.1, p.2])).dedup

/-- An equality-class label for a present value. -/
def observedLabel (S : DifferenceSpec) (a v : Value) : Nat :=
  (differenceNewFields S).findIdx fun f =>
    match a.field f with
    | some w => Value.beq w v
    | none => false

/-- Canonical OLD-field choice: preserve scalar absence, and otherwise use the normalized
shortest-path coordinate of the selected DBM region. -/
def canonicalOldChoice (S : DifferenceSpec) (a : Value) (f : FieldName) : Option Value :=
  if hq : .coord (oldQ f) ∈ specVars S then
    match (PredRE.symbolOld a).scalar f with
    | some _ => some (.int (regionValue S (selectedRegion S a) (.coord (oldQ f)) hq))
    | none => none
  else none

/-- Canonical NEW-field choice. Scalar values use the DBM witness; all other present values use
a finite equality-class symbol, preserving full `fieldEqField` observations. -/
def canonicalNewChoice (S : DifferenceSpec) (a : Value) (f : FieldName) : Option Value :=
  match a.field f with
  | none => none
  | some v =>
      if hq : .coord (newQ f) ∈ specVars S then
        match v with
        | .int _ => some (.int (regionValue S (selectedRegion S a) (.coord (newQ f)) hq))
        | _ => some (.sym (observedLabel S a v))
      else some (.sym (observedLabel S a v))

/-- Choice-built record, shared by the OLD and NEW products. -/
def choiceRecord (fs : List FieldName) (g : FieldName → Option Value) : Value :=
  .record (fs.filterMap (fun f => (g f).map (fun v => (f, v))))

def canonicalOld (S : DifferenceSpec) (a : Value) : Value :=
  choiceRecord (differenceOldFields S) (canonicalOldChoice S a)

def canonicalNew (S : DifferenceSpec) (a : Value) : Value :=
  choiceRecord (differenceNewFields S) (canonicalNewChoice S a)

/-- The concrete finite representative of a symbol. -/
def restrictDifferenceSymbol (S : DifferenceSpec) (a : Value) : Value :=
  PredRE.transitionSymbol (canonicalOld S a) (canonicalNew S a)

/-- Field lookup on a record built from distinct field choices. -/
theorem valueField_ofChoices {g : FieldName → Option Value} :
    ∀ {fs : List FieldName}, fs.Nodup → ∀ {f : FieldName}, f ∈ fs →
      (choiceRecord fs g).field f = g f := by
  intro fs
  induction fs with
  | nil => intro _ f hf; simp at hf
  | cons x xs ih =>
      intro hnd f hf
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      by_cases hfx : f = x
      · subst x
        cases hgf : g f with
        | none =>
            simp only [choiceRecord]
            rw [List.filterMap_cons_none (by rw [hgf]; rfl)]
            simp only [Value.field]
            rw [List.find?_eq_none.mpr, Option.map_none]
            intro p hp
            obtain ⟨y, hy, hpy⟩ := List.mem_filterMap.mp hp
            cases hgy : g y with
            | none => rw [hgy] at hpy; simp at hpy
            | some v =>
                rw [hgy] at hpy
                simp only [Option.map_some, Option.some.injEq] at hpy
                subst p
                simp only [Bool.not_eq_true, beq_eq_false_iff_ne, ne_eq]
                intro hyf
                exact hx (hyf ▸ hy)
        | some v =>
            simp only [choiceRecord]
            rw [List.filterMap_cons_some (by rw [hgf]; rfl)]
            simp only [Value.field]
            rw [List.find?_cons_of_pos (by simp)]
            rfl
      · have hf' : f ∈ xs := by
          rcases List.mem_cons.mp hf with h | h
          · exact absurd h hfx
          · exact h
        cases hgx : g x with
        | none =>
            simp only [choiceRecord]
            rw [List.filterMap_cons_none (by rw [hgx]; rfl)]
            exact ih hnd' hf'
        | some v =>
            simp only [choiceRecord]
            rw [List.filterMap_cons_some (by rw [hgx]; rfl)]
            simp only [Value.field]
            rw [List.find?_cons_of_neg (by simpa using fun h => hfx h.symm)]
            exact ih hnd' hf'

/-- Scalar lookup on a choice-built record. -/
theorem valueScalar_ofChoices {g : FieldName → Option Value} {fs : List FieldName}
    (hnd : fs.Nodup) {f : FieldName} (hf : f ∈ fs) :
    (choiceRecord fs g).scalar f =
      match g f with | some (.int i) => some i | _ => none := by
  simp only [Value.scalar, valueField_ofChoices hnd hf]
  cases g f with
  | none => rfl
  | some v => cases v <;> rfl

/-- Uniform finite OLD choices: absent or any shortest-path integer. -/
def oldValueChoices (S : DifferenceSpec) : List (Option Value) :=
  none :: (differenceValues S).map (fun x => some (.int x))

/-- Uniform finite NEW choices: absent, any shortest-path integer, or one of finitely many
full-value equality labels. -/
def newValueChoices (S : DifferenceSpec) : List (Option Value) :=
  none :: (differenceValues S).map (fun x => some (.int x)) ++
    (List.range (differenceNewFields S).length).map (fun k => some (.sym k))

/-- Product of one finite option list over a finite field list. -/
def choiceRecords (fs : List FieldName) (opts : List (Option Value)) : List Value :=
  ((fs.map (fun f => opts.map (fun o => (f, o)))).sections).map
    (fun ch => .record (ch.filterMap (fun p => p.2.map (fun v => (p.1, v)))))

/-- The finite transition alphabet for a difference specification. -/
def differenceCands (S : DifferenceSpec) : List Value :=
  (choiceRecords (differenceOldFields S) (oldValueChoices S)).flatMap fun old =>
    (choiceRecords (differenceNewFields S) (newValueChoices S)).map fun new =>
      PredRE.transitionSymbol old new

/-- The transition envelope reserves two NEW-field names. Difference fragments fail closed unless
their mentioned NEW fields avoid those names. -/
def SafeDifference (S : DifferenceSpec) : Prop :=
  PredRE.transitionTagField ∉ differenceNewFields S ∧
    PredRE.transitionOldField ∉ differenceNewFields S

theorem oldField_mem_differenceOldFields {S : DifferenceSpec} {f : FieldName}
    (hq : .coord (oldQ f) ∈ specVars S) : f ∈ differenceOldFields S := by
  simp only [differenceOldFields, List.mem_dedup, List.mem_filterMap]
  exact ⟨.coord (oldQ f), hq, rfl⟩

theorem newField_mem_differenceNewFields {S : DifferenceSpec} {f : FieldName}
    (hq : .coord (newQ f) ∈ specVars S) : f ∈ differenceNewFields S := by
  simp only [differenceNewFields, List.mem_dedup, List.mem_append, List.mem_filterMap]
  exact Or.inl ⟨.coord (newQ f), hq, rfl⟩

theorem valueEq_left_mem_differenceNewFields {S : DifferenceSpec} {f g : FieldName}
    (hp : (f, g) ∈ S.valueEqs) : f ∈ differenceNewFields S := by
  simp only [differenceNewFields, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(f, g), hp, by simp⟩

theorem valueEq_right_mem_differenceNewFields {S : DifferenceSpec} {f g : FieldName}
    (hp : (f, g) ∈ S.valueEqs) : g ∈ differenceNewFields S := by
  simp only [differenceNewFields, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(f, g), hp, by simp⟩

/-- Authored NEW fields survive the reserved transition prefix. -/
theorem transitionSymbol_field {old : Value} {fs : List (FieldName × Value)} {f : FieldName}
    (htag : f ≠ PredRE.transitionTagField) (hold : f ≠ PredRE.transitionOldField) :
    (PredRE.transitionSymbol old (Value.record fs)).field f = (Value.record fs).field f := by
  unfold PredRE.transitionSymbol
  simp only [Value.field]
  rw [List.find?_cons_of_neg (by simpa using htag.symm),
    List.find?_cons_of_neg (by simpa using hold.symm)]

theorem transitionSymbol_scalar {old : Value} {fs : List (FieldName × Value)} {f : FieldName}
    (htag : f ≠ PredRE.transitionTagField) (hold : f ≠ PredRE.transitionOldField) :
    (PredRE.transitionSymbol old (Value.record fs)).scalar f = (Value.record fs).scalar f := by
  simp only [Value.scalar, transitionSymbol_field htag hold]

theorem symbolOld_restrictDifferenceSymbol (S : DifferenceSpec) (a : Value) :
    PredRE.symbolOld (restrictDifferenceSymbol S a) = canonicalOld S a := by
  simp [restrictDifferenceSymbol, canonicalNew, choiceRecord, PredRE.transitionSymbol,
    PredRE.symbolOld, PredRE.transitionTagField, PredRE.transitionOldField]

theorem regionValue_zero (S : DifferenceSpec) (G : List (DBM.Edge (specVars S).length)) :
    regionValue S G .zero (zero_mem_specVars S) = 0 := by
  simp [regionValue]

/-- Canonicalization replaces each present scalar coordinate by its region potential and preserves
absence. -/
theorem coordScalar_restrictDifferenceSymbol (S : DifferenceSpec) (a : Value)
    (hsafe : SafeDifference S) (q : DiffCoord) (hq : .coord q ∈ specVars S) :
    coordScalar (restrictDifferenceSymbol S a) q =
      match coordScalar a q with
      | some _ => some (regionValue S (selectedRegion S a) (.coord q) hq)
      | none => none := by
  cases q with
  | mk slot f =>
    cases slot with
    | old =>
        have hf := oldField_mem_differenceOldFields (S := S) (f := f) hq
        simp only [coordScalar, DiffCoord.slot, DiffCoord.field]
        rw [symbolOld_restrictDifferenceSymbol, canonicalOld]
        rw [valueScalar_ofChoices (g := canonicalOldChoice S a) (fs := differenceOldFields S)
          (List.nodup_dedup _) hf]
        simp [canonicalOldChoice, oldQ, hq]
        cases hs : (PredRE.symbolOld a).scalar f <;> simp [hs]
    | new =>
        have hf := newField_mem_differenceNewFields (S := S) (f := f) hq
        have htag : f ≠ PredRE.transitionTagField := fun h => hsafe.1 (h ▸ hf)
        have hold : f ≠ PredRE.transitionOldField := fun h => hsafe.2 (h ▸ hf)
        simp only [coordScalar, DiffCoord.slot, DiffCoord.field]
        rw [restrictDifferenceSymbol, canonicalNew]
        unfold choiceRecord
        rw [transitionSymbol_scalar htag hold]
        change (choiceRecord (differenceNewFields S) (canonicalNewChoice S a)).scalar f = _
        rw [valueScalar_ofChoices (g := canonicalNewChoice S a) (fs := differenceNewFields S)
          (List.nodup_dedup _) hf]
        simp only [canonicalNewChoice]
        cases hfld : a.field f with
        | none => simp [Value.scalar, hfld]
        | some v =>
          cases v with
          | int x => simp [newQ, hq, Value.scalar, hfld]
          | dig d => simp [newQ, hq, Value.scalar, hfld]
          | sym k => simp [newQ, hq, Value.scalar, hfld]
          | record fs => simp [newQ, hq, Value.scalar, hfld]

/-- The same statement for a DBM variable, including the fixed zero vertex. -/
theorem varScalar_restrictDifferenceSymbol (S : DifferenceSpec) (a : Value)
    (hsafe : SafeDifference S) (v : DiffVar) (hv : v ∈ specVars S) :
    varScalar (restrictDifferenceSymbol S a) v =
      match varScalar a v with
      | some _ => some (regionValue S (selectedRegion S a) v hv)
      | none => none := by
  cases v with
  | zero => simp [varScalar, regionValue_zero]
  | coord q => exact coordScalar_restrictDifferenceSymbol S a hsafe q hv

/-- The selected region contains the orientation chosen for every present cut. -/
theorem chosenEdge_mem_regionOf (S : DifferenceSpec) (a : Value) :
    ∀ (cs : List DiffCut) (hsub : ∀ c ∈ cs, c ∈ S.cuts) (c : DiffCut) (hc : c ∈ cs),
      (varScalar a c.lhs).isSome = true → (varScalar a c.rhs).isSome = true →
      (if cutTruth a c then positiveEdge S c (hsub c hc)
       else negativeEdge S c (hsub c hc)) ∈ regionOf S a cs hsub := by
  intro cs
  induction cs with
  | nil => intro _ c hc; simp at hc
  | cons d ds ih =>
      intro hsub c hc hl hr
      rcases List.mem_cons.mp hc with rfl | hc
      · cases hdl : varScalar a c.lhs with
        | none => rw [hdl] at hl; contradiction
        | some xl =>
          cases hdr : varScalar a c.rhs with
          | none => rw [hdr] at hr; contradiction
          | some xr =>
              simp only [regionOf, hdl, hdr]
              split <;> simp
      · let ht : ∀ e ∈ ds, e ∈ S.cuts :=
          fun e he => hsub e (List.mem_cons_of_mem _ he)
        have hi := ih ht c hc hl hr
        simp only [regionOf]
        cases hdl : varScalar a d.lhs <;> cases hdr : varScalar a d.rhs
        all_goals simp only [hdl, hdr]
        · exact hi
        · exact hi
        · exact hi
        · split <;> exact List.mem_cons_of_mem _ hi

/-- Shortest-path normalization realizes the same Boolean orientation of every present cut. -/
theorem regionValue_cutTruth (S : DifferenceSpec) (a : Value) (c : DiffCut) (hc : c ∈ S.cuts)
    {xl xr : Int} (hl : varScalar a c.lhs = some xl) (hr : varScalar a c.rhs = some xr) :
    decide (regionValue S (selectedRegion S a) c.lhs (cut_lhs_mem_specVars hc) -
      regionValue S (selectedRegion S a) c.rhs (cut_rhs_mem_specVars hc) ≤ c.bound) =
      cutTruth a c := by
  have hsat := selectedRegion_regionValue_satisfies S a
  have hmem := chosenEdge_mem_regionOf S a S.cuts (fun _ h => h) c hc
    (by simp [hl]) (by simp [hr])
  by_cases ht : cutTruth a c = true
  · rw [if_pos ht] at hmem
    have he := hsat _ hmem
    simp only [positiveEdge] at he
    simp only [decide_eq_true_eq, ht]
    exact he
  · rw [if_neg (by simpa using ht)] at hmem
    have he := hsat _ hmem
    simp only [negativeEdge] at he
    change regionValue S (selectedRegion S a) c.rhs (cut_rhs_mem_specVars hc) -
      regionValue S (selectedRegion S a) c.lhs (cut_lhs_mem_specVars hc) ≤
        -c.bound - 1 at he
    have hn : ¬ (regionValue S (selectedRegion S a) c.lhs (cut_lhs_mem_specVars hc) -
        regionValue S (selectedRegion S a) c.rhs (cut_rhs_mem_specVars hc) ≤ c.bound) := by omega
    rw [show cutTruth a c = false by cases h : cutTruth a c <;> simp_all]
    simpa [hn]

/-- Full-value equality observations carry their two scalar equality cuts. This invariant is
created by `predDifference?` and preserved by specification append. -/
def ValueEqClosed (S : DifferenceSpec) : Prop :=
  ∀ f g, (f, g) ∈ S.valueEqs →
    newQ f ∈ S.coords ∧ newQ g ∈ S.coords ∧
      diffLe (newQ f) (newQ g) 0 ∈ S.cuts ∧ diffLe (newQ g) (newQ f) 0 ∈ S.cuts

theorem observedLabel_lt {S : DifferenceSpec} {a v : Value} {f : FieldName}
    (hf : f ∈ differenceNewFields S) (hv : a.field f = some v) :
    observedLabel S a v < (differenceNewFields S).length := by
  unfold observedLabel
  apply List.findIdx_lt_length_of_exists
  refine ⟨f, hf, ?_⟩
  simp [hv, Value.beq_iff]

/-- Equality-class numbering is injective on values actually present at mentioned fields. -/
theorem observedLabel_eq_iff {S : DifferenceSpec} {a v w : Value} {f g : FieldName}
    (hf : f ∈ differenceNewFields S) (hg : g ∈ differenceNewFields S)
    (hv : a.field f = some v) (hw : a.field g = some w) :
    observedLabel S a v = observedLabel S a w ↔ v = w := by
  constructor
  · intro heq
    have hlv := observedLabel_lt hf hv
    have hlw := observedLabel_lt hg hw
    unfold observedLabel at hlv hlw heq
    let pv : FieldName → Bool := fun k =>
      match a.field k with | some z => Value.beq z v | none => false
    let pw : FieldName → Bool := fun k =>
      match a.field k with | some z => Value.beq z w | none => false
    have hvAt := @List.findIdx_getElem FieldName pv (differenceNewFields S) hlv
    have hwAt := @List.findIdx_getElem FieldName pw (differenceNewFields S) hlw
    have heq' : List.findIdx pv (differenceNewFields S) =
        List.findIdx pw (differenceNewFields S) := by
      simpa [pv, pw] using heq
    have hwAt' : pw (differenceNewFields S)[List.findIdx pv (differenceNewFields S)] = true := by
      simpa only [heq'] using hwAt
    cases hk : a.field (differenceNewFields S)[List.findIdx pv (differenceNewFields S)] with
    | none => simp [pv, hk] at hvAt
    | some z =>
        have hzv : z = v := (Value.beq_iff z v).mp (by simpa [pv, hk] using hvAt)
        have hzw : z = w := (Value.beq_iff z w).mp (by simpa [pw, hk] using hwAt')
        exact hzv.symm.trans hzw
  · rintro rfl
    rfl

theorem canonicalOldChoice_mem (S : DifferenceSpec) (a : Value) (f : FieldName) :
    canonicalOldChoice S a f ∈ oldValueChoices S := by
  unfold canonicalOldChoice
  split
  · next hq =>
      cases hs : (PredRE.symbolOld a).scalar f with
      | none => simp [oldValueChoices]
      | some x =>
          simp only [oldValueChoices, List.mem_cons, Option.some.injEq]
          apply Or.inr
          apply List.mem_map.mpr
          exact ⟨_, regionValue_mem S (selectedRegion_mem S a) _ hq, rfl⟩
  · simp [oldValueChoices]

theorem canonicalNewChoice_mem (S : DifferenceSpec) (a : Value) {f : FieldName}
    (hf : f ∈ differenceNewFields S) : canonicalNewChoice S a f ∈ newValueChoices S := by
  cases hv : a.field f with
  | none => simp [canonicalNewChoice, hv, newValueChoices]
  | some v =>
      have hlabel := observedLabel_lt hf hv
      have hsym : some (.sym (observedLabel S a v)) ∈ newValueChoices S := by
        unfold newValueChoices
        apply List.mem_cons.mpr; apply Or.inr
        apply List.mem_append.mpr; apply Or.inr
        exact List.mem_map.mpr ⟨_, List.mem_range.mpr hlabel, rfl⟩
      simp only [canonicalNewChoice, hv]
      by_cases hq : .coord (newQ f) ∈ specVars S
      · rw [dif_pos hq]
        cases v with
        | int x =>
            unfold newValueChoices
            apply List.mem_cons.mpr; apply Or.inr
            apply List.mem_append.mpr; apply Or.inl
            exact List.mem_map.mpr
              ⟨_, regionValue_mem S (selectedRegion_mem S a) _ hq, rfl⟩
        | dig d => exact hsym
        | sym k => exact hsym
        | record fs => exact hsym
      · rw [dif_neg hq]
        exact hsym

/-- A pointwise-selected record belongs to the corresponding finite `sections` product. -/
theorem choiceRecord_mem_choiceRecords (fs : List FieldName) (opts : List (Option Value))
    (g : FieldName → Option Value) (hg : ∀ f ∈ fs, g f ∈ opts) :
    choiceRecord fs g ∈ choiceRecords fs opts := by
  apply List.mem_map.mpr
  refine ⟨fs.map (fun f => (f, g f)), ?_, ?_⟩
  · apply List.mem_sections.mpr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro f hf
    exact List.mem_map.mpr ⟨g f, hg f hf, rfl⟩
  · simp [choiceRecord, Function.comp_def]

theorem restrictDifferenceSymbol_mem_differenceCands (S : DifferenceSpec) (a : Value) :
    restrictDifferenceSymbol S a ∈ differenceCands S := by
  apply List.mem_flatMap.mpr
  refine ⟨canonicalOld S a, ?_, ?_⟩
  · exact choiceRecord_mem_choiceRecords _ _ _ (fun f _ => canonicalOldChoice_mem S a f)
  · apply List.mem_map.mpr
    refine ⟨canonicalNew S a, ?_, rfl⟩
    exact choiceRecord_mem_choiceRecords _ _ _ (fun _ hf => canonicalNewChoice_mem S a hf)

theorem restrictDifferenceSymbol_field (S : DifferenceSpec) (a : Value)
    (hsafe : SafeDifference S) {f : FieldName} (hf : f ∈ differenceNewFields S) :
    (restrictDifferenceSymbol S a).field f = canonicalNewChoice S a f := by
  have htag : f ≠ PredRE.transitionTagField := fun h => hsafe.1 (h ▸ hf)
  have hold : f ≠ PredRE.transitionOldField := fun h => hsafe.2 (h ▸ hf)
  rw [restrictDifferenceSymbol, canonicalNew]
  unfold choiceRecord
  rw [transitionSymbol_field htag hold]
  change (choiceRecord (differenceNewFields S) (canonicalNewChoice S a)).field f = _
  exact valueField_ofChoices (List.nodup_dedup _) hf

/-- The two DBM equality cuts make scalar region representatives equal exactly when the original
scalars were equal. -/
theorem regionValue_new_eq_iff (S : DifferenceSpec) (a : Value) (hclosed : ValueEqClosed S)
    {f g : FieldName} (hp : (f, g) ∈ S.valueEqs) {x y : Int}
    (hf : a.field f = some (.int x)) (hg : a.field g = some (.int y)) :
    regionValue S (selectedRegion S a) (.coord (newQ f))
        (coord_mem_specVars (hclosed f g hp).1) =
      regionValue S (selectedRegion S a) (.coord (newQ g))
        (coord_mem_specVars (hclosed f g hp).2.1) ↔ x = y := by
  have hfscalar : a.scalar f = some x := by simp [Value.scalar, hf]
  have hgscalar : a.scalar g = some y := by simp [Value.scalar, hg]
  have hqf := coord_mem_specVars (hclosed f g hp).1
  have hqg := coord_mem_specVars (hclosed f g hp).2.1
  have hfg := regionValue_cutTruth S a (diffLe (newQ f) (newQ g) 0)
    (hclosed f g hp).2.2.1
    (by simpa [diffLe, qv, varScalar, coordScalar, newQ] using hfscalar)
    (by simpa [diffLe, qv, varScalar, coordScalar, newQ] using hgscalar)
  have hgf := regionValue_cutTruth S a (diffLe (newQ g) (newQ f) 0)
    (hclosed f g hp).2.2.2
    (by simpa [diffLe, qv, varScalar, coordScalar, newQ] using hgscalar)
    (by simpa [diffLe, qv, varScalar, coordScalar, newQ] using hfscalar)
  have hfg' :
      (regionValue S (selectedRegion S a) (.coord (newQ f)) hqf -
          regionValue S (selectedRegion S a) (.coord (newQ g)) hqg ≤ 0) ↔ x - y ≤ 0 := by
    simpa [cutTruth, diffLe, qv, varScalar, coordScalar, newQ, hfscalar, hgscalar,
      decide_eq_decide] using hfg
  have hgf' :
      (regionValue S (selectedRegion S a) (.coord (newQ g)) hqg -
          regionValue S (selectedRegion S a) (.coord (newQ f)) hqf ≤ 0) ↔ y - x ≤ 0 := by
    simpa [cutTruth, diffLe, qv, varScalar, coordScalar, newQ, hfscalar, hgscalar,
      decide_eq_decide] using hgf
  constructor
  · intro heq
    have hxy := hfg'.mp (by omega)
    have hyx := hgf'.mp (by omega)
    omega
  · intro heq
    have hfgv := hfg'.mpr (by omega)
    have hgfv := hgf'.mpr (by omega)
    omega

/-- The canonical NEW choices preserve genuine option/full-`Value` equality at every declared
equality pair. -/
theorem canonicalNewChoice_eq_iff (S : DifferenceSpec) (a : Value) (hclosed : ValueEqClosed S)
    {f g : FieldName} (hp : (f, g) ∈ S.valueEqs) :
    canonicalNewChoice S a f = canonicalNewChoice S a g ↔ a.field f = a.field g := by
  have hcf := (hclosed f g hp).1
  have hcg := (hclosed f g hp).2.1
  have hqf := coord_mem_specVars hcf
  have hqg := coord_mem_specVars hcg
  have hmf := valueEq_left_mem_differenceNewFields hp
  have hmg := valueEq_right_mem_differenceNewFields hp
  cases hf : a.field f with
  | none =>
      cases hg : a.field g with
      | none => simp [canonicalNewChoice, hf, hg]
      | some w => cases w <;> simp [canonicalNewChoice, hf, hg, hqg]
  | some v =>
      cases hg : a.field g with
      | none => cases v <;> simp [canonicalNewChoice, hf, hg, hqf]
      | some w =>
          have hlabel := observedLabel_eq_iff hmf hmg hf hg
          cases v with
          | int x =>
              cases w with
              | int y =>
                  simpa [canonicalNewChoice, hf, hg, hqf, hqg] using
                    regionValue_new_eq_iff S a hclosed hp hf hg
              | dig d => simp [canonicalNewChoice, hf, hg, hqf, hqg]
              | sym k => simp [canonicalNewChoice, hf, hg, hqf, hqg]
              | record fs => simp [canonicalNewChoice, hf, hg, hqf, hqg]
          | dig d =>
              cases w <;> simp [canonicalNewChoice, hf, hg, hqf, hqg] at hlabel ⊢ <;>
                exact hlabel
          | sym k =>
              cases w <;> simp [canonicalNewChoice, hf, hg, hqf, hqg] at hlabel ⊢ <;>
                exact hlabel
          | record fs =>
              cases w <;> simp [canonicalNewChoice, hf, hg, hqf, hqg] at hlabel ⊢ <;>
                exact hlabel

/-- Canonical NEW choices preserve field presence. -/
theorem canonicalNewChoice_none_iff (S : DifferenceSpec) (a : Value) (f : FieldName) :
    canonicalNewChoice S a f = none ↔ a.field f = none := by
  cases hf : a.field f with
  | none => simp [canonicalNewChoice, hf]
  | some v =>
      cases v <;> simp [canonicalNewChoice, hf] <;> split <;> simp

/-- The concrete representative has exactly the full difference signature of the source symbol. -/
theorem restrictDifferenceSymbol_same (S : DifferenceSpec) (a : Value)
    (hsafe : SafeDifference S) (hclosed : ValueEqClosed S) :
    SameDifference S (restrictDifferenceSymbol S a) a := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have hread := coordScalar_restrictDifferenceSymbol S a hsafe q (coord_mem_specVars hq)
    rw [hread]
    cases coordScalar a q <;> rfl
  · intro c hc
    have hl := varScalar_restrictDifferenceSymbol S a hsafe c.lhs (cut_lhs_mem_specVars hc)
    have hr := varScalar_restrictDifferenceSymbol S a hsafe c.rhs (cut_rhs_mem_specVars hc)
    cases hla : varScalar a c.lhs with
    | none => simp [cutTruth, hl, hla]
    | some xl =>
      cases hra : varScalar a c.rhs with
      | none => simp [cutTruth, hl, hr, hla, hra]
      | some xr =>
          simp only [hla] at hl
          simp only [hra] at hr
          simp only [cutTruth, hl, hr, hla, hra]
          simpa [cutTruth, hla, hra] using regionValue_cutTruth S a c hc hla hra
  · rintro ⟨f, g⟩ hp
    have hmf := valueEq_left_mem_differenceNewFields hp
    have hmg := valueEq_right_mem_differenceNewFields hp
    have hff := restrictDifferenceSymbol_field S a hsafe hmf
    have hfg := restrictDifferenceSymbol_field S a hsafe hmg
    simp only [valueEqTruth, leaf, Pred.eval, hff, hfg]
    cases hf : a.field f with
    | none =>
        have hnone := (canonicalNewChoice_none_iff S a f).mpr hf
        simp [hnone, hf]
    | some v =>
      cases hg : a.field g with
      | none =>
          have hnone := (canonicalNewChoice_none_iff S a g).mpr hg
          simp [hnone, hg]
      | some w =>
          have hfn : canonicalNewChoice S a f ≠ none := by
            intro h
            have hn := (canonicalNewChoice_none_iff S a f).mp h
            rw [hn] at hf
            contradiction
          have hgn : canonicalNewChoice S a g ≠ none := by
            intro h
            have hn := (canonicalNewChoice_none_iff S a g).mp h
            rw [hn] at hg
            contradiction
          cases hcf : canonicalNewChoice S a f with
          | none => exact absurd hcf hfn
          | some u =>
            cases hcg : canonicalNewChoice S a g with
            | none => exact absurd hcg hgn
            | some z =>
                simp only [hcf, hcg]
                apply bool_eq_of_iff
                simp only [Value.beq_iff]
                have heq := canonicalNewChoice_eq_iff S a hclosed hp
                simpa [hcf, hcg, hf, hg] using heq

/-! ## §6 The `MintermCover` plug-in and existing decision assemblies -/

@[simp] theorem DifferenceSpec.append_coords (A B : DifferenceSpec) :
    (A ++ B).coords = A.coords ++ B.coords := rfl

@[simp] theorem DifferenceSpec.append_cuts (A B : DifferenceSpec) :
    (A ++ B).cuts = A.cuts ++ B.cuts := rfl

@[simp] theorem DifferenceSpec.append_valueEqs (A B : DifferenceSpec) :
    (A ++ B).valueEqs = A.valueEqs ++ B.valueEqs := rfl

theorem DifferenceSpec.append_assoc (A B C : DifferenceSpec) :
    (A ++ B) ++ C = A ++ (B ++ C) := by
  rcases A with ⟨ac, ak, ae⟩
  rcases B with ⟨bc, bk, be⟩
  rcases C with ⟨cc, ck, ce⟩
  change DifferenceSpec.mk ((ac ++ bc) ++ cc) ((ak ++ bk) ++ ck) ((ae ++ be) ++ ce) =
    DifferenceSpec.mk (ac ++ (bc ++ cc)) (ak ++ (bk ++ ck)) (ae ++ (be ++ ce))
  rw [List.append_assoc, List.append_assoc, List.append_assoc]

theorem mem_specVars_append {A B : DifferenceSpec} {v : DiffVar} :
    v ∈ specVars (A ++ B) ↔ v ∈ specVars A ∨ v ∈ specVars B := by
  simp [specVars, List.flatMap_append]
  aesop

theorem mem_differenceNewFields_append {A B : DifferenceSpec} {f : FieldName} :
    f ∈ differenceNewFields (A ++ B) ↔
      f ∈ differenceNewFields A ∨ f ∈ differenceNewFields B := by
  simp only [differenceNewFields, List.mem_dedup, List.mem_append,
    List.mem_filterMap, List.mem_flatMap, mem_specVars_append]
  constructor
  · rintro (⟨v, hv, hmap⟩ | ⟨p, hp, hpair⟩)
    · rcases hv with hv | hv
      · exact Or.inl (Or.inl ⟨v, hv, hmap⟩)
      · exact Or.inr (Or.inl ⟨v, hv, hmap⟩)
    · simp only [DifferenceSpec.append_valueEqs, List.mem_append] at hp
      rcases hp with hp | hp
      · exact Or.inl (Or.inr ⟨p, hp, hpair⟩)
      · exact Or.inr (Or.inr ⟨p, hp, hpair⟩)
  · rintro (hf | hf)
    · rcases hf with ⟨v, hv, hmap⟩ | ⟨p, hp, hpair⟩
      · exact Or.inl ⟨v, Or.inl hv, hmap⟩
      · exact Or.inr ⟨p, by simp [hp], hpair⟩
    · rcases hf with ⟨v, hv, hmap⟩ | ⟨p, hp, hpair⟩
      · exact Or.inl ⟨v, Or.inr hv, hmap⟩
      · exact Or.inr ⟨p, by simp [hp], hpair⟩

theorem SafeDifference.append {A B : DifferenceSpec} (hA : SafeDifference A)
    (hB : SafeDifference B) : SafeDifference (A ++ B) := by
  constructor
  · intro h
    rcases mem_differenceNewFields_append.mp h with h | h
    · exact hA.1 h
    · exact hB.1 h
  · intro h
    rcases mem_differenceNewFields_append.mp h with h | h
    · exact hA.2 h
    · exact hB.2 h

theorem ValueEqClosed.empty : ValueEqClosed DifferenceSpec.empty := by
  intro f g hp
  simp [DifferenceSpec.empty] at hp

theorem ValueEqClosed.append {A B : DifferenceSpec} (hA : ValueEqClosed A)
    (hB : ValueEqClosed B) : ValueEqClosed (A ++ B) := by
  intro f g hp
  change (f, g) ∈ A.valueEqs ++ B.valueEqs at hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨hf, hg, hfg, hgf⟩ := hA f g hp
    exact ⟨List.mem_append.mpr (Or.inl hf), List.mem_append.mpr (Or.inl hg),
      List.mem_append.mpr (Or.inl hfg), List.mem_append.mpr (Or.inl hgf)⟩
  · obtain ⟨hf, hg, hfg, hgf⟩ := hB f g hp
    exact ⟨List.mem_append.mpr (Or.inr hf), List.mem_append.mpr (Or.inr hg),
      List.mem_append.mpr (Or.inr hfg), List.mem_append.mpr (Or.inr hgf)⟩

/-- Simple atoms carry no full-value equality probes. -/
theorem simpleDifference?_closed {c : SimpleConstraint} {S : DifferenceSpec}
    (h : simpleDifference? c = some S) : ValueEqClosed S := by
  intro f g hp
  induction c generalizing S <;> simp_all [simpleDifference?]
  all_goals subst S; simp at hp

/-- State-constraint extraction carries no full-value equality probes. -/
theorem constraintDifference?_closed {c : StateConstraint} {S : DifferenceSpec}
    (h : constraintDifference? c = some S) : ValueEqClosed S := by
  cases c with
  | simple sc => exact simpleDifference?_closed h
  | fieldLeField f g => simp [constraintDifference?] at h; subst S; simp [ValueEqClosed]
  | fieldDeltaInRange f lo hi => simp [constraintDifference?] at h; subst S; simp [ValueEqClosed]
  | sumEquals _ _ => simp [constraintDifference?] at h
  | sumEqualsAcross _ _ => simp [constraintDifference?] at h
  | allowedTransitions _ _ => simp [constraintDifference?] at h
  | anyOf _ => simp [constraintDifference?] at h
  | boundDelta _ _ _ _ => simp [constraintDifference?] at h
  | clearanceGe _ _ _ => simp [constraintDifference?] at h
  | affineLe _ _ => simp [constraintDifference?] at h
  | affineEq _ _ => simp [constraintDifference?] at h
  | reachable _ _ _ => simp [constraintDifference?] at h
  | affineDeltaLe _ _ => simp [constraintDifference?] at h
  | affineDeltaLeField _ _ => simp [constraintDifference?] at h
  | observedFieldEquals _ _ _ => simp [constraintDifference?] at h
  | anyOfBound _ => simp [constraintDifference?] at h
  | countFieldsEq _ _ _ => simp [constraintDifference?] at h

/-- Extraction always creates the scalar cuts required by its full-value equality observations. -/
theorem predDifference?_closed : ∀ {p : Pred} {S : DifferenceSpec},
    predDifference? p = some S → ValueEqClosed S
  | .atom c, S, h => constraintDifference?_closed h
  | .tt, S, h => by simp [predDifference?] at h; subst S; exact ValueEqClosed.empty
  | .ff, S, h => by simp [predDifference?] at h; subst S; exact ValueEqClosed.empty
  | .and l r, S, h => by
      simp only [predDifference?] at h
      cases hl : predDifference? l with
      | none => rw [hl] at h; simp at h
      | some A =>
        cases hr : predDifference? r with
        | none => rw [hl, hr] at h; simp at h
        | some B =>
          rw [hl, hr, Option.some.injEq] at h
          subst S
          exact ValueEqClosed.append (predDifference?_closed hl) (predDifference?_closed hr)
  | .or l r, S, h => by
      simp only [predDifference?] at h
      cases hl : predDifference? l with
      | none => rw [hl] at h; simp at h
      | some A =>
        cases hr : predDifference? r with
        | none => rw [hl, hr] at h; simp at h
        | some B =>
          rw [hl, hr, Option.some.injEq] at h
          subst S
          exact ValueEqClosed.append (predDifference?_closed hl) (predDifference?_closed hr)
  | .not p, S, h => by
      apply predDifference?_closed (p := p)
      exact h
  | .fieldEqField f g, S, h => by
      simp only [predDifference?, Option.some.injEq] at h
      subst S
      simp [ValueEqClosed, eqCuts, diffLe, newQ]
  | .allOf _, _, h => by simp [predDifference?] at h
  | .anyOf _, _, h => by simp [predDifference?] at h
  | .symEq _ _, _, h => by simp [predDifference?] at h
  | .symMemberOf _ _, _, h => by simp [predDifference?] at h
  | .digEq _ _, _, h => by simp [predDifference?] at h
  | .digFieldEq _ _, _, h => by simp [predDifference?] at h
  | .symUnchanged _, _, h => by simp [predDifference?] at h
  | .symChanged _, _, h => by simp [predDifference?] at h
  | .digUnchanged _, _, h => by simp [predDifference?] at h
  | .digChanged _, _, h => by simp [predDifference?] at h
termination_by p S h => predMeasure p
decreasing_by all_goals simp [predMeasure] <;> omega

/-- Fold difference extraction over a leaf list. -/
def differenceLeaves? : List Pred → Option DifferenceSpec
  | [] => some .empty
  | p :: ps =>
      match predDifference? p, differenceLeaves? ps with
      | some A, some B => some (A ++ B)
      | _, _ => none

theorem differenceLeaves?_spec : ∀ {l : List Pred} {S : DifferenceSpec},
    differenceLeaves? l = some S →
      ∀ p ∈ l, ∃ A, predDifference? p = some A ∧ DifferenceSpec.Subset A S := by
  intro l
  induction l with
  | nil => intro S _ p hp; simp at hp
  | cons p ps ih =>
      intro S h q hq
      simp only [differenceLeaves?] at h
      cases hp : predDifference? p with
      | none => rw [hp] at h; simp at h
      | some A =>
        cases hps : differenceLeaves? ps with
        | none => rw [hp, hps] at h; simp at h
        | some B =>
          rw [hp, hps, Option.some.injEq] at h
          subst S
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨A, hp, DifferenceSpec.subset_append_left A B⟩
          · obtain ⟨C, hC, hsub⟩ := ih hps q hq
            exact ⟨C, hC, ⟨fun x hx => List.mem_append.mpr (Or.inr (hsub.1 hx)),
              fun x hx => List.mem_append.mpr (Or.inr (hsub.2.1 hx)),
              fun x hx => List.mem_append.mpr (Or.inr (hsub.2.2 hx))⟩⟩

theorem differenceLeaves?_closed {l : List Pred} {S : DifferenceSpec}
    (h : differenceLeaves? l = some S) : ValueEqClosed S := by
  induction l generalizing S with
  | nil => simp [differenceLeaves?] at h; subst S; exact ValueEqClosed.empty
  | cons p ps ih =>
      simp only [differenceLeaves?] at h
      cases hp : predDifference? p with
      | none => rw [hp] at h; simp at h
      | some A =>
        cases hps : differenceLeaves? ps with
        | none => rw [hp, hps] at h; simp at h
        | some B =>
          rw [hp, hps, Option.some.injEq] at h
          subst S
          exact ValueEqClosed.append (predDifference?_closed hp) (ih hps)

/-- **The DBM minterm cover.** Every symbol is represented by its shortest-path region witness and
finite equality-class labels, hence every leaf in `L` has the same truth value. -/
def coverOfDifference (S : DifferenceSpec) (L : List Pred)
    (hL : ∀ p ∈ L, ∃ A, predDifference? p = some A ∧ DifferenceSpec.Subset A S)
    (hsafe : SafeDifference S) (hclosed : ValueEqClosed S) : MintermCover L where
  cands := differenceCands S
  covers a := by
    refine ⟨restrictDifferenceSymbol S a, restrictDifferenceSymbol_mem_differenceCands S a, ?_⟩
    apply List.map_inj_left.mpr
    intro p hp
    obtain ⟨A, hA, hsub⟩ := hL p hp
    exact predDifference?_reads hA ((restrictDifferenceSymbol_same S a hsafe hclosed).mono hsub)

/-- Extraction commutes with list append, up to specification append. -/
theorem differenceLeaves?_append {xs ys : List Pred} {A B : DifferenceSpec}
    (hA : differenceLeaves? xs = some A) (hB : differenceLeaves? ys = some B) :
    differenceLeaves? (xs ++ ys) = some (A ++ B) := by
  induction xs generalizing A with
  | nil =>
      simp [differenceLeaves?] at hA
      subst A
      have hE : DifferenceSpec.empty ++ B = B := by cases B; rfl
      have hE' : ({} : DifferenceSpec) ++ B = B := by cases B; rfl
      simpa [differenceLeaves?, DifferenceSpec.empty, DifferenceSpec.append, hE, hE'] using hB
  | cons p ps ih =>
      simp only [differenceLeaves?] at hA
      cases hp : predDifference? p with
      | none => rw [hp] at hA; simp at hA
      | some P =>
        cases hps : differenceLeaves? ps with
        | none => rw [hp, hps] at hA; simp at hA
        | some Q =>
          rw [hp, hps, Option.some.injEq] at hA
          subst A
          simp only [List.cons_append, differenceLeaves?, hp, ih hps]
          rw [DifferenceSpec.append_assoc]

/-- Executable reserved-name check. -/
instance (S : DifferenceSpec) : Decidable (SafeDifference S) := by
  unfold SafeDifference
  infer_instance

def safeDifferenceB (S : DifferenceSpec) : Bool := decide (SafeDifference S)

/-- The computable DBM fragment check for a whole regex. -/
def differenceRE (R : PredRE) : Bool :=
  match differenceLeaves? (leavesOf R) with
  | some S => safeDifferenceB S
  | none => false

/-- Accepted leaves are `predBEq`-reflexive, so ACI rigidity is derivable. -/
theorem predBEq_refl_of_difference : ∀ {p : Pred} {S : DifferenceSpec},
    predDifference? p = some S → predBEq p p = true
  | .atom c, _, _ => by simp [predBEq]
  | .tt, _, _ => rfl
  | .ff, _, _ => rfl
  | .fieldEqField f g, _, _ => by simp [predBEq]
  | .and l r, S, h => by
      simp only [predDifference?] at h
      cases hl : predDifference? l with
      | none => rw [hl] at h; simp at h
      | some A =>
        cases hr : predDifference? r with
        | none => rw [hl, hr] at h; simp at h
        | some B =>
          simp only [predBEq, Bool.and_eq_true]
          exact ⟨predBEq_refl_of_difference hl, predBEq_refl_of_difference hr⟩
  | .or l r, S, h => by
      simp only [predDifference?] at h
      cases hl : predDifference? l with
      | none => rw [hl] at h; simp at h
      | some A =>
        cases hr : predDifference? r with
        | none => rw [hl, hr] at h; simp at h
        | some B =>
          simp only [predBEq, Bool.and_eq_true]
          exact ⟨predBEq_refl_of_difference hl, predBEq_refl_of_difference hr⟩
  | .not p, S, h => by
      simpa [predBEq] using predBEq_refl_of_difference (p := p) h
  | .allOf _, _, h => by simp [predDifference?] at h
  | .anyOf _, _, h => by simp [predDifference?] at h
  | .symEq _ _, _, h => by simp [predDifference?] at h
  | .symMemberOf _ _, _, h => by simp [predDifference?] at h
  | .digEq _ _, _, h => by simp [predDifference?] at h
  | .digFieldEq _ _, _, h => by simp [predDifference?] at h
  | .symUnchanged _, _, h => by simp [predDifference?] at h
  | .symChanged _, _, h => by simp [predDifference?] at h
  | .digUnchanged _, _, h => by simp [predDifference?] at h
  | .digChanged _, _, h => by simp [predDifference?] at h
termination_by p S h => predMeasure p
decreasing_by all_goals simp [predMeasure] <;> omega

theorem rigidRE_of_differenceLeaves {R : PredRE} {S : DifferenceSpec}
    (h : differenceLeaves? (leavesOf R) = some S) : RigidFull R :=
  rigidRE_of_leaves fun p hp => by
    obtain ⟨A, hA, -⟩ := differenceLeaves?_spec h p hp
    exact predBEq_refl_of_difference hA

/-- The fragment is closed under symmetric difference. -/
theorem differenceRE_symDiff {R T : PredRE} (hR : differenceRE R = true)
    (hT : differenceRE T = true) : differenceRE (symDiff R T) = true := by
  cases hr : differenceLeaves? (leavesOf R) with
  | none => simp [differenceRE, hr] at hR
  | some A =>
    cases ht : differenceLeaves? (leavesOf T) with
    | none => simp [differenceRE, ht] at hT
    | some B =>
      have hsA : SafeDifference A := by
        simpa [differenceRE, hr, safeDifferenceB] using hR
      have hsB : SafeDifference B := by
        simpa [differenceRE, ht, safeDifferenceB] using hT
      have hab := differenceLeaves?_append hr ht
      have habab := differenceLeaves?_append hab hab
      simp only [differenceRE, symDiff, leavesOf]
      rw [habab]
      simp only [safeDifferenceB, decide_eq_true_eq]
      exact (hsA.append hsB).append (hsA.append hsB)

/-- Existing generic assembly, instantiated with the DBM cover. -/
def predRE_emptiness_decidable_difference (fuel : Nat) {R : PredRE}
    (h : differenceRE R = true) : Decidable (∃ w, derives w R = true) :=
  match hS : differenceLeaves? (leavesOf R) with
  | some S =>
      predRE_emptiness_decidable_cover
        (coverOfDifference S (leavesOf R) (differenceLeaves?_spec hS)
          (by simpa [differenceRE, hS, safeDifferenceB] using h)
          (differenceLeaves?_closed hS))
        fuel (symbolicOver_leavesOf R) (rigidRE_of_differenceLeaves hS)
  | none => absurd h (by simp [differenceRE, hS])

/-- Existing equivalence assembly via symmetric-difference emptiness. -/
def predRE_equivalence_decidable_difference (fuel : Nat) {R T : PredRE}
    (hR : differenceRE R = true) (hT : differenceRE T = true) :
    Decidable (∀ w, derives w R = derives w T) :=
  match hS : differenceLeaves? (leavesOf (symDiff R T)) with
  | some S =>
      predRE_equivalence_decidable_cover
        (coverOfDifference S (leavesOf (symDiff R T)) (differenceLeaves?_spec hS)
          (by simpa [differenceRE, hS, safeDifferenceB] using differenceRE_symDiff hR hT)
          (differenceLeaves?_closed hS))
        fuel (symbolicOver_leavesOf _) (rigidRE_of_differenceLeaves hS)
  | none => absurd (differenceRE_symDiff hR hT) (by simp [differenceRE, hS])

/-- Candidate list used by the cheap direct-computation demonstrations below. -/
def differenceFixCands (R : PredRE) : List Value :=
  match differenceLeaves? (leavesOf R) with
  | some S => differenceCands S
  | none => []

/-! ## §7 Cheap Bool-level demonstrations

These reduce `differenceRE`, `rigidRE`, and `emptyFix` directly. They never reduce a transported
`Decidable` instance. The example-specific alphabets below enumerate their tiny inhabited truth
signatures directly, avoiding thousands of duplicate worklist successors from the general product. -/

private def monotonicAmount : PredRE :=
  .sym (.atom (.simple (.monotonic "amount")))

private def deltaMinusOne : PredRE :=
  .sym (.atom (.simple (.fieldDelta "amount" (-1))))

private def monotonicContradiction : PredRE :=
  .inter monotonicAmount deltaMinusOne

private def immutableAmount : PredRE :=
  .sym (.atom (.simple (.immutable "amount")))

private def deltaZeroAmount : PredRE :=
  .sym (.atom (.simple (.fieldDelta "amount" 0)))

private def presentImmutable : PredRE := .inter monotonicAmount immutableAmount
private def presentDeltaZero : PredRE := .inter monotonicAmount deltaZeroAmount

private def presentImmutableDeltaDiff : PredRE :=
  symDiff presentImmutable presentDeltaZero

/-- Globally these are deliberately not equivalent: absent OLD is a first-write witness for
`immutable`, while `fieldDelta 0` requires both scalar coordinates. -/
private def immutableDeltaDiff : PredRE := symDiff immutableAmount deltaZeroAmount

private def crossFieldEq : PredRE := .sym (.fieldEqField "left" "right")
private def crossFieldLe : PredRE := .sym (.atom (.fieldLeField "left" "right"))

private def reactiveCatalog : PredRE :=
  .alt (.sym (.atom (.simple (.monotonic "amount")))) <|
  .alt (.sym (.atom (.simple (.strictMono "amount")))) <|
  .alt (.sym (.atom (.simple (.fieldDelta "amount" 3)))) <|
  .alt (.sym (.atom (.simple (.deltaBounded "amount" 4)))) <|
  .alt (.sym (.atom (.simple (.immutable "amount"))))
       (.sym (.atom (.simple (.writeOnce "amount"))))

private def amountStep (old new : Option Int) : Value :=
  PredRE.transitionSymbol
    (.record (old.toList.map (fun x => ("amount", Value.int x))))
    (.record (new.toList.map (fun x => ("amount", Value.int x))))

/-! ### ⚠ THE `#guard`s BELOW USE HAND-AUTHORED ALPHABETS — read this before quoting them.

The candidate lists in this section (`monotonicGuardCands`, `contradictionGuardCands`,
`immutableGuardCands`) are HAND-WRITTEN truth-signature enumerations. They are NOT produced by
`coverOfDifference`, and their cover-ness is NOT machine-proven — it is asserted by the docstrings
and was checked BY HAND (the enumerations are in fact complete: the omitted signatures are
unrealizable). Consequently:

  * The `= some false` (NONEMPTY) guards are SOUND regardless — exhibiting a word only ever needs
    SOME alphabet, and `emptyFix` nonemptiness holds for arbitrary candidate sets.
  * The `= some true` (EMPTY) guards are the direction that NEEDS completeness — too few candidates
    explores too few derivatives and could wrongly report EMPTY. Those two guards are therefore
    ILLUSTRATIVE Bool evaluations, NOT certified verdicts.

⚠ AND: the CERTIFIED cover (`coverOfDifference`) is never EXECUTED anywhere. `allRegions` enumerates
`3^|cuts|` DBM regions, which is not runnable at the sizes these examples need — hence the bespoke
alphabets here. So this module PROVES a decision procedure and DEMONSTRATES the algorithm on
hand-picked alphabets; it does not exhibit the proven path running end to end. Do not lift
"decides X" from this file into a summary without that distinction.

FOLLOW-UP to make them certified: instantiate `coverOfDifference` for these tiny specs and prove the
hand lists are covers (or derive the lists from it). -/

/-- Complete truth-signature cover for the single `monotonic` leaf. (Hand-authored — see the
section note above: cover-ness is hand-checked, not machine-proven.) -/
private def monotonicGuardCands : List Value :=
  [amountStep (some 0) (some 0), amountStep (some 1) (some 0)]

/-- Complete joint signature cover for `monotonic` and `fieldDelta (-1)`. -/
private def contradictionGuardCands : List Value :=
  [amountStep none none, amountStep (some 1) (some 0), amountStep (some 0) (some 0)]

/-- Complete joint signature cover for `monotonic`, `immutable`, and `fieldDelta 0`:
`(F,T,F)`, `(F,F,F)`, `(T,T,T)`, `(T,F,F)`. -/
private def immutableGuardCands : List Value :=
  [amountStep none (some 0), amountStep (some 0) none,
   amountStep (some 0) (some 0), amountStep (some 0) (some 1)]

private def crossEqGuardCands : List Value :=
  [PredRE.transitionSymbol (.record [])
      (.record [("left", .int 0), ("right", .int 0)]),
   PredRE.transitionSymbol (.record []) (.record [])]

#guard differenceRE monotonicAmount = true
#guard rigidRE monotonicAmount = true
#guard emptyFix monotonicGuardCands 32 monotonicAmount = some false

#guard differenceRE reactiveCatalog = true
#guard rigidRE reactiveCatalog = true

#guard differenceRE monotonicContradiction = true
#guard emptyFix contradictionGuardCands 32 monotonicContradiction = some true

#guard differenceRE presentImmutableDeltaDiff = true
#guard emptyFix immutableGuardCands 128 presentImmutableDeltaDiff = some true

#guard differenceRE immutableDeltaDiff = true
#guard emptyFix immutableGuardCands 128 immutableDeltaDiff = some false

#guard differenceRE crossFieldEq = true
#guard rigidRE crossFieldEq = true
#guard emptyFix crossEqGuardCands 32 crossFieldEq = some false

#guard differenceRE crossFieldLe = true
#guard emptyFix crossEqGuardCands 32 crossFieldLe = some false

/-! ## Axiom hygiene -/

#assert_all_clean [
  DBM.noNegativeCycle_of_satisfies, DBM.potential_satisfies, DBM.feasible_iff_noNegativeCycle,
  simpleDifference?_reads, constraintDifference?_reads, predDifference?_reads,
  selectedRegion_regionValue_satisfies, regionValue_cutTruth,
  restrictDifferenceSymbol_same, restrictDifferenceSymbol_mem_differenceCands,
  coverOfDifference, rigidRE_of_differenceLeaves, differenceRE_symDiff,
  predRE_emptiness_decidable_difference, predRE_equivalence_decidable_difference
]

end Dregg2.Crypto.Deriv
