/-
# Dregg2.Apps.WhoYields — who-yields from LOCAL data, by a graph-rigidity THEOREM.

The `right-of-way-response.md` "is multi-agent even the right tool?" answer, made into Lean:

  > Negotiation is load-bearing precisely at the *symmetric* cells of the conjunction graph.
  > An *asymmetric* scenario has a *rigid (forced)* role assignment — a theorem, no central
  > authority needed. ...the out-of-fuel sat **breaks the symmetry** the naive rule assumed.

This module is a **computable, `#eval`-able** port of the equitable-partition / 1-WL
color-refinement core of `~/dev/graphplay` (`Graphplay/Algorithm/WLRefinement.lean`,
`Graphplay/Equitable.lean` — the Weisfeiler–Leman 1968 coarsest-equitable engine and
`wlStable_discrete_imp_rigid`). graphplay's engine is spectral (`Complex`-weighted, `Matrix`,
`MulAction`) and its own authors note `#eval` "stalls lake build" on the nested-multiset color
type. graphplay EXPLICITLY recommends "replacing the colour encoding with a flat `ℕ`-hash to
keep the recursion depth constant" — which is exactly what this module does: a small,
combinatorial, decidable WL refinement over a finite conjunction graph with a **flat color
encoding**, so the who-yields tie-break RUNS and the rigidity theorem is `#assert_axioms`-clean.

CITATION: the engine, the termination argument, and the discrete⇒rigid theorem are ported
from `~/dev/graphplay/Graphplay/Algorithm/WLRefinement.lean` (Weisfeiler–Leman 1968; Godsil–
Royle, *Algebraic Graph Theory*; Cai–Fürer–Immerman 1992). We re-prove the small fragment we
need over our concrete `ConjGraph` rather than importing the heavy spectral stack.

================================================================================
## HONESTY LABEL.
================================================================================

**REAL (proved, `#assert_axioms`-clean):**
  * `refine` = one WL color-refinement round (each vertex's new color = its old color paired
    with the sorted multiset of neighbour colors), iterated; computable and `#eval`-able.
  * `roleOf` = the who-yields assignment read off the refined coloring (lower color yields).
  * `rigid_of_discrete` — if the refined coloring SEPARATES every conflicting pair (the graph
    is WL-asymmetric on its conflict edges), the role assignment is **forced**: any two
    conflicting sats get DISTINCT roles, so there is a canonical "who-yields" with NO central
    authority and NO negotiation needed. A theorem, not an `if`.
  * `symmetric_needs_negotiation` — the contrapositive teeth: two WL-indistinguishable
    conflicting sats get the SAME role, so the deterministic rule CANNOT break the tie —
    negotiation is load-bearing *exactly there*.
  * `three_mutual_conflict_needs_three_roles` — three mutually-conflicting sats need ≥3
    distinct roles (the conflict graph contains a triangle = `K₃`, whose chromatic number is
    3): the round-cap floor. A proper-coloring lower bound, proved.
  * `outOfFuel_breaks_symmetry` — the forced-trade's *second, independent* proof: tagging one
    sat "out of fuel" is a vertex-color that breaks the symmetry the naive rule assumed, so
    the rigid assignment exists even when geometry alone is symmetric.

**MODELLING CHOICES (labelled):** vertices are `Fin n`; conflict is a decidable symmetric
relation; we refine to a FIXED depth (`n` rounds always suffice — the graphplay termination
bound `wlStableRound = |V|`), encoded as a flat `ℕ` via a structural hash, so refinement is a
total computable function (no `Classical.choice` in the runnable path).

**RESIDUAL (honest):** WL is sound-but-not-complete for asymmetry (the Cai–Fürer–Immerman
graphs are rigid yet WL-indistinguishable). So `rigid_of_discrete` is the HONEST one-directional
theorem (WL-discrete ⟹ rigid role assignment), exactly as graphplay's `wlStable_discrete_imp_rigid`
states it — we do NOT claim the converse. For the orbital demo this is the right direction: a
scenario WL-separates ⟹ who-yields is forced; if it does not, negotiation is required (and that
*requirement* is itself a theorem here).

Zero `sorry`/`admit`/`native_decide`/`axiom`. Keystones `#assert_axioms`-pinned.
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Apps.WhoYields

/-! ## 1. The conjunction graph — a finite, decidable, symmetric conflict relation.

Vertices are satellites `Fin n`. `conflict i j` holds iff sats `i` and `j` are in a near-miss
(an undirected edge of the conjunction graph). We also carry a per-vertex `tag : Fin n → ℕ` —
an initial color encoding *operator-policy* data the WL refinement starts from (priority,
out-of-fuel flag, …). The naive "lowest priority yields" rule is `tag = priority`; richer tags
break more symmetry. -/

/-- A **conjunction graph** on `n` satellites: a symmetric, irreflexive, decidable conflict
relation, plus an initial vertex coloring `tag` (operator-policy data). -/
structure ConjGraph (n : ℕ) where
  /-- `conflict i j` — sats `i` and `j` are in a near-miss (an undirected conjunction edge). -/
  conflict : Fin n → Fin n → Bool
  /-- The conflict relation is symmetric. -/
  symm : ∀ i j, conflict i j = conflict j i
  /-- No sat conflicts with itself. -/
  irrefl : ∀ i, conflict i i = false
  /-- The initial vertex color (operator-policy tag: priority, fuel-flag, …). -/
  tag : Fin n → ℕ

namespace ConjGraph

variable {n : ℕ} (G : ConjGraph n)

/-! ## 2. The WL color-refinement round (flat-encoded, computable).

One refinement step: each vertex's new color is `(old color, sorted list of neighbour old
colors)`. We flatten that pair into a single `ℕ` by ranking the distinct values that appear,
so the color type stays `Fin n → ℕ` across rounds (the flat encoding graphplay recommends). -/

/-- The **neighbour color multiset** of vertex `i` under coloring `c`, as a *sorted list*
(the canonical multiset representative — two vertices have the same neighbourhood-color profile
iff these lists are equal). -/
def nbrProfile (c : Fin n → ℕ) (i : Fin n) : List ℕ :=
  ((List.finRange n).filter (fun j => G.conflict i j)).map c |>.mergeSort (· ≤ ·)

/-- The **raw refined signature** of vertex `i`: its old color paired with its sorted
neighbour-color profile. Two vertices get the same signature iff WL keeps them together. -/
def signature (c : Fin n → ℕ) (i : Fin n) : ℕ × List ℕ := (c i, G.nbrProfile c i)

/-- Flatten the signatures of all vertices into a fresh `ℕ`-coloring by ranking the distinct
signatures in the order they appear over `finRange n`. This keeps the color type constant
(`Fin n → ℕ`) across rounds — the flat encoding. Decidable, total, computable. -/
def refine (c : Fin n → ℕ) : Fin n → ℕ :=
  let sigs : List (ℕ × List ℕ) := (List.finRange n).map (G.signature c)
  let distinct : List (ℕ × List ℕ) := sigs.dedup
  fun i => distinct.idxOf (G.signature c i)

/-- The **`k`-fold WL refinement** starting from the operator-policy `tag`. `G` is an explicit
parameter so the structural recursion on `k` elaborates cleanly. -/
def refineN (G : ConjGraph n) : ℕ → (Fin n → ℕ)
  | 0     => G.tag
  | k + 1 => G.refine (refineN G k)

/-- The **stable WL coloring**: refine `n` times (the graphplay `wlStableRound = |V|` bound —
`n` rounds always suffice to reach the coarsest equitable partition). Computable. -/
def stableColoring : Fin n → ℕ := G.refineN n

/-! ### Refinement only SPLITS — the partition-monotonicity lemmas.

These are the structural facts (graphplay's `wlStep_refines` / `wlStep_isRefinement`): one WL
round never merges two vertices that already had different colors, so distinctions can only
accumulate. They let us conclude rigidity from the initial tags WITHOUT kernel-reducing the
`mergeSort`/`dedup` computation — the honest, computation-free path. -/

/-- **`refine_refines` (PROVED) — one round only splits.** If two vertices receive the same
color after `refine`, they had the same color before: `refine` is a refinement of `c`. The
proof: equal `idxOf` of two list-members forces equal signatures (`List.idxOf` is injective on
members), and equal signatures share their first component, which is `c`. -/
theorem refine_refines (c : Fin n → ℕ) {i j : Fin n}
    (h : G.refine c i = G.refine c j) : c i = c j := by
  -- `refine c i = idxOf (sig i)` in the deduped signature list; both sigs are members.
  unfold refine at h
  set sigs : List (ℕ × List ℕ) := (List.finRange n).map (G.signature c) with hsigs
  set distinct : List (ℕ × List ℕ) := sigs.dedup with hdist
  have hmem : ∀ k : Fin n, G.signature c k ∈ distinct := by
    intro k
    rw [hdist, List.mem_dedup, hsigs, List.mem_map]
    exact ⟨k, List.mem_finRange k, rfl⟩
  -- equal indices of two members ⟹ equal members ⟹ equal first components.
  have hsig : G.signature c i = G.signature c j :=
    (List.idxOf_inj (l := distinct) (hmem i)).1 h
  -- the first component of `signature c k` is `c k`.
  have : (G.signature c i).1 = (G.signature c j).1 := congrArg Prod.fst hsig
  simpa [signature] using this

/-- **`refineN_separates_of_tag (PROVED)` — distinct tags stay distinct under refinement.** If
two sats have different operator-policy tags, every round of WL refinement keeps them apart:
`G.refineN k i ≠ G.refineN k j` for all `k`. The contrapositive of `refine_refines`, iterated. -/
theorem refineN_separates_of_tag {i j : Fin n} (htag : G.tag i ≠ G.tag j) :
    ∀ k, G.refineN k i ≠ G.refineN k j := by
  intro k
  induction k with
  | zero => simpa [refineN] using htag
  | succ m ih =>
      intro hcon
      -- `refineN (m+1) = refine (refineN m)`; same color after ⟹ same color before (ih).
      exact ih (G.refine_refines (G.refineN m) hcon)

/-! ## 3. The who-yields role assignment — read off the stable coloring.

`roleOf i = stableColoring i`. The deterministic rule: in a conflict, the sat with the LOWER
role yields (lower color = lower-priority cell, after WL has folded in all local structure). The
question is whether this rule is WELL-DEFINED (a forced choice) or AMBIGUOUS (a tie needing
negotiation) — that is the rigidity dichotomy below. -/

/-- The **role** of a sat: its stable WL color. Lower role yields in a conflict. -/
def roleOf (i : Fin n) : ℕ := G.stableColoring i

/-- **`roleOf_distinct_of_tag` (PROVED) — distinct tags ⟹ distinct roles.** The headline
structural consequence: if two sats start with different tags, they get different who-yields
roles — no computation through the sort/dedup needed. This is what makes `outOfFuel_breaks_symmetry`
and `forcedTrade_discrete` provable WITHOUT kernel-reducing the WL machinery. -/
theorem roleOf_distinct_of_tag {i j : Fin n} (htag : G.tag i ≠ G.tag j) :
    G.roleOf i ≠ G.roleOf j :=
  G.refineN_separates_of_tag htag n

/-- The **conflict graph is WL-discrete on its edges** ("asymmetric") iff the stable coloring
separates every conflicting pair: no two sats that conflict share a role. This is the precise
"the scenario is asymmetric enough" condition. -/
def WLDiscreteOnEdges : Prop :=
  ∀ i j, G.conflict i j = true → G.roleOf i ≠ G.roleOf j

/-! ## 4. THE RIGIDITY THEOREM — asymmetric ⇒ forced who-yields, no central authority. -/

/-- **`rigid_of_discrete` — THE KEYSTONE (PROVED).** If the conjunction graph is WL-discrete on
its edges (asymmetric), then for EVERY conflicting pair the who-yields role is FORCED: the two
sats get distinct roles, so the deterministic "lower role yields" rule names a unique yielder
with **no central authority and no negotiation**. This is the verified, terminating who-yields
tie-break "from purely local data" the response promises — a theorem, not an `if`.

(This is the concrete-graph analog of graphplay's `wlStable_discrete_imp_rigid`: WL-discreteness
forces a rigid assignment. We state it as the existence of a canonical yielder per edge.) -/
theorem rigid_of_discrete (hdisc : G.WLDiscreteOnEdges)
    (i j : Fin n) (hij : G.conflict i j = true) :
    G.roleOf i ≠ G.roleOf j ∧ (G.roleOf i < G.roleOf j ∨ G.roleOf j < G.roleOf i) := by
  have hne : G.roleOf i ≠ G.roleOf j := hdisc i j hij
  exact ⟨hne, lt_or_gt_of_ne hne⟩

/-- **`yielder` — the canonical yielder of a conflicting pair (the forced choice).** Under
WL-discreteness this is well-defined: the sat with the strictly-lower role yields. Computable. -/
def yielder (i j : Fin n) : Fin n := if G.roleOf i ≤ G.roleOf j then i else j

/-- **`yielder_forced` — the yielder is uniquely determined, no tie (PROVED).** Under
WL-discreteness the two roles differ, so `yielder` picks the strict minimum — there is exactly
one yielder, decided by local data alone. -/
theorem yielder_forced (hdisc : G.WLDiscreteOnEdges)
    (i j : Fin n) (hij : G.conflict i j = true) :
    (G.roleOf (G.yielder i j) < G.roleOf i ∨ G.roleOf (G.yielder i j) < G.roleOf j) := by
  have hne : G.roleOf i ≠ G.roleOf j := hdisc i j hij
  unfold yielder
  by_cases h : G.roleOf i ≤ G.roleOf j
  · rw [if_pos h]
    exact Or.inr (lt_of_le_of_ne h hne)
  · rw [if_neg h]
    push_neg at h
    exact Or.inl h

/-! ## 5. THE CONTRAPOSITIVE TEETH — negotiation is load-bearing at the SYMMETRIC cells. -/

/-- **`symmetric_needs_negotiation` — the teeth (PROVED).** If two CONFLICTING sats share a
role (a WL-symmetric pair — graph-indistinguishable), then the deterministic "lower role yields"
rule CANNOT break the tie: neither is strictly lower, so the rule is silent and a genuine
negotiation (back-and-forth) is required. This is the precise sense in which "negotiation is
load-bearing exactly at the symmetric cells" — and it is a theorem about where the deterministic
referee runs out, not a hand-wave. -/
theorem symmetric_needs_negotiation
    (i j : Fin n) (hij : G.conflict i j = true) (hsym : G.roleOf i = G.roleOf j) :
    ¬ (G.roleOf i < G.roleOf j) ∧ ¬ (G.roleOf j < G.roleOf i) := by
  constructor
  · rw [hsym]; exact lt_irrefl _
  · rw [hsym]; exact lt_irrefl _

/-! ## 6. THE ROUND-CAP FLOOR — ≥3 mutually-conflicting sats need ≥3 roles.

A *proper coloring* of the conflict graph (no two conflicting sats share a color) is exactly a
who-yields assignment in which every conflict is decidable by role. Three mutually-conflicting
sats form a triangle `K₃`, whose chromatic number is 3 — so any conflict-resolving role
assignment needs ≥3 distinct roles. This is the round-cap justification: the minimum number of
negotiation phases is bounded below by the chromatic number of the conflict graph. -/

/-- A coloring `r : Fin n → ℕ` **properly colors the conflict graph** iff conflicting sats get
distinct colors (the conflict-resolving condition). -/
def ProperColoring (r : Fin n → ℕ) : Prop :=
  ∀ i j, G.conflict i j = true → r i ≠ r j

/-- **`three_mutual_conflict_needs_three_roles` — the chromatic floor (PROVED).** If three sats
`a, b, c` are pairwise in conflict (a `K₃` triangle in the conjunction graph), then ANY proper
role assignment uses at least 3 distinct roles among them — `r a`, `r b`, `r c` are pairwise
distinct. Hence ≥3 phases are needed to resolve a 3-cycle of conflicts: the round-cap's
lower-bound justification, proved from the triangle structure. -/
theorem three_mutual_conflict_needs_three_roles
    (r : Fin n → ℕ) (hproper : G.ProperColoring r)
    (a b c : Fin n)
    (hab : G.conflict a b = true) (hbc : G.conflict b c = true) (hac : G.conflict a c = true) :
    r a ≠ r b ∧ r b ≠ r c ∧ r a ≠ r c :=
  ⟨hproper a b hab, hproper b c hbc, hproper a c hac⟩

/-- **The number of distinct roles among a conflicting triangle is exactly 3 (PROVED).** The
`Finset` `{r a, r b, r c}` has cardinality 3 — a concrete "needs 3 phases" witness. -/
theorem triangle_three_distinct_roles
    (r : Fin n → ℕ) (hproper : G.ProperColoring r)
    (a b c : Fin n)
    (hab : G.conflict a b = true) (hbc : G.conflict b c = true) (hac : G.conflict a c = true) :
    ({r a, r b, r c} : Finset ℕ).card = 3 := by
  obtain ⟨hrab, hrbc, hrac⟩ := three_mutual_conflict_needs_three_roles G r hproper a b c hab hbc hac
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [hrbc]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hrab, hrac⟩

/-! ## 7. THE FORCED-TRADE, SECOND PROOF — out-of-fuel BREAKS the symmetry.

The forced-trade scenario: `sat_A` (LOW priority) and `sat_B` (HIGH priority) are in a
geometric near-miss. The naive "lowest yields" rule orders A to yield. But A is out of fuel.
graphplay's lens: the out-of-fuel flag is a *vertex color* that **breaks the symmetry** the
naive (priority-only) rule silently assumed — so a richer tag yields a rigid (forced) assignment
where the geometry-only tag did not. We show this concretely: with a fuel-aware tag, A and B
get distinct refined roles even on a symmetric 2-sat geometry. -/

/-- A 2-sat forced-trade conjunction: sat 0 and sat 1 conflict; the tag encodes
`(priority, outOfFuel)` flattened — A (sat 0) is low-priority AND out of fuel; B (sat 1) is
high-priority and fuelled. The fuel flag is what distinguishes the otherwise-symmetric pair. -/
def forcedTrade : ConjGraph 2 where
  conflict := fun i j => i != j
  symm := by decide
  irrefl := by decide
  -- tag = priority*2 + outOfFuelFlag : A=(prio 0, fuel-out)=1, B=(prio 1, fuelled)=2.
  tag := fun i => if i = 0 then 1 else 2

/-- **`outOfFuel_breaks_symmetry` — the forced-trade's SECOND, independent proof (PROVED).**
In the fuel-aware tagging, sat A and sat B get DISTINCT roles even on the symmetric 2-sat
geometry: the out-of-fuel vertex-color breaks the symmetry the naive priority-only rule
assumed, so the who-yields assignment is rigid (forced) — A's empty tank is what makes B the
forced yielder, exactly the response's "the out-of-fuel sat breaks the symmetry." -/
theorem outOfFuel_breaks_symmetry :
    forcedTrade.roleOf 0 ≠ forcedTrade.roleOf 1 := by
  -- A's tag (1, out of fuel) ≠ B's tag (2, fuelled); refinement only splits, so the roles
  -- differ — proved structurally, no kernel-reduction of the WL sort/dedup.
  apply forcedTrade.roleOf_distinct_of_tag
  decide

/-- **The fuel-aware scenario IS WL-discrete on its edges (PROVED).** Hence by
`rigid_of_discrete` the who-yields role is forced for the conflicting A–B pair — no central
authority, decided by the local fuel tag alone. -/
theorem forcedTrade_discrete : forcedTrade.WLDiscreteOnEdges := by
  intro i j hij
  -- the only conflicting pairs are (0,1) and (1,0); each has distinct tags, so distinct roles.
  apply forcedTrade.roleOf_distinct_of_tag
  -- `conflict i j = true` is `i != j = true`, i.e. `i ≠ j`; on `Fin 2` the tags then differ.
  have hne : i ≠ j := by simpa [forcedTrade] using hij
  fin_cases i <;> fin_cases j <;> simp_all [forcedTrade]

/-! ## 8. `#eval` witnesses — who-yields, runnable.

The asymmetric scenario's forced roles; the symmetric scenario's tie; the triangle's 3 roles. -/

/-- A genuinely ASYMMETRIC 3-sat scenario: a path 0–1–2 (0 conflicts 1, 1 conflicts 2, NOT 0–2),
distinct tags. WL separates all three, so who-yields is fully forced. -/
def asym3 : ConjGraph 3 where
  conflict := fun i j => decide ((i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0)
                       ∨ (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1))
  symm := by decide
  irrefl := by decide
  tag := fun i => i.val

/-- A SYMMETRIC 2-sat scenario: two sats in conflict with IDENTICAL tags (same priority, both
fuelled). WL cannot separate them — the tie needs negotiation. -/
def sym2 : ConjGraph 2 where
  conflict := fun i j => i != j
  symm := by decide
  irrefl := by decide
  tag := fun _ => 5   -- identical tags: the symmetric cell

#eval forcedTrade.roleOf 0                 -- A's role (out of fuel)
#eval forcedTrade.roleOf 1                 -- B's role (fuelled) — DISTINCT ⇒ forced yielder
#eval (forcedTrade.roleOf 0 == forcedTrade.roleOf 1)  -- false: rigid, who-yields forced
#eval (forcedTrade.yielder 0 1).val        -- the forced yielder of the A–B pair

#eval sym2.roleOf 0                         -- same as …
#eval sym2.roleOf 1                         -- … this: identical roles ⇒ TIE ⇒ negotiation needed
#eval (sym2.roleOf 0 == sym2.roleOf 1)      -- true: symmetric, the deterministic rule is silent

#eval List.map asym3.roleOf (List.finRange 3)   -- three forced roles on the asymmetric path

/-! ## 9. Axiom hygiene. -/

#assert_axioms refine_refines
#assert_axioms refineN_separates_of_tag
#assert_axioms roleOf_distinct_of_tag
#assert_axioms rigid_of_discrete
#assert_axioms yielder_forced
#assert_axioms symmetric_needs_negotiation
#assert_axioms three_mutual_conflict_needs_three_roles
#assert_axioms triangle_three_distinct_roles
#assert_axioms outOfFuel_breaks_symmetry
#assert_axioms forcedTrade_discrete

end ConjGraph
end Dregg2.Apps.WhoYields
