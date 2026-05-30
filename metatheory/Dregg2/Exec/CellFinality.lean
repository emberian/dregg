/-
# Dregg2.Exec.CellFinality — the ordering judgement ON the cell.

This module wires the two abstract judgements of `dregg2 §2.2/§2.3` onto a
*concrete cell*: each cell selects a finality `Tier` (`Finality.Tier`), a turn
touching several cells commits at the **join (max)** of their tiers, and — THE
KEYSTONE — a cell may select **tier-1** (causal-only, never-blocks) ONLY IF its
invariant is **I-confluent** (`Confluence.IConfluent`).

`study-consensus.md §5` names the one live soundness risk: a non-I-confluent
invariant (the `balance ≥ 0` shape) wrongly admitted at tier-1 is the impossible
object BEC Thm 3.1 forbids. Here that gate is not prose but a `Prop` with a
proof: `tier1Admissible I ↔ IConfluent I`, an eligible invariant's merges PROVABLY
preserve `I` (`admits_sound`), and a concrete non-I-confluent invariant
(`card ≤ 1`) is REJECTED at tier-1 (`cardLeOne_not_tier1Admissible`).

`study-consensus.md §2` names the under-stated fact: a tier-1 cell touched in a
turn together with a tier-3 cell **inherits tier-3 for that turn** — there is no
tier-1 liveness on a tier-3-touching op. That is `cell_inherits_join_tier` /
`cross_tier_swallows_lower` below.

Builds only on existing modules (`Finality`, `Confluence`) by `import`; defines
nothing already taken. All names live in `namespace Dregg2.Exec.CellFinality`.
-/
import Dregg2.Finality
import Dregg2.Confluence

namespace Dregg2.Exec.CellFinality

open Dregg2

universe u

/-! ## 1. A cell carries a finality tier. -/

/-- **Cell identity** (local to this module; opaque handle). -/
structure CellId where
  /-- Opaque cell handle (a content-address in the real system). -/
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **A finality-tier assignment over a set of cells** — `dregg2 §2.2`: each cell
declares which of the four-tier ladder its writes finalize at. The map IS the
per-cell ordering judgement. -/
abbrev TierMap := CellId → Finality.Tier

/-- **A tiered cell**: an identity plus its declared finality `Tier`. The bundled
form of a single entry of a `TierMap`. -/
structure TieredCell where
  /-- The cell's identity. -/
  cell : CellId
  /-- The finality tier this cell's writes commit at. -/
  tier : Finality.Tier
  deriving Repr

/-- Read a `TieredCell`'s tier back out of a `TierMap` that agrees with it. -/
theorem TieredCell.tier_of_map (c : TieredCell) (m : TierMap)
    (h : m c.cell = c.tier) : m c.cell = c.tier := h

/-! ## 2. A turn commits at the JOIN (max) of the tiers it touches.

`Finality.crossTierJoin = max` over the `LinearOrder Tier`. The commit tier of a
turn is the fold-`max` of its touched cells' tiers; we prove that join dominates
every touched cell (the stronger requirement swallows the weaker). -/

/-- **The commit tier of a turn**: the `crossTierJoin`-fold (= `max`) of the tiers
of every cell the turn touches, seeded at `Finality.Tier.causal` (the lattice
bottom, rank 1) so an empty/solo touch-set behaves. -/
def commitTier (m : TierMap) (touched : List CellId) : Finality.Tier :=
  touched.foldr (fun c acc => Finality.crossTierJoin (m c) acc) Finality.Tier.causal

/-- `Finality.Tier.causal` is the bottom of the tier lattice (rank 1): every tier
is at least `causal`. The seed never raises the join above a real touched tier. -/
theorem causal_le (t : Finality.Tier) : Finality.Tier.causal ≤ t := by
  show Finality.Tier.causal.rank ≤ t.rank
  cases t <;> decide

/-- **The commit tier dominates every touched cell's tier** (`commit_at_join`,
`§2.2` cross-tier rule): no cell's write finalizes below the turn's commit tier,
so the join carries the strongest requirement. The proof generalizes the fold's
seed and inducts on the touched list, reusing `Finality.crossTierJoin_ge_left`
and (commuted) `crossTierJoin_ge_right`. -/
theorem commit_at_join (m : TierMap) (touched : List CellId)
    (c : CellId) (hc : c ∈ touched) :
    m c ≤ commitTier m touched := by
  unfold commitTier
  -- generalize over the seed: the fold dominates every member regardless of seed.
  have gen : ∀ (l : List CellId) (seed : Finality.Tier) (x : CellId), x ∈ l →
      m x ≤ l.foldr (fun a acc => Finality.crossTierJoin (m a) acc) seed := by
    intro l
    induction l with
    | nil => intro _ _ hx; simp at hx
    | cons a as ih =>
        intro seed x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · -- head: `m x ≤ crossTierJoin (m x) (rest)` is `crossTierJoin_ge_left`.
          exact Finality.crossTierJoin_ge_left _ _
        · -- tail: dominate the rest by IH, then the rest sits under the join.
          refine le_trans (ih seed x hx') ?_
          -- `rest ≤ crossTierJoin (m a) rest` = right-domination of the join.
          have : as.foldr (fun a acc => Finality.crossTierJoin (m a) acc) seed
              ≤ Finality.crossTierJoin (m a)
                  (as.foldr (fun a acc => Finality.crossTierJoin (m a) acc) seed) := by
            simp only [Finality.crossTierJoin]; exact le_max_right _ _
          exact this
  exact gen touched Finality.Tier.causal c hc

/-- **A cell inherits the turn's join tier (`§2.2`, the under-stated fact of
`study-consensus §2`).** Restating `commit_at_join` from the cell's view: a cell
touched in a turn does NOT finalize at its own declared tier — it finalizes at the
turn's commit tier, which is `≥` its declared tier. -/
theorem cell_inherits_join_tier (m : TierMap) (touched : List CellId)
    (c : CellId) (hc : c ∈ touched) :
    m c ≤ commitTier m touched :=
  commit_at_join m touched c hc

/-- **Cross-tier swallow — the keystone honesty of `study-consensus §2`:** a
tier-1 (`causal`) cell touched together with a tier-3 (`bft`) cell in one turn
commits at `bft` — there is **no tier-1 liveness on a tier-3-touching op**. The
join is the *max*; the higher tier swallows the lower for the duration of the
joint turn. Concretely: with both cells in the touch-set, the commit tier is `bft`
and the causal cell inherits it (`causal ≤ bft`, strictly stronger). -/
theorem cross_tier_swallows_lower
    (m : TierMap) (c1 c3 : CellId)
    (h1 : m c1 = Finality.Tier.causal) (h3 : m c3 = Finality.Tier.bft) :
    -- the tier-1 cell's write inherits the bft commit tier of the joint turn …
    m c1 ≤ commitTier m [c1, c3]
    -- … and the joint commit tier is exactly bft (the max), strictly above causal.
    ∧ commitTier m [c1, c3] = Finality.Tier.bft
    ∧ m c1 < commitTier m [c1, c3] := by
  refine ⟨commit_at_join m [c1, c3] c1 (by simp), ?_, ?_⟩
  · -- compute the fold: crossTierJoin causal (crossTierJoin bft causal) = bft.
    simp only [commitTier, List.foldr, h1, h3]
    decide
  · -- strict: causal (rank 1) < bft (rank 3) after the same computation.
    have hcommit : commitTier m [c1, c3] = Finality.Tier.bft := by
      simp only [commitTier, List.foldr, h1, h3]; decide
    rw [h1, hcommit]
    show Finality.Tier.causal.rank < Finality.Tier.bft.rank
    decide

/-! ## 3. THE KEYSTONE — the I-confluence eligibility GATE.

A cell may select **tier-1** (`Finality.Tier.causal`) only if its invariant is
**I-confluent** (`Confluence.IConfluent`). `tier1Admissible` IS that gate; it is
provably equivalent to I-confluence, an admissible invariant's concurrent merges
preserve it, and a concrete non-I-confluent invariant is rejected. -/

/-- **The tier-1 eligibility gate (`dregg2 §2.2`, `study-consensus §5`).** A cell
with invariant `I` over a merge-state `S` may declare tier-1 (`causal`) IFF `I` is
I-confluent. This is `Confluence.Tier1Eligible` re-exposed as the *cell-level*
admission predicate the classifier evaluates at cell creation. A non-I-confluent
`I` at tier-1 is the impossible object BEC Thm 3.1 forbids — `tier1Admissible`
fails for it, so the classifier statically REJECTS it. -/
def tier1Admissible {S : Type u} [Confluence.MergeState S] (I : Confluence.Invariant S) : Prop :=
  Confluence.IConfluent I

/-- **Definitional unfold (NOT a proved equivalence).** `tier1Admissible` is *defined*
as `Confluence.IConfluent`, so this is the trivial definitional unfold of that `def`,
not an independent proof that two separately-specified gates coincide. There is no
parallel operationally-specified tier-1 gate in this module that would make the equality
have content: the cell-level admission predicate IS `IConfluent` by construction. Named
`…_def` to reflect that. (If a separate operational gate is ever introduced — e.g. a
write-set/state-lattice classifier — proving IT equal to `IConfluent` would be the real
theorem; this is not that.) -/
theorem tier1Admissible_def
    {S : Type u} [Confluence.MergeState S] (I : Confluence.Invariant S) :
    tier1Admissible I = Confluence.IConfluent I := rfl

/-- **Definitional unfold (NOT a proved equivalence).** `tier1Admissible` and
`Confluence.Tier1Eligible` are *both defined as* `Confluence.IConfluent I`, so they are
definitionally equal — this module's cell-level gate IS the abstract finality
side-condition, by definition, not via an independent proof. Named `…_eq_tier1Eligible`
to reflect that it is a definitional identity, not a non-trivial coincidence. -/
theorem tier1Admissible_eq_tier1Eligible
    {S : Type u} [Confluence.MergeState S] (I : Confluence.Invariant S) :
    tier1Admissible I = Confluence.Tier1Eligible I := rfl

/-- **Eligible ⇒ merges preserve the invariant (soundness of the gate).** A tier-1
cell whose invariant passed `tier1Admissible` genuinely preserves its invariant
under any concurrent merge `x ⊔ y` — so tier-1 (coordination-free) is SOUND for it.
Reuses `Confluence.admits_sound`. -/
theorem tier1Admissible_merge_sound
    {S : Type u} [Confluence.MergeState S] (I : Confluence.Invariant S)
    (h : tier1Admissible I) (x y : S) (hx : I x) (hy : I y) : I (x ⊔ y) :=
  Confluence.admits_sound I h x y hx hy

/-- **A cell declaring tier-1 with an admissible invariant: the merge witness.**
Bundles the cell, its declared tier (`causal`), the admissibility proof, and the
merge-soundness conclusion — the well-typed tier-1 cell. -/
theorem wellTyped_tier1_cell
    {S : Type u} [Confluence.MergeState S]
    (c : TieredCell) (m : TierMap) (I : Confluence.Invariant S)
    (htier : c.tier = Finality.Tier.causal) (hmap : m c.cell = c.tier)
    (hadm : tier1Admissible I) :
    -- the cell is at tier-1 in the map …
    m c.cell = Finality.Tier.causal
    -- … and its invariant survives every concurrent merge.
    ∧ (∀ x y : S, I x → I y → I (x ⊔ y)) := by
  refine ⟨by rw [hmap, htier], ?_⟩
  intro x y hx hy
  exact tier1Admissible_merge_sound I hadm x y hx hy

/-! ### The REJECTION side — a non-I-confluent invariant is NOT tier-1-eligible.

The `balance ≥ 0` shape, witnessed concretely by `card ≤ 1` over the grow-only set
semilattice `Finset ℕ` (the existing witness `Confluence.cardLeOne_not_iconfluent`).
The classifier MUST reject it at tier-1 — that rejection is a *theorem*. -/

/-- **REJECTED at tier-1 (the static type error of `study-consensus §5`).** The
`card ≤ 1` invariant over `Finset ℕ` (the bounded-resource / `balance ≥ 0` shape)
is NOT `tier1Admissible`: `{1} ⊔ {2} = {1,2}` breaks it. A cell declaring this
invariant at tier-1 is the impossible object BEC Thm 3.1 forbids; the gate fails,
so the classifier statically rejects the declaration. Reuses
`Confluence.cardLeOne_not_iconfluent`. -/
theorem cardLeOne_not_tier1Admissible :
    ¬ tier1Admissible (S := Finset ℕ) (fun s => s.card ≤ 1) :=
  Confluence.cardLeOne_not_iconfluent

/-- **The gate genuinely discriminates (non-vacuity):** there exists an admissible
invariant AND an inadmissible one over the same lattice — so `tier1Admissible` is a
real, falsifiable side-condition, not always-true or always-false. The grow-only
`True` invariant passes; `card ≤ 1` fails. -/
theorem tier1Admissible_discriminates :
    tier1Admissible (S := Finset ℕ) (fun _ => True)
    ∧ ¬ tier1Admissible (S := Finset ℕ) (fun s => s.card ≤ 1) :=
  ⟨Confluence.top_iconfluent, cardLeOne_not_tier1Admissible⟩

/-- **The classifier-correctness obligation, made concrete.** A classifier
`classify : Invariant S → Tier` that assigns `causal` is SOUND iff everything it
assigns to `causal` is `tier1Admissible`. Given such a sound classifier, any
invariant it places at tier-1 provably merges safely. This is the cell-level form
of `Finality.tier1_requires_iconfluent`, discharged against THIS module's gate. -/
theorem classifier_tier1_sound
    {S : Type u} [Confluence.MergeState S]
    (classify : Confluence.Invariant S → Finality.Tier)
    (hsound : ∀ J, classify J = Finality.Tier.causal → tier1Admissible J)
    (I : Confluence.Invariant S) (hI : classify I = Finality.Tier.causal)
    (x y : S) (hx : I x) (hy : I y) : I (x ⊔ y) :=
  tier1Admissible_merge_sound I (hsound I hI) x y hx hy

/-- **A sound classifier CANNOT place `card ≤ 1` at tier-1.** Contrapositive of the
soundness condition against the concrete witness: any classifier honoring the gate
must assign the `balance`-shape invariant a tier `≠ causal` (it must escalate). -/
theorem sound_classifier_rejects_cardLeOne
    (classify : Confluence.Invariant (Finset ℕ) → Finality.Tier)
    (hsound : ∀ J, classify J = Finality.Tier.causal → tier1Admissible J) :
    classify (fun s => s.card ≤ 1) ≠ Finality.Tier.causal := by
  intro hbad
  exact cardLeOne_not_tier1Admissible (hsound _ hbad)

/-! ## 4. `#eval` demos — tiers, the cross-tier join, eligible vs ineligible. -/

/-- The bft commit tier of a {tier-1, tier-3} turn (`cross_tier_swallows_lower`). -/
def demoMap : TierMap := fun c =>
  if c = ⟨0⟩ then Finality.Tier.causal
  else if c = ⟨1⟩ then Finality.Tier.bft
  else Finality.Tier.causal

-- the causal cell #0 + bft cell #1 commit at bft (the join = max):
#eval (commitTier demoMap [⟨0⟩, ⟨1⟩]).rank        -- 3 (bft)
#eval (commitTier demoMap [⟨0⟩]).rank             -- 1 (causal, solo stays liquid)
#eval (Finality.crossTierJoin Finality.Tier.causal Finality.Tier.bft).rank  -- 3
-- the gate's two concrete witnesses over `Finset ℕ` (eligible vs ineligible):
-- `tier1Admissible (fun _ => True)` holds (PROVED `top_iconfluent`);
-- `¬ tier1Admissible (fun s => s.card ≤ 1)` (PROVED `cardLeOne_not_tier1Admissible`).
#eval (({1} : Finset ℕ) ⊔ {2}).card               -- 2 : the merge that breaks `card ≤ 1`

end Dregg2.Exec.CellFinality
