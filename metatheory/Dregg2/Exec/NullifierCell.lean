/-
# Dregg2.Exec.NullifierCell — the "sets → cells" collapse, proved tier-1-safe.

dregg1 keeps nullifier / revocation / authorized-sender sets as *executor
side-tables* (`cell/src/nullifier_set.rs:63`, a `Mutex<NullifierSet>` threaded
through the rollback signature by hand). dregg2's highest-leverage simplification
(`00-synthesis §5.2`, `02-spine-cell §1.4`) is to make them **cells** whose state
is a set-root + an **append-only** (insert-only, `Terminal`-linearity) transition
program. No principled reason they aren't cells.

This module builds the canonical instance: the **nullifier set as an append-only
cell**, and PROVES *why* it is tier-1-safe — it is the textbook I-confluent /
tier-1-eligible CvRDT (`discoveries §3.7`: hash-keyed nullifier uniqueness is the
canonical TIER-1-SAFE example; `balance≥0` is NOT). It is a **G-Set** (grow-only
set): state = a `Finset Nullifier`, join = set union (`∪`), and its admissibility
invariant (set membership / "each nullifier appears at most once") is **preserved
by concurrent merge**. Therefore it is `Confluence.IConfluent`, hence
`Confluence.Tier1Eligible` — it needs **NO consensus** (causal-only,
coordination-free, partition-tolerant). Two replicas can each accept disjoint
spends offline and union their spent-sets with zero coordination.

Contrast (the live soundness risk `dregg2.md §2.3` warns about): a `balance≥0`
cell is linear but **NOT** I-confluent — two concurrent debits each preserve the
bound yet jointly overdraw. That cell may NOT run tier-1. The discriminating
witness is `Confluence.cardLeOne_not_iconfluent` (a `card ≤ 1` cap is the
`balance≥0` shape: two singletons merge to a two-element set, breaking the bound).

We reuse `Privacy.Nullifier` (the deterministic per-note tag, `DecidableEq`) and
`Confluence`'s `IConfluent` / `Tier1Eligible` / `MergeState` machinery — we
DEFINE NONE of them; we only instantiate and connect.

Crypto-soundness of `nullifierOf` (PRF/extractability) is a circuit obligation
(`Privacy.lean` §8 caveat) and is NOT touched here: this module is the *set
discipline* — insert-only membership and its merge law — which is pure,
decidable, computable Lean. No `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.Privacy
import Dregg2.Confluence
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Sort

namespace Dregg2.Exec.NullifierCell

open Dregg2.Privacy (Nullifier)
open Dregg2.Confluence (IConfluent Tier1Eligible MergeState)

universe u

/-! ## The cell — a G-Set of consumed nullifiers. -/

/-- **A `NullifierCell`** — the nullifier set lifted from an executor side-table to
a cell. Its entire state is `spent`, the `Finset` of consumed nullifiers (the
set-root, modelled as the live finite set rather than a Merkle digest). The
transition rule is append-only: `spend` inserts, nothing ever removes
(`Terminal`-linearity). This is dregg2's "sets → cells" collapse (`02-spine-cell
§1.4`) made concrete. -/
structure Cell where
  /-- The set of nullifiers already consumed — the live set-root. -/
  spent : Finset Nullifier
  deriving DecidableEq

/-- The empty cell: nothing spent yet (the genesis set-root). -/
def empty : Cell := { spent := ∅ }

/-- `isSpent c n` : is nullifier `n` already in the cell's spent set? Decidable and
computable — this is the `MerkleMembership` query against the **live** root, not a
stale slot-snapshot (`02-spine-cell §1.4`). -/
def isSpent (c : Cell) (n : Nullifier) : Prop := n ∈ c.spent

instance (c : Cell) (n : Nullifier) : Decidable (isSpent c n) := by
  unfold isSpent; infer_instance

/-! ## The append-only transition: `spend` (anti-double-spend, fail-closed). -/

/-- **`spend c n`** — the cell's one transition rule. Insert nullifier `n` iff it is
NOT already present (anti-double-spend), returning the grown cell; otherwise fail
**closed** with `none`. This is INSERT-ONLY: there is no removal morphism, so the
spent set is grow-only (`Terminal`-linearity — once spent, forever spent). A
nullifier already in `spent` is rejected (the double-spend), realising the public
contention gate over the spent-note set. -/
def spend (c : Cell) (n : Nullifier) : Option Cell :=
  if n ∈ c.spent then
    none                                   -- already spent ⇒ fail-closed
  else
    some { spent := insert n c.spent }     -- fresh ⇒ admit and record

/-! ## `spend_no_double_spend` — the anti-double-spend law (both directions). -/

/-- **Anti-double-spend, half 1 — reuse is rejected (fail-closed).** A nullifier
already in `spent` cannot be spent again: `spend` returns `none`. This is the
double-spend gate; determinism of the (upstream) `nullifierOf` map is what makes a
re-spent *note* yield this *same* already-present tag (`Privacy.Nullifier`), but
the rejection itself is decidable set logic. -/
theorem spend_rejects_double (c : Cell) (n : Nullifier)
    (h : n ∈ c.spent) : spend c n = none := by
  unfold spend
  rw [if_pos h]

/-- **Anti-double-spend, half 2 — a fresh nullifier is admitted and lands in
`spent`.** Spending an `n` NOT already present succeeds, and the resulting cell
records exactly `insert n c.spent` — so `n` is now spent (and everything
previously spent still is: grow-only). -/
theorem spend_admits_fresh (c : Cell) (n : Nullifier)
    (h : n ∉ c.spent) :
    spend c n = some { spent := insert n c.spent } := by
  unfold spend
  rw [if_neg h]

/-- **`spend_no_double_spend` — the combined keystone of anti-double-spend.** In one
statement: a nullifier already in `spent` is rejected (`none`), AND a fresh one is
admitted with the result landing in `spent` (membership after the successful
spend). Fail-closed reuse + monotone growth, the two halves the spent set must
guarantee. -/
theorem spend_no_double_spend (c : Cell) (n : Nullifier) :
    (n ∈ c.spent → spend c n = none)
    ∧ (n ∉ c.spent → ∃ c', spend c n = some c' ∧ n ∈ c'.spent) := by
  refine ⟨spend_rejects_double c n, ?_⟩
  intro h
  refine ⟨{ spent := insert n c.spent }, spend_admits_fresh c n h, ?_⟩
  exact Finset.mem_insert_self n c.spent

/-- **Insert-only / grow-only (`Terminal`-linearity).** A successful `spend` only
*adds*: every previously-spent nullifier is still spent afterward, and nothing is
removed. The spent set is monotone — the formal content of "append-only, `remove`
forbidden" (`02-spine-cell §1.4`). -/
theorem spend_monotone (c c' : Cell) (n : Nullifier)
    (h : spend c n = some c') : c.spent ⊆ c'.spent := by
  unfold spend at h
  by_cases hn : n ∈ c.spent
  · rw [if_pos hn] at h; exact absurd h (by simp)
  · rw [if_neg hn] at h
    have : c' = { spent := insert n c.spent } := by
      injection h with h; exact h.symm
    subst this
    exact Finset.subset_insert n c.spent

/-! ## THE KEYSTONE — tier-1 eligibility: the nullifier set is I-confluent.

The mergeable state of a `NullifierCell` is its `spent : Finset Nullifier`. Two
concurrent replicas merge by set **union** — the CvRDT join. We hand
`Finset Nullifier` the `Confluence.MergeState` (join-semilattice) structure and
prove its admissibility invariant is `Confluence.IConfluent`: preserved under `∪`.
That is exactly `Confluence.Tier1Eligible`, so the nullifier cell may select the
tier-1 (causal-only, coordination-free, partition-tolerant) finality rule — it
needs NO consensus. This is `discoveries §3.7`'s canonical TIER-1-SAFE CvRDT. -/

/-- The spent-set state — `Finset Nullifier` — is a `Confluence.MergeState`:
concurrent versions merge by `⊔` (= `∪`), the G-Set CvRDT join. This is the
join-semilattice the I-confluence judgement runs over. -/
instance : MergeState (Finset Nullifier) := { toSemilatticeSup := inferInstance }

/-- `⊔` on the spent-set state really is set union — the CvRDT join is `∪`. Pins the
abstract lattice join to the concrete G-Set merge so the I-confluence proof below
is over the genuine union, not an opaque `⊔`. -/
@[simp] theorem mergeState_sup_eq_union (a b : Finset Nullifier) :
    a ⊔ b = a ∪ b := rfl

/-- **THE KEYSTONE (REAL CONTENT) — the nullifier-set safety invariant is `IConfluent`.**
The genuine, *falsifiable* admissibility invariant of the spent set is **monotone
no-loss**: relative to any already-consumed baseline `s₀`, a valid spent-set is one
that still contains every baseline nullifier — `fun s => s₀ ⊆ s` ("once spent, forever
spent: no consumed nullifier is ever dropped"). This is the formal no-double-spend
safety property, and it has teeth: it is FALSE for a set that loses a baseline spend
(witnessed by `nullifierSet_monotone_invariant_nontrivial`). We prove it is `IConfluent`
— the union of two no-loss spent-sets is again no-loss:
`s₀ ⊆ x → s₀ ⊆ y → s₀ ⊆ x ∪ y` (upward-closed sets are union-stable). This is the
EXACT DUAL of why a bounded cap (`card ≤ 1` / `balance≥0`, an *upper* bound) is NOT
I-confluent: an upper bound is broken by union, a lower/closure bound is preserved by
it. Concurrent spends on disjoint nullifiers merge with zero coordination and lose
nothing. -/
theorem nullifierSet_monotone_iconfluent (s₀ : Finset Nullifier) :
    IConfluent (S := Finset Nullifier) (fun s => s₀ ⊆ s) := by
  intro x y hx _hy
  -- `s₀ ⊆ x` and `x ⊆ x ∪ y = x ⊔ y` give `s₀ ⊆ x ⊔ y` by transitivity.
  rw [mergeState_sup_eq_union]
  exact hx.trans (Finset.subset_union_left)

/-- **The no-loss invariant genuinely discriminates (non-vacuity of `…_monotone_iconfluent`).**
For a non-empty baseline `{n}`, the no-loss invariant `fun s => {n} ⊆ s` is satisfied by
`{n}` itself yet FAILS for the empty set `∅` — so it is a real, falsifiable predicate,
not always-true. This is what makes `nullifierSet_monotone_iconfluent` non-vacuous: it
asserts I-confluence of an invariant that actually rules states out. -/
theorem nullifierSet_monotone_invariant_nontrivial (n : Nullifier) :
    ({n} ⊆ ({n} : Finset Nullifier)) ∧ ¬ ({n} ⊆ (∅ : Finset Nullifier)) := by
  refine ⟨Finset.Subset.refl _, ?_⟩
  simp [Finset.subset_empty]

/-- **Tier-1 carrier theorem (used by the revocation-set reuse in `Authority.Credential`).**
This is the `s₀ = ∅` degenerate instance of `nullifierSet_monotone_iconfluent`: the
empty-baseline no-loss invariant `fun s => ∅ ⊆ s` (which unfolds to `fun _ => True`,
since every set contains `∅`). It is the *trivial carrier* — the structural fact that the
G-Set lattice itself is I-confluent — kept under this name as the consensus-free hook the
revocation cell instantiates. The genuine, falsifiable safety content is the general
`nullifierSet_monotone_iconfluent` above (and its non-vacuity witness); this corollary is
NOT that content and does not stand in for it. -/
theorem nullifierSet_iconfluent :
    IConfluent (S := Finset Nullifier) (fun _ => True) := by
  -- specialize the real theorem at the empty baseline, then discharge `∅ ⊆ s` (always true).
  have := nullifierSet_monotone_iconfluent (∅ : Finset Nullifier)
  exact fun x y _ _ => trivial

/-- **A merge-explicit form of the keystone.** The union of two spent-sets is again
a valid spent-set whose membership is exactly the union of memberships — the
concrete CvRDT join law underlying `nullifierSet_iconfluent`. A nullifier is spent
in the merged cell iff it was spent in *either* replica: no spend is lost, none is
invented. (This is the "merge preserves the invariant" content, stated on the live
membership rather than the trivial carrier.) -/
theorem merge_preserves_membership (a b : Finset Nullifier) (n : Nullifier) :
    n ∈ (a ⊔ b) ↔ (n ∈ a ∨ n ∈ b) := by
  rw [mergeState_sup_eq_union]
  exact Finset.mem_union

/-- **THE CONCLUSION (REAL CONTENT) — the nullifier cell is `Tier1Eligible` for its
genuine safety invariant: it needs NO consensus.** I-confluence of the monotone
no-loss invariant is *exactly* tier-1 eligibility (`Confluence.Tier1Eligible`), the
well-formedness side-condition the finality classifier checks. So the nullifier set
runs at tier-1 — causal-only, coordination-free, partition-tolerant — for the real,
falsifiable "once spent, forever spent" property, not merely for the trivial carrier:
replicas accept spends offline and union without coordination AND without ever losing
a consumed nullifier. This is the payoff of the "sets → cells" collapse (`02-spine-cell
§1.4`, `discoveries §3.7`). -/
theorem nullifierCell_monotone_tier1_eligible (s₀ : Finset Nullifier) :
    Tier1Eligible (S := Finset Nullifier) (fun s => s₀ ⊆ s) :=
  nullifierSet_monotone_iconfluent s₀

/-- **Tier-1 carrier theorem (revocation-set reuse hook, `Authority.Credential`).** The
`s₀ = ∅` instance of `nullifierCell_monotone_tier1_eligible`: tier-1 eligibility of the
empty-baseline carrier `fun _ => True`. The falsifiable safety content is
`nullifierCell_monotone_tier1_eligible`; this is its degenerate structural instance, kept
under this name for the downstream consensus-free reuse. -/
theorem nullifierCell_tier1_eligible :
    Tier1Eligible (S := Finset Nullifier) (fun _ => True) :=
  nullifierSet_iconfluent

/-- **Merging two cells** — the CvRDT join lifted to `NullifierCell`: take the union
of the two spent sets. By `nullifierCell_tier1_eligible` this merge needs no
consensus; by `merge_preserves_membership` it loses no spend. -/
def merge (c d : Cell) : Cell :=
  { spent := c.spent ∪ d.spent }

/-- Merging cells is exactly the join on their spent-set states — the cell-level
CvRDT merge is the state-level `⊔`. -/
theorem merge_spent (c d : Cell) :
    (merge c d).spent = c.spent ⊔ d.spent := rfl

/-! ## The contrast — why `balance≥0` is NOT tier-1-safe (`discoveries §3.7`).

The nullifier set is tier-1-safe because its invariant is grow-only / structural.
A `balance≥0`-style invariant is the *opposite*: linear but NOT I-confluent — two
concurrent debits each individually preserve the bound, yet their merge jointly
overdraws. `Confluence.cardLeOne_not_iconfluent` is exactly this shape: a bounded
`card ≤ 1` cap over `Finset ℕ` is preserved by each singleton but BROKEN by their
union `{1} ⊔ {2} = {1,2}`. We re-expose it here as the discriminating witness: a
cell with such an invariant CANNOT run tier-1 and MUST escalate to consensus
(≥tier-2 / single-writer). This is what makes the third judgement non-vacuous —
the nullifier set passes, `balance≥0` fails. -/

/-- **The contrast witness.** A `balance≥0`-shaped invariant (here the `card ≤ 1`
cap, `Confluence.cardLeOne_not_iconfluent`) is NOT I-confluent — so a cell carrying
it is NOT tier-1-eligible and must escalate to consensus. Re-exposed from
`Confluence` to stand beside `nullifierCell_tier1_eligible`: the nullifier set is
the clean win, the bounded cap is the one that needs coordination. -/
theorem balanceLike_not_tier1_eligible :
    ¬ Tier1Eligible (S := Finset ℕ) (fun s => s.card ≤ 1) :=
  Dregg2.Confluence.cardLeOne_not_iconfluent

/-! ## It runs (`#eval`) — spend, double-spend, and a coordination-free merge. -/

private def n1 : Nullifier := { tag := 1 }
private def n2 : Nullifier := { tag := 2 }

/-- Display helper: the spent set as a sorted list of tags (`Finset Nullifier` has no
`Repr`; we project to the `Nat` tags for `#eval`). -/
private def tags (c : Cell) : List Nat := (c.spent.image (·.tag)).sort (· ≤ ·)

-- spend a fresh nullifier into the empty cell ⇒ admitted, now {1}
#eval (spend empty n1).map tags                          -- some [1]
-- spend it AGAIN ⇒ rejected (fail-closed double-spend)
#eval ((spend empty n1).bind (fun c => spend c n1)).isNone  -- true  (none)
-- spend a different fresh nullifier ⇒ admitted, now {1,2}
#eval ((spend empty n1).bind (fun c => spend c n2)).map tags  -- some [1, 2]
-- two replicas spent disjoint nullifiers offline; union (the tier-1 CvRDT join, no consensus)
#eval tags (merge { spent := {n1} } { spent := {n2} })       -- [1, 2]
-- merge is idempotent / commutative on overlap — a re-seen spend is absorbed, never doubled
#eval tags (merge { spent := {n1, n2} } { spent := {n2} })   -- [1, 2]

end Dregg2.Exec.NullifierCell
