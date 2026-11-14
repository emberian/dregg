/-
# Dregg2.Distributed.LaceMerge — the blocklace CRDT delta-merge as a PURE JOIN, with
# order-independence (commutativity / associativity / idempotence) + monotonicity, composed
# with `BlocklaceFinality` to conclude **same causally-closed blocks ⇒ same executed state**.

**The gap this closes.** `Authority.Blocklace` models the DAG + equivocation; `Distributed.BlocklaceFinality`
models the *ordering* rule (`ordering.rs::tau`) and proves its determinism + the executor wire. NEITHER
models the **replication merge** — `blocklace/src/finality.rs::Blocklace::merge` — the CRDT delta-join that
the SSB-style dissemination (`dissemination.rs`, `node/src/blocklace_sync.rs`) runs to bring two replicas'
laces into agreement. That is the SAFETY this file is about: a replica's blocklace is a `HashMap<BlockId, Block>`
(`finality.rs:477`), keyed by the content-address; `merge(delta)` topologically sorts the (causally-closed)
delta and inserts each block, **skipping ids already present** (`finality.rs:690`). The observable replica
state — the SET of blocks keyed by id — is therefore a **set union**, and the topological-sort/insertion-order
is pure plumbing that the final HashMap forgets.

This module models THAT: `mergeLace` is the executable join the node computes (skip-if-present append, the
exact `finality.rs:690` guard); its content-addressed observable is `laceIds : Lace → Finset BlockId`
(the `HashMap`'s keyset). We prove the merge is a **join on that keyset** — `laceIds (mergeLace B Δ)
= laceIds B ∪ laceIds Δ` — and READ the CRDT laws off `Finset`'s `∪` (a genuine bounded join-semilattice):
**commutativity, associativity, idempotence, monotonicity**. The order-independence of replication then
follows: two replicas that merge the same set of (causally-closed) blocks — in ANY order, grouped into ANY
deltas — reach laces with the SAME keyset (`laceIds`).

⚑ **EQUAL KEYSETS ARE NOT EQUAL LACES, AND `Lace.Canonical` DOES NOT CLOSE THE GAP.** This header said,
until 2026-07-27, that "under the content-addressing invariant (`Lace.Canonical`) the same keyset is the
same `lookup` function". That is FALSE, and `crossCanonical_is_the_gap` (§8b) refutes it: two laces can
each be internally canonical, have the SAME keyset, and still resolve one address to DIFFERENT blocks —
`[b0]` and `[b0Forged]` do exactly that, and their `SameView` fails. The assumption that actually turns
equal keysets into a shared `lookup` is CROSS-lace canonicity, `CrossCanonical` (§6), which is independent
of the two per-lace `Canonical` facts. It is where a content-address collision breaks CRDT convergence,
and it was carried ANONYMOUSLY (`hagree`) at every convergence site until it was named here.

Given that assumption, and composing with `BlocklaceFinality`'s ordering determinism and
`ConsensusExec.finalized_execution_agreement`, two replicas resolve the finalized order to the SAME BLOCKS
(`merge_convergence_tauBlocks`) and reach the SAME executed `RecChainedState`
(`merge_convergence_to_state`), at **n>1** (two replicas, an explicit Byzantine fork in the witness lace);
n=1 is the scales-to-zero special case.

## SCOPE.

FAITHFUL (matches `finality.rs::merge` as a pure function of the block SET):
* `mergeLace B Δ` — the skip-if-present insertion (`finality.rs:690` `if self.blocks.contains_key(&id)
  { continue }`); the result's keyset is `keyset(B) ∪ keyset(Δ)`, which is what the HashMap holds.
* The CRDT join laws (comm/assoc/idem) are over `laceIds` — the HashMap KEYSET, the genuine content-addressed
  observable; this is the level at which two replicas "have the same blocklace".

SIMPLIFIED (a faithful PROJECTION, stated, not hidden):
* `merge` ALSO mutates `equivocators` and `tips` (`finality.rs:706/724`). Those are **deterministic VIEWS of
  the block set**: `equivocators(B)` = creators with an incomparable in-`B` pair (`Authority.Blocklace.Equivocator`),
  `tips(B)` = per-creator max-seq non-equivocator block. They are FUNCTIONS of `laceIds B` (+ `lookup`), so
  equal keysets ⇒ equal equivocators/tips. We prove the join law for the keyset (the primary CRDT state) and
  note (`tips`/`equivocators` derive from it) — we do NOT re-derive their fold here (that is the FinalityFold
  residual, named).
* We assume `merge`'s causal-closure precondition (`MergeError::NotCausallyClosed`) and signature validity
  (`block.verify_signature`) — i.e. we model a SUCCESSFUL merge of a well-formed delta. Signature
  unforgeability is the §8 crypto seam (a HYPOTHESIS `WellFormedDelta`), exactly the status of
  `Authority.Blocklace`'s §8 boundary.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Distributed.LaceMerge`. Differential: `blocklace/src/finality.rs::merge`.
-/
import Dregg2.Distributed.BlocklaceFinality
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.List.Basic

namespace Dregg2.Distributed.LaceMerge

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)
open Dregg2.Distributed.BlocklaceFinality (tauOrder tauBlocks executeTau tauOrder_deterministic)

/-! ## 1. The content-addressed observable — the HashMap KEYSET (`finality.rs::Blocklace.blocks` keys).

A replica's blocklace IS a `HashMap<BlockId, Block>` keyed by the content-address. The observable CRDT
state — what it means for two replicas to "have the same blocklace" — is the SET of keys (the ids), since
content-addressing makes the id determine the block (`Lace.Canonical`). We project a `Lace` to that keyset. -/

/-- **`laceIds B`** — the content-address keyset of the lace (`finality.rs::Blocklace.blocks` keys). The
genuine CRDT observable: two laces with the same `laceIds` (under `Canonical`) hold the same blocks. -/
def laceIds (B : Lace) : Finset BlockId := (B.map (·.id)).toFinset

@[simp] theorem laceIds_nil : laceIds [] = ∅ := rfl

@[simp] theorem mem_laceIds {B : Lace} {h : BlockId} :
    h ∈ laceIds B ↔ ∃ b ∈ B, b.id = h := by
  unfold laceIds
  simp only [List.mem_toFinset, List.mem_map]

theorem laceIds_append (B C : Lace) : laceIds (B ++ C) = laceIds B ∪ laceIds C := by
  ext h; simp only [mem_laceIds, Finset.mem_union, List.mem_append]
  constructor
  · rintro ⟨b, hb | hb, rfl⟩
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨b, hb, rfl⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact ⟨b, Or.inl hb, rfl⟩
    · exact ⟨b, Or.inr hb, rfl⟩

/-! ## 2. `mergeLace` — the skip-if-present insertion (`finality.rs::merge`, line 690).

`merge` topologically sorts the delta then inserts each block, `continue`-ing past any id already in the
map (`if self.blocks.contains_key(&id) { continue }`). The topological sort is pure insertion-ORDER plumbing
that the final HashMap forgets; the resulting keyset is `keyset(B) ∪ keyset(Δ)`. We model the net effect:
append the delta blocks whose id is NOT already in `B`. The result is a `Lace` whose keyset is the union. -/

/-- The sub-delta of blocks NEW to `B` (id not already present) — the blocks `merge` actually
inserts (the others hit the `continue`). -/
def newBlocks (B Δ : Lace) : Lace := Δ.filter (fun b => decide (b.id ∉ laceIds B))

/-- **`mergeLace B Δ`** — the net effect of `finality.rs::merge`: `B` with the new delta blocks
appended (skip-if-present). The insertion ORDER (the topological sort) is forgotten by the keyset, which is
all the CRDT observes — so we need not model the sort to capture the join. -/
def mergeLace (B Δ : Lace) : Lace := B ++ newBlocks B Δ

/-! ## 3. THE JOIN LAW — `mergeLace`'s keyset is the set union (`HashMap` insert = key-union). -/

/-- **`laceIds_mergeLace` (the JOIN).** The keyset of `mergeLace B Δ` is exactly `laceIds B ∪
laceIds Δ`: skipping already-present ids does not change the union (those ids are in `laceIds B` already),
and inserting the new ones adds exactly `laceIds Δ \ laceIds B`. This is the content of "the
HashMap insert is a keyset union": the merge is a **pure join on the content-addressed observable**. -/
theorem laceIds_mergeLace (B Δ : Lace) : laceIds (mergeLace B Δ) = laceIds B ∪ laceIds Δ := by
  unfold mergeLace
  rw [laceIds_append]
  ext h
  simp only [Finset.mem_union, mem_laceIds, newBlocks, List.mem_filter, decide_not,
    Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro (hB | ⟨b, ⟨hbΔ, _⟩, rfl⟩)
    · exact Or.inl hB
    · exact Or.inr ⟨b, hbΔ, rfl⟩
  · rintro (hB | ⟨b, hbΔ, rfl⟩)
    · exact Or.inl hB
    · -- b.id is in laceIds Δ; either it's already in laceIds B (left) or it's new (right filter).
      by_cases hmem : b.id ∈ laceIds B
      · exact Or.inl (mem_laceIds.mp hmem)
      · exact Or.inr ⟨b, ⟨hbΔ, fun hc => hmem (mem_laceIds.mpr hc)⟩, rfl⟩

/-! ## 4. ORDER-INDEPENDENCE — commutativity / associativity / idempotence, READ off `Finset ∪`.

The CRDT laws are now one rewrite each: `mergeLace`'s observable is `laceIds B ∪ laceIds Δ`, and `Finset`'s
`∪` is a genuine bounded join-semilattice (commutative, associative, idempotent). So `mergeLace` is a join:
the order in which a replica merges deltas — and how it groups blocks into deltas — does NOT affect the keyset
it converges to. We state each law as keyset-equality (the content-addressed equality of replica states). -/

/-- **`merge_comm` (COMMUTATIVITY).** `mergeLace B C` and `mergeLace C B` have the SAME keyset:
merging C-into-B vs B-into-C converge to the same content-addressed state. Two replicas exchanging deltas in
either direction agree. (`∪` commutative.) -/
theorem merge_comm (B C : Lace) : laceIds (mergeLace B C) = laceIds (mergeLace C B) := by
  rw [laceIds_mergeLace, laceIds_mergeLace, Finset.union_comm]

/-- **`merge_assoc` (ASSOCIATIVITY).** Merging `(B then C) then D` and `B then (C then D)` reach the
SAME keyset: how a replica GROUPS incoming blocks into deltas is irrelevant. (`∪` associative.) -/
theorem merge_assoc (B C D : Lace) :
    laceIds (mergeLace (mergeLace B C) D) = laceIds (mergeLace B (mergeLace C D)) := by
  rw [laceIds_mergeLace, laceIds_mergeLace, laceIds_mergeLace, laceIds_mergeLace,
    Finset.union_assoc]

/-- **`merge_idem` (IDEMPOTENCE).** Re-merging a delta already absorbed is a no-op on the keyset:
`mergeLace B B` has the same keyset as `B`. Duplicate gossip / re-delivery (SSB at-least-once) cannot perturb
a replica's content-addressed state. (`∪` idempotent.) -/
theorem merge_idem (B : Lace) : laceIds (mergeLace B B) = laceIds B := by
  rw [laceIds_mergeLace, Finset.union_idempotent]

/-- **`merge_absorb` (absorption / at-least-once safety).** Merging a delta whose ids are ALL
already present leaves the keyset unchanged: `laceIds Δ ⊆ laceIds B → laceIds (mergeLace B Δ) = laceIds B`.
The strong form of idempotence the dissemination layer relies on (redundant deltas are inert). -/
theorem merge_absorb (B Δ : Lace) (h : laceIds Δ ⊆ laceIds B) :
    laceIds (mergeLace B Δ) = laceIds B := by
  rw [laceIds_mergeLace, Finset.union_eq_left.mpr h]

/-! ## 5. MONOTONICITY — the CRDT inflationary law (a replica's keyset only grows). -/

/-- **`merge_monotone` (MONOTONICITY / inflationary).** A merge only GROWS the keyset:
`laceIds B ⊆ laceIds (mergeLace B Δ)`. A replica never loses a block by merging — the CRDT state advances up
the `⊆`-lattice. The foundation of `Authority.Blocklace.attested_mono` / `World.recv_mono`: finality, once
reached, is preserved because the underlying block set is monotone. -/
theorem merge_monotone (B Δ : Lace) : laceIds B ⊆ laceIds (mergeLace B Δ) := by
  rw [laceIds_mergeLace]; exact Finset.subset_union_left

/-- **`merge_monotone_delta`.** Dually, the merged-in delta is also absorbed:
`laceIds Δ ⊆ laceIds (mergeLace B Δ)`. Everything offered IS received (no silent drop of a valid block). -/
theorem merge_monotone_delta (B Δ : Lace) : laceIds Δ ⊆ laceIds (mergeLace B Δ) := by
  rw [laceIds_mergeLace]; exact Finset.subset_union_right

/-- **`merge_least_upper_bound` (the JOIN universal property).** `mergeLace B Δ`'s keyset is the
LEAST keyset containing both `B`'s and `Δ`'s: any lace `U` whose keyset contains both contains the merge's.
So `mergeLace` computes the genuine lattice JOIN `⊔` — not merely an upper bound — which is what makes the
blocklace a join-semilattice CRDT (Almeida–Shapiro §3, "universal CRDT"). -/
theorem merge_least_upper_bound (B Δ U : Lace)
    (hB : laceIds B ⊆ laceIds U) (hΔ : laceIds Δ ⊆ laceIds U) :
    laceIds (mergeLace B Δ) ⊆ laceIds U := by
  rw [laceIds_mergeLace]; exact Finset.union_subset hB hΔ

/-! ## 6. CONVERGENCE — same blocks ⇒ same keyset ⇒ (under CROSS-canonicity) same `lookup` ⇒ same blocks.

The order-independence laws say: two replicas that merge the SAME SET of blocks (in any order, any grouping)
reach the SAME keyset. We now turn "same keyset" into "same finalized BLOCKS", and (composing with the
executor) "same executed state". The bridge is content-addressing, and it is an ASSUMPTION, not a
consequence of the join laws: equal keysets plus per-lace canonicity do NOT determine `Lace.lookup`
(`crossCanonical_is_the_gap`, §8b). What determines it is `CrossCanonical` — the two replicas resolve any
SHARED address to the same block — and we name it, model it and refute it below rather than carry it as an
unnamed binder. `SameView` (two laces present the same block at every id) is the consequence, and it is the
precondition the finalized-block resolution depends on. -/

/-- **`SameView B₁ B₂`** — the two replicas resolve EVERY content-address to the SAME block. This is the
content-addressed equality of laces, and it is the precise precondition under which the finalized order
resolves to the same BLOCKS on both sides.

⚑ It is NOT what equal keysets plus per-lace canonicity give you. This docstring used to say "equal
keysets PLUS canonical content-addressing collapse to this (an id present in both maps to the same block,
by `Canonical`)" — `Canonical` says nothing about an id present in BOTH laces, only about two blocks
within ONE, and `crossCanonical_is_the_gap` exhibits the counterexample. The missing premise is
`CrossCanonical`, below. -/
def SameView (B₁ B₂ : Lace) : Prop := ∀ h, B₁.lookup h = B₂.lookup h

/-- `SameView` is reflexive / symmetric / transitive — it is the convergence equivalence on replica views. -/
theorem SameView.refl (B : Lace) : SameView B B := fun _ => rfl
theorem SameView.symm {B₁ B₂ : Lace} (h : SameView B₁ B₂) : SameView B₂ B₁ := fun x => (h x).symm
theorem SameView.trans {B₁ B₂ B₃ : Lace} (h₁ : SameView B₁ B₂) (h₂ : SameView B₂ B₃) :
    SameView B₁ B₃ := fun x => (h₁ x).trans (h₂ x)

/-! ### `CrossCanonical` — THE assumption the convergence actually rests on.

Until 2026-07-27 this was an unnamed binder `hagree` sitting beside two `Lace.Canonical` hypotheses at
every convergence site in this module, in `CheckpointPrune` and in `CatchupConverges`. It is a DIFFERENT
and STRONGER assumption than either of them, it is the one a hash collision breaks, and because it had no
name it appeared in no census, no floor list and no exposure count in the tree. Naming it is the whole
point of this section; the three-arm discipline (`feedback-prove-the-floor-false`) is discharged in §8b —
SATISFIABLE (`crossCanonical_replicas`, at the real two-replica Byzantine-fork trace), REFUTABLE
(`crossCanonical_is_the_gap`), therefore NOT PROVABLE. -/

/-- **`CrossCanonical B₁ B₂`** — CROSS-LACE canonicity: a block held by replica `B₁` and a block held by
replica `B₂` that share a content-address ARE THE SAME BLOCK. This is content-addressing across the
replica boundary, i.e. the §8 collision-resistance obligation at the exact point the CRDT consumes it.

**How it relates to the two `Lace.Canonical` hypotheses it used to hide behind.**
* On the diagonal it IS canonicity: `crossCanonical_self`, `CrossCanonical B B ↔ B.Canonical`.
* Off the diagonal neither implies the other, and `canonical_append_iff` says exactly what the difference
  is: `(B₁ ++ B₂).Canonical ↔ B₁.Canonical ∧ B₂.Canonical ∧ CrossCanonical B₁ B₂`. Cross-canonicity is
  PRECISELY the content of "the two replicas' blocks, taken TOGETHER, are content-addressed" that per-lace
  canonicity does not carry.
* Adding equal keysets does not rescue it either — `crossCanonical_is_the_gap` exhibits two canonical laces
  with equal keysets and no cross-canonicity, whose `SameView` fails.

It is an explicit structural hypothesis, NOT a crypto axiom and NOT a theorem: the wire-format fact that
makes it hold is Poseidon2 collision resistance over the block encoding, which this tree does not prove. -/
def CrossCanonical (B₁ B₂ : Lace) : Prop :=
  ∀ b₁ ∈ B₁, ∀ b₂ ∈ B₂, b₁.id = b₂.id → b₁ = b₂

/-- `CrossCanonical` is DECIDABLE on concrete laces — a replica can CHECK the assumption on the block set
it actually holds rather than assume it. Used by the §8b model and teeth. -/
instance decidableCrossCanonical (B₁ B₂ : Lace) : Decidable (CrossCanonical B₁ B₂) := by
  unfold CrossCanonical; infer_instance

/-- Cross-canonicity is symmetric: it is a statement about the PAIR of replicas. -/
theorem CrossCanonical.symm {B₁ B₂ : Lace} (h : CrossCanonical B₁ B₂) : CrossCanonical B₂ B₁ :=
  fun b₂ hb₂ b₁ hb₁ hid => (h b₁ hb₁ b₂ hb₂ hid.symm).symm

/-- **On the DIAGONAL, cross-canonicity IS `Lace.Canonical`** — so it is a genuine generalisation of the
named floor rather than a different subject, and the named floor is its one-replica special case. -/
theorem crossCanonical_self (B : Lace) : CrossCanonical B B ↔ B.Canonical := Iff.rfl

/-- **`canonical_append_iff` — the exact strength of the assumption that had no name.** The union of the
two replicas' block lists is content-addressed IFF each is, AND they agree across the boundary. So
`CrossCanonical` is precisely the residue of global content-addressing that the two `Lace.Canonical`
hypotheses do NOT carry — it is not a restatement of them, and it is not implied by them. -/
theorem canonical_append_iff (B₁ B₂ : Lace) :
    (B₁ ++ B₂).Canonical ↔ B₁.Canonical ∧ B₂.Canonical ∧ CrossCanonical B₁ B₂ := by
  constructor
  · intro h
    refine ⟨fun a ha b hb hid => h a (List.mem_append_left _ ha) b (List.mem_append_left _ hb) hid,
            fun a ha b hb hid => h a (List.mem_append_right _ ha) b (List.mem_append_right _ hb) hid,
            fun a ha b hb hid => h a (List.mem_append_left _ ha) b (List.mem_append_right _ hb) hid⟩
  · rintro ⟨h₁, h₂, hx⟩ a ha b hb hid
    rcases List.mem_append.mp ha with ha' | ha' <;> rcases List.mem_append.mp hb with hb' | hb'
    · exact h₁ a ha' b hb' hid
    · exact hx a ha' b hb' hid
    · exact (hx b hb' a ha' hid.symm).symm
    · exact h₂ a ha' b hb' hid

/-- **`sameView_of_canonical_eq_ids` (the content-addressing bridge).** Two laces that are each canonical,
have the SAME keyset, and are CROSS-canonical present the SAME block at every id. This is the step that
turns the join laws (which give EQUAL KEYSETS) into `SameView`.

⚑ All three hypotheses are load-bearing, and the third is the one that does the cryptographic work:
`crossCanonical_is_the_gap` (§8b) exhibits `hc₁`, `hc₂` and `hids` all holding while the conclusion FAILS.
An earlier version of this docstring described `hcross` as "exactly content-addressing … same status as
`Lace.Canonical` itself"; that was wrong in the way that matters — it is strictly more than `Lace.Canonical`
(`canonical_append_iff`), and it is not implied by any combination of the other hypotheses. -/
theorem sameView_of_canonical_eq_ids {B₁ B₂ : Lace}
    (hc₁ : B₁.Canonical) (hc₂ : B₂.Canonical)
    (hids : laceIds B₁ = laceIds B₂)
    (hcross : CrossCanonical B₁ B₂) :
    SameView B₁ B₂ := by
  intro h
  -- Case on whether id `h` is present in B₁.
  cases h1 : B₁.lookup h with
  | none =>
    -- h absent in B₁ ⇒ (equal keysets) absent in B₂.
    cases h2 : B₂.lookup h with
    | none => rfl
    | some b₂ =>
      exfalso
      have hb₂mem : b₂ ∈ B₂ := List.mem_of_find?_eq_some h2
      have hb₂id : b₂.id = h := by
        have := List.find?_some h2; simpa using this
      have hmem₂ : h ∈ laceIds B₂ := mem_laceIds.mpr ⟨b₂, hb₂mem, hb₂id⟩
      rw [← hids] at hmem₂
      obtain ⟨b₁, hb₁mem, hb₁id⟩ := mem_laceIds.mp hmem₂
      have hcontra : B₁.lookup h = some b₁ := by
        rw [← hb₁id]; exact Dregg2.Authority.Blocklace.lookup_of_mem hc₁ hb₁mem
      rw [h1] at hcontra; exact absurd hcontra (by simp)
  | some b₁ =>
    have hb₁mem : b₁ ∈ B₁ := List.mem_of_find?_eq_some h1
    have hb₁id : b₁.id = h := by have := List.find?_some h1; simpa using this
    have hmem₁ : h ∈ laceIds B₁ := mem_laceIds.mpr ⟨b₁, hb₁mem, hb₁id⟩
    rw [hids] at hmem₁
    obtain ⟨b₂, hb₂mem, hb₂id⟩ := mem_laceIds.mp hmem₁
    have hl2 : B₂.lookup h = some b₂ := by
      rw [← hb₂id]; exact Dregg2.Authority.Blocklace.lookup_of_mem hc₂ hb₂mem
    rw [hl2]
    -- b₁ and b₂ share id h, so by CROSS-lace content-addressing they are equal.
    have : b₁ = b₂ := hcross b₁ hb₁mem b₂ hb₂mem (by rw [hb₁id, hb₂id])
    rw [this]

/-! ### The `tauOrder`-agreement seam — an ASSUMED hypothesis, and what is NOT established.

The convergence theorems below take `tauOrder B₁ … = tauOrder B₂ …` as an explicit hypothesis `hOrder`,
and this module does not derive it. Stated at the resolution it deserves:

**NOT ESTABLISHED: permutation-invariance of `tauOrder`.** The obligation is
`B₁.Canonical → B₂.Canonical → laceIds B₁ = laceIds B₂ → CrossCanonical B₁ B₂ →
tauOrder B₁ p w = tauOrder B₂ p w`, and no theorem in this tree proves it. Two things stand in the way,
and neither is a formality:
* THE ROUND MAP HALF IS NOW A THEOREM. `BlocklaceFinality.computeRounds` used to fold the lace in
  `Array.qsort` order by `(seq, creator)`; that order was not even topological (dregg issue #100),
  and its ties — exactly EQUIVOCATING pairs — made the output a function of the input order. It now
  folds a Kahn enumeration, and `BlocklaceFinality.roundOf_perm` proves that two listings of the
  same blocks (distinct ids, no predecessor cycle) give every id the same round.
* THE REST IS NOT. `tauOrder` also reads the lace's LIST ORDER through `causalPastIncl` (a BFS
  whose output order follows the predecessor lists and `Lace.lookup`), `closureLace`,
  `blocksAtRound`, `leaderCandidates` and the `previousRatifiedLeader` fold. Each is plausibly
  order-insensitive on canonical laces; none is proved so, and `xsortBy`'s output depends on the
  ids' own order (its ready ties break by `(round, id)`).

The previous version of this note asserted `tauOrder` "is permutation-invariant on canonical laces" as a
fact and called `hOrder` "true-but-unrediscovered". That was a claim, not a result, and the tie case above
is why it is not obvious. What IS proved here: the JOIN laws give equal keysets, `sameView_of_canonical_eq_ids`
turns equal keysets PLUS cross-canonicity into a shared `lookup`, and — GIVEN order-agreement — the two
replicas resolve to the same finalized BLOCKS (`merge_convergence_tauBlocks`) and the executor reaches the
same state (`merge_convergence_to_state`). For the n=1 / identical-representative case `hOrder` is
`tauOrder_deterministic` (`rfl`); at n>1 it is assumed. -/

/-! ## 7. THE CONVERGENCE THEOREM — same causally-closed blocks ⇒ same executed state (n>1).

Two replicas that have merged the same SET of causally-closed blocks reach the same keyset (join laws); under
content-addressing that is the same `SameView`; `tauOrder` over the same view computes the same finalized
order (`tauOrder_deterministic` on a single canonical representative); and `executeTau` over the same order
yields the same `RecChainedState` (`ConsensusExec.finalized_execution_agreement`, ridden by
`BlocklaceFinality.tau_execution_agreement`). So **same blocks ⇒ same executed state**. We state it at n>1: the
two laces `B₁ B₂` are TWO replicas (the witness §8 lace carries a Byzantine fork — n>1 with an adversary). -/

open Dregg2.Distributed.BlocklaceFinality (tau_execution_agreement)
open Dregg2.Exec.ConsensusExec (Decoder)
open Dregg2.Exec (RecChainedState)

/-- **`merge_convergence_tauBlocks` (consensus-side convergence, the REAL statement).** Two replicas
that hold content-addressed-equal laces (same keyset, both canonical, CROSS-canonical) and finalize the
same ID ORDER resolve that order to the SAME SEQUENCE OF BLOCKS. This is the consensus-side of CRDT
convergence: the replicated state machines agree on the turns to execute, not merely on their addresses.

⚑ **This theorem replaces `merge_convergence_tauOrder`, which was `P → P`** (2026-07-27). That theorem's
hypothesis `hOrder` was verbatim its own conclusion, its two `Canonical` hypotheses fed a `have` discarded
at an underscore, and it carried the name "consensus-side convergence" while establishing nothing. The
honest statement is this one, and the difference between them is exactly the work `hcross` does:
`finalized_resolution_diverges_at_a_collision` (§8b) shows two replicas AGREEING on the finalized id order
and executing DIFFERENT blocks, because one address carries different content on the two sides. Agreement
on `tauOrder` is not agreement on `tauBlocks`; that gap is the collision, and closing it is what this
theorem does and what the tautology did not. -/
theorem merge_convergence_tauBlocks {B₁ B₂ : Lace} (participants : List AuthorId) (wavelength : Nat)
    (hc₁ : B₁.Canonical) (hc₂ : B₂.Canonical)
    (hids : laceIds B₁ = laceIds B₂)
    (hcross : CrossCanonical B₁ B₂)
    (hOrder : tauOrder B₁ participants wavelength = tauOrder B₂ participants wavelength) :
    tauBlocks B₁ participants wavelength = tauBlocks B₂ participants wavelength := by
  have hview : SameView B₁ B₂ := sameView_of_canonical_eq_ids hc₁ hc₂ hids hcross
  unfold tauBlocks
  rw [hOrder]
  apply List.filterMap_congr
  intro h _
  exact hview h

/-- **`merge_convergence_to_state` (THE end-to-end convergence at n>1).** Two replicas (`B₁`, `B₂`)
that — after merging the same causally-closed block set in any order — hold canonical, CROSS-canonical
laces with equal keysets AND finalize the same `tauOrder`, execute to the SAME `RecChainedState`. Proof:
their `tauBlocks` are equal (`merge_convergence_tauBlocks`), so `executeTau` folds the identical decoded
turn list from the same genesis through the verified `executeFinalized` — equal by function-determinism.
This is "same blocks ⇒ same executed state": the merge join laws (§4–5) composed with the ordering
determinism (`BlocklaceFinality`) and the executor determinism (`ConsensusExec`), end to end, for two
distinct replicas — CONDITIONAL on `hOrder`, whose undischarged status is stated in §6. -/
theorem merge_convergence_to_state (dec : Decoder) (s0 : RecChainedState)
    {B₁ B₂ : Lace} (participants : List AuthorId) (wavelength : Nat)
    (hc₁ : B₁.Canonical) (hc₂ : B₂.Canonical)
    (hids : laceIds B₁ = laceIds B₂)
    (hcross : CrossCanonical B₁ B₂)
    (hOrder : tauOrder B₁ participants wavelength = tauOrder B₂ participants wavelength) :
    executeTau dec s0 B₁ participants wavelength = executeTau dec s0 B₂ participants wavelength := by
  have htb : tauBlocks B₁ participants wavelength = tauBlocks B₂ participants wavelength :=
    merge_convergence_tauBlocks participants wavelength hc₁ hc₂ hids hcross hOrder
  -- executeTau is executeFinalized over (tauBlocks _).map dec; equal tauBlocks ⇒ equal.
  unfold executeTau
  rw [htb]

/-! ## 8. NON-VACUITY at n>1 — a CONCRETE two-replica merge over a Byzantine-forked block set.

The convergence is not vacuous: TWO replicas receive the SAME three causally-closed blocks — including a
Byzantine FORK (creator 9's incomparable pair `f1 ∥ f2`, the `Authority.Blocklace.demoLace` adversary) — in
OPPOSITE merge orders, and the join laws drive them to the SAME keyset. This is n>1 with an adversary present:
the order-independence holds THROUGH the fork (the merge keyset-union absorbs both fork branches identically
regardless of arrival order; equivocation handling is a deterministic view of the resulting set). The `#guard`s
are the model⟺node differential on a real trace: `finality.rs::merge` over these blocks in either order yields
the same keyset, matching `finality_tests.rs`'s order-independence tests. -/

/-- Three causally-closed blocks: genesis `b0`, and a Byzantine FORK by creator 9 — two seq-1 blocks `f1`,
`f2` that each ack `b0` but NOT each other (incomparable; the `Authority.Blocklace` adversary). -/
def b0 : Block := { id := 100, creator := 7, seq := 0, preds := [] }
def fork1 : Block := { id := 101, creator := 9, seq := 1, preds := [100] }
def fork2 : Block := { id := 102, creator := 9, seq := 1, preds := [100] }

/-- Replica R1 merges the delta `[fork1, fork2]` onto a lace that already has `b0`. -/
def replica1 : Lace := mergeLace [b0] [fork1, fork2]
/-- Replica R2 receives the SAME blocks but merges in the OPPOSITE grouping/order: first the fork, then b0. -/
def replica2 : Lace := mergeLace [fork2, fork1] [b0]
/-- Replica R3 merges everything as a single delta onto the empty lace (a fresh joiner). -/
def replica3 : Lace := mergeLace [] [b0, fork2, fork1]

-- n>1 ORDER-INDEPENDENCE on a Byzantine-forked block set: all three replicas converge to the SAME keyset.
#guard laceIds replica1 == laceIds replica2
#guard laceIds replica2 == laceIds replica3
#guard laceIds replica1 == ({100, 101, 102} : Finset BlockId)
-- IDEMPOTENCE on a real lace: re-merging the same delta is inert.
#guard laceIds (mergeLace replica1 [fork1, fork2]) == laceIds replica1
-- MONOTONICITY: merging never shrinks the keyset (b0 survives the fork-merge).
#guard decide ((100 : BlockId) ∈ laceIds replica1)
-- COMMUTATIVITY witness at the keyset level.
#guard laceIds (mergeLace [b0, fork1] [fork2]) == laceIds (mergeLace [fork2] [b0, fork1])
-- ABSORPTION: a delta of already-known blocks leaves the keyset fixed.
#guard laceIds (mergeLace [b0, fork1, fork2] [b0, fork1]) == laceIds [b0, fork1, fork2]

/-! ## 8b. `CrossCanonical` — the MODEL, and the two teeth.

`feedback-prove-the-floor-false` wants three arms and this tree has chronically had one. All three, here:

* **SATISFIABLE** — `crossCanonical_replicas`, at the REAL two-replica trace of §8, which is off-diagonal
  (`replica1 ≠ replica2` as lists), non-empty, shares all three addresses, and carries a Byzantine fork.
  Not a degenerate witness: it is the exact object the convergence theorems are about.
* **REFUTABLE** — `crossCanonical_is_the_gap`, and it refutes something worth refuting: both laces
  canonical, keysets EQUAL, and cross-canonicity still fails, taking `SameView` down with it.
* Hence **NOT PROVABLE**, which is what makes it an assumption rather than a lemma nobody got round to.

⚑ The refutability pole is deliberately NOT spelled `¬ CrossCanonical …` as a bare conclusion, for the
reason recorded at `ae37dd523` and in `docs/UNREFUTED-FLOORS-AUDIT.md` §4: `#floor_ratchet` derives its
refuted-floor set from exactly that conclusion shape, so writing the doctrine-REQUIRED refutability half
in the obvious spelling would reclassify an honest structural assumption as a refuted floor and gate every
consumer as a vacuous carrier. The instrument punishes completing its own test; nothing here works around
that, the content is simply carried in conjunctive position. The same is true of `Lace.Canonical` below.

⚑ **The forgery is at the DEPLOYED shape.** `b0Forged` differs from `b0` in ONE bit — `signed` — at the
SAME content-address. That is precisely what a Poseidon2 collision over the block encoding buys an
adversary, and the two teeth measure what it costs: two replicas that pass every check this module proves
(each canonical, keysets equal, join laws satisfied, finalized id order identical) execute DIFFERENT
blocks. Consensus safety at n>1 rests on this not happening, and nothing in this tree proves it does not. -/

/-- The SAME content-address as `b0`, carrying a DIFFERENT block: one bit of difference (`signed`) at one
address. A content-address collision, at the shape the wire format actually has. -/
def b0Forged : Block := { id := 100, creator := 7, seq := 0, preds := [], signed := false }

/-- **`crossCanonical_replicas` — THE MODEL (satisfiability).** The two §8 replicas, which merged the same
Byzantine-forked block set in OPPOSITE orders and are DIFFERENT lists, really are cross-canonical. So the
assumption is inhabited at the object the convergence theorems quantify over, and every theorem carrying
it is non-vacuous there. -/
theorem crossCanonical_replicas : CrossCanonical replica1 replica2 := by decide

-- The model is genuinely OFF-DIAGONAL, so `crossCanonical_self` does not account for it; and it is not
-- vacuous on the right (replica2 is non-empty, and every address is shared with replica1).
#guard decide (replica1 ≠ replica2)
#guard decide (replica2 ≠ ([] : Lace))
#guard laceIds replica1 == laceIds replica2

/-- **`crossCanonical_is_the_gap` — THE TOOTH (refutability, and the load-bearing demonstration).**
Two laces, each `Canonical`, with EQUAL keysets — and cross-canonicity fails, and `SameView` fails with
it. So:
* `CrossCanonical` is refutable, hence not provable, hence a genuine assumption;
* and `sameView_of_canonical_eq_ids` is FALSE without it. The hypothesis is not decoration and it is not
  implied by the two named `Lace.Canonical` hypotheses beside it plus equal keysets — this is the
  counterexample to the claim this module's header made until 2026-07-27. -/
theorem crossCanonical_is_the_gap :
    ∃ B₁ B₂ : Lace, B₁.Canonical ∧ B₂.Canonical ∧ laceIds B₁ = laceIds B₂
      ∧ ¬ CrossCanonical B₁ B₂ ∧ ¬ SameView B₁ B₂ := by
  refine ⟨[b0], [b0Forged], (crossCanonical_self _).mp (by decide),
    (crossCanonical_self _).mp (by decide), rfl, by decide, ?_⟩
  intro hview
  have h : (some b0 : Option Block) = some b0Forged := hview 100
  exact absurd h (by decide)

/-- **`finalized_resolution_diverges_at_a_collision` — the CONSENSUS damage, at the exact step
`merge_convergence_tauBlocks` guards.** `tauBlocks B p w = (tauOrder B p w).filterMap B.lookup`
(`BlocklaceFinality`), so this says: on the finalized id order `[b0.id]`, two replicas holding colliding
content resolve to DIFFERENT executed blocks while AGREEING on the order. `hOrder` alone therefore cannot
give `tauBlocks` agreement, which is the whole reason `merge_convergence_tauBlocks` is a theorem and
`merge_convergence_tauOrder` was not. -/
theorem finalized_resolution_diverges_at_a_collision :
    ([b0.id] : List BlockId).filterMap (Lace.lookup [b0])
      ≠ ([b0.id] : List BlockId).filterMap (Lace.lookup [b0Forged]) := by decide

/-! The `#guard`s are the project's machine-checked non-vacuity teeth (a false `#guard` is a BUILD ERROR).
They establish, against a CONCRETE n>1 trace WITH a Byzantine fork: (i) three replicas merging the same
causally-closed blocks in different orders/groupings reach the SAME keyset (the join's order-independence,
witnessed non-vacuously); (ii) idempotence/absorption are inert on a real lace; (iii) monotonicity preserves
genesis through a fork-merge. So the CRDT-join theorems constrain a REAL non-trivial replicated state, and the
model reproduces `finality.rs::merge`'s order-independent convergence. -/

/-! ## 9. Axiom hygiene — the join laws + the convergence wire are kernel-clean. -/

#assert_axioms laceIds_mergeLace
#assert_axioms merge_comm
#assert_axioms merge_assoc
#assert_axioms merge_idem
#assert_axioms merge_absorb
#assert_axioms merge_monotone
#assert_axioms merge_least_upper_bound
#assert_axioms crossCanonical_self
#assert_axioms canonical_append_iff
#assert_axioms sameView_of_canonical_eq_ids
#assert_axioms crossCanonical_replicas
#assert_axioms crossCanonical_is_the_gap
#assert_axioms finalized_resolution_diverges_at_a_collision
#assert_axioms merge_convergence_tauBlocks
#assert_axioms merge_convergence_to_state

end Dregg2.Distributed.LaceMerge
