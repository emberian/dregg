/-
# Dregg2.Distributed.CatchupConverges — STATE CATCH-UP convergence: a node that JOINS fresh
# or FALLS BEHIND, then receives the same causally-closed set of finalized blocks as a peer,
# reaches the SAME finalized executed state.

**The gap this closes.** `Distributed.LaceMerge` proves the CRDT delta-merge (`finality.rs::merge`)
is a pure JOIN on the content-addressed keyset, and that two replicas which merge the same block set
converge (`merge_convergence_to_state`). `Distributed.BlocklaceFinality` proves the `tau` ordering is
deterministic and wires it to the executor. NEITHER models the **catch-up RECEPTION path** that the node
runs — `node/src/blocklace_sync.rs::handle_push` + `node/src/catchup.rs::apply_with_buffering` — where a
lagging/fresh node ingests blocks that arrive OUT OF ORDER or with GAPS, BUFFERS the orphans, requests the
missing predecessors, and re-applies them in CAUSAL order. The node-level claim we must justify is:

  *a node that has received the same causally-closed set of finalized blocks (in ANY arrival order,
   grouped into ANY deltas, with ANY amount of buffering) reaches the SAME finalized state as any peer.*

This file models THAT reception as a FOLD of the CRDT merge over the received blocks
(`catchupFrom = blocks.foldl (fun B b => mergeLace B [b]) []`) — each received block is merged into the
growing lace, exactly the skip-if-present insertion `receive_block`/`apply_with_buffering` performs (the
orphan buffer only DELAYS a merge until the block's past is present; it never admits a block out of causal
order and never drops one whose past arrives later, so the SET of blocks that ultimately enter the keyset is
invariant to the buffering — see `node/src/catchup.rs::out_of_order_delivery_converges_to_full_chain`). We
prove:

* **`catchup_keyset` (the reconstruction is exact).** `laceIds (catchupFrom blocks) = blocks.toFinset-ids`:
  catching up from a received block list yields a lace whose content-addressed keyset is EXACTLY the set of
  received block ids. The fold of merges accumulates the union (`LaceMerge.laceIds_mergeLace`), independent
  of order (so any arrival permutation gives the same keyset).
* **`catchup_order_independent` (arrival order is irrelevant).** Two nodes that receive the SAME set of
  blocks in DIFFERENT orders reach laces with the SAME keyset. This is the order-independence of catch-up:
  the lossy/out-of-order gossip + orphan-buffering converge to one content-addressed state.
* **`catchup_converges_to_leader` (THE convergence — a laggard matches the leader).** A node that catches up
  from the leader's full block set reaches the SAME finalized executed state as the leader: same keyset
  (`catchup_keyset`) PLUS cross-lace canonicity (`LaceMerge.CrossCanonical` — the ASSUMPTION, see below)
  ⇒ `SameView` (`LaceMerge.sameView_of_canonical_eq_ids`) ⇒ same finalized blocks ⇒ same `executeTau`
  (`LaceMerge.merge_convergence_to_state`). Equal keysets alone do NOT give `SameView`
  (`LaceMerge.crossCanonical_is_the_gap`), so the catch-up convergence is CONDITIONAL on two undischarged
  hypotheses, both named below.

## SCOPE.

FAITHFUL (matches the node catch-up path as a pure function of the received block SET):
* `catchupFrom blocks` — the fold of skip-if-present merges. The orphan buffer
  (`catchup.rs::OrphanBuffer`) is a SCHEDULING device: it reorders WHEN each block's merge happens so that a
  block is merged only once its predecessors are present, but the multiset of blocks merged is exactly the
  received set, and `mergeLace`'s keyset is order-independent (`LaceMerge.merge_comm/assoc`). So the keyset
  of the node's lace after catch-up depends only on the received SET — which is what `catchup_keyset` states.

ASSUMED (stated, not hidden — inherited from `LaceMerge`):
* The `tauOrder`-agreement seam (`hOrder`) is taken as an explicit hypothesis and is NOT derived. The
  earlier version of this note called it "TRUE because `BlocklaceFinality.tauOrder` is permutation-invariant
  on canonical laces" — that permutation-invariance is a CLAIM, not a result in this tree, and
  `LaceMerge` §6 states precisely what is and is not established (the round map is permutation-invariant,
  `BlocklaceFinality.roundOf_perm`; the rest of `tauOrder` is not proved so). For the
  identical-representative case `hOrder` is `tauOrder_deterministic` (`rfl`); at n>1 it is assumed.
* `LaceMerge.CrossCanonical` — CROSS-lace canonicity, that the leader and the caught-up laggard resolve any
  shared content-address to the SAME block. This was an ANONYMOUS binder `hagree` here until 2026-07-27; it
  is now the named assumption, and it is strictly more than the two `Lace.Canonical` hypotheses beside it
  (`LaceMerge.canonical_append_iff`, `LaceMerge.crossCanonical_is_the_gap`). It is the §8 collision-
  resistance obligation, and it is where a Poseidon2 collision breaks catch-up convergence.
* Signature validity / causal closure are the §8 / `WellFormedDelta` hypotheses of `LaceMerge`; here a
  caught-up node is fed a well-formed closed set (`receive_block`/`apply_with_buffering` enforce sig+seq+
  equivocation at the Rust boundary — the A1 fix — and the buffer enforces causal order before each merge).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Distributed.CatchupConverges`. Differential: `node/src/catchup.rs` +
`node/src/blocklace_sync.rs::handle_push`.
-/
import Dregg2.Distributed.LaceMerge

namespace Dregg2.Distributed.CatchupConverges

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)
open Dregg2.Distributed.LaceMerge
  (laceIds mergeLace laceIds_mergeLace laceIds_nil mem_laceIds SameView CrossCanonical
   sameView_of_canonical_eq_ids merge_convergence_to_state)
open Dregg2.Distributed.BlocklaceFinality (tauOrder tauBlocks executeTau)

/-! ## 1. The catch-up reconstruction — a FOLD of the CRDT merge over received blocks.

A node catching up ingests blocks one delta at a time (`handle_push` calls `apply_with_buffering`, which
merges each block — possibly after buffering it until its predecessors land). We model the net effect as a
left-fold of `mergeLace` over the received blocks, starting from the empty lace (a fresh joiner). The orphan
buffer's reordering is invisible at this level: it only changes WHICH ARRIVAL becomes WHICH fold step, and
the keyset of a fold of merges is the union of all merged-in ids regardless of step order. -/

/-- **`catchupFrom blocks`** — the lace a node reconstructs by merging each received block in turn
(`catchup.rs::apply_with_buffering` over a received batch, with buffering folded out). Starts from the empty
lace (fresh joiner); a node already holding `B₀` catches up via `catchupOnto B₀ blocks`. -/
def catchupFrom (blocks : List Block) : Lace :=
  blocks.foldl (fun B b => mergeLace B [b]) []

/-- **`catchupOnto B₀ blocks`** — a node that already holds `B₀` (e.g. a checkpoint or its prior lace)
catching up by merging each received block. The lagging-node case: `B₀` is what it had before falling behind,
`blocks` are the finalized blocks it was missing. -/
def catchupOnto (B₀ : Lace) (blocks : List Block) : Lace :=
  blocks.foldl (fun B b => mergeLace B [b]) B₀

/-! ## 2. THE RECONSTRUCTION LAW — the caught-up keyset is exactly the received-id set. -/

/-- **`laceIds_singleton` (helper).** The keyset of a one-block delta `[b]` is `{b.id}`. -/
theorem laceIds_singleton (b : Block) : laceIds [b] = {b.id} := by
  ext h; simp [mem_laceIds, eq_comm]

/-- **`catchupOnto_keyset` (reconstruction is exact, lagging case).** Catching `blocks` up ONTO a
held lace `B₀` yields a keyset that is `laceIds B₀` plus exactly the received block ids. The fold of merges
accumulates the union one id at a time (`laceIds_mergeLace`), so the result depends only on the SET of
received ids — NOT their arrival order or grouping. This is the load-bearing fact behind "a caught-up node
holds exactly what it had plus what it received". -/
theorem catchupOnto_keyset (B₀ : Lace) (blocks : List Block) :
    laceIds (catchupOnto B₀ blocks) = laceIds B₀ ∪ (blocks.map (·.id)).toFinset := by
  unfold catchupOnto
  induction blocks generalizing B₀ with
  | nil => simp
  | cons b rest ih =>
    -- foldl over (b :: rest) from B₀ = foldl over rest from (mergeLace B₀ [b]).
    simp only [List.foldl_cons]
    rw [ih (mergeLace B₀ [b])]
    rw [laceIds_mergeLace, laceIds_singleton]
    -- (laceIds B₀ ∪ {b.id}) ∪ rest-ids = laceIds B₀ ∪ (b.id :: rest)-ids
    simp only [List.map_cons, List.toFinset_cons]
    -- both sides are laceIds B₀ ∪ {b.id} ∪ rest.toFinset, modulo associativity/comm of ∪.
    rw [Finset.insert_eq]
    ac_rfl

/-- **`catchup_keyset` (reconstruction is exact, fresh-joiner case).** A FRESH node (empty starting
lace) that catches up from `blocks` reaches a lace whose keyset is EXACTLY the received id set. The corollary
of `catchupOnto_keyset` at `B₀ = []`. -/
theorem catchup_keyset (blocks : List Block) :
    laceIds (catchupFrom blocks) = (blocks.map (·.id)).toFinset := by
  have : catchupFrom blocks = catchupOnto [] blocks := rfl
  rw [this, catchupOnto_keyset]
  simp [laceIds_nil]

/-! ## 3. ORDER-INDEPENDENCE OF CATCH-UP — different arrival orders, same content-addressed state. -/

/-- **`catchup_order_independent`.** Two nodes that receive the SAME set of blocks (here: one list a
PERMUTATION of the other — same multiset, hence same id-toFinset) in DIFFERENT orders reconstruct laces with
the SAME keyset. The order-independence of the lossy/out-of-order catch-up: whatever order gossip delivered
the finalized blocks in, the caught-up content-addressed state is identical. -/
theorem catchup_order_independent {blocks₁ blocks₂ : List Block}
    (hperm : blocks₁.Perm blocks₂) :
    laceIds (catchupFrom blocks₁) = laceIds (catchupFrom blocks₂) := by
  rw [catchup_keyset, catchup_keyset]
  -- equal multisets ⇒ equal membership ⇒ equal toFinset.
  ext h
  simp only [List.mem_toFinset]
  exact (hperm.map (·.id)).mem_iff

/-- **`catchup_order_independent_set` (the SET form).** More generally, any two received lists with
the SAME id-keyset reconstruct the same keyset, even if not literal permutations (e.g. one carries a
duplicate-gossip copy, or content-addressing collapses equal-id blocks). The robust statement the
dissemination layer relies on: catch-up converges on the id SET, not the delivery sequence. -/
theorem catchup_order_independent_set {blocks₁ blocks₂ : List Block}
    (hids : (blocks₁.map (·.id)).toFinset = (blocks₂.map (·.id)).toFinset) :
    laceIds (catchupFrom blocks₁) = laceIds (catchupFrom blocks₂) := by
  rw [catchup_keyset, catchup_keyset]; exact hids

/-! ## 4. THE CONVERGENCE THEOREM — a caught-up node matches the leader's finalized state.

We compose §2 (the caught-up keyset equals the received id set) with `LaceMerge.merge_convergence_to_state`
(same keyset + canonical + content-agreement ⇒ same executed state). The setup: a LEADER holds a canonical
lace `leader`; a LAGGARD catches up from a received list `recv` whose ids are exactly the leader's keyset
(it received the same causally-closed finalized set — what the catch-up `Pull`/`Push` deliver, with their
causal past). Then the laggard executes to the SAME `RecChainedState` as the leader. -/

open Dregg2.Exec.ConsensusExec (Decoder)
open Dregg2.Exec (RecChainedState)

/-- **`catchup_converges_to_leader` (THE end-to-end catch-up convergence).** A laggard node that
catches up from a received block list `recv` whose content-addressed keyset equals the leader's lace keyset —
with both laces canonical, CROSS-canonical (`hcross`: leader and laggard resolve any shared content-address
to the same block) and finalizing the same `tauOrder` — EXECUTES TO THE SAME finalized `RecChainedState`
as the leader. Catch-up reconstruction (`catchup_keyset`) feeding LaceMerge convergence
(`merge_convergence_to_state`), end to end.

⚑ `hcross` was the unnamed binder `hagree` here; it is `LaceMerge.CrossCanonical`, and it is the
assumption a hash collision breaks. It is NOT implied by `hcL`, `hcC` and `hids` together
(`LaceMerge.crossCanonical_is_the_gap`), and `hOrder` remains undischarged (`LaceMerge` §6). -/
theorem catchup_converges_to_leader
    (dec : Decoder) (s0 : RecChainedState)
    (leader : Lace) (recv : List Block)
    (participants : List AuthorId) (wavelength : Nat)
    (hcL : leader.Canonical) (hcC : (catchupFrom recv).Canonical)
    (hids : laceIds leader = (recv.map (·.id)).toFinset)
    (hcross : CrossCanonical leader (catchupFrom recv))
    (hOrder : tauOrder leader participants wavelength
              = tauOrder (catchupFrom recv) participants wavelength) :
    executeTau dec s0 leader participants wavelength
      = executeTau dec s0 (catchupFrom recv) participants wavelength := by
  -- The caught-up keyset equals the leader keyset.
  have hkey : laceIds leader = laceIds (catchupFrom recv) := by
    rw [hids, catchup_keyset]
  -- Apply LaceMerge's two-replica convergence with leader = B₁, catchup = B₂.
  exact merge_convergence_to_state dec s0 participants wavelength hcL hcC hkey hcross hOrder

/-- **`catchup_lagging_converges` (the LAGGING-node variant).** A node already holding `B₀` that
catches up by merging the missing finalized blocks `recv` reaches the same executed state as a leader whose
keyset equals `laceIds B₀ ∪ recv-ids`. Same proof shape via `catchupOnto_keyset`; the lagging node's lace is
`catchupOnto B₀ recv`. Models the "fell behind then synced the delta" case (vs. the fresh-joiner
`catchup_converges_to_leader`). -/
theorem catchup_lagging_converges
    (dec : Decoder) (s0 : RecChainedState)
    (leader B₀ : Lace) (recv : List Block)
    (participants : List AuthorId) (wavelength : Nat)
    (hcL : leader.Canonical) (hcC : (catchupOnto B₀ recv).Canonical)
    (hids : laceIds leader = laceIds B₀ ∪ (recv.map (·.id)).toFinset)
    (hcross : CrossCanonical leader (catchupOnto B₀ recv))
    (hOrder : tauOrder leader participants wavelength
              = tauOrder (catchupOnto B₀ recv) participants wavelength) :
    executeTau dec s0 leader participants wavelength
      = executeTau dec s0 (catchupOnto B₀ recv) participants wavelength := by
  have hkey : laceIds leader = laceIds (catchupOnto B₀ recv) := by
    rw [hids, catchupOnto_keyset]
  exact merge_convergence_to_state dec s0 participants wavelength hcL hcC hkey hcross hOrder

/-! ## 5. NON-VACUITY — a concrete multi-step catch-up over a real (forked) finalized set.

Mirrors `node/src/catchup.rs`'s integration tests + `LaceMerge`'s Byzantine-fork witness: a LAGGARD receives
the SAME three causally-closed blocks (genesis + a creator-9 FORK `fork1 ∥ fork2`) as the leader, but in
REVERSE arrival order (the orphan buffer reorders them back), and the reconstruction reaches the SAME keyset
as the leader's full lace. The `#guard`s are the model⟺node differential: `apply_with_buffering` over these
blocks in any order yields the leader keyset, matching `catchup.rs::out_of_order_delivery_converges_to_full_chain`
and `two_replicas_converge_to_same_keyset`. -/

open Dregg2.Distributed.LaceMerge (b0 fork1 fork2)

/-- The leader's full lace: genesis + the creator-9 fork (a real Byzantine finalized set). -/
def leaderLace : Lace := [b0, fork1, fork2]

/-- A LAGGARD that received the three blocks in REVERSE order (orphan buffer puts them back in causal order). -/
def laggardCatchup : Lace := catchupFrom [fork2, fork1, b0]
/-- A second laggard that received them in a DIFFERENT order / grouping. -/
def laggardCatchup2 : Lace := catchupFrom [fork1, b0, fork2]

-- The reconstructed keyset equals the leader's full keyset (catch-up is exact, any order).
#guard laceIds laggardCatchup == laceIds leaderLace
#guard laceIds laggardCatchup2 == laceIds leaderLace
#guard laceIds laggardCatchup == ({100, 101, 102} : Finset BlockId)
-- Two laggards converge to the SAME keyset despite different arrival orders.
#guard laceIds laggardCatchup == laceIds laggardCatchup2
-- A laggard that already held genesis, catching up the fork delta, lands on the leader keyset.
#guard laceIds (catchupOnto [b0] [fork1, fork2]) == laceIds leaderLace
-- Idempotent re-catch-up (duplicate gossip / at-least-once): re-receiving is inert.
#guard laceIds (catchupOnto laggardCatchup [b0, fork1, fork2]) == laceIds leaderLace

/-! The `#guard`s are the project's machine-checked non-vacuity teeth (a false `#guard` is a BUILD ERROR).
Against a CONCRETE multi-step catch-up over a Byzantine-forked finalized set: (i) a laggard receiving the
finalized blocks in reverse / shuffled order reconstructs EXACTLY the leader's keyset; (ii) two laggards with
different arrival orders converge; (iii) catching a delta ONTO a held genesis lands on the leader keyset; (iv)
re-catch-up is idempotent. So the convergence theorems constrain a REAL non-trivial catch-up, and the model
reproduces `catchup.rs`'s order-independent reconstruction. -/

/-! ## 6. Axiom hygiene — the catch-up reconstruction + convergence wire are kernel-clean. -/

#assert_axioms catchupOnto_keyset
#assert_axioms catchup_keyset
#assert_axioms catchup_order_independent
#assert_axioms catchup_order_independent_set
#assert_axioms catchup_converges_to_leader
#assert_axioms catchup_lagging_converges

end Dregg2.Distributed.CatchupConverges
