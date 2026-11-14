/-
# Dregg2.Consensus.Safety — CONSENSUS SAFETY at the CHAIN level: no two honest nodes
# finalize CONFLICTING histories.

**The gap this closes — the chain-level sibling of `lightclient_unfoolable`.**
`Circuit.CircuitSoundness.lightclient_unfoolable` proves a single accepted TURN witnesses a
genuine kernel transition — per-turn *validity*. It does NOT say WHICH chain is canonical.
Every consensus-safety theorem already in the tree fixes ONE lace / ONE state:

* `Proof.BFT.bft_safety` — over one `votes` pool: two conflicting blocks cannot both reach a
  BFT quorum (quorum-intersection at an honest process).
* `Proof.CordialMiners.cordial_agreement` / `…_from_lace` — over ONE `CordialState`: a wave
  anchors a single super-ratified leader (the quorum read off that lace).
* `Distributed.BlocklaceFinality.finalLeaders_one_per_wave` / `tauOrder_deterministic` — over
  ONE `Lace`: a wave has ≤ 1 final leader; the order is a function of (lace, participants).
* `Consensus.TauPrefixMonotone.tau_finalized_prefix_monotone` — over ONE lace's GROWTH: the
  finalized prefix is append-only *under* `ClosedExtension` + `ChainExtends` (CM Prop. 3's
  leader-safety, imported from the paper, owed a Lean proof). The former three-field
  `FinalizedRegionStable` is deleted and its unconditional refutation RETRACTED — the
  counterexample was a fact about a τ that had deviated from CM Def. 6, not about the CM rule.

What NONE of them state is the property a LIGHT CLIENT'S CHAIN-CHOICE actually rests on:
**two honest nodes, holding DIFFERENT (partial) laces `S₁ ≠ S₂`, cannot finalize conflicting
leaders at the same wave — so their finalized HISTORIES never disagree.** A client that follows
either node's finalized chain lands on the SAME history; there is no fork it can be split across.

This module supplies that apex. The honest observation that makes it tractable: the proof of
`cordial_agreement` never uses that its two super-ratifications come from the *same* state — it
consumes only the two ratifier vote pools, the BFT honest-majority model over their union, the
honesty law, and id-determinism. So the cross-node lift is a genuine generalization, not a
re-proof: §1 isolates the pure two-pool quorum-intersection kernel (`quorum_pair_agreement`,
the generalization of `bft_safety` from one pool to two independent pools), §2 lifts it to two
`CordialState`s, §3 reads the quorum off each node's lace (`Committed`, via the existing
`SuperRatification.ofLace`), and §4 composes per-wave agreement into the chain-level
`no_conflicting_finalized_history`.

## CARRIERS (hypotheses, never `axiom`s — the honest floor).

* **Honest majority / `n > 3f`.** Carried by `BFT.BFTModel` over the UNION of the two nodes'
  ratification pools (its `bft_threshold`, `fault_bound`, `population_bound`, `honest_vote_once`
  fields). This is the standard BFT floor; deriving that the union actually meets it is the
  post-GST dissemination argument (the same residual `BFT.lean`'s O2 and
  `cordial_agreement_from_lace` name) — off the safety-critical path, NOT an open hole here.
* **Shared participant universe.** The two nodes count ratifiers over the same participant id
  set, so two `≥ n − f` pools intersect in an honest participant. Carried implicitly by the
  single `Finality.Config` both pools are read against.
* **CROSS-NODE content-addressing** (`CrossNodeCanonical S₁ S₂`, §0): a block held by node 1 and
  a block held by node 2 that share an id ARE THE SAME BLOCK. This is what discharges the
  per-pair `hid_inj : LeaderIdPins l₁ l₂` at every cross-node site.

  ⚑ **This doc-comment used to say `Lace.Canonical` at the anchor. That was WRONG, and the
  correction is the point of the 2026-07-28 repair.** `l₁` comes from node 1's lace and `l₂`
  from node 2's; `Lace.Canonical` constrains two blocks WITHIN ONE lace and says nothing about
  an id present in both. `Model.crossNodeCanonical_is_the_gap` (§5) exhibits two node laces that
  are EACH `Lace.Canonical`, each genuinely commits a leader at wave 0, share a cross-node BFT
  model — and whose anchors are DIFFERENT BLOCKS AT THE SAME ADDRESS, so `LeaderIdPins` fails
  and the two finalized histories DISAGREE. The assumption is the one a content-address
  collision breaks, and breaking it splits the light client across a fork. It is
  `Distributed.LaceMerge.CrossCanonical` read on the two nodes' laces — the same assumption the
  CRDT-convergence lane named on 2026-07-27, consumed here at the consensus layer.

**`OPEN-CM-SUPERRATIFY-BRIDGE` — BUILT 2026-07-28, at a named price.**
`Consensus.SuperRatifyBridge` carries the deployed finalizer into this module's `Committed`:

    committed_of_finalLeaderAt :
      B.Canonical → participants.Nodup → ThresholdAgrees cfg participants →
      LeaderNotGlobalEquivocator B l → finalLeaderAt B participants wave wavelength = some l →
      Committed (deployedState B participants wavelength) cfg l

`finalizedBy_deployedHistory` then DISCHARGES `FinalizedBy` below from the node's own wave loop
(it had no supplier before), and `deployed_nodes_no_conflicting_history` reaches this file's apex
from two nodes each running `finalLeaderAt` / `findAllFinalLeaders` — the rule behind
`@[export] dregg_tau_order`. What that bridge established, and what it cost, is item 1 of the
honest-scope list below. **It is `finalLeaderAt`, not `isSuperRatified`, that bridges**:
`isSuperRatified` carries NO unique-leader guard and is INCOMPARABLE with `Committed`
(`SuperRatifyBridge.superRatified_alone_is_not_committed`).

## THE VACUITY THIS FILE CARRIED UNTIL 2026-07-28, AND WHAT REPLACED IT.

`no_conflicting_finalized_history`'s only hypothesis was a `CrossNodeWitness`, and
`CrossNodeWitness` was **INHABITED NOWHERE IN THE TREE** — zero constructions, zero `hid_inj :=`.
The apex quantified over an empty premise. §5's "non-vacuity" did not rescue it: it showed the §1
kernel firing (its own hypotheses still assumed as binders) and `Consistent` being two-sided, and
never once inhabited the apex's hypothesis. That is the `CrossSchemeSameOpening` disease — a
consumer with no model.

What is here now:
* `Model.crossWitness` — **a real `CrossNodeWitness`**, at two nodes holding GENUINELY DIFFERENT
  laces (neither view contains the other's wave-end observer), each committing the wave-0 leader
  off its own blocks, with a cross-node BFT model carrying an ACTUAL Byzantine ratifier at the
  `f = 1` budget. Every field derived; nothing assumed.
* `Model.apex_fires_on_two_nodes` — the APEX ITSELF applied to that witness. The chain-safety
  conclusion is reached on real data, not merely stated.
* `crossNodeBftOfCommitted` — a general theorem, not a fixture: the cross-node BFT carrier is
  INHABITED whenever the two nodes share a bounded participant universe with ≤ f corrupt and both
  committed the same anchor id. (At DIFFERENT anchor ids with both quorums met it is not
  inhabitable — that is precisely what `quorum_pair_agreement` refutes. The scope is honest, not
  a convenience.)
* `no_conflicting_finalized_history_of_committed` — the apex with the histories TIED to the nodes
  (`FinalizedBy`) and cross-node canonicity stated ONCE at the lace level instead of per pair.
  The old apex never related `h₁` to `S₁` at all: it was a statement about two arbitrary lists.

## WHAT CHAIN SAFETY THIS DOES *NOT* ESTABLISH — read before citing.

1. **The deployed finalizer IS covered now — CONDITIONALLY, and one of the conditions is a
   coverage hole.** `Consensus.SuperRatifyBridge.committed_of_finalLeaderAt` proves the block the
   node's wave loop pushes onto `final_leaders` is `Committed`, so safety transfers — but it costs
   two hypotheses beyond `Lace.Canonical` and `participants.Nodup`, both NAMED and MODELLED there:
   * `ThresholdAgrees cfg participants` (`cfg.n − cfg.f ≤ superMajority participants.length`).
     Benign at every parameter anyone runs: the two thresholds are EQUAL on `3f+1 ≤ n ≤ 3f+3`
     (`thresholdAgrees_of_canonical_bft`) and the band is TIGHT
     (`thresholdAgrees_fails_at_3f_plus_4` — at `n = 7, f = 1` the node finalizes on 5 ratifiers
     where `Committed` demands 6).
   * `LeaderNotGlobalEquivocator B l` (`¬ Equivocator B l.creator`) — **NOT benign.** The node's
     guard (`hasEquivInPast`) is OBSERVER-LOCAL and keyed on a same-ROUND pair; `Equivocator` is
     GLOBAL and keyed on an INCOMPARABLE pair. `SuperRatifyBridge.Model.forked` is a lace where
     the node's observers ratify the leader at full supermajority AND the node finalizes it
     (`#guard finalLeaderAt forked parts 0 3 == some leader`) while `Committed` is FALSE
     (`forked_is_not_committed`). So: **a node that finalizes a leader whose author forked
     outside every observer's causal past is finalizing OUTSIDE this theorem's domain.** That is
     a coverage hole, not an attack — the deployed rule is the more faithful of the two, and the
     repair is to teach `CordialState.approves` the observer-local guard
     (`OPEN-CM-LOCAL-EQUIVOCATION`, open).
   ⚑ Also note `CordialState.approves` was repaired on 2026-07-28 from strict `≺` to the
   INCLUSIVE past `ordering.rs` actually uses. That changed what `Committed` means (it is now
   easier to satisfy, so this apex is STRONGER, not weaker); without it the bridge is unprovable
   at every canonical BFT parameter, because the missing voter is exactly `l.creator`.
2. **The BFT model over the UNION remains an assumption in the case that matters.**
   `crossNodeBftOfCommitted` inhabits it only when both nodes committed the SAME anchor id; at
   DIFFERENT ids with both quorums met it is uninhabitable, which is the whole force of
   `quorum_pair_agreement` but also means the carrier is *never discharged from the runtime*.
   Whether two honest nodes' actual ratifier pools meet `n > 3f` / `≤ f` corrupt over their union
   is the post-GST dissemination residual — **unchanged by the bridge**, which passes it straight
   through as a hypothesis of `deployed_nodes_no_conflicting_history`.
3. **`CrossNodeCanonical` is backed by nothing in-tree.** It is collision resistance over the
   block encoding at the point consensus consumes it; this tree does not prove that. It is
   decidable, so a node can check it against a peer's blocks — that is what naming it buys, and
   it is all it buys. **Unchanged by the bridge**, which also passes it through. Its within-one-
   lace weakening `Lace.Canonical` gained a sixth consumer there (`past_block`), where it is what
   turns an id the deployed BFS reached into a block the `≺` order can talk about.
4. **The model is a toy.** `n = 4, f = 1`, one wave, one leader, six blocks. It settles
   satisfiability and refutability; it is not a scale claim. (The BRIDGE theorem itself is fully
   general in `n`, `f`, `B` and `participants`; only its models are at those parameters.)
5. **No Lean THEOREM in this tree evaluates the deployed finalizer on a concrete lace.** When
   this was written none could: `roundOf` → `computeRounds` → `Array.qsort`, which the kernel
   cannot reduce (measured 2026-07-28). Every `#guard` about `tauOrder` / `isSuperRatified` /
   `finalLeaderAt` — including the two in `SuperRatifyBridge.Model` — runs in the COMPILER,
   outside the kernel. They are tests, not proofs, and the bridge's own models are built
   round-FREE for that reason. Since dregg issue #100 the round map is a structural Kahn fold and
   `decide` DOES reduce `roundOf` / `isSuperRatified` / `finalLeaderAt` (measured 2026-11-13;
   `tauOrder` still does not, through `List.mergeSort`) — so those `#guard`s could now be
   theorems. They have not been restated; that is owed.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Consensus.Safety`.
-/
import Mathlib.Tactic
import Dregg2.Proof.CordialMiners
import Dregg2.Distributed.LaceMerge

namespace Dregg2.Consensus.Safety

open Dregg2 Dregg2.World Dregg2.Authority.Blocklace
open Dregg2.Proof.BFT Dregg2.Proof.CordialMiners

/-! ## §0. `CrossNodeCanonical` — the assumption `hid_inj` ACTUALLY is.

Nine sites in this file and `Proof.CordialMiners` carried `hid_inj : l₁.id = l₂.id → l₁ = l₂` as
an anonymous binder, doc-commented "`Lace.Canonical` at the anchor". At the CROSS-NODE sites that
attribution is wrong: `l₁` is read off node 1's lace and `l₂` off node 2's, and `Lace.Canonical`
is a statement about two blocks inside ONE lace. The assumption that pins two DIFFERENT nodes'
anchors is cross-lace canonicity — `Distributed.LaceMerge.CrossCanonical`, named by the CRDT
lane on 2026-07-27 for exactly the same mis-attribution on the convergence side. We reuse it
rather than mint a second shape, and prove the per-pair form is its consequence. -/

/-- **`CrossNodeCanonical S₁ S₂`** — the two nodes' laces are content-addressed ACROSS the node
boundary: a block node 1 holds and a block node 2 holds that share a content-address ARE THE SAME
BLOCK. Definitionally `Distributed.LaceMerge.CrossCanonical` on the two laces — the consensus
layer consuming the assumption the CRDT layer already named.

It is NOT implied by the two laces being each `Lace.Canonical`
(`Model.crossNodeCanonical_is_the_gap`), it is NOT a crypto axiom, and it is NOT a theorem: the
wire-format fact that makes it hold is collision resistance over the block encoding, which this
tree does not prove. -/
def CrossNodeCanonical (S₁ S₂ : CordialState) : Prop :=
  Distributed.LaceMerge.CrossCanonical S₁.lace S₂.lace

/-- Cross-node canonicity is DECIDABLE on two concrete views — a node can CHECK it against a
peer's blocks rather than assume it. -/
instance decidableCrossNodeCanonical (S₁ S₂ : CordialState) :
    Decidable (CrossNodeCanonical S₁ S₂) :=
  Distributed.LaceMerge.decidableCrossCanonical S₁.lace S₂.lace

/-- It is a statement about the PAIR of nodes, so it is symmetric. -/
theorem CrossNodeCanonical.symm {S₁ S₂ : CordialState} (h : CrossNodeCanonical S₁ S₂) :
    CrossNodeCanonical S₂ S₁ :=
  Distributed.LaceMerge.CrossCanonical.symm h

/-- **On the diagonal it IS `Lace.Canonical`** — so it generalises the named per-lace floor
rather than changing the subject, and a single node comparing two of its own anchors needs no
more than what `Proof.CordialMiners` already assumed. -/
theorem crossNodeCanonical_self (S : CordialState) :
    CrossNodeCanonical S S ↔ S.lace.Canonical :=
  Distributed.LaceMerge.crossCanonical_self S.lace

/-- **`CrossNodeCanonical.leaderIdPins` — the per-pair binder, DERIVED from the named lace-level
assumption.** This is the honest discharge of every cross-node `hid_inj` in this file: it needs
the two anchors to be blocks of their own nodes' laces (which `committed_mem_lace` supplies from
the commit facts) and cross-node canonicity — NOT `Lace.Canonical` of either lace. -/
theorem CrossNodeCanonical.leaderIdPins {S₁ S₂ : CordialState} (h : CrossNodeCanonical S₁ S₂)
    {l₁ l₂ : Block} (h₁ : l₁ ∈ S₁.lace) (h₂ : l₂ ∈ S₂.lace) : LeaderIdPins l₁ l₂ :=
  fun hid => h l₁ h₁ l₂ h₂ hid

/-! ## §1. The pure two-pool quorum-intersection kernel.

`BFT.bft_safety` lives over a SINGLE `votes` pool — it answers "can two conflicting blocks both
reach a quorum *in one node's view*?". The chain-level question is over TWO views: node 1's
ratifier pool `v1` for `b1`, node 2's pool `v2` for `b2`. We monotone-lift each quorum onto the
UNION pool `v1 ++ v2` and run the classical intersection there: the honest witness ratified
across the union, so the honesty law collapses `b1 = b2`. This is `bft_safety` generalized from
one pool to two independent pools — the genuinely new kernel the chain apex needs. -/

/-- A node's ratifier read over `v1` is preserved when its pool is appended to another node's
pool: every distinct voter for `b` in `v1` is still a distinct voter for `b` in `v1 ++ v2`. -/
theorem votersFor_subset_append_left (v1 v2 : List Vote) (b : Nat) :
    votersFor v1 b ⊆ votersFor (v1 ++ v2) b := by
  intro x hx
  have hxsrc : x ∈ ((v1.filter (fun v => v.block = b)).map (·.voter)) :=
    List.dedup_subset _ hx
  apply List.subset_dedup
  have hf : v1.filter (fun v => v.block = b) ⊆ (v1 ++ v2).filter (fun v => v.block = b) := by
    intro y hy
    rw [List.mem_filter] at hy ⊢
    exact ⟨List.mem_append_left _ hy.1, hy.2⟩
  exact List.map_subset _ hf hxsrc

/-- Symmetric to `votersFor_subset_append_left`, for the right (second node's) pool. -/
theorem votersFor_subset_append_right (v1 v2 : List Vote) (b : Nat) :
    votersFor v2 b ⊆ votersFor (v1 ++ v2) b := by
  intro x hx
  have hxsrc : x ∈ ((v2.filter (fun v => v.block = b)).map (·.voter)) :=
    List.dedup_subset _ hx
  apply List.subset_dedup
  have hf : v2.filter (fun v => v.block = b) ⊆ (v1 ++ v2).filter (fun v => v.block = b) := by
    intro y hy
    rw [List.mem_filter] at hy ⊢
    exact ⟨List.mem_append_right _ hy.1, hy.2⟩
  exact List.map_subset _ hf hxsrc

/-- The ratifier COUNT only grows when a pool is unioned with another (both sides are `Nodup`,
being `.dedup`s, so subset gives `length ≤`). The monotonicity that lifts each node's local
`≥ n − f` quorum onto the union pool. -/
theorem votersFor_length_le_append_left (v1 v2 : List Vote) (b : Nat) :
    (votersFor v1 b).length ≤ (votersFor (v1 ++ v2) b).length :=
  ((List.nodup_dedup _).subperm (votersFor_subset_append_left v1 v2 b)).length_le

theorem votersFor_length_le_append_right (v1 v2 : List Vote) (b : Nat) :
    (votersFor v2 b).length ≤ (votersFor (v1 ++ v2) b).length :=
  ((List.nodup_dedup _).subperm (votersFor_subset_append_right v1 v2 b)).length_le

/-- **`quorum_pair_agreement` — the chain-safety kernel.** Two INDEPENDENT ratifier pools (the
two honest nodes' views), `v1` endorsing `b1` and `v2` endorsing `b2`, each meeting the BFT
quorum `n − f`. Under a `BFTModel` over their UNION (the honest-majority floor, shared
participant universe) and the honesty law (an honest participant who ratified across the union
ratified a single block), the two pools cannot endorse distinct blocks: `b1 = b2`.

This is `BFT.bft_safety` lifted from one pool to two: the two `n − f` quorums, monotone-lifted
onto `v1 ++ v2`, still meet `n − f`, so `honest_witness_in_intersection` produces an honest
participant in both — who then ratified both blocks. The classical quorum-intersection floor
does ALL the work; what is new is that the two quorums are read from DIFFERENT nodes' views. -/
theorem quorum_pair_agreement
    (cfg : Finality.Config) (v1 v2 : List Vote) (b1 b2 : Nat)
    (hq1 : cfg.n - cfg.f ≤ (votersFor v1 b1).length)
    (hq2 : cfg.n - cfg.f ≤ (votersFor v2 b2).length)
    (M : BFTModel cfg (v1 ++ v2))
    (honest_one : ∀ v : Nat, ¬ M.Byzantine v →
        v ∈ votersFor (v1 ++ v2) b1 → v ∈ votersFor (v1 ++ v2) b2 → b1 = b2) :
    b1 = b2 := by
  -- lift each node-local quorum onto the union pool.
  have hq1' : cfg.n - cfg.f ≤ (votersFor (v1 ++ v2) b1).length :=
    le_trans hq1 (votersFor_length_le_append_left v1 v2 b1)
  have hq2' : cfg.n - cfg.f ≤ (votersFor (v1 ++ v2) b2).length :=
    le_trans hq2 (votersFor_length_le_append_right v1 v2 b2)
  -- the transferred BFT feeder: the two union-quorums share an HONEST participant.
  obtain ⟨v, hhonest, hv1, hv2⟩ :=
    honest_witness_in_intersection cfg (v1 ++ v2) M b1 b2 hq1' hq2'
  -- that honest participant ratified both blocks ⇒ the honesty law collapses them.
  exact honest_one v hhonest hv1 hv2

/-! ## §2. Cross-node leader agreement — two `CordialState`s, one wave, one leader.

The super-ratification level. `sr₁` is node 1's super-ratification of leader `l₁` (over its
lace `S₁`); `sr₂` is node 2's, over `S₂`. We feed their vote pools to the §1 kernel. -/

/-- **`cross_node_leader_agreement` — DAG-BFT safety ACROSS NODES.** Two super-ratifications of
leaders `l₁ l₂` held by DIFFERENT nodes (`S₁`, `S₂`), with a `BFTModel` over the union of their
ratifier pools and the honesty law, cannot anchor distinct blocks: `l₁ = l₂`. The two states are
genuinely independent — this is `cordial_agreement` with the single-state assumption removed. -/
theorem cross_node_leader_agreement
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block)
    (sr₁ : SuperRatification S₁ cfg l₁) (sr₂ : SuperRatification S₂ cfg l₂)
    (M : BFTModel cfg (sr₁.votes ++ sr₂.votes))
    (honest_one : ∀ v : Nat, ¬ M.Byzantine v →
        v ∈ votersFor (sr₁.votes ++ sr₂.votes) l₁.id →
        v ∈ votersFor (sr₁.votes ++ sr₂.votes) l₂.id → l₁.id = l₂.id)
    (hid_inj : LeaderIdPins l₁ l₂) :
    l₁ = l₂ :=
  hid_inj
    (quorum_pair_agreement cfg sr₁.votes sr₂.votes l₁.id l₂.id sr₁.quorum sr₂.quorum M honest_one)

/-- **`no_conflicting_cross_node_leader` — the `False` / safety form.** Two DISTINCT blocks
cannot both be super-ratified by two different nodes for the same wave position. -/
theorem no_conflicting_cross_node_leader
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block) (hconflict : l₁ ≠ l₂)
    (sr₁ : SuperRatification S₁ cfg l₁) (sr₂ : SuperRatification S₂ cfg l₂)
    (M : BFTModel cfg (sr₁.votes ++ sr₂.votes))
    (honest_one : ∀ v : Nat, ¬ M.Byzantine v →
        v ∈ votersFor (sr₁.votes ++ sr₂.votes) l₁.id →
        v ∈ votersFor (sr₁.votes ++ sr₂.votes) l₂.id → l₁.id = l₂.id)
    (hid_inj : LeaderIdPins l₁ l₂) :
    False :=
  hconflict (cross_node_leader_agreement cfg S₁ S₂ l₁ l₂ sr₁ sr₂ M honest_one hid_inj)

/-- The honesty law is discharged by the BFT model's own `honest_vote_once` over the union pool
— exactly as `cordial_agreement_via_bft` does single-state. So consuming the cross-node honesty
hypothesis costs nothing beyond the BFT model already granted. -/
theorem cross_node_honesty_of_bft
    (cfg : Finality.Config) (votes : List Vote) (M : BFTModel cfg votes)
    (l₁ l₂ : Block) (v : Nat) (hhonest : ¬ M.Byzantine v)
    (hv1 : v ∈ votersFor votes l₁.id) (hv2 : v ∈ votersFor votes l₂.id) :
    l₁.id = l₂.id :=
  M.honest_vote_once v l₁.id l₂.id hhonest hv1 hv2

/-- **`cross_node_leader_agreement_via_bft`** — the packaged cross-node safety theorem: the
honesty hypothesis is discharged by the BFT model, no separate oracle. -/
theorem cross_node_leader_agreement_via_bft
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block)
    (sr₁ : SuperRatification S₁ cfg l₁) (sr₂ : SuperRatification S₂ cfg l₂)
    (M : BFTModel cfg (sr₁.votes ++ sr₂.votes))
    (hid_inj : LeaderIdPins l₁ l₂) :
    l₁ = l₂ :=
  cross_node_leader_agreement cfg S₁ S₂ l₁ l₂ sr₁ sr₂ M
    (cross_node_honesty_of_bft cfg (sr₁.votes ++ sr₂.votes) M l₁ l₂) hid_inj

/-! ## §3. The lace-derived cross-node agreement — quorum READ OFF EACH NODE'S LACE.

The form a node actually realizes: each node holds `Committed Sᵢ cfg lᵢ` (the lace exhibits the
`≥ n − f` ratifier read, `superRatifiedFromLace`). We materialize each lace's ratifier set into
the BFT feeder (`SuperRatification.ofLace`, count preserved) and run §2. The quorum the safety
argument consumes is `(ratifyingVoters …).length` over each REAL lace — not assumed data. -/

/-- **`cross_node_agreement_from_lace` — chain-safety with the quorum read off each lace.** Two
nodes whose laces each EXHIBIT a `≥ n − f` ratifier read for leaders `l₁ l₂` (their `Committed`
facts), under the honest BFT model over the materialized union pool and id-determinism, anchor
the SAME leader. The two nodes' laces `S₁`, `S₂` are independent. -/
theorem cross_node_agreement_from_lace
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block)
    (h₁ : Committed S₁ cfg l₁) (h₂ : Committed S₂ cfg l₂)
    (M : BFTModel cfg
      ((SuperRatification.ofLace h₁.some).votes ++ (SuperRatification.ofLace h₂.some).votes))
    (hid_inj : LeaderIdPins l₁ l₂) :
    l₁ = l₂ :=
  cross_node_leader_agreement_via_bft cfg S₁ S₂ l₁ l₂
    (SuperRatification.ofLace h₁.some) (SuperRatification.ofLace h₂.some) M hid_inj

/-! ### §3b. The cross-node BFT carrier IS INHABITABLE — generally, not just at a fixture.

Every theorem above takes `M : BFTModel cfg (…ofLace h₁.some… ++ …ofLace h₂.some…)`. That type
mentions `Committed.some`, a `Classical.choice` extraction whose observer nobody can name, and
until this section nothing in the tree ever produced such an `M`. The satisfiability question is
therefore not decoration: if that type were empty, every cross-node theorem here — and the apex
above them — would be vacuous.

It is not empty, and the reason is structural rather than fixture-specific: whichever observer
`Committed.some` hands us, the ratifier set it reads is a `filter`+`dedup` of that node's
PARTICIPANT list (`ratifyingVoters_subset_participants`), so the union pool's voters are bounded
by the two participant lists no matter what. That is enough for `population_bound` and
`fault_bound`; `honest_vote_once` comes free because every materialized vote endorses the anchor
it was built for.

**The scope is honest.** The construction needs `l₂.id = l₁.id`. At DIFFERENT anchor ids, with
both `n − f` quorums met over a shared participant universe, the model is genuinely
UNINHABITABLE — that is exactly what `quorum_pair_agreement` proves. So this is not a
convenience assumption dodging the hard case; the hard case is the theorem. -/

/-- **`crossNodeBftOfCommitted` — the cross-node honest-majority carrier, CONSTRUCTED.** Given
two nodes' commit facts at the SAME anchor id, a shared participant universe of size ≤ `n` with
at most `f` corrupt in it, and the BFT floor `n > 3f`, the `BFTModel` over the union of the two
lace-derived ratifier pools EXISTS. Works for the opaque `Committed.some` observers, because it
only ever uses that a ratifier set is drawn from its node's participants. -/
noncomputable def crossNodeBftOfCommitted
    (cfg : Finality.Config) {S₁ S₂ : CordialState} {l₁ l₂ : Block}
    (c₁ : Committed S₁ cfg l₁) (c₂ : Committed S₂ cfg l₂)
    (hid : l₂.id = l₁.id)
    (Byz : Nat → Prop) [inst : DecidablePred Byz]
    (hthr : cfg.n > 3 * cfg.f)
    (hcard : ((S₁.participants ++ S₂.participants).toFinset).card ≤ cfg.n)
    (hfault : (((S₁.participants ++ S₂.participants).toFinset).filter
        (fun v => Byz v)).card ≤ cfg.f) :
    BFTModel cfg
      ((SuperRatification.ofLace c₁.some).votes ++ (SuperRatification.ofLace c₂.some).votes) := by
  classical
  -- whatever observers `Committed.some` picked, their ratifier sets live in the participant lists.
  have hP : ∀ b : Nat,
      votersFor ((SuperRatification.ofLace c₁.some).votes
        ++ (SuperRatification.ofLace c₂.some).votes) b
        ⊆ S₁.participants ++ S₂.participants := by
    intro b x hx
    have hsub := votersFor_union_subset
      (S₁.ratifyingVoters c₁.some.observer l₁) (S₂.ratifyingVoters c₂.some.observer l₂)
      l₁.id l₂.id b hx
    rcases List.mem_append.mp hsub with h | h
    · exact List.mem_append_left _ (ratifyingVoters_subset_participants S₁ _ _ h)
    · exact List.mem_append_right _ (ratifyingVoters_subset_participants S₂ _ _ h)
  have hUnion : ∀ b₁ b₂ : Nat,
      ((votersFor ((SuperRatification.ofLace c₁.some).votes
          ++ (SuperRatification.ofLace c₂.some).votes) b₁).toFinset
        ∪ (votersFor ((SuperRatification.ofLace c₁.some).votes
          ++ (SuperRatification.ofLace c₂.some).votes) b₂).toFinset)
        ⊆ (S₁.participants ++ S₂.participants).toFinset := by
    intro b₁ b₂ x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact List.mem_toFinset.mpr (hP b₁ (List.mem_toFinset.mp h))
    · exact List.mem_toFinset.mpr (hP b₂ (List.mem_toFinset.mp h))
  exact
    { Byzantine := Byz
      byzantineDec := inst
      bft_threshold := hthr
      population_bound := fun b₁ b₂ => le_trans (Finset.card_le_card (hUnion b₁ b₂)) hcard
      fault_bound := fun b₁ b₂ =>
        le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (hUnion b₁ b₂))) hfault
      honest_vote_once := by
        -- every materialized vote endorses `l₁.id` (= `l₂.id`), so any voted-for id IS that id.
        intro v b₁ b₂ _ hv1 hv2
        have h1 := block_of_voter_union hv1
        have h2 := block_of_voter_union hv2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2, hid] }

/-! ## §4. THE CHAIN-LEVEL APEX — no two honest nodes finalize conflicting histories.

A node's FINALIZED HISTORY is its wave-indexed sequence of committed leaders (the `tauOrder`
anchors, keyed by wave). Two histories CONFLICT iff they disagree on the leader of some common
wave. The apex: under the per-wave cross-node witness (each node committed its leader + the
cross-node honest-majority BFT model), the histories are CONSISTENT — never disagree. A light
client following either node's finalized chain lands on the same history. -/

/-- A node's finalized history: per wave index, the leader block it committed (the `tauOrder`
anchors — since `d182d10fc`, the ratified-leader chain walked back from `lastFinalLeader`'s
head, keyed by wave; `findAllFinalLeaders` supplies only the head). -/
abbrev FinalizedHistory := List (Nat × Block)

/-- The leader a history finalized at wave `w` (the first entry tagged `w`, if any). -/
def leaderAtWave (h : FinalizedHistory) (w : Nat) : Option Block :=
  (h.find? (fun e => e.1 == w)).map (·.2)

/-- **`Consistent h₁ h₂`** — two finalized histories never disagree at a common wave. This is
the chain-level "no fork": both nodes' canonical chains coincide wherever both have finalized. -/
def Consistent (h₁ h₂ : FinalizedHistory) : Prop :=
  ∀ w l₁ l₂, leaderAtWave h₁ w = some l₁ → leaderAtWave h₂ w = some l₂ → l₁ = l₂

/-- **`CrossNodeWitness`** — the per-wave evidence the chain apex consumes for a common wave:
both nodes committed their leader (`Committed`, quorum read off the lace), the cross-node BFT
honest-majority model over the materialized union pool, and id-determinism. This bundles exactly
the carriers named in the header — no `axiom`. -/
structure CrossNodeWitness (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block) where
  /-- Node 1's lace exhibits the ratifying quorum for `l₁`. -/
  committed₁ : Committed S₁ cfg l₁
  /-- Node 2's lace exhibits the ratifying quorum for `l₂`. -/
  committed₂ : Committed S₂ cfg l₂
  /-- The honest-majority `n > 3f` BFT model over the UNION of the two lace-derived ratifier
  pools (the carrier — its fields, not `axiom`s). -/
  bft : BFTModel cfg
    ((SuperRatification.ofLace committed₁.some).votes
      ++ (SuperRatification.ofLace committed₂.some).votes)
  /-- **CROSS-NODE content-addressing at the anchor pair.** `l₁` is node 1's anchor and `l₂` is
  node 2's, so the assumption that pins them is `CrossNodeCanonical S₁ S₂` restricted to this
  pair (`CrossNodeCanonical.leaderIdPins`), NOT `Lace.Canonical` of either node's lace — this
  field's docstring said the latter until 2026-07-28 and `Model.crossNodeCanonical_is_the_gap`
  refutes it. -/
  hid_inj : LeaderIdPins l₁ l₂

/-- A `CrossNodeWitness` forces the two nodes' leaders equal (it is §3 packaged). -/
theorem CrossNodeWitness.agree
    {cfg : Finality.Config} {S₁ S₂ : CordialState} {l₁ l₂ : Block}
    (W : CrossNodeWitness cfg S₁ S₂ l₁ l₂) : l₁ = l₂ :=
  cross_node_agreement_from_lace cfg S₁ S₂ l₁ l₂ W.committed₁ W.committed₂ W.bft W.hid_inj

/-- **`no_conflicting_finalized_history` — chain safety in the PER-PAIR WITNESS form.** If, at
every wave both histories finalized, a `CrossNodeWitness` holds (both nodes committed + the
union honest-majority BFT model + cross-node content-addressing at that pair), then the two
histories are CONSISTENT: they never disagree on a finalized wave's leader.

⚑ **Read the hypothesis literally: this statement does NOT tie `hᵢ` to `Sᵢ`.** Nothing here says
`h₁` is the history node 1 finalized — the states enter only through the witness supplier. The
theorem is true and useful (`Model.apex_fires_on_two_nodes` runs it on the exhibited witness),
but the sentence "two honest nodes' finalized histories never disagree" is carried by
`no_conflicting_finalized_history_of_committed` below, which does carry the tie. Cite THAT as
the apex. -/
theorem no_conflicting_finalized_history
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (h₁ h₂ : FinalizedHistory)
    (W : ∀ w l₁ l₂, leaderAtWave h₁ w = some l₁ → leaderAtWave h₂ w = some l₂ →
          CrossNodeWitness cfg S₁ S₂ l₁ l₂) :
    Consistent h₁ h₂ := by
  intro w l₁ l₂ hw1 hw2
  exact (W w l₁ l₂ hw1 hw2).agree

/-! ### §4b. The apex with the histories TIED TO THE NODES.

`no_conflicting_finalized_history` takes `S₁ S₂ : CordialState` and `h₁ h₂ : FinalizedHistory`
and NEVER RELATES THEM: nothing says `h₁` is the history node 1 finalized. Read literally it is a
statement about two arbitrary lists whose every compared pair happens to come with a witness. The
prose ("two honest nodes with laces `S₁, S₂` and finalized histories `h₁, h₂`") claimed the tie;
the statement did not carry it.

`FinalizedBy` carries it: every leader the history lists at a wave is a block the node ACTUALLY
COMMITTED off its own lace. With the tie in place the per-pair `hid_inj` dissolves into ONE
lace-level `CrossNodeCanonical S₁ S₂` — membership of each anchor in its own lace is *derived*
from the commit fact (`committed_mem_lace`), not assumed. -/

/-- **`FinalizedBy S cfg h`** — `h` is the history THIS node finalized: every leader it lists at
a wave is `Committed` on `S`'s own lace (the `≥ n − f` ratifier read, `findAllFinalLeaders`
pushing the block onto `final_leaders`). -/
def FinalizedBy (S : CordialState) (cfg : Finality.Config) (h : FinalizedHistory) : Prop :=
  ∀ w l, leaderAtWave h w = some l → Committed S cfg l

/-- Reading a leader off a history means the `(wave, leader)` pair IS in the list — the bridge
between `leaderAtWave` and the concrete histories the model exhibits. -/
theorem leaderAtWave_mem {h : FinalizedHistory} {w : Nat} {l : Block}
    (hl : leaderAtWave h w = some l) : (w, l) ∈ h := by
  unfold leaderAtWave at hl
  cases he : h.find? (fun e => e.1 == w) with
  | none => rw [he] at hl; simp at hl
  | some e =>
    rw [he] at hl
    simp only [Option.map_some, Option.some_inj] at hl
    have hp := List.find?_some he
    simp only [beq_iff_eq] at hp
    have hpair : (w, l) = e := by rw [← hp, ← hl]
    rw [hpair]
    exact List.mem_of_find?_eq_some he

/-- **`no_conflicting_finalized_history_of_committed` — THE APEX, HISTORIES TIED TO NODES.**
Two nodes, each history being the one that node actually finalized (`FinalizedBy`), a shared
`n > 3f` config, ONE cross-node content-addressing assumption at the lace level, and the
cross-node BFT model for the pairs actually compared. Conclusion: the two finalized histories
never disagree — no fork a light client can be split across.

Against the older apex this (i) TIES `hᵢ` to `Sᵢ`, which the older statement did not, and
(ii) replaces the per-pair `hid_inj` by the single named `CrossNodeCanonical S₁ S₂`, with each
anchor's lace-membership DERIVED from its commit fact. Its carriers are strictly the header's
three, stated once each. -/
theorem no_conflicting_finalized_history_of_committed
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (h₁ h₂ : FinalizedHistory)
    (hthr : cfg.n > 3 * cfg.f)
    (F₁ : FinalizedBy S₁ cfg h₁) (F₂ : FinalizedBy S₂ cfg h₂)
    (hcanon : CrossNodeCanonical S₁ S₂)
    (bft : ∀ w l₁ l₂, leaderAtWave h₁ w = some l₁ → leaderAtWave h₂ w = some l₂ →
      ∀ (c₁ : Committed S₁ cfg l₁) (c₂ : Committed S₂ cfg l₂),
        BFTModel cfg ((SuperRatification.ofLace c₁.some).votes
          ++ (SuperRatification.ofLace c₂.some).votes)) :
    Consistent h₁ h₂ := by
  intro w l₁ l₂ hw1 hw2
  have c₁ := F₁ w l₁ hw1
  have c₂ := F₂ w l₂ hw2
  have hpos : 0 < cfg.n - cfg.f := quorum_pos_of_threshold hthr
  exact cross_node_agreement_from_lace cfg S₁ S₂ l₁ l₂ c₁ c₂ (bft w l₁ l₂ hw1 hw2 c₁ c₂)
    (hcanon.leaderIdPins (committed_mem_lace hpos c₁) (committed_mem_lace hpos c₂))

/-! ## §5. Non-vacuity — the kernel APPLIES, and `Consistent` is genuinely two-sided.

Per the "don't launder vacuity" discipline: we exhibit (i) the §1 kernel firing on the minimal
BFT config (so `quorum_pair_agreement`'s hypotheses are jointly satisfiable, the conclusion not
vacuous), and (ii) `Consistent` holding on agreeing histories AND FAILING on conflicting ones
(so the predicate is non-trivial — true and false). -/

namespace NonVacuity

/-- The minimal BFT config `n = 4, f = 1` (`n = 3f + 1`). -/
def cfg : Finality.Config := ⟨4, 1, 3⟩

/-- Node 1's pool and node 2's pool BOTH carry three honest ratifiers for block 7 (the agreeing
case: same participant universe `{0,1,2}`, no equivocation). -/
def v1 : List Vote := [⟨0, 7⟩, ⟨1, 7⟩, ⟨2, 7⟩]
def v2 : List Vote := [⟨0, 7⟩, ⟨1, 7⟩, ⟨2, 7⟩]

/-- The empty-adversary model over the UNION pool inhabits `BFTModel` — the §1 kernel's
hypotheses are jointly satisfiable, so `quorum_pair_agreement` is non-vacuous. -/
def unionModel : BFTModel cfg (v1 ++ v2) where
  Byzantine := fun _ => False
  byzantineDec := fun _ => inferInstanceAs (Decidable False)
  fault_bound := by intro b₁ b₂; simp
  bft_threshold := by decide
  population_bound := by
    intro b₁ b₂
    have : ((votersFor (v1 ++ v2) b₁).toFinset ∪ (votersFor (v1 ++ v2) b₂).toFinset)
        ⊆ ({0, 1, 2} : Finset Nat) := by
      intro x hx
      simp only [Finset.mem_union, List.mem_toFinset, votersFor, v1, v2] at hx
      rcases hx with h | h <;>
        · simp only [List.mem_dedup, List.mem_map, List.mem_filter] at h
          obtain ⟨a, ⟨ha, _⟩, hav⟩ := h
          fin_cases ha <;> simp_all
    exact le_trans (Finset.card_le_card this) (by decide)
  honest_vote_once := by
    intro v b₁ b₂ _ hv1 hv2
    simp only [votersFor, v1, v2, List.mem_dedup, List.mem_map, List.mem_filter] at hv1 hv2
    obtain ⟨a, ⟨ha, hab1⟩, _⟩ := hv1
    obtain ⟨c, ⟨hc, hcb2⟩, _⟩ := hv2
    fin_cases ha <;> fin_cases hc <;>
      simp only [decide_eq_true_eq] at hab1 hcb2 <;> omega

/-- The §1 kernel FIRES on the inhabited model: both pools' block ids agree. (Confirms the
hypotheses are jointly satisfiable; the conclusion `b1 = b2` is reached, not vacuous.) -/
example (b1 b2 : Nat)
    (hq1 : cfg.n - cfg.f ≤ (votersFor v1 b1).length)
    (hq2 : cfg.n - cfg.f ≤ (votersFor v2 b2).length)
    (honest_one : ∀ v : Nat, ¬ unionModel.Byzantine v →
        v ∈ votersFor (v1 ++ v2) b1 → v ∈ votersFor (v1 ++ v2) b2 → b1 = b2) :
    b1 = b2 :=
  quorum_pair_agreement cfg v1 v2 b1 b2 hq1 hq2 unionModel honest_one

/-- Two minimal leader blocks (distinct ids). -/
def blkA : Block := ⟨7, 1, 0, [], true⟩
def blkB : Block := ⟨8, 1, 0, [], true⟩

/-- `Consistent` holds on agreeing histories (the TRUE side): both reads hit the same list, so
the two leaders coincide. -/
example : Consistent [(0, blkA)] [(0, blkA)] := by
  intro w l₁ l₂ hw1 hw2
  exact Option.some_inj.mp (hw1.symm.trans hw2)

/-- `Consistent` FAILS on conflicting histories (the FALSE side — the predicate is non-trivial,
it genuinely detects a fork). -/
example : ¬ Consistent [(0, blkA)] [(0, blkB)] := by
  intro h
  have hc := h 0 blkA blkB rfl rfl
  simp [blkA, blkB] at hc

end NonVacuity

/-! ## §5b. THE MODEL — two real nodes, a real `CrossNodeWitness`, and the tooth.

§5 above shows the §1 kernel firing and `Consistent` being two-sided. Neither of those touches
the apex's hypothesis, and until 2026-07-28 `CrossNodeWitness` was inhabited NOWHERE IN THE
TREE — so `no_conflicting_finalized_history` proved nothing about anything. This section closes
that, on the three-arm discipline (`feedback-prove-the-floor-false`):

* **SATISFIABLE** — `crossWitness` is a `CrossNodeWitness` at two nodes holding GENUINELY
  DIFFERENT laces (`node1_lace_ne_node2`; neither view holds the other's wave-end observer), each
  committing the wave-0 leader off its OWN blocks, with a cross-node BFT model carrying an actual
  Byzantine ratifier at the `f = 1` budget. `apex_fires_on_two_nodes` and
  `tied_apex_fires_on_two_nodes` run the two apexes on it.
* **REFUTABLE, and the refutation is the mis-attribution's counterexample** —
  `crossNodeCanonical_is_the_gap`: node 1 and a forked node whose laces are EACH
  `Lace.Canonical`, which each genuinely `Committed` a wave-0 leader off their own blocks, which
  share a cross-node BFT model — and whose anchors are DIFFERENT BLOCKS AT THE SAME
  CONTENT-ADDRESS (`signed` flipped, one bit). `CrossNodeCanonical` fails, `LeaderIdPins` fails
  with it, `Consistent` FAILS, and no `CrossNodeWitness` exists for that pair. Per-lace
  canonicity does NOT rescue chain safety, which is exactly what the old doc-comment claimed.
* **Therefore NOT PROVABLE**, and decidable: a node can CHECK `CrossNodeCanonical` against a
  peer's blocks (`decidableCrossNodeCanonical`).

The two nodes reuse `Proof.CordialMiners.Inhabited`'s lace — the leader strand `rg0 ≺ rg1`, the
three approvers `ra0/ra1/ra2` — and differ in their wave-end observer, which is what "two honest
nodes with different partial views" means concretely. -/

namespace Model

open Dregg2.Authority.Blocklace
open Dregg2.Proof.CordialMiners.Inhabited
  (cfg rg0 rg1 ra0 ra1 ra2 ro ratLace g1_committed p2_ratifies)

/-- **Node 1** IS the `CordialMiners` fixture node: lace `ratLace`, wave-end observer `ro`
(author 0), leader `rg1` committed with the quorum read off its own blocks. -/
abbrev node1 : CordialState := Dregg2.Proof.CordialMiners.Inhabited.state

/-! ### Node 2 — the same leader strand, its OWN wave-end observer. -/

/-- **Node 2's wave-end observer** (author 1, id 121): a DIFFERENT block from node 1's `ro`.
Node 2 never received `ro`, node 1 never received `ro2` — the partial-view asymmetry is
two-sided, so neither node's lace contains the other's. -/
def ro2 : Block := { id := 121, creator := 1, seq := 1, preds := [110, 111, 112] }

/-- **Node 2's lace.** -/
def lace2 : Lace := [rg0, rg1, ra0, ra1, ra2, ro2]

/-- **Node 2** — the second honest node, same participants and wavelength, different view. -/
def node2 : CordialState where
  lace := lace2
  rounds := fun id =>
    if id = rg0.id then 1
    else if id = rg1.id then 2
    else if id = ro2.id then 4
    else 3
  participants := [7, 0, 1, 2]
  wavelength := 3

/-- Author 7 is honest on node 2's lace too (`rg0 ≺ rg1`), so the approval guard holds there. -/
theorem lace2_author7_honest : HonestChain lace2 7 := by
  intro a b ha hb hpa hpb hne
  have hbase : ∀ x : Block, lace2.lookup x.id = some x → x.creator = 7 → x = rg0 ∨ x = rg1 := by
    intro x hx hcr
    have hxmem : x ∈ lace2 := List.mem_of_find?_eq_some hx
    simp only [lace2, List.mem_cons, List.not_mem_nil, or_false] at hxmem
    rcases hxmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hcr (by decide)
    · exact absurd hcr (by decide)
    · exact absurd hcr (by decide)
    · exact absurd hcr (by decide)
  have hpre : precedes lace2 rg0 rg1 := .base ⟨by decide, by decide, by decide⟩
  rcases hbase a ha hpa with rfl | rfl <;> rcases hbase b hb hpb with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl hpre
  · exact Or.inr hpre
  · exact absurd rfl hne

theorem lace2_author7_no_equiv : ¬ Equivocator lace2 7 :=
  honest_no_equivocation lace2_author7_honest

theorem ra0_approves2 : node2.approves ra0 rg1 :=
  ⟨Or.inr (.base ⟨by decide, by decide, by decide⟩), lace2_author7_no_equiv⟩
theorem ra1_approves2 : node2.approves ra1 rg1 :=
  ⟨Or.inr (.base ⟨by decide, by decide, by decide⟩), lace2_author7_no_equiv⟩
theorem ra2_approves2 : node2.approves ra2 rg1 :=
  ⟨Or.inr (.base ⟨by decide, by decide, by decide⟩), lace2_author7_no_equiv⟩

theorem ra0_pre_ro2 : precedes node2.lace ra0 ro2 := .base ⟨by decide, by decide, by decide⟩
theorem ra1_pre_ro2 : precedes node2.lace ra1 ro2 := .base ⟨by decide, by decide, by decide⟩
theorem ra2_pre_ro2 : precedes node2.lace ra2 ro2 := .base ⟨by decide, by decide, by decide⟩

theorem p0_ratifies2 : node2.HasApprovingBlock ro2 rg1 0 :=
  ⟨ra0, by decide, by decide, Or.inr ra0_pre_ro2, ra0_approves2⟩
theorem p1_ratifies2 : node2.HasApprovingBlock ro2 rg1 1 :=
  ⟨ra1, by decide, by decide, Or.inr ra1_pre_ro2, ra1_approves2⟩
theorem p2_ratifies2 : node2.HasApprovingBlock ro2 rg1 2 :=
  ⟨ra2, by decide, by decide, Or.inr ra2_pre_ro2, ra2_approves2⟩

/-- **Node 2's quorum, READ OFF NODE 2's OWN LACE** — three distinct ratifiers at `ro2`. -/
theorem quorum_from_lace2 : cfg.n - cfg.f ≤ (node2.ratifyingVoters ro2 rg1).length := by
  classical
  have hmem : ∀ p ∈ ([0, 1, 2] : List AuthorId), p ∈ node2.ratifyingVoters ro2 rg1 := by
    intro p hp
    unfold CordialState.ratifyingVoters
    rw [List.mem_dedup, List.mem_filter]
    fin_cases hp
    · exact ⟨by decide, by simpa using decide_eq_true p0_ratifies2⟩
    · exact ⟨by decide, by simpa using decide_eq_true p1_ratifies2⟩
    · exact ⟨by decide, by simpa using decide_eq_true p2_ratifies2⟩
  have hsub : ([0, 1, 2] : List AuthorId) ⊆ node2.ratifyingVoters ro2 rg1 := fun p hp => hmem p hp
  have hnd : ([0, 1, 2] : List AuthorId).Nodup := by decide
  have h3 : (3 : Nat) = ([0, 1, 2] : List AuthorId).length := by decide
  rw [show cfg.n - cfg.f = 3 from by decide, h3]
  exact (hnd.subperm hsub).length_le

/-- Node 2's lace-derived super-ratification of `rg1`. -/
def sr2 : superRatifiedFromLace node2 cfg rg1 where
  observer := ro2
  observer_mem := by decide
  quorum_from_lace := quorum_from_lace2
  unique_leader := by
    intro b hb hcreator hround
    have hbmem : b ∈ lace2 := hb
    simp only [lace2, List.mem_cons, List.not_mem_nil, or_false] at hbmem
    rcases hbmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso; revert hround; decide
    · rfl
    · exact absurd hcreator (by decide)
    · exact absurd hcreator (by decide)
    · exact absurd hcreator (by decide)
    · exact absurd hcreator (by decide)

/-- **Node 2 committed `rg1`** — off its own blocks, not node 1's. -/
theorem node2_commits : Committed node2 cfg rg1 := ⟨sr2⟩

/-! ### The two views are genuinely different, and cross-node canonical. -/

/-- The two nodes hold DIFFERENT laces — this is not one node compared with itself. -/
theorem node1_lace_ne_node2 : node1.lace ≠ node2.lace := by decide
/-- Node 1's wave-end observer is absent from node 2's view … -/
theorem ro_not_in_node2 : ro ∉ node2.lace := by decide
/-- … and node 2's is absent from node 1's. The partial-view gap is two-sided. -/
theorem ro2_not_in_node1 : ro2 ∉ node1.lace := by decide

/-- **SATISFIABLE — cross-node canonicity HOLDS between the two honest views**, DECIDED on the
real block lists. The carrier the apex rests on is checkable and met here. -/
theorem crossCanonical_nodes : CrossNodeCanonical node1 node2 := by decide

/-- **THE INHABITANT — a real `CrossNodeWitness`.** Two nodes, two different laces, each
committing the wave-0 leader off its own blocks; the BFT carrier CONSTRUCTED by
`crossNodeBftOfCommitted` with participant 2 actually Byzantine (the `f = 1` budget spent, not a
vacuous empty adversary); id-determinism DERIVED from the decided `crossCanonical_nodes` rather
than asserted. No field is assumed. -/
noncomputable def crossWitness : CrossNodeWitness cfg node1 node2 rg1 rg1 where
  committed₁ := g1_committed
  committed₂ := node2_commits
  bft := crossNodeBftOfCommitted cfg g1_committed node2_commits rfl (fun p => p = 2)
    (by decide) (by decide) (by decide)
  hid_inj := crossCanonical_nodes.leaderIdPins (by decide) (by decide)

/-- Participant 2 — the one `crossWitness`'s model calls Byzantine — IS a real ratifier on BOTH
nodes' laces. So the `f = 1` adversary budget is genuinely SPENT: the witness does not smuggle in
the empty-adversary model that §5's `unionModel` uses. -/
theorem byzantine_is_a_real_ratifier :
    (2 : AuthorId) ∈ node1.ratifyingVoters ro rg1
      ∧ (2 : AuthorId) ∈ node2.ratifyingVoters ro2 rg1 := by
  classical
  constructor
  · unfold CordialState.ratifyingVoters
    rw [List.mem_dedup, List.mem_filter]
    exact ⟨by decide, by simpa using decide_eq_true p2_ratifies⟩
  · unfold CordialState.ratifyingVoters
    rw [List.mem_dedup, List.mem_filter]
    exact ⟨by decide, by simpa using decide_eq_true p2_ratifies2⟩

/-- **The witness is NON-DEGENERATE**, in one statement: the two nodes' laces DIFFER, the
difference is two-sided (neither holds the other's wave-end observer), each node's commit is read
off its OWN lace, and the adversary budget is spent on a real ratifier. -/
theorem crossWitness_nondegenerate :
    node1.lace ≠ node2.lace
    ∧ ro ∉ node2.lace ∧ ro2 ∉ node1.lace
    ∧ Committed node1 cfg rg1 ∧ Committed node2 cfg rg1
    ∧ (2 : AuthorId) ∈ node1.ratifyingVoters ro rg1
    ∧ (2 : AuthorId) ∈ node2.ratifyingVoters ro2 rg1 :=
  ⟨node1_lace_ne_node2, ro_not_in_node2, ro2_not_in_node1, g1_committed, node2_commits,
    byzantine_is_a_real_ratifier.1, byzantine_is_a_real_ratifier.2⟩

/-- Reading a wave off a one-entry history pins the leader. -/
theorem leaderAtWave_singleton {w : Nat} {b l : Block}
    (h : leaderAtWave [(0, b)] w = some l) : l = b := by
  have hm := leaderAtWave_mem h
  simp only [List.mem_singleton, Prod.mk.injEq] at hm
  exact hm.2

/-- **THE APEX FIRES ON REAL DATA.** `no_conflicting_finalized_history` applied to the exhibited
witness.

⚑ Say what this does and does not show. At an AGREEING trace the CONCLUSION `Consistent h h` is
reflexively true and proves nothing on its own — the content is entirely in the PROOF TERM: the
apex's premise is discharged by `crossWitness`, a real inhabitant, so the apex is no longer a
statement about an empty hypothesis. That `Consistent` is not itself trivial is witnessed
separately, on both sides: `NonVacuity` refutes it on conflicting histories, and
`crossNodeCanonical_is_the_gap` refutes it at a trace where both nodes genuinely committed. -/
theorem apex_fires_on_two_nodes : Consistent [(0, rg1)] [(0, rg1)] :=
  no_conflicting_finalized_history cfg node1 node2 [(0, rg1)] [(0, rg1)]
    (fun _ _ _ hw1 hw2 => by
      obtain rfl := leaderAtWave_singleton hw1
      obtain rfl := leaderAtWave_singleton hw2
      exact crossWitness)

/-- Node 1's finalized history is genuinely node 1's: its wave-0 entry is a block node 1
committed off its own lace. -/
theorem finalizedBy_node1 : FinalizedBy node1 cfg [(0, rg1)] := by
  intro _ l hl
  obtain rfl := leaderAtWave_singleton hl
  exact g1_committed

/-- Same for node 2, against node 2's lace. -/
theorem finalizedBy_node2 : FinalizedBy node2 cfg [(0, rg1)] := by
  intro _ l hl
  obtain rfl := leaderAtWave_singleton hl
  exact node2_commits

/-- **THE TIED APEX FIRES TOO** — same reading as `apex_fires_on_two_nodes`: the value is the
discharged premise, not the reflexive conclusion. Here EVERY hypothesis is met by a proved fact
about the two real nodes — `FinalizedBy` from their own commits, `CrossNodeCanonical` decided on
their blocks, and the BFT carrier built generically by `crossNodeBftOfCommitted`. Nothing is
assumed. -/
theorem tied_apex_fires_on_two_nodes : Consistent [(0, rg1)] [(0, rg1)] :=
  no_conflicting_finalized_history_of_committed cfg node1 node2 [(0, rg1)] [(0, rg1)]
    (by decide) finalizedBy_node1 finalizedBy_node2 crossCanonical_nodes
    (fun _ _ _ hw1 hw2 c₁ c₂ => by
      obtain rfl := leaderAtWave_singleton hw1
      obtain rfl := leaderAtWave_singleton hw2
      exact crossNodeBftOfCommitted cfg c₁ c₂ rfl (fun p => p = 2)
        (by decide) (by decide) (by decide))

/-! ### THE TOOTH — the same setup with ONE BIT flipped at the leader's content-address.

`rg1Forged` is the leader block at address `101` with `signed := false`. A node whose gossip
delivered the forged strand builds a lace that is INTERNALLY content-addressed, ratifies the
block it holds, and commits it. Everything the apex asks for is present on both sides EXCEPT
cross-node canonicity — and the two finalized histories disagree at wave 0. -/

/-- **`rg1Forged`** — the wave-0 leader at THE SAME content-address `101`, one bit different
(`signed := false`). The consensus-anchor twin of `LaceMerge`'s `b0Forged`. -/
def rg1Forged : Block := { id := 101, creator := 7, seq := 1, preds := [100], signed := false }

/-- The forked node's lace: the forged leader in place of `rg1`, same approvers, same observer
as node 2. It is internally content-addressed — the forgery is invisible from inside. -/
def forkLace : Lace := [rg0, rg1Forged, ra0, ra1, ra2, ro2]

/-- **The forked node** — an honest node whose gossip delivered the forged strand. -/
def forkNode : CordialState where
  lace := forkLace
  rounds := fun id =>
    if id = rg0.id then 1
    else if id = rg1Forged.id then 2
    else if id = ro2.id then 4
    else 3
  participants := [7, 0, 1, 2]
  wavelength := 3

theorem forkLace_author7_honest : HonestChain forkLace 7 := by
  intro a b ha hb hpa hpb hne
  have hbase : ∀ x : Block, forkLace.lookup x.id = some x → x.creator = 7 →
      x = rg0 ∨ x = rg1Forged := by
    intro x hx hcr
    have hxmem : x ∈ forkLace := List.mem_of_find?_eq_some hx
    simp only [forkLace, List.mem_cons, List.not_mem_nil, or_false] at hxmem
    rcases hxmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hcr (by decide)
    · exact absurd hcr (by decide)
    · exact absurd hcr (by decide)
    · exact absurd hcr (by decide)
  have hpre : precedes forkLace rg0 rg1Forged := .base ⟨by decide, by decide, by decide⟩
  rcases hbase a ha hpa with rfl | rfl <;> rcases hbase b hb hpb with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl hpre
  · exact Or.inr hpre
  · exact absurd rfl hne

theorem forkLace_author7_no_equiv : ¬ Equivocator forkLace 7 :=
  honest_no_equivocation forkLace_author7_honest

theorem ra0_approvesF : forkNode.approves ra0 rg1Forged :=
  ⟨Or.inr (.base ⟨by decide, by decide, by decide⟩), forkLace_author7_no_equiv⟩
theorem ra1_approvesF : forkNode.approves ra1 rg1Forged :=
  ⟨Or.inr (.base ⟨by decide, by decide, by decide⟩), forkLace_author7_no_equiv⟩
theorem ra2_approvesF : forkNode.approves ra2 rg1Forged :=
  ⟨Or.inr (.base ⟨by decide, by decide, by decide⟩), forkLace_author7_no_equiv⟩

theorem ra0_pre_roF : precedes forkNode.lace ra0 ro2 := .base ⟨by decide, by decide, by decide⟩
theorem ra1_pre_roF : precedes forkNode.lace ra1 ro2 := .base ⟨by decide, by decide, by decide⟩
theorem ra2_pre_roF : precedes forkNode.lace ra2 ro2 := .base ⟨by decide, by decide, by decide⟩

theorem p0_ratifiesF : forkNode.HasApprovingBlock ro2 rg1Forged 0 :=
  ⟨ra0, by decide, by decide, Or.inr ra0_pre_roF, ra0_approvesF⟩
theorem p1_ratifiesF : forkNode.HasApprovingBlock ro2 rg1Forged 1 :=
  ⟨ra1, by decide, by decide, Or.inr ra1_pre_roF, ra1_approvesF⟩
theorem p2_ratifiesF : forkNode.HasApprovingBlock ro2 rg1Forged 2 :=
  ⟨ra2, by decide, by decide, Or.inr ra2_pre_roF, ra2_approvesF⟩

/-- The forked node's quorum is a genuine lace read — the forgery is ratified by three distinct
participants on ITS view. Nothing about this node is degenerate. -/
theorem quorum_from_laceF : cfg.n - cfg.f ≤ (forkNode.ratifyingVoters ro2 rg1Forged).length := by
  classical
  have hmem : ∀ p ∈ ([0, 1, 2] : List AuthorId), p ∈ forkNode.ratifyingVoters ro2 rg1Forged := by
    intro p hp
    unfold CordialState.ratifyingVoters
    rw [List.mem_dedup, List.mem_filter]
    fin_cases hp
    · exact ⟨by decide, by simpa using decide_eq_true p0_ratifiesF⟩
    · exact ⟨by decide, by simpa using decide_eq_true p1_ratifiesF⟩
    · exact ⟨by decide, by simpa using decide_eq_true p2_ratifiesF⟩
  have hsub : ([0, 1, 2] : List AuthorId) ⊆ forkNode.ratifyingVoters ro2 rg1Forged :=
    fun p hp => hmem p hp
  have hnd : ([0, 1, 2] : List AuthorId).Nodup := by decide
  have h3 : (3 : Nat) = ([0, 1, 2] : List AuthorId).length := by decide
  rw [show cfg.n - cfg.f = 3 from by decide, h3]
  exact (hnd.subperm hsub).length_le

def srF : superRatifiedFromLace forkNode cfg rg1Forged where
  observer := ro2
  observer_mem := by decide
  quorum_from_lace := quorum_from_laceF
  unique_leader := by
    intro b hb hcreator hround
    have hbmem : b ∈ forkLace := hb
    simp only [forkLace, List.mem_cons, List.not_mem_nil, or_false] at hbmem
    rcases hbmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso; revert hround; decide
    · rfl
    · exact absurd hcreator (by decide)
    · exact absurd hcreator (by decide)
    · exact absurd hcreator (by decide)
    · exact absurd hcreator (by decide)

/-- **The forked node COMMITS the forgery** — a real `Committed`, quorum read off its own lace. -/
theorem forkNode_commits : Committed forkNode cfg rg1Forged := ⟨srF⟩

/-- Node 1's lace is internally content-addressed. -/
theorem node1_lace_canonical : node1.lace.Canonical := by unfold Lace.Canonical; decide
/-- So is the forked node's — the forgery is invisible from inside a single view. -/
theorem forkNode_lace_canonical : forkNode.lace.Canonical := by unfold Lace.Canonical; decide

/-- **The cross-node BFT carrier is inhabited AT THE FORK TOO** — so what fails below is NOT the
honest-majority model. Both anchors share the id `101`, which is exactly the collision. -/
noncomputable def forkBft : BFTModel cfg
    ((SuperRatification.ofLace (g1_committed).some).votes
      ++ (SuperRatification.ofLace forkNode_commits.some).votes) :=
  crossNodeBftOfCommitted cfg g1_committed forkNode_commits rfl (fun p => p = 2)
    (by decide) (by decide) (by decide)

/-- **`crossNodeCanonical_is_the_gap` — THE TOOTH.** Everything the chain-safety apex asks for is
present on both sides: each node's lace is `Lace.Canonical`, each node genuinely `Committed` its
wave-0 leader off its own blocks, and they share a cross-node honest-majority BFT model. The ONE
thing that fails is `CrossNodeCanonical` — and with it `LeaderIdPins`, the `CrossNodeWitness`,
and `Consistent`. The two nodes finalize DIFFERENT BLOCKS at the SAME wave, and a light client
following either is on a different chain.

So: per-lace `Lace.Canonical` does NOT give chain safety, which is precisely what the `hid_inj`
doc-comments claimed until 2026-07-28. The assumption is CROSS-node, it is load-bearing, it is
refutable, and it is therefore not provable — an assumption, and now a checkable one. -/
theorem crossNodeCanonical_is_the_gap :
    node1.lace.Canonical
    ∧ forkNode.lace.Canonical
    ∧ Committed node1 cfg rg1
    ∧ Committed forkNode cfg rg1Forged
    ∧ Nonempty (BFTModel cfg
        ((SuperRatification.ofLace (g1_committed).some).votes
          ++ (SuperRatification.ofLace forkNode_commits.some).votes))
    ∧ ¬ CrossNodeCanonical node1 forkNode
    ∧ ¬ LeaderIdPins rg1 rg1Forged
    ∧ ¬ Nonempty (CrossNodeWitness cfg node1 forkNode rg1 rg1Forged)
    ∧ ¬ Consistent [(0, rg1)] [(0, rg1Forged)] :=
  ⟨node1_lace_canonical, forkNode_lace_canonical, g1_committed, forkNode_commits, ⟨forkBft⟩,
    by decide, by decide,
    (by rintro ⟨W⟩; exact absurd W.agree (by decide)),
    (by intro h; exact absurd (h 0 rg1 rg1Forged rfl rfl) (by decide))⟩

end Model

/-! ## §6. Axiom hygiene — every chain-safety keystone is kernel-clean.

All theorems reduce to `BFTModel` structure fields (carriers, not `axiom`s), the lace-read
`Committed`/`SuperRatification.ofLace` evidence, and `BFT.honest_witness_in_intersection`; none
pull any oracle axiom. -/
#assert_axioms quorum_pair_agreement
#assert_axioms cross_node_leader_agreement
#assert_axioms no_conflicting_cross_node_leader
#assert_axioms cross_node_leader_agreement_via_bft
#assert_axioms cross_node_agreement_from_lace
#assert_axioms CrossNodeWitness.agree
#assert_axioms no_conflicting_finalized_history
#assert_axioms CrossNodeCanonical.leaderIdPins
#assert_axioms crossNodeBftOfCommitted
#assert_axioms leaderAtWave_mem
#assert_axioms no_conflicting_finalized_history_of_committed
#assert_axioms Model.node2_commits
#assert_axioms Model.crossCanonical_nodes
#assert_axioms Model.crossWitness
#assert_axioms Model.crossWitness_nondegenerate
#assert_axioms Model.apex_fires_on_two_nodes
#assert_axioms Model.tied_apex_fires_on_two_nodes
#assert_axioms Model.forkNode_commits
#assert_axioms Model.crossNodeCanonical_is_the_gap

end Dregg2.Consensus.Safety
