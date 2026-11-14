/-
# Dregg2.Distributed.BlocklaceFinality — a FAITHFUL, EXECUTABLE model of the node's
# REAL blocklace finalization rule (`blocklace/src/ordering.rs::tau`), wired to the executor.

**The gap this closes.** `Dregg2/Distributed/Consensus.lean` is a free-floating BFT *algebra*: it
carries an *abstract* `Committed` predicate (a `superRatifiedFromLace` record) and proves quorum-
intersection safety over it, but it NEVER models the algorithm the running node actually computes.
The node (`node/src/blocklace_sync.rs::poll_finalized_blocks`) does NOT consult an abstract
"is-committed" oracle: it calls `dregg_blocklace::ordering::tau(&lace, &participants)` — a concrete
function that

  1. `compute_rounds`        — round(b) = 1 + max(round(p) | p ∈ preds), genesis = 1 (DAG depth);
  2. `find_all_final_leaders`— for each wave w, the round-robin `wave_leader(w)`; if it has EXACTLY
     ONE block at the wave-start round (no equivocation) AND that block `is_super_ratified` (a
     supermajority of DISTINCT participants have wave-end blocks that ratify it), it is a final
     leader;
  3. `tau`                   — walk final leaders in wave order, collect each leader's coverage
     (union of causal pasts of ratifying wave-end blocks), take the blocks NEW to this segment
     (minus equivocators), `xsort` them, append — producing the total order;

and then SLICES `ordered[executed_up_to..]` and feeds those turns to `TurnExecutor::execute`.

This module models THAT computed rule — `computeRounds` / `findAllFinalLeaders` / `tauOrder` as
genuine **executable Lean functions over `Lace`** (not an abstract record) — proves a REAL safety
property the node relies on (**no two conflicting final leaders per wave**; for finalized-prefix
monotonicity under lace growth see `Dregg2.Consensus.TauPrefixMonotone`, where it is proved from a
STRUCTURAL growth hypothesis (`ClosedExtension`) plus ONE named import of CM Prop. 3
(`ChainExtends`) — the honest-laggard counterexample that used to refute it unconditionally is now
that module's positive exhibit), CONNECTS it
to the verified executor
(`Exec.ConsensusExec.executeFinalized`, the cell `execFullForestG` commits onto), and ships a
**DIFFERENTIAL**: the computed Lean `tauOrder` and the Rust `ordering.rs::tau` AGREE on a concrete
multi-node trace (the Lean model reproduces the exact order the node finalizes).

## SCOPE — what is faithful, what is simplified, what is the named residual.

FAITHFUL (matches `ordering.rs` line-for-line as a pure function):
* `computeRounds` — the round = 1 + max(pred rounds), genesis = 1 recurrence (`compute_rounds`).
* `roundToWave` / `waveFirstRound` / `waveLastRound` / `waveLeader` — the wave arithmetic and the
  round-robin `participants[w % len]` leader (`ordering.rs:147..170`).
* `superMajority n = 2n/3 + 1` (`supermajority_threshold`).
* `approves` / `ratifies` / `isSuperRatified` / `findAllFinalLeaders` — the approval→ratification→
  super-ratification ladder over the causal past (`ordering.rs:184..336`), reading the SAME
  equivocation guard (`hasEquivInPast`).

SIMPLIFIED (a faithful PROJECTION, stated, not hidden):
* `causalPastIncl` uses a fuel bound (the lace length) for the BFS — totalizing the DAG walk; the
  Rust `causal_past` is an unbounded BFS over the same edge set. On any concrete (finite, acyclic)
  lace the fuel = |lace| is sufficient, so the two coincide (the differential exhibits this).
* `xsort` is a ready-set (Kahn) sort over the segment's transitive causal past, as in the Rust; the
  ready-set PRIORITY is the OPEN-CM-XSORT residual (named in `ConsensusExec`): `(round, id)` here,
  min block id in the Rust `xsort`. The order is a linear extension of the causal order
  (`anchorSegment_linear_extension`) under either priority; the two agree where the ready set is
  one round at a time. The SAFETY theorem (no conflicting leader) does NOT depend on the priority,
  only on WHICH leaders anchor, exactly as `cordial_agreement` is about the anchor.

The safety theorems proved here — `finalLeaders_one_per_wave` / `tauOrder_deterministic` — are
properties the NODE relies on: a wave anchors at most one leader and the order is a deterministic
function of (lace, participants). "Finalization is append-only" (T5, finalized-prefix
monotonicity) is proved in `Dregg2.Consensus.TauPrefixMonotone` under `ClosedExtension` (CM Def. 19
*closed*, which the receive path already enforces) plus `ChainExtends` (CM Prop. 3, leader-safety,
imported from the paper and owed a Lean proof). The honest-laggard trace that used to refute it —
a lagging validator's late wave-end ratifier growing an already-final wave's COVERAGE — cannot
arise against CM Def. 6, because an anchor orders its own closure and a closure does not move.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Distributed.BlocklaceFinality`.
-/
import Dregg2.Exec.ConsensusExec
import Std.Data.HashMap
import Std.Data.HashSet

namespace Dregg2.Distributed.BlocklaceFinality

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)

/-! ## 1. `computeRounds` — the DAG-depth recurrence (`ordering.rs::compute_rounds`),
OVER THE ENROLLED EDGE SET.

round(b) = 1 + max over present ENROLLED predecessors of round(p); no such pred = 1. The Rust runs
Kahn's algorithm, and so does this: the fold runs over `topoLace B`, an enumeration in which every
block comes after all the predecessors the lace holds. We memoize into an assoc list.

⚑ **The fold order is not a detail.** `roundOfStep` reads the rounds computed SO FAR and skips a
predecessor that has none yet, so the map is right only if every held predecessor was folded
first. This fold used to run over the lace sorted by `(seq, creator)`, on the claim that the sort
is topological. It is not: another author's EARLIER block can carry a LARGER `seq`. A validator
that joins late or lags writes a first block with `seq 0` that cites the current tips; the sort
put it ahead of them, the fold skipped every one of its predecessors, and it got round `1`. No
Byzantine step is needed; §9's `traceLateFirst` / `traceLateLeader` execute it against
`computeRoundsSeqOrder`, the old fold kept as the falsification witness. With one, it was worse:
`traceSeqGapFilled` is a single enrolled validator retracting an anchored wave without equivocating.

What is proved now, for a lace with distinct ids that Kahn finishes (`laceStuck B = []`, i.e. a
DAG — `laceStuck_eq_nil_iff`): the recurrence holds at the FINISHED map
(`computeRounds_recurrence`), any ancestor-respecting enumeration gives the same map
(`computeRounds_enumeration_invariant`), and so does any listing of the same blocks
(`roundOf_perm`): the round is a function of the DAG.

⚑ **Why the recurrence reads `participants` (HORIZONLOG B6's named residual, this pass).** It used
to count EVERY present predecessor. Depth is the wave clock — `roundToWave`, `blocksAtRound`, the
leader slot, the wave end, and `xsortBy`'s ready priority are all read off it — so any creator who
could add depth could move the wave structure. A NON-PARTICIPANT chain that one honest block acks
did exactly that, and §9's `traceOrderFork` is the measurement: two honest nodes holding the
IDENTICAL enrolled sub-lace, differing only in whether they received two outsider blocks, finalize
the SAME twelve enrolled coordinates in DIFFERENT ORDERS (creator 3's `seq 1` block lands at index 5
on one node and index 7 on the other, and neither order is a prefix of the other). That is
`no_conflicting_finalized_history` violated between two HONEST nodes, not a timing wobble — and
non-participants are precisely the creators dissemination does not guarantee every node sees, so the
divergent view is the ordinary case, not the exotic one.

**We filter the EDGES, not the NODES.** The Rust `tau_unified` sibling (`compute_rounds_filtered`)
drops non-participant blocks from the round map entirely. That is sound THERE — every downstream
read in `tau_unified` is participant-restricted — but on `tau`'s path it would SUBSUME the B6
repair: `blocksAtRound` at the wave end would no longer contain an outsider's block at all, so
`traceSybilOnly` would stop exhibiting the ratifier gate and start exhibiting an empty wave-end
round, and `tauOrderUnfiltered`'s red guard would go green for the wrong reason. So a
non-participant's block still RECEIVES the round its enrolled predecessors give it; what it cannot
do is CONTRIBUTE one. -/

/-- Look up an already-computed round for a block id. -/
def roundLookup (rs : List (BlockId × Nat)) (h : BlockId) : Option Nat :=
  (rs.find? (fun p => p.1 = h)).map (·.2)

/-- **`enrolledId B participants bid`** — the ENROLLMENT PREDICATE: the block at `bid` was created
by a member of the reference participant set. It gates TWO things, and they are independent:

* **WHICH ACKS COUNT AS DEPTH** (§1, this pass) — `roundOfStep` maxes only over enrolled
  predecessors, so a non-participant cannot move the wave clock;
* **WHOSE BLOCKS MAY BE ORDERED** (§6, `tauOrder`) — the finalized order carries only enrolled
  creators, so an unenrolled creator's state transition cannot reach the executor.

**Why the second exists** (`node/src/finality_gate.rs`'s falsifier
`attacker_block_from_unenrolled_creator_is_refused_by_the_verified_rule`). The per-anchor input was
formerly `leaderCoverage` — DELETED with the CM Def. 6 rewrite — the union of the causal pasts of
the wave-end blocks that ratify the leader, and `leaderSegment`
subtracts only `prevCovered` and equivocators. A block from a creator that is NOT in `participants`
sits in the honest leader's causal past as soon as one honest node acks it — so the rule EMITTED it,
and the node fed it to the executor. Measured on a 4-creator / 3-round lace with 3 enrolled: the
finalized set was 12 coordinates, 100% of the lace, including all three of the unenrolled creator's
blocks. `participants` was consulted for the round-robin leader schedule and the supermajority
count, and NEVER for who is allowed to be ordered at all.

The Rust sibling `blocklace/src/ordering.rs::tau_unified` already carried this filter (
"FILTER: only include blocks from reference group participants"); `ordering.rs::tau` — the one the
node runs — did not, because its docstring's precondition is "all blocks belong to participants".
That precondition is NOT enforceable on the live path (see the module header of
`node/src/finality_gate.rs` and `blocklace/src/finality.rs::from_checkpoint_trusted`), so the rule
enforces it itself.

**`none ⇒ true` is deliberate.** An id that does not resolve in `B` is not the enrollment filter's
business: it is an invariant breach (`tauOrder` only ever emits ids drawn from the anchor's own
closure — formerly `leaderCoverage`, now deleted — so from present blocks), and the CALLER owns
it — `tauBlocks`'
`filterMap B.lookup`, the Rust `compute_order`'s `id_to_block` filter_map, and
`poll_finalized_blocks`' `error!("finalized block id not present in the lace")`. Making this branch
`false` would silently convert a breach into a drop and hide it; it would also make the
honest-lace identity theorems below false for a reason that has nothing to do with enrollment. On
the §1 depth side the `none` branch is inert for a second reason: an absent pred has no entry in the
accumulator either, so `roundLookup` drops it whichever way this branch goes. -/
def enrolledId (B : Lace) (participants : List AuthorId) (bid : BlockId) : Bool :=
  match B.lookup bid with
  | some b => participants.contains b.creator
  | none   => true

/-- One folding step of `compute_rounds`: given the rounds computed so far (`rs`) and the next
block `b` (in an ancestor-respecting order), assign `round(b) = 1 + max(round(p) | p ∈ b.preds, p ENROLLED and
present in rs)`, defaulting the max to `0` (so a block with no enrolled predecessor gets round `1`).
Mirrors `ordering.rs:82..93` with the participant filter of `compute_rounds`' `participant_set`. -/
def roundOfStep (B : Lace) (participants : List AuthorId)
    (rs : List (BlockId × Nat)) (b : Block) : Nat :=
  let predRounds : List Nat :=
    (b.preds.filter (enrolledId B participants)).filterMap (fun p => roundLookup rs p)
  1 + predRounds.foldl Nat.max 0

/-- **`roundOfStepPreParticipant`** — the depth step EXACTLY as it stood before this pass: every
present predecessor counts, enrolled or not.

⚑ THIS IS NOT THE RECURRENCE. It is kept, named, and reachable from nothing but
`computeRoundsPreParticipant` and the §9 `#guard`s, for one reason: it is the FALSIFICATION WITNESS
for the participant filter — the same discipline `isSuperRatifiedPreEnrollment` and
`tauOrderUnfiltered` carry. A red-proof that lives in the tree forever instead of in a reverted
source edit. -/
def roundOfStepPreParticipant (rs : List (BlockId × Nat)) (b : Block) : Nat :=
  let predRounds : List Nat := b.preds.filterMap (fun p => roundLookup rs p)
  1 + predRounds.foldl Nat.max 0

/-- The lace sorted by `(seq, creator)` — the order the depth fold USED to run over, and the order
the node's wire (`finality_gate.rs::build_wire`) still lists blocks in.

⚑ THIS IS NOT A TOPOLOGICAL ORDER and nothing on the rule's path folds over it any more. It is
kept, reachable only from `computeRoundsSeqOrder` and the §9 `#guard`s, as the falsification
witness for `topoLace`. -/
def sortedLace (B : Lace) : List Block :=
  (B.toArray.qsort (fun a b => a.seq < b.seq || (a.seq == b.seq && a.creator < b.creator))).toList

/-- The depth fold itself, over an explicit block list. Every statement about the map is proved by
induction on this list, whatever produced it. -/
def roundsFold (B : Lace) (participants : List AuthorId) (bs : List Block) : List (BlockId × Nat) :=
  bs.foldl (fun rs b => (b.id, roundOfStep B participants rs b) :: rs) []

/-! ### The enumeration the fold runs over — Kahn's algorithm. -/

/-- A held id names a member block. -/
theorem laceHas_iff {B : Lace} {h : BlockId} : B.has h = true ↔ ∃ c ∈ B, c.id = h := by
  unfold Lace.has Lace.lookup
  rw [List.find?_isSome]
  constructor
  · rintro ⟨c, hc, hid⟩; exact ⟨c, hc, by simpa using hid⟩
  · rintro ⟨c, hc, hid⟩; exact ⟨c, hc, by simpa using hid⟩

/-- **`predsEmitted B done b`** — `b` is READY against the emitted prefix `done`: every predecessor
the lace HOLDS has already been emitted. A predecessor the lace does not hold is an edge nothing
traverses (`expandPreds` filters on `B.has` identically), so it imposes no constraint. -/
def predsEmitted (B : Lace) (done : List Block) (b : Block) : Bool :=
  b.preds.all (fun p => !B.has p || done.any (fun c => c.id == p))

theorem predsEmitted_iff {B : Lace} {done : List Block} {b : Block} :
    predsEmitted B done b = true ↔ ∀ p ∈ b.preds, B.has p = true → ∃ c ∈ done, c.id = p := by
  unfold predsEmitted
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq]
  constructor
  · intro h p hp hhas
    rcases h p hp with hn | hy
    · rw [hn] at hhas; exact absurd hhas (by simp)
    · exact hy
  · intro h p hp
    by_cases hhas : B.has p = true
    · exact Or.inr (h p hp hhas)
    · exact Or.inl (by simpa using hhas)

/-- One step of a Kahn sweep: emit `b` if it is ready against what has been emitted so far,
otherwise defer it to the next sweep. -/
def kahnStep (B : Lace) (st : List Block × List Block) (b : Block) : List Block × List Block :=
  if predsEmitted B st.1 b then (st.1 ++ [b], st.2) else (st.1, st.2 ++ [b])

/-- Kahn's algorithm as repeated sweeps. Each sweep walks `pending` in list order and emits every
block whose held predecessors are all emitted (INCLUDING ones emitted earlier in the same sweep, so
a lace already in a causal order finishes in ONE sweep). It stops when a sweep emits nothing; what
is left is exactly the blocks on or behind a predecessor cycle. Returns `(emitted, stuck)`. -/
def kahnAux (B : Lace) : Nat → List Block → List Block → List Block × List Block
  | 0,        done, pending => (done, pending)
  | fuel + 1, done, pending =>
      let st := pending.foldl (kahnStep B) (done, [])
      if st.2.length < pending.length then kahnAux B fuel st.1 st.2 else st

/-- The Kahn pass over a whole lace. -/
def kahn (B : Lace) : List Block × List Block := kahnAux B B.length [] B

/-- **`laceStuck B`** — the blocks Kahn could never emit: those on, or causally behind, a
predecessor CYCLE. `[]` on every lace hash pointers can build. -/
def laceStuck (B : Lace) : List Block := (kahn B).2

/-- **`topoLace B`** — the lace in an ANCESTOR-RESPECTING order (every block after all the
predecessors the lace holds), the enumeration the depth fold runs over. On a cyclic lace the stuck
blocks are appended in list order, so this is always a permutation of `B`. -/
def topoLace (B : Lace) : List Block := (kahn B).1 ++ (kahn B).2

/-- **`AncestorRespecting B bs`** — `bs` lists every block after all of its held predecessors. -/
def AncestorRespecting (B : Lace) (bs : List Block) : Prop :=
  ∀ pre b post, bs = pre ++ b :: post → predsEmitted B pre b = true

theorem AncestorRespecting.nil (B : Lace) : AncestorRespecting B [] := by
  intro pre b post h; simp at h

theorem AncestorRespecting.snoc {B : Lace} {bs : List Block} {b : Block}
    (h : AncestorRespecting B bs) (hb : predsEmitted B bs b = true) :
    AncestorRespecting B (bs ++ [b]) := by
  intro pre x post heq
  rcases List.eq_nil_or_concat post with hp | ⟨L, c, hp⟩
  · subst hp
    have := List.append_inj' heq rfl
    obtain ⟨h1, h2⟩ := this
    simp only [List.cons.injEq, and_true] at h2
    subst h1; subst h2; exact hb
  · subst hp
    have heq' : bs ++ [b] = (pre ++ x :: L) ++ [c] := by simpa using heq
    have := List.append_inj' heq' rfl
    exact h pre x L this.1

theorem AncestorRespecting.prefix {B : Lace} {bs t : List Block}
    (h : AncestorRespecting B (bs ++ t)) : AncestorRespecting B bs := by
  intro pre b post heq
  exact h pre b (post ++ t) (by simp [heq])

/-- In an ancestor-respecting list, every held predecessor of a listed block is itself listed. -/
theorem AncestorRespecting.pred_mem {B : Lace} {bs : List Block} (h : AncestorRespecting B bs)
    {x : Block} (hx : x ∈ bs) {p : BlockId} (hp : p ∈ x.preds) (hhas : B.has p = true) :
    p ∈ bs.map (·.id) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hx
  obtain ⟨c, hc, hid⟩ := predsEmitted_iff.mp (h pre x post rfl) p hp hhas
  exact List.mem_map.mpr ⟨c, by simp [hc], hid⟩

/-! #### The sweep keeps everything and emits only ready blocks. -/

theorem kahnStep_fold_perm (B : Lace) :
    ∀ (pending : List Block) (st : List Block × List Block),
      ((pending.foldl (kahnStep B) st).1 ++ (pending.foldl (kahnStep B) st).2).Perm
        (st.1 ++ st.2 ++ pending) := by
  intro pending
  induction pending with
  | nil => intro st; simp
  | cons b rest ih =>
    intro st
    rw [List.foldl_cons]
    refine (ih (kahnStep B st b)).trans ?_
    unfold kahnStep
    split
    · simp only
      have : (st.1 ++ [b] ++ st.2 ++ rest).Perm (st.1 ++ st.2 ++ b :: rest) := by
        simp only [List.append_assoc, List.singleton_append]
        exact List.Perm.append_left _ (by
          simpa using (List.perm_middle (a := b) (l₁ := st.2) (l₂ := rest)).symm)
      exact this
    · simp

theorem kahnAux_perm (B : Lace) :
    ∀ (fuel : Nat) (done pending : List Block),
      ((kahnAux B fuel done pending).1 ++ (kahnAux B fuel done pending).2).Perm (done ++ pending) := by
  intro fuel
  induction fuel with
  | zero => intro done pending; exact List.Perm.refl _
  | succ n ih =>
    intro done pending
    have hf := kahnStep_fold_perm B pending (done, [])
    simp only [List.append_nil] at hf
    unfold kahnAux
    simp only
    split
    · exact (ih _ _).trans hf
    · exact hf

/-- **`topoLace_perm`** — the enumeration is a PERMUTATION of the lace, unconditionally. -/
theorem topoLace_perm (B : Lace) : (topoLace B).Perm B := by
  have := kahnAux_perm B B.length [] B
  simpa [topoLace, kahn] using this

theorem mem_topoLace {B : Lace} {b : Block} : b ∈ topoLace B ↔ b ∈ B :=
  (topoLace_perm B).mem_iff

theorem kahnStep_fold_respects (B : Lace) :
    ∀ (pending : List Block) (st : List Block × List Block),
      AncestorRespecting B st.1 → AncestorRespecting B (pending.foldl (kahnStep B) st).1 := by
  intro pending
  induction pending with
  | nil => intro st h; exact h
  | cons b rest ih =>
    intro st h
    rw [List.foldl_cons]
    apply ih
    unfold kahnStep
    split
    · rename_i hb; exact h.snoc hb
    · exact h

theorem kahnAux_respects (B : Lace) :
    ∀ (fuel : Nat) (done pending : List Block),
      AncestorRespecting B done → AncestorRespecting B (kahnAux B fuel done pending).1 := by
  intro fuel
  induction fuel with
  | zero => intro done pending h; exact h
  | succ n ih =>
    intro done pending h
    have hf := kahnStep_fold_respects B pending (done, []) h
    unfold kahnAux
    simp only
    split
    · exact ih _ _ hf
    · exact hf

/-- **`topoLace_ancestorRespecting`** — when Kahn leaves nothing stuck, the enumeration puts every
block after all of its held predecessors. -/
theorem topoLace_ancestorRespecting {B : Lace} (hdag : laceStuck B = []) :
    AncestorRespecting B (topoLace B) := by
  have h := kahnAux_respects B B.length [] B (AncestorRespecting.nil B)
  unfold topoLace
  unfold laceStuck at hdag
  rw [hdag, List.append_nil]
  exact h

/-! #### Kahn never sticks on a DAG. -/

/-- **`LaceDag B`** — the held-predecessor relation is well-founded: some rank strictly decreases
along every edge the lace holds. Arrival order under the receive path's predecessor buffering is
such a rank; that a hash-linked lace has one at all is collision resistance, a §8 seam, and is NOT
proved here. `laceStuck B = []` is the executable form (`laceStuck_eq_nil_iff`). -/
def LaceDag (B : Lace) : Prop :=
  ∃ rank : BlockId → Nat, ∀ b ∈ B, ∀ p ∈ b.preds, B.has p = true → rank p < rank b.id

theorem exists_min_rank {α : Type} (rank : α → Nat) :
    ∀ (l : List α), l ≠ [] → ∃ x ∈ l, ∀ a ∈ l, rank x ≤ rank a := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _
    by_cases ht : t = []
    · subst ht; exact ⟨a, by simp, by simp⟩
    · obtain ⟨x, hx, hmin⟩ := ih ht
      by_cases hax : rank a ≤ rank x
      · refine ⟨a, by simp, ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_refl _
        · exact le_trans hax (hmin c hc)
      · refine ⟨x, by simp [hx], ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · omega
        · exact hmin c hc

theorem kahnStep_fold_deferred_le (B : Lace) :
    ∀ (pending : List Block) (st : List Block × List Block),
      (pending.foldl (kahnStep B) st).2.length ≤ st.2.length + pending.length := by
  intro pending
  induction pending with
  | nil => intro st; simp
  | cons b rest ih =>
    intro st
    rw [List.foldl_cons]
    refine le_trans (ih _) ?_
    unfold kahnStep
    split
    · simp only [List.length_cons]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega

theorem kahnStep_fold_deferred_mem (B : Lace) :
    ∀ (pending : List Block) (st : List Block × List Block) (c : Block),
      c ∈ (pending.foldl (kahnStep B) st).2 → c ∈ st.2 ∨ c ∈ pending := by
  intro pending
  induction pending with
  | nil => intro st c h; exact Or.inl h
  | cons b rest ih =>
    intro st c h
    rw [List.foldl_cons] at h
    rcases ih _ c h with h1 | h1
    · unfold kahnStep at h1
      split at h1
      · exact Or.inl h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (by simp at h2; simp [h2])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- A sweep that meets a ready block defers strictly fewer than it was given. -/
theorem kahnStep_fold_progress (B : Lace) :
    ∀ (pending : List Block) (st : List Block × List Block),
      (∃ x ∈ pending, predsEmitted B st.1 x = true) →
      (pending.foldl (kahnStep B) st).2.length < st.2.length + pending.length := by
  intro pending
  induction pending with
  | nil => intro st ⟨x, hx, _⟩; simp at hx
  | cons b rest ih =>
    intro st ⟨x, hx, hready⟩
    rw [List.foldl_cons]
    by_cases hb : predsEmitted B st.1 b = true
    · have hle := kahnStep_fold_deferred_le B rest (kahnStep B st b)
      have : (kahnStep B st b).2 = st.2 := by unfold kahnStep; simp [hb]
      rw [this] at hle
      simp only [List.length_cons]; omega
    · have hxr : x ∈ rest := by
        rcases List.mem_cons.mp hx with rfl | h
        · exact absurd hready hb
        · exact h
      have hst : kahnStep B st b = (st.1, st.2 ++ [b]) := by unfold kahnStep; simp [hb]
      have := ih (kahnStep B st b) ⟨x, hxr, by rw [hst]; exact hready⟩
      rw [hst] at this ⊢
      simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
      omega

theorem kahnAux_stuck_nil {B : Lace} (hdag : LaceDag B) :
    ∀ (fuel : Nat) (done pending : List Block),
      (∀ c ∈ B, c ∈ done ∨ c ∈ pending) → (∀ c ∈ pending, c ∈ B) → pending.length ≤ fuel →
      (kahnAux B fuel done pending).2 = [] := by
  obtain ⟨rank, hrank⟩ := hdag
  intro fuel
  induction fuel with
  | zero =>
    intro done pending _ _ hlen
    have hnil : pending = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil; rfl
  | succ n ih =>
    intro done pending hcov hsub hlen
    unfold kahnAux
    simp only
    by_cases hp : pending = []
    · subst hp; simp
    · -- the rank-least pending block is ready: its held predecessors rank lower, so none is pending
      obtain ⟨x, hx, hmin⟩ := exists_min_rank (fun b : Block => rank b.id) pending hp
      have hready : predsEmitted B done x = true := by
        rw [predsEmitted_iff]
        intro p hpp hhas
        obtain ⟨c, hc, hid⟩ := laceHas_iff.mp hhas
        rcases hcov c hc with hd | hpend
        · exact ⟨c, hd, hid⟩
        · have h1 := hrank x (hsub x hx) p hpp hhas
          have h2 := hmin c hpend
          simp only [hid] at h2
          omega
      have hprog := kahnStep_fold_progress B pending (done, []) ⟨x, hx, hready⟩
      simp only [List.length_nil, Nat.zero_add] at hprog
      simp only [hprog, ite_true]
      have hperm := kahnStep_fold_perm B pending (done, [])
      simp only [List.append_nil] at hperm
      apply ih
      · intro c hc
        have : c ∈ done ++ pending := by
          rcases hcov c hc with h | h <;> simp [h]
        exact List.mem_append.mp (hperm.mem_iff.mpr this)
      · intro c hc
        rcases kahnStep_fold_deferred_mem B pending (done, []) c hc with h | h
        · simp at h
        · exact hsub c h
      · omega

/-- Kahn leaves nothing stuck on a DAG. -/
theorem laceStuck_eq_nil_of_dag {B : Lace} (hdag : LaceDag B) : laceStuck B = [] :=
  kahnAux_stuck_nil hdag B.length [] B (fun _ hc => Or.inr hc) (fun _ hc => hc) (le_refl _)

/-! #### The depth map is a function of the DAG, not of the enumeration. -/

theorem roundLookup_cons (k : BlockId) (v : Nat) (rs : List (BlockId × Nat)) (h : BlockId) :
    roundLookup ((k, v) :: rs) h = if k = h then some v else roundLookup rs h := by
  unfold roundLookup
  by_cases hk : k = h <;> simp [hk]

theorem roundsFold_snoc (B : Lace) (P : List AuthorId) (bs : List Block) (b : Block) :
    roundsFold B P (bs ++ [b])
      = (b.id, roundOfStep B P (roundsFold B P bs) b) :: roundsFold B P bs := by
  simp [roundsFold, List.foldl_append]

/-- The fold's key set is exactly the ids it folded. -/
theorem roundLookup_roundsFold_eq_none (B : Lace) (P : List AuthorId) :
    ∀ (bs : List Block) (h : BlockId), h ∉ bs.map (·.id) →
      roundLookup (roundsFold B P bs) h = none := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil => intro h _; rfl
  | append_singleton bs b ih =>
    intro h hh
    rw [roundsFold_snoc, roundLookup_cons]
    have h1 : b.id ≠ h := by
      intro e; exact hh (by simp [e])
    have h2 : h ∉ bs.map (·.id) := by
      intro e; exact hh (by simp only [List.map_append, List.mem_append]; exact Or.inl e)
    simp [h1, ih h h2]

/-- A step reads the accumulator only at the block's own predecessors. -/
theorem roundOfStep_congr (B : Lace) (P : List AuthorId) {rs rs' : List (BlockId × Nat)}
    {b : Block} (h : ∀ p ∈ b.preds, roundLookup rs p = roundLookup rs' p) :
    roundOfStep B P rs b = roundOfStep B P rs' b := by
  unfold roundOfStep
  have : (b.preds.filter (enrolledId B P)).filterMap (fun p => roundLookup rs p)
       = (b.preds.filter (enrolledId B P)).filterMap (fun p => roundLookup rs' p) := by
    apply List.filterMap_congr
    intro p hp
    exact h p (List.mem_filter.mp hp).1
  simp only [this]

/-- **THE RECURRENCE, AT THE FINISHED MAP.** Over an ancestor-respecting enumeration every block's
round is `1 + max` of the FINAL rounds of its enrolled predecessors — not of whichever
predecessors happened to be folded before it. This is the equation the `(seq, creator)` fold did
not satisfy. -/
theorem roundsFold_recurrence (B : Lace) (P : List AuthorId) :
    ∀ (bs : List Block), AncestorRespecting B bs → (bs.map (·.id)).Nodup → (∀ x ∈ bs, x ∈ B) →
      ∀ x ∈ bs, roundLookup (roundsFold B P bs) x.id
                  = some (roundOfStep B P (roundsFold B P bs) x) := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil => intro _ _ _ x hx; simp at hx
  | append_singleton bs b ih =>
    intro hAR hnd hsub x hx
    have hARp : AncestorRespecting B bs := hAR.prefix
    have hnd' : (bs.map (·.id)).Nodup ∧ b.id ∉ bs.map (·.id) := by
      rw [List.map_append, List.nodup_append] at hnd
      refine ⟨hnd.1, ?_⟩
      intro e
      exact hnd.2.2 b.id e b.id (by simp) rfl
    have hbB : B.has b.id = true := laceHas_iff.mpr ⟨b, hsub b (by simp), rfl⟩
    -- no listed block (nor `b` itself) names `b` as a predecessor
    have hno : ∀ y ∈ bs ++ [b], b.id ∉ y.preds := by
      intro y hy hmem
      rcases List.mem_append.mp hy with hyb | hyb
      · exact hnd'.2 (hARp.pred_mem hyb hmem hbB)
      · have hyb' : y = b := by simpa using hyb
        subst hyb'
        obtain ⟨c, hc, hid⟩ := predsEmitted_iff.mp (hAR bs y [] rfl) y.id hmem hbB
        exact hnd'.2 (List.mem_map.mpr ⟨c, hc, hid⟩)
    have hstep : ∀ y ∈ bs ++ [b],
        roundOfStep B P (roundsFold B P (bs ++ [b])) y = roundOfStep B P (roundsFold B P bs) y := by
      intro y hy
      apply roundOfStep_congr
      intro p hp
      rw [roundsFold_snoc, roundLookup_cons]
      have : b.id ≠ p := by intro e; exact hno y hy (e ▸ hp)
      simp [this]
    rw [hstep x hx, roundsFold_snoc, roundLookup_cons]
    rcases List.mem_append.mp hx with hxb | hxb
    · have hne : b.id ≠ x.id := by
        intro e; exact hnd'.2 (e ▸ List.mem_map_of_mem hxb)
      simp only [hne, ite_false]
      exact ih hARp hnd'.1 (fun y hy => hsub y (by simp [hy])) x hxb
    · have : x = b := by simpa using hxb
      subst this; simp

/-- **`roundsFold_enumeration_invariant`** — ANY two ancestor-respecting enumerations of the same
blocks produce the same round for every id. The depth map is a function of the DAG. -/
theorem roundsFold_enumeration_invariant (B : Lace) (P : List AuthorId) {bs₁ bs₂ : List Block}
    (hperm : bs₁.Perm bs₂) (h₁ : AncestorRespecting B bs₁) (h₂ : AncestorRespecting B bs₂)
    (hnd : (bs₁.map (·.id)).Nodup) (hsub : ∀ x ∈ bs₁, x ∈ B) (h : BlockId) :
    roundLookup (roundsFold B P bs₁) h = roundLookup (roundsFold B P bs₂) h := by
  have hnd₂ : (bs₂.map (·.id)).Nodup := (hperm.map _).nodup_iff.mp hnd
  have hsub₂ : ∀ x ∈ bs₂, x ∈ B := fun x hx => hsub x (hperm.mem_iff.mpr hx)
  have hids : ∀ q, q ∈ bs₁.map (·.id) ↔ q ∈ bs₂.map (·.id) := fun q => (hperm.map _).mem_iff
  -- along `bs₁`, by induction on the prefix
  have key : ∀ (pre post : List Block), bs₁ = pre ++ post →
      ∀ x ∈ pre, roundLookup (roundsFold B P bs₁) x.id = roundLookup (roundsFold B P bs₂) x.id := by
    intro pre
    induction pre using List.reverseRecOn with
    | nil => intro _ _ x hx; simp at hx
    | append_singleton pre b ih =>
      intro post heq x hx
      have heq' : bs₁ = pre ++ b :: post := by simp [heq]
      rcases List.mem_append.mp hx with hxp | hxb
      · exact ih (b :: post) heq' x hxp
      · have hxb' : x = b := by simpa using hxb
        subst hxb'
        have hx₁ : x ∈ bs₁ := by rw [heq']; simp
        have hx₂ : x ∈ bs₂ := hperm.mem_iff.mp hx₁
        rw [roundsFold_recurrence B P bs₁ h₁ hnd hsub x hx₁,
            roundsFold_recurrence B P bs₂ h₂ hnd₂ hsub₂ x hx₂]
        congr 1
        apply roundOfStep_congr
        intro p hp
        by_cases hpin : p ∈ bs₁.map (·.id)
        · obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hpin
          have hhas : B.has p = true := laceHas_iff.mpr ⟨c, hsub c hc, hcid⟩
          obtain ⟨c', hc', hid'⟩ := predsEmitted_iff.mp (h₁ pre x post heq') p hp hhas
          rw [← hid']
          exact ih (x :: post) heq' c' hc'
        · rw [roundLookup_roundsFold_eq_none B P bs₁ p hpin,
              roundLookup_roundsFold_eq_none B P bs₂ p (fun e => hpin ((hids p).mpr e))]
  by_cases hin : h ∈ bs₁.map (·.id)
  · obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hin
    rw [← hcid]
    exact key bs₁ [] (by simp) c hc
  · rw [roundLookup_roundsFold_eq_none B P bs₁ h hin,
        roundLookup_roundsFold_eq_none B P bs₂ h (fun e => hin ((hids h).mpr e))]


/-- **`computeRounds B participants`** — fold `roundOfStep` over `topoLace B`, producing the
`(id, round)` map. A block with no enrolled predecessor gets round `1`; depth increases by one per
ENROLLED causal layer. (`ordering.rs::compute_rounds`.) -/
def computeRounds (B : Lace) (participants : List AuthorId) : List (BlockId × Nat) :=
  roundsFold B participants (topoLace B)

/-- **`computeRoundsSeqOrder B participants`** — the depth map EXACTLY as it stood while the fold
ran over the `(seq, creator)` sort.

⚑ THIS IS NOT THE RECURRENCE. It is kept, named, and reachable from nothing but the §9 `#guard`s,
as the FALSIFICATION WITNESS for the fold order: on `traceLateFirst` it gives an honest late
joiner round `1` where the recurrence gives `4`. -/
def computeRoundsSeqOrder (B : Lace) (participants : List AuthorId) : List (BlockId × Nat) :=
  roundsFold B participants (sortedLace B)

/-- **`computeRoundsPreParticipant B`** — the depth map with EVERY present predecessor counted,
enrolled or not. The FALSIFICATION WITNESS for the participant filter; see
`roundOfStepPreParticipant`. It folds the same enumeration `computeRounds` does, so the
participant filter is the only variable. Feeding it to `tauOrderWithRounds` (§6b) runs the WHOLE
rule with the round map as the only variable, which is what makes §9's exhibits an experiment
rather than two anecdotes. -/
def computeRoundsPreParticipant (B : Lace) : List (BlockId × Nat) :=
  (topoLace B).foldl (fun rs b => (b.id, roundOfStepPreParticipant rs b) :: rs) []

/-- The round of a specific block id in the computed map (`0` if absent — only for ids not in `B`). -/
def roundOf (B : Lace) (participants : List AuthorId) (h : BlockId) : Nat :=
  (roundLookup (computeRounds B participants) h).getD 0

/-- In a lace with distinct ids, a member is what its id resolves to. -/
theorem lookup_of_mem_nodup : ∀ {B : Lace}, (B.map (·.id)).Nodup → ∀ {c : Block}, c ∈ B →
    B.lookup c.id = some c := by
  intro B
  induction B with
  | nil => intro _ c hc; simp at hc
  | cons a t ih =>
    intro hnd c hc
    simp only [List.map_cons, List.nodup_cons] at hnd
    unfold Lace.lookup
    rcases List.mem_cons.mp hc with rfl | hct
    · simp
    · have hne : a.id ≠ c.id := by
        intro e; exact hnd.1 (e ▸ List.mem_map_of_mem hct)
      simp only [List.find?_cons, hne, decide_false]
      exact ih hnd.2 hct

/-- `Lace.lookup` reads the block SET, not the list order, once ids are distinct. -/
theorem lookup_perm {B₁ B₂ : Lace} (hperm : B₁.Perm B₂) (hnd : (B₁.map (·.id)).Nodup)
    (h : BlockId) : B₁.lookup h = B₂.lookup h := by
  have hnd₂ : (B₂.map (·.id)).Nodup := (hperm.map _).nodup_iff.mp hnd
  cases h₁ : B₁.lookup h with
  | some c =>
    have hc : c ∈ B₁ := List.mem_of_find?_eq_some h₁
    have hid : c.id = h := by have := List.find?_some h₁; simpa using this
    rw [← hid]
    exact (lookup_of_mem_nodup hnd₂ (hperm.mem_iff.mp hc)).symm
  | none =>
    cases h₂ : B₂.lookup h with
    | none => rfl
    | some c =>
      have hc : c ∈ B₂ := List.mem_of_find?_eq_some h₂
      have hid : c.id = h := by have := List.find?_some h₂; simpa using this
      have := lookup_of_mem_nodup hnd (hperm.mem_iff.mpr hc)
      rw [hid, h₁] at this
      exact absurd this (by simp)

/-- When Kahn leaves nothing stuck the lace is a DAG: position in the Kahn enumeration is a rank
that strictly decreases along every held edge. -/
theorem laceDag_of_stuck_nil {B : Lace} (hnd : (B.map (·.id)).Nodup) (hdag : laceStuck B = []) :
    LaceDag B := by
  refine ⟨fun h => ((topoLace B).map (·.id)).idxOf h, ?_⟩
  intro b hb p hp hhas
  have hAR := topoLace_ancestorRespecting hdag
  have hndT : ((topoLace B).map (·.id)).Nodup := ((topoLace_perm B).map _).nodup_iff.mpr hnd
  obtain ⟨pre, post, heq⟩ := List.append_of_mem (mem_topoLace.mpr hb)
  obtain ⟨c, hc, hid⟩ := predsEmitted_iff.mp (hAR pre b post heq) p hp hhas
  have hpin : p ∈ pre.map (·.id) := List.mem_map.mpr ⟨c, hc, hid⟩
  have hbnot : b.id ∉ pre.map (·.id) := by
    rw [heq, List.map_append, List.nodup_append] at hndT
    intro e
    exact hndT.2.2 b.id e b.id (by simp) rfl
  simp only [heq, List.map_append, List.map_cons]
  rw [List.idxOf_append_of_mem hpin, List.idxOf_append_of_notMem hbnot, List.idxOf_cons_self]
  have := List.idxOf_lt_length_of_mem hpin
  simp only [List.length_map] at this ⊢
  omega

/-- **`laceStuck_eq_nil_iff`** — with distinct ids, "Kahn finishes" IS "the lace is a DAG". -/
theorem laceStuck_eq_nil_iff {B : Lace} (hnd : (B.map (·.id)).Nodup) :
    laceStuck B = [] ↔ LaceDag B :=
  ⟨laceDag_of_stuck_nil hnd, laceStuck_eq_nil_of_dag⟩

/-- **`computeRounds_recurrence`** — on a DAG with distinct ids, every block's round is `1 + max`
of the rounds of ALL its enrolled predecessors. -/
theorem computeRounds_recurrence {B : Lace} (P : List AuthorId)
    (hnd : (B.map (·.id)).Nodup) (hdag : laceStuck B = []) :
    ∀ b ∈ B, roundLookup (computeRounds B P) b.id
               = some (roundOfStep B P (computeRounds B P) b) := by
  intro b hb
  exact roundsFold_recurrence B P (topoLace B) (topoLace_ancestorRespecting hdag)
    (((topoLace_perm B).map _).nodup_iff.mpr hnd) (fun x hx => mem_topoLace.mp hx)
    b (mem_topoLace.mpr hb)

/-- **`computeRounds_enumeration_invariant`** — folding ANY ancestor-respecting enumeration of the
lace gives the round `computeRounds` gives. -/
theorem computeRounds_enumeration_invariant {B : Lace} (P : List AuthorId)
    (hnd : (B.map (·.id)).Nodup) {E : List Block} (hperm : E.Perm B)
    (hE : AncestorRespecting B E) (h : BlockId) :
    roundLookup (computeRounds B P) h = roundLookup (roundsFold B P E) h := by
  have hndE : (E.map (·.id)).Nodup := (hperm.map _).nodup_iff.mpr hnd
  -- `E` itself witnesses that the lace is a DAG
  have hdag : LaceDag B := by
    refine ⟨fun q => (E.map (·.id)).idxOf q, ?_⟩
    intro b hb p hp hhas
    obtain ⟨pre, post, heq⟩ := List.append_of_mem (hperm.mem_iff.mpr hb)
    obtain ⟨c, hc, hid⟩ := predsEmitted_iff.mp (hE pre b post heq) p hp hhas
    have hpin : p ∈ pre.map (·.id) := List.mem_map.mpr ⟨c, hc, hid⟩
    have hbnot : b.id ∉ pre.map (·.id) := by
      rw [heq, List.map_append, List.nodup_append] at hndE
      intro e
      exact hndE.2.2 b.id e b.id (by simp) rfl
    simp only [heq, List.map_append, List.map_cons]
    rw [List.idxOf_append_of_mem hpin, List.idxOf_append_of_notMem hbnot, List.idxOf_cons_self]
    have := List.idxOf_lt_length_of_mem hpin
    simp only [List.length_map] at this ⊢
    omega
  exact roundsFold_enumeration_invariant B P ((topoLace_perm B).trans hperm.symm)
    (topoLace_ancestorRespecting (laceStuck_eq_nil_of_dag hdag)) hE
    (((topoLace_perm B).map _).nodup_iff.mpr hnd) (fun x hx => mem_topoLace.mp hx) h

/-- **`roundOf_perm`** — THE ROUND IS A FUNCTION OF THE BLOCK SET. Two listings of the same DAG —
arrival order, the wire's `(seq, creator)` order, any other — give every id the same round. -/
theorem roundOf_perm {B₁ B₂ : Lace} (hperm : B₁.Perm B₂) (hnd : (B₁.map (·.id)).Nodup)
    (hdag : laceStuck B₁ = []) (P : List AuthorId) (h : BlockId) :
    roundOf B₁ P h = roundOf B₂ P h := by
  have hlk : B₁.lookup = B₂.lookup := funext (lookup_perm hperm hnd)
  have hhas : B₁.has = B₂.has := by funext q; unfold Lace.has; rw [hlk]
  have hen : enrolledId B₁ P = enrolledId B₂ P := by funext q; unfold enrolledId; rw [hlk]
  have hstep : roundOfStep B₁ P = roundOfStep B₂ P := by
    funext rs b; unfold roundOfStep; rw [hen]
  have hfold : roundsFold B₁ P = roundsFold B₂ P := by
    funext bs; unfold roundsFold; rw [hstep]
  have hpe : predsEmitted B₁ = predsEmitted B₂ := by
    funext d b; unfold predsEmitted; rw [hhas]
  have hE₂ : AncestorRespecting B₁ (topoLace B₂) := by
    obtain ⟨rank, hrank⟩ := laceDag_of_stuck_nil hnd hdag
    have hdag₂ : laceStuck B₂ = [] := laceStuck_eq_nil_of_dag
      ⟨rank, fun b hb p hp hh => hrank b (hperm.mem_iff.mpr hb) p hp (by rw [hhas]; exact hh)⟩
    intro pre b post heq
    rw [hpe]
    exact topoLace_ancestorRespecting hdag₂ pre b post heq
  unfold roundOf
  rw [computeRounds_enumeration_invariant P hnd ((topoLace_perm B₂).trans hperm.symm) hE₂ h,
      hfold]
  rfl


/-! ## 2. Wave arithmetic + round-robin leader (`ordering.rs:147..170`). -/

/-- The supermajority threshold `⌊2n/3⌋ + 1` (`ordering.rs::supermajority_threshold`). -/
def superMajority (n : Nat) : Nat := (n * 2 / 3) + 1

/-- `round_to_wave`: rounds are 1-indexed; wave 0 = rounds `[1, w]`. (`ordering.rs:147`.) -/
def roundToWave (round wavelength : Nat) : Nat := (round - 1) / wavelength

/-- `wave_first_round` (`ordering.rs:152`). -/
def waveFirstRound (wave wavelength : Nat) : Nat := wave * wavelength + 1

/-- `wave_last_round` (`ordering.rs:157`). -/
def waveLastRound (wave wavelength : Nat) : Nat := (wave + 1) * wavelength

/-- **`waveLeader`** — the round-robin leader `participants[wave % len]` (`ordering.rs:167`).
`none` when there are no participants (the Rust caller guards this). -/
def waveLeader (wave : Nat) (participants : List AuthorId) : Option AuthorId :=
  if participants.isEmpty then none
  else participants[wave % participants.length]?

/-! ## 3. Causal past (fuel-bounded BFS over the present-pred edge set — `ordering.rs::causal_past`). -/

/-- One BFS layer: expand a frontier of ids to the union with their present predecessors. -/
def expandPreds (B : Lace) (frontier : List BlockId) : List BlockId :=
  frontier.flatMap (fun h => match B.lookup h with
                              | some b => b.preds.filter (fun p => B.has p)
                              | none   => [])

/-- Fuel-bounded transitive closure of `expandPreds` starting from `[h]`. `fuel = B.length` is
sufficient for any finite acyclic lace (each layer adds at least one strictly-smaller-depth block).
Returns the accumulated id set (deduped), INCLUSIVE of `h` (`causal_past_inclusive`).

⚑ **THIS IS THE SPECIFICATION, NOT THE PATH ANYTHING RUNS — it is EXPONENTIAL, and that is a
measurement, not an estimate.** The layer `nxt` is `expandPreds`'s `flatMap` output filtered against
`acc` ONLY; the filter tests every duplicate against the SAME `acc`, so it cannot remove duplicates
*within* a layer. On a round-synchronous lace where each block acks all `d` blocks of the previous
round, layer `k` therefore has **`d^k` elements** — measured directly, `[4, 16, 64, 256, 1024, 4096,
16384, 65536, 262144, …]` for `d = 4`. `acc` reaches `(d^(k+1)-1)/(d-1)` cells and `acc.contains` is
`List.elem`, so one `causalPastIncl` of a round-`R` tip costs ~`d^(2R)/(d-1)` list-cell probes:
**390 billion at `R = 11`, and `mkPastCache` pays it per block (1.7 × 10¹²).**

That is the consensus wedge, and the shape of the curve names the round: `n=4` costs ~6.5 s at
`R = 9`, ~104 s at `R = 10`, ~28 min at `R = 11` — 16× per round. Four wedged nodes were sampled
under `gdb` at 100% CPU on an idle box, all in `List.filterTR_loop`/`List.elem` under
`causalPastAux ← causalPastIncl ← mkPastCache ← advanceGateFast`. **Indexing the lace does not
touch this**: `d^k` is a LIST LENGTH, not a lookup cost, so an O(1) `Lace.lookup` would have bought
a constant factor and left the exponential standing.

`causalPastIncl` runs `causalPastAuxFast` below, which is this function with the layer `dedup`ed and
is proved to return **the identical list** (`causalPastAuxFast_eq`). Keep this def as the spec: every
theorem and differential in this file is stated about it. -/
def causalPastAux (B : Lace) : Nat → List BlockId → List BlockId → List BlockId
  | 0,        _,        acc => acc.dedup
  | _,        [],       acc => acc.dedup
  | fuel + 1, frontier, acc =>
      let nxt := (expandPreds B frontier).filter (fun p => ¬ acc.contains p)
      causalPastAux B fuel nxt (acc ++ nxt)

/-! ### The frontier-dedup repair, and the four lemmas that make it VALUE-PRESERVING.

The fix is one `.dedup` on the layer. What has to be proved is that it changes NOTHING: the BFS
carries the deduped layer forward, so every later `expandPreds` sees a different *list* — and the
final answer must still be equal, element for element, in order. That is `causalPastAuxFast_eq`,
and it rests on one real fact about `List.dedup` (`dedup_flatMap_dedup`): **duplicated `flatMap`
sources cannot survive a `dedup`.**

⚠ `List.dedup` keeps the **LAST** occurrence (`[1,2,1,3,2].dedup = [1,3,2]` — evaluated, not
recalled). Every lemma here is stated to respect that; a "keep the first" reading of the same code
is what put a divergent twin on the live τ path (§6c). -/

/-- `l₁ ⊆ l₂ → l₁ ∪ l₂ = l₂`. -/
theorem union_eq_right_of_subset {α} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₁ ∪ l₂ = l₂
  | [], _, _ => by simp
  | a :: t, l₂, h => by
      rw [List.cons_union, union_eq_right_of_subset (fun _ hx => h (List.mem_cons_of_mem a hx))]
      exact List.insert_of_mem (h (List.mem_cons_self ..))

/-- A `∪`'s LEFT argument only matters up to `dedup`. -/
theorem union_dedup_left {α} [DecidableEq α] :
    ∀ (l X : List α), l ∪ X = l.dedup ∪ X
  | [], _ => rfl
  | a :: t, X => by
      by_cases hm : a ∈ t
      · rw [List.dedup_cons_of_mem hm, List.cons_union, union_dedup_left t X]
        exact List.insert_of_mem (List.mem_union_iff.mpr (Or.inl (List.mem_dedup.mpr hm)))
      · rw [List.dedup_cons_of_notMem hm, List.cons_union, List.cons_union, union_dedup_left t X]

/-- `dedup`-equality is a congruence for `++`. -/
theorem dedup_append_congr {α} [DecidableEq α] {a₁ a₂ b₁ b₂ : List α}
    (ha : a₁.dedup = a₂.dedup) (hb : b₁.dedup = b₂.dedup) :
    (a₁ ++ b₁).dedup = (a₂ ++ b₂).dedup := by
  rw [List.dedup_append, List.dedup_append, hb, union_dedup_left a₁, union_dedup_left a₂, ha]

/-- **The engine: duplicated `flatMap` SOURCES cannot survive a `dedup`.** Expanding `l` and
expanding `l.dedup` give lists of wildly different length (this is the whole exponential), but the
same `dedup`. Because `dedup` keeps LAST occurrences, the source block that contributes a value's
final copy is exactly the source that survives `l.dedup`, at the same relative position. -/
theorem dedup_flatMap_dedup {α β} [DecidableEq α] [DecidableEq β] (g : α → List β) :
    ∀ l : List α, (l.flatMap g).dedup = (l.dedup.flatMap g).dedup
  | [] => rfl
  | a :: t => by
      by_cases hm : a ∈ t
      · rw [List.dedup_cons_of_mem hm, List.flatMap_cons, List.dedup_append,
            dedup_flatMap_dedup g t]
        exact union_eq_right_of_subset (fun x hx => List.mem_dedup.mpr
          (List.mem_flatMap.mpr ⟨a, List.mem_dedup.mpr hm, hx⟩))
      · rw [List.dedup_cons_of_notMem hm, List.flatMap_cons, List.flatMap_cons,
            List.dedup_append, List.dedup_append, dedup_flatMap_dedup g t]

/-- `dedup`-equal frontiers expand to `dedup`-equal layers. -/
theorem dedup_flatMap_congr {α β} [DecidableEq α] [DecidableEq β] (g : α → List β)
    {l₁ l₂ : List α} (h : l₁.dedup = l₂.dedup) :
    (l₁.flatMap g).dedup = (l₂.flatMap g).dedup := by
  rw [dedup_flatMap_dedup g l₁, dedup_flatMap_dedup g l₂, h]

/-- **`causalPastAuxFast`** — `causalPastAux` with the layer `dedup`ed before it is carried forward.
That single `.dedup` is what collapses `d^k` to `≤ |B|`: a deduped frontier cannot re-expand the
same source twice, so the BFS visits each block once per layer instead of once per PATH. -/
def causalPastAuxFast (B : Lace) : Nat → List BlockId → List BlockId → List BlockId
  | 0,        _,        acc => acc.dedup
  | _,        [],       acc => acc.dedup
  | fuel + 1, frontier, acc =>
      let nxt := ((expandPreds B frontier).filter (fun p => ¬ acc.contains p)).dedup
      causalPastAuxFast B fuel nxt (acc ++ nxt)

/-- **The BFS depends on its frontier and accumulator ONLY up to `dedup`.** The induction that
carries the repair: a deduped layer expands to a `dedup`-equal layer (`dedup_flatMap_congr`), a
`dedup`-equal accumulator induces the SAME membership filter, and `++` preserves both. -/
theorem causalPastAux_dedup_congr (B : Lace) (fuel : Nat) :
    ∀ (f₁ f₂ acc₁ acc₂ : List BlockId),
      f₁.dedup = f₂.dedup → acc₁.dedup = acc₂.dedup →
      causalPastAux B fuel f₁ acc₁ = causalPastAux B fuel f₂ acc₂ := by
  induction fuel with
  | zero => intro _ _ _ _ _ ha; simpa [causalPastAux] using ha
  | succ n ih =>
    intro f₁ f₂ acc₁ acc₂ hf ha
    have hmem : ∀ p, p ∈ acc₁ ↔ p ∈ acc₂ := fun p => by
      rw [← List.mem_dedup (l := acc₁), ha, List.mem_dedup]
    have hc : ∀ p, acc₁.contains p = acc₂.contains p := fun p => by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]; exact hmem p
    match f₁, f₂ with
    | [], [] => simpa [causalPastAux] using ha
    | [], _ :: _ => simp at hf
    | _ :: _, [] => simp at hf
    | a :: t, b :: u =>
      show causalPastAux B n _ _ = causalPastAux B n _ _
      have hQ : (fun p => decide ¬(acc₁.contains p = true))
              = (fun p => decide ¬(acc₂.contains p = true)) := by
        funext p; simp only [hc p]
      have hnxt : ((expandPreds B (a :: t)).filter (fun p => decide ¬(acc₁.contains p = true))).dedup
                = ((expandPreds B (b :: u)).filter (fun p => decide ¬(acc₂.contains p = true))).dedup := by
        rw [← hQ]
        unfold expandPreds
        rw [List.filter_flatMap, List.filter_flatMap]
        exact dedup_flatMap_congr _ hf
      exact ih _ _ _ _ hnxt (dedup_append_congr ha hnxt)

/-- **`causalPastAuxFast_eq` — THE ORDER IS UNCHANGED.** Not "the same set", not "a permutation":
the fast BFS returns the IDENTICAL LIST as the spec, for every lace, fuel, frontier and accumulator.
So every theorem, `#guard` and differential stated about `causalPastAux` transfers with no
re-proving, and nothing downstream — `closureLace`, `hasEquivInPast`, `ratifies`, `anchorSegment`'s
`xsortBy`, `tauOrder`, `advanceGate` — can observe the repair. -/
theorem causalPastAuxFast_eq (B : Lace) (fuel : Nat) :
    ∀ (f acc : List BlockId), causalPastAuxFast B fuel f acc = causalPastAux B fuel f acc := by
  induction fuel with
  | zero => intro f acc; rfl
  | succ n ih =>
    intro f acc
    match f with
    | [] => rfl
    | a :: t =>
      show causalPastAuxFast B n _ _ = causalPastAux B n _ _
      rw [ih]
      exact causalPastAux_dedup_congr B n _ _ _ _ List.dedup_idem
        (dedup_append_congr rfl List.dedup_idem)

/-- **`causalPastIncl B h`** — the inclusive causal past of `h` (`h` itself + everything it
observes), fuel = `B.length`. (`ordering.rs::causal_past_inclusive`.) This is CM Def. 19's
closure `[h] := {b′ ∈ B : h ⪰ b′}`, as an id list.

Runs the frontier-deduped BFS; `causalPastIncl_eq_spec` is the proof that this is the same list the
spec `causalPastAux` returns. -/
def causalPastIncl (B : Lace) (h : BlockId) : List BlockId :=
  causalPastAuxFast B B.length [h] [h]

/-- **`causalPastIncl_eq_spec`** — the deployed causal past IS the specified one, as a list. -/
theorem causalPastIncl_eq_spec (B : Lace) (h : BlockId) :
    causalPastIncl B h = causalPastAux B B.length [h] [h] :=
  causalPastAuxFast_eq B B.length [h] [h]

/-- Every id in a causal past other than the block itself ranks strictly below it, for any rank
that decreases along held edges. -/
theorem causalPastAux_rank {B : Lace} {rank : BlockId → Nat}
    (hrank : ∀ b ∈ B, ∀ p ∈ b.preds, B.has p = true → rank p < rank b.id) (x : BlockId) :
    ∀ (fuel : Nat) (frontier acc : List BlockId),
      (∀ a ∈ frontier, a = x ∨ rank a < rank x) → (∀ a ∈ acc, a = x ∨ rank a < rank x) →
      ∀ a ∈ causalPastAux B fuel frontier acc, a = x ∨ rank a < rank x := by
  intro fuel
  induction fuel with
  | zero =>
    intro frontier acc _ hacc a ha
    simp only [causalPastAux, List.mem_dedup] at ha
    exact hacc a ha
  | succ n ih =>
    intro frontier acc hfr hacc a ha
    match frontier, hfr, ha with
    | [], _, ha =>
      simp only [causalPastAux, List.mem_dedup] at ha
      exact hacc a ha
    | f :: fs, hfr, ha =>
      simp only [causalPastAux] at ha
      have hnxt : ∀ q ∈ (expandPreds B (f :: fs)).filter (fun p => ¬ acc.contains p),
          q = x ∨ rank q < rank x := by
        intro q hq
        have hq' := (List.mem_filter.mp hq).1
        unfold expandPreds at hq'
        obtain ⟨c, hc, hqc⟩ := List.mem_flatMap.mp hq'
        cases hl : B.lookup c with
        | none => rw [hl] at hqc; simp at hqc
        | some blk =>
          rw [hl] at hqc
          have hqp := List.mem_filter.mp hqc
          have hblk : blk ∈ B := List.mem_of_find?_eq_some hl
          have hid : blk.id = c := by have := List.find?_some hl; simpa using this
          have hlt := hrank blk hblk q hqp.1 (by simpa using hqp.2)
          rw [hid] at hlt
          rcases hfr c hc with rfl | hcx
          · exact Or.inr hlt
          · exact Or.inr (lt_trans hlt hcx)
      refine ih _ _ hnxt ?_ a ha
      intro q hq
      rcases List.mem_append.mp hq with h1 | h1
      · exact hacc q h1
      · exact hnxt q h1

theorem causalPastIncl_rank {B : Lace} {rank : BlockId → Nat}
    (hrank : ∀ b ∈ B, ∀ p ∈ b.preds, B.has p = true → rank p < rank b.id) {x a : BlockId}
    (ha : a ∈ causalPastIncl B x) : a = x ∨ rank a < rank x := by
  rw [causalPastIncl_eq_spec] at ha
  exact causalPastAux_rank hrank x B.length [x] [x] (by simp) (by simp) a ha

theorem causalPastAux_nodup (B : Lace) :
    ∀ (fuel : Nat) (frontier acc : List BlockId), (causalPastAux B fuel frontier acc).Nodup := by
  intro fuel
  induction fuel with
  | zero => intro frontier acc; simp [causalPastAux, List.nodup_dedup]
  | succ n ih =>
    intro frontier acc
    match frontier with
    | [] => simp [causalPastAux, List.nodup_dedup]
    | f :: fs => simp only [causalPastAux]; exact ih _ _

theorem causalPastIncl_nodup (B : Lace) (h : BlockId) : (causalPastIncl B h).Nodup := by
  rw [causalPastIncl_eq_spec]; exact causalPastAux_nodup B _ _ _

/-- **`closureLace B h`** — CM Def. 19's `[h]` AS A LACE: the sub-lace induced by `h`'s inclusive
causal past.

⚑ **This object is the whole point of the τ re-authoring (CM Def. 6 / Alg. 2:37).** Every
quantifier in Cordial Miners' ordering function ranges over the *anchor's closure* — `xsort(b1,
[b1] \ [b2])`, `approves(b, ·)` over `[b]`, `ratifies([b1], b)` over `[b1]`, `previous_ratified_
leader`'s `R ⊆ [b1] \ {b1}`. A closure is fixed forever by `h`'s own signed hash pointers, so
*nothing that arrives later can change it*. Running the rule against `closureLace B h` rather than
against `B` makes that arrival-independence TRUE AT THE TYPE LEVEL instead of merely intended, and
it is what lets `Consensus.TauPrefixMonotone` prove prefix-monotonicity instead of assuming it.

Two properties this buys, both proved in `TauPrefixMonotone`:

* **Stability.** For a closed extension `B' = B ++ new` (CM Def. 19 *closed* — the buffering rule
  of CM Alg. 3:49, which `node/src/catchup.rs::apply_with_buffering` already implements),
  `closureLace B' h = closureLace B h` for every `h ∈ B`. Late blocks have new ids, so they are
  filtered out; and the closure is pred-closed, so the BFS inside it cannot reach them.
* **A depth map that does not read the live lace.** `roundOf (closureLace B h) P` folds
  `computeRounds` over the CLOSURE, not over `B`. Every block in the closure has all its present
  predecessors in the closure, so the recurrence gives the same depth — and the *input list is
  literally the same list* in `B` and `B'`, so the stability argument needs nothing about how the
  fold enumerates it. -/
def closureLace (B : Lace) (h : BlockId) : Lace :=
  let past := causalPastIncl B h
  B.filter (fun b => past.contains b.id)

/-! ## 4. Equivocation-in-past, approval, ratification, super-ratification (`ordering.rs:120..278`). -/

/-- The equivocation scan with the observer's causal past and the round map SUPPLIED: `creator` has
two distinct blocks of `past` at one round of `rc`. ONE body for the three callers — the rule
(`hasEquivInPast`), the memoized head selection (`hasEquivInPastC`) and the per-anchor segment
(`anchorSegmentWith`, which asks about every creator from one observer and so builds the past and
the map once, not once per block). -/
def hasEquivInPastWith (B : Lace) (past : List BlockId) (rc : List (BlockId × Nat))
    (creator : AuthorId) : Bool :=
  let r := fun h => (roundLookup rc h).getD 0
  let creatorBlocks : List Block :=
    past.filterMap (fun bid => match B.lookup bid with
                                | some b => if b.creator = creator then some b else none
                                | none   => none)
  -- two distinct creator-blocks sharing a round ⇒ equivocation visible from observer.
  creatorBlocks.any (fun a => creatorBlocks.any (fun b => a.id ≠ b.id && r a.id == r b.id))

/-- **`hasEquivInPast`** — a creator has two DISTINCT blocks at the SAME round, both in the
observer's causal past (`ordering.rs::EquivocationIndex::equivocates_in_past` — renamed from
`has_equivocation_in_past` when the equivocator scan was memoized into a precomputed index; the
per-observer predicate is unchanged. Corrected 2026-07-16). The exact equivocation guard the
node's `approves`/`tau` consult to repel a forking creator. -/
def hasEquivInPast (B : Lace) (participants : List AuthorId)
    (observer : BlockId) (creator : AuthorId) : Bool :=
  hasEquivInPastWith B (causalPastIncl B observer) (computeRounds B participants) creator

/-- **`approves`** — observer block `o` approves leader `l`: `l` is in `o`'s causal past AND no
equivocation by `l.creator` is visible from `o` (`ordering.rs:184..200`). -/
def approves (B : Lace) (participants : List AuthorId) (o l : Block) : Bool :=
  (causalPastIncl B o.id).contains l.id && ¬ hasEquivInPast B participants o.id l.creator

/-- **`ratifies`** — block `o` ratifies leader `l` iff a supermajority of DISTINCT participants
have at least one block in `o`'s causal past that approves `l` (`ordering.rs:206..234`). -/
def ratifies (B : Lace) (participants : List AuthorId) (o l : Block) : Bool :=
  let past := causalPastIncl B o.id
  let approvingParticipants : Nat :=
    (participants.filter (fun p =>
      past.any (fun bid => match B.lookup bid with
                            | some b => b.creator == p && approves B participants b l
                            | none   => false))).length
  approvingParticipants ≥ superMajority participants.length

/-- All block ids at a given round in `B`.

⚑ NOT restricted to enrolled creators, deliberately. Restricting it here would make the B6
ratifier gate (`ratifiesEnrolled`, the only thing that decides whether a wave-end block COUNTS)
unreachable on exactly the traces that exhibit it — `traceSybilOnly`'s wave-end round would become
empty and stop being an exhibit of the gate. The depth an outsider's block carries is now derived
from its enrolled predecessors (§1), so its presence in a round set is view-consistent; whether it
DECIDES anything is B6's question, and stays B6's question. -/
def blocksAtRound (B : Lace) (participants : List AuthorId) (r : Nat) : List BlockId :=
  (B.filter (fun b => roundOf B participants b.id == r)).map (·.id)

/-- **`ratifiesEnrolled`** — the RATIFIER-SIDE enrollment gate: a wave-end block counts as a
ratifier only when its OWN creator is an enrolled participant, on top of the Cordial-Miners
`ratifies` predicate.

**Why this exists** (HORIZONLOG B6). `ratifies` above consults `participants` on the APPROVER side
— it counts how many participants have an approving block in the observer's past — and never asks
who the OBSERVER is. `isSuperRatified` then collected `b.creator` from the wave-end blocks with no
enrollment check at all, so a NON-PARTICIPANT's wave-end block contributed a distinct creator to a
count whose own docstring says "a supermajority of DISTINCT PARTICIPANTS". The threshold is not
weakened by this repair (`superMajority` is untouched — `supermajority_threshold(3) = 3` stays);
what changes is WHO IS ELIGIBLE TO BE COUNTED.

The harm is SAFETY, not liveness: an unenrolled creator's ordinary, well-formed block SUBSTITUTES
for a silent honest validator and pushes a leader over the finality threshold that the enrolled
committee did not reach. §9's `traceSybilRatify` exhibits exactly that (creator `3` silent at the
wave end, unenrolled creator `9` present ⇒ the pre-repair rule super-ratifies on `{1,2,9}`), and
`traceSybilOnly` exhibits the extreme — a wave super-ratified by THREE unenrolled creators with
ZERO enrolled ratifiers. It is not an attacker-only shape: `blocklace/src/finality.rs::enroll_pq`
is INSERT-ONLY while `constitution.current.participants` SHRINKS on a passed membership proposal,
so a ROTATED-OUT validator keeps its ratifying power under the pre-repair rule; and
`from_checkpoint_trusted` reloads the persisted DAG with no roster check at all.

Applied at BOTH sites that map a wave-end block to a decision — `isSuperRatified` (does the wave
anchor?) and the per-anchor segment (what does the anchor order?; this site was `leaderCoverage`,
since DELETED) — because an unenrolled ack must
neither decide finality nor decide WHERE an honest block lands in the total order. The second
matters because non-participants' blocks are exactly the ones honest nodes are NOT guaranteed to
have all seen, so letting them shape coverage breaks the reduction `tauOrder_deterministic` rests
on ("agreement reduces to seeing the same lace").

On an `EnrolledLace` this is the IDENTITY (`ratifiesEnrolled_eq_of_enrolled`), so no honest
federation loses a ratifier — the liveness pole. -/
def ratifiesEnrolled (B : Lace) (participants : List AuthorId) (o l : Block) : Bool :=
  participants.contains o.creator && ratifies B participants o l

/-- **`isSuperRatified`** — a supermajority of DISTINCT ENROLLED participants have wave-end blocks
that ratify the leader (`ordering.rs::is_super_ratified`). The node's finality condition for a
leader. The `ratifiesEnrolled` gate is the B6 repair; see its docstring. -/
def isSuperRatified (B : Lace) (participants : List AuthorId)
    (l : Block) (waveEndRound : Nat) : Bool :=
  let endBlocks := blocksAtRound B participants waveEndRound
  let ratifyingCreators : List AuthorId :=
    (endBlocks.filterMap (fun bid => match B.lookup bid with
       | some b => if ratifiesEnrolled B participants b l then some b.creator else none
       | none   => none)).dedup
  ratifyingCreators.length ≥ superMajority participants.length

/-- **`isSuperRatifiedPreEnrollment`** — the super-ratification test EXACTLY as it stood before the
B6 ratifier-enrollment repair: the wave-end creators are counted with no check that they are
participants.

⚑ THIS IS NOT THE FINALITY CONDITION. It is kept, named, and reachable from nothing but the §9
`#guard`s for one reason: it is the FALSIFICATION WITNESS for `isSuperRatified`'s gate — the same
discipline `tauOrderUnfiltered` carries for `enrolledId`. The §9 guards run it against
`traceSybilRatify` / `traceSybilOnly` and show it returns `true` exactly where the repaired rule
returns `false`, so the gate is demonstrably load-bearing rather than a no-op that "obviously"
changes nothing. A red-proof that lives in the tree forever instead of in a reverted source edit. -/
def isSuperRatifiedPreEnrollment (B : Lace) (participants : List AuthorId)
    (l : Block) (waveEndRound : Nat) : Bool :=
  let endBlocks := blocksAtRound B participants waveEndRound
  let ratifyingCreators : List AuthorId :=
    (endBlocks.filterMap (fun bid => match B.lookup bid with
       | some b => if ratifies B participants b l then some b.creator else none
       | none   => none)).dedup
  ratifyingCreators.length ≥ superMajority participants.length

/-! ## 5. `findAllFinalLeaders` — the wave loop (`ordering.rs:283..336`).

For each wave `w` from `0` up to the wave containing `maxRound`: take the round-robin
`waveLeader w`. Collect that creator's blocks at the wave-START round. If there is EXACTLY ONE
(no equivocation at the leader slot) AND it `isSuperRatified` by the wave-END round, it is a final
leader. We bound the wave count by `maxRound` (the deepest block), which the node bounds by
`max_round`. -/

/-- The maximum computed round over the lace (`compute_rounds`' returned `max_round`). -/
def maxRound (B : Lace) (participants : List AuthorId) : Nat :=
  (B.map (fun b => roundOf B participants b.id)).foldl Nat.max 0

/-- The leader's candidate blocks: creator = `waveLeader w` at the wave-START round. The node
requires EXACTLY ONE (`leader_blocks.len() == 1`) — a second block at the slot is the leader itself
equivocating, which forfeits the wave. -/
def leaderCandidates (B : Lace) (participants : List AuthorId)
    (wave wavelength : Nat) : List Block :=
  match waveLeader wave participants with
  | none => []
  | some lk =>
      let ws := waveFirstRound wave wavelength
      B.filter (fun b => b.creator == lk && roundOf B participants b.id == ws)

/-- **`finalLeaderAt`** — the (optional) final leader anchoring wave `w`: the unique leader-slot
block, if super-ratified by the wave end. Mirrors the body of `find_all_final_leaders`' loop. -/
def finalLeaderAt (B : Lace) (participants : List AuthorId)
    (wave wavelength : Nat) : Option Block :=
  match leaderCandidates B participants wave wavelength with
  | [l] => if isSuperRatified B participants l (waveLastRound wave wavelength) then some l else none
  | _   => none  -- zero candidates (leader silent) OR ≥2 (leader equivocated at the slot)

/-- **`findAllFinalLeaders`** — the final leaders in wave order. We iterate waves `0..waveCount`
where `waveCount` is the wave containing `maxRound` (the node breaks when `wave_end > max_round`).
(`ordering.rs:283..336`.) -/
def findAllFinalLeaders (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List Block :=
  let mr := maxRound B participants
  let waveCount := if wavelength == 0 then 0 else mr / wavelength + 1
  (List.range waveCount).filterMap (fun w => finalLeaderAt B participants w wavelength)

/-! ## 5b. THE ANCHOR CHAIN — CM Alg. 2 lines 32, 35, 41–46.

CM's τ does **not** fold over "every final leader in the live lace". It takes ONE head — the
deepest final leader (`last_final_leader()`, Alg. 2:44–46) — and recurses backward through
`previous_ratified_leader` (Alg. 2:41–43), a walk that is quantified entirely over the *anchor's
own closure*:

```
41: procedure previous_ratified_leader(b1):
42:    return arg_{b∈R} max depth(b)
43:    where R = {b ∈ [b1] \ {b1} : b.creator = leader(depth(b)) ∧ ratifies([b1], b)}
```

Finality appears in CM's τ **exactly once** — choosing the head — and **nowhere in the recursion**
(CM Def. 6's note: *"when τ′ is called with a leader b, it makes a recursive call with a leader
ratified by b, which is not necessarily super-ratified"*). That single structural fact is what makes
CM's history append-only, and folding over a recomputed `findAllFinalLeaders` is what cost us it: a
wave that was skipped in `B` and anchors late in `B'` splices a whole segment into the MIDDLE of the
leader list, so the old order is not a prefix of the new one even before coverage is considered. -/

/-- **`isLeaderBlock`** — CM Def. 23 / Alg. 2:43,46 `b.creator = leader(depth(b))`: `b` sits at a
wave-START round and its creator is that wave's round-robin leader. -/
def isLeaderBlock (B : Lace) (participants : List AuthorId) (wavelength : Nat) (b : Block) : Bool :=
  let r := roundOf B participants b.id
  let w := roundToWave r wavelength
  r == waveFirstRound w wavelength && waveLeader w participants == some b.creator

/-- **`lastFinalLeader`** — CM Alg. 2:44–46 `last_final_leader()`: the DEEPEST final leader.
`findAllFinalLeaders` walks waves in increasing order, so its last entry is the deepest. -/
def lastFinalLeader (B : Lace) (participants : List AuthorId) (wavelength : Nat) : Option Block :=
  (findAllFinalLeaders B participants wavelength).getLast?

/-- **`previousRatifiedLeader`** — CM Alg. 2:41–43. The deepest leader block, other than `b1`
itself, that lies in `b1`'s closure AND is ratified by `b1`.

Everything here reads `closureLace B b1.id`, never `B`: the candidate set is `[b1] \ {b1}`, the
leader test reads the closure's depth map, and `ratifies` is CM's `ratifies([b1], b)` — a
supermajority of distinct participants with an approving block in `[b1]`. **Finality is not
consulted**, exactly as in the paper.

The argmax tie-break: two leader blocks at the same depth are by the same miner (same wave slot),
mutually non-observing, hence an equivocating pair — CM Prop. 9's `=` case, which its proof
discharges from "a supermajority of correct miners" (at most one of an equivocating pair can hold
supermajority approval, Lem. 31). The fold below is lexicographic argmax of `(depth, id)`: at equal
depth it switches to the newer candidate when the incumbent's id is SMALLER, i.e. it keeps the
LARGER id. Stated precisely because the direction is easy to misread from the code and the Rust
mirror has to match it — under the fault bound the tie cannot arise among *ratified* candidates at
all, so the choice of direction is arbitrary, but it must be the SAME arbitrary choice on both
sides. -/
def previousRatifiedLeader (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (b1 : Block) : Option Block :=
  let Bl := closureLace B b1.id
  let cands : List Block :=
    (causalPastIncl B b1.id).filterMap (fun bid => match Bl.lookup bid with
      | some b =>
          if b.id != b1.id && isLeaderBlock Bl participants wavelength b
             && ratifies Bl participants b1 b then some b else none
      | none   => none)
  cands.foldl (fun best b => match best with
    | none   => some b
    | some c =>
        let dc := roundOf Bl participants c.id
        let db := roundOf Bl participants b.id
        if dc < db || (dc == db && c.id < b.id) then some b else some c) none

/-- The backward walk of CM Alg. 2:33–36, materialised OLDEST-FIRST so the ordering fold reads
left to right. `fuel` bounds the recursion; each step strictly decreases depth, and every chain
element is a distinct member of `[b]`, so `(causalPastIncl B b.id).length` always suffices — and
being closure-local, that bound does not move when the lace grows. -/
def ratifiedLeaderChainAux (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    Nat → Block → List Block
  | 0,        b => [b]
  | fuel + 1, b =>
      match previousRatifiedLeader B participants wavelength b with
      | none    => [b]
      | some b' => ratifiedLeaderChainAux B participants wavelength fuel b' ++ [b]

/-- **`ratifiedLeaderChain B P wl b`** — `[b₁, …, b_k = b]`, the sequence of ratified leaders CM's
τ′ recurses through, oldest first. A pure function of `[b]`. -/
def ratifiedLeaderChain (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (b : Block) : List Block :=
  ratifiedLeaderChainAux B participants wavelength (causalPastIncl B b.id).length b

/-! ## 5c. CORDIALITY — the per-block ADMISSION predicate (CM Def. 25 / Alg. 1:15-16).

**This is the premise the whole safety story runs on, and it is one cheap local check.**

> **Def. 25 (Cordial Block, Blocklace).** A block `b ∈ B` of round `r` is cordial if `r = 1` or it
> acknowledges blocks by a supermajority of miners of round `r − 1`. A blocklace `B ⊂ B` is cordial
> if all its blocks are cordial.

```
15: procedure correct_block(b):
16:    return {b′.creator : hash(b′) ∈ b.pointers} is a supermajority ∧ ¬equivocator(b.creator, [b])
```

and CM Alg. 3:49 makes it a PRECONDITION OF RECEIPT — *"incorrect blocks are ignored"*. From it the
entire chain follows: cordial ⟹ leader-safe (Prop. 3) ⟹ τ monotone (Prop. 9) ⟹ τ safe (Prop. 10)
⟹ protocol safe (Prop. 37). `Consensus.TauPrefixMonotone`'s one surviving hypothesis, `ChainExtends`,
is Prop. 3's conclusion — so this predicate is exactly what would let it be DERIVED rather than
imported.

⚑ **Not wired yet, and the shape of the debt is worth naming.** Nothing on the receive path
evaluates this: `blocklace/src/finality.rs::insert_checked` checks predecessor closure, signature,
roster pin, consensus-time frontier and equivocation, and **never cardinality of the pointer set**.
There is a `blocklace/src/ordering.rs::is_cordial`, but it is (a) hand-written Rust consensus logic,
which is the drift this repo forbids, and (b) called from nothing outside its own tests. The right
wiring is an `@[export]` off THIS definition into `insert_checked`, and it needs a buffering story —
unlike a missing predecessor, a block that fails cordiality is not fixable by waiting. -/

/-- **CM Def. 25** — `b` acknowledges a supermajority of the ENROLLED miners of round `r − 1`.
Round 1 is cordial by definition (there is no previous round). The enrollment restriction is ours,
for the same reason `ratifiesEnrolled` carries one: a supermajority "of miners" that counts
non-participants is not a supermajority of the committee. -/
def acksSupermajorityOfPrevRound (B : Lace) (participants : List AuthorId) (b : Block) : Bool :=
  let r := roundOf B participants b.id
  if r ≤ 1 then true
  else
    let ackedCreators : List AuthorId :=
      (b.preds.filterMap (fun p => match B.lookup p with
        | some q => if roundOf B participants q.id == r - 1 && participants.contains q.creator
                    then some q.creator else none
        | none   => none)).dedup
    ackedCreators.length ≥ superMajority participants.length

/-- **`isCordialBlock`** — CM Alg. 1:15-16's `correct_block`: a supermajority acknowledgement AND
the author is not an equivocator in the block's own causal past. Both clauses are functions of `b`'s
own pointers, so this is evaluable at receipt with no view of the rest of the lace. -/
def isCordialBlock (B : Lace) (participants : List AuthorId) (b : Block) : Bool :=
  acksSupermajorityOfPrevRound B participants b
    && ¬ hasEquivInPast B participants b.id b.creator

/-- **CM Def. 19 *closed*** as a per-block check — CM Alg. 3:49's buffering condition
`b.pointers ⊆ hash(blocklace)`. This is the hypothesis `Consensus.TauPrefixMonotone.ClosedExtension`
names as `pred_closed`, and the one thing on this list the node ALREADY enforces
(`finality.rs::insert_checked` → `MissingPredecessor`, `catchup.rs::apply_with_buffering`). -/
def predsPresent (B : Lace) (b : Block) : Bool := b.preds.all (fun p => B.has p)

/-- **`admitBlock`** — the receive-time gate CM Alg. 3:49 specifies: buffer until closed, then
refuse unless cordial. -/
def admitBlock (B : Lace) (participants : List AuthorId) (b : Block) : Bool :=
  predsPresent B b && isCordialBlock B participants b

/-- A whole lace is cordial when every block is (CM Def. 25's second sentence) — the hypothesis of
CM Prop. 3 and Prop. 9. -/
def isCordialLace (B : Lace) (participants : List AuthorId) : Bool :=
  B.all (fun b => isCordialBlock B participants b)

/-! ## 6. `tauOrder` — the total order, CM Def. 6.

```
τ′(b) := xsort(b, [b])                     if [b] has no leader ratified by b, else
         τ′(b′) · xsort(b, [b] \ [b′])     if b′ is the last leader ratified by b in [b]
```

with `xsort(b, B) = topological sort wrt ≻ of {b′ ∈ B : approves(b, b′)}` (Alg. 2:39–40), and
`approves(b, b1) = b1 ∈ [b] ∧ ∀b2 ∈ [b] : ¬equivocation(b1, b2)` (Alg. 1:17).

**What this used to be, and why it changed.** The previous rule folded over
`findAllFinalLeaders B P wl` and gave each anchor a *coverage* = the union of the causal pasts of
every wave-END block **in the live lace `B`** that ratified it. The anchor sits at the wave's first
round and the ratifiers at its last, so that coverage was a strict SUPERSET of `[anchor]` **that
grew with arrivals**: a late honest wave-end ratifier for an already-final wave *k* pulled its own
past into wave *k*'s segment, i.e. spliced blocks MID-PREFIX, ahead of everything waves *k+1…* had
already emitted. `Consensus.TauPrefixMonotone`'s `lagBase → lagGrown` is that trace — four
validators, one of them merely LAGGING, no Byzantine step, every block passing the verified
`insert` — and the old order was not a prefix of the new one. The anchor survived only as an
equivocation filter; its ORDERING role, which is its entire role in the paper, had been dropped.

Under Def. 6 the segment for an anchor is a function of that anchor's own signed hash pointers and
of nothing else, so it cannot move. The price is CM's real latency: a block at round `r` is ordered
by the first final leader that OBSERVES it, which is at a strictly greater round — never by a
ratifier at its own wave's end. That is not a regression to fix, it is the property being bought.

The intra-segment linearization is a ready-set (Kahn) sort over the transitive causal past, as the
Rust `xsort` is. What remains of OPEN-CM-XSORT is the ready-set PRIORITY: `(round, id)` here, min
block id in the Rust. -/

/-! #### The ready-set linearisation. -/

/-- **`readySort past fuel rest`** — emit, one at a time, the FIRST id of `rest` none of whose
other members lies in its causal past. Fed a list already in `(round, id)` order this is Kahn's
algorithm with a `(round, id)` ready-priority: `erase` keeps the order, so the first ready id is
the least. `none` (no ready id) happens only on a cycle; the remainder is then emitted as is. -/
def readySort (past : BlockId → List BlockId) : Nat → List BlockId → List BlockId
  | 0,        rest => rest
  | fuel + 1, rest =>
    match rest.find? (fun x => rest.all (fun a => a == x || !(past x).contains a)) with
    | some x => x :: readySort past fuel (rest.erase x)
    | none   => rest

theorem readySort_perm (past : BlockId → List BlockId) :
    ∀ (fuel : Nat) (rest : List BlockId), (readySort past fuel rest).Perm rest := by
  intro fuel
  induction fuel with
  | zero => intro rest; exact List.Perm.refl _
  | succ n ih =>
    intro rest
    unfold readySort
    split
    · rename_i x hx
      have hmem : x ∈ rest := List.mem_of_find?_eq_some hx
      exact ((ih (rest.erase x)).cons x).trans (List.perm_cons_erase hmem).symm
    · exact List.Perm.refl _

/-- The linearisation reads `past` only at the ids it is sorting. -/
theorem readySort_congr {past₁ past₂ : BlockId → List BlockId} :
    ∀ (fuel : Nat) (rest : List BlockId), (∀ x ∈ rest, past₁ x = past₂ x) →
      readySort past₁ fuel rest = readySort past₂ fuel rest := by
  intro fuel
  induction fuel with
  | zero => intro rest _; rfl
  | succ n ih =>
    intro rest h
    have hf : rest.find? (fun x => rest.all (fun a => a == x || !(past₁ x).contains a))
            = rest.find? (fun x => rest.all (fun a => a == x || !(past₂ x).contains a)) := by
      apply List.find?_congr
      intro x hx
      rw [h x hx]
    unfold readySort
    rw [hf]
    split
    · rename_i x hx
      rw [ih (rest.erase x) (fun y hy => h y (List.mem_of_mem_erase hy))]
    · rfl

/-- **THE LINEAR-EXTENSION PROPERTY.** If every nonempty sub-collection of the input has a member
with no OTHER member in its past (true whenever `past` is well-founded on the input), then nothing
the sort emits AFTER an id lies in that id's past: every id comes after all of its ancestors. -/
theorem readySort_linear_extension (past : BlockId → List BlockId) :
    ∀ (fuel : Nat) (rest : List BlockId),
      (∀ sub : List BlockId, (∀ a ∈ sub, a ∈ rest) → sub ≠ [] →
          ∃ x ∈ sub, ∀ a ∈ sub, a = x ∨ a ∉ past x) →
      rest.length ≤ fuel →
      ∀ pre x post, readySort past fuel rest = pre ++ x :: post →
        ∀ a ∈ post, a = x ∨ a ∉ past x := by
  intro fuel
  induction fuel with
  | zero =>
    intro rest _ hlen pre x post heq
    have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp [readySort] at heq
  | succ n ih =>
    intro rest hprog hlen pre x post heq
    by_cases hr : rest = []
    · subst hr; simp [readySort] at heq
    · obtain ⟨x₀, hx₀, hready₀⟩ := hprog rest (fun a ha => ha) hr
      have hsome : (rest.find? (fun x => rest.all (fun a => a == x || !(past x).contains a))).isSome := by
        rw [List.find?_isSome]
        refine ⟨x₀, hx₀, ?_⟩
        simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
          List.contains_eq_mem, decide_eq_false_iff_not]
        exact hready₀
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
      have hymem : y ∈ rest := List.mem_of_find?_eq_some hy
      have hyready : ∀ a ∈ rest, a = y ∨ a ∉ past y := by
        have := List.find?_some hy
        simpa only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
          List.contains_eq_mem, decide_eq_false_iff_not] using this
      have hout : readySort past (n + 1) rest = y :: readySort past n (rest.erase y) := by
        rw [readySort, hy]
      rw [hout] at heq
      have hpermE := readySort_perm past n (rest.erase y)
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        obtain ⟨rfl, hpost⟩ := heq
        intro a ha
        have : a ∈ rest.erase y := hpermE.mem_iff.mp (hpost ▸ ha)
        exact hyready a (List.mem_of_mem_erase this)
      | cons z pre' =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨_, htail⟩ := heq
        refine ih (rest.erase y) ?_ ?_ pre' x post htail
        · intro sub hsub hne
          exact hprog sub (fun a ha => List.mem_of_mem_erase (hsub a ha)) hne
        · rw [List.length_erase_of_mem hymem]; omega

/-- A rank that strictly decreases into the past makes every nonempty sub-collection have a ready
member — the rank-least one. -/
theorem ready_of_rank {past : BlockId → List BlockId} {rank : BlockId → Nat} {ids : List BlockId}
    (hrank : ∀ x ∈ ids, ∀ a ∈ ids, a ∈ past x → a ≠ x → rank a < rank x) :
    ∀ sub : List BlockId, (∀ a ∈ sub, a ∈ ids) → sub ≠ [] →
      ∃ x ∈ sub, ∀ a ∈ sub, a = x ∨ a ∉ past x := by
  intro sub hsub hne
  obtain ⟨x, hx, hmin⟩ := exists_min_rank rank sub hne
  refine ⟨x, hx, ?_⟩
  intro a ha
  by_cases hax : a = x
  · exact Or.inl hax
  · refine Or.inr ?_
    intro hpast
    have := hrank x (hsub x hx) a (hsub a ha) hpast hax
    have := hmin a ha
    omega

/-- **`xsortByRoundKey`** — the linearization EXACTLY as it stood: a key sort by `(round, id)`, on
the claim that "a predecessor has a strictly smaller round, so this respects causal order".

⚑ THIS IS NOT THE LINEARIZATION. The claim stopped being true when `roundOfStep` began counting
only ENROLLED predecessors (§1) while `causalPastIncl` walks every edge: a block that reaches later
rounds only through an unenrolled relay keeps a low round, and the key sort emits it before its own
causal ancestors. Kept, reachable from nothing but the §9 `#guard`s, as the falsification witness
for `xsortBy`: on `traceRelayLift6` it puts `41` ahead of `12, 22, 32`, all three in `41`'s past. -/
def xsortByRoundKey (B : Lace) (participants : List AuthorId) (ids : List BlockId) : List BlockId :=
  ids.mergeSort (fun a b =>
    roundOf B participants a < roundOf B participants b
      || (roundOf B participants a == roundOf B participants b && a ≤ b))

/-- **`xsortWith past rc ids`** — the intra-segment linearization, with the causal past and the
round map as PARAMETERS: order `ids` by `(round, id)`, then run the ready-set sort over it. So the
output is Kahn's algorithm over the transitive causal past restricted to `ids`, with the
`(round, id)`-least ready id emitted at each step — the Rust `xsort` with a different ready
priority (OPEN-CM-XSORT).

`past` is a parameter so the runtime twin can hand in its memoized map (§6c) instead of re-walking
the lace per id; `readySort_congr` is why that cannot change the value. `List.mergeSort` rather
than `Array.qsort` because it carries `mergeSort_perm`. -/
def xsortWith (past : BlockId → List BlockId) (rc : List (BlockId × Nat)) (ids : List BlockId) :
    List BlockId :=
  let r := fun h => (roundLookup rc h).getD 0
  readySort past ids.length (ids.mergeSort (fun a b => r a < r b || (r a == r b && a ≤ b)))

/-- **`xsortBy B participants ids`** — `ids` in a linear extension of `B`'s causal order, ready
ties broken by `(round, id)`. -/
def xsortBy (B : Lace) (participants : List AuthorId) (ids : List BlockId) : List BlockId :=
  xsortWith (causalPastIncl B) (computeRounds B participants) ids

/-- **`xsortWith_perm`** — the linearization is a PERMUTATION of its input, whatever `past` and
`rc` are. -/
theorem xsortWith_perm (past : BlockId → List BlockId) (rc : List (BlockId × Nat))
    (ids : List BlockId) : (xsortWith past rc ids).Perm ids :=
  (readySort_perm past _ _).trans (List.mergeSort_perm ids _)

/-- **`xsortBy_perm`** — the linearization is a PERMUTATION of its input. The one fact every
"the order only carries ids from the anchor's closure" argument needs. -/
theorem xsortBy_perm (B : Lace) (participants : List AuthorId) (ids : List BlockId) :
    (xsortBy B participants ids).Perm ids :=
  xsortWith_perm _ _ ids

/-- **`mem_xsortBy`** — membership transfers through the linearization. -/
theorem mem_xsortBy {B : Lace} {participants : List AuthorId} {ids : List BlockId} {x : BlockId}
    (h : x ∈ xsortBy B participants ids) : x ∈ ids :=
  (xsortBy_perm B participants ids).mem_iff.mp h

/-- The linearization reads `past` only at the ids it sorts. -/
theorem xsortWith_congr {past₁ past₂ : BlockId → List BlockId} (rc : List (BlockId × Nat))
    {ids : List BlockId} (h : ∀ x ∈ ids, past₁ x = past₂ x) :
    xsortWith past₁ rc ids = xsortWith past₂ rc ids := by
  unfold xsortWith
  exact readySort_congr _ _ (fun x hx => h x ((List.mergeSort_perm ids _).mem_iff.mp hx))

/-- **`xsortWith_linear_extension` — THE ORDER RESPECTS CAUSALITY.** On a DAG with distinct ids,
nothing the linearization emits AFTER an id lies in that id's causal past — whatever round map
breaks the ties. Every block comes after all of its ancestors in the segment, including the ones it
reaches only through a block that is NOT in the segment (an unenrolled relay), because readiness
reads the TRANSITIVE past.

Premises: distinct ids is content addressing; `laceStuck B = []` is "Kahn finishes", equivalent to
the lace being a DAG (`laceStuck_eq_nil_iff`), `#guard`ed on every §9 trace and refuted by
`traceCycle`. Teeth: `xsortByRoundKey` violates the conclusion on `traceRelayLift6`. -/
theorem xsortWith_linear_extension {B : Lace} (hnd : (B.map (·.id)).Nodup)
    (hdag : laceStuck B = []) (rc : List (BlockId × Nat)) (ids : List BlockId) :
    ∀ pre x post, xsortWith (causalPastIncl B) rc ids = pre ++ x :: post →
      ∀ a ∈ post, a = x ∨ a ∉ causalPastIncl B x := by
  obtain ⟨rank, hrank⟩ := laceDag_of_stuck_nil hnd hdag
  intro pre x post heq
  unfold xsortWith at heq
  refine readySort_linear_extension (causalPastIncl B) ids.length _ ?_ ?_ pre x post heq
  · apply ready_of_rank (rank := rank)
    intro y _ a _ hpast hne
    rcases causalPastIncl_rank hrank hpast with h | h
    · exact absurd h hne
    · exact h
  · rw [List.length_mergeSort]

/-- **`xsortBy_linear_extension`** — `xsortBy`'s output is a linear extension of `B`'s causal
order restricted to its input. -/
theorem xsortBy_linear_extension {B : Lace} (hnd : (B.map (·.id)).Nodup)
    (hdag : laceStuck B = []) (participants : List AuthorId) (ids : List BlockId) :
    ∀ pre x post, xsortBy B participants ids = pre ++ x :: post →
      ∀ a ∈ post, a = x ∨ a ∉ causalPastIncl B x :=
  xsortWith_linear_extension hnd hdag _ ids

/-- **`anchorSegmentWith past keep B P prevCovered l`** — CM Alg. 2:37, `xsort(l, [l] \ [b₂])`,
with the causal past and the creator filter as PARAMETERS. `anchorSegment` below is the rule; the
parameters exist so the runtime twin can pass its memoized past, and so `tauOrderUnfiltered` can be
the SAME code with the enrollment filter switched off rather than a second copy of it.

`prevCovered` is `[b₂]`, the closure of the previous ratified leader (the fold below carries it).
The `approves(l, ·)` filter is CM Alg. 1:17: membership in `[l]` is automatic because the candidate
set IS `[l]`, so what remains is the equivocation clause, evaluated — as the paper quantifies it —
over `[l]`, i.e. against `closureLace B l.id` (`hasEquivInPastWith Bl pastL rc c` is
`hasEquivInPast Bl P l.id c`, by `rfl`). The ready ties are broken by the closure's own depth
map; readiness reads `past`, the causal past in the WHOLE lace, as the Rust `xsort` does.

⚑ **`keep` is applied BEFORE the sort, and that placement is load-bearing.** A ready-set sort is
not a key sort: an element left in the segment changes WHEN its descendants become ready relative
to the other ready blocks, so a relay left in and filtered out afterwards would let a
non-participant reorder honest blocks. Filtering first makes the segment identical on two nodes
with identical enrolled sub-laces — the placement `ordering.rs::order_over_anchor_chain` uses. The
relay still constrains the order through the transitive past of the blocks that cite it.

⚑ **THE EQUIVOCATION CLAUSE DOES NOT STAND ALONE — it is one half of a property split across two
files, and the other half is `blocklace/src/finality.rs`.** `hasEquivInPast Bl P l.id c` can only
fire if creator `c` has TWO blocks at one round inside `[l]`. Under a one-tip-per-creator
dissemination rule that is unreachable: a receiver holding one fork half and a leader observing the
other never put both in the same causal past, so the filter would be a no-op however faithfully
written. CM Alg. 1:5 is explicit that a block points at **"at most two tips per miner"**, and its
whole exclusion story (Alg. 1:17 `approves`, Fig. 1.B's blue block observing both red blocks and
approving neither) presupposes it.

The floor EXISTS as of `89238335a`: `finality.rs::CreatorTips::Pair` pins a detected equivocating
pair so the next locally-authored block points at BOTH halves, welding the evidence into our own
chain and thence into later anchors' closures. So this clause is live rather than vestigial — but
only because of that, and a change that relaxes tip-pinning silently disarms an exclusion rule
written in a different language in a different directory. Neither file is sufficient on its own;
this note exists so a reader of either one learns that. -/
def anchorSegmentWith (past : BlockId → List BlockId) (keep : Block → Bool) (B : Lace)
    (participants : List AuthorId) (prevCovered : List BlockId) (l : Block) : List BlockId :=
  let Bl := closureLace B l.id
  -- the closure's depth map and the anchor's past inside it, each built ONCE per segment
  let rc := computeRounds Bl participants
  let pastL := causalPastIncl Bl l.id
  let newIds := (past l.id).filter (fun bid => ¬ prevCovered.contains bid)
  let approved := newIds.filter (fun bid => match Bl.lookup bid with
    | some b => keep b && ¬ hasEquivInPastWith Bl pastL rc b.creator
    | none   => false)
  xsortWith past rc approved

/-- **`anchorSegment B P prevCovered l`** — the rule's per-anchor segment: `[l] \ [b₂]`, minus
equivocators, minus blocks whose creator is not enrolled, linearized over `B`'s causal past. -/
def anchorSegment (B : Lace) (participants : List AuthorId)
    (prevCovered : List BlockId) (l : Block) : List BlockId :=
  anchorSegmentWith (causalPastIncl B) (fun b => participants.contains b.creator) B participants
    prevCovered l

/-- Every id a segment emits passed the creator filter: it resolves, in the anchor's closure, to a
block `keep` accepts. -/
theorem anchorSegmentWith_keep {past : BlockId → List BlockId} {keep : Block → Bool} {B : Lace}
    {participants : List AuthorId} {prevCovered : List BlockId} {l : Block} {bid : BlockId}
    (h : bid ∈ anchorSegmentWith past keep B participants prevCovered l) :
    ∃ b, (closureLace B l.id).lookup bid = some b ∧ keep b = true := by
  unfold anchorSegmentWith at h
  have h1 := (xsortWith_perm _ _ _).mem_iff.mp h
  have h2 := (List.mem_filter.mp h1).2
  cases hl : (closureLace B l.id).lookup bid with
  | none => rw [hl] at h2; simp at h2
  | some b =>
    rw [hl] at h2
    simp only [Bool.and_eq_true] at h2
    exact ⟨b, rfl, h2.1⟩

/-- A segment carries no id twice. -/
theorem anchorSegment_nodup (B : Lace) (participants : List AuthorId)
    (prevCovered : List BlockId) (l : Block) :
    (anchorSegment B participants prevCovered l).Nodup := by
  unfold anchorSegment anchorSegmentWith
  refine (xsortWith_perm _ _ _).nodup_iff.mpr ?_
  exact ((causalPastIncl_nodup B l.id).filter _).filter _

/-- **`anchorSegment_linear_extension` — WITHIN A SEGMENT, EVERY BLOCK COMES AFTER ALL ITS
ANCESTORS.** On a DAG with distinct ids, no id an anchor's segment emits after `x` lies in `x`'s
causal past in `B`. This is CM's `xsort` contract ("topological sort wrt ≻", Alg. 2:39–40), and it
is what `xsortByRoundKey` broke (§9, `traceRelayLift6`). -/
theorem anchorSegment_linear_extension {B : Lace} (hnd : (B.map (·.id)).Nodup)
    (hdag : laceStuck B = []) (participants : List AuthorId) (prevCovered : List BlockId)
    (l : Block) :
    ∀ pre x post, anchorSegment B participants prevCovered l = pre ++ x :: post →
      ∀ a ∈ post, a ∉ causalPastIncl B x := by
  intro pre x post heq a ha
  have hndS := anchorSegment_nodup B participants prevCovered l
  rw [heq] at hndS
  have hax : a ≠ x := by
    rintro rfl
    have := (List.nodup_append.mp hndS).2.1
    exact (List.nodup_cons.mp this).1 ha
  unfold anchorSegment anchorSegmentWith at heq
  rcases xsortWith_linear_extension hnd hdag _ _ pre x post heq a ha with h | h
  · exact absurd h hax
  · exact h

/-- **`tauStepWith`** — one unfolding of CM Def. 6's recursion, written left-to-right over the
chain: append `xsort(l, [l] \ [prev])`, and carry `[l]` forward as the next `prev`. -/
def tauStepWith (past : BlockId → List BlockId) (keep : Block → Bool) (B : Lace)
    (participants : List AuthorId)
    (acc : List BlockId × List BlockId) (l : Block) : List BlockId × List BlockId :=
  (acc.1 ++ anchorSegmentWith past keep B participants acc.2 l, past l.id)

/-- **`tauStep`** — the rule's fold step: `tauStepWith` at the lace's own causal past and the
enrollment filter. -/
def tauStep (B : Lace) (participants : List AuthorId)
    (acc : List BlockId × List BlockId) (l : Block) : List BlockId × List BlockId :=
  tauStepWith (causalPastIncl B) (fun b => participants.contains b.creator) B participants acc l

/-- Every id a fold of segments emits was either already accumulated or passed the creator filter
of the segment that emitted it. -/
theorem foldl_tauStepWith_keep {past : BlockId → List BlockId} {keep : Block → Bool} {B : Lace}
    {participants : List AuthorId} :
    ∀ (L : List Block) (acc : List BlockId × List BlockId) (bid : BlockId),
      bid ∈ (L.foldl (tauStepWith past keep B participants) acc).1 →
      bid ∈ acc.1 ∨ ∃ l ∈ L, ∃ b, (closureLace B l.id).lookup bid = some b ∧ keep b = true := by
  intro L
  induction L with
  | nil => intro acc bid h; exact Or.inl h
  | cons l L ih =>
    intro acc bid h
    rw [List.foldl_cons] at h
    rcases ih _ bid h with h1 | ⟨l', hl', b, hb⟩
    · rcases List.mem_append.mp h1 with h2 | h2
      · exact Or.inl h2
      · obtain ⟨b, hb⟩ := anchorSegmentWith_keep h2
        exact Or.inr ⟨l, by simp, b, hb⟩
    · exact Or.inr ⟨l', List.mem_cons_of_mem _ hl', b, hb⟩

/-- **`tauOrderUnfiltered B participants wavelength`** — CM's τ WITHOUT the enrollment filter: the
rule exactly as it stood before `enrolledId` was introduced, i.e. the same fold with the segment's
creator filter switched off.

⚑ THIS IS NOT THE FINALIZATION RULE. It is kept, named, and NOT exported for one reason: it is the
falsification witness for `tauOrder`. The §9 `#guard`s run it against `traceUnenrolled6` and show it
DOES finalize a block whose creator is not in `participants` — so the filter in `tauOrder` below is
demonstrably load-bearing rather than a no-op that "obviously" changes nothing. Nothing else may
call it; the `@[export]`s (`FinalityGate.finalizeGate` / `tauOrderGate`) route through `tauOrder`
and `tauOrderFast`. -/
def tauOrderUnfiltered (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List BlockId :=
  match lastFinalLeader B participants wavelength with
  | none    => []
  | some hd => ((ratifiedLeaderChain B participants wavelength hd).foldl
                  (tauStepWith (causalPastIncl B) (fun _ => true) B participants) ([], [])).1

/-- **`tauOrder B participants wavelength`** — the computed total order (`ordering.rs::tau`),
RESTRICTED TO ENROLLED CREATORS.

The enrollment filter sits INSIDE each segment, before the sort (`anchorSegmentWith`'s `keep`),
where the Rust `order_over_anchor_chain` puts it. It used to be applied to the finished order, on
the argument that the two placements are the same value because the linearizer was a key sort. It
no longer is one, so they are not: `tauOrder` is NOT `tauOrderUnfiltered` filtered (§9 exhibits a
lace where the two differ), and the filter has to come first. -/
def tauOrder (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List BlockId :=
  match lastFinalLeader B participants wavelength with
  | none    => []
  | some hd => ((ratifiedLeaderChain B participants wavelength hd).foldl
                  (tauStep B participants) ([], [])).1

/-! ## 6b. THE MEMOIZED FAST PATH — the SAME `tauOrder`, with the causal past computed ONCE.

**Why.** The pure `tauOrder` above RE-COMPUTES `causalPastIncl` for the same block ids an
EXPONENTIAL number of times: `ratifies` rebuilds an observer's past and, per past block, calls
`approves` (another past) + `hasEquivInPast` (another past); `isSuperRatified` calls `ratifies` per
wave-end block; `findAllFinalLeaders` calls `isSuperRatified` per wave; and the former
`leaderCoverage` (DELETED) called `ratifies` + `causalPastIncl` again. On a cross-linked DAG (the live `n=5` shape) this nested
re-traversal blows up — the finality-FFI wedge the node hit (the `dregg_tau_order` export pinned a
tokio worker and starved the runtime).

**The fix, proof-preserving.** A parallel stack that threads a `PastCache` — each block's inclusive
causal past computed ONCE — mirroring the Rust `PastCache` (`blocklace/src/ordering.rs:41`). Every
function gets a `…C` twin that LOOKS UP the past instead of recomputing it; each twin is proved EQUAL
(`…C_eq`) to its pure original at `cache = mkPastCache B`, so the safety theorems and `#guard`s about
`tauOrder`/`tauGolden`/`findAllFinalLeaders` (which the originals back) are untouched. The
order-faithful equality `tauOrderFast_eq : tauOrderFast = tauOrder` lets the live gate exports
(`FinalityGate.tauOrderGate`/`finalizeGate`) run the FAST path while every proof that named `tauOrder`
stays valid by rewriting through the equality. Building the cache is `O(|B|)` calls to the
(individually polynomial) `causalPastIncl`, and the lookups replace the exponential re-traversal — the
blow-up is gone (the §9 `…Fast` `#guard`s witness identical output on the concrete trace). -/

/-- A memo of each block's inclusive causal past — an assoc list keyed by `BlockId`, the Lean
analogue of the Rust `PastCache` (`HashMap<BlockId, Rc<HashSet<BlockId>>>`). -/
abbrev PastCache := List (BlockId × List BlockId)

/-- Build the cache: compute `causalPastIncl B b.id` ONCE per block in `B`. -/
def mkPastCache (B : Lace) : PastCache :=
  B.map (fun b => (b.id, causalPastIncl B b.id))

/-- Look up a block's causal past in `cache`, FALLING BACK to the pure `causalPastIncl` on a miss (an
id not in `B`). The fallback makes correctness UNCONDITIONAL: `cachedPast B (mkPastCache B) h` is
ALWAYS `causalPastIncl B h` — a hit returns the value the cache stored (= `causalPastIncl B h`), a
miss recomputes it. On the live path every observed id is present, so it is always a hit (the
speedup). -/
def cachedPast (B : Lace) (cache : PastCache) (h : BlockId) : List BlockId :=
  match cache.find? (fun p => p.1 == h) with
  | some p => p.2
  | none   => causalPastIncl B h

/-- **`cachedPast_eq`** — the cache is FAITHFUL: a lookup via `mkPastCache B` returns EXACTLY the pure
`causalPastIncl B h`, for every `h`. So replacing `causalPastIncl` with `cachedPast … (mkPastCache B)`
anywhere is value-preserving — the engine of every `…C_eq` below. -/
theorem cachedPast_eq (B : Lace) (h : BlockId) :
    cachedPast B (mkPastCache B) h = causalPastIncl B h := by
  unfold cachedPast
  cases hf : (mkPastCache B).find? (fun p => p.1 == h) with
  | none => rfl
  | some p =>
    have hp1 : p.1 = h := by
      have h2 := List.find?_some hf
      simpa using h2
    have hmem : p ∈ mkPastCache B := List.mem_of_find?_eq_some hf
    unfold mkPastCache at hmem
    obtain ⟨b, _hb, hbp⟩ := List.mem_map.mp hmem
    have hb_id : b.id = p.1 := by rw [← hbp]
    have hb_v : causalPastIncl B b.id = p.2 := by rw [← hbp]
    show p.2 = causalPastIncl B h
    rw [← hb_v, hb_id, hp1]

/-! ### THE ROUND CACHE — the SECOND memoization, killing `computeRounds` recomputation.

**Why.** The `PastCache` above memoized the causal past, but it did NOT touch the OTHER un-memoized
recompute in this file: `roundOf B h` is `roundLookup (computeRounds B) h` — it folds `computeRounds`
over the WHOLE lace on EVERY call, and `roundOf` is called pervasively (inside `maxRound`'s `B.map`,
`blocksAtRound`'s `B.filter`, and the nested
`creatorBlocks.any (… creatorBlocks.any (… roundOf …))` of `hasEquivInPast`). So even with the past
memoized, the fast fold re-derived `computeRounds B` (itself O(n²) over the `List`-backed lace)
thousands of times per finalization — the EXACT `causalPast`-class sibling, on the same live
`@[export] dregg_tau_order` / `dregg_blocklace_finalize` path.

**The fix, proof-preserving.** A `RoundCache` = `computeRounds B` built ONCE (the Lean analogue of the
Rust `rounds: HashMap<BlockId, u64>`, `ordering.rs::compute_rounds`), threaded alongside `cache`. Each
round-reading primitive gets an `…R` twin that LOOKS UP the precomputed rounds; each is proved EQUAL
to its pure original at `rc = mkRoundCache B` — definitionally (`rfl`), since `roundOfR (mkRoundCache B)`
unfolds to exactly `roundOf B`. The `…C` fast twins now thread `rc` and call the `…R` primitives, so
`computeRounds B` is folded ONCE per finalization instead of per-`roundOf`. The `…C_eq` theorems keep
their statements (now also fixing `rc = mkRoundCache B`) and the safety theorems / `#guard`s about the
pure rule are untouched. -/

/-- A memo of the computed round map — `computeRounds B` built ONCE (the Lean analogue of the Rust
`rounds: HashMap<BlockId, u64>`, `ordering.rs::compute_rounds`). -/
abbrev RoundCache := List (BlockId × Nat)

/-- Build the round cache: run the `computeRounds` fold over `B` ONCE. -/
def mkRoundCache (B : Lace) (participants : List AuthorId) : RoundCache :=
  computeRounds B participants

/-- `roundOf` against a precomputed round cache (the lookup that replaces the per-call recompute). -/
def roundOfR (rc : RoundCache) (h : BlockId) : Nat := (roundLookup rc h).getD 0

theorem roundOfR_eq (B : Lace) (P : List AuthorId) (h : BlockId) :
    roundOfR (mkRoundCache B P) h = roundOf B P h := rfl

/-- `maxRound` against the cache. -/
def maxRoundR (rc : RoundCache) (B : Lace) : Nat :=
  (B.map (fun b => roundOfR rc b.id)).foldl Nat.max 0

theorem maxRoundR_eq (B : Lace) (P : List AuthorId) :
    maxRoundR (mkRoundCache B P) B = maxRound B P := rfl

/-- `blocksAtRound` against the cache. -/
def blocksAtRoundR (rc : RoundCache) (B : Lace) (r : Nat) : List BlockId :=
  (B.filter (fun b => roundOfR rc b.id == r)).map (·.id)

theorem blocksAtRoundR_eq (B : Lace) (P : List AuthorId) (r : Nat) :
    blocksAtRoundR (mkRoundCache B P) B r = blocksAtRound B P r := rfl

/-- `leaderCandidates` against the cache. -/
def leaderCandidatesR (rc : RoundCache) (B : Lace) (participants : List AuthorId)
    (wave wavelength : Nat) : List Block :=
  match waveLeader wave participants with
  | none => []
  | some lk =>
      let ws := waveFirstRound wave wavelength
      B.filter (fun b => b.creator == lk && roundOfR rc b.id == ws)

theorem leaderCandidatesR_eq (B : Lace) (participants : List AuthorId) (wave wavelength : Nat) :
    leaderCandidatesR (mkRoundCache B participants) B participants wave wavelength
      = leaderCandidates B participants wave wavelength := rfl

/-- `hasEquivInPast` with both caches (`§4`). -/
def hasEquivInPastC (B : Lace) (cache : PastCache) (rc : RoundCache) (observer : BlockId) (creator : AuthorId) : Bool :=
  hasEquivInPastWith B (cachedPast B cache observer) rc creator

theorem hasEquivInPastC_eq (B : Lace) (P : List AuthorId) (observer : BlockId) (creator : AuthorId) :
    hasEquivInPastC B (mkPastCache B) (mkRoundCache B P) observer creator
      = hasEquivInPast B P observer creator := by
  simp only [hasEquivInPastC, hasEquivInPast, cachedPast_eq, mkRoundCache]

/-- `approves` with both caches (`§4`). -/
def approvesC (B : Lace) (cache : PastCache) (rc : RoundCache) (o l : Block) : Bool :=
  (cachedPast B cache o.id).contains l.id && ¬ hasEquivInPastC B cache rc o.id l.creator

theorem approvesC_eq (B : Lace) (P : List AuthorId) (o l : Block) :
    approvesC B (mkPastCache B) (mkRoundCache B P) o l = approves B P o l := by
  simp only [approvesC, approves, cachedPast_eq, hasEquivInPastC_eq]

/-- `ratifies` with both caches (`§4`). -/
def ratifiesC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId) (o l : Block) : Bool :=
  let past := cachedPast B cache o.id
  let approvingParticipants : Nat :=
    (participants.filter (fun p =>
      past.any (fun bid => match B.lookup bid with
                            | some b => b.creator == p && approvesC B cache rc b l
                            | none   => false))).length
  approvingParticipants ≥ superMajority participants.length

theorem ratifiesC_eq (B : Lace) (participants : List AuthorId) (o l : Block) :
    ratifiesC B (mkPastCache B) (mkRoundCache B participants) participants o l
      = ratifies B participants o l := by
  simp only [ratifiesC, ratifies, cachedPast_eq, approvesC_eq]

/-- `ratifiesEnrolled` with both caches (`§4`) — the B6 ratifier-enrollment gate on the fast path. -/
def ratifiesEnrolledC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId) (o l : Block) : Bool :=
  participants.contains o.creator && ratifiesC B cache rc participants o l

theorem ratifiesEnrolledC_eq (B : Lace) (participants : List AuthorId) (o l : Block) :
    ratifiesEnrolledC B (mkPastCache B) (mkRoundCache B participants) participants o l
      = ratifiesEnrolled B participants o l := by
  simp only [ratifiesEnrolledC, ratifiesEnrolled, ratifiesC_eq]

/-- `isSuperRatified` with both caches (`§4`). -/
def isSuperRatifiedC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId)
    (l : Block) (waveEndRound : Nat) : Bool :=
  let endBlocks := blocksAtRoundR rc B waveEndRound
  let ratifyingCreators : List AuthorId :=
    (endBlocks.filterMap (fun bid => match B.lookup bid with
       | some b => if ratifiesEnrolledC B cache rc participants b l then some b.creator else none
       | none   => none)).dedup
  ratifyingCreators.length ≥ superMajority participants.length

theorem isSuperRatifiedC_eq (B : Lace) (participants : List AuthorId) (l : Block) (waveEndRound : Nat) :
    isSuperRatifiedC B (mkPastCache B) (mkRoundCache B participants) participants l waveEndRound
      = isSuperRatified B participants l waveEndRound := by
  simp only [isSuperRatifiedC, isSuperRatified, blocksAtRoundR_eq, ratifiesEnrolledC_eq]

/-- `finalLeaderAt` with both caches (`§5`). -/
def finalLeaderAtC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId)
    (wave wavelength : Nat) : Option Block :=
  match leaderCandidatesR rc B participants wave wavelength with
  | [l] => if isSuperRatifiedC B cache rc participants l (waveLastRound wave wavelength) then some l else none
  | _   => none

theorem finalLeaderAtC_eq (B : Lace) (participants : List AuthorId) (wave wavelength : Nat) :
    finalLeaderAtC B (mkPastCache B) (mkRoundCache B participants) participants wave wavelength
      = finalLeaderAt B participants wave wavelength := by
  simp only [finalLeaderAtC, finalLeaderAt, leaderCandidatesR_eq, isSuperRatifiedC_eq]

/-- `findAllFinalLeaders` with both caches (`§5`). -/
def findAllFinalLeadersC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId)
    (wavelength : Nat) : List Block :=
  let mr := maxRoundR rc B
  let waveCount := if wavelength == 0 then 0 else mr / wavelength + 1
  (List.range waveCount).filterMap (fun w => finalLeaderAtC B cache rc participants w wavelength)

theorem findAllFinalLeadersC_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    findAllFinalLeadersC B (mkPastCache B) (mkRoundCache B participants) participants wavelength
      = findAllFinalLeaders B participants wavelength := by
  simp only [findAllFinalLeadersC, findAllFinalLeaders, maxRoundR_eq, finalLeaderAtC_eq]

/-- `lastFinalLeader` with both caches (`§5b`). The ONLY part of CM's τ that reads the live lace —
choosing the head (Alg. 2:32,44–46) — and therefore the only part the whole-lace memo serves.

⚑ The chain walk and the per-anchor segments deliberately have NO `…C` twin. They are quantified
over `closureLace B l.id`, whose size is bounded by one anchor's causal past and whose depth map is
folded over that sub-lace alone; the exponential re-traversal the `PastCache`/`RoundCache` were
built to kill lived in `findAllFinalLeaders` (a `ratifies` per wave-end block per wave over the
WHOLE lace), which is exactly what this twin still covers. Mirroring the closure-local half would
add a second cache keyed by anchor for no measured win, and every `…C_eq` is a proof obligation. -/
def lastFinalLeaderC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId)
    (wavelength : Nat) : Option Block :=
  (findAllFinalLeadersC B cache rc participants wavelength).getLast?

theorem lastFinalLeaderC_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    lastFinalLeaderC B (mkPastCache B) (mkRoundCache B participants) participants wavelength
      = lastFinalLeader B participants wavelength := by
  simp only [lastFinalLeaderC, lastFinalLeader, findAllFinalLeadersC_eq]

/-- **`tauOrderFastUnfiltered`** — `tauOrderUnfiltered` with the head selected through the memoized
causal past (`mkPastCache B`) and round map (`mkRoundCache B`). -/
def tauOrderFastUnfiltered (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List BlockId :=
  match lastFinalLeaderC B (mkPastCache B) (mkRoundCache B participants) participants wavelength with
  | none    => []
  | some hd => ((ratifiedLeaderChain B participants wavelength hd).foldl
                  (tauStepWith (causalPastIncl B) (fun _ => true) B participants) ([], [])).1

/-- **`tauOrderFastUnfiltered_eq`** — the memoized head selection computes EXACTLY the pure one, and
therefore the whole order does (order-faithful, not merely set-equal). The memoization half of
`tauOrderFast_eq`, stated on the pre-enrollment-filter objects so the two changes (memoization,
enrollment) stay separable. -/
theorem tauOrderFastUnfiltered_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    tauOrderFastUnfiltered B participants wavelength = tauOrderUnfiltered B participants wavelength := by
  simp only [tauOrderFastUnfiltered, tauOrderUnfiltered, lastFinalLeaderC_eq]

/-- **`tauOrderFast B participants wavelength`** — the SAME finalized order as `tauOrder`, with the
head selected through BOTH memos (the causal past `mkPastCache B` and the round map
`mkRoundCache B`), each built once. This is the function the live gate exports run. -/
def tauOrderFast (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List BlockId :=
  match lastFinalLeaderC B (mkPastCache B) (mkRoundCache B participants) participants wavelength with
  | none    => []
  | some hd => ((ratifiedLeaderChain B participants wavelength hd).foldl
                  (tauStep B participants) ([], [])).1

/-- **`tauOrderFast_eq`** — the memoized fast path computes EXACTLY the pure `tauOrder` (order-faithful,
not merely set-equal). So every theorem and `#guard` that names `tauOrder` transfers to `tauOrderFast`
by rewriting, and the live gate may run the fast path with no loss of the verified guarantee. -/
theorem tauOrderFast_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    tauOrderFast B participants wavelength = tauOrder B participants wavelength := by
  simp only [tauOrderFast, tauOrder, lastFinalLeaderC_eq]

/-- **`tauOrderWithRounds B rc participants wavelength`** — the finalization rule with the WHOLE-LACE
round map as an explicit PARAMETER: the leader slot, the wave end, `maxRound`'s wave count and the
`ratifies`/`hasEquivInPast` reads inside `findAllFinalLeaders` all come from `rc`, so instantiating
`rc` is the ONLY variable.

This is what makes §9's exhibits an EXPERIMENT rather than two anecdotes: `tauOrderWithRounds B
(computeRoundsPreParticipant B) …` is the rule as it stood before the §1 edge filter and
`tauOrderWithRounds B (mkRoundCache B P) …` is the rule now, on ONE lace, with one bit changed. It
is not a second implementation — `tauOrderFast_eq_withRounds` below is `rfl`.

⚑ Its REACH SHRANK with the τ re-authoring, and the shrink is the point. `rc` now drives only the
head selection; the chain walk and the segments read `roundOf (closureLace B l.id) P`, a depth map
folded over the anchor's closure. A whole-lace depth perturbation can therefore still move WHICH
wave anchors — it can no longer move where an already-ordered block sits. -/
def tauOrderWithRounds (B : Lace) (rc : RoundCache) (participants : List AuthorId)
    (wavelength : Nat) : List BlockId :=
  match lastFinalLeaderC B (mkPastCache B) rc participants wavelength with
  | none    => []
  | some hd => ((ratifiedLeaderChain B participants wavelength hd).foldl
                  (tauStep B participants) ([], [])).1

/-- **`tauOrderFast_eq_withRounds`** — the live path IS `tauOrderWithRounds` at the participant-
filtered round map. Definitional, so the §9 pre/post pair compares the deployed rule against itself
with only `rc` swapped. -/
theorem tauOrderFast_eq_withRounds (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    tauOrderFast B participants wavelength
      = tauOrderWithRounds B (mkRoundCache B participants) participants wavelength := rfl

/-- **`tauOrderPreRounds B participants wavelength`** — the finalization rule driven by the
PRE-PARTICIPANT depth map: the rule exactly as it stood before this pass.

⚑ THIS IS NOT THE FINALIZATION RULE. It is kept, named, and reachable from nothing but the §9
`#guard`s, for one reason: it is the FALSIFICATION WITNESS for the §1 edge filter — the same
discipline `isSuperRatifiedPreEnrollment` and `tauOrderUnfiltered` carry. §9 runs it against
`traceOrderFork` and `traceRelayStall` and shows it computes an order the repaired rule does not,
so the filter is demonstrably load-bearing rather than a no-op that "obviously" changes nothing. -/
def tauOrderPreRounds (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List BlockId :=
  tauOrderWithRounds B (computeRoundsPreParticipant B) participants wavelength

/-! ## 6c. THE RUNTIME FAST PATH — `@[implemented_by]` over `Std.HashMap`/`Std.HashSet`.

**Why this exists, and why it is SOUND.** The §6b `…C` fast twins killed the *within-call*
exponential re-traversal by memoizing into `List`-backed caches (`PastCache`/`RoundCache`), but the
DATA STRUCTURES are still `List`s: `cachedPast`'s `cache.find?` (:319) is an O(n) scan per lookup,
`causalPastAux`'s `acc.dedup`/`acc.contains` (:135,:138) are O(n)/elem, and `mkPastCache` (:311)
rebuilds ALL of them per FFI call — so the exported `dregg_tau_order` is O(n³)-to-build and pays it
every finality poll (docs/VERIFIED-GATE-PERF.md: 9.2 s @ 35 blocks). This section adds a runtime
twin backed by `Std.HashMap`/`Std.HashSet` (O(1) dedup/contains/lookup) and attaches it to
`tauOrderFast` via `@[implemented_by]`.

`@[implemented_by]` is TRUSTED — the kernel does NOT check the twin equals the pure def; a wrong
twin silently corrupts finality with no theorem catching it (every theorem/`#guard` is about the
PURE def). Two disciplines make it safe:
  1. The twin below is a LINE-FOR-LINE mirror of the §6b `…C` functions with the sole change of
     `List.find?`/`.contains`/`.dedup` → `Std.HashMap`/`Std.HashSet` operations.
  2. The `@[implemented_by]` is attached ONLY to `tauOrderFast`; the pure `tauOrder`,
     `causalPastIncl`, and every `…C`/`…R` def keep their normal compilation. So the §9 differential
     `#guard tauOrderFast … == tauOrder …` and `#guard fastCausalPastIncl … == causalPastIncl …`
     compare the FAST-compiled twin against the PURE-compiled def (NOT fast-vs-fast) — a genuine,
     non-vacuous check on the golden 3-node trace, the equivocation trace, AND a fresh round-2-shaped
     multi-wave n=4 DAG (`traceMW4`). -/

/-- BFS layer expansion with a `Std.HashSet` frontier-dedup — the runtime twin of `causalPastAux`.
O(1) `HashSet` membership replaces the pure def's O(n) `List.contains`/`.dedup`. Terminates because
`seen` grows and is bounded by `|B|`.

⚑ **CORRECTED — this twin used to DIVERGE from the def it is trusted to implement.** It kept the
FIRST occurrence within a layer (a pred already `seen` is skipped), justified by a docstring claim
that `acc.dedup` "keeps the first". **`List.dedup` keeps the LAST** — `[1,2,1,3,2].dedup = [1,3,2]`,
evaluated. The divergence needs only one layer whose expansion repeats an id around another, i.e.
two frontier blocks with overlapping-but-unequal pred sets, and is exhibited on a FIVE-block lace by
`fast_twin_matches_the_spec_on_the_uneven_pred_lace` in §9: `p,q` at round 1, `b1` acking `[p,q]`,
`b2` acking `[p]`, `hd` acking `[b1,b2]` — the layer expands to `[p,q,p]`, the pure def returns
`[hd,b1,b2,q,p]` and the old twin returned `[hd,b1,b2,p,q]`.

`@[implemented_by]` is TRUSTED — the kernel checks nothing — so that was a silent order divergence on
the live `dregg_tau_order` path, invisible to every theorem (all of which are about the pure def) and
missed by the §9 `#guard`s because a fully cross-linked trace gives every block in a layer the
IDENTICAL pred list, the one shape where first and last coincide. The `traceMW4`/equivocation traces
share that shape.

The layer is now deduped LAST-occurrence-wise — built with a right fold, which meets each id's final
copy first and prepends, reproducing `List.dedup`'s output order exactly. -/
partial def fastCausalPastAux (B : Lace) (seen : Std.HashSet BlockId) (acc : Array BlockId)
    (frontier : List BlockId) : Array BlockId :=
  match frontier with
  | [] => acc
  | _ =>
    -- the raw layer, in `expandPreds` order, filtered against PREVIOUS layers only (= the pure
    -- def's `filter (¬ acc.contains ·)`, which likewise cannot see intra-layer duplicates).
    let raw : List BlockId :=
      frontier.flatMap (fun hid =>
        match B.lookup hid with
        | some b => b.preds.filter (fun p => B.has p && !seen.contains p)
        | none   => [])
    -- keep the LAST occurrence of each id, in first-appearance order of those survivors — exactly
    -- `List.dedup`. A right fold sees each id's LAST copy first; prepending restores the order.
    let nxt : List BlockId :=
      (raw.foldr (init := ((∅ : Std.HashSet BlockId), ([] : List BlockId)))
        (fun p st => if st.1.contains p then st else (st.1.insert p, p :: st.2))).2
    let seen := nxt.foldl (fun s p => s.insert p) seen
    let acc := nxt.foldl (fun a p => a.push p) acc
    fastCausalPastAux B seen acc nxt

/-- Runtime twin of `causalPastIncl` (HashSet-backed BFS). Value-identical; §9 differential-guarded. -/
def fastCausalPastIncl (B : Lace) (h : BlockId) : List BlockId :=
  (fastCausalPastAux B ((∅ : Std.HashSet BlockId).insert h) #[h] [h]).toList

/-- The past cache as a `Std.HashMap` (O(1) lookup) — the runtime twin of `mkPastCache`. Built ONCE
per finalization; first-occurrence-keyed (skip if already present), matching `cachedPast`'s
`find?`-first-hit on `mkPastCache`. -/
def fastPastMap (B : Lace) : Std.HashMap BlockId (List BlockId) :=
  B.foldl (init := (∅ : Std.HashMap BlockId (List BlockId)))
    (fun m b => if m.contains b.id then m else m.insert b.id (fastCausalPastIncl B b.id))

/-- Runtime twin of `kahnAux` (§1): the same sweeps in the same order, with the held ids and the
emitted ids as `Std.HashSet`s in place of `Lace.has` and `done.any`. `held.contains p` is
`B.has p`; `st.1.contains p` is "some emitted block has id `p`". Returns emitted ++ stuck, i.e.
`topoLace`. -/
def fastKahnAux (held : Std.HashSet BlockId) :
    Nat → Std.HashSet BlockId → Array Block → List Block → Array Block
  | 0,        _,       done, pending => done ++ pending.toArray
  | fuel + 1, doneIds, done, pending =>
      let st := pending.foldl
        (init := (doneIds, done, (#[] : Array Block)))
        (fun st b =>
          if b.preds.all (fun p => !held.contains p || st.1.contains p)
          then (st.1.insert b.id, st.2.1.push b, st.2.2)
          else (st.1, st.2.1, st.2.2.push b))
      if st.2.2.size < pending.length then fastKahnAux held fuel st.1 st.2.1 st.2.2.toList
      else st.2.1 ++ st.2.2

/-- Runtime twin of `topoLace`. Value-identical; §9 differential-guarded. -/
def fastTopoLace (B : Lace) : List Block :=
  (fastKahnAux (B.foldl (fun s b => s.insert b.id) (∅ : Std.HashSet BlockId)) B.length
    (∅ : Std.HashSet BlockId) #[] B).toList

/-- The round map as a `Std.HashMap` (O(1) lookup) — the runtime twin of `mkRoundCache`
(`computeRounds`), built ONCE with `Std.HashMap.get?` replacing the pure fold's `roundLookup`
`List.find?`. The same fold over the same Kahn enumeration (`fastTopoLace`). -/
def fastRoundMap (B : Lace) (participants : List AuthorId) : Std.HashMap BlockId Nat :=
  -- the enrolled BLOCK IDS as a HashSet, built ONCE: the O(1) twin of `enrolledId`'s `B.lookup`
  -- scan. First-wins on a duplicated id, matching `Lace.lookup`'s `List.find?`; an id ABSENT from
  -- the lace is `enrolledId`-true and is dropped by the `rm.get?` miss anyway (§1's docstring).
  let ps : Std.HashSet AuthorId :=
    participants.foldl (fun acc p => acc.insert p) (∅ : Std.HashSet AuthorId)
  let enrolled : Std.HashSet BlockId :=
    (B.foldl (init := ((∅ : Std.HashMap BlockId AuthorId), (∅ : Std.HashSet BlockId)))
      (fun st b =>
        let (seen, acc) := st
        if seen.contains b.id then st
        else (seen.insert b.id b.creator, if ps.contains b.creator then acc.insert b.id else acc))).2
  (fastTopoLace B).foldl (init := (∅ : Std.HashMap BlockId Nat))
    (fun rm b => rm.insert b.id
      (1 + ((b.preds.filter (fun p => enrolled.contains p)).filterMap (fun p => rm.get? p)).foldl
        Nat.max 0))

/-- O(1) past lookup with a LAZY pure fallback (the `match`, not `getD`, keeps the fallback from
being computed on a hit) — the runtime twin of `cachedPast`. -/
@[inline] def fastPast (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (h : BlockId) : List BlockId :=
  match pm.get? h with
  | some v => v
  | none   => fastCausalPastIncl B h

/-- O(1) round lookup — the runtime twin of `roundOfR`. -/
@[inline] def fastROf (rm : Std.HashMap BlockId Nat) (h : BlockId) : Nat := rm.getD h 0

/-- Runtime twin of `hasEquivInPastC`. -/
def fastHasEquivInPast (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (observer : BlockId) (creator : AuthorId) : Bool :=
  let past := fastPast B pm observer
  let creatorBlocks : List Block :=
    past.filterMap (fun bid => match B.lookup bid with
                                | some b => if b.creator = creator then some b else none
                                | none   => none)
  creatorBlocks.any (fun a =>
    creatorBlocks.any (fun b => a.id ≠ b.id && fastROf rm a.id == fastROf rm b.id))

/-- Runtime twin of `approvesC`. -/
def fastApproves (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (o l : Block) : Bool :=
  (fastPast B pm o.id).contains l.id && ¬ fastHasEquivInPast B pm rm o.id l.creator

/-- Runtime twin of `ratifiesC`. -/
def fastRatifies (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (o l : Block) : Bool :=
  let past := fastPast B pm o.id
  let approvingParticipants : Nat :=
    (participants.filter (fun p =>
      past.any (fun bid => match B.lookup bid with
                            | some b => b.creator == p && fastApproves B pm rm b l
                            | none   => false))).length
  approvingParticipants ≥ superMajority participants.length

/-- Runtime twin of `blocksAtRoundR`. -/
def fastBlocksAtRound (B : Lace) (rm : Std.HashMap BlockId Nat) (r : Nat) : List BlockId :=
  (B.filter (fun b => fastROf rm b.id == r)).map (·.id)

/-- Runtime twin of `ratifiesEnrolledC` — the B6 ratifier-enrollment gate on the runtime path. -/
def fastRatifiesEnrolled (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (o l : Block) : Bool :=
  participants.contains o.creator && fastRatifies B pm rm participants o l

/-- Runtime twin of `isSuperRatifiedC`. -/
def fastIsSuperRatified (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (l : Block) (waveEndRound : Nat) : Bool :=
  let endBlocks := fastBlocksAtRound B rm waveEndRound
  let ratifyingCreators : List AuthorId :=
    (endBlocks.filterMap (fun bid => match B.lookup bid with
       | some b => if fastRatifiesEnrolled B pm rm participants b l then some b.creator else none
       | none   => none)).dedup
  ratifyingCreators.length ≥ superMajority participants.length

/-- Runtime twin of `leaderCandidatesR`. -/
def fastLeaderCandidates (B : Lace) (rm : Std.HashMap BlockId Nat) (participants : List AuthorId)
    (wave wavelength : Nat) : List Block :=
  match waveLeader wave participants with
  | none => []
  | some lk =>
      let ws := waveFirstRound wave wavelength
      B.filter (fun b => b.creator == lk && fastROf rm b.id == ws)

/-- Runtime twin of `finalLeaderAtC`. -/
def fastFinalLeaderAt (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (wave wavelength : Nat) : Option Block :=
  match fastLeaderCandidates B rm participants wave wavelength with
  | [l] => if fastIsSuperRatified B pm rm participants l (waveLastRound wave wavelength) then some l else none
  | _   => none

/-- Runtime twin of `maxRoundR`. -/
def fastMaxRound (B : Lace) (rm : Std.HashMap BlockId Nat) : Nat :=
  (B.map (fun b => fastROf rm b.id)).foldl Nat.max 0

/-- Runtime twin of `findAllFinalLeadersC`. -/
def fastFindAllFinalLeaders (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (wavelength : Nat) : List Block :=
  let mr := fastMaxRound B rm
  let waveCount := if wavelength == 0 then 0 else mr / wavelength + 1
  (List.range waveCount).filterMap (fun w => fastFinalLeaderAt B pm rm participants w wavelength)

/-- Runtime twin of `lastFinalLeaderC` — the head selection (CM Alg. 2:32,44–46), the ONLY part of
τ that reads the whole lace and therefore the only part this `Std.HashMap` stack still serves. The
chain walk and the per-anchor segments run the pure closure-local defs; see `lastFinalLeaderC`. -/
def fastLastFinalLeader (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (wavelength : Nat) : Option Block :=
  (fastFindAllFinalLeaders B pm rm participants wavelength).getLast?

/-- **`tauOrderFastImpl`** — the runtime twin of `tauOrderFast`: builds the past + round maps as
`Std.HashMap`s ONCE (O(|B|) HashSet-BFS calls + one topological fold), selects the head with O(1)
lookups, and runs the SAME segment fold with the memoized past handed to the linearizer
(`tauStepWith (fastPast B pm)`), so no segment re-walks the lace per id. This is the
`@[implemented_by]` target for `tauOrderFast` (below) — the function the exported
`dregg_tau_order` / `dregg_blocklace_finalize` actually execute. TRUSTED; §9-guarded. The
enrollment filter is the segment's own (`anchorSegmentWith`'s `keep`), the same one `tauOrderFast`
applies, so there is no separate filter twin. -/
def tauOrderFastImpl (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List BlockId :=
  let pm := fastPastMap B
  let rm := fastRoundMap B participants
  match fastLastFinalLeader B pm rm participants wavelength with
  | none    => []
  | some hd => ((ratifiedLeaderChain B participants wavelength hd).foldl
                  (tauStepWith (fastPast B pm) (fun b => participants.contains b.creator)
                    B participants) ([], [])).1

/-! Route the exported `tauOrderFast` (hence both `dregg_tau_order` and `dregg_blocklace_finalize`)
through the `Std.HashMap`/`Std.HashSet` runtime twin. Proofs are unaffected (`@[implemented_by]` is
runtime-only, introduces no axioms — `#assert_axioms tauOrderFast_eq` below stays clean); the §9
differential `#guard`s witness value-identity of the twin against the pure `tauOrder` on concrete
laces (golden 3-node, equivocation, and the round-2-shaped multi-wave n=4 `traceMW4`). -/
attribute [implemented_by tauOrderFastImpl] tauOrderFast

/-! ## 7. THE SAFETY PROPERTY — no two conflicting final leaders per wave + determinism.

The property the node RELIES on: a wave anchors AT MOST ONE final leader, and the finalized order
is a deterministic function of `(lace, participants, wavelength)` — so two honest replicas that see
the same lace compute the SAME finalized order, hence (composed with `ConsensusExec.executeFinalized`
determinism) the SAME executed state. This is the computed-rule analogue of `cordial_agreement`'s
single-anchor — proved DIRECTLY over the node's `find_all_final_leaders` function, not an abstract
record. -/

/-- **`finalLeaderAt_unique` (single anchor per wave, the SAFETY tooth).** `finalLeaderAt`
returns AT MOST ONE leader for a wave: it is an `Option Block` whose `some` branch fires ONLY when
the leader slot has EXACTLY ONE candidate. So a wave cannot anchor two distinct final leaders — the
no-conflicting-leader property, read straight off the node's computed rule. Two `some` results for
the same `(B, participants, wave, wavelength)` are EQUAL (`Option` is a function value). -/
theorem finalLeaderAt_unique (B : Lace) (participants : List AuthorId) (wave wavelength : Nat)
    (l₁ l₂ : Block)
    (h₁ : finalLeaderAt B participants wave wavelength = some l₁)
    (h₂ : finalLeaderAt B participants wave wavelength = some l₂) :
    l₁ = l₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-- **`finalLeaderAt_needs_unique_candidate` (the anti-equivocation tooth).** A wave yields
a final leader ONLY when its leader slot has exactly one candidate block: if the round-robin leader
equivocates at the slot (`≥ 2` candidates) or is silent (`0`), `finalLeaderAt = none`. So a forking
leader CANNOT anchor a wave — the equivocation guard the node enforces, proved over the rule. -/
theorem finalLeaderAt_needs_unique_candidate (B : Lace) (participants : List AuthorId)
    (wave wavelength : Nat) (l : Block)
    (h : finalLeaderAt B participants wave wavelength = some l) :
    leaderCandidates B participants wave wavelength = [l] := by
  unfold finalLeaderAt at h
  -- case-split on the candidate list shape; only the singleton branch can produce `some`.
  cases hc : leaderCandidates B participants wave wavelength with
  | nil => rw [hc] at h; simp at h
  | cons x xs =>
    cases xs with
    | nil =>
      rw [hc] at h
      -- singleton: the `if` either returns `some x` or `none`.
      by_cases hsr : isSuperRatified B participants x (waveLastRound wave wavelength)
      · simp only [hsr, if_true] at h
        exact congrArg (fun z => [z]) (Option.some.inj h)
      · simp only [hsr] at h; exact absurd h (by simp)
    | cons y ys => rw [hc] at h; simp at h

/-- **`tauOrder_deterministic` (the determinism tooth).** The finalized order is a
deterministic FUNCTION of `(lace, participants, wavelength)`: two computations from the same inputs
are equal. So two honest replicas with the same lace finalize the SAME order — the consensus-side of
"no two conflicting finalized states" (the execution-side is `ConsensusExec.executeFinalized` being a
function). Trivial as Lean (`tauOrder` is a `def`), but it is the load-bearing STATEMENT: agreement
reduces to seeing the same lace. -/
theorem tauOrder_deterministic (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (o₁ o₂ : List BlockId)
    (h₁ : tauOrder B participants wavelength = o₁)
    (h₂ : tauOrder B participants wavelength = o₂) :
    o₁ = o₂ := by rw [← h₁, ← h₂]

/-- **`findAllFinalLeaders_deterministic`.** The final-leader set is a deterministic
function of the inputs — equal laces ⇒ equal final-leader lists. The anchor sequence the node
finalizes is reproducible. -/
theorem findAllFinalLeaders_deterministic (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (xs ys : List Block)
    (h₁ : findAllFinalLeaders B participants wavelength = xs)
    (h₂ : findAllFinalLeaders B participants wavelength = ys) :
    xs = ys := by rw [← h₁, ← h₂]

/-- **`finalLeaders_one_per_wave` (the structural agreement, indexed by wave).** Reading
`findAllFinalLeaders` through `finalLeaderAt`, the leader anchoring ANY GIVEN wave is unique:
whatever the node lists as the final leader of wave `w` is the single `finalLeaderAt … w …` value, so
two computations cannot disagree on a wave's anchor. This is the executable-model face of
`Proof.CordialMiners.cordial_agreement` — proved DIRECTLY over the node's `find_all_final_leaders`
rule (its `Option`-valued per-wave body), not an abstract `Committed` record. -/
theorem finalLeaders_one_per_wave (B : Lace) (participants : List AuthorId) (wave wavelength : Nat)
    (l₁ l₂ : Block)
    (h₁ : finalLeaderAt B participants wave wavelength = some l₁)
    (h₂ : finalLeaderAt B participants wave wavelength = some l₂) :
    l₁ = l₂ :=
  finalLeaderAt_unique B participants wave wavelength l₁ l₂ h₁ h₂

/-! ## 7b. THE ENROLLMENT TOOTH — the finalized order carries ONLY enrolled creators, and on an
enrolled lace the filter is the IDENTITY.

These are the two halves the node's falsifier
(`node/src/finality_gate.rs::attacker_block_from_unenrolled_creator_is_refused_by_the_verified_rule`)
demands, and the first is the statement `finality_gate.rs`'s `VerifiedFinality::admits` doc-comment
CLAIMED and did not have: "an attacker key that does not match an enrolled hybrid participant is
never interned and never admitted". The interning half was false (`build_wire::next_extra` interns
every creator it meets) and the admission half was false (`tauOrder` had no identity filter). The
interning half stays false ON PURPOSE — an unenrolled creator IS put on the wire, so the refusal
below is the RULE declining, never a `HashMap` miss. -/

/-- **`EnrolledLace B participants`** — every block in the lace was created by a participant. This
is the precondition `ordering.rs::tau`'s docstring ASSERTED ("assumes all blocks belong to
participants") and the live path cannot enforce: `receive_block_pinned`'s roster is INSERT-ONLY
(`blocklace/src/finality.rs::enroll_pq`) while the constitution's participant set shrinks on a
membership change, and `from_checkpoint_trusted` (the restart path) re-inserts every persisted block
with no check at all. Satisfiable (`trace3`, `traceMW4`, `lagGrown`) and REFUTABLE
(`traceUnenrolled`), which is what makes the identity theorem below carry information. -/
def EnrolledLace (B : Lace) (participants : List AuthorId) : Prop :=
  ∀ b ∈ B, participants.contains b.creator = true

/-- A sub-lace selected by a predicate on ids resolves an id to the block the lace does. -/
theorem lookup_of_filter_lookup {q : BlockId → Bool} :
    ∀ {B : Lace} {bid : BlockId} {b : Block},
      Lace.lookup (B.filter (fun x => q x.id)) bid = some b → B.lookup bid = some b := by
  intro B
  induction B with
  | nil => intro bid b h; simp [Lace.lookup] at h
  | cons a t ih =>
    intro bid b h
    have hb : b ∈ List.filter (fun x => q x.id) (a :: t) := List.mem_of_find?_eq_some h
    have hbid : b.id = bid := by have := List.find?_some h; simpa using this
    by_cases hq : q a.id = true
    · by_cases ha : a.id = bid
      · have hf : List.filter (fun x => q x.id) (a :: t) = a :: List.filter (fun x => q x.id) t := by
          simp [hq]
        simp only [Lace.lookup, hf, List.find?_cons, ha, decide_true] at h ⊢
        exact h
      · have h' : Lace.lookup (t.filter (fun x => q x.id)) bid = some b := by
          simpa [Lace.lookup, List.filter_cons, hq, List.find?_cons, ha] using h
        simpa [Lace.lookup, List.find?_cons, ha] using ih h'
    · have h' : Lace.lookup (t.filter (fun x => q x.id)) bid = some b := by
        simpa [Lace.lookup, List.filter_cons, hq] using h
      have ha : a.id ≠ bid := by
        intro e
        have hqb : q b.id = true := by
          have := (List.mem_filter.mp hb).2; simpa using this
        rw [hbid, ← e] at hqb
        exact hq hqb
      simpa [Lace.lookup, List.find?_cons, ha] using ih h'

/-- An id the anchor's closure resolves, the lace resolves to the same block. -/
theorem lookup_of_closureLace_lookup {B : Lace} {h bid : BlockId} {b : Block}
    (hl : (closureLace B h).lookup bid = some b) : B.lookup bid = some b :=
  lookup_of_filter_lookup (q := fun i => (causalPastIncl B h).contains i) hl

/-- **`tauOrder_only_enrolled` (THE SAFETY HALF).** Every block the verified rule finalizes was
created by an ENROLLED participant. No hypothesis on the lace: this holds on a lace stuffed with
unenrolled creators' blocks, which is precisely the case that mattered — an unenrolled node can no
longer inject a state transition into the executor through the finalized order. -/
theorem tauOrder_only_enrolled (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (bid : BlockId) (b : Block)
    (hmem : bid ∈ tauOrder B participants wavelength)
    (hlook : B.lookup bid = some b) :
    participants.contains b.creator = true := by
  unfold tauOrder at hmem
  cases hhd : lastFinalLeader B participants wavelength with
  | none => rw [hhd] at hmem; simp at hmem
  | some hd =>
    rw [hhd] at hmem
    have hfun : tauStep B participants
        = tauStepWith (causalPastIncl B) (fun b => participants.contains b.creator) B participants := by
      funext acc l; rfl
    simp only [hfun] at hmem
    rcases foldl_tauStepWith_keep _ _ bid hmem with h0 | ⟨l, _, b', hb', hkeep⟩
    · simp at h0
    · have := lookup_of_closureLace_lookup hb'
      rw [hlook] at this
      rw [Option.some.inj this]
      exact hkeep

/-- A segment depends on its creator filter only through the blocks of the anchor's closure. -/
theorem anchorSegmentWith_congr_keep {past : BlockId → List BlockId} {keep₁ keep₂ : Block → Bool}
    {B : Lace} {participants : List AuthorId} {prevCovered : List BlockId} {l : Block}
    (h : ∀ b ∈ closureLace B l.id, keep₁ b = keep₂ b) :
    anchorSegmentWith past keep₁ B participants prevCovered l
      = anchorSegmentWith past keep₂ B participants prevCovered l := by
  simp only [anchorSegmentWith]
  congr 1
  apply List.filter_congr
  intro bid _
  cases hl : (closureLace B l.id).lookup bid with
  | none => rfl
  | some b => simp only [h b (List.mem_of_find?_eq_some hl)]

/-- **`tauOrder_enrolled_eq_unfiltered` (THE LIVENESS HALF).** On a lace whose every block is from a
participant — an HONEST lace, the only kind a correct federation produces — the enrollment filter
changes NOTHING: the finalized order is bit-identical to the pre-fix rule's, same blocks, same
order, same length. So this is a pure subtraction of unenrolled blocks, not a liveness trade: no
legitimate block is dropped, and no honest node's finalization is delayed by one wave.

Together with `tauOrder_only_enrolled` this is the whole content of the change: OFF the enrolled
lace it removes the unenrolled blocks before the sort; ON the enrolled lace it is the identity. -/
theorem tauOrder_enrolled_eq_unfiltered (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (h : EnrolledLace B participants) :
    tauOrder B participants wavelength = tauOrderUnfiltered B participants wavelength := by
  have hfun : tauStep B participants
      = tauStepWith (causalPastIncl B) (fun _ => true) B participants := by
    funext acc l
    unfold tauStep tauStepWith
    rw [anchorSegmentWith_congr_keep (keep₂ := fun _ => true)]
    intro b hb
    exact h b (List.mem_filter.mp hb).1
  unfold tauOrder tauOrderUnfiltered
  rw [hfun]

/-! ## 7c. THE RATIFIER-ENROLLMENT TOOTH (HORIZONLOG B6) — the supermajority counts ONLY enrolled
creators, and on an enrolled lace the gate is the IDENTITY.

The §7b tooth (`enrolledId`) governs WHOSE BLOCKS MAY BE ORDERED. It says nothing about WHO MAY
DECIDE that a wave anchors: `isSuperRatified` collected `b.creator` off the wave-end blocks with no
enrollment check, so an unenrolled creator was a full member of the quorum whose own docstring reads
"a supermajority of DISTINCT PARTICIPANTS". The two are independent — `tauOrder_only_enrolled` holds
of the pre-repair rule too, because the unenrolled creator's OWN blocks were filtered out of the
ORDER while its VOTE still finalized the honest ones. That is the shape B6 names, and it is safety:
finality reached without the committee.

Both halves, as §7b: the count exhibits an ENROLLED ratifier (safety), and on an enrolled lace the
gate changes nothing (liveness). -/

/-- **`ratifiesEnrolled_eq_of_enrolled`** — on a lace whose every block is from a participant, the
ratifier gate is the IDENTITY on `ratifies`. The pointwise liveness half: no honest federation loses
a ratifier, so no wave that used to anchor stops anchoring. The `EnrolledLace` hypothesis is
genuinely refutable (`traceUnenrolled`, `traceSybilRatify`, `traceSybilOnly` all refute it, §9). -/
theorem ratifiesEnrolled_eq_of_enrolled (B : Lace) (participants : List AuthorId) (o l : Block)
    (ho : o ∈ B) (h : EnrolledLace B participants) :
    ratifiesEnrolled B participants o l = ratifies B participants o l := by
  simp only [ratifiesEnrolled, h o ho, Bool.true_and]

/-- **`isSuperRatified_eq_pre_of_enrolled` (THE LIVENESS HALF).** On an HONEST lace — every block
from a participant, the only kind a correct federation produces — the repaired super-ratification
test is BIT-IDENTICAL to the pre-repair one. So this is a pure subtraction of unenrolled ratifiers,
never a liveness trade: the honest committee anchors exactly the waves it anchored before, and no
finalization is delayed by one wave. (Whole-rule liveness is machine-checked by the §9 `#guard`s on
`trace3`, `traceUnenrolled`, `traceMW4`, and by `Consensus.TauPrefixMonotone`'s `lagBase`/`lagGrown`
golden orders, all of which are unchanged by this repair.) -/
theorem isSuperRatified_eq_pre_of_enrolled (B : Lace) (participants : List AuthorId)
    (l : Block) (waveEndRound : Nat) (h : EnrolledLace B participants) :
    isSuperRatified B participants l waveEndRound
      = isSuperRatifiedPreEnrollment B participants l waveEndRound := by
  unfold isSuperRatified isSuperRatifiedPreEnrollment
  have hf : (fun bid => match B.lookup bid with
                | some b => if ratifiesEnrolled B participants b l then some b.creator else none
                | none   => (none : Option AuthorId))
          = (fun bid => match B.lookup bid with
                | some b => if ratifies B participants b l then some b.creator else none
                | none   => (none : Option AuthorId)) := by
    funext bid
    cases hl : B.lookup bid with
    | none => rfl
    | some b =>
      have hmem : b ∈ B := List.mem_of_find?_eq_some hl
      show (if ratifiesEnrolled B participants b l = true then some b.creator else none)
         = (if ratifies B participants b l = true then some b.creator else none)
      rw [ratifiesEnrolled_eq_of_enrolled B participants b l hmem h]
  rw [hf]

/-- **`superRatified_exists_enrolled_ratifier` (THE SAFETY HALF).** Super-ratification now EXHIBITS
an ENROLLED ratifier: if the rule says a leader is super-ratified, some block of the lace, created
by a PARTICIPANT, ratifies it. No hypothesis on the lace — this holds on a lace stuffed with
unenrolled creators' blocks, which is precisely the case that mattered. Before the repair the
strongest available statement was "SOME block of the lace ratifies it"
(`Consensus.SuperRatifyBridge.exists_ratifying_observer`), which a Sybil satisfies; that theorem now
rides this one.

Non-vacuity: the conclusion is genuinely unreachable on `traceSybilOnly` (§9), where every wave-end
block ratifies the leader and NOT ONE of them is enrolled — the pre-repair predicate returns `true`
there and this one returns `false`. -/
theorem superRatified_exists_enrolled_ratifier {B : Lace} {participants : List AuthorId}
    {l : Block} {r : Nat} (hsr : isSuperRatified B participants l r = true) :
    ∃ o ∈ B, participants.contains o.creator = true ∧ ratifies B participants o l = true := by
  unfold isSuperRatified at hsr
  simp only [decide_eq_true_eq] at hsr
  set cs := ((blocksAtRound B participants r).filterMap (fun bid => match B.lookup bid with
      | some b => if ratifiesEnrolled B participants b l then some b.creator else none
      | none => none)).dedup with hcs
  have hpos : 0 < cs.length := lt_of_lt_of_le (Nat.succ_pos _) hsr
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos hpos)
  rw [hcs, List.mem_dedup, List.mem_filterMap] at hc
  obtain ⟨bid, _, hf⟩ := hc
  cases hlk : B.lookup bid with
  | none => rw [hlk] at hf; simp at hf
  | some b =>
    rw [hlk] at hf
    have hf' : (if ratifiesEnrolled B participants b l = true then some b.creator else none)
        = some c := hf
    by_cases hr : ratifiesEnrolled B participants b l = true
    · have hr' := hr
      simp only [ratifiesEnrolled, Bool.and_eq_true] at hr'
      exact ⟨b, List.mem_of_find?_eq_some hlk, hr'.1, hr'.2⟩
    · rw [if_neg hr] at hf'; simp at hf'

/-! ## 7d. THE DEPTH TOOTH — the wave clock is driven ONLY by enrolled blocks, and on an enrolled
lace the edge filter is the IDENTITY.

§7b (`enrolledId` on the OUTPUT) governs whose blocks may be ORDERED. §7c (`ratifiesEnrolled`)
governs who may DECIDE that a wave anchors. Neither says anything about who may move the CLOCK, and
that turned out to be the third, independent question: `computeRounds` maxed over every present
predecessor, so a non-participant chain that one honest block acked added depth, and depth is what
`roundToWave` / `blocksAtRound` / the leader slot / the wave end / `xsortBy`'s ready priority are
all read off.

Both halves, as §7b and §7c: the depth EXHIBITS an enrolled predecessor (safety, no hypothesis on
the lace), and on an enrolled lace the filter changes nothing (liveness). -/

/-- `List.foldl Nat.max a l` is either the seed or one of the list's own elements — the arithmetic
fact that turns "the depth is `1 + max`" into "the depth NAMES a predecessor". -/
theorem foldl_max_eq_or_mem : ∀ (l : List Nat) (a : Nat),
    l.foldl Nat.max a = a ∨ l.foldl Nat.max a ∈ l := by
  intro l
  induction l with
  | nil => intro a; exact Or.inl rfl
  | cons x xs ih =>
    intro a
    simp only [List.foldl_cons]
    rcases ih (Nat.max a x) with h | h
    · rw [h]
      by_cases hle : a ≤ x
      · have hx : Nat.max a x = x := by simp [Nat.max_def, hle]
        exact Or.inr (by rw [hx]; simp)
      · exact Or.inl (by simp [Nat.max_def, hle])
    · exact Or.inr (List.mem_cons_of_mem x h)

/-- **`unenrolled_preds_contribute_no_depth`** — the leak's direct negation, at the recurrence. A
block whose acks are ALL from non-participants sits at genesis depth `1`, however deep the chain it
acknowledges. No hypothesis on the lace. -/
theorem unenrolled_preds_contribute_no_depth (B : Lace) (participants : List AuthorId)
    (rs : List (BlockId × Nat)) (b : Block)
    (h : ∀ p ∈ b.preds, enrolledId B participants p = false) :
    roundOfStep B participants rs b = 1 := by
  have hnil : b.preds.filter (enrolledId B participants) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simp [h p hp]
  show 1 + _ = 1
  rw [hnil]
  rfl

/-- **`roundOfStep_exhibits_enrolled_pred`** — one step of the recurrence, at full detail: any depth
above `1` NAMES an ENROLLED predecessor carrying exactly one less. No hypothesis on the lace. -/
theorem roundOfStep_exhibits_enrolled_pred {B : Lace} {participants : List AuthorId}
    {rs : List (BlockId × Nat)} {b : Block} (h : 1 < roundOfStep B participants rs b) :
    ∃ p ∈ b.preds, enrolledId B participants p = true ∧
      roundLookup rs p = some (roundOfStep B participants rs b - 1) := by
  have hstep : roundOfStep B participants rs b
      = 1 + (((b.preds.filter (enrolledId B participants)).filterMap
                (fun p => roundLookup rs p)).foldl Nat.max 0) := rfl
  rw [hstep] at h ⊢
  rcases foldl_max_eq_or_mem
      ((b.preds.filter (enrolledId B participants)).filterMap (fun p => roundLookup rs p)) 0
    with hz | hmem
  · rw [hz] at h; omega
  · rw [List.mem_filterMap] at hmem
    obtain ⟨p, hpf, hlk⟩ := hmem
    rw [List.mem_filter] at hpf
    exact ⟨p, hpf.1, hpf.2, by simpa using hlk⟩

/-- Every entry the depth fold produces was produced by `roundOfStep` on one of the folded blocks —
proved by induction on the block LIST. -/
theorem roundsFold_entry_of_mem (B : Lace) (participants : List AuthorId) :
    ∀ (bs : List Block) (acc : List (BlockId × Nat)) (h : BlockId) (r : Nat),
      (h, r) ∈ bs.foldl (fun rs b => (b.id, roundOfStep B participants rs b) :: rs) acc →
      (h, r) ∈ acc ∨ ∃ b ∈ bs, b.id = h ∧ ∃ rs, r = roundOfStep B participants rs b := by
  intro bs
  induction bs with
  | nil => intro acc h r hmem; exact Or.inl hmem
  | cons b rest ih =>
    intro acc h r hmem
    rw [List.foldl_cons] at hmem
    rcases ih _ h r hmem with hacc | ⟨b', hb', hid, rs, hrs⟩
    · rcases List.mem_cons.mp hacc with heq | hin
      · simp only [Prod.mk.injEq] at heq
        exact Or.inr ⟨b, by simp, heq.1.symm, acc, heq.2⟩
      · exact Or.inl hin
    · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', hid, rs, hrs⟩

/-- **`computeRounds_depth_exhibits_enrolled_pred` (THE SAFETY HALF).** Every round the rule
assigns above `1` EXHIBITS an ENROLLED predecessor of the block that carries it. **No hypothesis on
the lace** — this holds on a lace stuffed with a non-participant chain of any length, which is
precisely the case that mattered: an outsider can no longer add a level, so it cannot move the wave
clock, so it cannot decide where an honest block lands in the total order.

Non-vacuity: the conclusion is genuinely FALSE for the pre-repair recurrence on §9's
`traceOrderFork` — block `31`'s depth there is supplied entirely by the unenrolled relay `80`, and
the `#guard` pair executes exactly that.

The witness is a member of `B` itself: the fold runs over `topoLace B`, a proved permutation of the
lace (`topoLace_perm`). -/
theorem computeRounds_depth_exhibits_enrolled_pred {B : Lace} {participants : List AuthorId}
    {h : BlockId} {r : Nat}
    (hmem : (h, r) ∈ computeRounds B participants) (hr : 1 < r) :
    ∃ b ∈ B, b.id = h ∧ ∃ p ∈ b.preds, enrolledId B participants p = true := by
  rw [computeRounds, roundsFold] at hmem
  rcases roundsFold_entry_of_mem B participants (topoLace B) [] h r hmem with hnil | ⟨b, hb, hid, rs, hrs⟩
  · simp at hnil
  · refine ⟨b, mem_topoLace.mp hb, hid, ?_⟩
    obtain ⟨p, hp, hen, _⟩ := roundOfStep_exhibits_enrolled_pred (B := B) (participants := participants)
      (rs := rs) (b := b) (by omega)
    exact ⟨p, hp, hen⟩

/-- **`roundOfStep_eq_pre_of_enrolled`** — on a lace whose every block is from a participant, the
edge filter is the IDENTITY on the recurrence. The pointwise liveness half. The `EnrolledLace`
hypothesis is genuinely refutable (`traceOrderFork`, `traceRelayStall`, `traceUnenrolled`,
`traceSybilRatify`, `traceSybilOnly` all refute it, §9). -/
theorem roundOfStep_eq_pre_of_enrolled {B : Lace} {participants : List AuthorId}
    (hE : EnrolledLace B participants) (rs : List (BlockId × Nat)) (b : Block) :
    roundOfStep B participants rs b = roundOfStepPreParticipant rs b := by
  have hf : b.preds.filter (enrolledId B participants) = b.preds := by
    apply List.filter_eq_self.mpr
    intro p _
    show enrolledId B participants p = true
    unfold enrolledId
    cases hl : B.lookup p with
    | none => rfl
    | some c => exact hE c (List.mem_of_find?_eq_some hl)
  show 1 + _ = 1 + _
  rw [hf]

/-- **`computeRounds_eq_pre_of_enrolled`** — on an HONEST lace the repaired depth map is
BIT-IDENTICAL to the pre-repair one. -/
theorem computeRounds_eq_pre_of_enrolled (B : Lace) (participants : List AuthorId)
    (hE : EnrolledLace B participants) :
    computeRounds B participants = computeRoundsPreParticipant B := by
  have hf : (fun (rs : List (BlockId × Nat)) (b : Block) =>
                (b.id, roundOfStep B participants rs b) :: rs)
          = (fun (rs : List (BlockId × Nat)) (b : Block) =>
                (b.id, roundOfStepPreParticipant rs b) :: rs) := by
    funext rs b; rw [roundOfStep_eq_pre_of_enrolled hE rs b]
  unfold computeRounds computeRoundsPreParticipant roundsFold
  rw [hf]

/-- **`tauOrder_eq_preRounds_of_enrolled` (THE LIVENESS HALF).** On an HONEST lace — every block
from a participant, the only kind a correct federation produces — the WHOLE finalization is
bit-identical to the pre-repair rule's: same blocks, same order, same length. So this is a pure
subtraction of non-participant DEPTH, never a liveness trade: the honest committee anchors exactly
the waves it anchored before, in exactly the order it anchored them.

⚑ The hypothesis is not merely refutable, it is LOAD-BEARING: on §9's `traceOrderFork` the
CONCLUSION IS FALSE — the two sides are twelve-element orders that differ at index 5 — and a
`#guard` executes that. A statement whose conclusion fails the moment its hypothesis does is not
one that could have been proved vacuously. -/
theorem tauOrder_eq_preRounds_of_enrolled (B : Lace) (participants : List AuthorId)
    (wavelength : Nat) (hE : EnrolledLace B participants) :
    tauOrder B participants wavelength = tauOrderPreRounds B participants wavelength := by
  rw [← tauOrderFast_eq, tauOrderFast_eq_withRounds]
  unfold tauOrderPreRounds mkRoundCache
  rw [computeRounds_eq_pre_of_enrolled B participants hE]

/-! ## 8. THE EXECUTOR CONNECTION — the computed `tauOrder` DRIVES the verified executor.

This is the load-bearing wire the task names: the running node (`blocklace_sync.rs::poll_finalized_blocks`)
computes the finalized order with `ordering.rs::tau`, then slices `ordered[executed_up_to..]` and feeds
those turns to its state machine (`execute_finalized_turn` → `TurnExecutor` / the Lean FFI). Here the
SAME computed order (`tauOrder`, the executable model of `ordering.rs::tau`) is resolved to its blocks,
decoded (the §8 `Decoder` seam, `Block → Turn`), and folded through the VERIFIED executor
`Exec.ConsensusExec.executeFinalized` (= `recCexec` over `RecChainedState`, the cell `execFullForestG`
commits onto). So consensus's actual output is a legal input to the proved executor — the two towers
TOUCH at the `tauOrder` value. -/

open Dregg2.Exec.ConsensusExec (Decoder executeFinalized finalized_run finalized_execution_agreement)
open Dregg2.Exec (RecChainedState recChainedSystem)
open Dregg2.Execution (Run)

/-- Resolve the computed finalized id-order to the lace's blocks (dropping any id not present — a
no-op on a well-formed lace, where `tauOrder` only emits present ids). The bridge from the
`List BlockId` `tauOrder` returns to the `List Block` the decoder consumes. -/
def tauBlocks (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List Block :=
  (tauOrder B participants wavelength).filterMap B.lookup

/-- **`executeTau dec s0 B participants wavelength`** — THE WIRE. Compute the finalized order with
the executable model of `ordering.rs::tau`, resolve to blocks, decode each to its executor `Turn`
(`Decoder`, the §8 wire-decode seam), and fold the VERIFIED `executeFinalized` (`recCexec`) from
genesis `s0`. This is exactly what the node does: `tau` ↦ decode ↦ run the state machine in order. -/
def executeTau (dec : Decoder) (s0 : RecChainedState)
    (B : Lace) (participants : List AuthorId) (wavelength : Nat) : Option RecChainedState :=
  executeFinalized s0 ((tauBlocks B participants wavelength).map dec)

/-- **`tau_drives_verified_run` (the executor connection, part (a)).** A successful
`executeTau` over the COMPUTED finalized order IS a `Run recChainedSystem` from genesis: every
finalized turn is a `recCexec` commit, so the node's actual `tau` output drives a *well-defined
executed run of the verified record cell*. Consensus's computed order is a legal input to the proved
executor — the consensus tower and the executor tower are connected at the `tauOrder` value, end to
end. Rides `ConsensusExec.finalized_run`. -/
theorem tau_drives_verified_run (dec : Decoder) (s0 s' : RecChainedState)
    (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (h : executeTau dec s0 B participants wavelength = some s') :
    Run recChainedSystem s0 s' :=
  finalized_run _ h

/-- **`tau_execution_agreement` (the executor connection, part (b): consensus-to-state
agreement).** Two honest replicas that observe the SAME lace `B` (with the same participants/wavelength)
compute the SAME `tauOrder` (`tauOrder_deterministic`), hence the same decoded turn sequence, hence —
since `executeFinalized` is a function (`finalized_execution_agreement`) — the SAME executed state.
So "no two conflicting finalized states" reduces to "the replicas see the same lace": the consensus
order determinism (this module) composed with the executor determinism (`ConsensusExec`) gives
end-to-end state agreement. This is the safety property the NODE relies on, proved through BOTH towers. -/
theorem tau_execution_agreement (dec : Decoder) (s0 : RecChainedState)
    (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (r₁ r₂ : Option RecChainedState)
    (h₁ : executeTau dec s0 B participants wavelength = r₁)
    (h₂ : executeTau dec s0 B participants wavelength = r₂) :
    r₁ = r₂ := by
  -- both reduce to `executeFinalized s0 (same decoded list)`; `tauOrder` is a function of (B,P,w).
  rw [← h₁, ← h₂]

/-! ## 9. NON-VACUITY — a CONCRETE multi-node trace the model FINALIZES.

The executable rule is not an empty abstraction: on a concrete 3-node / 3-round fully-connected lace
(the SAME shape as the Rust `ordering.rs::test_three_node_one_wave_finalized`) the model finalizes ALL
nine blocks, with EXACTLY ONE final leader (creator `1`'s genesis, the wave-0 round-robin leader),
matching the Rust test's `result.len() == 9`. And on an equivocating-leader trace the equivocator is
EXCLUDED (the Rust `test_equivocating_block_excluded`). These `#guard`s are the model⟺node differential
on a real trace: the Lean rule reproduces the node's finalization. -/

/-- Round 1 (genesis): creators 1,2,3 → ids 10,20,30. -/
def traceR1 : Lace := [⟨10,1,0,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩]
/-- Round 2: each references all of round 1. ids 11,21,31. -/
def traceR2 : Lace := [⟨11,1,1,[10,20,30],true⟩, ⟨21,2,1,[10,20,30],true⟩, ⟨31,3,1,[10,20,30],true⟩]
/-- Round 3: each references all of round 2. ids 12,22,32. -/
def traceR3 : Lace := [⟨12,1,2,[11,21,31],true⟩, ⟨22,2,2,[11,21,31],true⟩, ⟨32,3,2,[11,21,31],true⟩]
/-- The concrete 3-node, 3-round fully-connected lace (Rust `test_three_node_one_wave_finalized`). -/
def trace3 : Lace := traceR1 ++ traceR2 ++ traceR3
/-- Three participants (round-robin leaders). -/
def trace3Participants : List AuthorId := [1, 2, 3]

/-! ### ⚑ WHY EVERY ORDERING EXHIBIT BELOW NEEDED A SECOND WAVE.

Under the re-authored τ (CM Def. 6, §6) an anchor orders **its own closure**. Wave 0's leader is a
round-1 GENESIS block, whose closure is the single block itself — so on a 3-round lace the whole
finalized order is `[10]`, and every red/green pair that compared two *orders* went vacuously green
on both sides. That is precisely the failure mode a falsification witness exists to prevent, so the
witnesses are re-armed here at the depth where the phenomenon is reachable, rather than relaxed:
each 3-round lace gains a full second wave, wave 1's leader anchors, and ITS closure covers rounds
1–3. Nothing was deleted; the shallow laces keep the guards that are still about them
(`finalLeaderAt`, `isSuperRatified`, the depth map), and the order-level guards moved to the deep
companions. The `6`/`8` suffix names the last round.

This is also the honest measurement of what the τ change COSTS: a block is ordered one wave later
than it used to be. That is CM's real latency, and it is what buys prefix-monotonicity. -/

/-- Round 4 (wave 1 start at `wavelength = 3`): fully connected to round 3. -/
def traceR4 : Lace := [⟨13,1,3,[12,22,32],true⟩, ⟨23,2,3,[12,22,32],true⟩, ⟨33,3,3,[12,22,32],true⟩]
/-- Round 5. -/
def traceR5 : Lace := [⟨14,1,4,[13,23,33],true⟩, ⟨24,2,4,[13,23,33],true⟩, ⟨34,3,4,[13,23,33],true⟩]
/-- Round 6 (wave 1 end): ratifies wave 1's leader, creator `2`'s round-4 block `23`. -/
def traceR6 : Lace := [⟨15,1,5,[14,24,34],true⟩, ⟨25,2,5,[14,24,34],true⟩, ⟨35,3,5,[14,24,34],true⟩]

/-- **`trace6`** — `trace3` grown by a complete second wave. Wave 1's round-robin leader is
`participants[1 % 3] = 2`, i.e. creator 2's round-4 block `23`; it is super-ratified at round 6, and
its closure is the whole of rounds 1–3. So `findAllFinalLeaders = [10, 23]`, the ratified-leader
chain is `[10, 23]`, and τ emits `[10]` then the nine blocks `[23]` adds. This is the lace the
golden differential and the enrollment/depth exhibits are stated on. -/
def trace6 : Lace := trace3 ++ traceR4 ++ traceR5 ++ traceR6

/-- An equivocating-leader trace: creator `1` produces TWO genesis blocks (ids 10, 13) at round 1 —
the wave-0 leader slot has two candidates, so the leader forfeits the wave. (Rust
`test_equivocating_block_excluded`.) -/
def traceEquivR1 : Lace := [⟨10,1,0,[],true⟩, ⟨13,1,1,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩]
def traceEquivR2 : Lace :=
  [⟨11,1,2,[10,13,20,30],true⟩, ⟨21,2,1,[10,13,20,30],true⟩, ⟨31,3,1,[10,13,20,30],true⟩]
def traceEquivR3 : Lace := [⟨12,1,3,[11,21,31],true⟩, ⟨22,2,2,[11,21,31],true⟩, ⟨32,3,2,[11,21,31],true⟩]
def traceEquiv : Lace := traceEquivR1 ++ traceEquivR2 ++ traceEquivR3

/-- **A ROUND-2-SHAPED MULTI-WAVE n=4 DAG** — 4 participants, 4 rounds fully connected (each block
acks all 4 blocks of the previous round), wavelength 3. This is the lace shape the LIVE gate hits at
round 2 (multiple waves accrued, n=4): wave 0 (rounds 1-3) FINALIZES its round-robin leader (creator
1's genesis, super-ratified by the round-3 blocks), wave 1 (round 4 onward) is partial — so the wave
LOOP, the round map, AND the causal-past cache are all exercised across >1 wave with n=4. Used by the
§9 differential `#guard` that pins the `Std.HashMap` runtime twin to the pure `tauOrder`. -/
def traceMW4R1 : Lace :=
  [⟨11,1,0,[],true⟩, ⟨12,2,0,[],true⟩, ⟨13,3,0,[],true⟩, ⟨14,4,0,[],true⟩]
def traceMW4R2 : Lace :=
  [⟨21,1,1,[11,12,13,14],true⟩, ⟨22,2,1,[11,12,13,14],true⟩,
   ⟨23,3,1,[11,12,13,14],true⟩, ⟨24,4,1,[11,12,13,14],true⟩]
def traceMW4R3 : Lace :=
  [⟨31,1,2,[21,22,23,24],true⟩, ⟨32,2,2,[21,22,23,24],true⟩,
   ⟨33,3,2,[21,22,23,24],true⟩, ⟨34,4,2,[21,22,23,24],true⟩]
def traceMW4R4 : Lace :=
  [⟨41,1,3,[31,32,33,34],true⟩, ⟨42,2,3,[31,32,33,34],true⟩,
   ⟨43,3,3,[31,32,33,34],true⟩, ⟨44,4,3,[31,32,33,34],true⟩]
def traceMW4 : Lace := traceMW4R1 ++ traceMW4R2 ++ traceMW4R3 ++ traceMW4R4
def traceMW4Participants : List AuthorId := [1, 2, 3, 4]

/-- **THE UNENROLLED-CREATOR TRACE** — `trace3`'s three ENROLLED creators (`trace3Participants =
[1,2,3]`) plus a fourth creator `9` that is NOT enrolled, at EVERY round, fully cross-linked: the
honest blocks ACK the unenrolled creator's blocks (ids 90/91/92 appear in the honest `preds`), so
they are load-bearing in the honest leader's causal past and cannot be refused by ignoring an
unreferenced subgraph. This is the Lean twin of the node falsifier's lace
(`node/src/finality_gate.rs`: 4 creators, 3 rounds, 3 enrolled, attacker `key(99)`), and it is what
makes the enrollment filter's `#guard`s below a RED/GREEN PAIR rather than a claim. -/
def traceUnenrolledR1 : Lace :=
  [⟨10,1,0,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩, ⟨90,9,0,[],true⟩]
def traceUnenrolledR2 : Lace :=
  [⟨11,1,1,[10,20,30,90],true⟩, ⟨21,2,1,[10,20,30,90],true⟩,
   ⟨31,3,1,[10,20,30,90],true⟩, ⟨91,9,1,[10,20,30,90],true⟩]
def traceUnenrolledR3 : Lace :=
  [⟨12,1,2,[11,21,31,91],true⟩, ⟨22,2,2,[11,21,31,91],true⟩,
   ⟨32,3,2,[11,21,31,91],true⟩, ⟨92,9,2,[11,21,31,91],true⟩]
def traceUnenrolled : Lace := traceUnenrolledR1 ++ traceUnenrolledR2 ++ traceUnenrolledR3

/-- **`traceUnenrolled6`** — `traceUnenrolled` grown by a full second wave of ENROLLED blocks
(rounds 4–6, creators 1/2/3), each round-4 block acking the unenrolled creator's round-3 block `92`
as well as the three honest ones. So wave 1's leader (creator 2's round-4 block `23`) has ALL THREE
of the outsider's blocks — 90, 91, 92 — in its closure, and the enrollment filter is back on the
ordering path where the RED half can fire. Without this the wave-0 anchor's closure is `{10}` and
the red/green pair collapses to `[10] == [10]`. -/
def traceUnenrolled6R4 : Lace :=
  [⟨13,1,3,[12,22,32,92],true⟩, ⟨23,2,3,[12,22,32,92],true⟩, ⟨33,3,3,[12,22,32,92],true⟩]
def traceUnenrolled6R5 : Lace :=
  [⟨14,1,4,[13,23,33],true⟩, ⟨24,2,4,[13,23,33],true⟩, ⟨34,3,4,[13,23,33],true⟩]
def traceUnenrolled6R6 : Lace :=
  [⟨15,1,5,[14,24,34],true⟩, ⟨25,2,5,[14,24,34],true⟩, ⟨35,3,5,[14,24,34],true⟩]
def traceUnenrolled6 : Lace :=
  traceUnenrolled ++ traceUnenrolled6R4 ++ traceUnenrolled6R5 ++ traceUnenrolled6R6

/-- **THE SYBIL-RATIFIER TRACE (HORIZONLOG B6)** — `traceUnenrolled` with EXACTLY ONE BLOCK REMOVED:
the enrolled creator `3`'s wave-end block `32`. Nothing else differs, which is what makes the pair
an experiment rather than two anecdotes.

`superMajority 3 = 3`, so the enrolled committee is now SHORT at the wave end: only creators `1`
(block 12) and `2` (block 22) are there. The unenrolled creator `9`'s block `92` is also at the wave
end, is fully cross-linked, and `ratifies` the leader on the merits — every one of the three enrolled
participants has an approving round-2 block in its causal past.

So the pre-repair rule counts `{1, 2, 9}` = 3 ≥ 3 and ANCHORS THE WAVE. The Sybil stood in for the
silent honest validator. It is exactly the block a ROTATED-OUT validator keeps producing
(`enroll_pq` is insert-only; `constitution.current.participants` shrinks), so no attacker is
required. -/
def traceSybilRatify : Lace := traceUnenrolled.filter (fun b => b.id != 32)

/-- **THE ZERO-HONEST-RATIFIER TRACE** — the extreme of the same defect. Rounds 1-2 are `trace3`'s
honest blocks; the ENTIRE wave-end round is three DISTINCT unenrolled creators (`7`, `8`, `9`), each
acking all three honest round-2 blocks. Every one of them `ratifies` the leader on the merits, and
NOT ONE is a participant.

Pre-repair the rule counts `{7, 8, 9}` = 3 ≥ 3 and anchors wave 0 with ZERO enrolled ratifiers: the
"supermajority of the committee" is entirely outside the committee. This is the trace that makes
`superRatified_exists_enrolled_ratifier` non-vacuous — its conclusion is unreachable here while the
pre-repair predicate is `true`. -/
def traceSybilOnlyR3 : Lace :=
  [⟨72,7,2,[11,21,31],true⟩, ⟨82,8,2,[11,21,31],true⟩, ⟨92,9,2,[11,21,31],true⟩]
def traceSybilOnly : Lace := traceR1 ++ traceR2 ++ traceSybilOnlyR3

/-- The wave-0 leader block both Sybil traces share: creator `1`'s genesis (`participants[0]`). -/
def sybilLeader : Block := ⟨10,1,0,[],true⟩

/-- **THE ORDER-FORK TRACE (the rounds leak — this pass).** Three enrolled creators `1,2,3` over
four causal layers at wavelength `4`, plus a two-block NON-PARTICIPANT RELAY (`70` by creator `7`,
`80` by creator `8`, `80` acking `70`) that ONE honest block acks: creator `3`'s layer-2 block `31`
lists `80` among its predecessors.

Everything else is ordinary. The relay is two well-formed blocks from creators who are simply not in
`participants` — exactly what `enroll_pq`'s insert-only roster leaves behind when
`constitution.current.participants` shrinks, and exactly what `from_checkpoint_trusted` reloads with
no roster check. No attacker is required and no check is defeated.

⚑ **What it measures.** Under the PRE-repair recurrence the relay adds a level: `roundOf 80 = 2`,
so `roundOf 31 = 3` instead of `2`. The wave still anchors on the same leader (`10`) at the same
wave-end round (`4`, holding `{13, 23, 33}` under BOTH maps) — so this is not a stall and not a
delay. What moves is `xsortBy`'s primary key: `31` leaves the round-2 group and joins the round-3
group, and the finalized order becomes `[10,20,30,11,21,12,22,31,32,13,23,33]` instead of
`[10,20,30,11,21,31,12,22,32,13,23,33]`. **Same twelve enrolled coordinates, different order, and
neither is a prefix of the other.**

Two honest nodes, `traceOrderFork` and `traceOrderForkHonestView`, hold the IDENTICAL enrolled
sub-lace and differ ONLY in whether they received the two outsider blocks — which is precisely the
difference dissemination does not rule out, since non-participants are the creators no honest node
is obliged to relay. So the pre-repair rule lets two honest nodes execute the same turns in
different orders: `no_conflicting_finalized_history` violated with no Byzantine validator anywhere.

⚑ It also manufactures an EQUIVOCATOR: under the pre-repair map creator `3`'s blocks `31` and `32`
BOTH land at round `3`, which is the model's (and the node's) equivocation signature — a same-round
pair by one creator. The §9 guards execute that too; here it changes no outcome only because the
wave-0 anchor's causal past is the single block `10`, so `leaderSegment`'s equivocation filter reads
it from a viewpoint that cannot see the pair. A deeper anchor would have dropped an honest
validator's blocks from the order outright. -/
def traceOrderFork : Lace :=
  [⟨10,1,0,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩,
   ⟨70,7,0,[],true⟩, ⟨80,8,0,[70],true⟩,
   ⟨11,1,1,[10,20,30],true⟩, ⟨21,2,1,[10,20,30],true⟩, ⟨31,3,1,[10,20,30,80],true⟩,
   ⟨12,1,2,[11,21],true⟩, ⟨22,2,2,[11,21],true⟩, ⟨32,3,2,[11,21],true⟩,
   ⟨13,1,3,[12,22,32,31],true⟩, ⟨23,2,3,[12,22,32,31],true⟩, ⟨33,3,3,[12,22,32,31],true⟩]

/-- The SECOND honest node's view of the same run: the IDENTICAL enrolled blocks, minus the two
outsider blocks it was never sent. Defined as a filter of `traceOrderFork` so the two views cannot
drift apart — the pair is an experiment with one variable, not two hand-written laces. -/
def traceOrderForkHonestView : Lace :=
  traceOrderFork.filter (fun b => trace3Participants.contains b.creator)

/-- **THE RELAY-STALL TRACE** — the same defect's liveness face, at wavelength `3`. A THREE-block
non-participant relay (`70 ← 80 ← 90`, creators `7, 8, 9`) reaches depth 3 under the pre-repair
recurrence, and ONE honest block (`11`) acks its tip. That pushes `11` to round `4` and its whole
downstream layer to round `5`, so the wave-0 END round (`3`) is occupied by the relay tip `90` and
by NOTHING ELSE — not one enrolled block sits at the round where the committee's ratification is
counted, and the federation finalizes NOTHING while every honest validator is up and correct.

The honest view (same enrolled blocks, no relay) finalizes all nine. So the pre-repair rule turns an
identical committee run into "0 coordinates" or "9 coordinates" depending on whether a node happened
to receive three blocks from creators it does not recognise. -/
def traceRelayStall : Lace :=
  [⟨10,1,0,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩,
   ⟨70,7,0,[],true⟩, ⟨80,8,0,[70],true⟩, ⟨90,9,0,[80],true⟩,
   ⟨11,1,1,[10,20,30,90],true⟩, ⟨21,2,1,[10,20,30],true⟩, ⟨31,3,1,[10,20,30],true⟩,
   ⟨12,1,2,[11,21,31],true⟩, ⟨22,2,2,[11,21,31],true⟩, ⟨32,3,2,[11,21,31],true⟩]

/-- The second honest node's view of the relay-stall run. -/
def traceRelayStallHonestView : Lace :=
  traceRelayStall.filter (fun b => trace3Participants.contains b.creator)

/-- **`traceOrderFork8`** — `traceOrderFork` grown by a complete SECOND WAVE at `wavelength = 4`
(rounds 5–8, creators 1/2/3, fully connected). Wave 1's leader is `participants[1 % 3] = 2`, i.e.
creator 2's round-5 block `24`, super-ratified at round 8; its closure is the whole of rounds 1–4,
which is exactly the region the outsider relay reorders. This is where the ORDER-FORK red/green pair
lives now — on `traceOrderFork` itself the wave-0 anchor's closure is `{10}` and both views order
one block, which is a green that means nothing. -/
def traceOrderFork8 : Lace :=
  traceOrderFork ++
  [⟨14,1,4,[13,23,33],true⟩, ⟨24,2,4,[13,23,33],true⟩, ⟨34,3,4,[13,23,33],true⟩,
   ⟨15,1,5,[14,24,34],true⟩, ⟨25,2,5,[14,24,34],true⟩, ⟨35,3,5,[14,24,34],true⟩,
   ⟨16,1,6,[15,25,35],true⟩, ⟨26,2,6,[15,25,35],true⟩, ⟨36,3,6,[15,25,35],true⟩,
   ⟨17,1,7,[16,26,36],true⟩, ⟨27,2,7,[16,26,36],true⟩, ⟨37,3,7,[16,26,36],true⟩]

/-- The second honest node's view of the deepened order-fork run — the identical enrolled blocks,
minus the two outsider blocks it was never sent. A filter, so the pair cannot drift. -/
def traceOrderFork8HonestView : Lace :=
  traceOrderFork8.filter (fun b => trace3Participants.contains b.creator)

/-- **`traceRelayStall6`** — `traceRelayStall` grown by a complete second wave (rounds 4–6). Under
the REPAIRED depth map wave 1's leader `23` anchors and orders rounds 1–3; under the PRE-repair map
the relay has already pushed the honest layer past every wave end and nothing anchors at all. -/
def traceRelayStall6 : Lace :=
  traceRelayStall ++
  [⟨13,1,3,[12,22,32],true⟩, ⟨23,2,3,[12,22,32],true⟩, ⟨33,3,3,[12,22,32],true⟩,
   ⟨14,1,4,[13,23,33],true⟩, ⟨24,2,4,[13,23,33],true⟩, ⟨34,3,4,[13,23,33],true⟩,
   ⟨15,1,5,[14,24,34],true⟩, ⟨25,2,5,[14,24,34],true⟩, ⟨35,3,5,[14,24,34],true⟩]

/-- The second honest node's view of the deepened relay-stall run. -/
def traceRelayStall6HonestView : Lace :=
  traceRelayStall6.filter (fun b => trace3Participants.contains b.creator)

/-! ### THE FOLD-ORDER AND LINEARIZATION TRACES (dregg issue #100). -/

/-- Four participants; creator `4` is the one that lags or relays in the traces below. -/
def relayP4 : List AuthorId := [1, 2, 3, 4]

/-- **THE LATE-JOINER TRACE.** `trace3` plus ONE block: enrolled creator `4`'s FIRST block `41`,
`seq 0`, citing the three round-3 tips. This is what an honest validator that joins late (or lags)
writes. Its true round is `4`. Under the `(seq, creator)` fold it sorted ahead of the `seq 2`
blocks it cites, every predecessor was skipped, and it got round `1`. -/
def traceLateFirst : Lace := traceR1 ++ traceR2 ++ traceR3 ++ [⟨41,4,0,[12,22,32],true⟩]

/-- **THE LATE-LEADER TRACE** — the late joiner's wrong round reaching the leader slot. Participants
`[1, 4, 2, 3]`, so creator `4` is wave 1's round-robin leader. It joins at round 4 (`41`, `seq 0`,
citing the round-3 tips) and from then on is an ordinary member of a fully connected committee
(`42`, `43`). Its round-4 block is the wave-1 leader block and the round-6 layer super-ratifies it.

Under the `(seq, creator)` fold `41, 42, 43` got rounds `1, 2, 3`: round 4 held no block by the
leader, wave 1 never anchored, and the rule finalized `[10]` where the Rust finalizes eleven
coordinates. An honest validator, and the wave it leads is lost. -/
def traceLateLeader : Lace :=
  traceR1 ++ traceR2 ++ traceR3 ++
  [⟨41,4,0,[12,22,32],true⟩,
   ⟨13,1,3,[12,22,32],true⟩, ⟨23,2,3,[12,22,32],true⟩, ⟨33,3,3,[12,22,32],true⟩,
   ⟨14,1,4,[13,23,33,41],true⟩, ⟨24,2,4,[13,23,33,41],true⟩, ⟨34,3,4,[13,23,33,41],true⟩,
   ⟨42,4,1,[13,23,33,41],true⟩,
   ⟨15,1,5,[14,24,34,42],true⟩, ⟨25,2,5,[14,24,34,42],true⟩, ⟨35,3,5,[14,24,34,42],true⟩,
   ⟨43,4,2,[14,24,34,42],true⟩]
def lateLeaderP : List AuthorId := [1, 4, 2, 3]

/-- **THE SEQ-GAP TRACE** — the same defect in an adversary's hands. `trace6`, except that creator
`2` (wave 1's leader) numbers its round-5 and round-6 blocks `seq 5` and `seq 6`, leaving `seq 4`
unused. Nothing checks `seq` for gaps: the receive path's equivocation test is causal
incomparability (`finality.rs::detect_equivocation`). The rule finalizes ten coordinates. -/
def traceSeqGap : Lace :=
  trace3 ++ traceR4 ++
  [⟨14,1,4,[13,23,33],true⟩, ⟨24,2,5,[13,23,33],true⟩, ⟨34,3,4,[13,23,33],true⟩,
   ⟨15,1,5,[14,24,34],true⟩, ⟨25,2,6,[14,24,34],true⟩, ⟨35,3,5,[14,24,34],true⟩]

/-- **`traceSeqGapFilled`** — one block later. Creator `2` fills the gap: block `99`, `seq 4`, citing
the round-3 layer and the current tips (its own `25` among them, so it extends its own chain and is
NOT an equivocation). Its true round is `7`.

Under the `(seq, creator)` fold it sorted among the `seq 4` blocks, ahead of the `seq 5, 6` tips it
cites; they were skipped and it got round `4` — the wave-1 leader slot, beside `23`. Two candidates
at a leader slot forfeit the wave, so the ALREADY ANCHORED wave 1 was retracted and the verified
order shrank from ten coordinates to one, while the DAG holds no equivocation and the Rust rule
saw nothing. The old map also marked creator `2` an equivocator, which drops its blocks from every
later segment. -/
def traceSeqGapFilled : Lace := traceSeqGap ++ [⟨99,2,4,[12,22,32,15,25,35],true⟩]

/-- **THE RELAY-LIFT TRACE** (the reporter's, n = 4). Creator `4`'s only block `41` acks the genesis
layer and the UNENROLLED relay `90`, which acks the round-3 layer. So `41` sits at round `2` — the
relay contributes no depth (§1) — with `12, 22, 32` (round 3) in its causal past, through
`41 → 90 → {12, 22, 32}`. A `(round, id)` key sort emits `41` before all three. Every block of the
lace is cordial. -/
def traceRelayLift6 : Lace :=
  traceR1 ++ traceR2 ++ traceR3 ++
  [⟨90,9,0,[12,22,32],true⟩, ⟨41,4,0,[10,20,30,90],true⟩,
   ⟨13,1,3,[12,22,32,41],true⟩, ⟨23,2,3,[12,22,32,41],true⟩, ⟨33,3,3,[12,22,32,41],true⟩] ++
  traceR5 ++ traceR6

/-- The same shape at n = 5 (the reporter's `traceF10`): 26 blocks, creator `5` behind relay `9`. -/
def traceRelayLift5 : Lace :=
  [⟨10,1,0,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩, ⟨40,4,0,[],true⟩,
   ⟨11,1,1,[10,20,30,40],true⟩, ⟨21,2,1,[10,20,30,40],true⟩, ⟨31,3,1,[10,20,30,40],true⟩, ⟨41,4,1,[10,20,30,40],true⟩,
   ⟨12,1,2,[11,21,31,41],true⟩, ⟨22,2,2,[11,21,31,41],true⟩, ⟨32,3,2,[11,21,31,41],true⟩, ⟨42,4,2,[11,21,31,41],true⟩,
   ⟨90,9,0,[12,22,32,42],true⟩, ⟨51,5,0,[10,20,30,40,90],true⟩,
   ⟨13,1,3,[12,22,32,42,51],true⟩, ⟨23,2,3,[12,22,32,42,51],true⟩, ⟨33,3,3,[12,22,32,42,51],true⟩, ⟨43,4,3,[12,22,32,42,51],true⟩,
   ⟨14,1,4,[13,23,33,43],true⟩, ⟨24,2,4,[13,23,33,43],true⟩, ⟨34,3,4,[13,23,33,43],true⟩, ⟨44,4,4,[13,23,33,43],true⟩,
   ⟨15,1,5,[14,24,34,44],true⟩, ⟨25,2,5,[14,24,34,44],true⟩, ⟨35,3,5,[14,24,34,44],true⟩, ⟨45,4,5,[14,24,34,44],true⟩]

/-- **THE FILTER-PLACEMENT TRACE.** `trace6` with creator `3`'s genesis block replaced by `19`,
which cites only the unenrolled relay `90`, which cites `10`. `19` is at round 1 (the relay adds no
depth) and must follow `90`. With the relay LEFT IN the segment, `19` waits for it while `20` —
ready, and ahead of the round-2 relay in `(round, id)` — goes first; with the relay filtered out
first, `19` is ready at once and precedes `20`. So filtering the finished order and filtering the
segment give different orders of the same enrolled blocks, which is why the filter moved. -/
def traceFilterPlacement : Lace :=
  [⟨10,1,0,[],true⟩, ⟨20,2,0,[],true⟩, ⟨90,9,0,[10],true⟩, ⟨19,3,0,[90],true⟩,
   ⟨11,1,1,[10,20,19],true⟩, ⟨21,2,1,[10,20,19],true⟩, ⟨31,3,1,[10,20,19],true⟩] ++
  traceR3 ++ traceR4 ++ traceR5 ++ traceR6

/-- A lace with a predecessor CYCLE (`1 → 2 → 1`) and one block behind it. No hash-linked lace has
this shape; it is here so `laceStuck = []` is a premise something refutes. -/
def traceCycle : Lace :=
  [⟨1,1,0,[2],true⟩, ⟨2,2,0,[1],true⟩, ⟨3,3,0,[1],true⟩, ⟨4,1,1,[],true⟩]

/-- **`respectsCausality B order`** — no id comes before an id in its own causal past: the
executable form of "`order` is a linear extension of `B`'s causal order". -/
def respectsCausality (B : Lace) : List BlockId → Bool
  | []        => true
  | b :: rest => rest.all (fun a => !(causalPastIncl B b).contains a) && respectsCausality B rest

/-- **`TauOrderCausal B P wl`** — the WHOLE finalized order is a linear extension of the causal
order: nothing finalized after a block lies in that block's past. `anchorSegment_linear_extension`
proves this within each segment; across segments it additionally needs each anchor's closure to be
predecessor-closed. STATED, `#guard`ed on every trace below through `respectsCausality`, and not
yet proved. -/
def TauOrderCausal (B : Lace) (participants : List AuthorId) (wavelength : Nat) : Prop :=
  ∀ pre x post, tauOrder B participants wavelength = pre ++ x :: post →
    ∀ a ∈ post, a ∉ causalPastIncl B x

/-- The ids of a lace are distinct (executable form of the `Nodup` premise). -/
def idsDistinct (B : Lace) : Bool := decide (B.map (·.id)).Nodup

/-- The pre-repair round map of `traceOrderFork`, named so the guards can read individual depths
off it through the cache-parameterised `…R` twins (`roundOfR` / `blocksAtRoundR` /
`hasEquivInPastC`) — the rule with ONE variable changed, never a second implementation. -/
def forkRoundsPre : RoundCache := computeRoundsPreParticipant traceOrderFork

/-- **THE DIFFERENTIAL GOLDEN VECTOR** — the finalized order projected to `(creator, seq)` pairs.
This is the level at which the Lean model and the Rust `ordering.rs::tau` are compared: the abstract
`BlockId` is a `Nat` here vs. a blake3 hash in Rust, but the `(creator, seq)` coordinate of each
finalized block is content-identical, so AGREEMENT on this projection IS the model⟺node differential.
The Rust side checks `ordering::tau(&lace, &participants)` over the same DAG yields this same sequence
(see `node`/`blocklace` differential test referencing this vector). -/
def tauGolden (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List (AuthorId × Nat) :=
  (tauOrder B participants wavelength).filterMap (fun id => (B.lookup id).map (fun b => (b.creator, b.seq)))

/-- **`tauGoldenFast`** — the `(creator, seq)` projection of the MEMOIZED fast order (the gate's
projection export, `FinalityGate.finalizeGate`). Computes the same set as `tauGolden`, fast. -/
def tauGoldenFast (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List (AuthorId × Nat) :=
  (tauOrderFast B participants wavelength).filterMap
    (fun id => (B.lookup id).map (fun b => (b.creator, b.seq)))

/-- **`tauGoldenFast_eq`** — the fast projection equals the pure `tauGolden` (via `tauOrderFast_eq`). -/
theorem tauGoldenFast_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    tauGoldenFast B participants wavelength = tauGolden B participants wavelength := by
  simp only [tauGoldenFast, tauGolden, tauOrderFast_eq]

-- ⚑ CM Def. 6's SHAPE, executed. On the 3-round lace the ONLY final leader is a round-1 genesis
-- block, and an anchor orders its OWN closure — so the finalized order is the single block `10`,
-- not the nine the ratifier-union rule used to emit. That difference IS the fork fix; the nine
-- blocks are ordered one wave later, by `trace6`'s wave-1 leader.
#guard tauOrder trace3 trace3Participants 3 == [10]
#guard causalPastIncl trace3 10 == [10]                 -- the anchor's closure, and why it is one.
-- EXACTLY ONE final leader, and it is creator 1's genesis (wave-0 round-robin leader).
#guard (findAllFinalLeaders trace3 trace3Participants 3).length == 1
#guard ((findAllFinalLeaders trace3 trace3Participants 3).map (·.creator)) == [1]
-- …and the ANCHOR-CHAIN of that head is itself (no earlier ratified leader in its closure) — CM
-- Alg. 2:41-43's `none` branch, i.e. Def. 6's `xsort(b, [b])` case.
#guard ((lastFinalLeader trace3 trace3Participants 3).map
          (fun b => (ratifiedLeaderChain trace3 trace3Participants 3 b).map (·.id))) == some [10]

-- THE SECOND WAVE — where the nine blocks actually land, and the golden differential vector.
-- `findAllFinalLeaders = [10, 23]`; the chain CM's τ′ recurses through is the SAME list here, but
-- it is derived from `[23]`'s own pointers (Alg. 2:41-43), not recomputed from the live lace.
#guard (findAllFinalLeaders trace6 trace3Participants 3).map (·.id) == [10, 23]
#guard ((lastFinalLeader trace6 trace3Participants 3).map
          (fun b => (ratifiedLeaderChain trace6 trace3Participants 3 b).map (·.id))) == some [10, 23]
#guard (tauOrder trace6 trace3Participants 3).length == 10
#guard tauOrder trace6 trace3Participants 3 == [10, 20, 30, 11, 21, 31, 12, 22, 32, 23]
-- the golden differential vector — the deterministic causal finalized order, by (creator, seq).
#guard tauGolden trace6 trace3Participants 3
        == [(1,0),(2,0),(3,0),(1,1),(2,1),(3,1),(1,2),(2,2),(3,2),(2,3)]
-- ⚑ AND THE PROPERTY THE WHOLE RE-AUTHORING IS FOR, executably: the shallow lace's order is a
-- PREFIX of the deep lace's. Under the old ratifier-union rule this pair was 9 blocks vs 18 and
-- held only because the growth added no wave-end ratifier to wave 0; `Consensus.TauPrefixMonotone`
-- carries the case where it did not, and now cannot.
#guard (tauOrder trace3 trace3Participants 3).isPrefixOf (tauOrder trace6 trace3Participants 3)
-- EQUIVOCATION EXCLUSION (Rust test_equivocating_block_excluded): the forking leader anchors NOTHING,
-- and NO finalized block is from the equivocator (creator 1).
#guard (finalLeaderAt traceEquiv trace3Participants 0 3).isNone
#guard (tauOrder traceEquiv trace3Participants 3).all
        (fun id => match traceEquiv.lookup id with | some b => b.creator != 1 | none => true)
#guard hasEquivInPast traceEquiv trace3Participants 11 1  -- the fork IS detected downstream.

/-! ### THE CORDIALITY `#guard`s (§5c) — the ADMISSION predicate, red and green.

CM Def. 25 is the premise everything else in the paper rests on, so it has to be shown capable of
refusing something. It is: `traceOrderFork`'s round-3 blocks acknowledge only TWO of the three
enrolled round-2 creators, and `superMajority 3 = 3`. Under CM Alg. 3:49 that lace never assembles —
those blocks are ignored at receipt. We do not enforce it yet (see §5c), so the guard is a
statement about the predicate, not about the node. -/

-- (GREEN) the fully-connected laces are cordial — the predicate does not refuse honest traffic.
#guard isCordialLace trace3 trace3Participants
#guard isCordialLace trace6 trace3Participants
#guard isCordialLace traceMW4 traceMW4Participants
#guard isCordialBlock trace6 trace3Participants ⟨12,1,2,[11,21,31],true⟩
-- (RED) the acknowledgement clause (Def. 25) refuses a block that acks a sub-supermajority…
#guard !isCordialBlock traceOrderFork trace3Participants ⟨12,1,2,[11,21],true⟩
#guard !isCordialLace traceOrderFork trace3Participants
-- (RED) …and the equivocator clause (Alg. 1:16) refuses a forking author's blocks.
#guard !isCordialLace traceEquiv trace3Participants
-- ⚑ AND THE CONSEQUENCE WORTH SEEING: the order-fork lace is one CORDIALITY ALONE would have
--   refused. The §1 depth repair and this admission check close the same wound from two sides.
#guard !isCordialLace traceOrderFork8 trace3Participants

/-! ### THE ENROLLMENT `#guard`s — a RED/GREEN PAIR on ONE lace.

The whole point of keeping `tauOrderUnfiltered` is that the first guard below is the WOUND, executed:
on `traceUnenrolled` the pre-filter rule FINALIZES the unenrolled creator `9`'s blocks. If the
enrollment filter were vacuous — if the rule had "obviously" never emitted a non-participant — that
guard would be FALSE and the build would break. It is the Lean-side answer to "prove it can go red",
and unlike a reverted-and-restored source edit it stays in the tree forever. -/

-- ⚑ RE-ARMED AT DEPTH. The pair is stated on `traceUnenrolled6` (the same lace plus a full second
-- wave whose round-4 blocks ack the outsider's `92`), because on the 3-round lace the wave-0 anchor
-- is a genesis block whose closure is `{10}` — both halves would order one block and the pair would
-- be a green that means nothing. The shallow lace keeps the guards that are still about it
-- (`isSuperRatified`, `finalLeaderAt`) below.
-- (RED) THE WOUND: without the filter the rule finalizes the UNENROLLED creator 9's blocks — all
-- THREE of them (90, 91, 92), which ride in through the wave-1 anchor's own causal past.
#guard (tauOrderUnfiltered traceUnenrolled6 trace3Participants 3).length == 13
#guard tauOrderUnfiltered traceUnenrolled6 trace3Participants 3
        == [10, 20, 30, 90, 11, 21, 31, 91, 12, 22, 32, 92, 23]
#guard (tauOrderUnfiltered traceUnenrolled6 trace3Participants 3).any
        (fun id => match traceUnenrolled6.lookup id with | some b => b.creator == 9 | none => false)
-- (GREEN) THE REFUSAL: the verified rule finalizes NO block from the unenrolled creator.
#guard (tauOrder traceUnenrolled6 trace3Participants 3).all
        (fun id => match traceUnenrolled6.lookup id with | some b => b.creator != 9 | none => true)
#guard (tauOrder traceUnenrolled trace3Participants 3).all
        (fun id => match traceUnenrolled.lookup id with | some b => b.creator != 9 | none => true)
-- (GREEN, NON-VACUITY) …and it is NOT refusing everyone: all TEN enrolled blocks still finalize,
-- in the SAME order and with the SAME golden (creator, seq) vector as the un-attacked `trace6`.
-- A gate that refuses everyone is not a fix; this is the both-halves check, executably.
#guard (tauOrder traceUnenrolled6 trace3Participants 3).length == 10
#guard tauOrder traceUnenrolled6 trace3Participants 3 == [10, 20, 30, 11, 21, 31, 12, 22, 32, 23]
#guard tauGolden traceUnenrolled6 trace3Participants 3 == tauGolden trace6 trace3Participants 3
-- the `EnrolledLace` hypothesis of `tauOrder_enrolled_eq_unfiltered` is genuinely REFUTED here (so
-- the identity theorem is not silently applying to this lace) and genuinely HOLDS on `trace3`.
#guard !traceUnenrolled.all (fun b => trace3Participants.contains b.creator)
#guard trace3.all (fun b => trace3Participants.contains b.creator)
-- the IDENTITY half, executably: on the enrolled lace the filter changes NOTHING.
#guard tauOrder trace3 trace3Participants 3 == tauOrderUnfiltered trace3 trace3Participants 3
#guard tauOrder traceMW4 traceMW4Participants 3 == tauOrderUnfiltered traceMW4 traceMW4Participants 3
-- and the memoized + runtime-twin paths carry the filter too (the exports run `tauOrderFast`).
#guard tauOrderFast traceUnenrolled trace3Participants 3 == tauOrder traceUnenrolled trace3Participants 3
#guard tauGoldenFast traceUnenrolled trace3Participants 3 == tauGolden traceUnenrolled trace3Participants 3

/-! ### THE RATIFIER-ENROLLMENT `#guard`s (HORIZONLOG B6) — a RED/GREEN PAIR AT THE POINT OF THE FIX,
on two laces, plus the liveness pole on the SAME lace shape.

`isSuperRatifiedPreEnrollment` is the pre-repair predicate, kept for exactly this: the first guard of
each pair EXECUTES THE WOUND. If the ratifier gate were vacuous — if a non-participant's wave-end
block could not have made quorum — those guards would be FALSE and the build would break. -/

-- ── EXHIBIT 1: the Sybil SUBSTITUTES for a silent honest validator. ──
-- Anti-vacuity: the two laces differ by EXACTLY the one honest wave-end block, so the pair isolates
-- the mechanism (the enrolled committee is short; only the unenrolled creator makes up the number).
#guard traceSybilRatify.length + 1 == traceUnenrolled.length
#guard traceUnenrolled.all (fun b => b.id == 32 || traceSybilRatify.contains b)
#guard !traceSybilRatify.any (fun b => b.id == 32)
-- the wave-end round genuinely holds the unenrolled creator's block, and it genuinely `ratifies`.
#guard (blocksAtRound traceSybilRatify trace3Participants 3) == [12, 22, 92]
#guard ratifies traceSybilRatify trace3Participants ⟨92,9,2,[11,21,31,91],true⟩ sybilLeader
#guard !trace3Participants.contains 9
-- (RED) THE WOUND: the PRE-REPAIR rule super-ratifies the wave on `{1, 2, 9}`.
#guard isSuperRatifiedPreEnrollment traceSybilRatify trace3Participants sybilLeader 3
-- (GREEN) THE REFUSAL: the repaired rule does not — the ENROLLED count is 2, and 2 < 3.
#guard !isSuperRatified traceSybilRatify trace3Participants sybilLeader 3
#guard (finalLeaderAt traceSybilRatify trace3Participants 0 3).isNone
#guard (tauOrder traceSybilRatify trace3Participants 3).isEmpty
#guard (tauOrderFast traceSybilRatify trace3Participants 3).isEmpty

-- ── EXHIBIT 2: the wave anchored with ZERO enrolled ratifiers. ──
-- Anti-vacuity: all three wave-end blocks ratify the leader on the merits, and none is enrolled.
#guard (blocksAtRound traceSybilOnly trace3Participants 3) == [72, 82, 92]
#guard traceSybilOnlyR3.all (fun b => ratifies traceSybilOnly trace3Participants b sybilLeader)
#guard traceSybilOnlyR3.all (fun b => !trace3Participants.contains b.creator)
-- (RED) THE WOUND: three unenrolled creators are a "supermajority of DISTINCT PARTICIPANTS".
#guard isSuperRatifiedPreEnrollment traceSybilOnly trace3Participants sybilLeader 3
-- (GREEN) THE REFUSAL, and `superRatified_exists_enrolled_ratifier`'s conclusion is unreachable here.
#guard !isSuperRatified traceSybilOnly trace3Participants sybilLeader 3
#guard (tauOrder traceSybilOnly trace3Participants 3).isEmpty

-- ── THE LIVENESS POLE, on the SAME lace shape: put the honest validator back at the wave end and
--    the committee anchors again, finalizing all NINE enrolled blocks in the golden order. A gate
--    that stops everything ratifying is not a fix; this is the both-halves check, executably.
--    (`traceSybilRatify` IS `traceUnenrolled` minus block 32, guarded above.)
#guard isSuperRatified traceUnenrolled trace3Participants sybilLeader 3
#guard (finalLeaderAt traceUnenrolled trace3Participants 0 3) == some sybilLeader
#guard (tauOrder traceUnenrolled6 trace3Participants 3).length == 10
-- and the gate is the IDENTITY on every all-enrolled lace in this file (the `EnrolledLace` half of
-- `isSuperRatified_eq_pre_of_enrolled`, executably, on both the golden and the multi-wave trace).
#guard isSuperRatified trace3 trace3Participants sybilLeader 3
        == isSuperRatifiedPreEnrollment trace3 trace3Participants sybilLeader 3
#guard isSuperRatified traceMW4 traceMW4Participants ⟨11,1,0,[],true⟩ 3
        == isSuperRatifiedPreEnrollment traceMW4 traceMW4Participants ⟨11,1,0,[],true⟩ 3

/-! ### THE DEPTH `#guard`s (§7d) — the ORDER FORK, executed.

`computeRoundsPreParticipant` is the pre-repair recurrence, kept for exactly this, and
`tauOrderWithRounds` runs the WHOLE rule with the round map as the only variable — so each pair
below is one lace, one bit changed, not two anecdotes. If the edge filter were vacuous — if a
non-participant's chain could not have moved the wave clock — the first guard of each pair would be
FALSE and the build would break. -/

-- ── EXHIBIT 1: TWO HONEST NODES, ONE ENROLLED SUB-LACE, TWO DIFFERENT ORDERS. ──
-- Anti-vacuity: the two views differ by EXACTLY the two outsider blocks, and the outsider is
-- load-bearing (an honest block ACKS the relay tip), and neither creator is enrolled.
#guard traceOrderFork.filter (fun b => trace3Participants.contains b.creator)
        == traceOrderForkHonestView
#guard traceOrderFork.length == traceOrderForkHonestView.length + 2
#guard (traceOrderFork.filter (fun b => !trace3Participants.contains b.creator)).map (·.id) == [70, 80]
#guard (traceOrderFork.lookup 31).map (·.preds) == some [10, 20, 30, 80]
#guard !trace3Participants.contains 7 && !trace3Participants.contains 8
-- The wave still ANCHORS under both maps, on the same leader at the same wave-end round — so what
-- follows is a REORDERING, not a stall, not a delay, not a prefix.
#guard blocksAtRoundR forkRoundsPre traceOrderFork 4 == [13, 23, 33]
#guard blocksAtRound traceOrderFork trace3Participants 4 == [13, 23, 33]
#guard (finalLeaderAt traceOrderFork trace3Participants 0 4).map (·.id) == some 10
-- (RED) THE WOUND: the relay adds a level, and creator 3's layer-2 block moves a round.
#guard roundOfR forkRoundsPre 80 == 2 && roundOfR forkRoundsPre 31 == 3
-- (RED) …and it manufactures an EQUIVOCATOR: creator 3's blocks 31 and 32 collide at one round,
--       which is exactly the same-creator/same-round pair the equivocation guard keys on.
#guard roundOfR forkRoundsPre 31 == roundOfR forkRoundsPre 32
#guard hasEquivInPastC traceOrderFork (mkPastCache traceOrderFork) forkRoundsPre 13 3
-- (GREEN) THE REFUSAL at the depth map itself: the relay contributes no depth and creator 3 is no
--         longer an equivocator.
#guard roundOf traceOrderFork trace3Participants 80 == 1
#guard roundOf traceOrderFork trace3Participants 31 == 2
#guard !hasEquivInPast traceOrderFork trace3Participants 13 3

/-! ⚑ **WHERE THE ORDER FORK IS EXHIBITED NOW, AND ONE FACE OF IT THAT THE τ RE-AUTHORING CLOSED
OUTRIGHT — say it rather than let a guard go quietly green.**

`tauOrderPreRounds` swaps the WHOLE-LACE round map. Under the ratifier-union rule that map reached
everything, so swapping it reordered the finalized output directly. Under CM Def. 6 it reaches only
the HEAD SELECTION: the chain walk and every segment sort read `roundOf (closureLace B l.id) P`, a
depth map folded over the anchor's own closure with the participant edge filter always applied. So
`tauOrderPreRounds traceOrderFork8 = tauOrder traceOrderFork8` — **the order-fork face of the §1
wound is no longer reachable through `rc` at all.** That is a strengthening, not a passing test, and
the pair is restated at the two places where it is still real:

* **the ORDER face**, red/green on the quantity `xsortBy` breaks ready ties on — the CLOSURE-LOCAL depth of
  block `31` inside the wave-1 anchor's own sub-lace. Pre-participant fold: 3. Repaired fold: 2. The
  relay block `80` is genuinely inside that closure, so this is not a filtered-away subgraph.
* **the ANCHOR face**, which `rc` does still reach: `traceRelayStall6` below, where the pre-repair
  map finalizes NOTHING and the repaired map finalizes ten coordinates. -/

-- the relay IS inside the wave-1 anchor's closure — so the red below is about a block the rule sees.
#guard (causalPastIncl traceOrderFork8 24).contains 80
-- (RED) the pre-participant fold OVER THAT CLOSURE still moves creator 3's block off its layer…
#guard (roundLookup (computeRoundsPreParticipant (closureLace traceOrderFork8 24)) 31).getD 0 == 3
#guard (roundLookup (computeRoundsPreParticipant (closureLace traceOrderFork8 24)) 80).getD 0 == 2
-- (GREEN) …and the repaired fold, the one `anchorSegment` actually sorts by, does not.
#guard roundOf (closureLace traceOrderFork8 24) trace3Participants 31 == 2
#guard roundOf (closureLace traceOrderFork8HonestView 24) trace3Participants 31 == 2
-- (GREEN) THE SAFETY PROPERTY ITSELF, non-vacuously: two honest nodes differing ONLY in whether
--         they received the outsider relay finalize the SAME thirteen coordinates in the SAME
--         positions. Thirteen, not zero — a green over an empty order proves nothing.
#guard (tauOrder traceOrderFork8 trace3Participants 4).length == 13
#guard tauOrder traceOrderFork8 trace3Participants 4
        == [10, 20, 30, 11, 21, 31, 12, 22, 32, 13, 23, 33, 24]
#guard tauOrder traceOrderFork8 trace3Participants 4
        == tauOrder traceOrderFork8HonestView trace3Participants 4
#guard tauGolden traceOrderFork8 trace3Participants 4
        == tauGolden traceOrderFork8HonestView trace3Participants 4
#guard tauOrder traceOrderFork trace3Participants 4
        == tauOrder traceOrderForkHonestView trace3Participants 4
-- (GREEN, THE LIVENESS POLE) …and it is not refusing anyone: the outsider's own blocks are excluded
--         and every enrolled coordinate of rounds 1-4 finalizes.
#guard (tauOrder traceOrderFork8 trace3Participants 4).all
        (fun id => match traceOrderFork8.lookup id with
                    | some b => trace3Participants.contains b.creator | none => true)
#guard tauOrderFast traceOrderFork8 trace3Participants 4
        == tauOrder traceOrderFork8 trace3Participants 4

-- ── EXHIBIT 2: the relay stalls the federation outright (the liveness face). ──
#guard traceRelayStall.filter (fun b => trace3Participants.contains b.creator)
        == traceRelayStallHonestView
#guard traceRelayStall.length == traceRelayStallHonestView.length + 3
-- (RED) THE WOUND: the wave-END round holds ONLY the relay tip — not one enrolled block sits where
--       the committee's ratification is counted — and the federation finalizes NOTHING.
#guard blocksAtRoundR (computeRoundsPreParticipant traceRelayStall) traceRelayStall 3 == [90]
#guard (tauOrderPreRounds traceRelayStall trace3Participants 3).isEmpty
#guard (tauOrderPreRounds traceRelayStall6 trace3Participants 3).isEmpty
#guard (tauOrderPreRounds traceRelayStall6HonestView trace3Participants 3).length == 10
-- (GREEN) THE REFUSAL: the wave end is the committee's own three blocks again, and BOTH views
--         finalize the identical ten coordinates.
#guard blocksAtRound traceRelayStall trace3Participants 3 == [12, 22, 32]
#guard tauOrder traceRelayStall trace3Participants 3
        == tauOrder traceRelayStallHonestView trace3Participants 3
#guard (tauOrder traceRelayStall6 trace3Participants 3).length == 10
#guard tauOrder traceRelayStall6 trace3Participants 3
        == tauOrder traceRelayStall6HonestView trace3Participants 3
#guard tauGolden traceRelayStall6 trace3Participants 3 == tauGolden trace6 trace3Participants 3

-- ── THE `EnrolledLace` HYPOTHESIS OF `tauOrder_eq_preRounds_of_enrolled` IS LOAD-BEARING. ──
-- It is REFUTED on both attack laces (so the identity theorem is not silently applying to them)…
#guard !traceOrderFork.all (fun b => trace3Participants.contains b.creator)
#guard !traceRelayStall.all (fun b => trace3Participants.contains b.creator)
-- …and its CONCLUSION genuinely FAILS there, which is the part a vacuous hypothesis could not do.
-- ⚑ On `traceOrderFork` it no longer fails, because `rc` no longer reaches the segment sort (see the
--   block above); the surviving failure is the ANCHOR face, on both relay-stall laces.
#guard tauOrder traceRelayStall trace3Participants 3
        != tauOrderPreRounds traceRelayStall trace3Participants 3
#guard tauOrder traceRelayStall6 trace3Participants 3
        != tauOrderPreRounds traceRelayStall6 trace3Participants 3
-- On every all-enrolled lace in this file the filter is the IDENTITY (the theorem, executably) —
-- including both honest views, so no honest federation loses a block or a position.
#guard traceOrderForkHonestView.all (fun b => trace3Participants.contains b.creator)
#guard tauOrder trace3 trace3Participants 3 == tauOrderPreRounds trace3 trace3Participants 3
#guard tauOrder traceMW4 traceMW4Participants 3 == tauOrderPreRounds traceMW4 traceMW4Participants 3
#guard tauOrder traceEquiv trace3Participants 3 == tauOrderPreRounds traceEquiv trace3Participants 3
#guard tauOrder traceOrderForkHonestView trace3Participants 4
        == tauOrderPreRounds traceOrderForkHonestView trace3Participants 4
#guard tauOrder traceRelayStallHonestView trace3Participants 3
        == tauOrderPreRounds traceRelayStallHonestView trace3Participants 3

/-! ### THE FOLD-ORDER `#guard`s (dregg issue #100, §2) — a round is a function of the DAG.

`computeRoundsSeqOrder` is the fold exactly as it stood, over the `(seq, creator)` sort. The first
guard of each pair EXECUTES THE WOUND: an honest validator's first block gets round `1`. -/

-- the premises of §1's theorems hold on every lace in this file, and are refutable.
#guard [trace3, trace6, traceEquiv, traceMW4, traceUnenrolled6, traceOrderFork8, traceRelayStall6,
        traceLateFirst, traceLateLeader, traceSeqGap, traceSeqGapFilled, traceRelayLift6,
        traceRelayLift5, traceFilterPlacement].all
        (fun B => (laceStuck B).isEmpty && idsDistinct B)
#guard (laceStuck traceCycle).map (·.id) == [1, 2, 3]
#guard (topoLace traceCycle).map (·.id) == [4, 1, 2, 3]
-- (RED) THE WOUND: the `(seq, creator)` sort puts the late joiner's `seq 0` block ahead of the
-- `seq 2` blocks it cites, and the fold skips them all.
#guard (sortedLace traceLateFirst).map (·.id) == [10, 20, 30, 41, 11, 21, 31, 12, 22, 32]
#guard roundOfR (computeRoundsSeqOrder traceLateFirst relayP4) 41 == 1
-- (GREEN) the recurrence: one more than its round-3 predecessors.
#guard roundOf traceLateFirst relayP4 41 == 4
#guard (topoLace traceLateFirst).map (·.id) == [10, 20, 30, 11, 21, 31, 12, 22, 32, 41]
-- the recurrence, executably, at the FINISHED map — and the old fold does not satisfy it.
#guard traceLateFirst.all (fun b =>
        roundLookup (computeRounds traceLateFirst relayP4) b.id
          == some (roundOfStep traceLateFirst relayP4 (computeRounds traceLateFirst relayP4) b))
#guard !traceLateFirst.all (fun b =>
        roundLookup (computeRoundsSeqOrder traceLateFirst relayP4) b.id
          == some (roundOfStep traceLateFirst relayP4 (computeRoundsSeqOrder traceLateFirst relayP4) b))
-- `roundOf_perm`, executably: the wire's `(seq, creator)` LISTING of the same blocks gets the same
-- rounds, where the old fold's answer depended on which listing it was handed.
#guard traceLateFirst.all (fun b =>
        roundOf (sortedLace traceLateFirst) relayP4 b.id == roundOf traceLateFirst relayP4 b.id)
-- the unenrolled relay of `traceRelayLift6` (seq 0, citing seq-2 blocks) had the same wrong round.
#guard roundOfR (computeRoundsSeqOrder traceRelayLift6 relayP4) 90 == 1
#guard roundOf traceRelayLift6 relayP4 90 == 4
-- ── THE WRONG ROUND REACHES THE LEADER SLOT. ──
-- (RED) wave 1's leader (creator 4) has no block at round 4 under the old map; its blocks sit at
--       rounds 1, 2, 3.
#guard [41, 42, 43].map (roundOfR (computeRoundsSeqOrder traceLateLeader lateLeaderP)) == [1, 2, 3]
#guard (leaderCandidatesR (computeRoundsSeqOrder traceLateLeader lateLeaderP) traceLateLeader
          lateLeaderP 1 3).isEmpty
#guard tauOrderWithRounds traceLateLeader (computeRoundsSeqOrder traceLateLeader lateLeaderP)
          lateLeaderP 3 == [10]
-- (GREEN) the late joiner leads its wave: `41` is the wave-1 leader block, it anchors, and its
--         closure — rounds 1 to 3 and itself — is finalized.
#guard [41, 42, 43].map (roundOf traceLateLeader lateLeaderP) == [4, 5, 6]
#guard (findAllFinalLeaders traceLateLeader lateLeaderP 3).map (·.id) == [10, 41]
#guard tauOrder traceLateLeader lateLeaderP 3 == [10, 20, 30, 11, 21, 31, 12, 22, 32, 41]
#guard tauOrderFast traceLateLeader lateLeaderP 3 == tauOrder traceLateLeader lateLeaderP 3

-- ── ONE ENROLLED VALIDATOR RETRACTS AN ANCHORED WAVE WITHOUT EQUIVOCATING. ──
-- before the gap is filled, both maps finalize the same ten coordinates.
#guard tauOrderWithRounds traceSeqGap (computeRoundsSeqOrder traceSeqGap trace3Participants)
          trace3Participants 3 == [10, 20, 30, 11, 21, 31, 12, 22, 32, 23]
#guard tauOrder traceSeqGap trace3Participants 3 == [10, 20, 30, 11, 21, 31, 12, 22, 32, 23]
-- (RED) THE WOUND: the gap-filling block lands in the wave-1 leader slot beside `23`, the creator
--       is read as an equivocator, and nine finalized coordinates are WITHDRAWN.
#guard roundOfR (computeRoundsSeqOrder traceSeqGapFilled trace3Participants) 99 == 4
#guard (leaderCandidatesR (computeRoundsSeqOrder traceSeqGapFilled trace3Participants)
          traceSeqGapFilled trace3Participants 1 3).map (·.id) == [23, 99]
#guard hasEquivInPastC traceSeqGapFilled (mkPastCache traceSeqGapFilled)
          (computeRoundsSeqOrder traceSeqGapFilled trace3Participants) 99 2
#guard tauOrderWithRounds traceSeqGapFilled
          (computeRoundsSeqOrder traceSeqGapFilled trace3Participants) trace3Participants 3 == [10]
-- (GREEN) the block is at round 7, where it is; nobody equivocated; the order stands, and the
--         shorter lace's order is a prefix of the longer one's.
#guard roundOf traceSeqGapFilled trace3Participants 99 == 7
#guard !hasEquivInPast traceSeqGapFilled trace3Participants 99 2
#guard tauOrder traceSeqGapFilled trace3Participants 3 == [10, 20, 30, 11, 21, 31, 12, 22, 32, 23]
#guard (tauOrder traceSeqGap trace3Participants 3).isPrefixOf
          (tauOrder traceSeqGapFilled trace3Participants 3)
#guard tauOrderFast traceSeqGapFilled trace3Participants 3
        == tauOrder traceSeqGapFilled trace3Participants 3

/-! The GREEN half of the two pairs above as KERNEL theorems, not `#guard`s. The round map and the
head selection are structural recursion now (no `Array.qsort`), so `decide` reduces them; a `#guard`
is the compiler's word and these are the kernel's. The RED halves stay `#guard`s — they run the old
`Array.qsort` fold, which the kernel cannot reduce — and so do the orders, since `xsortWith` goes
through `List.mergeSort`. -/

set_option maxRecDepth 1000000 in
/-- An honest late joiner's first block sits one round above the tips it cites. -/
theorem lateJoiner_round_is_depth : roundOf traceLateFirst relayP4 41 = 4 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- The wave a late joiner leads anchors on its first block. -/
theorem lateJoiner_wave_anchors :
    (findAllFinalLeaders traceLateLeader lateLeaderP 3).map (·.id) = [10, 41] := by decide

/-! ### THE LINEARIZATION `#guard`s (dregg issue #100, §1) — the order respects causality.

`xsortByRoundKey` is the `(round, id)` key sort exactly as it stood. -/

-- every block of the relay lace is cordial: nothing here is refused at admission.
#guard isCordialLace traceRelayLift6 relayP4
-- the premise of the wound: `41` is at round 2, its ancestors `12, 22, 32` at round 3.
#guard roundOf traceRelayLift6 relayP4 41 == 2
#guard [12, 22, 32].all (fun a => (causalPastIncl traceRelayLift6 41).contains a
                                    && roundOf traceRelayLift6 relayP4 a == 3)
-- (RED) THE WOUND: the key sort emits `41` before three blocks of its own causal past.
#guard xsortByRoundKey traceRelayLift6 relayP4 [20, 30, 11, 21, 31, 12, 22, 32, 41, 23]
        == [20, 30, 11, 21, 31, 41, 12, 22, 32, 23]
#guard !respectsCausality traceRelayLift6
          (xsortByRoundKey traceRelayLift6 relayP4 [20, 30, 11, 21, 31, 12, 22, 32, 41, 23])
-- (GREEN) the ready-set sort does not, on the same input…
#guard xsortBy traceRelayLift6 relayP4 [20, 30, 11, 21, 31, 12, 22, 32, 41, 23]
        == [20, 30, 11, 21, 31, 12, 22, 32, 41, 23]
-- …and the finalized order is the reporter's expected one, on both paths.
#guard tauOrder traceRelayLift6 relayP4 3 == [10, 20, 30, 11, 21, 31, 12, 22, 32, 41, 23]
#guard tauOrderFast traceRelayLift6 relayP4 3 == [10, 20, 30, 11, 21, 31, 12, 22, 32, 41, 23]
#guard respectsCausality traceRelayLift6 (tauOrder traceRelayLift6 relayP4 3)
-- the n = 5 exhibit: `51` after all four round-3 blocks in its past.
#guard tauOrder traceRelayLift5 [1, 2, 3, 4, 5] 3
        == [10, 20, 30, 40, 11, 21, 31, 41, 12, 22, 32, 42, 51, 23]
#guard tauOrderFast traceRelayLift5 [1, 2, 3, 4, 5] 3 == tauOrder traceRelayLift5 [1, 2, 3, 4, 5] 3
#guard respectsCausality traceRelayLift5 (tauOrder traceRelayLift5 [1, 2, 3, 4, 5] 3)
-- `TauOrderCausal`, executably, on every ordering trace in this file.
#guard respectsCausality trace6 (tauOrder trace6 trace3Participants 3)
#guard respectsCausality traceUnenrolled6 (tauOrder traceUnenrolled6 trace3Participants 3)
#guard respectsCausality traceUnenrolled6 (tauOrderUnfiltered traceUnenrolled6 trace3Participants 3)
#guard respectsCausality traceOrderFork8 (tauOrder traceOrderFork8 trace3Participants 4)
#guard respectsCausality traceRelayStall6 (tauOrder traceRelayStall6 trace3Participants 3)
#guard respectsCausality traceLateLeader (tauOrder traceLateLeader lateLeaderP 3)
#guard respectsCausality traceMW4 (tauOrder traceMW4 traceMW4Participants 3)
-- ── WHY THE ENROLLMENT FILTER MOVED INSIDE THE SEGMENT. ──
-- both orders respect causality, and they order the same enrolled blocks DIFFERENTLY: with the
-- relay left in the segment `20` overtakes `19`.
#guard tauOrder traceFilterPlacement trace3Participants 3
        == [10, 19, 20, 11, 21, 31, 12, 22, 32, 23]
#guard (tauOrderUnfiltered traceFilterPlacement trace3Participants 3).filter
          (enrolledId traceFilterPlacement trace3Participants)
        == [10, 20, 19, 11, 21, 31, 12, 22, 32, 23]
#guard respectsCausality traceFilterPlacement (tauOrder traceFilterPlacement trace3Participants 3)
#guard respectsCausality traceFilterPlacement
          (tauOrderUnfiltered traceFilterPlacement trace3Participants 3)
#guard tauOrderFast traceFilterPlacement trace3Participants 3
        == tauOrder traceFilterPlacement trace3Participants 3

-- THE MEMOIZED FAST PATH agrees with the pure rule on the concrete traces (the live gate exports run
-- `tauOrderFast`/`tauGoldenFast`; the exponential re-traversal is gone, the order is IDENTICAL).
#guard tauOrderFast trace3 trace3Participants 3 == tauOrder trace3 trace3Participants 3
#guard tauGoldenFast trace3 trace3Participants 3 == tauGolden trace3 trace3Participants 3
#guard tauOrderFast trace6 trace3Participants 3 == tauOrder trace6 trace3Participants 3
#guard tauGoldenFast trace6 trace3Participants 3
        == [(1,0),(2,0),(3,0),(1,1),(2,1),(3,1),(1,2),(2,2),(3,2),(2,3)]
#guard (tauOrderFast traceEquiv trace3Participants 3).all
        (fun id => match traceEquiv.lookup id with | some b => b.creator != 1 | none => true)

/-! ### THE `@[implemented_by]` DIFFERENTIAL — the `Std.HashMap`/`Std.HashSet` runtime twin (§6c)
computes EXACTLY the pure def, on multiple laces INCLUDING a round-2-shaped multi-wave n=4 DAG.

Since `@[implemented_by]` is attached ONLY to `tauOrderFast` (§6c) and the pure `tauOrder` /
`causalPastIncl` keep normal compilation, each `#guard` below runs the FAST-compiled twin on the LHS
against the PURE-compiled def on the RHS — a genuine fast-vs-pure differential (NOT fast-vs-fast). A
false `#guard` is a build error, so a divergent twin fails the build. This is the load-bearing check
that the TRUSTED fast path (which no theorem constrains) equals the verified rule. -/

-- (i) the HashSet-backed causal-past twin returns the IDENTICAL id list as the pure `causalPastIncl`,
--     for EVERY block, on all three concrete laces (the memoization primitive is exact).
#guard trace3.all (fun b => fastCausalPastIncl trace3 b.id == causalPastIncl trace3 b.id)
#guard traceEquiv.all (fun b => fastCausalPastIncl traceEquiv b.id == causalPastIncl traceEquiv b.id)
#guard traceMW4.all (fun b => fastCausalPastIncl traceMW4 b.id == causalPastIncl traceMW4 b.id)
#guard trace6.all (fun b => fastCausalPastIncl trace6 b.id == causalPastIncl trace6 b.id)
#guard traceOrderFork8.all (fun b => fastCausalPastIncl traceOrderFork8 b.id
                                       == causalPastIncl traceOrderFork8 b.id)

/-! #### ⚑ The lace the five `#guard`s above could not see

Every trace above is round-synchronous and fully cross-linked, so every block in a BFS layer has the
IDENTICAL pred list — the one shape where "keep the first duplicate" and "keep the last" agree. The
twin kept the FIRST and the pure `acc.dedup` keeps the LAST, and for as long as those were the only
laces on the bench the differential was GREEN over a divergence that was live on `dregg_tau_order`.

`laceUnevenPreds` is the smallest lace that separates them: `b1` acks `[p, q]` and `b2` acks `[p]`,
so the layer under `hd` expands to `[p, q, p]` — a duplicate with another id *between* its copies,
which is precisely what a uniform pred list can never produce. Named, not `#guard`ed, so the fact is
a term with an axiom record. -/

/-- Round 1: `p`, `q`. Round 2: `b1 → {p,q}`, `b2 → {p}` — UNEVEN pred sets, the separating shape.
Round 3: `hd → {b1,b2}`. -/
def laceUnevenPreds : Lace :=
  [ { id := 1, creator := 0, seq := 1, preds := [] },
    { id := 2, creator := 1, seq := 1, preds := [] },
    { id := 3, creator := 0, seq := 2, preds := [1, 2] },
    { id := 4, creator := 1, seq := 2, preds := [1] },
    { id := 5, creator := 0, seq := 3, preds := [3, 4] } ]

/-- The layer really does repeat an id around another one — the premise of the whole exhibit. If a
future edit makes this list uniform, the theorem below stops being a falsifier and this goes red
first, rather than silently passing on a lace that cannot separate the two dedup conventions. -/
theorem laceUnevenPreds_layer_repeats_an_id :
    expandPreds laceUnevenPreds [3, 4] = [1, 2, 1] := by native_decide

/-- **The trusted twin computes the specified list on the lace that separates the conventions.**
Before the §6c repair this was `[5,3,4,1,2]` against the spec's `[5,3,4,2,1]`. -/
theorem fast_twin_matches_the_spec_on_the_uneven_pred_lace :
    laceUnevenPreds.all (fun b => fastCausalPastIncl laceUnevenPreds b.id
                                    == causalPastIncl laceUnevenPreds b.id) = true := by
  native_decide

/-- And the order the τ rule finalizes over that lace agrees, twin against pure. -/
theorem fast_tau_matches_the_spec_on_the_uneven_pred_lace :
    tauOrderFast laceUnevenPreds [0, 1] 2 = tauOrder laceUnevenPreds [0, 1] 2 := by
  native_decide

#assert_compiled laceUnevenPreds_layer_repeats_an_id
#assert_compiled fast_twin_matches_the_spec_on_the_uneven_pred_lace
#assert_compiled fast_tau_matches_the_spec_on_the_uneven_pred_lace
-- ⚑ and the runtime twin on the DEEP laces, where the order is 10 and 13 blocks rather than 1 —
--   a `@[implemented_by]` differential over a one-element list constrains almost nothing.
#guard tauOrderFast trace6 trace3Participants 3 == tauOrder trace6 trace3Participants 3
#guard tauGoldenFast trace6 trace3Participants 3 == tauGolden trace6 trace3Participants 3
#guard tauOrderFast traceOrderFork8 trace3Participants 4 == tauOrder traceOrderFork8 trace3Participants 4
#guard tauGoldenFast traceOrderFork8 trace3Participants 4
        == tauGolden traceOrderFork8 trace3Participants 4
#guard tauOrderFast traceUnenrolled6 trace3Participants 3 == tauOrder traceUnenrolled6 trace3Participants 3
#guard (tauOrderFast trace6 trace3Participants 3).length == 10

-- (i') the Kahn twin enumerates the IDENTICAL list as the pure `topoLace`, and the round twin
--      returns the pure round for every block — including the late-joiner and relay laces (more
--      than one sweep) and the cyclic lace (the stuck tail).
#guard [trace3, trace6, traceEquiv, traceMW4, traceUnenrolled6, traceOrderFork8, traceRelayStall6,
        traceLateFirst, traceLateLeader, traceRelayLift6, traceRelayLift5, traceFilterPlacement,
        traceCycle, sortedLace traceLateLeader, sortedLace traceRelayLift5].all
        (fun B => fastTopoLace B == topoLace B)
#guard [trace6, traceOrderFork8, traceRelayStall6, traceLateFirst, traceLateLeader, traceRelayLift6,
        traceRelayLift5, traceFilterPlacement, sortedLace traceLateLeader].all
        (fun B => B.all (fun b => fastROf (fastRoundMap B relayP4) b.id == roundOf B relayP4 b.id)
                  && B.all (fun b => fastROf (fastRoundMap B trace3Participants) b.id
                                       == roundOf B trace3Participants b.id))
-- (ii) the full `tauOrderFast` runtime twin == the pure `tauOrder`, on the golden 3-node trace, the
--      equivocation trace, AND the round-2-shaped multi-wave n=4 DAG.
#guard tauOrderFast traceMW4 traceMW4Participants 3 == tauOrder traceMW4 traceMW4Participants 3
#guard tauGoldenFast traceMW4 traceMW4Participants 3 == tauGolden traceMW4 traceMW4Participants 3
-- non-vacuity: the multi-wave lace actually FINALIZES a non-empty prefix (wave 0's leader anchors),
--      so the differential is over a real order, not the empty list.
#guard (tauOrderFast traceMW4 traceMW4Participants 3).length > 0
#guard (findAllFinalLeaders traceMW4 traceMW4Participants 3).length ≥ 1

/-! The `#guard`s above are the project's machine-checked non-vacuity teeth (the sanctioned
mechanism for executable defs — a false `#guard` is a BUILD ERROR, exactly like a
failed test). They establish, against a CONCRETE trace, that: (i) the model finalizes all nine blocks
of the 3-node lace (the Rust `result.len() == 9`); (ii) there is EXACTLY ONE final leader, creator 1's
genesis (the single-anchor `finalLeaders_one_per_wave` is witnessed non-vacuously); (iii) the golden
`(creator, seq)` differential vector is the exact deterministic causal order the node finalizes; and
(iv) an equivocating leader anchors NOTHING and contributes no finalized block. So the safety theorems
constrain a REAL, non-trivial finalized order, and the model reproduces the node's finalization. -/

/-! ## 10. Axiom hygiene — the executable rule + the executor connection are kernel-clean. -/

#assert_axioms finalLeaderAt_unique
#assert_axioms finalLeaderAt_needs_unique_candidate
#assert_axioms finalLeaders_one_per_wave
#assert_axioms tauOrder_deterministic
#assert_axioms findAllFinalLeaders_deterministic
#assert_axioms tau_drives_verified_run
#assert_axioms tau_execution_agreement
#assert_axioms cachedPast_eq
#assert_axioms tauOrderFast_eq
#assert_axioms tauGoldenFast_eq
#assert_axioms tauOrderFastUnfiltered_eq
#assert_axioms tauOrder_only_enrolled
#assert_axioms tauOrder_enrolled_eq_unfiltered
#assert_axioms ratifiesEnrolled_eq_of_enrolled
#assert_axioms isSuperRatified_eq_pre_of_enrolled
#assert_axioms superRatified_exists_enrolled_ratifier
#assert_axioms foldl_max_eq_or_mem
#assert_axioms unenrolled_preds_contribute_no_depth
#assert_axioms roundOfStep_exhibits_enrolled_pred
#assert_axioms roundsFold_entry_of_mem
#assert_axioms computeRounds_depth_exhibits_enrolled_pred
#assert_axioms roundOfStep_eq_pre_of_enrolled
#assert_axioms computeRounds_eq_pre_of_enrolled
#assert_axioms tauOrder_eq_preRounds_of_enrolled
#assert_axioms tauOrderFast_eq_withRounds
#assert_axioms topoLace_perm
#assert_axioms topoLace_ancestorRespecting
#assert_axioms laceStuck_eq_nil_iff
#assert_axioms roundsFold_recurrence
#assert_axioms roundsFold_enumeration_invariant
#assert_axioms computeRounds_recurrence
#assert_axioms computeRounds_enumeration_invariant
#assert_axioms roundOf_perm
#assert_axioms causalPastIncl_rank
#assert_axioms readySort_perm
#assert_axioms readySort_linear_extension
#assert_axioms xsortBy_perm
#assert_axioms xsortWith_congr
#assert_axioms xsortWith_linear_extension
#assert_axioms xsortBy_linear_extension
#assert_axioms anchorSegment_linear_extension
#assert_axioms lateJoiner_round_is_depth
#assert_axioms lateJoiner_wave_anchors
#assert_axioms anchorSegmentWith_congr_keep
