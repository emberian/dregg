/-
# Dregg2.Consensus.TauPrefixMonotone — T5: finalized-prefix monotonicity for `tauOrder`,
# with two of its three former hypotheses DISCHARGED and the third named as the paper's theorem.

**The claim (CM Prop. 9).** *Let B be a cordial blocklace with a supermajority of correct miners.
Then τ is monotonic wrt the superset relation among closed subsets of B, namely for any two closed
blocklaces B₂ ⊆ B₁ ⊆ B, τ(B₂) ⪯ τ(B₁).* The live node relies on it: `ExecutionCursor` caches the
finalized prefix, which CM §5 p.9 explicitly authorises **because of Prop. 9** — *"a sequence up to
a super-ratified leader is final (Prop. 9) and hence can be cached"*.

## What this module used to say, and why it changed

It carried `FinalizedRegionStable`, a THREE-field hypothesis, and a counterexample —
`lagBase → lagGrown`, four validators with one merely LAGGING, no Byzantine step, every block
passing the verified `insert` — refuting the unconditional claim:

```
  tauOrder lagBase   = [10,20,30,40,11,21,31,12,22,32]
  tauOrder lagGrown  = [10,20,30,40,11,21,31,41,12,22,32,42]     -- 41 lands at index 7
```

That counterexample was not a fact about Cordial Miners. It was a fact about a τ that had **deviated
from CM Def. 6**: a wave's segment was its leader's *coverage* — the union of the causal pasts of
every wave-END block **in the live lace** that ratified it — and coverage grows with arrivals. CM's
τ orders the anchor's OWN closure `[b₁] \ [b₂]` (Alg. 2:37), a set fixed forever by `b₁`'s signed
hash pointers, and folds over the ratified-leader chain reachable from ONE head (Alg. 2:41-46),
never over a leader list recomputed from the live lace.

`Distributed.BlocklaceFinality` §5b/§6 is now that rule. **On the same trace, with the same
validator lagging the same way, `tauOrder lagBase = tauOrder lagGrown = [10]`** — the growth adds
nothing to the anchor's closure because it cannot, and the §4 guards below pin it. The
counterexample is retained, inverted: it is now the module's positive exhibit that an
insert-valid honest laggard can no longer reorder finalized history.

## What is proved here, and what is still assumed

`FinalizedRegionStable`'s three fields, against CM:

| former field | what it said | status now |
|---|---|---|
| `fold_agrees` | replaying the old anchors in the grown lace reproduces the same segments | **THEOREM** (`tauStep_stable`), from `ClosedExtension` alone |
| `enrollment_agrees` | the growth does not reclassify an already-ordered block's creator | **THEOREM**: the creator filter sits inside the segment and reads the anchor's closure, so it is part of `anchorSegment_stable`; `enrolledId_stable` is the same fact for the whole-lace predicate |
| `leaders_extend` | the anchor list only extends | **SURVIVES**, as `ChainExtends` — see below |

`ClosedExtension` is not a restatement of the conclusion. It is three STRUCTURAL facts about the
growth — the lace is extended, block ids are unique, and every predecessor of a held block is held —
and the third is exactly CM Def. 19's *closed*, which CM Alg. 3:49 establishes by BUFFERING
(*"Received 'out of order' blocks are buffered"*) and which `node/src/catchup.rs::apply_with_buffering`
already implements. Nothing here is a runtime stability check over two whole laces; the old
`stableCheck`, which nothing ever called, is deleted.

**The surviving hypothesis, named honestly.** `ChainExtends` says the old head appears in the new
head's ratified-leader chain, so the chains extend. That is precisely CM Prop. 9's central argument,
and CM DERIVES it: Prop. 3 (*a cordial blocklace is leader-safe*) gives that every final leader is
ratified by every subsequent leader, from **cordiality alone** — a per-block admission predicate
(CM Def. 25, Alg. 1:15-16), which `Distributed.BlocklaceFinality` §5c now **defines**.

⚠ Defines, and nothing more: `isCordialBlock` carries no `@[export]`, and NOTHING on the receive
path evaluates it — `insert_checked` still never looks at the cardinality of a block's pointer set.
So cordiality is available as a predicate, not established as a fact, and the derivation below is
not yet open to us even in principle. §5c's own debt block says the same; this paragraph exists so
the two cannot drift apart. Three gaps stand between here and a Lean proof of `ChainExtends`:

0. **The premise is not enforced.** Wiring `isCordialBlock` into the receive path needs an FFI
   export and a refusal policy — unlike a missing predecessor, a cordiality failure is not fixable
   by waiting, so it cannot simply be buffered.

1. **Prop. 3 itself is not formalised.** Its proof is quorum intersection over the DAG (App. C, two
   cases on the relative depth of the ratifying supermajority) and it is a real formalisation, not a
   rewrite. It is the next piece of work, not a side condition.
2. **Our `finalLeaderAt` is not monotone, and CM's `final_leader` is.** CM Alg. 2:48 evaluates
   `super-ratifies` over a depth-bounded prefix that only grows, so finality only ever turns ON;
   ours returns `none` unless the leader slot holds EXACTLY ONE block, so a late second leader-slot
   block by an equivocating leader RETRACTS an already-anchored wave and can move the head
   backwards. CM handles that case by approval instead (§4.2 + Lem. 31: at most one of an
   equivocating pair can hold supermajority approval). Until that is changed, `ChainExtends` also
   absorbs head-monotonicity, and a live equivocating leader can still shorten τ.

So the honest summary is: **the arrival-dependence is gone and proved gone; the leader-safety half
is imported from the paper and owed a Lean proof.** That is a different position from assuming the
conclusion, which is where this module was.

Non-vacuity (the sanctioned `#guard` teeth for these executable defs; `native_decide` is banned):
  * §4 — the FORMER counterexample, now a positive: insert-valid, equivocation-free, and the old
    order IS a prefix of the new one, with the mechanism pinned (the anchor's closure did not move).
  * §5 — a real growth that orders strictly more (`trace3 → trace6`, 1 → 10 blocks), so the
    conclusion is non-trivial rather than a prefix of nothing.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Consensus.TauPrefixMonotone`.
-/
import Dregg2.Distributed.BlocklaceFinality

namespace Dregg2.Consensus.TauPrefixMonotone

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)
open Dregg2.Distributed.BlocklaceFinality

/-! ## 1. The growth hypothesis — STRUCTURAL, and established at admission.

`ClosedExtension B B'` is what a node's receive path already guarantees, stated as three facts
about the pair rather than as a property of the finalized order:

* `grown` — `B'` extends `B` (the blocklace is a grow-only set; `World.recv_mono`);
* `ids_nodup` — block ids are unique, i.e. content addressing (`Lace.Canonical`'s list form);
* `pred_closed` — every predecessor of a held block is held. **CM Def. 19 *closed*.** CM Alg. 3:49
  makes it a precondition of receipt and buffers what fails it; `blocklace/src/finality.rs::
  insert_checked` returns `MissingPredecessor` and `node/src/catchup.rs::apply_with_buffering`
  parks the block in the `OrphanBuffer` until it holds.

Note what is NOT here: nothing about waves, nothing about arrival timing, nothing comparing two τ
folds. The whole arrival-independence result comes out of `pred_closed`. -/

/-- The growth `B → B'` is a CLOSED EXTENSION (CM Def. 19). -/
structure ClosedExtension (B B' : Lace) : Prop where
  grown : ∃ new : Lace, B' = B ++ new
  ids_nodup : (B'.map (·.id)).Nodup
  pred_closed : ∀ b ∈ B, ∀ p ∈ b.preds, B.has p = true

/-! ## 2. Lookup, membership and the causal past are stable under a closed extension. -/

/-- A block id that resolves in `B` resolves to the SAME block in `B'`: `Lace.lookup` is
`List.find?`, which commits to the first hit, and `B` is the prefix. -/
theorem lookup_stable {B B' : Lace} (h : ClosedExtension B B') {bid : BlockId}
    (hb : B.has bid = true) : B'.lookup bid = B.lookup bid := by
  obtain ⟨new, rfl⟩ := h.grown
  unfold Lace.has Lace.lookup at *
  cases hf : B.find? (fun b => b.id = bid) with
  | none => rw [hf] at hb; simp at hb
  | some x => simp [List.find?_append, hf]

/-- Membership is stable for ids already held. -/
theorem has_stable {B B' : Lace} (h : ClosedExtension B B') {bid : BlockId}
    (hb : B.has bid = true) : B'.has bid = true := by
  unfold Lace.has at *; rw [lookup_stable h hb]; exact hb

/-- Everything `expandPreds` produces is held by the lace (it filters on exactly that). -/
theorem expandPreds_has (B : Lace) (fr : List BlockId) :
    ∀ x ∈ expandPreds B fr, B.has x = true := by
  intro x hx
  unfold expandPreds at hx
  obtain ⟨h, _, hmem⟩ := List.mem_flatMap.mp hx
  cases hl : B.lookup h with
  | none => rw [hl] at hmem; simp at hmem
  | some b =>
    rw [hl] at hmem
    exact (List.mem_filter.mp hmem).2

/-- **`expandPreds_stable`** — one BFS layer is the same in `B` and `B'`. This is where
`pred_closed` earns its place: without it a dangling pointer in `B` could RESOLVE in `B'` and the
layer would grow. -/
theorem expandPreds_stable {B B' : Lace} (h : ClosedExtension B B') :
    ∀ (fr : List BlockId), (∀ x ∈ fr, B.has x = true) →
      expandPreds B' fr = expandPreds B fr := by
  intro fr hfr
  unfold expandPreds
  induction fr with
  | nil => rfl
  | cons a rest ih =>
    have ha : B.has a = true := hfr a (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, B.has x = true := fun x hx => hfr x (List.mem_cons_of_mem _ hx)
    simp only [List.flatMap_cons]
    rw [ih hrest, lookup_stable h ha]
    cases hl : B.lookup a with
    | none => rfl
    | some b =>
      have hbB : b ∈ B := List.mem_of_find?_eq_some (by simpa [Lace.lookup] using hl)
      have hall : ∀ p ∈ b.preds, B.has p = true := h.pred_closed b hbB
      have : b.preds.filter (fun p => B'.has p) = b.preds.filter (fun p => B.has p) := by
        apply List.filter_congr
        intro p hp
        rw [hall p hp, has_stable h (hall p hp)]
      simp [this]

/-- **`causalPastAux_stable`** — the whole BFS agrees at the SAME fuel, given the frontier is held
by `B`. Induction over the fuel, one `expandPreds_stable` per layer. -/
theorem causalPastAux_stable {B B' : Lace} (h : ClosedExtension B B') :
    ∀ (f : Nat) (fr acc : List BlockId), (∀ x ∈ fr, B.has x = true) →
      causalPastAux B' f fr acc = causalPastAux B f fr acc := by
  intro f
  induction f with
  | zero => intro fr acc _; cases fr <;> rfl
  | succ f ih =>
    intro fr acc hfr
    cases fr with
    | nil => rfl
    | cons a rest =>
      show causalPastAux B' f _ _ = causalPastAux B f _ _
      rw [expandPreds_stable h (a :: rest) hfr]
      exact ih _ _ (fun x hx => expandPreds_has B (a :: rest) x
        (List.mem_filter.mp hx).1)

/-! ### The fuel gap — the one piece of real counting.

`causalPastIncl B h` runs the BFS with fuel `B.length`, and `causalPastIncl B' h` with fuel
`B'.length`. So same-fuel agreement is not enough: the extra fuel must be a no-op. It is, and the
reason is a pigeonhole — each surviving layer adds at least one NEW id, every id comes from `B`, and
ids are unique — but Lean has to be told. -/

/-- Once no unvisited predecessor remains, the BFS is done and further fuel changes nothing. -/
theorem causalPastAux_stop (B : Lace) :
    ∀ (f : Nat) (fr acc : List BlockId),
      (expandPreds B fr).filter (fun p => ¬ acc.contains p) = [] →
      causalPastAux B f fr acc = acc.dedup := by
  intro f fr acc hnx
  cases f with
  | zero => cases fr <;> rfl
  | succ f =>
    cases fr with
    | nil => rfl
    | cons a rest =>
      show causalPastAux B f _ _ = acc.dedup
      rw [hnx]
      cases f <;> simp [causalPastAux]

/-- A nodup list contained in a nodup list of no greater length covers it. Pigeonhole, via
`List.Nodup.subperm`. -/
theorem covers_of_length {α : Type} [DecidableEq α] {l m : List α}
    (hl : l.Nodup) (hs : l ⊆ m) (hlen : m.length ≤ l.length) : ∀ x ∈ m, x ∈ l := by
  obtain ⟨u, hu, hsub⟩ := hl.subperm hs
  have hul : u.length = l.length := hu.length_eq
  have hum : u.length ≤ m.length := hsub.length_le
  have : u = m := hsub.eq_of_length (by omega)
  intro x hx
  exact hu.mem_iff.mp (this ▸ hx)

/-- Appending a nonempty list of ids none of which is already present strictly grows the deduped
length. The measure that makes the pigeonhole above bite. -/
theorem dedup_length_grows {α : Type} [DecidableEq α] (acc nxt : List α)
    (hne : nxt ≠ []) (hdisj : ∀ x ∈ nxt, x ∉ acc) :
    acc.dedup.length + 1 ≤ (acc ++ nxt).dedup.length := by
  cases nxt with
  | nil => exact absurd rfl hne
  | cons x xs =>
    have hxacc : x ∉ acc := hdisj x (List.mem_cons_self ..)
    have hxd : x ∉ acc.dedup := fun hc => hxacc (List.mem_dedup.mp hc)
    have hnd : (x :: acc.dedup).Nodup := List.nodup_cons.mpr ⟨hxd, acc.nodup_dedup⟩
    have hsub : (x :: acc.dedup) ⊆ (acc ++ (x :: xs)).dedup := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact List.mem_dedup.mpr (List.mem_append_right _ (List.mem_cons_self ..))
      · exact List.mem_dedup.mpr (List.mem_append_left _ (List.mem_dedup.mp hy'))
    have := (hnd.subperm hsub).length_le
    simpa using this

/-- **`causalPastAux_fuel_step`** — with enough fuel already spent, one more unit changes nothing. -/
theorem causalPastAux_fuel_step {B : Lace} (hnd : (B.map (·.id)).Nodup) :
    ∀ (f : Nat) (fr acc : List BlockId),
      (∀ x ∈ acc, B.has x = true) → B.length ≤ acc.dedup.length + f →
      causalPastAux B f fr acc = causalPastAux B (f + 1) fr acc := by
  intro f
  induction f with
  | zero =>
    intro fr acc hacc hlen
    -- fuel exhausted AND the accumulator already covers `B`, so no layer can survive.
    have haccIds : acc.dedup ⊆ B.map (·.id) := by
      intro x hx
      have hxa : x ∈ acc := List.mem_dedup.mp hx
      have := hacc x hxa
      unfold Lace.has Lace.lookup at this
      cases hf : B.find? (fun b => b.id = x) with
      | none => rw [hf] at this; simp at this
      | some b =>
        have hbB : b ∈ B := List.mem_of_find?_eq_some hf
        have : b.id = x := by
          have := List.find?_some hf; simpa using this
        exact this ▸ List.mem_map_of_mem hbB
    have hcov : ∀ x ∈ B.map (·.id), x ∈ acc.dedup :=
      covers_of_length acc.nodup_dedup haccIds (by simpa using hlen)
    have hnx : (expandPreds B fr).filter (fun p => ¬ acc.contains p) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hxB : B.has x = true := expandPreds_has B fr x hx
      have : x ∈ B.map (·.id) := by
        unfold Lace.has Lace.lookup at hxB
        cases hf : B.find? (fun b => b.id = x) with
        | none => rw [hf] at hxB; simp at hxB
        | some b =>
          have hbB : b ∈ B := List.mem_of_find?_eq_some hf
          have hbx : b.id = x := by have := List.find?_some hf; simpa using this
          exact hbx ▸ List.mem_map_of_mem hbB
      have : x ∈ acc := List.mem_dedup.mp (hcov x this)
      simp [List.contains_iff_mem, this]
    rw [causalPastAux_stop B 0 fr acc hnx, causalPastAux_stop B 1 fr acc hnx]
  | succ f ih =>
    intro fr acc hacc hlen
    cases fr with
    | nil => rfl
    | cons a rest =>
      set nxt := (expandPreds B (a :: rest)).filter (fun p => ¬ acc.contains p) with hnxt
      show causalPastAux B f nxt (acc ++ nxt) = causalPastAux B (f + 1) nxt (acc ++ nxt)
      by_cases hemp : nxt = []
      · rw [hemp]
        cases f <;> simp [causalPastAux]
      · have hdisj : ∀ x ∈ nxt, x ∉ acc := by
          intro x hx
          have := (List.mem_filter.mp (hnxt ▸ hx)).2
          simpa [List.contains_iff_mem] using this
        have hgrow := dedup_length_grows acc nxt hemp hdisj
        refine ih nxt (acc ++ nxt) ?_ (by omega)
        intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact hacc x h1
        · exact expandPreds_has B (a :: rest) x (List.mem_filter.mp (hnxt ▸ h2)).1

/-- **`causalPastAux_fuel_irrelevant`** — any extra fuel above the saturation point is a no-op. -/
theorem causalPastAux_fuel_irrelevant {B : Lace} (hnd : (B.map (·.id)).Nodup) :
    ∀ (k f : Nat) (fr acc : List BlockId),
      (∀ x ∈ acc, B.has x = true) → B.length ≤ acc.dedup.length + f →
      causalPastAux B f fr acc = causalPastAux B (f + k) fr acc := by
  intro k
  induction k with
  | zero => intro f fr acc _ _; rfl
  | succ k ih =>
    intro f fr acc hacc hlen
    have hstep := causalPastAux_fuel_step hnd (f + k) fr acc hacc (by omega)
    have harith : f + (k + 1) = (f + k) + 1 := by omega
    rw [ih f fr acc hacc hlen, harith, hstep]

/-- Everything in an inclusive causal past rooted at a held id is itself held. -/
theorem causalPastAux_has (B : Lace) :
    ∀ (f : Nat) (fr acc : List BlockId), (∀ x ∈ acc, B.has x = true) →
      ∀ x ∈ causalPastAux B f fr acc, B.has x = true := by
  intro f
  induction f with
  | zero => intro fr acc hacc x hx; cases fr <;> exact hacc x (List.mem_dedup.mp hx)
  | succ f ih =>
    intro fr acc hacc x hx
    cases fr with
    | nil => exact hacc x (List.mem_dedup.mp hx)
    | cons a rest =>
      refine ih _ _ ?_ x hx
      intro y hy
      rcases List.mem_append.mp hy with h1 | h2
      · exact hacc y h1
      · exact expandPreds_has B (a :: rest) y (List.mem_filter.mp h2).1

theorem causalPastIncl_has (B : Lace) {bid : BlockId} (hb : B.has bid = true) :
    ∀ x ∈ causalPastIncl B bid, B.has x = true := by
  -- `causalPastIncl` runs the frontier-deduped BFS; `causalPastIncl_eq_spec` is the proof that it
  -- returns the spec's list, so every lemma stated about `causalPastAux` still applies verbatim.
  rw [causalPastIncl_eq_spec]
  exact causalPastAux_has B B.length [bid] [bid]
    (by intro x hx; simpa [List.mem_singleton.mp hx] using hb)

/-- **`causalPastIncl_stable` — THE LEMMA THE WHOLE RESULT RESTS ON.** For a closed extension, the
inclusive causal past of a held block is EXACTLY the same list. CM Def. 19's `[b]` cannot move,
because `b`'s pointers are signed and the lace holds everything they reach. -/
theorem causalPastIncl_stable {B B' : Lace} (h : ClosedExtension B B') {bid : BlockId}
    (hb : B.has bid = true) : causalPastIncl B' bid = causalPastIncl B bid := by
  obtain ⟨new, hnew⟩ := h.grown
  have hlen : B'.length = B.length + new.length := by rw [hnew]; simp
  have hndB : (B.map (·.id)).Nodup := by
    have := h.ids_nodup
    rw [hnew] at this
    simpa using (List.nodup_append.mp (by simpa using this)).1
  have hacc : ∀ x ∈ ([bid] : List BlockId), B.has x = true := by
    intro x hx; simpa [List.mem_singleton.mp hx] using hb
  have hd1 : ([bid] : List BlockId).dedup = [bid] := by simp
  have hbound : B.length ≤ ([bid] : List BlockId).dedup.length + B.length := by
    rw [hd1]; omega
  rw [causalPastIncl_eq_spec, causalPastIncl_eq_spec,
      causalPastAux_stable h B'.length [bid] [bid] hacc, hlen]
  exact (causalPastAux_fuel_irrelevant hndB new.length B.length [bid] [bid] hacc hbound).symm

/-- **`closureLace_stable`** — CM's `[b]` AS A LACE does not move either. The new blocks are
filtered out because their ids are fresh (`ids_nodup`) and the closure only holds ids of `B`. -/
theorem closureLace_stable {B B' : Lace} (h : ClosedExtension B B') {bid : BlockId}
    (hb : B.has bid = true) : closureLace B' bid = closureLace B bid := by
  obtain ⟨new, hnew⟩ := h.grown
  have hpast := causalPastIncl_stable h hb
  unfold closureLace
  rw [hpast, hnew, List.filter_append]
  have hnil : new.filter (fun b => (causalPastIncl B bid).contains b.id) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro b hbnew hcontra
    have hmem : b.id ∈ causalPastIncl B bid := by
      simpa [List.contains_iff_mem] using hcontra
    have hInB : B.has b.id = true := causalPastIncl_has B hb b.id hmem
    -- but `b.id` is an id of `new`, and the two id lists are disjoint by `ids_nodup`.
    have happ : ((B.map (·.id)) ++ (new.map (·.id))).Nodup := by
      have := h.ids_nodup; rw [hnew] at this; simpa using this
    have hne := (List.nodup_append.mp happ).2.2
    have hxB : b.id ∈ B.map (·.id) := by
      unfold Lace.has Lace.lookup at hInB
      cases hf : B.find? (fun x => x.id = b.id) with
      | none => rw [hf] at hInB; simp at hInB
      | some c =>
        have hcB : c ∈ B := List.mem_of_find?_eq_some hf
        have : c.id = b.id := by have := List.find?_some hf; simpa using this
        exact this ▸ List.mem_map_of_mem hcB
    exact hne b.id hxB b.id (List.mem_map_of_mem hbnew) rfl
  rw [hnil, List.append_nil]

/-! ## 3. τ's per-anchor contribution is a function of the anchor's closure — the discharge of the
former `fold_agrees` hypothesis, which no longer exists. -/

/-- Every segment an anchor appends is unchanged by the growth. This is the former `fold_agrees`
hypothesis — deleted — as a theorem:
`anchorSegment` reads `closureLace B l.id` and `causalPastIncl B l.id`, both of which are pinned by
`l`'s own pointers; and its linearization reads the causal past only of ids in `[l]`, each pinned by
its own pointers the same way (`xsortWith_congr`). -/
theorem anchorSegment_stable {B B' : Lace} (h : ClosedExtension B B') (P : List AuthorId)
    (prev : List BlockId) {l : Block} (hl : B.has l.id = true) :
    anchorSegment B' P prev l = anchorSegment B P prev l := by
  simp only [anchorSegment, anchorSegmentWith]
  rw [closureLace_stable h hl, causalPastIncl_stable h hl]
  apply xsortWith_congr
  intro x hx
  have h2 := (List.mem_filter.mp hx).1
  have h3 := (List.mem_filter.mp h2).1
  exact causalPastIncl_stable h (causalPastIncl_has B hl x h3)

/-- …hence one fold step is unchanged. -/
theorem tauStep_stable {B B' : Lace} (h : ClosedExtension B B') (P : List AuthorId)
    (acc : List BlockId × List BlockId) {l : Block} (hl : B.has l.id = true) :
    tauStep B' P acc l = tauStep B P acc l := by
  have hseg := anchorSegment_stable h P acc.2 hl
  unfold anchorSegment at hseg
  unfold tauStep tauStepWith
  rw [hseg, causalPastIncl_stable h hl]

/-- The anchor CHAIN is unchanged too: `previousRatifiedLeader` quantifies over `[b1]` and nothing
else (CM Alg. 2:41-43). -/
theorem previousRatifiedLeader_stable {B B' : Lace} (h : ClosedExtension B B')
    (P : List AuthorId) (wl : Nat) {b1 : Block} (hb : B.has b1.id = true) :
    previousRatifiedLeader B' P wl b1 = previousRatifiedLeader B P wl b1 := by
  unfold previousRatifiedLeader
  rw [closureLace_stable h hb, causalPastIncl_stable h hb]

/-! ## 4. The fold only APPENDS, and it appends the same things — the structural half of T5. -/

/-- One `tauStep` extends the accumulated order by the anchor's segment (definitional). -/
theorem tauStep_fst (B : Lace) (P : List AuthorId)
    (acc : List BlockId × List BlockId) (l : Block) :
    (tauStep B P acc l).1 = acc.1 ++ anchorSegment B P acc.2 l := rfl

/-- **`foldl_tauStep_fst_extend`** — folding ANY further anchor list onto an accumulator only
APPENDS: CM Alg. 2's recursion never edits what it has already output. The reorder risk therefore
lives ENTIRELY in the anchor chain and the per-anchor segments — and §3 just pinned the segments. -/
theorem foldl_tauStep_fst_extend (B : Lace) (P : List AuthorId) :
    ∀ (T : List Block) (acc : List BlockId × List BlockId),
      ∃ rest, (T.foldl (tauStep B P) acc).1 = acc.1 ++ rest
  | [], acc => ⟨[], by simp⟩
  | l :: T, acc => by
    obtain ⟨r, hr⟩ := foldl_tauStep_fst_extend B P T (tauStep B P acc l)
    exact ⟨anchorSegment B P acc.2 l ++ r, by
      simp only [List.foldl_cons, hr, tauStep_fst, List.append_assoc]⟩

/-- **`foldl_congr_mem`** — a fold is determined by its step function ON THE ELEMENTS IT VISITS.
Stated for ABSTRACT `f`/`g`, deliberately: instantiated at `tauStep B' P` / `tauStep B P` the kernel
would otherwise reduce through `tauStep → anchorSegment → closureLace → causalPastIncl`, a
fuel-recursive BFS over the whole lace, and time out. With the step functions as variables there is
nothing to unfold. (Measured: the `rw`-based proof of the specialised statement did not typecheck at
the default heartbeat budget and did not finish at 20x it.) -/
theorem foldl_congr_mem {α β : Type} {f g : β → α → β} :
    ∀ (L : List α), (∀ (acc : β) (a : α), a ∈ L → f acc a = g acc a) →
      ∀ acc : β, L.foldl f acc = L.foldl g acc
  | [], _, _ => rfl
  | a :: L, h, acc => by
    have h1 : f acc a = g acc a := h acc a (List.mem_cons_self ..)
    calc (a :: L).foldl f acc
        = L.foldl f (f acc a) := rfl
      _ = L.foldl f (g acc a) := congrArg (fun x => List.foldl f x L) h1
      _ = L.foldl g (g acc a) :=
            foldl_congr_mem L (fun acc' x hx => h acc' x (List.mem_cons_of_mem _ hx)) _
      _ = (a :: L).foldl g acc := rfl

/-- Replaying an anchor list of held blocks through the GROWN lace reproduces the fold exactly.
This is the former `fold_agrees` hypothesis (deleted), discharged. -/
theorem foldl_tauStep_stable {B B' : Lace} (h : ClosedExtension B B') (P : List AuthorId)
    (L : List Block) (hall : ∀ l ∈ L, B.has l.id = true)
    (acc : List BlockId × List BlockId) :
    L.foldl (tauStep B' P) acc = L.foldl (tauStep B P) acc :=
  foldl_congr_mem L (fun acc' l hl => tauStep_stable h P acc' (hall l hl)) acc

/-! ## 5. The enrollment verdict is stable — the discharge of the former `enrollment_agrees`
hypothesis, deleted with the rest of `FinalizedRegionStable`.

The old field assumed the growth does not reclassify an already-ordered block's creator. It cannot:
`enrolledId` reads `Lace.lookup`, and §2 pinned that. What was missing was the OTHER half — that
every id the fold emits is one the lace already holds — and that needs membership to survive the
intra-segment sort (`xsortWith_perm`). -/

theorem enrolledId_stable {B B' : Lace} (h : ClosedExtension B B') (P : List AuthorId)
    {bid : BlockId} (hb : B.has bid = true) : enrolledId B P bid = enrolledId B' P bid := by
  unfold enrolledId
  rw [lookup_stable h hb]

/-- Every id an anchor's segment emits is held by the lace. -/
theorem anchorSegment_mem (B : Lace) (P : List AuthorId) (prev : List BlockId) {l : Block}
    (hl : B.has l.id = true) : ∀ bid ∈ anchorSegment B P prev l, B.has bid = true := by
  intro bid hbid
  unfold anchorSegment anchorSegmentWith at hbid
  have h1 := (xsortWith_perm _ _ _).mem_iff.mp hbid
  have h2 := (List.mem_filter.mp h1).1
  have h3 := (List.mem_filter.mp h2).1
  exact causalPastIncl_has B hl bid h3

/-- …hence every id the whole fold emits is held. -/
theorem foldl_tauStep_mem (B : Lace) (P : List AuthorId) :
    ∀ (L : List Block), (∀ l ∈ L, B.has l.id = true) →
      ∀ (acc : List BlockId × List BlockId), (∀ bid ∈ acc.1, B.has bid = true) →
        ∀ bid ∈ (L.foldl (tauStep B P) acc).1, B.has bid = true := by
  intro L
  induction L with
  | nil => intro _ acc hacc bid hbid; exact hacc bid hbid
  | cons l L ih =>
    intro hall acc hacc bid hbid
    have hl := hall l (List.mem_cons_self ..)
    refine ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (tauStep B P acc l) ?_ bid hbid
    intro y hy
    rw [tauStep_fst] at hy
    rcases List.mem_append.mp hy with h1 | h2
    · exact hacc y h1
    · exact anchorSegment_mem B P acc.2 hl y h2

/-! ## 6. Anchors are held blocks.

`previousRatifiedLeader` picks its argmax out of `closureLace B b1.id = B.filter …`, so every anchor
the chain walk reaches came from `B`. Two small general facts do it: a `foldl` whose step returns
either its new element or its accumulator can only ever return a list member or the seed, and a
block present in a lace is `has`. -/

/-- A block present in the lace resolves. -/
theorem has_of_mem {B : Lace} {b : Block} (hb : b ∈ B) : B.has b.id = true := by
  unfold Lace.has Lace.lookup
  cases hf : B.find? (fun x => x.id = b.id) with
  | none => exact absurd (by simp) (List.find?_eq_none.mp hf b hb)
  | some _ => rfl

/-- An argmax-style `foldl` returns the seed or a member of the list. -/
theorem foldl_pick_mem {α : Type} (f : Option α → α → Option α)
    (hf : ∀ o a, f o a = some a ∨ f o a = o) :
    ∀ (l : List α) (init : Option α) (r : α), l.foldl f init = some r → r ∈ l ∨ init = some r := by
  intro l
  induction l with
  | nil => intro init r h; exact Or.inr h
  | cons a rest ih =>
    intro init r h
    simp only [List.foldl_cons] at h
    rcases ih (f init a) r h with h1 | h2
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · rcases hf init a with he | he
      · rw [he] at h2; exact Or.inl ((Option.some.inj h2) ▸ List.mem_cons_self ..)
      · rw [he] at h2; exact Or.inr h2

/-- The previous ratified leader, when it exists, is a block of `B`. -/
theorem previousRatifiedLeader_has {B : Lace} {P : List AuthorId} {wl : Nat} {b1 b' : Block}
    (hp : previousRatifiedLeader B P wl b1 = some b') : B.has b'.id = true := by
  classical
  unfold previousRatifiedLeader at hp
  set Bl := closureLace B b1.id with hBl
  set cands := (causalPastIncl B b1.id).filterMap (fun bid => match Bl.lookup bid with
      | some b => if b.id != b1.id && isLeaderBlock Bl P wl b && ratifies Bl P b1 b
                  then some b else none
      | none   => none) with hcands
  have hcand : ∀ b ∈ cands, B.has b.id = true := by
    intro b hb
    rw [hcands] at hb
    obtain ⟨bid, _, hbid⟩ := List.mem_filterMap.mp hb
    cases hl : Bl.lookup bid with
    | none => rw [hl] at hbid; simp at hbid
    | some c =>
      rw [hl] at hbid
      have hcB : c ∈ B := by
        have hcc : c ∈ Bl := List.mem_of_find?_eq_some hl
        rw [hBl] at hcc
        unfold closureLace at hcc
        exact (List.mem_filter.mp hcc).1
      simp only [] at hbid
      split at hbid
      · have : c = b := Option.some.inj hbid
        exact this ▸ has_of_mem hcB
      · simp at hbid
  rcases foldl_pick_mem _ (fun o a => by
      cases o with
      | none => exact Or.inl rfl
      | some c => by_cases hc : (roundOf Bl P c.id < roundOf Bl P a.id
            || (roundOf Bl P c.id == roundOf Bl P a.id && c.id < a.id)) = true
                  · exact Or.inl (by simp [hc])
                  · exact Or.inr (by simp [hc])) cands none b' hp with h1 | h2
  · exact hcand b' h1
  · simp at h2

/-- Every element of a ratified-leader chain rooted at a held anchor is itself held. -/
theorem ratifiedLeaderChainAux_has (B : Lace) (P : List AuthorId) (wl : Nat) :
    ∀ (f : Nat) (b : Block), B.has b.id = true →
      ∀ x ∈ ratifiedLeaderChainAux B P wl f b, B.has x.id = true := by
  intro f
  induction f with
  | zero =>
    intro b hb x hx
    rw [show ratifiedLeaderChainAux B P wl 0 b = [b] from rfl] at hx
    simpa [List.mem_singleton.mp hx] using hb
  | succ f ih =>
    intro b hb x hx
    unfold ratifiedLeaderChainAux at hx
    cases hp : previousRatifiedLeader B P wl b with
    | none => rw [hp] at hx; simpa [List.mem_singleton.mp hx] using hb
    | some b' =>
      rw [hp] at hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact ih b' (previousRatifiedLeader_has hp) x h1
      · simpa [List.mem_singleton.mp h2] using hb

theorem ratifiedLeaderChain_has (B : Lace) (P : List AuthorId) (wl : Nat) {b : Block}
    (hb : B.has b.id = true) : ∀ x ∈ ratifiedLeaderChain B P wl b, B.has x.id = true :=
  ratifiedLeaderChainAux_has B P wl _ b hb

/-- The head τ picks is a block of `B` (`leaderCandidates` filters `B`). -/
theorem lastFinalLeader_has {B : Lace} {P : List AuthorId} {wl : Nat} {hd : Block}
    (h : lastFinalLeader B P wl = some hd) : B.has hd.id = true := by
  classical
  have hmem : hd ∈ findAllFinalLeaders B P wl := by
    unfold lastFinalLeader at h
    exact List.mem_of_getLast? h
  unfold findAllFinalLeaders at hmem
  obtain ⟨w, _, hw⟩ := List.mem_filterMap.mp hmem
  unfold finalLeaderAt at hw
  cases hc : leaderCandidates B P w wl with
  | nil => rw [hc] at hw; simp at hw
  | cons l rest =>
    cases rest with
    | cons _ _ => rw [hc] at hw; simp at hw
    | nil =>
      rw [hc] at hw
      simp only [] at hw
      split at hw
      · have hld : l = hd := Option.some.inj hw
        have hlm : l ∈ leaderCandidates B P w wl := by rw [hc]; exact List.mem_cons_self ..
        unfold leaderCandidates at hlm
        cases hwl : waveLeader w P with
        | none => rw [hwl] at hlm; simp at hlm
        | some lk =>
          rw [hwl] at hlm
          exact hld ▸ has_of_mem (List.mem_filter.mp hlm).1
      · simp at hw

/-! ## 7. T5 — finalized-prefix monotonicity, with ONE hypothesis.

`ChainExtends` is CM Prop. 9's central argument: the smaller lace's head `b̂₂` appears in the
recursion chain of the larger lace's head `b̂₁`, so the chains extend. CM derives it from Prop. 3
(leader-safety), which follows from CORDIALITY alone — a per-block admission predicate
(`Distributed.BlocklaceFinality.isCordialBlock`, CM Def. 25 / Alg. 1:15-16).

⚠ It is NOT proved here, and the module header says exactly what stands between it and a proof:
Prop. 3 needs a quorum-intersection formalisation over the DAG, and our `finalLeaderAt` is not
monotone in the way CM's `final_leader` is. This is one named import from the paper, where there
used to be three assumptions the deployed rule could not satisfy at all. -/

/-- **`ChainExtends B B' P wl`** — the anchor chain only extends (CM Prop. 3 / Prop. 9). -/
structure ChainExtends (B B' : Lace) (P : List AuthorId) (wl : Nat) : Prop where
  head_chain : ∀ hd, lastFinalLeader B P wl = some hd →
      ∃ hd', lastFinalLeader B' P wl = some hd'
        ∧ ratifiedLeaderChain B P wl hd <+: ratifiedLeaderChain B' P wl hd'

/-- **`tau_finalized_prefix_monotone` (T5).** Under a CLOSED EXTENSION and CM's leader-safety, the
computed finalized order only extends: previously-finalized blocks keep their positions. No
rollback, no reorder, and — the part that is new — no hypothesis about coverage or about replaying
a fold, because CM Def. 6's per-anchor input cannot move. -/
theorem tau_finalized_prefix_monotone {B B' : Lace} {P : List AuthorId} {wl : Nat}
    (hext : ClosedExtension B B') (hchain : ChainExtends B B' P wl) :
    tauOrder B P wl <+: tauOrder B' P wl := by
  classical
  cases hhd : lastFinalLeader B P wl with
  | none =>
    have hnil : tauOrder B P wl = [] := by
      unfold tauOrder; rw [hhd]
    rw [hnil]
    exact List.nil_prefix
  | some hd =>
    obtain ⟨hd', hhd', T, hT⟩ := hchain.head_chain hd hhd
    have hheld : B.has hd.id = true := lastFinalLeader_has hhd
    have hchainHas : ∀ l ∈ ratifiedLeaderChain B P wl hd, B.has l.id = true :=
      ratifiedLeaderChain_has B P wl hheld
    -- the OLD fold, replayed in the GROWN lace, is the old fold (the former `fold_agrees`
    -- hypothesis, deleted and discharged). The enrollment verdict rides inside each segment, so
    -- the former `enrollment_agrees` hypothesis is discharged by the same replay.
    have hreplay := foldl_tauStep_stable hext P (ratifiedLeaderChain B P wl hd) hchainHas ([], [])
    -- the grown fold is the old fold followed by the extra anchors, which only APPEND.
    obtain ⟨rest, hrest⟩ :=
      foldl_tauStep_fst_extend B' P T
        ((ratifiedLeaderChain B P wl hd).foldl (tauStep B' P) ([], []))
    have hgrown : tauOrder B' P wl = tauOrder B P wl ++ rest := by
      unfold tauOrder
      simp only [hhd, hhd']
      rw [← hT, List.foldl_append, hrest, hreplay]
    exact ⟨rest, hgrown.symm⟩

/-- **`tau_executed_prefix_fixed`** — the node-shaped corollary: the first `(tauOrder B).length`
entries of the grown order are EXACTLY the old order. This is what `ExecutionCursor`'s cached prefix
needs, and it is what CM §5 p.9 says the caching is licensed by. -/
theorem tau_executed_prefix_fixed {B B' : Lace} {P : List AuthorId} {wl : Nat}
    (hext : ClosedExtension B B') (hchain : ChainExtends B B' P wl) :
    tauOrder B P wl = (tauOrder B' P wl).take (tauOrder B P wl).length :=
  List.prefix_iff_eq_take.mp (tau_finalized_prefix_monotone hext hchain)

/-! ## 8. THE FORMER COUNTEREXAMPLE, INVERTED.

Four validators `[1,2,3,4]` (supermajority 3), wavelength 3. Validator 4 publishes its genesis block
`40`, then LAGS — a partition, a slow link, pure asynchrony, no fault. Validators 1–3 complete
rounds 2 and 3 and wave 0's leader (validator 1's genesis, block `10`) is super-ratified. THEN
validator 4 catches up: its round-2 block `41` and round-3 block `42` arrive, both passing every
verified-insert check, and `42` sits at wave 0's END round and ratifies leader `10`.

Under the RATIFIER-UNION rule that grew wave 0's coverage by `{41, 42}` and `xsort` placed `41`
(round 2) BEFORE round-3 blocks the node had already executed:

```
  tauOrder lagBase  = [10,20,30,40,11,21,31,12,22,32]
  tauOrder lagGrown = [10,20,30,40,11,21,31,41,12,22,32,42]     -- NOT a prefix
```

Under CM Def. 6 the anchor is block `10`, its closure is `{10}`, and `41`/`42` are not in it. Both
laces order `[10]`; the late blocks are ordered by a LATER anchor, after everything already emitted.
The guards below pin the whole chain of reasoning, not just the conclusion. -/

def lagR1 : Lace := [⟨10,1,0,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩, ⟨40,4,0,[],true⟩]
def lagR2 : Lace :=
  [⟨11,1,1,[10,20,30,40],true⟩, ⟨21,2,1,[10,20,30,40],true⟩, ⟨31,3,1,[10,20,30,40],true⟩]
def lagR3 : Lace := [⟨12,1,2,[11,21,31],true⟩, ⟨22,2,2,[11,21,31],true⟩, ⟨32,3,2,[11,21,31],true⟩]
/-- The lace at the first poll: wave 0 finalized WITHOUT validator 4's rounds 2–3. -/
def lagBase : Lace := lagR1 ++ lagR2 ++ lagR3
/-- Validator 4 catches up: an honest round-2 block and a round-3 block ratifying leader `10`. -/
def lagLate : Lace := [⟨41,4,1,[10,20,30,40],true⟩, ⟨42,4,2,[11,21,31,41],true⟩]
/-- The grown lace at the next poll. -/
def lagGrown : Lace := lagBase ++ lagLate
def lagParticipants : List AuthorId := [1, 2, 3, 4]

/-- **`insertValidArrival`** — the arrival order satisfies the verified `insert`'s feed-integrity
discipline (`blocklace/src/lib.rs::insert`): every block signed, all preds already present, and
per-creator `seq` strictly monotone. Certifies the trace needs NO Byzantine step. -/
def insertValidArrival (arrival : List Block) : Bool := go [] arrival
  where go (acc : Lace) : List Block → Bool
    | [] => true
    | b :: rest =>
        b.signed
        && b.preds.all (fun p => acc.has p)
        && acc.all (fun a => a.creator != b.creator || a.seq < b.seq)
        && go (acc ++ [b]) rest

-- The arrival is honest: verified-insert-valid, nobody equivocates, and the growth is a plain
-- superset extension — every premise the old refutation relied on is still here.
#guard insertValidArrival lagGrown
#guard lagGrown.all (fun a => lagGrown.all (fun b =>
        a.id == b.id || a.creator != b.creator
          || roundOf lagGrown lagParticipants a.id != roundOf lagGrown lagParticipants b.id))
#guard superMajority lagParticipants.length == 3
#guard lagBase.all (fun b => lagGrown.contains b)
-- …and the growth is a CLOSED EXTENSION: ids unique, every predecessor of a held block held.
#guard (lagBase.map (·.id)).eraseDups.length == lagBase.length
#guard (lagGrown.map (·.id)).eraseDups.length == lagGrown.length
#guard lagBase.all (fun b => b.preds.all (fun p => lagBase.has p))
#guard lagGrown.all (fun b => b.preds.all (fun p => lagGrown.has p))

-- THE INVERSION. Both laces still finalize wave 0 on the same anchor…
#guard (findAllFinalLeaders lagBase lagParticipants 3).map (·.id) == [10]
#guard (findAllFinalLeaders lagGrown lagParticipants 3).map (·.id) == [10]
-- …the anchor's closure — CM's `[b₁]`, the ONLY thing its segment is a function of — did not move…
#guard causalPastIncl lagBase 10 == causalPastIncl lagGrown 10
#guard causalPastIncl lagGrown 10 == [10]
#guard closureLace lagBase 10 == closureLace lagGrown 10
-- …the anchor CHAIN did not move…
#guard ratifiedLeaderChain lagBase lagParticipants 3 ⟨10,1,0,[],true⟩
        == ratifiedLeaderChain lagGrown lagParticipants 3 ⟨10,1,0,[],true⟩
-- …so the finalized order is unchanged, and the old order IS a prefix of the new one.
#guard tauOrder lagBase lagParticipants 3 == [10]
#guard tauOrder lagGrown lagParticipants 3 == [10]
#guard (tauOrder lagBase lagParticipants 3).isPrefixOf (tauOrder lagGrown lagParticipants 3)
-- ⚑ AND THE MECHANISM THAT USED TO BREAK IT IS GONE AT THE SOURCE: the late ratifier `42` really is
--   a wave-end block that ratifies the leader — the premise of the old refutation still holds — it
--   simply no longer decides what the anchor orders.
#guard roundOf lagGrown lagParticipants 42 == 3
#guard ratifiesEnrolled lagGrown lagParticipants ⟨42,4,2,[11,21,31,41],true⟩ ⟨10,1,0,[],true⟩
#guard !(causalPastIncl lagGrown 10).contains 41
#guard !(tauOrder lagGrown lagParticipants 3).contains 41
-- The node-side damage the old rule caused is therefore unreachable: nothing already emitted is
-- re-emitted, and nothing falls behind a cursor.
#guard (tauOrder lagGrown lagParticipants 3).take (tauOrder lagBase lagParticipants 3).length
        == tauOrder lagBase lagParticipants 3

-- ⚑ AND THE TRACE SITS INSIDE CM'S HYPOTHESIS. Both laces are CORDIAL (CM Def. 25), so this was
--   never a case the paper excludes — it was one our deviation from Def. 6 created. That is the
--   difference between "the counterexample is out of scope" and "the counterexample is fixed".
#guard isCordialLace lagBase lagParticipants
#guard isCordialLace lagGrown lagParticipants
-- `pred_closed` is load-bearing and CAN go red: block 42 is not admissible into `lagBase`, because
-- its predecessor 41 is absent. CM Alg. 3:49 buffers exactly this, and so does
-- `node/src/catchup.rs::apply_with_buffering`.
#guard !predsPresent lagBase ⟨42,4,2,[11,21,31,41],true⟩
#guard !admitBlock lagBase lagParticipants ⟨42,4,2,[11,21,31,41],true⟩
#guard lagGrown.all (fun b => predsPresent lagGrown b)

/-! ## 9. NON-VACUITY (positive) — a growth that orders STRICTLY MORE.

A prefix result over an order that never grows is worth nothing. `trace3 → trace6` (the 3-node lace
grown by a full second wave) anchors a SECOND leader, whose closure is the whole of rounds 1–3, so
the order goes from 1 block to 10 and the old order is a proper prefix. -/

#guard insertValidArrival trace6
#guard (findAllFinalLeaders trace6 trace3Participants 3).map (·.id) == [10, 23]
#guard (tauOrder trace3 trace3Participants 3).length == 1
#guard (tauOrder trace6 trace3Participants 3).length == 10
#guard (tauOrder trace3 trace3Participants 3).isPrefixOf (tauOrder trace6 trace3Participants 3)
#guard (tauOrder trace6 trace3Participants 3).take (tauOrder trace3 trace3Participants 3).length
        == tauOrder trace3 trace3Participants 3
-- the anchor chain EXTENDS (the `ChainExtends` hypothesis, satisfied by a real growth)…
#guard (ratifiedLeaderChain trace3 trace3Participants 3 ⟨10,1,0,[],true⟩).map (·.id) == [10]
#guard (ratifiedLeaderChain trace6 trace3Participants 3 ⟨23,2,3,[12,22,32],true⟩).map (·.id)
        == [10, 23]
-- …and the growth is a closed extension, so `tau_finalized_prefix_monotone` genuinely applies here.
#guard trace6.all (fun b => b.preds.all (fun p => trace6.has p))
#guard (trace6.map (·.id)).eraseDups.length == trace6.length

/-! The `#guard`s are the sanctioned executable teeth (a false one is a BUILD ERROR;
`native_decide` is banned in this tree). Together: §8 shows the growth that USED to reorder
finalized history now cannot, with the mechanism pinned at the anchor's closure rather than at the
conclusion; §9 shows a growth that satisfies the hypotheses and strictly extends, so the theorem's
conclusion is non-trivial. -/

/-! ## 10. Axiom hygiene. -/

#assert_axioms lookup_stable
#assert_axioms expandPreds_stable
#assert_axioms causalPastAux_stable
#assert_axioms causalPastIncl_stable
#assert_axioms closureLace_stable
#assert_axioms anchorSegment_stable
#assert_axioms tauStep_stable
#assert_axioms previousRatifiedLeader_stable
#assert_axioms foldl_tauStep_stable
#assert_axioms foldl_tauStep_fst_extend
#assert_axioms enrolledId_stable
#assert_axioms foldl_tauStep_mem
#assert_axioms ratifiedLeaderChain_has
#assert_axioms lastFinalLeader_has
#assert_axioms tau_finalized_prefix_monotone
#assert_axioms tau_executed_prefix_fixed

end Dregg2.Consensus.TauPrefixMonotone
