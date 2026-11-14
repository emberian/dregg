/-
# Dregg2.Consensus.SuperRatifyBridge — `OPEN-CM-SUPERRATIFY-BRIDGE`, closed as far as it
# closes: from the finalizer THE NODE RUNS to the finalizer THE SAFETY THEOREM PROVES.

`Consensus.Safety` proves chain safety on `Proof.CordialMiners.Committed` — the BFT algebra.
The node does not run that. The node runs `Distributed.BlocklaceFinality.tauOrderFast`
(`@[export] dregg_tau_order`, `node/src/finality_gate.rs`), whose commit decision is
`finalLeaderAt` → `isSuperRatified`. Nothing in the tree said the second obeys the first. This
module states the exact mismatch, proves the implication that does hold, and names + models the
hypotheses it does not.

## THE MISMATCH, axis by axis (§1 states each as a theorem or a refutation).

| | deployed (`isSuperRatified`/`finalLeaderAt`) | proved (`Committed`) | direction |
|-|-|-|-|
|outer quorum|supermajority of DISTINCT **ENROLLED** wave-end creators, each `ratifies`|**one** observer anywhere in the lace|deployed STRONGER|
|inner threshold|`superMajority n = ⌊2n/3⌋+1`|`cfg.n − cfg.f`|**incomparable**|
|leader-in-past|`causal_past_INCLUSIVE`|(was strict `≺`; repaired 2026-07-28)|now agree|
|equivocation guard|observer-LOCAL, same-ROUND pair in `o`'s past|GLOBAL `Equivocator` = incomparable pair anywhere|**incomparable**|
|unique leader|`leaderCandidates = [l]` — lives in `finalLeaderAt`|`unique_leader` field|`isSuperRatified` alone has NONE|
|id → block|`BlockId` + `lookup`|`Block`|needs `Lace.Canonical`|

**So `isSuperRatified` and `Committed` are INCOMPARABLE, and `isSuperRatified` is the wrong
object to bridge from** — it carries no unique-leader guard at all (`superRatified_alone_is_not_committed`).
`finalLeaderAt` is the right one: it is where `leader_blocks.len() == 1` lives, and it is what
`findAllFinalLeaders`/`tauOrder` actually call.

## WHAT IS PROVED (§3): `committed_of_finalLeaderAt`.

    B.Canonical → participants.Nodup → ThresholdAgrees cfg participants →
    LeaderNotGlobalEquivocator B l → finalLeaderAt B participants wave wavelength = some l →
    Committed (deployedState B participants wavelength) cfg l

and its lift `finalizedBy_deployedHistory` : the history the node's own wave loop produces
satisfies the apex's `FinalizedBy` premise; and the capstone
`deployed_nodes_no_conflicting_history` : **two nodes each running the deployed finalizer never
disagree on a finalized wave's leader** — the apex, reached from the deployed rule.

## THE TWO HYPOTHESES THIS COSTS — NAMED, MODELLED, REFUTED (§2, §4).

1. **`ThresholdAgrees cfg participants`** — `cfg.n − cfg.f ≤ superMajority participants.length`.
   The deployed rule counts against `⌊2n/3⌋+1`; the algebra's quorum field is `n − f`. They
   coincide EXACTLY on `3f+1 ≤ n ≤ 3f+3` (`thresholdAgrees_of_canonical_bft`) and the upper
   bound is TIGHT (`thresholdAgrees_fails_at_3f_plus_4`): at `n = 7, f = 1` the node finalizes on
   5 ratifiers where the algebra demands 6. Decidable, satisfiable, refutable.
2. **`LeaderNotGlobalEquivocator B l`** — `¬ Equivocator B l.creator`. The node's guard
   (`hasEquivInPast`) is OBSERVER-LOCAL and keyed on a same-ROUND pair; `Equivocator` is GLOBAL
   and keyed on an INCOMPARABLE pair. `Model.forked` exhibits a lace where a full supermajority
   of the node's ratifiers ratify the leader (`forked_node_still_ratifies`, by `decide`) while
   `Equivocator` holds and therefore `Committed` is FALSE (`forked_is_not_committed`). **This is
   a COVERAGE HOLE, not an attack**: the deployed rule is the more faithful of the two here (a
   node can only act on what it sees), so the honest reading is that the ALGEBRA is over-strong
   and the safety theorem is silent on those runs. The repair — teaching `CordialState.approves`
   the observer-local guard — is `OPEN-CM-LOCAL-EQUIVOCATION`, named and NOT done here.

## WHAT THE KERNEL CANNOT SEE — read before trusting a `#guard`.

When this module was written `roundOf` → `computeRounds` → `Array.qsort`, whose worker is
well-founded-recursive and private to `Init`, so the kernel could not reduce it (measured
2026-07-28: `decide` stuck on `roundOf pB 100 = 1`) and no Lean THEOREM could evaluate the
deployed finalizer on a concrete lace. §4's models were therefore built to be round-FREE where
they are theorems (they turn on `Lace`-structural facts and `causalPastIncl`, both of which DO
reduce), and the round-dependent facts appear only as `#guard`s, labelled — COMPILER checks,
outside the kernel, tests and not proofs.

⚑ That obstacle is gone for the round map and the head selection. Since dregg issue #100
`computeRounds` folds a structural Kahn enumeration (`BlocklaceFinality.topoLace`), and `decide`
reduces `roundOf`, `isSuperRatified`, `finalLeaderAt` and `findAllFinalLeaders` on
`BlocklaceFinality`'s traces (measured 2026-11-13). It still does not reduce `tauOrder`, whose
linearization goes through `List.mergeSort`. The `#guard`s below have NOT been re-stated as
theorems; that is owed, not done.

## SCOPE — what this does NOT do.

* It does not discharge the union BFT model, and it does not discharge `CrossNodeCanonical`.
  The capstone carries both, exactly as the apex does.
* `Model.*` is `n = 4, f = 1`, one wave. Satisfiability and refutability, NOT scale. The bridge
  theorem itself is fully general in `n`, `f`, `B` and `participants`.
* `OPEN-CM-LOCAL-EQUIVOCATION` (above) is open. Until it closes, a node that finalizes a leader
  whose author forked OUTSIDE every honest observer's causal past is finalizing OUTSIDE the
  safety theorem's domain.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no `native_decide`.
Verified with `lake build Dregg2.Consensus.SuperRatifyBridge`.
-/
import Dregg2.Consensus.Safety

namespace Dregg2.Consensus.SuperRatifyBridge

open Dregg2 Dregg2.Authority.Blocklace
open Dregg2.Proof.CordialMiners
open Dregg2.Distributed.BlocklaceFinality

/-! ## §0. Structural facts about `precedes` the models need (no decidability required).

`precedes` is an inductive `Prop` (the transitive closure of `pointed`), so `decide` cannot
refute it. These two lemmas are what let a concrete lace prove `¬ precedes` — and therefore
`incomparable`, and therefore `Equivocator`. -/

/-- **`precedes_preds_ne_nil`** — nothing precedes a block with no predecessors. The base case
puts `a.id` in `b.preds`; `trans` inherits the right-hand end. A genesis block is a leaf of `≺`. -/
theorem precedes_preds_ne_nil {B : Lace} {a b : Block} (h : precedes B a b) : b.preds ≠ [] := by
  induction h with
  | base hp =>
    obtain ⟨hin, _, _⟩ := hp
    intro hnil
    rw [hnil] at hin
    exact absurd hin (by simp)
  | trans _ _ _ ihmb => exact ihmb

/-- **`precedes_inv`** — one step down. If `a ≺ b` then some predecessor id `p` of `b` either IS
`a`, or resolves to a block `m` with `a ≺ m`. Inverting the transitive closure from the TOP,
which is what a concrete lace can iterate. -/
theorem precedes_inv {B : Lace} {a b : Block} (h : precedes B a b) :
    ∃ p ∈ b.preds, a.id = p ∨ ∃ m, B.lookup p = some m ∧ precedes B a m := by
  induction h with
  | @base a b hp => exact ⟨a.id, hp.1, Or.inl rfl⟩
  | @trans a m b hab hmb _ ihmb =>
    obtain ⟨p, hpb, hp⟩ := ihmb
    rcases hp with hid | ⟨m', hm', hmm'⟩
    · exact ⟨p, hpb, Or.inr ⟨m, hid ▸ precedes_lookup_left hmb, hab⟩⟩
    · exact ⟨p, hpb, Or.inr ⟨m', hm', hab.trans hmm'⟩⟩

/-! ## §1. `causalPastIncl` is SOUND for `precedes` — the id-level BFS meets the Prop-level order.

`ordering.rs::causal_past_inclusive` is a fuel-bounded BFS over `BlockId`s; `Committed` is stated
with `Authority.Blocklace.precedes`, an inductive `Prop` over `Block`s. Every step of the bridge
crosses that boundary. Nothing in the tree had crossed it before. -/

/-- **`PastWitness B h bid`** — the `Prop`-level meaning of "the BFS reached `bid` from `h`":
either `bid` IS `h`, or the block at `bid` genuinely precedes the block at `h`. -/
def PastWitness (B : Lace) (h bid : BlockId) : Prop :=
  bid = h ∨ ∃ a hb, B.lookup bid = some a ∧ B.lookup h = some hb ∧ precedes B a hb

/-- A resolved id is the resolved block's own id (`lookup` matches on `b.id = h`). -/
theorem lookup_id {B : Lace} {bid : BlockId} {a : Block} (h : B.lookup bid = some a) :
    a.id = bid := by
  have := List.find?_some h
  simpa using this

/-- A resolved id names a block of the lace. -/
theorem lookup_mem {B : Lace} {bid : BlockId} {a : Block} (h : B.lookup bid = some a) : a ∈ B :=
  List.mem_of_find?_eq_some h

/-- **`mem_expandPreds`** — one BFS layer only ever produces genuine `pointed` predecessors. -/
theorem mem_expandPreds {B : Lace} {frontier : List BlockId} {bid : BlockId}
    (hm : bid ∈ expandPreds B frontier) :
    ∃ h' ∈ frontier, ∃ a b', B.lookup bid = some a ∧ B.lookup h' = some b' ∧ precedes B a b' := by
  unfold expandPreds at hm
  rw [List.mem_flatMap] at hm
  obtain ⟨h', hh', hbid⟩ := hm
  cases hlk : B.lookup h' with
  | none => rw [hlk] at hbid; simp at hbid
  | some b' =>
    rw [hlk] at hbid
    simp only [List.mem_filter] at hbid
    obtain ⟨hmem, hhas⟩ := hbid
    unfold Lace.has at hhas
    rw [Option.isSome_iff_exists] at hhas
    obtain ⟨a, ha⟩ := hhas
    refine ⟨h', hh', a, b', ha, hlk, ?_⟩
    exact precedes.base ⟨by rw [lookup_id ha]; exact hmem, by rw [lookup_id ha]; exact ha,
      by rw [lookup_id hlk]; exact hlk⟩

/-- **`causalPastAux_sound`** — the BFS invariant: everything the accumulator ever holds is a
genuine `PastWitness`. Induction on fuel, with the frontier and accumulator generalized. -/
theorem causalPastAux_sound (B : Lace) (h : BlockId) :
    ∀ (fuel : Nat) (frontier acc : List BlockId),
      (∀ x ∈ frontier, PastWitness B h x) → (∀ x ∈ acc, PastWitness B h x) →
      ∀ x ∈ causalPastAux B fuel frontier acc, PastWitness B h x := by
  intro fuel
  induction fuel with
  | zero =>
    intro frontier acc _ hacc x hx
    exact hacc x (List.mem_dedup.mp hx)
  | succ n ih =>
    intro frontier acc hfr hacc x hx
    cases frontier with
    | nil => exact hacc x (List.mem_dedup.mp hx)
    | cons y ys =>
      set nxt := (expandPreds B (y :: ys)).filter (fun p => ¬ acc.contains p) with hnxt
      have hstep : causalPastAux B (n + 1) (y :: ys) acc = causalPastAux B n nxt (acc ++ nxt) :=
        rfl
      rw [hstep] at hx
      have hnew : ∀ z ∈ nxt, PastWitness B h z := by
        intro z hz
        rw [hnxt, List.mem_filter] at hz
        obtain ⟨h', hh', a, b', hla, hlb, hpre⟩ := mem_expandPreds hz.1
        rcases hfr h' hh' with rfl | ⟨a₂, hb, hla₂, hlh, hpre₂⟩
        · exact Or.inr ⟨a, b', hla, hlb, hpre⟩
        · have : a₂ = b' := by rw [hlb] at hla₂; exact (Option.some_inj.mp hla₂.symm)
          subst this
          exact Or.inr ⟨a, hb, hla, hlh, hpre.trans hpre₂⟩
      refine ih nxt (acc ++ nxt) hnew ?_ x hx
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hacc z hz
      · exact hnew z hz

/-- **`causalPastIncl_sound`** — the deployed BFS never reports a block that does not genuinely
precede the observer (or IS it). This is the id-level → `Prop`-level crossing, once. -/
theorem causalPastIncl_sound {B : Lace} {h x : BlockId} (hx : x ∈ causalPastIncl B h) :
    PastWitness B h x := by
  -- `causalPastIncl` runs the frontier-deduped BFS; `causalPastIncl_eq_spec` says it returns the
  -- spec's list, so the soundness lemma about `causalPastAux` applies to the membership unchanged.
  rw [causalPastIncl_eq_spec] at hx
  refine causalPastAux_sound B h B.length [h] [h] ?_ ?_ x hx <;>
    · intro z hz; simp only [List.mem_singleton] at hz; exact Or.inl hz

/-- **`past_block`** — the block-level corollary, on a CANONICAL lace: if the BFS from `o` reached
`b`'s address, then `b = o` or `b ≺ o`. `Lace.Canonical` is exactly what turns "an id the BFS
reached" into "this block". Consumer number six of that floor. -/
theorem past_block {B : Lace} (hc : B.Canonical) {o b : Block}
    (hob : o ∈ B) (hbb : b ∈ B) (hm : b.id ∈ causalPastIncl B o.id) :
    b = o ∨ precedes B b o := by
  rcases causalPastIncl_sound hm with hid | ⟨a, hb, hla, hlo, hpre⟩
  · exact Or.inl (hc b hbb o hob hid)
  · have hab : a = b := by
      rw [lookup_of_mem hc hbb] at hla; exact (Option.some_inj.mp hla).symm
    have hbo : hb = o := by
      rw [lookup_of_mem hc hob] at hlo; exact (Option.some_inj.mp hlo).symm
    subst hab; subst hbo; exact Or.inr hpre

/-- `Lace.Canonical` is decidable on a concrete lace — a node can CHECK its own content-addressing
invariant, and the models below can `decide` it. -/
instance decidableCanonical (B : Lace) : Decidable B.Canonical := by
  unfold Lace.Canonical; infer_instance

/-! ## §2. The two hypotheses the bridge costs — NAMED, decidable, with their exact reach. -/

/-- **`ThresholdAgrees cfg participants`** — the deployed supermajority is at least the algebra's
quorum. `ordering.rs::supermajority_threshold` counts against `⌊2n/3⌋+1`;
`superRatifiedFromLace.quorum_from_lace` demands `n − f`. They are DIFFERENT numbers and the
bridge needs the deployed one to dominate. Decidable, so a node can check its own config. -/
def ThresholdAgrees (cfg : Finality.Config) (participants : List AuthorId) : Prop :=
  cfg.n - cfg.f ≤ superMajority participants.length

instance (cfg : Finality.Config) (ps : List AuthorId) : Decidable (ThresholdAgrees cfg ps) := by
  unfold ThresholdAgrees; infer_instance

/-- **`thresholdAgrees_of_canonical_bft` — it holds on the whole canonical BFT band.** For
`n = participants.length` with `3f+1 ≤ n ≤ 3f+3`, `⌊2n/3⌋+1 = n − f` EXACTLY. So at every
parameter a real deployment uses, the two thresholds are the same number. -/
theorem thresholdAgrees_of_canonical_bft {cfg : Finality.Config} {ps : List AuthorId}
    (hn : cfg.n = ps.length) (hlo : 3 * cfg.f + 1 ≤ cfg.n) (hhi : cfg.n ≤ 3 * cfg.f + 3) :
    ThresholdAgrees cfg ps := by
  unfold ThresholdAgrees superMajority
  omega

/-- **`thresholdAgrees_fails_at_3f_plus_4` — and the band is TIGHT.** One participant past it the
deployed rule finalizes on strictly FEWER ratifiers than the algebra's quorum: at `n = 3f+4` the
node needs `2f+3` and `Committed` demands `2f+4`. Not provable, therefore genuinely a hypothesis. -/
theorem thresholdAgrees_fails_at_3f_plus_4 (f : Nat) (ps : List AuthorId)
    (hn : ps.length = 3 * f + 4) :
    ¬ ThresholdAgrees ⟨3 * f + 4, f, 0⟩ ps := by
  unfold ThresholdAgrees superMajority
  simp only [hn]
  omega

/-- Concrete refutation at the smallest instance: `n = 7, f = 1` — the node finalizes a leader on
5 wave-end ratifiers while `Committed` demands 6. -/
theorem thresholdAgrees_refuted_n7 : ¬ ThresholdAgrees ⟨7, 1, 0⟩ [0, 1, 2, 3, 4, 5, 6] := by
  decide

/-- Concrete satisfaction at the canonical `n = 4, f = 1`. -/
theorem thresholdAgrees_satisfied_n4 : ThresholdAgrees ⟨4, 1, 3⟩ [7, 0, 1, 2] := by decide

/-- **`LeaderNotGlobalEquivocator B l`** — the leader's author did not fork ANYWHERE in this
lace. The node cannot check this: `ordering.rs::approves` consults
`equiv.equivocates_in_past(leader_creator, &past)`, which is OBSERVER-LOCAL and keyed on a
same-ROUND pair, while `Equivocator` is GLOBAL and keyed on an INCOMPARABLE pair. Neither
predicate implies the other. `Model.forked` refutes this one with the node's ratifiers intact. -/
def LeaderNotGlobalEquivocator (B : Lace) (l : Block) : Prop := ¬ Equivocator B l.creator

/-- **`not_committed_of_equivocator`** — the whole force of the second hypothesis, general: a
leader whose author is a global equivocator is committed by the algebra on NO lace, because
`CordialState.approves` conjoins `¬ Equivocator` and so the lace-read ratifier list is EMPTY. The
node's `ratifies` may still be `true` (it reads the local guard) — that gap IS the coverage hole. -/
theorem not_committed_of_equivocator {B : Lace} {rnd : Nat → Nat} {ps : List AuthorId}
    {wl : Nat} {cfg : Finality.Config} {l : Block}
    (hpos : 0 < cfg.n - cfg.f) (heq : Equivocator B l.creator) :
    ¬ Committed ⟨B, rnd, ps, wl⟩ cfg l := by
  classical
  rintro ⟨sr⟩
  have hq := sr.quorum_from_lace
  have hnil : (CordialState.ratifyingVoters ⟨B, rnd, ps, wl⟩ sr.observer l) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro p hp
    unfold CordialState.ratifyingVoters at hp
    rw [List.mem_dedup, List.mem_filter] at hp
    obtain ⟨b, _, _, _, happ⟩ := of_decide_eq_true hp.2
    exact happ.2 heq
  rw [hnil] at hq
  simp only [List.length_nil] at hq
  omega

/-! ## §3. THE BRIDGE. -/

/-- **`deployedState B participants wavelength`** — the `CordialState` the node's own inputs
determine: its lace, `ordering.rs::compute_rounds` as the round map, its participant list, its
wavelength. This is the state on which `Consensus.Safety`'s apex must be read if it is to be a
statement about a running node. -/
def deployedState (B : Lace) (participants : List AuthorId) (wavelength : Nat) : CordialState :=
  { lace := B, rounds := roundOf B participants, participants := participants,
    wavelength := wavelength }

/-- The per-participant test inside `ordering.rs::ratifies` (a `p`-authored block in the
observer's inclusive past that approves the leader), named so it can be reasoned about. -/
def RatifierRead (B : Lace) (ps : List AuthorId) (o l : Block) (p : AuthorId) : Bool :=
  (causalPastIncl B o.id).any (fun bid => match B.lookup bid with
    | some b => b.creator == p && approves B ps b l
    | none   => false)

/-- `ratifies` IS the count of `RatifierRead` over the participants, against `superMajority`. -/
theorem ratifies_eq (B : Lace) (ps : List AuthorId) (o l : Block) :
    ratifies B ps o l
      = decide (superMajority ps.length ≤ (ps.filter (RatifierRead B ps o l)).length) := rfl

/-- Filtering by a stronger predicate cannot keep more. Proved directly (no name-guessing at the
`countP` API). -/
theorem length_filter_mono {α : Type _} (l : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hp : p a = true
    · have hq := h a hp
      simp only [List.filter_cons, hp, hq, if_pos, List.length_cons]
      omega
    · simp only [Bool.not_eq_true] at hp
      by_cases hq : q a = true
      · simp only [List.filter_cons, hp, hq, if_pos, if_neg, List.length_cons,
          Bool.false_eq_true, not_false_eq_true]
        omega
      · simp only [Bool.not_eq_true] at hq
        simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_neg, not_false_eq_true]
        omega

/-- **`hasApprovingBlock_of_ratifierRead`** — the semantic core. The node's `RatifierRead` (ids,
`Bool`, BFS, observer-local equivocation) implies the algebra's `HasApprovingBlock` (blocks,
`Prop`, `≺`, global equivocation) — GIVEN canonicity (to turn reached ids into blocks) and
`LeaderNotGlobalEquivocator` (to supply the conjunct the node never checks). -/
theorem hasApprovingBlock_of_ratifierRead {B : Lace} {rnd : Nat → Nat} {ps : List AuthorId}
    {wl : Nat} {o l : Block} {p : AuthorId}
    (hc : B.Canonical) (hoB : o ∈ B) (hlB : l ∈ B)
    (hne : LeaderNotGlobalEquivocator B l)
    (hr : RatifierRead B ps o l p = true) :
    CordialState.HasApprovingBlock ⟨B, rnd, ps, wl⟩ o l p := by
  unfold RatifierRead at hr
  rw [List.any_eq_true] at hr
  obtain ⟨bid, hbid, hcond⟩ := hr
  cases hlk : B.lookup bid with
  | none => rw [hlk] at hcond; simp at hcond
  | some b =>
    rw [hlk] at hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hcr, happ⟩ := hcond
    have hbB : b ∈ B := lookup_mem hlk
    have hbid' : b.id = bid := lookup_id hlk
    -- the approving block is in the observer's inclusive past
    have hbo : b = o ∨ precedes B b o := past_block hc hoB hbB (by rw [hbid']; exact hbid)
    -- the leader is in the approving block's INCLUSIVE past (`ordering.rs` uses
    -- `causal_past_inclusive`; `CordialState.approves` was repaired to match on 2026-07-28)
    unfold approves at happ
    simp only [Bool.and_eq_true] at happ
    have hlp : l.id ∈ causalPastIncl B b.id := by
      have := happ.1
      simpa using List.mem_of_elem_eq_true this
    have hlb : l = b ∨ precedes B l b := past_block hc hbB hlB hlp
    exact ⟨b, hbB, hcr, hbo, hlb, hne⟩

/-- **`quorum_of_ratifies`** — the deployed count transfers to the algebra's lace-read count. -/
theorem quorum_of_ratifies {B : Lace} {rnd : Nat → Nat} {ps : List AuthorId} {wl : Nat}
    {o l : Block}
    (hc : B.Canonical) (hnd : ps.Nodup) (hoB : o ∈ B) (hlB : l ∈ B)
    (hne : LeaderNotGlobalEquivocator B l)
    (hrat : ratifies B ps o l = true) :
    superMajority ps.length
      ≤ (CordialState.ratifyingVoters ⟨B, rnd, ps, wl⟩ o l).length := by
  classical
  rw [ratifies_eq] at hrat
  have hcount : superMajority ps.length ≤ (ps.filter (RatifierRead B ps o l)).length :=
    of_decide_eq_true hrat
  refine le_trans hcount ?_
  have hsub : ps.filter (RatifierRead B ps o l)
      ⊆ CordialState.ratifyingVoters ⟨B, rnd, ps, wl⟩ o l := by
    intro p hp
    rw [List.mem_filter] at hp
    unfold CordialState.ratifyingVoters
    rw [List.mem_dedup, List.mem_filter]
    refine ⟨hp.1, ?_⟩
    simpa using decide_eq_true (hasApprovingBlock_of_ratifierRead hc hoB hlB hne hp.2)
  exact ((List.Nodup.filter _ hnd).subperm hsub).length_le

/-- **`exists_ratifying_observer`** — `is_super_ratified` returning `true` MEANS at least one
wave-end block of the lace ratifies the leader (the supermajority is `≥ 1`). This is all the
bridge needs from the outer quorum: the algebra asks for ONE observer, the node exhibits many.

⚑ STRENGTHENED UPSTREAM (HORIZONLOG B6). This used to be the strongest statement available, and a
SYBIL SATISFIED IT: before `BlocklaceFinality.ratifiesEnrolled`, `isSuperRatified` counted the
wave-end creators with no enrollment check, so the observer this theorem exhibits could be a
non-participant — and on `BlocklaceFinality.traceSybilOnly` EVERY exhibited observer was. The rule
now gates the ratifier, so `superRatified_exists_enrolled_ratifier` exhibits an ENROLLED one; this
theorem is its projection, kept because the bridge's consumers only need the `ratifies` half. -/
theorem exists_ratifying_observer {B : Lace} {ps : List AuthorId} {l : Block} {r : Nat}
    (hsr : isSuperRatified B ps l r = true) :
    ∃ o ∈ B, ratifies B ps o l = true := by
  obtain ⟨o, hoB, _, hrat⟩ := superRatified_exists_enrolled_ratifier hsr
  exact ⟨o, hoB, hrat⟩

/-- **`finalLeaderAt_spec`** — unpacking the node's per-wave commit decision: a unique
leader-slot candidate AND super-ratification by the wave end. -/
theorem finalLeaderAt_spec {B : Lace} {ps : List AuthorId} {wave wl : Nat} {l : Block}
    (h : finalLeaderAt B ps wave wl = some l) :
    leaderCandidates B ps wave wl = [l] ∧ isSuperRatified B ps l (waveLastRound wave wl) = true := by
  unfold finalLeaderAt at h
  cases hlc : leaderCandidates B ps wave wl with
  | nil => rw [hlc] at h; simp at h
  | cons a t =>
    cases t with
    | cons b t' => rw [hlc] at h; simp at h
    | nil =>
      rw [hlc] at h
      have h' : (if isSuperRatified B ps a (waveLastRound wave wl) = true then some a else none)
          = some l := h
      by_cases hsr : isSuperRatified B ps a (waveLastRound wave wl) = true
      · rw [if_pos hsr] at h'
        obtain rfl := Option.some_inj.mp h'
        exact ⟨rfl, hsr⟩
      · rw [if_neg hsr] at h'; simp at h'

/-- **`mem_leaderCandidates_iff`** — what `leader_blocks` (`ordering.rs:396..403`) actually
collects: the round-robin leader's blocks at the wave-START round. Stated as an iff so the
`len() == 1` guard can be read in BOTH directions. -/
theorem mem_leaderCandidates_iff {B : Lace} {ps : List AuthorId} {wave wl : Nat} {b : Block} :
    b ∈ leaderCandidates B ps wave wl ↔
      ∃ lk, waveLeader wave ps = some lk ∧ b ∈ B ∧ b.creator = lk ∧
        roundOf B ps b.id = waveFirstRound wave wl := by
  unfold leaderCandidates
  cases hwl : waveLeader wave ps with
  | none => simp
  | some lk =>
    -- the goal is DEFEQ to this (the `match some lk` iota-reduces, the `have ws` zeta-reduces)
    have hgoal :
        (b ∈ B.filter (fun x => x.creator == lk && roundOf B ps x.id == waveFirstRound wave wl)) ↔
          ∃ lk', some lk = some lk' ∧ b ∈ B ∧ b.creator = lk' ∧
            roundOf B ps b.id = waveFirstRound wave wl := by
      rw [List.mem_filter]
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨hb, hcr, hrd⟩; exact ⟨lk, rfl, hb, hcr, hrd⟩
      · rintro ⟨lk', hwl', hb, hcr, hrd⟩
        obtain rfl := Option.some_inj.mp hwl'
        exact ⟨hb, hcr, hrd⟩
    exact hgoal

/-- A committed leader is a block of the lace — read straight off the candidate list. -/
theorem mem_lace_of_finalLeaderAt {B : Lace} {ps : List AuthorId} {wave wl : Nat} {l : Block}
    (h : finalLeaderAt B ps wave wl = some l) : l ∈ B := by
  obtain ⟨hlc, _⟩ := finalLeaderAt_spec h
  have : l ∈ leaderCandidates B ps wave wl := by rw [hlc]; simp
  obtain ⟨_, _, hb, _, _⟩ := mem_leaderCandidates_iff.mp this
  exact hb

/-- **`unique_leader_of_finalLeaderAt`** — the `leader_blocks.len() == 1` guard of
`find_all_final_leaders` IS the algebra's `unique_leader` field. This is the axis on which
`isSuperRatified` alone has nothing at all to say. -/
theorem unique_leader_of_finalLeaderAt {B : Lace} {ps : List AuthorId} {wave wl : Nat} {l : Block}
    (h : finalLeaderAt B ps wave wl = some l) :
    ∀ b ∈ B, b.creator = l.creator → roundOf B ps b.id = roundOf B ps l.id → b = l := by
  obtain ⟨hlc, _⟩ := finalLeaderAt_spec h
  intro b hbB hcr hrd
  have hlmem : l ∈ leaderCandidates B ps wave wl := by rw [hlc]; simp
  obtain ⟨lk, hwl, _, hlcr, hlrd⟩ := mem_leaderCandidates_iff.mp hlmem
  have hbmem : b ∈ leaderCandidates B ps wave wl :=
    mem_leaderCandidates_iff.mpr ⟨lk, hwl, hbB, hcr.trans hlcr, hrd.trans hlrd⟩
  rw [hlc, List.mem_singleton] at hbmem
  exact hbmem

/-- **`committed_of_finalLeaderAt` — THE BRIDGE.** The block the node's wave loop pushes onto
`final_leaders` IS `Committed` in the algebra `Consensus.Safety` proves safety on. Under two
NAMED hypotheses (§2) and `Lace.Canonical`, and fully general in `n`, `f`, `B`, `participants`
and `wavelength`. -/
theorem committed_of_finalLeaderAt {B : Lace} {ps : List AuthorId} {wave wl : Nat} {l : Block}
    {cfg : Finality.Config}
    (hc : B.Canonical) (hnd : ps.Nodup)
    (hthr : ThresholdAgrees cfg ps)
    (hne : LeaderNotGlobalEquivocator B l)
    (hfin : finalLeaderAt B ps wave wl = some l) :
    Committed (deployedState B ps wl) cfg l := by
  obtain ⟨_, hsr⟩ := finalLeaderAt_spec hfin
  obtain ⟨o, hoB, hrat⟩ := exists_ratifying_observer hsr
  have hlB : l ∈ B := mem_lace_of_finalLeaderAt hfin
  refine ⟨{ observer := o, observer_mem := hoB, quorum_from_lace := ?_,
            unique_leader := unique_leader_of_finalLeaderAt hfin }⟩
  exact le_trans hthr (quorum_of_ratifies hc hnd hoB hlB hne hrat)

/-! ### §3b. From the bridge to the apex: the node's OWN history satisfies `FinalizedBy`. -/

/-- **`deployedHistory`** — the `(wave, leader)` history the node's wave loop produces. Exactly
`findAllFinalLeaders`' loop (`ordering.rs:283..336`), keeping the wave index the apex's
`leaderAtWave` reads. -/
def deployedHistory (B : Lace) (ps : List AuthorId) (wl : Nat) : Safety.FinalizedHistory :=
  let waveCount := if wl == 0 then 0 else maxRound B ps / wl + 1
  (List.range waveCount).filterMap (fun w => (finalLeaderAt B ps w wl).map (fun l => (w, l)))

/-- Reading a leader off the deployed history means the node's per-wave rule returned it. -/
theorem finalLeaderAt_of_deployedHistory {B : Lace} {ps : List AuthorId} {wl w : Nat} {l : Block}
    (h : Safety.leaderAtWave (deployedHistory B ps wl) w = some l) :
    finalLeaderAt B ps w wl = some l := by
  have hmem := Safety.leaderAtWave_mem h
  unfold deployedHistory at hmem
  simp only [List.mem_filterMap, Option.map_eq_some_iff] at hmem
  obtain ⟨w', _, l', hl', heq⟩ := hmem
  have hw : w' = w := congrArg Prod.fst heq
  have hl : l' = l := congrArg Prod.snd heq
  subst hw; subst hl; exact hl'

/-- **`finalizedBy_deployedHistory`** — the apex's `FinalizedBy` premise, DISCHARGED from the
deployed finalizer. Before this, `FinalizedBy` had no supplier: nothing in the tree connected a
node's actual `findAllFinalLeaders` output to `Committed`. -/
theorem finalizedBy_deployedHistory {B : Lace} {ps : List AuthorId} {wl : Nat}
    {cfg : Finality.Config}
    (hc : B.Canonical) (hnd : ps.Nodup) (hthr : ThresholdAgrees cfg ps)
    (hne : ∀ w l, finalLeaderAt B ps w wl = some l → LeaderNotGlobalEquivocator B l) :
    Safety.FinalizedBy (deployedState B ps wl) cfg (deployedHistory B ps wl) := by
  intro w l hw
  have hfin := finalLeaderAt_of_deployedHistory hw
  exact committed_of_finalLeaderAt hc hnd hthr (hne w l hfin) hfin

/-- **`deployed_nodes_no_conflicting_history` — THE CAPSTONE.** Two nodes, each holding its own
lace, each running the DEPLOYED finalizer (`finalLeaderAt` / `findAllFinalLeaders`, the rule
behind `@[export] dregg_tau_order`), never disagree on a finalized wave's leader.

The carriers are exactly the apex's — `n > 3f`, `CrossNodeCanonical`, the union BFT model —
PLUS the two this bridge costs. Nothing is assumed about the histories: they are computed from
the laces by the node's own rule. -/
theorem deployed_nodes_no_conflicting_history
    (cfg : Finality.Config) (B₁ B₂ : Lace) (ps : List AuthorId) (wl : Nat)
    (h3f : cfg.n > 3 * cfg.f)
    (hc₁ : B₁.Canonical) (hc₂ : B₂.Canonical) (hnd : ps.Nodup)
    (hthr : ThresholdAgrees cfg ps)
    (hne₁ : ∀ w l, finalLeaderAt B₁ ps w wl = some l → LeaderNotGlobalEquivocator B₁ l)
    (hne₂ : ∀ w l, finalLeaderAt B₂ ps w wl = some l → LeaderNotGlobalEquivocator B₂ l)
    (hcross : Safety.CrossNodeCanonical (deployedState B₁ ps wl) (deployedState B₂ ps wl))
    (bft : ∀ w l₁ l₂,
      Safety.leaderAtWave (deployedHistory B₁ ps wl) w = some l₁ →
      Safety.leaderAtWave (deployedHistory B₂ ps wl) w = some l₂ →
      ∀ (c₁ : Committed (deployedState B₁ ps wl) cfg l₁)
        (c₂ : Committed (deployedState B₂ ps wl) cfg l₂),
        Proof.BFT.BFTModel cfg ((SuperRatification.ofLace c₁.some).votes
          ++ (SuperRatification.ofLace c₂.some).votes)) :
    Safety.Consistent (deployedHistory B₁ ps wl) (deployedHistory B₂ ps wl) :=
  Safety.no_conflicting_finalized_history_of_committed cfg _ _ _ _ h3f
    (finalizedBy_deployedHistory hc₁ hnd hthr hne₁)
    (finalizedBy_deployedHistory hc₂ hnd hthr hne₂) hcross bft

/-! ## §4. MODELS — satisfiability, and the refutations. `n = 4, f = 1`, one wave.

Everything here that is a THEOREM is round-FREE, because `roundOf` did not kernel-reduce when
these were written (see the header: it does now). The round-dependent facts are `#guard`s —
COMPILER checks, not proofs — and are labelled as such. -/

namespace Model

/-- The wave-0 leader: author `7`, the round-robin `participants[0]`. Genesis (`preds = []`). -/
def leader : Block := ⟨100, 7, 0, [], true⟩
/-- An independent genesis block by a non-participant, so the fork below has somewhere to attach
that does NOT observe the leader. -/
def other : Block := ⟨90, 8, 0, [], true⟩
/-- Three approvers, authors `0/1/2`, each acking the leader directly. -/
def ra0 : Block := ⟨110, 0, 1, [100], true⟩
def ra1 : Block := ⟨111, 1, 1, [100], true⟩
def ra2 : Block := ⟨112, 2, 1, [100], true⟩
/-- Three wave-end observers, authors `0/1/2`, each acking all three approvers. -/
def ro0 : Block := ⟨120, 0, 2, [110, 111, 112], true⟩
def ro1 : Block := ⟨121, 1, 2, [110, 111, 112], true⟩
def ro2 : Block := ⟨122, 2, 2, [110, 111, 112], true⟩
/-- An independent genesis block by an ENROLLED author (`2`) that does NOT observe the leader —
present in `forked` ONLY, so `honest` and every theorem about it are untouched.

⚑ **Why it exists** (the participant-filtered wave clock, `BlocklaceFinality.computeRounds`). This
model's fork used to attach to `other`, a NON-PARTICIPANT genesis. Under the pre-filter recurrence
that gave the fork round `2` and the leader slot (round `1`) stayed a singleton, so the node
finalized and §4b's coverage hole had its witness. Under the filtered clock a block whose ENTIRE
ancestry is outside the committee has committee-depth `0` and sits at round `1` — so the fork
collides with `leader` AT THE LEADER SLOT, `leader_blocks.len() == 1` fails, and the node correctly
refuses the wave. That is a STRENGTHENING (a fork rooted wholly outside the committee is now visible
where it decides something), and it is NOT a closure of `OPEN-CM-LOCAL-EQUIVOCATION`: a fork with
genuine in-committee depth still sits at its own round and is still invisible to the observer-local
guard. `freeBlk` gives this fork exactly that depth, so the witness keeps witnessing the hole that
is actually open rather than one the clock now catches. -/
def freeBlk : Block := ⟨91, 2, 7, [], true⟩
/-- **The HIDDEN FORK**: a second author-`7` block, attached to `freeBlk`, hence incomparable with
`leader` — and NOT in any observer's causal past, so `hasEquivInPast` never sees it. -/
def forkBlk : Block := ⟨130, 7, 9, [91], true⟩

/-- The honest lace: no author-`7` fork. -/
def honest : Lace := [leader, other, ra0, ra1, ra2, ro0, ro1, ro2]
/-- The forked lace: `honest` plus the hidden author-`7` equivocation and the independent enrolled
genesis it hangs from. Both additions are `forked`-only. -/
def forked : Lace := forkBlk :: freeBlk :: honest

/-- `participants[0] = 7`, so author `7` is the wave-0 round-robin leader. -/
def parts : List AuthorId := [7, 0, 1, 2]
/-- `n = 4`, `f = 1` — the canonical band, where `superMajority 4 = 3 = n − f`. -/
def cfg : Finality.Config := ⟨4, 1, 3⟩

theorem honest_canonical : honest.Canonical := by decide
theorem forked_canonical : forked.Canonical := by decide
theorem parts_nodup : parts.Nodup := by decide
theorem threshold_holds : ThresholdAgrees cfg parts := by decide

/-! ### 4a. SATISFIABILITY — the bridge FIRES, kernel-checked, on the honest lace.

`ratifies` is round-free HERE by construction: the equivocation guard scans the author-`7` blocks
in the observer's past, of which there is exactly ONE, so the `a.id ≠ b.id` test short-circuits
before `roundOf` is ever forced. This is why the model puts the leader on its own author. -/

/-- The node's `ratifies` fires at the full supermajority — COMPUTED. -/
theorem honest_ratifies : ratifies honest parts ro0 leader = true := by decide

/-- Author `7` has exactly one block in the honest lace, so it is no equivocator. -/
theorem honest_only_leader_by_7 : ∀ b ∈ honest, b.creator = 7 → b = leader := by decide

theorem honest_no_equiv : LeaderNotGlobalEquivocator honest leader := by
  rintro ⟨a, b, ha, hb, hac, hbc, hinc⟩
  have hae : a = leader := honest_only_leader_by_7 a (lookup_mem ha) hac
  have hbe : b = leader := honest_only_leader_by_7 b (lookup_mem hb) hbc
  exact hinc.1 (hae.trans hbe.symm)

/-- **The bridge's premises are JOINTLY SATISFIABLE and its conclusion is REACHED.** No
`finalLeaderAt` here — that would force `roundOf`; the model feeds the round-free core directly,
with the unique-leader guard discharged from the lace and holding for EVERY round map. -/
theorem bridge_fires :
    Committed ⟨honest, roundOf honest parts, parts, 3⟩ cfg leader := by
  refine ⟨{ observer := ro0, observer_mem := by decide, quorum_from_lace := ?_,
            unique_leader := ?_ }⟩
  · exact le_trans threshold_holds
      (quorum_of_ratifies honest_canonical parts_nodup (by decide) (by decide)
        honest_no_equiv honest_ratifies)
  · intro b hbB hcr _
    exact honest_only_leader_by_7 b hbB hcr

-- Compiler-level (NOT kernel) confirmation that the honest model is a real run of the deployed
-- rule: the node's own per-wave decision returns this leader. `#guard` evaluates OUTSIDE the
-- kernel — see the header. This is a test, not a proof.
#guard finalLeaderAt honest parts 0 3 == some leader

/-! ### 4b. REFUTATION — the node still ratifies; `Committed` is FALSE.

Same lace plus one hidden author-`7` fork. The node's observer `ro0` is UNCHANGED and still
ratifies at the full supermajority (its causal past does not contain the fork, so
`hasEquivInPast` is blind to it). The algebra's `Equivocator` is global, sees it, and empties the
ratifier list. -/

/-- The fork is genuinely an equivocation: two distinct author-`7` blocks, neither observing the
other (`leader` is genesis; `forkBlk`'s only predecessor is the non-leader genesis `freeBlk`). -/
theorem forked_is_equivocator : Equivocator forked 7 := by
  refine ⟨leader, forkBlk, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · decide
  · -- ¬ precedes forked leader forkBlk : the only way down from `forkBlk` is `freeBlk`, a genesis
    intro hpre
    obtain ⟨p, hp, hcase⟩ := precedes_inv hpre
    have hp' : p = 91 := by simpa [forkBlk] using hp
    subst hp'
    rcases hcase with hid | ⟨m, hm, hpm⟩
    · exact absurd hid (by decide)
    · have hmo : m = freeBlk := by
        have : (forked.lookup 91) = some freeBlk := by decide
        rw [this] at hm; exact (Option.some_inj.mp hm).symm
      subst hmo
      exact precedes_preds_ne_nil hpm (by decide)
  · -- ¬ precedes forked forkBlk leader : `leader` is genesis, nothing precedes it
    intro hpre
    exact precedes_preds_ne_nil hpre (by decide)

/-- Top-level `¬`-form of the refutation, so `#floor_census` Pass 0b sees it WITHOUT descending
into a conjunction — the shape the cross-canonicity family had to be hand-registered for. -/
theorem leaderNotGlobalEquivocator_refuted : ¬ LeaderNotGlobalEquivocator forked leader :=
  fun h => h forked_is_equivocator

/-- **THE NODE STILL RATIFIES** — `decide`d on the forked lace, at the same observer, at the same
full supermajority. The deployed guard is observer-local and the fork is outside `ro0`'s past. -/
theorem forked_node_still_ratifies : ratifies forked parts ro0 leader = true := by decide

/-- **AND THE ALGEBRA DOES NOT COMMIT IT** — for every round map, so this is not an artifact of
the round computation the kernel cannot see. -/
theorem forked_is_not_committed (rnd : Nat → Nat) (wl : Nat) :
    ¬ Committed ⟨forked, rnd, parts, wl⟩ cfg leader :=
  not_committed_of_equivocator (by decide) forked_is_equivocator

-- Compiler-level (NOT kernel) confirmation that the node FINALIZES on the forked lace too — the
-- fork sits at a different round from the leader slot, so `leader_blocks.len() == 1` still holds.
-- This is the whole coverage hole in one line: the node commits, the theorem is silent.
#guard finalLeaderAt forked parts 0 3 == some leader

/-! ### 4c. `isSuperRatified` ALONE is not the bridgeable object.

It carries no unique-leader guard, so it cannot imply `Committed` on any lace where the leader
slot is contested. Stated round-free: whatever the round map, if two distinct blocks by the
leader's author share a round, `unique_leader` fails and `Committed` is false — while
`isSuperRatified` (which never looks at the leader slot) is untouched. -/

/-- **`superRatified_alone_is_not_committed`** — a leader-slot equivocation refutes `Committed`
without touching the ratifier read at all. `isSuperRatified` inspects only wave-END blocks; the
guard that would catch this lives in `finalLeaderAt`, which is why the bridge is stated there. -/
theorem superRatified_alone_is_not_committed
    {B : Lace} {rnd : Nat → Nat} {ps : List AuthorId} {wl : Nat} {cfg : Finality.Config}
    {l l' : Block} (hmem : l' ∈ B) (hcr : l'.creator = l.creator)
    (hrd : rnd l'.id = rnd l.id) (hne : l' ≠ l) :
    ¬ Committed ⟨B, rnd, ps, wl⟩ cfg l := by
  rintro ⟨sr⟩
  exact hne (sr.unique_leader l' hmem hcr hrd)

/-- The refutation is inhabited on the model's own shape: two author-`7` blocks at a common round
value. (`rnd := fun _ => 1` is a legitimate round map for the statement's purposes — the point is
that `Committed` fails for SOME round map the `CordialState` field can hold, which is exactly the
generality `CordialState.rounds` was given.) -/
theorem superRatified_alone_refuted :
    ¬ Committed ⟨forked, fun _ => 1, parts, 3⟩ cfg leader :=
  superRatified_alone_is_not_committed (B := forked) (l := leader) (l' := forkBlk)
    (by decide) (by decide) rfl (by decide)

end Model

/-! ## §5. Axiom hygiene — every load-bearing theorem pinned. -/

#assert_axioms precedes_preds_ne_nil
#assert_axioms precedes_inv
#assert_axioms causalPastIncl_sound
#assert_axioms past_block
#assert_axioms thresholdAgrees_of_canonical_bft
#assert_axioms thresholdAgrees_fails_at_3f_plus_4
#assert_axioms not_committed_of_equivocator
#assert_axioms hasApprovingBlock_of_ratifierRead
#assert_axioms quorum_of_ratifies
#assert_axioms exists_ratifying_observer
#assert_axioms unique_leader_of_finalLeaderAt
#assert_axioms committed_of_finalLeaderAt
#assert_axioms finalizedBy_deployedHistory
#assert_axioms deployed_nodes_no_conflicting_history
#assert_axioms Model.bridge_fires
#assert_axioms Model.forked_is_equivocator
#assert_axioms Model.leaderNotGlobalEquivocator_refuted
#assert_axioms Model.forked_node_still_ratifies
#assert_axioms Model.forked_is_not_committed
#assert_axioms Model.superRatified_alone_refuted

end Dregg2.Consensus.SuperRatifyBridge
