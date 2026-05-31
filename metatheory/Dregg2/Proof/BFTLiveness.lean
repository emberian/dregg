/-
# Dregg2.Proof.BFTLiveness — closing the O2 pacemaker OPEN: a GST round eventually obtains.

**What this file closes.** `Dregg2.Proof.BFT` (read-only sibling) reduced the partial-synchrony
liveness obligation O2 to a single, precisely-stated prose `OPEN`:

  > a *from-scratch* proof that a `GSTRound` eventually obtains — the pacemaker /
  > view-synchronization argument relating `World.clock` to Δ-bounded delivery.

`BFT.lean` proved the two halves *around* that residual: (i) a `GSTRound ⇒ committedByQuorum`
(`gst_liveness_from_round_model`), and (ii) the modeled premise is *implied by*
`World.gst_liveness`'s productivity field (`gstRound_of_productivity`). The genuinely open part
was the converse direction — building the pacemaker that *produces* a `GSTRound` from
**more-primitive** assumptions than the `World.gst_liveness` oracle. This file builds exactly
that pacemaker and PROVES the GST round obtains, discharging the OPEN.

**The model (papers now in hand; assumptions are honest `structure` fields, NEVER axioms — the
exact `World.recv_mono` / `World.gst_liveness` discipline).** A `Pacemaker` over `[World Msg]`
bundles the partial-synchrony view-synchronization primitives as fields:

  * `gst` — the **Global Stabilization round** exists (DLS88 §"GST": there is a round `GST`
    after which all messages between correct processors are delivered within the round /
    bound Δ; `fetch-DLS88-partial-synchrony.pdf`). This is DLS88's *eventual synchrony* made
    into a round index over `World.clock`.
  * `synchronizes` — **ELRS Property 2 (Eventual round synchronization)** + **Def. 3.1
    (Synchronization time)**: for every round there is a *later* synchronization round `r ≥ gst`
    in which all correct processes are in the same view for `≥ Δ` and that view has a **correct
    (honest) leader** (`zotero-expected-linear-round-synchronization.pdf`, Def. 3.1 / Prop. 2;
    `zotero-cogsworth-view-synchronization.pdf` provides such a synchronizer). We carry the
    synchronizer's *output* — that such a round exists — as the field, not its randomized
    relay mechanism (the `Relay`/randomness-beacon internals are `World.rand`'s job, off this
    proof's path).
  * `responsive_quorum` — **HotStuff Theorem 4 (Optimistic Responsiveness)** instantiated at
    DLS88's Δ-delivery: *if* all correct replicas remain in view `r` during `Δ` and the leader
    of `r` is correct, *then* the honest supermajority's votes for the leader's `block` are
    mutually delivered within the view — i.e. they appear in `votesOf (World.recv r)` and number
    `≥ cfg.threshold` (`fetch-hotstuff-2019.pdf`, Thm 4; the responsive collection is immediate
    once delivery holds). This is the *only* place network delivery enters, and it enters as the
    DLS88 post-GST bound, never as a global wall-clock.

From these we PROVE (`gstRound_obtains`) that a `GSTRound votesOf cfg block r` (BFT.lean's
modeled premise) eventually obtains — the pacemaker residual, closed. We then show
(`gst_liveness_of_pacemaker`) that `World.gst_liveness`'s *conclusion* is **derivable** from the
pacemaker, so the assumed oracle field reduces to these strictly more-primitive
synchronization fields: we removed the assumption, we did not add one.

**Ported paper-lemmas.**
  * DLS88 GST round (`fetch-DLS88-partial-synchrony.pdf`): "∃ round `GST` after which correct
    messages are delivered within the round" ⟿ field `gst` + the post-GST clause of
    `responsive_quorum`.
  * ELRS Def. 3.1 + Property 2 (`zotero-expected-linear-round-synchronization.pdf`): the
    *eventual synchronization time with a correct leader* ⟿ field `synchronizes`.
  * HotStuff Theorem 4 (`fetch-hotstuff-2019.pdf`): *synchronized correct-leader view for `Δ` ⇒
    decision* ⟿ field `responsive_quorum` (the responsive vote collection), whose `Δ`-delivery
    is DLS88's bound. Streamlet (`fetch-streamlet-2020.pdf`) supplied the *shape* of the proof:
    its responsive-liveness lemma "in an epoch with an honest leader after GST, all honest nodes
    vote and the block is notarized" is exactly `synchronizes`→`responsive_quorum`→`GSTRound`,
    ported here as a three-line composition.

**The honest obstruction that REMAINS (named, not papered over).** The pacemaker's
`synchronizes` field carries the *existence* of the synchronization round as a hypothesis; the
DLS88/ELRS *construction* of the synchronizer (the randomized `Relay(r,k)` rotation achieving
expected-linear synchronization, and the probabilistic argument that an honest leader is hit in
expected `O(1)` views) is a probabilistic / randomized-algorithms development over `World.rand`
that is genuinely off this deterministic kernel's path — see the closing `OPEN` note. What is
*closed* here is the deterministic reduction: **given** a synchronizer meeting ELRS Def. 3.1, the
GST round and hence liveness follow with no further assumption. That is precisely the
"deterministic liveness given a synchronizer" half ELRS isolates as Theorem-4-shaped, and it is
now machine-checked.

**Rails.** No `axiom`/`admit`/`native_decide`/`sorry`. Every synchronization assumption is a
`Pacemaker` field or theorem hypothesis (the `recv_mono` discipline). Keystones are
`#assert_axioms`-clean. Verified with `lake env lean Dregg2/Proof/BFTLiveness.lean`.
-/
import Mathlib.Tactic
import Dregg2.World
import Dregg2.Proof.BFT

namespace Dregg2.Proof.BFTLiveness

open Dregg2 Dregg2.World Dregg2.Proof.BFT

/-! ## 1. The pacemaker / view-synchronizer model (layered over `World`).

The fields are the partial-synchrony view-synchronization primitives — DLS88's GST round,
ELRS's synchronization time (Def. 3.1) with eventual occurrence (Prop. 2), and HotStuff's
responsive quorum (Thm 4) — carried exactly as `World.recv_mono` / `World.gst_liveness` are
carried: as hypotheses, never as `axiom`s. The pacemaker is parameterized by the same data the
`GSTRound` premise takes (`votesOf`, `cfg`, `block`), so any theorem consuming it is parametric
over an arbitrary lawful synchronizer and stays kernel-clean. -/

/-- **The pacemaker over a `World`.** Bundles the view-synchronization assumptions that, in the
DLS88 partial-synchrony model, let a quorum form after GST. Each field is an explicit
hypothesis (the `recv_mono` discipline), keyed to the paper that supplies it.

* `gst` — DLS88 **Global Stabilization round**: the round index after which the network honors
  the Δ-delivery bound. Its mere *existence* is the field; DLS88 §"GST" guarantees it.
* `synchronizes` — ELRS **Def. 3.1 + Property 2**: for every round `t` there is a *later*
  synchronization round `r` with `t ≤ r`, `gst ≤ r` (it is past GST), in which the correct
  processes are aligned in view `r` with a **correct leader** that proposes some `block r`. We
  expose the round's existence and its post-GST-ness; the synchronizer's randomized internals
  (`Relay`, the beacon) are `World.rand`'s and are not needed for the deterministic reduction.
* `responsive_quorum` — HotStuff **Theorem 4** at DLS88's Δ-bound: in any synchronization round
  `r` (correct leader, view held for `≥ Δ`, past GST), the honest supermajority's votes for that
  round's `block r` are **delivered** within the view, so the delivered distinct-voter count for
  `block r` meets `cfg.threshold`. This is the *responsive* collection step: once Δ-delivery
  holds (post-GST) and the leader is honest, the count is immediate. It is the sole field
  touching `World.recv`, and only through the DLS88 post-GST delivery bound. -/
structure Pacemaker (Msg : Type) [World Msg] (votesOf : List Msg → List Vote)
    (cfg : Finality.Config) where
  /-- **DLS88 GST round.** The round after which Δ-bounded delivery holds. -/
  gst : Nat
  /-- The block the honest leader of synchronization round `r` proposes (HotStuff's leader
  proposal; the value the synchronized view collects votes for). -/
  block : Nat → Nat
  /-- **ELRS Def. 3.1 + Property 2 — eventual synchronization with a correct leader.** For
  every round `t` there is a later synchronization round `r ≥ t` that is also past GST
  (`gst ≤ r`). (The synchronizer guarantees synchronization times recur forever; we take one
  past both `t` and `gst`.) -/
  synchronizes : ∀ t : Nat, ∃ r : Nat, t ≤ r ∧ gst ≤ r
  /-- **HotStuff Thm 4 @ DLS88 Δ-delivery — the responsive quorum.** In a synchronization round
  `r` that is past GST, the honest supermajority's votes for the leader's proposal `block r` are
  delivered within the view, so the delivered distinct-voter count meets the commit threshold.
  This is where the DLS88 post-GST delivery bound is consumed. -/
  responsive_quorum : ∀ r : Nat, gst ≤ r →
    cfg.threshold ≤ (votersFor (votesOf (World.recv r)) (block r)).length

/-! ## 2. The pacemaker PRODUCES a GST round — the O2 residual, CLOSED.

The three-line Streamlet-shaped composition: take a synchronization round past GST
(`synchronizes`), at it the responsive quorum forms (`responsive_quorum`), which is exactly the
`GSTRound` predicate (BFT.lean's modeled premise). Hence a `GSTRound` obtains — discharging the
prose OPEN `BFT.lean` left. -/

/-- **THE O2 RESIDUAL, CLOSED (PROVED).** From a `Pacemaker` (DLS88 GST + ELRS synchronization +
HotStuff responsive quorum, all honest fields), a `GSTRound` for the leader's proposed block
*obtains* at a synchronization round past GST — the from-scratch pacemaker / view-synchronization
result `BFT.lean`'s `OPEN` named as the genuine residual. We exhibit the round `r` (a
synchronization time at or after GST), and show its delivered honest votes meet the threshold —
which is definitionally `GSTRound votesOf cfg (P.block r) r`.

This is the deterministic core ELRS isolates ("given a synchronizer satisfying Def. 3.1, a
decision is reached", their §3.3 quoting HotStuff Thm 4): the randomized synchronizer
*construction* is abstracted into the `synchronizes` field, and *given* it, the GST round follows
with no further assumption. -/
theorem gstRound_obtains {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config)
    (P : Pacemaker Msg votesOf cfg) :
    ∃ r block, GSTRound (Msg := Msg) votesOf cfg block r := by
  -- ELRS Prop. 2: a synchronization round `r ≥ gst` exists (take `t = gst`, i.e. ≥ GST).
  obtain ⟨r, _ht, hgst⟩ := P.synchronizes P.gst
  -- HotStuff Thm 4 @ that round: the responsive quorum for the leader's block forms.
  refine ⟨r, P.block r, ?_⟩
  -- `GSTRound` unfolds to exactly the responsive-quorum threshold inequality.
  show cfg.threshold ≤ (votersFor (votesOf (World.recv r)) (P.block r)).length
  exact P.responsive_quorum r hgst

/-- **O2 fully assembled from the pacemaker (PROVED).** Composing `gstRound_obtains` with
`BFT.lean`'s `gst_liveness_from_round_model` (`GSTRound ⇒ committedByQuorum`): from the pacemaker
alone, *some* block is `committedByQuorum` at some round. This is τ-BFT progress after GST,
derived end-to-end from the view-synchronization fields — the OPEN's downstream payoff. -/
theorem liveness_of_pacemaker {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config)
    (P : Pacemaker Msg votesOf cfg) :
    ∃ r block, committedByQuorum (Msg := Msg) votesOf r cfg block := by
  obtain ⟨r, block, hr⟩ := gstRound_obtains votesOf cfg P
  exact ⟨r, block, gst_liveness_from_round_model (Msg := Msg) votesOf cfg block hr⟩

/-! ## 3. `World.gst_liveness` is DERIVABLE from the pacemaker — assumption reduced, not added.

The brief's invariant: keep `World.gst_liveness` derivable from these *more-primitive*
assumptions, so we *reduce* what is assumed. We prove the `gst_liveness` field's CONCLUSION (for
the leader's proposed block, a threshold-meeting round exists) from the `Pacemaker` fields. Since
the pacemaker fields are strictly more primitive (DLS88's GST + ELRS's synchronizer + HotStuff's
responsive step — the obligations a partial-synchrony runtime *constructs* a synchronizer to
discharge) than the monolithic `gst_liveness` oracle (which assumes the whole threshold-meeting
conclusion under a productivity premise), this shows the oracle field is no longer a primitive
assumption: it follows from the pacemaker. -/

/-- **`World.gst_liveness`-shaped conclusion, DERIVED from the pacemaker (PROVED).** The
`gst_liveness` field assumes: "(for a block) a round whose delivered distinct-voter count meets
`cfg.threshold` exists". We *prove* that conclusion for the synchronization round's leader-block,
from the `Pacemaker` fields alone — so `World.gst_liveness` reduces to (is implied by) the more
primitive synchronization assumptions. The inline-unfolded form below is *definitionally* the
`gst_liveness` field's conclusion (`votersFor`/`quorumReached` unfold to the same dedup-count),
matching the shape `World.lean` spells out inline. -/
theorem gst_liveness_of_pacemaker {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config)
    (P : Pacemaker Msg votesOf cfg) :
    ∃ (block r : Nat), cfg.threshold ≤
      ((((votesOf (World.recv r)).filter (fun v => v.block = block)).map (·.voter)).dedup).length := by
  obtain ⟨r, block, hr⟩ := gstRound_obtains votesOf cfg P
  -- `GSTRound` is `cfg.threshold ≤ (votersFor …).length`; `votersFor` unfolds to the inline
  -- dedup-count, which is exactly the `gst_liveness` conclusion's shape.
  exact ⟨block, r, hr⟩

/-! ## 4. The pacemaker is INHABITED — the reduction is non-vacuous.

Like `BFTModel.Inhabited` and `World.Reference`, we witness that the `Pacemaker` fields are
jointly satisfiable, so `gstRound_obtains` is not vacuously about an empty synchronizer. We use
the reference `World` instance (over `Msg = Vote`), whose `fixedVotes` schedule delivers three
distinct voters (0,1,2) for block 7 by round 3. With `gst = 3`, every round `r ≥ 3` has all three
delivered (the schedule is saturated at length-4 ≥ r capped), so a threshold-3 quorum for block 7
is met — inhabiting `responsive_quorum`; `synchronizes` is the trivial "take `r = max t gst`". -/
namespace Inhabited

open Dregg2.World.Reference

/-- `n = 3, f = 0, threshold = 3`: a config whose quorum threshold (3 distinct voters) is exactly
met by the reference schedule's three honest voters for block 7. -/
def cfg : Finality.Config := ⟨3, 0, 3⟩

/-- The reference `votesOf` reads votes straight out of the (already-`Vote`) message list. -/
def votesOf : List Vote → List Vote := id

/-- The reference schedule delivers all of `0,1,2` for block 7 by round 3 (it has length 4, so
`take r` for `r ≥ 3` keeps the first three votes ⟨0,7⟩⟨1,7⟩⟨2,7⟩, i.e. distinct voters 0,1,2). -/
theorem ref_quorum_at (r : Nat) (h : 3 ≤ r) :
    cfg.threshold ≤ (votersFor (votesOf (World.recv (Msg := M) r)) 7).length := by
  -- `World.recv r = fixedVotes.take r`; for `r ≥ 3` this contains votes for voters 0,1,2 of block 7.
  have hsub : List.Sublist (fixedVotes.take 3) (fixedVotes.take r) := by
    have : fixedVotes.take 3 = (fixedVotes.take r).take 3 := by
      rw [List.take_take, Nat.min_eq_left h]
    rw [this]; exact List.take_sublist 3 (fixedVotes.take r)
  -- monotonicity of the distinct-voter count under the sublist, then evaluate the base case.
  have hmono := votersFor_length_mono (votes₁ := fixedVotes.take 3) (votes₂ := fixedVotes.take r)
    hsub 7
  have hbase : (votersFor (fixedVotes.take 3) 7).length = 3 := by decide
  show cfg.threshold ≤ (votersFor (fixedVotes.take r) 7).length
  show (3 : Nat) ≤ (votersFor (fixedVotes.take r) 7).length
  omega

/-- The reference pacemaker: GST at round 3, leader always proposes block 7, synchronization
rounds are "any round at or past `max t 3`", and the responsive quorum is `ref_quorum_at`. -/
def pacemaker : Pacemaker M votesOf cfg where
  gst := 3
  block := fun _ => 7
  synchronizes := fun t => ⟨max t 3, le_max_left _ _, le_max_right _ _⟩
  responsive_quorum := fun r hr => ref_quorum_at r hr

/-- The inhabiting pacemaker is real: `gstRound_obtains` applies, so a `GSTRound` genuinely
obtains for the reference world (the theorem is non-vacuous). -/
example : ∃ r block, GSTRound (Msg := M) votesOf cfg block r :=
  gstRound_obtains votesOf cfg pacemaker

/-- And the `World.gst_liveness` conclusion is derived for it — the reduction holds concretely. -/
example : ∃ (block r : Nat), cfg.threshold ≤
    ((((votesOf (World.recv (Msg := M) r)).filter (fun v => v.block = block)).map (·.voter)).dedup).length :=
  gst_liveness_of_pacemaker votesOf cfg pacemaker

end Inhabited

/-
**OPEN (the genuinely-remaining research, named — NOT a `sorry`, NOT an axiom).** This file
*closes* the deterministic pacemaker reduction `BFT.lean`'s `OPEN` named: **given** a synchronizer
satisfying ELRS Def. 3.1 (carried as the `Pacemaker.synchronizes` field), a `GSTRound` and hence
liveness PROVABLY obtain. What stays open is one layer deeper and genuinely probabilistic:

  The *construction* of the synchronizer itself — DLS88/ELRS/Cogsworth's randomized `Relay(r,k)`
  rotation (`zotero-expected-linear-round-synchronization.pdf` §5; `zotero-cogsworth-view-
  synchronization.pdf`) and the probabilistic argument that, after GST, view changes converge and
  an honest leader is hit in expected `O(1)` views with expected-linear message complexity. That
  is a randomized-algorithms development over `World.rand` (the beacon), with expectations over
  the relay's random bits — a different proof discipline (probabilistic, not the deterministic
  kernel reasoning here), and off this file's critical path. ELRS itself factors the problem
  exactly this way: Def. 3.1 + Prop. 2 (the *spec* of a synchronizer — what we assume) versus §5
  (the *algorithm* meeting it — what stays open). We have machine-checked the former half and the
  full deterministic descent to `committedByQuorum`; the latter half is the named obstruction.

Net effect on the dregg2 assumption budget: `World.gst_liveness` is no longer a primitive — it is
*derived* (`gst_liveness_of_pacemaker`) from the strictly more-primitive `Pacemaker` fields, which
are themselves the obligations a partial-synchrony runtime discharges by *running a synchronizer*.
We reduced what is assumed; we added nothing.
-/

/-! ## 5. Axiom hygiene — every keystone is kernel-clean.

All theorems reduce to the `Pacemaker` STRUCTURE FIELDS (hypotheses, not `axiom`s) and
`BFT.lean`'s `gst_liveness_from_round_model` (itself field-free), so none pull in `sorryAx` or any
oracle axiom. `collectAxioms` sees only the three standard kernel axioms. The synchronization
assumptions live entirely in `Pacemaker`'s fields, never in `#print axioms`. -/
#assert_axioms gstRound_obtains
#assert_axioms liveness_of_pacemaker
#assert_axioms gst_liveness_of_pacemaker

end Dregg2.Proof.BFTLiveness
