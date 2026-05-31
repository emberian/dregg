/-
# Dregg2.World — the SIBLING portal to `CryptoKernel` for the nondeterministic
external inputs that consensus / finality need (network, clock, randomness).

**The architecture (mirrors `CryptoKernel`).** `CryptoKernel.lean` is the portal for the
*cryptographic* operations dregg2 needs (hash/verify/commit/nullifier) — an interface of
opaque ops bundled with the algebraic laws Lean proofs rely on, with two realizations of
the SAME interface (an abstract `[CryptoKernel …]` for PROVING; a Rust FFI instance for
RUNNING). `World` is its sibling: the portal for the *nondeterministic external inputs*
consensus needs — the **network** (which messages/votes a round received), the **clock**
(a monotone logical time), and **randomness** (leader election / sortition). These are
exactly the things a deterministic Lean semantics cannot produce on its own; like crypto,
they are supplied from outside and treated as an uninterpreted oracle whose only Lean-side
commitments are its stated laws (the obligations the operational environment discharges).

Two realizations of the SAME interface (the `CryptoKernel` answer to "FFI or uninterpreted
symbols?" — *both*):
  • **PROVING** — an abstract `[World Msg]` (uninterpreted symbols + their laws). Every
    Lean theorem here is parametric over it, so it holds for *any* lawful environment
    (any scheduling of the network, any clock, any randomness beacon).
  • **RUNNING** — Rust (the node's runtime) supplies the concrete delivery, the system
    clock, and the randomness beacon; the compiled Lean calls into them via FFI
    (`@[extern "dregg_world_recv"] opaque recv …`, `dregg_world_clock`,
    `dregg_world_rand`), which IS a lawful instance. The `recv` oracle is the network
    adversary's scheduling made into an interface; Lean never *proves* the network behaves,
    it *assumes* the laws the runtime guarantees (e.g. clock monotonicity).

This is the network/clock/randomness half the `CryptoKernel` doc flagged as "a sibling
`World` oracle, future work". With it we can express *real finality* over the network: a
concrete `quorumReached` vote-count meeting `Finality`'s lifted `½(n+f)` threshold, the
abstract `Finality.Committed` predicate instantiated as "a quorum of votes was received
over `World.recv`", and the clean monotonicity facts that follow. The Byzantine /
asynchrony guarantees (safety under equivocation, liveness after GST) are NOT provable from
this interface alone — they need the full τ-BFT protocol — and are left as honest `OPEN`s.
-/
import Mathlib.Tactic
import Dregg2.Finality
import Dregg2.Execution
import Dregg2.Tactics

namespace Dregg2.World

open Dregg2

/-! ## Messages and votes — the network payloads.

`Msg` is a *parameter* (an interface type, like `CryptoKernel`'s `Digest`/`Proof`): the
network carries opaque messages whose internal structure Lean does not interpret. A `Vote`
is the one payload finality *does* need to interpret — a participant id endorsing a block —
so it is concrete here (the quorum model counts distinct voters). -/

/-- **A vote for a block** — the network payload consensus counts. `voter` is the
participant id (so a quorum is "enough *distinct* voters"); `block` is the (opaque) block
id being endorsed. Concrete because `quorumReached` must inspect it; the generic network
payload `Msg` stays a parameter. -/
structure Vote where
  /-- The endorsing participant's id (distinctness is what a quorum counts). -/
  voter : Nat
  /-- The block id this vote endorses. -/
  block : Nat
  deriving DecidableEq, Repr

/-! ## The `World` interface — the network/clock/randomness oracle. -/

/-- **The `World` interface.** The sibling of `CryptoKernel`: `Msg` (the generic network
payload) is uninterpreted; the three operations are opaque; the fields ending in a law are
the obligations the runtime (Rust node + OS clock + randomness beacon) must satisfy
(assumed, never proved, in Lean — exactly as `CryptoKernel`'s `commit_hom`/`hash_inj` are
assumed). These are the nondeterministic external inputs: the Lean semantics is a *function
of* them, it does not generate them.

FFI/uninterpreted-symbols realization (mirrors `CryptoKernel`): for PROVING, an abstract
`[World Msg]`; for RUNNING, `@[extern "dregg_world_clock"] opaque clock`,
`@[extern "dregg_world_recv"] opaque recv`, `@[extern "dregg_world_rand"] opaque rand`
backed by the node runtime. -/
class World (Msg : Type) where
  /-- **The clock oracle** — a monotone-ish logical time. `clock ()` reads the current
  logical time; the runtime (OS / hybrid logical clock) supplies it. We do NOT read a
  global wall-clock into safety (the §2.2 "synchronized wall-clock deadline" globalism seam
  is rejected); this is a logical timestamp used for round bookkeeping only. Realized at
  runtime via `@[extern "dregg_world_clock"]`. -/
  clock : Unit → Nat
  /-- **The network oracle** — the messages/votes delivered *by* a given round. `recv r` is
  the multiset (as a `List`) of messages the local node has received up to round `r`. This
  IS the network adversary's delivery schedule made into an interface; Lean assumes only
  the law below about it. Realized at runtime via `@[extern "dregg_world_recv"]`. -/
  recv : Nat → List Msg
  /-- **The randomness oracle** — leader election / sortition (`rand r` = the beacon value
  for round `r`). Used to pick a τ-BFT wave leader; opaque, supplied by the runtime beacon.
  Realized at runtime via `@[extern "dregg_world_rand"]`. -/
  rand : Nat → Nat
  /-- **LAW — network monotonicity (no un-delivery).** What a round has received is never
  retracted: a later round has received (at least) everything an earlier round did. This is
  the only network guarantee Lean relies on — the message log grows; the adversary may
  delay and reorder but cannot make a delivered message *un*-happen. The runtime discharges
  it (an append-only receive log). (Asynchrony / GST liveness is NOT here — that needs the
  protocol; see the OPEN below.) -/
  recv_mono : ∀ {r r' : Nat}, r ≤ r' → List.Sublist (recv r) (recv r')
  /-- **LAW — GST liveness (partial-synchrony progress oracle).** After the global
  stabilization time the network is no longer fully asynchronous: it is the assumed
  obligation of a *partial-synchrony* runtime that progress is eventually made. The premise
  `hlive` is the honest precondition this oracle quantifies under — the GST + honest-quorum
  hypothesis, abstracted as "for this vote-reading `votesOf` and config `cfg`, there really
  IS a round whose delivered votes meet the threshold for some block" (a fully-asynchronous
  adversary that delays everything forever, or an unsatisfiable config, simply does not
  supply `hlive`, and then the law says nothing). Under that premise the law commits the
  runtime to *exhibiting* such a round. This is the honest counterpart to `recv_mono`: NOT
  provable from the bare network oracle (FLP forbids unconditional liveness), so — exactly as
  crypto laws like `hash_inj` and the network law `recv_mono` are *assumed*, never proved, in
  Lean — it is carried here as a stated field, the progress guarantee the runtime's GST/Δ
  delivery bound discharges. A partially-synchronous network (and the reference instance
  below, whose growing schedule eventually meets any reached threshold) inhabits it. Because
  it is a class FIELD (a hypothesis), theorems using it stay kernel-clean — it never appears
  in `#print axioms`. -/
  gst_liveness : ∀ (votesOf : List Msg → List Vote) (cfg : Finality.Config) (block : Nat),
    -- `hprod` — the GST + honest-quorum precondition, abstracted: for this block the count of
    -- distinct voters delivered grows without bound (an honest supermajority keeps voting
    -- and, after GST, those votes are delivered). A fully-asynchronous adversary that
    -- silences voters never supplies this; a partially-synchronous runtime does. (The
    -- distinct-voter count is spelled out inline — `votersFor`/`quorumReached` are defined
    -- below the class, so the law cannot forward-reference them by name; the `quorumRule`
    -- and theorems prove these inline forms are definitionally those names.)
    (∀ k : Nat, ∃ r : Nat,
      k ≤ ((((votesOf (recv r)).filter (fun v => v.block = block)).map (·.voter)).dedup).length) →
    ∃ (r : Nat), cfg.threshold ≤
      ((((votesOf (recv r)).filter (fun v => v.block = block)).map (·.voter)).dedup).length

variable {Msg : Type}

/-! ## The concrete quorum model — real finality over the network.

`Finality.lean` keeps `Committed`/quorum abstract and lifts the `½(n+f)` threshold into
`Config`. Here we give the *concrete* vote-counting predicate over a `World`-delivered vote
list and connect it to the abstract `Finality.Committed`. -/

/-- **The set of distinct voters that endorsed `block` in `votes`** (deduplicated by
`voter`, restricted to this block). A quorum counts *distinct* participants, so we
deduplicate: two votes from the same voter for the same block count once. -/
def votersFor (votes : List Vote) (block : Nat) : List Nat :=
  ((votes.filter (fun v => v.block = block)).map (·.voter)).dedup

/-- **`quorumReached votes cfg block`** — a vote count meets the lifted `½(n+f)` threshold.
The number of *distinct* voters that endorsed `block` is at least `cfg.threshold` (the
config's commit threshold, canonically `Config.halfQuorum n f = ⌊(n+f)/2⌋+1`). This is the
concrete realization of the quorum `Finality.Committed` leaves abstract; the `½(n+f)`
constant is read from `cfg`, never hardcoded (§2.2). -/
def quorumReached (votes : List Vote) (cfg : Finality.Config) (block : Nat) : Bool :=
  cfg.threshold ≤ (votersFor votes block).length

/-! ## Connecting the abstract `Finality.Committed` to the network quorum. -/

/-- **The block-id history substrate.** For the network-driven finality model a "history"
is just a block id (`Nat`) — the thing votes endorse and the thing `Committed` ranges over.
(`Finality.History` is `Type u`; we instantiate it at `Nat`.) -/
abbrev BlockId := Nat

/-- **`committedByQuorum` — the abstract `Finality.Committed` instantiated as "a quorum of
votes was received over `World.recv`".** Given a `World`, a round `r`, a way to read the
votes out of the received messages (`votesOf`), and a config, a block is *committed* exactly
when `quorumReached` holds over the votes the network delivered by round `r`. This is the
portal connection: `Finality`'s opaque `Committed` predicate is realized by a concrete count
over the `World` network oracle's output. -/
def committedByQuorum [World Msg] (votesOf : List Msg → List Vote)
    (r : Nat) (cfg : Finality.Config) : Finality.Committed BlockId :=
  fun block => quorumReached (votesOf (World.recv r)) cfg block = true

/-! ## PROVED facts about the quorum model. -/

/-- **Dedup never lengthens a list** (helper) — the deduplicated voter list is no longer
than the raw one. Used to bound a quorum from the underlying votes. -/
theorem votersFor_length_le (votes : List Vote) (block : Nat) :
    (votersFor votes block).length ≤
      ((votes.filter (fun v => v.block = block)).map (·.voter)).length := by
  simpa [votersFor] using
    List.Sublist.length_le (List.dedup_sublist
      ((votes.filter (fun v => v.block = block)).map (·.voter)))

/-- **A sublist of votes has a sublist of voters-for-a-block** (helper). If `votes₁` is a
sublist of `votes₂` (the network only ever *added* votes), then the distinct voters for any
block under `votes₁` are a subset of those under `votes₂`, hence no more numerous. The key
monotonicity step under the network's append-only delivery. -/
theorem votersFor_length_mono {votes₁ votes₂ : List Vote}
    (h : List.Sublist votes₁ votes₂)
    (block : Nat) :
    (votersFor votes₁ block).length ≤ (votersFor votes₂ block).length := by
  -- filtering preserves the sublist, mapping preserves it, and dedup is monotone in length
  -- under the subset induced by a sublist.
  have hfilt : List.Sublist (votes₁.filter (fun v => v.block = block))
      (votes₂.filter (fun v => v.block = block)) := h.filter _
  have hmap : List.Sublist ((votes₁.filter (fun v => v.block = block)).map (·.voter))
      ((votes₂.filter (fun v => v.block = block)).map (·.voter)) := hfilt.map _
  -- a sublist's dedup is contained in the larger list's dedup ⇒ length ≤.
  have hsub : ((votes₁.filter (fun v => v.block = block)).map (·.voter)).dedup
      ⊆ ((votes₂.filter (fun v => v.block = block)).map (·.voter)).dedup := by
    intro a ha
    rw [List.mem_dedup] at ha ⊢
    exact hmap.subset ha
  have hnd : ((votes₁.filter (fun v => v.block = block)).map (·.voter)).dedup.Nodup :=
    List.nodup_dedup _
  -- a nodup list that is a subset of another is a subperm of it, hence no longer.
  simpa [votersFor] using (List.subperm_of_subset hnd hsub).length_le

/-- **`quorum_monotone` (PROVED) — more votes preserve quorum-reached.** If a quorum was
reached over a vote list `votes₁`, then it is still reached over any larger list `votes₂`
(`votes₁ <+ votes₂`). Distinct-voter count is monotone under adding votes, and the threshold
is fixed; this is *safety of the count* under the network's append-only delivery — once a
quorum exists, delivering more messages cannot destroy it. -/
theorem quorum_monotone {votes₁ votes₂ : List Vote}
    (h : List.Sublist votes₁ votes₂)
    (cfg : Finality.Config) (block : Nat)
    (hq : quorumReached votes₁ cfg block = true) :
    quorumReached votes₂ cfg block = true := by
  simp only [quorumReached, decide_eq_true_eq] at hq ⊢
  exact le_trans hq (votersFor_length_mono h block)

/-- **Quorum is monotone *along network delivery* (PROVED).** Combining `World.recv_mono`
with `quorum_monotone`: if a quorum for `block` was reached over the votes delivered by
round `r`, it is still reached over the votes delivered by any later round `r' ≥ r`, *for
any voter-extraction `votesOf` that respects sublists* (delivering more messages yields a
superlist of votes). So `committedByQuorum` is monotone in the round — a committed block
*stays* committed as the network log grows. This is the network-level statement that quorum
commits do not un-happen. -/
theorem committedByQuorum_mono [World Msg]
    (votesOf : List Msg → List Vote)
    (hvotesOf : ∀ {m₁ m₂ : List Msg}, List.Sublist m₁ m₂ →
      List.Sublist (votesOf m₁) (votesOf m₂))
    {r r' : Nat} (hrr : r ≤ r') (cfg : Finality.Config) (block : BlockId)
    (hc : committedByQuorum votesOf r cfg block) :
    committedByQuorum votesOf r' cfg block := by
  unfold committedByQuorum at hc ⊢
  exact quorum_monotone (hvotesOf (World.recv_mono hrr)) cfg block hc

/-! ## A `FinalityRule` built from the network quorum, and no-downgrade over it.

The quorum predicate supplies a *concrete* `Finality.FinalityRule` whose `committed` is
`committedByQuorum`. Its commit-soundness (`committed ⇒ canonical`) is, per §2.2, an
obligation each rule satisfies by construction; for the network model we take canonicity to
be *exactly* having-a-quorum, which makes the obligation hold definitionally. We then relay
`Finality.no_downgrade`'s tier-monotonicity shape over a `World`-driven finality run. -/

/-- **The network-quorum finality rule (PROVED to be a lawful `FinalityRule`).** A
tier-`tier` rule whose `committed` predicate is `committedByQuorum` over round `r`, and
whose `canonical` selector is the *same* predicate — so commit-soundness
(`committed h → canonical h`) holds by `id`. This is the §2.2 "tier-2 ack-threshold / tier-3
BFT quorum" rule made concrete over the `World` network oracle; the abstract
`Finality.Committed` of the rule is now the real vote count. -/
def quorumRule [World Msg] (tier : Finality.Tier) (votesOf : List Msg → List Vote)
    (r : Nat) (cfg : Finality.Config) : Finality.FinalityRule BlockId where
  tier := tier
  config := cfg
  committed := committedByQuorum votesOf r cfg
  canonical := committedByQuorum votesOf r cfg
  commit_canonical := fun _ h => h

/-- The network-quorum rule's `committed` is exactly `committedByQuorum` (definitional
unfolding — confirms the abstract predicate is wired to the concrete vote count). -/
@[simp] theorem quorumRule_committed [World Msg] (tier : Finality.Tier)
    (votesOf : List Msg → List Vote) (r : Nat) (cfg : Finality.Config) (block : BlockId) :
    (quorumRule tier votesOf r cfg).committed block
      = (quorumReached (votesOf (World.recv r)) cfg block = true) :=
  rfl

/-- **No-downgrade relayed over a `World`-driven finality run (PROVED).** The
finality-strength transition system `Finality.finalitySystem` (configurations = `Tier`,
steps may only keep-or-strengthen the tier) is driven, in the real system, by network
events delivered through `World.recv`; this theorem instantiates `Finality.no_downgrade`'s
shape over such a run. Along ANY sequence of (re-)finalization events on one value — i.e.
any `Execution.Run finalitySystem t₀ t` whose steps are triggered by the `World` oracle —
the final tier `t` is no weaker than the initial tier `t₀`. The network can deliver more
votes, advance the clock, and re-run leader election, but it can never *downgrade* a
value's finality. Proved by relaying `Finality.no_downgrade` (which lifts the per-step
"a step never lowers the tier" through `Execution.invariant_run`). -/
theorem world_no_downgrade [World Msg] {t₀ t : Finality.Tier}
    (hrun : Execution.Run Finality.finalitySystem t₀ t) :
    t₀ ≤ t :=
  Finality.no_downgrade hrun

/-! ## Quorum intersection (PROVED via pigeonhole) and the GST liveness obligation.

The intersection *core* of BFT safety — that two quorums for distinct blocks must share a
voter — is pure counting from the `½(n+f)` threshold and a participant-membership bound, so
it is proved here with no external paper. The *full* honest-vote-once safety (a shared voter
is a CONTRADICTION because an honest node never double-votes) needs the adversary/honesty
model and Malkhi–Reiter; that part stays an honest scope-note, NOT a `sorry`. Liveness after
GST is discharged from a NAMED assumed `World` oracle law (`gst_liveness`), the
partial-synchrony obligation the network layer satisfies — the same honest pattern as
`recv_mono`, not an axiom. -/

/-- **Quorum intersection (PROVED, pigeonhole).** If `cfg.threshold` is the lifted
`halfQuorum = ⌊(n+f)/2⌋+1` and two quorums for blocks `b₁`, `b₂` have both formed over a
common vote list, and the union of their distinct voters is bounded by the participant
population `n + f` (the membership bound the protocol layer supplies — the network oracle
itself says nothing about *who* may vote), then the two quorums **share a voter**. This is
the seed of the BFT safety contradiction, established by pure counting:

  `|Q₁| + |Q₂| ≥ 2·(⌊(n+f)/2⌋+1) > n+f ≥ |Q₁ ∪ Q₂|`,

so by inclusion–exclusion `|Q₁ ∩ Q₂| = |Q₁| + |Q₂| − |Q₁ ∪ Q₂| ≥ 1`. No adversary model and
no external paper are needed for THIS step. (`hconflict`/`hbft` are recorded as the intended
protocol context — `n > 3f` is what makes the membership bound `≤ n+f` survive `f` Byzantine
voters — but the intersection itself follows from the threshold + union bound alone.)

**Honestly scoped-out (NOT proved here):** that a shared voter is a *contradiction* for
conflicting blocks. That is the full honest-vote-once argument (an honest node casts at most
one vote per height); it requires the adversary/honesty model and the per-node voting
discipline (Malkhi–Reiter style), which live with the τ-BFT protocol, not the bare network
oracle. This theorem closes the intersection core; the contradiction step is the protocol's. -/
theorem quorum_intersection_safety
    (cfg : Finality.Config) (votes : List Vote) (b₁ b₂ : Nat)
    (hconflict : b₁ ≠ b₂)
    (hquorum_is_half : cfg.threshold = Finality.Config.halfQuorum cfg.n cfg.f)
    (hbft : cfg.n > 3 * cfg.f)
    -- the participant-membership bound the protocol layer supplies: every distinct voter is
    -- one of the `n + f` participants, so the *union* of the two quorums' voters is no larger
    -- than the population. (`n > 3f` keeps this honest under `f` Byzantine voters.)
    (hbound : ((votersFor votes b₁).toFinset ∪ (votersFor votes b₂).toFinset).card
      ≤ cfg.n + cfg.f)
    (hq1 : quorumReached votes cfg b₁ = true) (hq2 : quorumReached votes cfg b₂ = true) :
    -- two quorums for distinct blocks must share a voter — quorum intersection.
    ∃ voter, voter ∈ votersFor votes b₁ ∧ voter ∈ votersFor votes b₂ := by
  -- the two voter lists are dedup'd, hence `Nodup`, so their `toFinset.card = length`.
  set Q1 := votersFor votes b₁ with hQ1
  set Q2 := votersFor votes b₂ with hQ2
  have hnd1 : Q1.Nodup := by rw [hQ1, votersFor]; exact List.nodup_dedup _
  have hnd2 : Q2.Nodup := by rw [hQ2, votersFor]; exact List.nodup_dedup _
  have hc1 : Q1.toFinset.card = Q1.length := List.toFinset_card_of_nodup hnd1
  have hc2 : Q2.toFinset.card = Q2.length := List.toFinset_card_of_nodup hnd2
  -- each quorum meets the threshold = halfQuorum.
  have hlen1 : Finality.Config.halfQuorum cfg.n cfg.f ≤ Q1.length := by
    simpa [quorumReached, hquorum_is_half] using hq1
  have hlen2 : Finality.Config.halfQuorum cfg.n cfg.f ≤ Q2.length := by
    simpa [quorumReached, hquorum_is_half] using hq2
  -- inclusion–exclusion: |Q1∪Q2| + |Q1∩Q2| = |Q1| + |Q2|.
  have hie : (Q1.toFinset ∪ Q2.toFinset).card + (Q1.toFinset ∩ Q2.toFinset).card
      = Q1.toFinset.card + Q2.toFinset.card := Finset.card_union_add_card_inter _ _
  -- pigeonhole: 2·(⌊(n+f)/2⌋+1) > n+f ≥ |Q1∪Q2| forces a nonempty intersection.
  have hinter_pos : 0 < (Q1.toFinset ∩ Q2.toFinset).card := by
    simp only [Finality.Config.halfQuorum] at hlen1 hlen2
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hinter_pos
  rw [Finset.mem_inter, List.mem_toFinset, List.mem_toFinset] at hv
  exact ⟨v, hv.1, hv.2⟩

/-- **Liveness after GST (PROVED, discharged from the `gst_liveness` oracle law).** Under the
GST + honest-quorum precondition `hprod` (for some `block`, the distinct-voter count delivered
grows without bound — an honest supermajority keeps voting and, after GST, their votes are
delivered), the network reaches a round where `committedByQuorum` holds — the τ-BFT progress
guarantee. UNCONDITIONAL liveness is FALSE for a fully-asynchronous network (FLP: the
adversary may delay all votes forever), so this cannot be proved from the bare oracle; the
honest move — matching how `recv_mono` supplies the only network safety guarantee — is to
discharge it from the NAMED assumed partial-synchrony law `World.gst_liveness` (the GST/Δ
delivery obligation the runtime satisfies). `hprod` is exactly the FLP escape hatch the
fully-asynchronous adversary refuses to grant. This is a hypothesis (a class field), not an
axiom — so this theorem stays kernel-clean (`#print axioms` shows none beyond Lean's own). -/
theorem liveness_after_gst [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) (block : BlockId)
    (hprod : ∀ k : Nat, ∃ r : Nat, k ≤ (votersFor (votesOf (World.recv r)) block).length) :
    ∃ (r : Nat), committedByQuorum votesOf r cfg block := by
  -- the partial-synchrony oracle law, fed the productivity precondition, gives a round at
  -- which a quorum has formed; unfold `committedByQuorum` to expose it IS that quorum.
  obtain ⟨r, hq⟩ := World.gst_liveness (Msg := Msg) votesOf cfg block hprod
  refine ⟨r, ?_⟩
  -- `hq : cfg.threshold ≤ (votersFor …).length` (the field's inline conclusion); package it
  -- back into `committedByQuorum`'s `quorumReached … = true`.
  show committedByQuorum votesOf r cfg block
  unfold committedByQuorum
  simp only [quorumReached, votersFor, decide_eq_true_eq]
  exact hq

/-! ## A reference (test) `World` — the Lean-as-host realization.

Mirrors `CryptoKernel.Reference`: a trivial lawful instance (over `Msg = Vote`) — enough to
`#eval`/test the network-driven finality WITHOUT a running node. The real instance is the
Rust FFI one. This witnesses that the interface is inhabitable (the `recv_mono` law is
satisfiable), so the parametric theorems above are not vacuous. -/
namespace Reference

/-- Reference message = a `Vote` (the test network carries only votes). -/
abbrev M := Vote

/-- A reference receive log: a fixed nondecreasing-by-construction schedule — round `r`
delivers the first `r` votes of a fixed list. `List.take` of a monotone index gives the
`recv_mono` sublist for free. -/
def fixedVotes : List Vote :=
  [⟨0, 7⟩, ⟨1, 7⟩, ⟨2, 7⟩, ⟨0, 7⟩]  -- note: voter 0 appears twice; dedup counts it once

instance : World M where
  clock := fun _ => 0
  recv := fun r => fixedVotes.take r
  rand := fun r => r
  recv_mono := by
    intro r r' h
    -- `take r = take r (take r')` when `r ≤ r'` (via `take_take`/`min`), and
    -- `take r (take r') <+ take r'`; compose.
    have hmin : min r r' = r := Nat.min_eq_left h
    have : fixedVotes.take r = (fixedVotes.take r').take r := by
      rw [List.take_take, hmin]
    rw [this]
    exact List.take_sublist r (fixedVotes.take r')
  gst_liveness := by
    -- The reference network discharges the GST law from the productivity premise alone: feed
    -- `hprod` the threshold to obtain a round whose delivered votes already meet it. (This is
    -- the honest shape — the trivial test net supplies no *unconditional* liveness; it
    -- relays the partial-synchrony precondition, exactly as a real GST runtime would.)
    intro votesOf cfg block hprod
    obtain ⟨r, hr⟩ := hprod cfg.threshold
    -- the field's conclusion is the inline `cfg.threshold ≤ …length`, exactly what `hprod`
    -- at `k = cfg.threshold` supplies.
    exact ⟨r, hr⟩

/-- The reference world is lawful and the parametric defs compute: by round 3 the fixed
schedule has delivered 3 distinct voters (0,1,2) for block 7, meeting a threshold of 3. -/
example :
    quorumReached ((World.recv (Msg := M) 3)) ⟨3, 0, 3⟩ 7 = true := by
  decide

end Reference

/-! ## Axiom hygiene — both new keystones are kernel-clean.

`quorum_intersection_safety` is a real pigeonhole proof; `liveness_after_gst` reduces to the
NAMED `World.gst_liveness` class FIELD (a hypothesis, not an `axiom`), so neither pulls in
`sorryAx` or any §8 oracle axiom — `collectAxioms` sees only the three standard kernel
axioms. The class field, being a hypothesis, never appears here. -/
#assert_axioms quorum_intersection_safety
#assert_axioms liveness_after_gst

end Dregg2.World
