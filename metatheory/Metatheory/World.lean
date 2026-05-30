/-
# Metatheory.World — the SIBLING portal to `CryptoKernel` for the nondeterministic
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
import Metatheory.Finality
import Metatheory.Execution

namespace Metatheory.World

open Metatheory

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

/-! ## OPEN obligations — the guarantees this interface alone cannot give.

These are NOT provable from the `World` interface + the quorum count; they need the full
τ-BFT protocol (the message-validity rules, the 3-step ratification, equivocation
detection) and an explicit synchrony/GST model. Left honest, mirroring `Finality.lean`'s
genuine `sorry`'d obligations. -/

/-- **OPEN: Byzantine quorum-intersection safety** — that two quorums for *conflicting*
blocks cannot both form when `cfg.threshold` is a `> ½(n+f)` quorum and at most `f` voters
are Byzantine (the classic `n > 3f` / quorum-intersection argument). This needs (a) the
adversary model (which `votersFor` voters are Byzantine), (b) the conflict relation on
blocks, and (c) the `threshold` to actually BE `halfQuorum` with `n > 3f`. The bare `World`
interface (which says nothing about *which* votes are honest) cannot establish it. It is the
core BFT safety theorem and belongs with the protocol, not the network oracle. -/
theorem quorum_intersection_safety_OPEN
    (cfg : Finality.Config) (votes : List Vote) (b₁ b₂ : Nat)
    (hconflict : b₁ ≠ b₂)
    (hquorum_is_half : cfg.threshold = Finality.Config.halfQuorum cfg.n cfg.f)
    (hbft : cfg.n > 3 * cfg.f)
    -- the honest population is bounded by `n` participants (the membership bound the
    -- protocol layer supplies; the bare network oracle says nothing about who is honest):
    (hbound : (votersFor votes b₁).length + (votersFor votes b₂).length ≤ cfg.n + cfg.f)
    (hq1 : quorumReached votes cfg b₁ = true) (hq2 : quorumReached votes cfg b₂ = true) :
    -- the intended conclusion: two quorums for conflicting blocks must share a voter
    -- (quorum intersection) — the seed of the BFT safety contradiction.
    ∃ voter, voter ∈ votersFor votes b₁ ∧ voter ∈ votersFor votes b₂ := by
  -- OPEN: needs the adversary/honesty model + conflict semantics + the n>3f arithmetic of
  -- quorum intersection — not derivable from the network oracle alone. The membership bound
  -- `hbound` is the protocol-supplied hypothesis; the pigeonhole/intersection argument over
  -- `Nat`-valued voters belongs with the protocol, which owns the honest-set semantics.
  sorry

/-- **OPEN: liveness after GST (a quorum eventually forms).** That, after the global
stabilization time, the network delivers enough honest votes for `quorumReached` to become
true for *some* block — the τ-BFT progress guarantee. This needs the partial-synchrony / GST
model (the `clock` becoming meaningful for bounds) and the honest-supermajority assumption,
neither of which the `World` interface commits to. It is the liveness counterpart to the
safety OPEN above and likewise belongs with the protocol. -/
theorem liveness_after_gst_OPEN [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) :
    -- intended: eventually (at some round) some block's quorum forms — the τ-BFT progress
    -- guarantee. Requires the GST + honesty model the interface deliberately omits
    -- (asynchrony is the adversary's, not a law), so it is not provable here.
    ∃ (r : Nat) (block : BlockId), committedByQuorum votesOf r cfg block := by
  -- OPEN: liveness is not a property of the bare (possibly fully-asynchronous) network
  -- oracle; without a GST bound the adversary may delay all votes forever. Provable only
  -- against the protocol + partial-synchrony assumption.
  sorry

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

/-- The reference world is lawful and the parametric defs compute: by round 3 the fixed
schedule has delivered 3 distinct voters (0,1,2) for block 7, meeting a threshold of 3. -/
example :
    quorumReached ((World.recv (Msg := M) 3)) ⟨3, 0, 3⟩ 7 = true := by
  decide

end Reference

end Metatheory.World
