/-
# Dregg2.Apps.MultisigVote — a verified MULTI-PARTY APPROVAL / MULTISIG VOTE over the REAL kernel.

A proposal `p` resolves to PASSED once `≥ threshold` DISTINCT, ENFRANCHISED voters have approved it,
each voter approving AT MOST ONCE. This runs on the GENUINE `RecordKernelState` (NOT the `DemoRes`
toy): the approval set IS the kernel's spent-note nullifier seen-set (`k.nullifiers`), each cast vote
inserting the voter's `CellId` as a "vote nullifier" exactly the way `apply_note_spend`
(`turn/src/executor/apply.rs:941`) inserts a spend nullifier — so DOUBLE-VOTE is rejected by the SAME
fail-closed set gate that prevents a double-spend (`note_no_double_spend`/`note_spend_inserts`).

It is **composition, not new kernel theory**: the no-double-vote keystone INSTANTIATES the proved
`RecordKernel` nullifier-set lemmas, and the AUTHORITY gate REUSES the cap-table branch of
`Exec/Kernel.authorizedB` — a voter is enfranchised iff they are in the published `registry` OR hold a
vote-capability `Cap.node proposalCell` (the `endpoint`/`node` cap branch that `authorizedB` consults,
NOT the reflexive `actor == src` tautology). What this module ADDS is the multisig COMPOSITION and the
four end-user guarantees:

  * **SAFETY (no double-vote)** — a voter already in the approval set, re-approving, does NOT change
    the approval set, so the tally cannot be inflated by re-voting (`castVote` fails-closed via the
    nullifier set, and the approval set is idempotent under a re-insert — `revote_no_change`,
    `revote_tally_unchanged`). Teeth: a concrete double approval is counted ONCE.
  * **SAFETY/AUTHORITY (enfranchisement)** — only voters in the `registry` OR holding the vote-cap
    count: a NON-enfranchised approval is REJECTED by `castVote` (`outsider_vote_rejected`). This
    EXERCISES A REAL GATE — `enfranchisedB` consults the registry membership AND the cap table — NOT
    the `actor == src` reflexive tautology. Teeth: an outsider (not in registry, no cap) is rejected,
    while a cap-bearer (NOT in the registry) is ADMITTED via the cap branch (`capbearer_admitted`).
  * **CORRECTNESS (pass iff threshold)** — the proposal PASSES iff the distinct-enfranchised approval
    count meets the threshold: `passes p k ↔ threshold ≤ tally p k`, BOTH directions (`passes_iff`).
  * **LIVENESS (◇ resolves)** — once `threshold` distinct enfranchised approvals have arrived, the
    proposal RESOLVES to passed: a concrete fixture reaches `passes = true` after exactly `threshold`
    cast votes (`votes_reach_quorum`, a decide witness on a real-kernel fixture).

TEETH (decide on a concrete fixture): a sub-threshold proposal does NOT pass; a double-voter is
counted once; an outsider is rejected; the cap-bearer is admitted. Runs on real kernel state.

§10+ adds the **WEIGHTED cast** (`castVoteW`) — the holding-weight ballot: a voter with a granted
weight `g voter` casts a ballot worth exactly that weight onto a monotone board, mirroring
`collective_choice::CollectiveChoice::cast_weighted` (Rust: the tally bump is `live + weight`, one
ballot cap per voter, zero weight refused). Keystones: **WEIGHT CONSERVATION** (the board equals the
sum of the granted weights of the counted ballots — `castVoteW_preserves_WFW` /
`board_eq_sum_of_granted`), **ONE-CAST-PER-VOTER under weights** (`weighted_second_cast_refused`,
via the SAME kernel nullifier gate as the unweighted cast), and the discriminating negatives: a
ZERO-weight cast is refused outright and changes nothing (`zero_weight_cast_changes_nothing` — the
voter is enfranchised and unspent, so the refusal is specifically the weight), and a positive weight
buys NO authority (`outsider_weight_buys_nothing`). Weighted teeth discriminate weight from
headcount: two casts of weights 50+100 pass a 120-WEIGHT quorum while the headcount tally is 2.
-/
import Dregg2.Exec.RecordKernel

namespace Dregg2.Apps.MultisigVote

open Dregg2.Exec
open Dregg2.Authority (Cap Auth)

/-! ## 1. The proposal config + the enfranchisement gate.

A `Proposal` bundles the on-chain target cell `proposalCell`, the published `registry` of enfranchised
voter cells, and the `threshold` (the quorum: number of distinct enfranchised approvals required to
pass). The approval set itself lives in the REAL kernel's `nullifiers` seen-set — a cast vote inserts
the voter's `CellId` as a vote nullifier, so the set is on-chain and the no-double-vote gate
is the kernel's own. -/

/-- **`Proposal`** — the multisig proposal config: the target cell `proposalCell`, the published
`registry` of enfranchised voter cells, and the `threshold` quorum (distinct enfranchised approvals
needed to pass). -/
structure Proposal where
  /-- the on-chain proposal cell (the target the vote-cap is `Cap.node`-keyed to). -/
  proposalCell : CellId
  /-- the published registry of enfranchised voter cells. -/
  registry     : Finset CellId
  /-- the quorum: number of distinct enfranchised approvals needed to pass. -/
  threshold    : Nat

/-- **`voteCap p`** — the enfranchisement capability for proposal `p`: a `Cap.node` keyed to the
proposal cell. A voter holding this cap is enfranchised even if NOT in the registry — exactly the
cap-table branch (`Cap.node turn.src`) that `Exec/Kernel.authorizedB` consults. -/
def voteCap (p : Proposal) : Cap := Cap.node p.proposalCell

/-- **`enfranchisedB p k voter`** — is `voter` enfranchised to vote on `p` in kernel state `k`? TRUE
iff the voter is in the published `registry` OR holds the vote-cap `Cap.node proposalCell` in the
kernel cap table `k.caps`. This is the REAL authority gate — it consults BOTH the registry AND the
cap table (the `Cap.node` branch of `authorizedB`), NEVER the reflexive `actor == src` tautology.
Decidable, computable, FAIL-CLOSED (a voter in neither is rejected). -/
def enfranchisedB (p : Proposal) (k : RecordKernelState) (voter : CellId) : Bool :=
  decide (voter ∈ p.registry) || (k.caps voter).contains (voteCap p)

/-! ## 2. Casting a vote on the REAL kernel (the fail-closed approval).

A cast vote inserts the voter's `CellId` into the kernel's `nullifiers` seen-set — the SAME set
`apply_note_spend` uses — gated by enfranchisement AND no-double-vote. Fail-closed (`none`) if the
voter is not enfranchised or has already approved. -/

/-- **`castVote p k voter`** — cast `voter`'s approval on proposal `p` over the REAL kernel state `k`.
Fail-closed (`none`) if the voter is NOT enfranchised (neither in the registry nor cap-bearing) OR has
already approved (`voter ∈ k.nullifiers`, the double-vote gate). On success, inserts `voter` into the
nullifier seen-set (the approval set) — exactly the way `noteSpendNullifier` inserts a spend
nullifier. -/
def castVote (p : Proposal) (k : RecordKernelState) (voter : CellId) : Option RecordKernelState :=
  if enfranchisedB p k voter = true ∧ voter ∉ k.nullifiers then
    some { k with nullifiers := voter :: k.nullifiers }
  else
    none

/-- **`approvalSet k`** — the set of voters who have approved (the on-chain `nullifiers` seen-set,
deduplicated to a `Finset`). The approval set is the kernel's own spent-nullifier set. -/
def approvalSet (k : RecordKernelState) : Finset CellId := k.nullifiers.toFinset

/-- **`tally p k`** — the number of DISTINCT, ENFRANCHISED approvals: the count of approval-set voters
who are actually enfranchised on `p`. Only enfranchised approvals are counted toward the quorum (so a
later-defranchised entry, or any non-enfranchised id, never inflates the tally). -/
def tally (p : Proposal) (k : RecordKernelState) : Nat :=
  ((approvalSet k).filter (fun v => enfranchisedB p k v = true)).card

/-- **`passes p k`** — does proposal `p` PASS in kernel state `k`? TRUE iff the distinct-enfranchised
approval count meets the threshold quorum. -/
def passes (p : Proposal) (k : RecordKernelState) : Bool := decide (p.threshold ≤ tally p k)

/-! ## 3. KEYSTONE — AUTHORITY/ENFRANCHISEMENT: a non-enfranchised vote is REJECTED.

The authority headline: `castVote` consults the REAL gate `enfranchisedB` (registry membership OR the
`Cap.node` cap branch), so a voter in NEITHER is fail-closed. This is the cap-table branch of
`authorizedB`, NOT the reflexive `actor == src` arm. -/

/-- **`castVote_enfranchised` (AUTHORITY)** — a committed vote was cast by an ENFRANCHISED voter: any
successful `castVote` forces `enfranchisedB p k voter = true`. The kernel never records an approval
from a voter outside the registry who holds no vote-cap. -/
theorem castVote_enfranchised {p : Proposal} {k k' : RecordKernelState} {voter : CellId}
    (h : castVote p k voter = some k') : enfranchisedB p k voter = true := by
  unfold castVote at h
  by_cases hg : enfranchisedB p k voter = true ∧ voter ∉ k.nullifiers
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`unenfranchised_vote_rejected` (AUTHORITY — fail-closed)** — a voter who is NOT enfranchised
(`enfranchisedB = false`) is REJECTED by `castVote` (`none`). The contrapositive face of the gate:
no approval is recorded from a non-enfranchised actor. This exercises the registry/cap gate, not the
`actor == src` tautology. -/
theorem unenfranchised_vote_rejected {p : Proposal} {k : RecordKernelState} {voter : CellId}
    (h : enfranchisedB p k voter = false) : castVote p k voter = none := by
  unfold castVote
  rw [if_neg]
  rintro ⟨he, _⟩
  rw [h] at he; exact absurd he (by simp)

/-! ## 4. KEYSTONE — SAFETY: no double-vote (re-approving cannot inflate the tally).

The safety headline composes the kernel's own nullifier-set anti-replay: a voter already in the
approval set cannot be inserted again (`castVote` fails-closed), and even at the SET level a re-insert
is idempotent — the approval set, hence the tally, is unchanged. -/

/-- **`revote_rejected` (SAFETY — fail-closed double-vote)** — a voter already in the approval set
(`voter ∈ k.nullifiers`) re-approving is REJECTED by `castVote` (`none`). Mirrors the kernel's
`note_no_double_spend`: the SAME seen-set gate that stops a double-spend stops a double-vote. -/
theorem revote_rejected {p : Proposal} {k : RecordKernelState} {voter : CellId}
    (h : voter ∈ k.nullifiers) : castVote p k voter = none := by
  unfold castVote
  rw [if_neg]
  rintro ⟨_, hnin⟩
  exact hnin h

/-- **`vote_inserts` — a committed vote actually inserts the voter** into the approval seen-set (so a
SUBSEQUENT vote by the same voter is rejected by `revote_rejected`). The positive face: the approval
lands on-chain. -/
theorem vote_inserts {p : Proposal} {k k' : RecordKernelState} {voter : CellId}
    (h : castVote p k voter = some k') : voter ∈ k'.nullifiers := by
  unfold castVote at h
  by_cases hg : enfranchisedB p k voter = true ∧ voter ∉ k.nullifiers
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; simp
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`revote_no_change` (SAFETY — set idempotence)** — re-inserting a voter ALREADY in the approval
set leaves the approval set UNCHANGED: `(voter :: k.nullifiers).toFinset = k.nullifiers.toFinset`.
This is `Finset.insert` idempotence — the SET-level reason a double-vote cannot inflate the count even
if the gate were bypassed. -/
theorem revote_no_change {k : RecordKernelState} {voter : CellId} (h : voter ∈ k.nullifiers) :
    approvalSet { k with nullifiers := voter :: k.nullifiers } = approvalSet k := by
  unfold approvalSet
  simp only [List.toFinset_cons]
  exact Finset.insert_eq_self.mpr (List.mem_toFinset.mpr h)

/-- **`revote_tally_unchanged` (SAFETY — the headline)** — re-recording a voter already in the approval
set does NOT change the tally for ANY proposal: the distinct-enfranchised count is fixed under a
re-insert. A double-vote is counted once. Composes `revote_no_change` (the approval set is unchanged)
under the tally's filter+card. -/
theorem revote_tally_unchanged {p : Proposal} {k : RecordKernelState} {voter : CellId}
    (h : voter ∈ k.nullifiers) :
    tally p { k with nullifiers := voter :: k.nullifiers } = tally p k := by
  unfold tally
  have hset : approvalSet { k with nullifiers := voter :: k.nullifiers } = approvalSet k :=
    revote_no_change h
  -- `enfranchisedB` reads `caps`/`registry`, both unchanged by the nullifier re-insert.
  simp only [enfranchisedB] at *
  rw [hset]
  rfl

/-! ## 5. KEYSTONE — CORRECTNESS: the proposal PASSES iff the threshold is met (an IFF, both ways). -/

/-- **`passes_iff` (CORRECTNESS — the headline IFF)** — proposal `p` PASSES in `k` IFF the
distinct-enfranchised approval count meets the threshold quorum: `passes p k = true ↔ threshold ≤
tally p k`. BOTH directions, by the definition of `passes` as the decidable threshold test. -/
theorem passes_iff (p : Proposal) (k : RecordKernelState) :
    passes p k = true ↔ p.threshold ≤ tally p k := by
  unfold passes; exact decide_eq_true_iff

/-- **`passes_of_quorum` (CORRECTNESS — the ⇐ resolve direction)** — if the distinct-enfranchised
approval count reaches the threshold, the proposal PASSES. The liveness payload: enough approvals ⇒
resolved-to-passed. -/
theorem passes_of_quorum {p : Proposal} {k : RecordKernelState} (h : p.threshold ≤ tally p k) :
    passes p k = true := (passes_iff p k).mpr h

/-- **`not_passes_of_subquorum` (CORRECTNESS — the ⇒ safety direction)** — if the tally is BELOW the
threshold, the proposal does NOT pass. A sub-threshold proposal cannot resolve. -/
theorem not_passes_of_subquorum {p : Proposal} {k : RecordKernelState} (h : tally p k < p.threshold) :
    passes p k = false := by
  rw [Bool.eq_false_iff, ne_eq, passes_iff]; omega

/-! ## 6. The FIXTURE — a concrete 3-of-{0,1,2,3} multisig on REAL kernel state.

Enfranchised registry `{0, 1, 2}` over proposal cell `100`, threshold `2`. Cell `3` is an OUTSIDER
(not in the registry, holds no vote-cap). Cell `4` is a CAP-BEARER (NOT in the registry, but holds the
vote-cap `Cap.node 100`) — admitted via the cap branch. The kernel state is a real `RecordKernelState`
with the genuine `accounts`/`caps` and an empty `nullifiers` (no votes yet). -/

/-- The vote fixture: a fresh proposal-bearing kernel state. Cells `{0,1,2,3,4}` are live; the cap
table grants ONLY cell `4` the vote-cap `Cap.node 100` (so `4` is enfranchised by cap, NOT registry);
no votes cast yet (`nullifiers = []`). -/
def voteK0 : RecordKernelState :=
  { accounts := {0, 1, 2, 3, 4}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 4 then [Cap.node 100] else [] }

/-- The 3-of registry proposal: enfranchised `{0, 1, 2}`, proposal cell `100`, threshold `2`. -/
def prop0 : Proposal := { proposalCell := 100, registry := {0, 1, 2}, threshold := 2 }

/-! ## 7. The TEETH — decided on the concrete fixture.

Real discriminating instances on `voteK0`/`prop0`: the empty proposal is sub-threshold (does NOT
pass); the outsider (cell 3) is rejected while the registry voter (cell 0) and the cap-bearer (cell 4)
are admitted; a double-voter is counted once; and reaching the threshold resolves the
proposal to passed. -/

/-- **`empty_does_not_pass` (TEETH — sub-threshold)** — with NO votes cast, the tally is `0 < 2`, so
the proposal does NOT pass. The vacuous-quorum guard. -/
theorem empty_does_not_pass : passes prop0 voteK0 = false := by decide

/-- **`outsider_vote_rejected` (TEETH — AUTHORITY)** — cell `3` is an OUTSIDER (not in registry `{0,1,2}`
and holds no vote-cap), so its approval is REJECTED (`castVote = none`). This exercises the REAL gate:
`enfranchisedB` fails on BOTH arms (`3 ∉ {0,1,2}`, and `caps 3 = []` has no `Cap.node 100`) — the
cap-table branch the `actor == src` tautology never touches. -/
theorem outsider_vote_rejected : castVote prop0 voteK0 3 = none := by decide

/-- **`registry_voter_admitted` (TEETH — non-vacuity of the gate, registry arm)** — cell `0` IS in the
registry, so its approval is ADMITTED (`castVote` is `some`). The gate is discriminating, not
"everything rejected". -/
theorem registry_voter_admitted : (castVote prop0 voteK0 0).isSome = true := by decide

/-- **`capbearer_admitted` (TEETH — the cap branch, genuine authority content)** — cell `4` is NOT in
the registry `{0,1,2}`, yet holds the vote-cap `Cap.node 100`, so it is ADMITTED via the CAP BRANCH of
`enfranchisedB` (`(caps 4).contains (Cap.node 100)`). This is the genuine cap-gated enfranchisement —
the same `Cap.node` branch `authorizedB` consults — distinguished from the outsider `3` who has
neither registry membership nor cap. -/
theorem capbearer_admitted : (castVote prop0 voteK0 4).isSome = true := by decide

/-- **`double_vote_counted_once` (TEETH — SAFETY)** — cell `0` votes, then `0` re-votes: the SECOND
vote is REJECTED (`none`), so the approval set holds `0` exactly once and the tally is `1`, NOT `2`.
A double-voter cannot inflate the quorum. Decided end-to-end on the real-kernel fixture. -/
theorem double_vote_counted_once :
    ((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 0)) = none ∧
    ((castVote prop0 voteK0 0).map (fun k => tally prop0 k)) = some 1 := by decide

/-- **`votes_reach_quorum` (TEETH — LIVENESS ◇)** — voters `0` then `1` (both enfranchised, distinct)
cast their approvals; the resulting state reaches the threshold-2 quorum and the proposal RESOLVES to
PASSED. Once `threshold` distinct enfranchised approvals arrive, `passes = true` — a concrete decide
witness of the liveness ◇ on the real-kernel fixture. -/
theorem votes_reach_quorum :
    ((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 1)).map (fun k => passes prop0 k)
      = some true := by decide

/-- **`subquorum_does_not_pass` (TEETH — CORRECTNESS, sub-threshold after a real vote)** — after only
ONE enfranchised approval (cell `0`), the tally is `1 < 2`, so the proposal still does NOT pass. A
single vote is not a quorum. -/
theorem subquorum_does_not_pass :
    ((castVote prop0 voteK0 0).map (fun k => passes prop0 k)) = some false := by decide

/-- **`capbearer_counts_toward_quorum` (TEETH — the cap branch reaches quorum)** — a registry voter
(`0`) plus the CAP-BEARER (`4`, not in registry but cap-enfranchised) together form a distinct quorum
of `2`, and the proposal PASSES. The cap branch is load-bearing for liveness, not merely admitted. -/
theorem capbearer_counts_toward_quorum :
    ((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 4)).map (fun k => passes prop0 k)
      = some true := by decide

/-! ## 8. `#eval` smoke — the vote's load-bearing bits, decided by the model alone. -/

-- empty proposal: tally 0, does not pass.
#guard (tally prop0 voteK0, passes prop0 voteK0) == (0, false)                             -- (0, false)
-- outsider (3) rejected; registry voter (0) and cap-bearer (4) admitted.
#guard (castVote prop0 voteK0 3).isSome == false                                          -- false
#guard ((castVote prop0 voteK0 0).isSome, (castVote prop0 voteK0 4).isSome) == (true, true)  -- (true, true)
-- one vote: tally 1, still sub-threshold.
#guard (castVote prop0 voteK0 0).map (fun k => (tally prop0 k, passes prop0 k)) == some (1, false)  -- some (1, false)
-- double vote rejected; tally stays 1.
#guard ((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 0)).isSome == false      -- false
-- two distinct enfranchised votes (0 then 1): quorum reached, PASSES.
#guard (((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 1)).map
        (fun k => (tally prop0 k, passes prop0 k))) == some (2, true)                      -- some (2, true)
-- registry + cap-bearer (0 then 4): quorum reached via the cap branch.
#guard (((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 4)).map
        (fun k => (tally prop0 k, passes prop0 k))) == some (2, true)                      -- some (2, true)

/-! ## 9. Axiom hygiene — every keystone pinned to the standard kernel triple.

`#assert_axioms` walks each keystone and errors if any escapes `{propext, Classical.choice,
Quot.sound}` — any stray axiom anywhere would fail the build. -/

#assert_axioms castVote_enfranchised
#assert_axioms unenfranchised_vote_rejected
#assert_axioms revote_rejected
#assert_axioms vote_inserts
#assert_axioms revote_no_change
#assert_axioms revote_tally_unchanged
#assert_axioms passes_iff
#assert_axioms passes_of_quorum
#assert_axioms not_passes_of_subquorum
#assert_axioms empty_does_not_pass
#assert_axioms outsider_vote_rejected
#assert_axioms registry_voter_admitted
#assert_axioms capbearer_admitted
#assert_axioms double_vote_counted_once
#assert_axioms votes_reach_quorum
#assert_axioms subquorum_does_not_pass
#assert_axioms capbearer_counts_toward_quorum

/-! ## §10 — The WEIGHTED cast (`castVoteW`): holding-weighted ballots on the same kernel gates.

A holding-weight ballot is worth its GRANTED weight `g voter` (in deployment `g` is the
Lean-proven `grantWeightCore` verdict over a consensus-proven holding — see
`Dregg2.Bridge.ProofOfHoldingsGeneric` / `HoldingWeightedTally`; here it is an arbitrary
assignment, so every theorem quantifies over ALL grants). `castVoteW` mirrors the deployed
`collective_choice::CollectiveChoice::cast_weighted`:

  * the ONE-CAST gate is the SAME kernel nullifier discipline as the unweighted `castVote`
    (a second cast by the same voter is refused no matter the weight);
  * the BOARD bump is `board + g voter` — the Rust `live + weight` monotone tally turn;
  * a ZERO weight is refused OUTRIGHT (`none`), before the nullifier is consumed — the ballot
    is not burned by a worthless cast (mirrors `VoteError::ZeroWeight`);
  * the append-only `log` is the cast log a light client replays
    (`CollectiveChoice::light_client_tally`). -/

/-- **`WeightedBox`** — the weighted poll state: the kernel (whose `nullifiers` seen-set is the
one-cast gate and whose `caps`/registry are the enfranchisement gate), the monotone tally
`board` (the Rust `Monotonic` tally slot), and the append-only cast `log` of
`(voter, granted weight)` pairs (the light-client replay object). -/
structure WeightedBox where
  /-- the real kernel state — nullifier one-cast gate + cap/registry enfranchisement. -/
  kernel : RecordKernelState
  /-- the monotone weighted tally board (`Monotonic` slot mirror). -/
  board  : Nat
  /-- the append-only cast log: `(voter, granted weight)` per counted ballot. -/
  log    : List (CellId × Nat)

/-- A fresh weighted box over kernel state `k`: empty board, empty log. -/
def freshWBox (k : RecordKernelState) : WeightedBox := ⟨k, 0, []⟩

/-- **`castVoteW p g b voter`** — cast `voter`'s ballot worth its granted weight `g voter`.
Fail-closed (`none`) if the grant is ZERO (a worthless cast must not burn the ballot), if the
voter is not enfranchised, or if the voter already cast (the kernel nullifier gate — the SAME
`castVote` gate as the unweighted engine). On success the board grows by EXACTLY `g voter`
(the Rust `live + weight` bump) and the cast is appended to the log. -/
def castVoteW (p : Proposal) (g : CellId → Nat) (b : WeightedBox) (voter : CellId) :
    Option WeightedBox :=
  if g voter = 0 then none
  else
    match castVote p b.kernel voter with
    | none => none
    | some k' => some ⟨k', b.board + g voter, (voter, g voter) :: b.log⟩

/-- The weighted total a light client replays from the cast log: the sum of the logged
weights (the `light_client_tally` fold). -/
def logWeight (log : List (CellId × Nat)) : Nat := (log.map Prod.snd).sum

/-- **`passesW p b`** — the WEIGHT-quorum gate: the poll passes once the weighted board
reaches the threshold (`threshold` read in WEIGHT units — the `AffineLe`
`M·RESOLVED − Σ TALLY ≤ 0` face of the deployed weighted poll). -/
def passesW (p : Proposal) (b : WeightedBox) : Bool := decide (p.threshold ≤ b.board)

/-- `castVote` success, characterized: exactly enfranchisement + unspent nullifier, and the
post-state is the nullifier insert. The workhorse for every weighted keystone. -/
theorem castVote_some_iff {p : Proposal} {k k' : RecordKernelState} {voter : CellId} :
    castVote p k voter = some k'
      ↔ enfranchisedB p k voter = true ∧ voter ∉ k.nullifiers
          ∧ k' = { k with nullifiers := voter :: k.nullifiers } := by
  unfold castVote
  by_cases hg : enfranchisedB p k voter = true ∧ voter ∉ k.nullifiers
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      exact ⟨hg.1, hg.2, h.symm⟩
    · rintro ⟨_, _, rfl⟩
      rfl
  · rw [if_neg hg]
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨h1, h2, _⟩
      exact absurd ⟨h1, h2⟩ hg

/-- `castVoteW` success, characterized: a NONZERO grant, enfranchisement, an unspent
nullifier, and the post-box is exactly (nullifier insert, board `+ g voter`, log cons). -/
theorem castVoteW_some_iff {p : Proposal} {g : CellId → Nat} {b b' : WeightedBox}
    {voter : CellId} :
    castVoteW p g b voter = some b'
      ↔ g voter ≠ 0 ∧ enfranchisedB p b.kernel voter = true ∧ voter ∉ b.kernel.nullifiers
          ∧ b' = ⟨{ b.kernel with nullifiers := voter :: b.kernel.nullifiers },
                  b.board + g voter, (voter, g voter) :: b.log⟩ := by
  unfold castVoteW
  by_cases h0 : g voter = 0
  · rw [if_pos h0]
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨hne, _⟩
      exact absurd h0 hne
  · rw [if_neg h0]
    cases hc : castVote p b.kernel voter with
    | none =>
      constructor
      · intro h
        exact absurd h (by simp)
      · rintro ⟨_, he, hn, _⟩
        have hs : castVote p b.kernel voter
            = some { b.kernel with nullifiers := voter :: b.kernel.nullifiers } :=
          castVote_some_iff.mpr ⟨he, hn, rfl⟩
        rw [hc] at hs
        exact absurd hs (by simp)
    | some k' =>
      obtain ⟨he, hn, hk⟩ := castVote_some_iff.mp hc
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        refine ⟨h0, he, hn, ?_⟩
        rw [← h, hk]
      · rintro ⟨_, _, _, rfl⟩
        subst hk
        rfl

/-! ### The keystones — zero-weight refusal, one-cast-per-voter, authority, the exact bump. -/

/-- **ZERO-WEIGHT REFUSED (fail-closed, ballot not burned).** A zero-grant cast is `none` —
no state transition AT ALL: the board does not move AND the voter's nullifier is NOT consumed
(the refusal happens before the kernel cast), so a later genuine grant can still cast. -/
theorem castVoteW_zero_refused (p : Proposal) (g : CellId → Nat) (b : WeightedBox)
    (voter : CellId) (h : g voter = 0) : castVoteW p g b voter = none := by
  unfold castVoteW
  rw [if_pos h]

/-- A voter already in the kernel nullifier set is refused by the WEIGHTED cast — the same
seen-set gate as the unweighted `revote_rejected`, untouched by weights. -/
theorem castVoteW_spent_refused {p : Proposal} {g : CellId → Nat} {b : WeightedBox}
    {voter : CellId} (h : voter ∈ b.kernel.nullifiers) : castVoteW p g b voter = none := by
  unfold castVoteW
  by_cases h0 : g voter = 0
  · rw [if_pos h0]
  · rw [if_neg h0, revote_rejected h]

/-- **ONE-CAST-PER-VOTER PRESERVED UNDER WEIGHTS (the safety headline).** A committed
weighted cast consumes the voter's nullifier, so a SECOND weighted cast by the same voter —
at ANY weight — is refused. Weights change what a ballot is worth, never how many ballots a
voter has. -/
theorem weighted_second_cast_refused {p : Proposal} {g : CellId → Nat} {b b' : WeightedBox}
    {voter : CellId} (h : castVoteW p g b voter = some b') :
    castVoteW p g b' voter = none := by
  obtain ⟨h0, he, hn, rfl⟩ := castVoteW_some_iff.mp h
  exact castVoteW_spent_refused (List.mem_cons_self ..)

/-- **AUTHORITY carried over** — a committed weighted cast was cast by an ENFRANCHISED voter
(the registry/cap gate, inherited from `castVote`). -/
theorem castVoteW_enfranchised {p : Proposal} {g : CellId → Nat} {b b' : WeightedBox}
    {voter : CellId} (h : castVoteW p g b voter = some b') :
    enfranchisedB p b.kernel voter = true :=
  (castVoteW_some_iff.mp h).2.1

/-- **AUTHORITY fail-closed** — a non-enfranchised voter is refused by the weighted cast no
matter how large the grant: weight buys NO authority. -/
theorem unenfranchised_weighted_cast_rejected {p : Proposal} {g : CellId → Nat}
    {b : WeightedBox} {voter : CellId} (h : enfranchisedB p b.kernel voter = false) :
    castVoteW p g b voter = none := by
  unfold castVoteW
  by_cases h0 : g voter = 0
  · rw [if_pos h0]
  · rw [if_neg h0, unenfranchised_vote_rejected h]

/-- **THE EXACT BUMP** — a committed weighted cast grows the board by EXACTLY the granted
weight (the Rust `live + weight` law): never `1`, never `0`, never an amplification. -/
theorem castVoteW_board {p : Proposal} {g : CellId → Nat} {b b' : WeightedBox}
    {voter : CellId} (h : castVoteW p g b voter = some b') :
    b'.board = b.board + g voter := by
  obtain ⟨_, _, _, rfl⟩ := castVoteW_some_iff.mp h
  rfl

/-! ### §11 — WEIGHT CONSERVATION: the board is exactly the sum of granted weights of the
counted ballots, an invariant every weighted cast preserves. -/

/-- Every counted (logged) ballot is genuine: its weight IS the granted weight of its voter,
its voter is enfranchised, and its voter's nullifier is consumed (so it can never be counted
again). -/
def Counted (p : Proposal) (g : CellId → Nat) (b : WeightedBox) : Prop :=
  ∀ e ∈ b.log, e.2 = g e.1 ∧ enfranchisedB p b.kernel e.1 = true ∧ e.1 ∈ b.kernel.nullifiers

/-- **`WFW`** — the weighted-box invariant: (1) WEIGHT CONSERVATION — the board equals the
logged weight total; (2) every counted ballot is genuine (`Counted`); (3) ONE BALLOT PER
VOTER — the logged voters are pairwise distinct. -/
def WFW (p : Proposal) (g : CellId → Nat) (b : WeightedBox) : Prop :=
  b.board = logWeight b.log ∧ Counted p g b ∧ (b.log.map Prod.fst).Nodup

/-- A fresh box is well-formed (board `0` = empty log, vacuously counted, trivially
distinct). -/
theorem wfw_fresh (p : Proposal) (g : CellId → Nat) (k : RecordKernelState) :
    WFW p g (freshWBox k) := by
  refine ⟨rfl, ?_, List.nodup_nil⟩
  intro e he
  simp [freshWBox] at he

/-- **THE CONSERVATION KEYSTONE — every weighted cast preserves `WFW`.** In particular the
tally board NEVER drifts from the sum of the granted weights of the counted ballots, no
counted ballot's weight was forged (each equals its voter's grant), and no voter is counted
twice. The proof leans on the kernel nullifier: a logged voter is spent, a casting voter is
unspent, so the new voter is fresh in the log. -/
theorem castVoteW_preserves_WFW {p : Proposal} {g : CellId → Nat} {b b' : WeightedBox}
    {voter : CellId} (hwf : WFW p g b) (h : castVoteW p g b voter = some b') :
    WFW p g b' := by
  obtain ⟨hcons, hcnt, hnd⟩ := hwf
  obtain ⟨h0, he, hn, rfl⟩ := castVoteW_some_iff.mp h
  refine ⟨?_, ?_, ?_⟩
  · -- (1) conservation: board + g voter = g voter + Σ logged weights.
    show b.board + g voter = logWeight ((voter, g voter) :: b.log)
    simp only [logWeight, List.map_cons, List.sum_cons] at *
    omega
  · -- (2) every counted ballot stays genuine; the new head is genuine by construction.
    intro e hemem
    rcases List.mem_cons.mp hemem with hhd | htl
    · subst hhd
      exact ⟨rfl, he, List.mem_cons_self ..⟩
    · obtain ⟨hw, hen, hnul⟩ := hcnt e htl
      exact ⟨hw, hen, List.mem_cons_of_mem _ hnul⟩
  · -- (3) the casting voter is fresh in the log: every logged voter is spent, this one
    -- was not.
    show (((voter, g voter) :: b.log).map Prod.fst).Nodup
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, hnd⟩
    intro hmem
    obtain ⟨e, hetl, hfst⟩ := List.mem_map.mp hmem
    have hspent := (hcnt e hetl).2.2
    rw [hfst] at hspent
    exact hn hspent

/-- **THE WORK-ORDER STATEMENT, verbatim: the tally total equals the sum of the GRANTED
weights of the counted ballots.** Under `WFW`, the board is `Σ (g voter)` over the cast log —
not the logged numerals, the GRANTS: a forged log weight is already excluded by `Counted`. -/
theorem board_eq_sum_of_granted {p : Proposal} {g : CellId → Nat} {b : WeightedBox}
    (hwf : WFW p g b) : b.board = (b.log.map (fun e => g e.1)).sum := by
  obtain ⟨hcons, hcnt, _⟩ := hwf
  rw [hcons]
  unfold logWeight
  have hmap : ∀ (l : List (CellId × Nat)), (∀ e ∈ l, e.2 = g e.1) →
      (l.map Prod.snd).sum = (l.map (fun e => g e.1)).sum := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a t ih =>
      intro hall
      simp only [List.map_cons, List.sum_cons]
      rw [hall a (List.mem_cons_self ..), ih (fun e he => hall e (List.mem_cons_of_mem _ he))]
  exact hmap b.log (fun e he => (hcnt e he).1)

/-! ### §12 — WEIGHTED TEETH on the concrete fixture (decide — real discriminating
instances).

`grantsFix` grants voter `0 ↦ 50`, `1 ↦ 100`, `2 ↦ 0` (enfranchised but worthless — the
zero-weight probe), `3 ↦ 7` (an OUTSIDER with a positive grant — the weight-buys-no-authority
probe), `4 ↦ 25`. `propW` sets a WEIGHT quorum of `120` (weight units, not headcount). -/

/-- The fixture grant assignment (in deployment: the Lean-proven `grantWeightCore` verdicts). -/
def grantsFix : CellId → Nat := fun v =>
  if v = 0 then 50 else if v = 1 then 100 else if v = 3 then 7 else if v = 4 then 25 else 0

/-- The fixture weighted box over the §6 kernel fixture (no casts yet). -/
def wbox0 : WeightedBox := freshWBox voteK0

/-- A WEIGHT-quorum proposal: registry `{0,1,2}`, threshold `120` WEIGHT units. -/
def propW : Proposal := { proposalCell := 100, registry := {0, 1, 2}, threshold := 120 }

/-- A smaller weight quorum (`90`) one whale's grant (`100`) clears alone. -/
def propWhale : Proposal := { proposalCell := 100, registry := {0, 1, 2}, threshold := 90 }

/-- **TEETH (weights flow, not headcount).** Voters `0` (weight 50) and `1` (weight 100)
cast: the board is `150` — NOT `2`. The weighted engine counts weight; the bump is
`+ g voter`, not `+ 1`. -/
theorem weighted_board_is_weight_not_headcount :
    ((castVoteW propW grantsFix wbox0 0).bind
      (fun b => castVoteW propW grantsFix b 1)).map (fun b => b.board) = some 150 := by
  decide

/-- **TEETH (the weight quorum discriminates from headcount).** After the same two casts the
WEIGHT quorum `120 ≤ 150` PASSES while the HEADCOUNT `passes` (2 distinct voters against the
same threshold read as a count) does NOT — the weighted gate is genuinely reading weight. -/
theorem weighted_quorum_passes_headcount_does_not :
    ((castVoteW propW grantsFix wbox0 0).bind
      (fun b => castVoteW propW grantsFix b 1)).map
        (fun b => (passesW propW b, passes propW b.kernel)) = some (true, false) := by
  decide

/-- **TEETH (one whale is a legitimate weight quorum).** ONE voter with grant `100` clears
the `90`-weight quorum alone — with a headcount of `1`. Weighted quorum ≠ distinct-voter
quorum, by design (mirrors the deployed weighted poll's `CountGe` demanding at least one
GENUINE distinct approver while `AffineLe` reads the weight). -/
theorem single_weighted_voter_meets_weight_quorum :
    (castVoteW propWhale grantsFix wbox0 1).map
      (fun b => (passesW propWhale b, passes propWhale b.kernel)) = some (true, false) := by
  decide

/-- **TEETH (sub-quorum weight refused).** One cast of weight `50` does NOT pass the
`120`-weight quorum. -/
theorem subquorum_weight_does_not_pass :
    (castVoteW propW grantsFix wbox0 0).map (fun b => passesW propW b) = some false := by
  decide

/-- **TEETH (second cast by the same voter refused, weights notwithstanding).** Voter `0`
casts (weight 50), then re-casts: the second cast is `none` — the kernel nullifier gate — so
the board holds exactly ONE ballot's weight. -/
theorem weighted_double_cast_refused_fixture :
    ((castVoteW propW grantsFix wbox0 0).bind
      (fun b => castVoteW propW grantsFix b 0)) = none
    ∧ (castVoteW propW grantsFix wbox0 0).map (fun b => b.board) = some 50 := by
  constructor
  · decide
  · decide

/-- **TEETH (a zero-weight cast changes NOTHING — and the refusal is SPECIFICALLY the
weight).** Voter `2` is enfranchised (registry) and unspent — the UNWEIGHTED cast admits it —
yet its grant is `0`, so the weighted cast is `none`: no board move, no nullifier burn. -/
theorem zero_weight_cast_changes_nothing :
    castVoteW propW grantsFix wbox0 2 = none
    ∧ (castVote propW voteK0 2).isSome = true := by
  constructor
  · decide
  · decide

/-- **TEETH (weight buys no authority).** Voter `3` carries a POSITIVE grant (`7`) but is an
outsider (not in the registry, no vote-cap): the weighted cast is refused. Enfranchisement is
the same gate as ever; the grant cannot open it. -/
theorem outsider_weight_buys_nothing :
    castVoteW propW grantsFix wbox0 3 = none := by
  decide

/-- **DEGENERACY CHECK (unit weights recover headcount).** Under the constant grant `1`, the
weighted board after two casts equals the unweighted distinct-enfranchised tally (`2`) — the
weighted engine strictly generalizes the unweighted one. -/
theorem unit_weights_recover_headcount :
    ((castVoteW prop0 (fun _ => 1) wbox0 0).bind
      (fun b => castVoteW prop0 (fun _ => 1) b 1)).map
        (fun b => (b.board, tally prop0 b.kernel)) = some (2, 2) := by
  decide

/-! ### `#guard` smoke — the weighted laws, decided by the model alone. -/

-- weights flow: 50 + 100 = 150 on the board, log holds both grants.
#guard (((castVoteW propW grantsFix wbox0 0).bind
          (fun b => castVoteW propW grantsFix b 1)).map
            (fun b => (b.board, logWeight b.log))) == some (150, 150)
-- zero-weight cast refused outright; the unweighted gate would have admitted the voter.
#guard (castVoteW propW grantsFix wbox0 2).isSome == false
#guard (castVote propW voteK0 2).isSome == true
-- double weighted cast refused; board keeps exactly one ballot's weight.
#guard (((castVoteW propW grantsFix wbox0 0).bind
          (fun b => castVoteW propW grantsFix b 0))).isSome == false
-- outsider with positive weight refused.
#guard (castVoteW propW grantsFix wbox0 3).isSome == false
-- weight quorum: 150 ≥ 120 passes; 50 < 120 does not.
#guard (((castVoteW propW grantsFix wbox0 0).bind
          (fun b => castVoteW propW grantsFix b 1)).map (passesW propW ·)) == some true
#guard ((castVoteW propW grantsFix wbox0 0).map (passesW propW ·)) == some false

/-! ### §13 — Axiom hygiene for the weighted keystones. -/

#assert_axioms castVote_some_iff
#assert_axioms castVoteW_some_iff
#assert_axioms castVoteW_zero_refused
#assert_axioms castVoteW_spent_refused
#assert_axioms weighted_second_cast_refused
#assert_axioms castVoteW_enfranchised
#assert_axioms unenfranchised_weighted_cast_rejected
#assert_axioms castVoteW_board
#assert_axioms wfw_fresh
#assert_axioms castVoteW_preserves_WFW
#assert_axioms board_eq_sum_of_granted
#assert_axioms weighted_board_is_weight_not_headcount
#assert_axioms weighted_quorum_passes_headcount_does_not
#assert_axioms single_weighted_voter_meets_weight_quorum
#assert_axioms subquorum_weight_does_not_pass
#assert_axioms weighted_double_cast_refused_fixture
#assert_axioms zero_weight_cast_changes_nothing
#assert_axioms outsider_weight_buys_nothing
#assert_axioms unit_weights_recover_headcount

end Dregg2.Apps.MultisigVote
