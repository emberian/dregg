/-
# Dregg2.Distributed.RoundAdvanceGate — the EVENTUAL-SYNCHRONY round-advance gate
# (Cordial Miners Alg. 4 lines 67–75), authored HERE and exported to the node.

**The defect this closes** (`docs/reference/READING-DAG-BFT-2026-08-08.md` §5.3). Cordial Miners
(arXiv:2205.09174) gives TWO protocol instances that differ in *both* leader election and round
advance, and §6.2 says the pairing is deliberate:

  * ASYNCHRONY (w = 5): retrospective shared-coin leader, advance **as soon as the round is
    cordial** (Alg. 4:59 — `es_advance_round` is a no-op).
  * EVENTUAL SYNCHRONY (w = 3): prospective round-robin leader, advance **only when the leader
    block is present / ratified / super-ratified — or a timeout fires** (Alg. 4:67–75).

The node runs the ES half of leader election (`wave_leader`, round-robin, published in genesis)
with the ASYNC half of round advance (`node/src/blocklace_sync.rs::plan_round_block` — cordiality
alone, no leader clause, no timer). CM §6.2, on why the ES clauses exist: *"These conditions are to
prevent the adversary from ordering the messages after GST, in particular, the leader block and the
blocks that super-ratify it, **as the leader is known in advance**."* And CM Prop. 38 (ES
leader-liveness w.p. 1) is stated **only** under `timeout > ∆`. The mixed halves are a LIVENESS
hole: an adversary controlling delivery keeps the (publicly known) leader's block out of the
fastest 2f+1 arrivals at each wave-start round and no wave ever anchors; and without any adversary,
a persistently slow leader loses its `1/n` of all waves, deterministically.

**This module is the missing half, authored in Lean** (consensus rules are AUTHORED IN LEAN; Rust
only calls the exported artifact). It defines the line-67 predicate over the SAME executable
vocabulary as the verified finalization rule (`BlocklaceFinality`: `roundOf`, `waveLeader`,
`leaderCandidates`, `approves`, `isSuperRatified`), proves the spec-level facts the node relies on,
and exposes the decision as `@[export] dregg_round_advance` (the `FinalityGate` /
`StrandAdmission` wire template). `node/src/blocklace_sync.rs::produce_round_block` consults it
before honoring a `RoundPlan::Advance`.

## The rule, translated to this repo's 1-indexed rounds

CM's rounds are 0-indexed (wave-start ⟺ `r mod w = 0`); the node's are 1-indexed with wave 0 =
rounds `[1, w]` (`ordering.rs::round_to_wave`), so the wave POSITION of round `r` is
`(r − 1) mod w`. For the round `r` a producer wants to COMPLETE (it is at `my_max_round = r` and
wants to author `r+1`):

```
advanceGate B P w r timeout :=
  cordialRound r                    -- Alg. 1:25–26: a supermajority of distinct enrolled
                                    --   participants have a block at round r
  ∧ ( pos = 0     ⟹ the wave leader has a block at round r            -- Alg. 4:69–70
    ∧ pos = 1     ⟹ that leader block is ratified by prefix(r)        -- Alg. 4:71–72
    ∧ pos = w − 1 ⟹ that leader block is SUPER-ratified at round r    -- Alg. 4:73–74
    ∨ timeout )                                                       -- Alg. 4:75
```

`timeout` is an INPUT BIT, deliberately: the CLOCK is I/O and lives in Rust (the node measures
elapsed time from the first instant round `r` was observed cordial, against the configured
`round_advance_timeout_ms`, which MUST exceed the assumed post-GST delay bound ∆ — Prop. 38's
hypothesis; the node states its ∆ assumption where the config is defined). The RULE — what the bit
unlocks and what it never unlocks — is decided here. `timeout_does_not_bypass_cordiality` pins the
never-half: CM's line 68 conjunction puts cordiality OUTSIDE the `∨ timeout`.

## Two deliberate deviations from the paper's letter, both named

1. **The wave-end clause uses the DEPLOYED finality predicate** `isSuperRatified` (ratifiers
   counted among WAVE-END-round blocks only, B6-enrollment-gated) rather than the paper's
   `super_ratifies(blocklace_prefix(r), b)` (ratifiers anywhere in the prefix). Wave-end-only
   ratifier counting is what `finalLeaderAt` — the rule that decides whether the wave ANCHORS —
   actually requires, so gating on it makes "advance past the wave end" wait for exactly the
   condition finality needs, not a weaker cousin that can pass while τ still skips the wave. It is
   STRICTER than the paper's clause (wave-end blocks ⊆ prefix blocks), and the `∨ timeout` arm is
   untouched, so Prop. 38's liveness argument (which only needs the timeout arm plus post-GST
   delivery) is unaffected.
2. **Cordiality counts ENROLLED participants only** (the B6 ratifier-enrollment discipline),
   where the Rust `plan_round_block` counts ANY distinct creator at the round. An unenrolled
   creator's block must not help a round LOOK complete any more than it may help a leader look
   super-ratified. The Rust cordiality check stays as the cheap pre-filter and diagnostic
   (`RoundPlan::Wait` carries the wedge telemetry); THIS predicate is the decider, and it is the
   stricter of the two, so the composition (Rust-cordial ∧ this gate) equals this gate.

The middle-round clause (`pos = 1`, and every non-end position for a hypothetical `w ≠ 3`;
deployed `w = 3` — `ordering.rs::OrderingConfig::default`, `node/src/finality_gate.rs::WAVELENGTH`)
is the paper's `ratifies(blocklace_prefix(r), b)` transliterated (`prefixRatifies`), with the
approver count enrollment-filtered for the same B6 reason. `wavelength = 0` is out of contract and
fails the clause (the gate then advances only on cordial ∧ timeout — fail-safe, never fail-open).

## What this module does NOT do

It does not change WHO the leader is (`waveLeader` stays round-robin — completing the ES instance,
not switching to the async one, is the design choice; the async instance needs a retrospective
shared coin this tree does not have), does not touch τ / finalization, and does not measure time.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}) for the spec theorems;
concrete-trace instances are `native_decide` + `#assert_compiled` (chosen when the round map rode
`Array.qsort`, which does not kernel-reduce under `decide`; since dregg issue #100 it is a
structural Kahn fold that does, so these could be restated with `decide` — not done here). Verified with `lake build Dregg2.Distributed.RoundAdvanceGate`.
-/
import Dregg2.Distributed.BlocklaceFinality
import Dregg2.Distributed.FinalityGate

namespace Dregg2.Distributed.RoundAdvanceGate

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)
open Dregg2.Distributed.BlocklaceFinality
  (superMajority roundOf roundToWave waveFirstRound waveLastRound waveLeader
   leaderCandidates approves isSuperRatified
   PastCache RoundCache mkPastCache mkRoundCache roundOfR approvesC isSuperRatifiedC
   leaderCandidatesR roundOfR_eq approvesC_eq isSuperRatifiedC_eq leaderCandidatesR_eq
   trace3 trace3Participants)
open Dregg2.Distributed.FinalityGate
  (parseNat? stripReq? decodeLaceWire encodeLaceWire)

/-! ## 1. The predicate, in the finalization rule's own vocabulary. -/

/-- The wave POSITION of a 1-indexed round: `0` = wave-start round, `wavelength − 1` = wave-end
round. (CM's 0-indexed `r mod w`, shifted: our round 1 is CM's round 0.) -/
def wavePos (r wavelength : Nat) : Nat := (r - 1) % wavelength

/-- **`cordialRound`** — CM Alg. 1:25–26 `cordial_round(r)`: a supermajority of distinct ENROLLED
participants have a block at round `r`. This is the ONLY clause the node's `plan_round_block`
checks today (with the divergence that it counts any creator; see the module docstring — this
enrolled count is the decider, and stricter). -/
def cordialRound (B : Lace) (participants : List AuthorId) (r : Nat) : Bool :=
  (participants.filter (fun p =>
    B.any (fun b => b.creator == p && roundOf B participants b.id == r))).length
    ≥ superMajority participants.length

/-- **`prefixRatifies`** — CM Alg. 1:18–19 `ratifies(blocklace_prefix(r), l)`: a supermajority of
distinct ENROLLED participants have a block at depth ≤ `r` that `approves` the leader block `l`
(the prefix is downward-closed, so "in the closure of the prefix" is "at depth ≤ r"). The
`pos = 1` clause of Alg. 4:71–72 ("second round of the wave: the round-(r−1) leader is ratified"). -/
def prefixRatifies (B : Lace) (participants : List AuthorId) (r : Nat) (l : Block) : Bool :=
  (participants.filter (fun p =>
    B.any (fun b => b.creator == p && roundOf B participants b.id ≤ r
                    && approves B participants b l))).length
    ≥ superMajority participants.length

/-- **`leaderClause`** — CM Alg. 4:69–74, the position-dependent leader condition for completing
round `r`. The wave-start leader blocks are `leaderCandidates` (creator = `waveLeader`, depth =
wave-start round); `∃b` in the paper is `List.any` here — an equivocating leader (two slot blocks)
can still satisfy the clause, and that is CORRECT for an ADVANCE gate: τ will skip such a wave
regardless (`finalLeaderAt` requires a UNIQUE candidate), and holding the round for it would buy
nothing but the timeout. `wavelength = 0` fails the clause (out of contract, fail-safe). -/
def leaderClause (B : Lace) (participants : List AuthorId) (wavelength r : Nat) : Bool :=
  if wavelength == 0 then false else
  let w := roundToWave r wavelength
  let pos := wavePos r wavelength
  if pos == 0 then
    -- wave-start round: the wave leader has a block AT round r (Alg. 4:69–70).
    !(leaderCandidates B participants w wavelength).isEmpty
  else if pos == wavelength - 1 then
    -- wave-end round: the wave-start leader block is super-ratified at round r (Alg. 4:73–74) —
    -- by the DEPLOYED `isSuperRatified` (wave-end ratifiers, B6-gated), the exact predicate
    -- `finalLeaderAt` anchors on. Deviation 1 in the module docstring.
    (leaderCandidates B participants w wavelength).any
      (fun l => isSuperRatified B participants l r)
  else
    -- middle round(s): the wave-start leader block is ratified by the prefix (Alg. 4:71–72).
    (leaderCandidates B participants w wavelength).any
      (fun l => prefixRatifies B participants r l)

/-- **THE GATE** — CM Alg. 4:67–75 for one round: complete round `r` (author `r+1`) iff the round
is cordial AND (the leader clause holds OR the timeout fired). `timeoutFired` is the Rust-measured
clock bit (elapsed-since-cordial ≥ `round_advance_timeout_ms > ∆`); the rule around it is decided
here. Note the conjunction shape: cordiality is OUTSIDE the disjunction — a timeout never advances
a round the committee has not filled (`timeout_does_not_bypass_cordiality`). -/
def advanceGate (B : Lace) (participants : List AuthorId) (wavelength r : Nat)
    (timeoutFired : Bool) : Bool :=
  cordialRound B participants r
    && (leaderClause B participants wavelength r || timeoutFired)

/-! ## 2. The memoized fast path (the `…C`/`…R` discipline of `BlocklaceFinality` §"THE ROUND
CACHE"), each twin proved equal to its pure original at the canonical caches — so the EXPORT runs
the memoized stack and the theorems speak about the pure rule. -/

/-- `cordialRound` against a precomputed round cache. -/
def cordialRoundR (rc : RoundCache) (B : Lace) (participants : List AuthorId) (r : Nat) : Bool :=
  (participants.filter (fun p =>
    B.any (fun b => b.creator == p && roundOfR rc b.id == r))).length
    ≥ superMajority participants.length

theorem cordialRoundR_eq (B : Lace) (P : List AuthorId) (r : Nat) :
    cordialRoundR (mkRoundCache B P) B P r = cordialRound B P r := rfl

/-- `prefixRatifies` with both caches. -/
def prefixRatifiesC (B : Lace) (cache : PastCache) (rc : RoundCache)
    (participants : List AuthorId) (r : Nat) (l : Block) : Bool :=
  (participants.filter (fun p =>
    B.any (fun b => b.creator == p && roundOfR rc b.id ≤ r
                    && approvesC B cache rc b l))).length
    ≥ superMajority participants.length

theorem prefixRatifiesC_eq (B : Lace) (P : List AuthorId) (r : Nat) (l : Block) :
    prefixRatifiesC B (mkPastCache B) (mkRoundCache B P) P r l = prefixRatifies B P r l := by
  -- Function-level rewrite (no simp-under-binder: the `decide` instances inside the lambdas
  -- resist congruence): `approvesC` at the canonical caches IS `approves`, as a function; the
  -- residual `roundOfR (mkRoundCache B P)` / `roundOf B P` difference is definitional.
  have ha : approvesC B (mkPastCache B) (mkRoundCache B P) = approves B P :=
    funext fun o => funext fun l' => approvesC_eq B P o l'
  have hr : roundOfR (mkRoundCache B P) = roundOf B P :=
    funext fun h => roundOfR_eq B P h
  unfold prefixRatifiesC prefixRatifies
  rw [ha, hr]

/-- `leaderClause` with both caches. -/
def leaderClauseC (B : Lace) (cache : PastCache) (rc : RoundCache)
    (participants : List AuthorId) (wavelength r : Nat) : Bool :=
  if wavelength == 0 then false else
  let w := roundToWave r wavelength
  let pos := wavePos r wavelength
  if pos == 0 then
    !(leaderCandidatesR rc B participants w wavelength).isEmpty
  else if pos == wavelength - 1 then
    (leaderCandidatesR rc B participants w wavelength).any
      (fun l => isSuperRatifiedC B cache rc participants l r)
  else
    (leaderCandidatesR rc B participants w wavelength).any
      (fun l => prefixRatifiesC B cache rc participants r l)

theorem leaderClauseC_eq (B : Lace) (P : List AuthorId) (wavelength r : Nat) :
    leaderClauseC B (mkPastCache B) (mkRoundCache B P) P wavelength r
      = leaderClause B P wavelength r := by
  have hlc : leaderCandidatesR (mkRoundCache B P) B P = leaderCandidates B P :=
    funext fun w' => funext fun wl => leaderCandidatesR_eq B P w' wl
  have hsr : isSuperRatifiedC B (mkPastCache B) (mkRoundCache B P) P = isSuperRatified B P :=
    funext fun l => funext fun e => isSuperRatifiedC_eq B P l e
  have hpr : prefixRatifiesC B (mkPastCache B) (mkRoundCache B P) P = prefixRatifies B P :=
    funext fun r' => funext fun l => prefixRatifiesC_eq B P r' l
  unfold leaderClauseC leaderClause
  rw [hlc, hsr, hpr]

/-- **`advanceGateFast`** — the gate with the causal-past and round maps computed ONCE. This is
what the export runs; `advanceGateFast_eq` carries every theorem about `advanceGate` onto it. -/
def advanceGateFast (B : Lace) (participants : List AuthorId) (wavelength r : Nat)
    (timeoutFired : Bool) : Bool :=
  let cache := mkPastCache B
  let rc := mkRoundCache B participants
  cordialRoundR rc B participants r
    && (leaderClauseC B cache rc participants wavelength r || timeoutFired)

theorem advanceGateFast_eq (B : Lace) (P : List AuthorId) (wavelength r : Nat) (t : Bool) :
    advanceGateFast B P wavelength r t = advanceGate B P wavelength r t := by
  show (cordialRoundR (mkRoundCache B P) B P r
          && (leaderClauseC B (mkPastCache B) (mkRoundCache B P) P wavelength r || t))
      = advanceGate B P wavelength r t
  unfold advanceGate
  rw [cordialRoundR_eq, leaderClauseC_eq]

/-! ## 3. The spec theorems — the two poles and the two "never"s, as facts about the rule. -/

/-- **The gate's whole truth condition**, as an iff — CM line 67–75 restated. Everything below is a
corollary, named separately because each is a distinct promise the node relies on. -/
theorem advance_iff (B : Lace) (P : List AuthorId) (wavelength r : Nat) (t : Bool) :
    advanceGate B P wavelength r t = true ↔
      (cordialRound B P r = true
        ∧ (leaderClause B P wavelength r = true ∨ t = true)) := by
  unfold advanceGate
  simp [Bool.and_eq_true, Bool.or_eq_true]

/-- **POLE 1 (promptness).** With the leader clause satisfied, a cordial round advances with NO
timeout — the good case pays nothing for the gate. -/
theorem leader_advances_promptly {B : Lace} {P : List AuthorId} {wavelength r : Nat}
    (hc : cordialRound B P r = true) (hl : leaderClause B P wavelength r = true) :
    advanceGate B P wavelength r false = true := by
  unfold advanceGate; rw [hc, hl]; rfl

/-- **POLE 2 (no early advance).** Without the leader clause and without the timeout, the gate
REFUSES — no matter how supermajor the cohort is. This is the exact bit `plan_round_block` was
missing: cordiality alone (the asynchrony rule, Alg. 4:59) no longer advances the round. -/
theorem no_early_advance {B : Lace} {P : List AuthorId} {wavelength r : Nat}
    (h : leaderClause B P wavelength r = false) :
    advanceGate B P wavelength r false = false := by
  unfold advanceGate; rw [h]; simp

/-- **POLE 2's escape (liveness).** The timeout restores the advance on any cordial round — a dead
or withheld leader stalls the committee for at most `timeout` (Prop. 38 needs `timeout > ∆`; the
clock and its bound live in Rust). -/
theorem timeout_advances {B : Lace} {P : List AuthorId} {wavelength r : Nat}
    (hc : cordialRound B P r = true) :
    advanceGate B P wavelength r true = true := by
  unfold advanceGate; rw [hc]; simp

/-- **NEVER 1.** The timeout does NOT bypass cordiality: line 68's conjunction puts
`cordial_round(r)` outside the `∨ timeout`. A timer can un-stick a leaderless round; it can never
advance a round the committee has not filled. -/
theorem timeout_does_not_bypass_cordiality {B : Lace} {P : List AuthorId} {wavelength r : Nat}
    (hc : cordialRound B P r = false) (t : Bool) :
    advanceGate B P wavelength r t = false := by
  unfold advanceGate; rw [hc]; rfl

/-- **NEVER 2.** Any advance implies cordiality — the gate only ever STRENGTHENS the old rule
(old = cordiality alone), it cannot weaken it. "It is greenfield" is never a reason to verify
less; this is the theorem form of that sentence for this gate. -/
theorem advance_requires_cordiality {B : Lace} {P : List AuthorId} {wavelength r : Nat} {t : Bool}
    (h : advanceGate B P wavelength r t = true) : cordialRound B P r = true := by
  unfold advanceGate at h
  exact ((Bool.and_eq_true _ _).mp h).1

#assert_axioms advance_iff
#assert_axioms leader_advances_promptly
#assert_axioms no_early_advance
#assert_axioms timeout_advances
#assert_axioms timeout_does_not_bypass_cordiality
#assert_axioms advance_requires_cordiality
#assert_axioms advanceGateFast_eq

/-! ## 4. Concrete traces — both poles WITNESSED, not just implied.

The refusal pole needs a lace that is CORDIAL-BUT-LEADERLESS, or the refusal theorem is satisfied
by any starving round and says nothing about the leader clause. At n=3 that shape cannot exist
(`superMajority 3 = 3` — every cordial round contains everyone), so the witness is n=4
(`superMajority 4 = 3`): creators 2,3,4 fill round 1, the wave-0 round-robin leader (participant
1) is silent. `noLeader_r1_cordial` is the anti-vacuity leg — the refusal below is attributable to
the LEADER clause, not to cordiality. -/

/-- n=4, round 1 filled by creators 2,3,4 — cordial (3 ≥ superMajority 4 = 3), leader (participant
1, wave 0) ABSENT. -/
def traceNoLeader : Lace := [⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩, ⟨40,4,0,[],true⟩]

/-- `traceNoLeader` grown by a full round 2 (still no participant-1 block anywhere): the stall
continues at wave position 1 — the whole wave waits for its timeout, round by round, exactly CM's
per-round timeout shape. -/
def traceNoLeader2 : Lace :=
  traceNoLeader ++ [⟨21,2,1,[20,30,40],true⟩, ⟨31,3,1,[20,30,40],true⟩, ⟨41,4,1,[20,30,40],true⟩]

/-- The n=4 participant roster the no-leader traces run under. -/
def nl4 : List AuthorId := [1, 2, 3, 4]

/-- n=4 with ONE creator at round 1 — NOT cordial. The timeout-cannot-bypass-cordiality witness. -/
def traceThin : Lace := [⟨20,2,0,[],true⟩]

/-- n=1 (the live Path-of-Angels shape since 08-05): the solo validator IS every wave's leader. -/
def traceSolo : Lace := [⟨10,1,0,[],true⟩]

-- ── POLE 1 on the 3-node golden trace: all three wave positions advance PROMPTLY (no timeout).
-- Round 1 = wave-start (leader block 10 present), round 2 = middle (10 prefix-ratified), round 3 =
-- wave-end (10 super-ratified — the same fact that lets `finalLeaderAt` anchor wave 0).
theorem trace3_wave_start_prompt :
    advanceGate trace3 trace3Participants 3 1 false = true := by native_decide
theorem trace3_mid_round_prompt :
    advanceGate trace3 trace3Participants 3 2 false = true := by native_decide
theorem trace3_wave_end_prompt :
    advanceGate trace3 trace3Participants 3 3 false = true := by native_decide

-- ── n=1: the solo validator never waits on this gate (it is its own leader).
theorem solo_advances_promptly :
    advanceGate traceSolo [1] 3 1 false = true := by native_decide

-- ── POLE 2, with its anti-vacuity leg first: the round IS cordial, the clause alone refuses.
theorem noLeader_r1_cordial :
    cordialRound traceNoLeader nl4 1 = true := by native_decide
theorem noLeader_r1_clause_false :
    leaderClause traceNoLeader nl4 3 1 = false := by native_decide
theorem noLeader_r1_refuses :
    advanceGate traceNoLeader nl4 3 1 false = false := by native_decide
theorem noLeader_r1_timeout_advances :
    advanceGate traceNoLeader nl4 3 1 true = true := by native_decide

-- ── the stall persists at wave position 1 (round 2) and the timeout unsticks it there too.
theorem noLeader_r2_refuses :
    advanceGate traceNoLeader2 nl4 3 2 false = false := by native_decide
theorem noLeader_r2_timeout_advances :
    advanceGate traceNoLeader2 nl4 3 2 true = true := by native_decide

-- ── NEVER 1 witnessed: a non-cordial round stays shut even with the timeout bit set.
theorem thin_timeout_is_not_enough :
    advanceGate traceThin nl4 3 1 true = false := by native_decide

-- ── the memoized path agrees with the pure rule on a concrete instance (belt over
--    `advanceGateFast_eq`, exercising the caches the export actually runs).
theorem fast_agrees_trace3 :
    advanceGateFast trace3 trace3Participants 3 2 false = true := by native_decide
theorem fast_agrees_noLeader :
    advanceGateFast traceNoLeader nl4 3 1 false = false := by native_decide

#assert_compiled trace3_wave_start_prompt
#assert_compiled trace3_mid_round_prompt
#assert_compiled trace3_wave_end_prompt
#assert_compiled solo_advances_promptly
#assert_compiled noLeader_r1_cordial
#assert_compiled noLeader_r1_clause_false
#assert_compiled noLeader_r1_refuses
#assert_compiled noLeader_r1_timeout_advances
#assert_compiled noLeader_r2_refuses
#assert_compiled noLeader_r2_timeout_advances
#assert_compiled thin_timeout_is_not_enough
#assert_compiled fast_agrees_trace3
#assert_compiled fast_agrees_noLeader

/-! ## 5. THE WIRE — `@[export] dregg_round_advance`, the `FinalityGate`/`StrandAdmission`
template. The lace segment REUSES `FinalityGate.decodeLaceWire` (one grammar, one Rust encoder —
`node/src/finality_gate.rs::build_wire` — for every consensus gate), prefixed by the two inputs
this gate adds.

```
INPUT  := "r=" Nat ";t=" ("0"|"1") ";" LACEWIRE      -- round to complete; timeout bit;
LACEWIRE := "w=" Nat ";P=" ... ";B=" ...             --   FinalityGate's (wavelength, P, lace)
OUTPUT := "1" (advance) | "0" (hold) | "ERR"          -- fail-closed: malformed ⇒ ERR ⇒ the node
                                                      --   HOLDS (a parse failure never advances)
```
-/

/-- Decode the advance-gate wire. Fail-closed on any deviation, including a timeout field that is
neither `"0"` nor `"1"`. -/
def decodeAdvanceWire (s : String) :
    Option (Nat × Bool × Nat × List AuthorId × Lace) := do
  let rest ← stripReq? "r=" s
  match rest.splitOn ";" with
  | rS :: tSeg :: tail =>
      let r ← parseNat? rS
      let tS ← stripReq? "t=" tSeg
      let t ← (match tS with
                | "1" => some true
                | "0" => some false
                | _   => none)
      let (w, parts, B) ← decodeLaceWire (String.intercalate ";" tail)
      some (r, t, w, parts, B)
  | _ => none

/-- Encode an advance-gate query (the inverse the node's Rust encoder mirrors). -/
def encodeAdvanceWire (r : Nat) (t : Bool) (w : Nat) (parts : List AuthorId) (B : Lace) :
    String :=
  "r=" ++ toString r ++ ";t=" ++ (if t then "1" else "0") ++ ";"
    ++ encodeLaceWire w parts B

/-- **The gate body**: decode ⤳ `advanceGateFast` ⤳ `"1"`/`"0"`, `"ERR"` fail-closed. -/
def advanceWireGate (s : String) : String :=
  match decodeAdvanceWire s with
  | some (r, t, w, parts, B) => if advanceGateFast B parts w r t then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_round_advance]` — the C-ABI entry the node's FFI bridge
(`dregg-lean-ffi/src/distributed_ffi.rs::shadow_round_advance`) calls before honoring a
`RoundPlan::Advance`. -/
@[export dregg_round_advance]
def dregg_round_advance (s : String) : String := advanceWireGate s

/-- **The export carries the proof** (`strand_admit_eq_admitted`'s shape): for any wire that
decodes, the exported verdict IS the verified `advanceGate` — so the node consulting the export is
consulting the rule the theorems above are about, by construction. -/
theorem round_advance_eq_gate (s : String) (r : Nat) (t : Bool) (w : Nat)
    (parts : List AuthorId) (B : Lace)
    (h : decodeAdvanceWire s = some (r, t, w, parts, B)) :
    dregg_round_advance s = (if advanceGate B parts w r t then "1" else "0") := by
  unfold dregg_round_advance advanceWireGate
  rw [h]
  simp only [advanceGateFast_eq]

#assert_axioms round_advance_eq_gate

-- ── wire-level witnesses: round-trip, both verdicts, and the fail-closed sentinel.
theorem wire_roundtrip_trace3 :
    decodeAdvanceWire (encodeAdvanceWire 2 false 3 trace3Participants trace3)
      = some (2, false, 3, trace3Participants, trace3) := by native_decide
theorem wire_advances_trace3 :
    advanceWireGate (encodeAdvanceWire 2 false 3 trace3Participants trace3) = "1" := by
  native_decide
theorem wire_holds_noLeader :
    advanceWireGate (encodeAdvanceWire 1 false 3 nl4 traceNoLeader) = "0" := by native_decide
theorem wire_timeout_advances_noLeader :
    advanceWireGate (encodeAdvanceWire 1 true 3 nl4 traceNoLeader) = "1" := by native_decide
theorem wire_malformed_errs :
    advanceWireGate "not a wire" = "ERR" := by native_decide
theorem wire_bad_timeout_bit_errs :
    advanceWireGate "r=1;t=2;w=3;P=1,2,3;B=" = "ERR" := by native_decide

#assert_compiled wire_roundtrip_trace3
#assert_compiled wire_advances_trace3
#assert_compiled wire_holds_noLeader
#assert_compiled wire_timeout_advances_noLeader
#assert_compiled wire_malformed_errs
#assert_compiled wire_bad_timeout_bit_errs

end Dregg2.Distributed.RoundAdvanceGate
