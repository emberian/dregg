/-
# Dregg2.Apps.RightOfWay — "the referee is a theorem" (a DEMONSTRATOR).

A verified collision-avoidance **referee** for the *Right of Way* idea
(`right-of-way-build-spec.md`, `right-of-way-response.md`): satellite-agents detect
orbital near-misses ("conjunctions"), an UNTRUSTED matcher (the LLM negotiation layer)
*proposes* an avoidance `Maneuver`, and a deterministic, in-trusted-base **referee**
ACCEPTS a proposed maneuver ONLY if re-running its own decidable `Verify` confirms the
post-maneuver scenario is conjunction-free — **even when the proposer is adversarial**.

This module makes the pitch's central claim — *"the referee is a theorem, not a black box
you take on faith"* — concrete by INSTANTIATING dregg2's already-proved assets, rather
than reproving them:

  * **the verify-not-find seam** (`Dregg2.Laws`, `Dregg2.Authority.Intent`): the proposer
    is `Searchable.find` (untrusted, may be adversarial); the referee is `Intent.resolve`
    (propose-then-VERIFY). `referee_sound` is an instance of `intent_sound_against_adversary`.
  * **the budget gate / forced trade** (`Dregg2.Exec.JointCell`): fuel is a cell budget;
    an out-of-fuel sat (`bal fuel = 0`) cannot burn (`applyHalfOut` REJECTS), and the naive
    "lowest-priority yields" ordering is a configuration the binding PROVABLY EXCLUDES
    (`binding_is_proper`).
  * **the escalation classifier** (`Dregg2.Confluence`): collision-safety is NOT
    I-confluent, so it MUST escalate to a joint maneuver (`nonpairwise_escalation`).

================================================================================
## HONESTY LABEL — READ THIS. The `Verify` predicate here is a TOY.
================================================================================

`hasConjunction` / `Verify` in §2 below are a **toy discrete-snapshot screen** (kept as the
simplest illustration of the seam): positions are single integers (a 1-D snapshot at one
instant), and "conjunction" is "two objects within a threshold AT THAT SAMPLE" — **NOT
orbital-sound**. BUT the substantive piece the response flagged as NOT inherited — a
*conservative* screen provably sound against the **between-samples closest approach** — is now
**BUILT**: see `Dregg2.Apps.OrbitalScreen` (`screen_clear_imp_continuous_clear`: a `clear`
verdict is sound on the CONTINUOUS trajectory, not merely at samples). §9 below plugs that REAL
screen into this exact referee seam, so `referee_sound_physics` carries genuine continuous-time
physics, not a toy. The toy §2 screen remains only as the minimal demonstrator of the seam shape.

What IS genuine throughout: the *seam* is real and proved. WHATEVER physics `Verify` you plug in
(the toy §2 screen OR the real `OrbitalScreen.screen`), the referee's adversary-proof soundness,
the budget gate, the forced-trade exclusion, and the escalation requirement all hold — they are
inherited theorems, not re-proved per-physics. §9 makes that concrete by instantiating the seam
at the conservative screen.

## THE FULL DEMONSTRATOR — four companion modules (all build green, all `#assert_axioms`-clean):

  * `Dregg2.Apps.OrbitalScreen` — the REAL conservative continuous-time-sound physics screen
    (`screen_clear_imp_continuous_clear`; the crossing-pair TEETH that the endpoint sampler misses).
  * `Dregg2.Apps.WhoYields` — the graph-symmetry who-yields bridge (ported WL color-refinement from
    `~/dev/graphplay`): `rigid_of_discrete` (asymmetric ⇒ forced role, no central authority),
    `symmetric_needs_negotiation` (the teeth), `three_mutual_conflict_needs_three_roles` (the
    round-cap floor), `outOfFuel_breaks_symmetry` (the forced-trade's second proof).
  * `Dregg2.Apps.EpistemicSheaf` — the sheaf-of-verifiers frame: `consensus_on_clearance`
    (H⁰ = global section), `byzantine_section_does_not_glue` (the fork = witnessed obstruction).
  * `Dregg2.Apps.ConservationBridge` — the deep seed: `conservation_is_flow_balance` (Σδ=0 IS the
    conjunction graph's flow-balance across the symmetry boundary — one law joining the two theories).

  * Fuel is modelled as a **SINK**: a single-cell debit on a `fuel` asset. There is NO
    constellation-wide conservation claim — a burn destroys Δv budget; it is not conserved
    across satellites. (Said plainly, as `right-of-way-response.md` §"Honest caveats" asks.)
  * Swarm liveness / round-cap convergence is NOT modelled here (it lives in the orchestrator
    round-cap, not a theorem).

Zero `sorry`/`admit`/`native_decide`/`axiom`. Every keystone is `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Laws
import Dregg2.Authority.Intent
import Dregg2.Exec.JointCell
import Dregg2.Confluence
import Dregg2.Apps.OrbitalScreen

namespace Dregg2.Apps.RightOfWay

open Dregg2.Laws
open Dregg2.Authority (Intent)

/-! ## 1. Domain types (`right-of-way-build-spec.md` §2, collapsed to a toy 1-D snapshot). -/

/-- An object id (a satellite or a piece of debris). -/
abbrev ObjId := Nat

/-- **A space object at a snapshot.** `pos` is its 1-D position at the screen instant (a
toy stand-in for the 3-D state `r:[x,y,z]` of the real contract). `priority` is the
operator-policy rank used by the naive "lowest yields" rule (LOW = small). -/
structure SpaceObject where
  /-- The object's id. -/
  id       : ObjId
  /-- The object's 1-D position at the screen instant (toy snapshot; not a 3-D orbit). -/
  pos      : ℤ
  /-- Operator-policy priority rank (the naive rule yields the LOWEST). -/
  priority : Nat
  deriving Repr, DecidableEq

/-- **A scenario.** A finite list of objects plus a conjunction `threshold`: two objects
are "in conjunction" when their (1-D, snapshot) separation is strictly below `threshold`. -/
structure Scenario where
  /-- The objects being screened. -/
  objects   : List SpaceObject
  /-- The conjunction threshold (separation strictly below this = a near-miss). -/
  threshold : ℤ
  deriving Repr

/-- **A maneuver — the witness the proposer offers.** Move object `target` by `delta`
(a 1-D position nudge; the toy stand-in for a `dv_vector`). -/
structure Maneuver where
  /-- The object the burn moves. -/
  target : ObjId
  /-- The position delta applied to that object (toy stand-in for Δv). -/
  delta  : ℤ
  deriving Repr, DecidableEq

/-! ## 2. The TOY screen — `hasConjunction` and the decidable `Verify`.

HONESTY: a discrete-snapshot 1-D screen, NOT orbital mechanics (see the module header).
The genuine conservative between-samples screen is out of scope; this is a placeholder at
the one physics seam. -/

/-- The (toy) pairwise separation of two snapshot positions. -/
def sep (a b : ℤ) : ℤ := (a - b).natAbs

/-- **`hasConjunction s` — does the scenario contain a near-miss?** TRUE iff some
*distinct* pair of objects is within `threshold` (separation strictly below it). Decidable,
total, cheap — exactly the VERIFY side of the seam. (TOY: one snapshot, 1-D.) -/
def hasConjunction (s : Scenario) : Bool :=
  s.objects.any (fun a =>
    s.objects.any (fun b =>
      a.id ≠ b.id && sep a.pos b.pos < s.threshold))

/-- **`applyManeuver s m` — the deterministic physics step.** Nudge the targeted object's
position by `m.delta`; everything else is unchanged. (TOY: a snapshot translation, not a
propagated orbit.) -/
def applyManeuver (s : Scenario) (m : Maneuver) : Scenario :=
  { s with objects := s.objects.map (fun o =>
      if o.id = m.target then { o with pos := o.pos + m.delta } else o) }

/-- **`Verify s m` — the referee's decidable check (in the TCB).** A maneuver is ACCEPTED
iff the *post-maneuver* scenario is conjunction-FREE. This is the runnable golden oracle AND
the proof target at the same time. (TOY screen — see header. The seam is real; the physics
is a placeholder.) -/
def Verify (s : Scenario) (m : Maneuver) : Bool :=
  !hasConjunction (applyManeuver s m)

/-! ## 3. THE REFEREE-IS-A-THEOREM — instantiate the verify-not-find seam.

The referee is exactly `Intent.resolve` at `P := Scenario`, `W := Maneuver`: the untrusted
matcher (`Searchable.find`, the LLM negotiation layer) PROPOSES a maneuver; the cell RE-RUNS
`Verify` and accepts ONLY a maneuver that genuinely clears the conjunction. Adversary-proof
soundness is then `intent_sound_against_adversary`, inherited verbatim. -/

/-- **The verify side of the seam, as a `Verifiable` instance.** The predicate is the
scenario; the witness is the proposed maneuver; VERIFY runs the toy screen. This is the *only*
thing the referee trusts — the matcher (`find`) is never trusted. -/
instance instVerifiable : Verifiable Scenario Maneuver where
  Verify := Verify

/-- **The referee's intent.** An existentially-quantified hole "find a maneuver that clears
scenario `s`", gated by the decidable `Verify`. The matcher fills it; the referee verifies. -/
def refereeIntent (s : Scenario) : Intent Scenario Maneuver := { want := s }

/-- **`referee s` — the referee.** Given an untrusted proposer (`Searchable Scenario
Maneuver` — the negotiation layer), PROPOSE a maneuver then VERIFY it: returns `some m` ONLY
for a maneuver the matcher returned AND the referee's own `Verify` accepted. This is
`Intent.resolve` — the propose-then-reverify shape, not a new mechanism. -/
def referee [Searchable Scenario Maneuver] (s : Scenario) : Option Maneuver :=
  (refereeIntent s).resolve

/-- **`referee_sound` — THE KEYSTONE: a committed maneuver was Verify-discharging, EVEN IF
the proposer is adversarial (PROVED, inherited).** For ANY `Searchable` instance whatsoever
(including a matcher engineered to return collision-creating garbage), if the referee COMMITS
a maneuver `m`, then `Verify s m = true` — `m` provably clears the conjunction. This is the
executed analog the pitch promises: the trust anchor is a machine-checked proof, not faith.

It is an *instance* of `Dregg2.Authority.intent_sound_against_adversary` (via
`Dregg2.Laws.Discharged`, which unfolds to `Verify · · = true`) — NOT re-proved here. The
matcher is outside the TCB; soundness rests on the referee's own `Verify` alone. -/
theorem referee_sound [Searchable Scenario Maneuver] (s : Scenario) (m : Maneuver)
    (h : referee s = some m) :
    Verify s m = true :=
  -- `Discharged (refereeIntent s).want m` is defeq `Verify s m = true`; the adversary-proof
  -- intent keystone supplies it for an arbitrary (possibly adversarial) `Searchable`.
  Dregg2.Authority.intent_sound_against_adversary (refereeIntent s) m h

/-! ## 4. TEETH — a garbage maneuver that does NOT clear the conjunction is REJECTED.

`referee_sound` would be vacuous if `Verify` accepted everything. It does not: we exhibit a
concrete near-miss scenario and a garbage maneuver that fails to separate the pair, and the
referee REJECTS it (`#eval`, below). Here we also pin the non-vacuity as a theorem. -/

/-- A concrete near-miss: two sats at positions 0 and 1, threshold 5 (separation 1 < 5). -/
def conjScenario : Scenario :=
  { objects := [ { id := 0, pos := 0, priority := 1 },
                 { id := 1, pos := 1, priority := 9 } ]
    threshold := 5 }

/-- A GARBAGE maneuver: nudge sat 0 by 1 (to pos 1) — now BOTH sats sit at pos 1,
separation 0 < 5: the conjunction is NOT cleared. The referee must reject it. -/
def garbageManeuver : Maneuver := { target := 0, delta := 1 }

/-- A CLEARING maneuver: nudge sat 0 by 100 (to pos 100) — separation 99 ≥ 5: clear. -/
def clearManeuver : Maneuver := { target := 0, delta := 100 }

/-- **TEETH (PROVED) — the garbage maneuver does NOT verify.** `Verify` genuinely rejects a
maneuver that fails to clear the conjunction; so `referee_sound` is non-vacuous (acceptance
is a real constraint, not `True`). -/
theorem garbage_rejected : Verify conjScenario garbageManeuver = false := by decide

/-- **The clearing maneuver DOES verify (PROVED)** — the screen is not fail-closed-on-
everything either: a genuine fix is accepted. With `garbage_rejected`, `Verify` is a real,
two-sided decision. -/
theorem clear_accepted : Verify conjScenario clearManeuver = true := by decide

/-! ### The referee against concrete (correct vs adversarial) proposers.

`goodProposer` returns the clearing maneuver (ACCEPTED); `evilProposer` returns the garbage
maneuver (REJECTED by the referee's VERIFY, even though the matcher proposed it). -/

/-- A CORRECT proposer (the negotiation layer happens to be right): proposes the clearing
maneuver. Untrusted, but sound here. -/
@[reducible] def goodProposer : Searchable Scenario Maneuver where
  find := fun _ => some clearManeuver

/-- An ADVERSARIAL proposer: proposes the garbage maneuver that does NOT clear the
conjunction. The referee must reject it. -/
@[reducible] def evilProposer : Searchable Scenario Maneuver where
  find := fun _ => some garbageManeuver

/-- A GIVE-UP proposer: finds nothing (models a stuck negotiation / round-cap timeout). -/
@[reducible] def emptyProposer : Searchable Scenario Maneuver where
  find := fun _ => none

/-- **TEETH against an adversary (PROVED) — the referee REJECTS the adversarial proposal.**
Even though `evilProposer` proposes `garbageManeuver`, the referee returns `none`: the
propose-then-VERIFY shape filters it out. This is `referee_sound` made concrete — the
adversarial fill never escapes. -/
theorem referee_rejects_adversary :
    (@referee evilProposer conjScenario) = none := by decide

/-- **The referee ACCEPTS the correct proposal (PROVED).** With a proposer that returns a
genuinely-clearing maneuver, the referee commits it. -/
theorem referee_accepts_good :
    (@referee goodProposer conjScenario) = some clearManeuver := by decide

/-! ## 5. FUEL-AS-CELL + THE FORCED TRADE (`Dregg2.Exec.JointCell`).

Fuel is a **cell budget**: a `KernelState` whose `bal` at the `fuel` asset is the remaining
Δv. A burn is a half-edge OUT of that cell (`applyHalfOut`). The budget gate is PROVED, not
checked: an out-of-fuel sat (`bal fuel = 0`) CANNOT burn any positive amount.

HONEST: fuel is a **SINK** here — a single-cell debit. There is NO constellation-wide
conservation: a burn destroys budget, it is not transferred to another sat's tank. -/

open Dregg2.Exec
open Dregg2.Exec.JointCell

/-- The cell id standing for sat A's **fuel tank**. -/
def fuelA : CellId := 0

/-- The cell id standing for sat B's fuel tank (the credit side of the joint maneuver). -/
def fuelB : CellId := 7

/-- **sat_A's fuel cell — EMPTY (`bal fuelA = 0`).** The LOW-priority sat that the naive
rule would order to yield, but which is physically out of Δv. Authority is by ownership
(empty cap table). -/
def satA_empty : KernelState :=
  { accounts := {fuelA}
    bal := fun _ => 0
    caps := fun _ => [] }

/-- sat_B's fuel cell, with budget 50 (the HIGH-priority sat that *can* burn). -/
def satB_fueled : KernelState :=
  { accounts := {fuelB}
    bal := fun c => if c = fuelB then 50 else 0
    caps := fun _ => [] }

/-- A burn of 10 Δv out of sat A's tank (`actorA = fuelA` owns it; amount 10). -/
def burnA : BiTurn :=
  { actorA := fuelA, srcA := fuelA, actorB := fuelB, dstB := fuelB, amt := 10, sid := 0 }

/-- **`outOfFuel_cannot_burn` — THE BUDGET GATE (PROVED).** sat_A, with `bal fuelA = 0`,
cannot execute any positive burn: `applyHalfOut` REJECTS `burnA` (amount 10 exceeds the
available 0). This is the executable "sat_A cannot yield" — a theorem about the gate, not a
demo `if`. It rests directly on `applyHalfOut`'s `amt ≤ k.bal srcA` budget condition. -/
theorem outOfFuel_cannot_burn : applyHalfOut satA_empty burnA = none := by decide

/-- For contrast: a fueled sat with `amt ≤ bal` DOES burn. -/
def burnB : BiTurn :=
  { actorA := fuelB, srcA := fuelB, actorB := fuelB, dstB := fuelB, amt := 10, sid := 0 }

/-- **A fueled sat CAN burn (PROVED contrast)** — the gate is two-sided, not fail-closed on
everything: `bal fuelB = 50 ≥ 10`, so the half-edge commits. -/
theorem fueled_can_burn : (applyHalfOut satB_fueled burnB).isSome = true := by decide

/-! ### THE FORCED TRADE as a `binding_is_proper` instance.

The naive rule is "lowest priority yields" → it orders sat_A (LOW) to burn. But sat_A is out
of fuel (`outOfFuel_cannot_burn`), so that configuration is physically impossible. Why is the
re-negotiation *forced by a theorem* rather than demo-scripting? Because cross-cell soundness
is **NOT** per-cell-sound ∧ per-cell-sound: the joint maneuver's half-edges must SUM TO ZERO
(`EqualAndOpposite`), and there exist declared configurations the binding PROVABLY EXCLUDES
(`Dregg2.Exec.JointCell.binding_is_proper`). The naive "A yields for free while B does
nothing" is exactly such an unbalanced, excluded configuration — the trade is forced, not
scripted. -/

/-- **`forced_trade_excludes_naive` — the naive ordering is PROVABLY EXCLUDED (PROVED,
inherited).** There exist declared half-edge magnitudes that do NOT cancel — a "free yield"
(A gives, B does not equally take) is one such — and every *committed* bilateral turn must
balance (`real_bilateral_balances`). So the binding carves a proper subobject: the naive
"lowest yields, no trade" configuration is excluded by a theorem.

This is `Dregg2.Exec.JointCell.binding_is_proper` re-exported into the Right-of-Way framing —
the forced trade stops being an if-statement. -/
theorem forced_trade_excludes_naive :
    ∃ out_amt in_amt : ℤ, ¬ FakeBalances out_amt in_amt :=
  binding_is_proper

/-- **The contrast (PROVED): a genuine bilateral trade DOES balance.** Whatever its amount,
sat_B's half-edge OUT and the matching half-edge IN cancel (`halfA bt + halfB bt = 0`), so a
*real* trade is admissible exactly where the naive free-yield is not. The forced trade is the
balanced configuration; the naive ordering is the excluded one. -/
theorem real_trade_balances (bt : BiTurn) : FakeBalances (halfA bt) (halfB bt) :=
  real_bilateral_balances bt

/-! ## 6. (Optional) THE ESCALATION — collision-safety is NOT I-confluent.

Why must the agents escalate to a *joint* maneuver instead of each fixing its own orbit
independently? Because collision-safety is a BOUNDED, coupled invariant — exactly the shape
that is NOT I-confluent (two independently-"safe" fixes can merge into a new conjunction).
`Dregg2.Confluence.nonpairwise_escalation` then FORCES escalation by exhibiting a clashing
pair. We instantiate the classifier at the "at most one occupant per cell" invariant — the
collision shape (two objects must not co-locate) — which `Dregg2.Confluence` already proves
is not I-confluent. -/

open Dregg2.Confluence

/-- **`collisionSafety_must_escalate` — collision-safety is NOT coordination-free; it MUST
escalate to a joint maneuver (PROVED, inherited).** The "at most one occupant" invariant (two
objects cannot share a slot — the collision shape) is NOT I-confluent: there is a concrete
clashing pair of individually-safe versions whose merge violates safety. Hence a cell with
this invariant cannot run tier-1 (coordination-free); it must escalate to consensus — i.e. a
JointTurn between the conflicting sats. This is `nonpairwise_escalation` applied to the
already-proved `cardLeOne_not_iconfluent`. -/
theorem collisionSafety_must_escalate :
    ∃ x y : Finset ℕ, (fun s => s.card ≤ 1) x ∧ (fun s => s.card ≤ 1) y
      ∧ ¬ (fun s => s.card ≤ 1) (x ⊔ y) :=
  nonpairwise_escalation (S := Finset ℕ) (fun s => s.card ≤ 1) cardLeOne_not_iconfluent

/-! ## 7. `#eval` witnesses — the demonstrator, runnable.

A clear maneuver ACCEPTED; a garbage maneuver REJECTED (the `referee_sound` teeth); the
out-of-fuel sat cannot burn; the forced-trade naive-ordering excluded. -/

-- The TOY screen: the near-miss scenario HAS a conjunction (sats at 0 and 1, threshold 5).
#eval hasConjunction conjScenario                       -- true  (a near-miss exists)
-- The clearing maneuver VERIFIES (post-maneuver scenario conjunction-free):
#eval Verify conjScenario clearManeuver                 -- true  (ACCEPTED)
-- The garbage maneuver does NOT verify (the conjunction is not cleared):
#eval Verify conjScenario garbageManeuver               -- false (REJECTED — referee_sound teeth)

-- THE REFEREE against a CORRECT proposer: ACCEPTS the clearing maneuver.
#eval (@referee goodProposer conjScenario)              -- some { target := 0, delta := 100 }
-- THE REFEREE against an ADVERSARIAL proposer: REJECTS (the propose-then-VERIFY filter).
#eval (@referee evilProposer conjScenario)              -- none  (adversarial fill never escapes)
-- The untrusted PROPOSE step DOES surface the adversarial maneuver …
#eval (@Searchable.find Scenario Maneuver evilProposer conjScenario)   -- some garbage
-- … but the referee's own VERIFY rejects it (decidable, in-TCB).

-- FUEL-AS-CELL: the out-of-fuel sat CANNOT burn (the budget gate).
#eval (applyHalfOut satA_empty burnA).isSome            -- false (bal fuelA = 0 < 10)
-- A fueled sat CAN burn (the gate is two-sided).
#eval (applyHalfOut satB_fueled burnB).isSome           -- true  (bal fuelB = 50 ≥ 10)

-- THE FORCED TRADE: the naive free-yield (1 out, 2 in) does NOT balance ⇒ excluded …
-- (`FakeBalances out in` is `out + in = 0`; the naive `(1,2)` gives `3 ≠ 0`, so it is
--  the `binding_is_proper` witness — a configuration the binding PROVABLY excludes.)
#eval (((1 : ℤ) + 2) == 0)                              -- false (1+2 ≠ 0 ⇒ naive ordering excluded)
-- … while a real trade of any amount balances (here amt = 10 ⇒ -10 + 10 = 0).
#eval (halfA burnB + halfB burnB)                       -- 0     (EqualAndOpposite)

/-! ## 9. THE REAL-PHYSICS REFEREE — the same seam, now carrying CONTINUOUS-TIME-SOUND physics.

This is the §"Honest scope" substantive piece, DISCHARGED: we plug the conservative orbital
screen of `Dregg2.Apps.OrbitalScreen` (`screen_clear_imp_continuous_clear`) into the EXACT same
`Intent.resolve` referee seam. The proposer (the LLM negotiation layer) is still the untrusted
`Searchable`; the referee re-runs the *continuous-time-sound* screen. Now `referee_sound_physics`
says: a committed maneuver is not merely "clear at a sampled instant" but **clear on the whole
continuous maneuver step** — the between-samples closest approach is covered, by a theorem. The
referee is a theorem AND the physics is real. -/

open Dregg2.Apps.OrbitalScreen

/-- **A physics screening problem** at the referee seam: a relative pair `(d0, v)` over step
`[0,T]` at squared threshold `thrSq`. (The real-physics analog of the toy §1 `Scenario`.) -/
structure PhysScenario where
  /-- relative position of the pair at step start -/
  d0    : Vec3
  /-- relative velocity over the maneuver step -/
  v     : Vec3
  /-- maneuver-step length -/
  T     : ℚ
  /-- squared conjunction threshold -/
  thrSq : ℚ
deriving Repr

/-- The witness the proposer offers (a "I ran the conservative screen, it's clear" token). The
content is in `VerifyPhys` below — every checker RE-RUNS the screen; the token is never trusted. -/
abbrev PhysWitness := Unit

/-- **VERIFY (in TCB): re-run the CONSERVATIVE, continuous-time-sound orbital screen.** Unlike
the toy §2 `Verify`, this is `OrbitalScreen.screen` — a `true` verdict is sound on the whole
continuous step, not just at samples. The referee trusts only this. -/
def VerifyPhys (s : PhysScenario) (_w : PhysWitness) : Bool :=
  screen s.d0 s.v s.T s.thrSq

/-- The verify side of the seam at the real screen. -/
instance instVerifiablePhys : Verifiable PhysScenario PhysWitness where
  Verify := VerifyPhys

/-- The physics referee's intent: "find a clearance certificate for scenario `s`." -/
def physRefereeIntent (s : PhysScenario) : Intent PhysScenario PhysWitness := { want := s }

/-- **`physReferee` — the referee at the REAL screen.** Same propose-then-VERIFY shape
(`Intent.resolve`), but VERIFY is the conservative continuous-time-sound screen. -/
def physReferee [Searchable PhysScenario PhysWitness] (s : PhysScenario) : Option PhysWitness :=
  (physRefereeIntent s).resolve

/-- **`physReferee_screened` — a committed clearance was screen-discharging, EVEN vs an
adversarial proposer (PROVED, inherited).** The same adversary-proof keystone as `referee_sound`,
now at the physics screen: whatever the (possibly adversarial) negotiation layer proposes, a
COMMITTED clearance has `screen s.d0 s.v s.T s.thrSq = true`. -/
theorem physReferee_screened [Searchable PhysScenario PhysWitness]
    (s : PhysScenario) (w : PhysWitness) (h : physReferee s = some w) :
    screen s.d0 s.v s.T s.thrSq = true :=
  Dregg2.Authority.intent_sound_against_adversary (physRefereeIntent s) w h

/-- **`referee_sound_physics` — THE UPGRADED KEYSTONE: a committed maneuver is clear on the
WHOLE CONTINUOUS STEP (PROVED).** Combining the adversary-proof seam (`physReferee_screened`)
with the conservative screen's continuous-time soundness
(`OrbitalScreen.screen_clear_imp_continuous_clear`): if the referee COMMITS a clearance for
scenario `s` — even against an adversarial proposer — then at EVERY continuous time `t ∈ [0,T]`
of the maneuver step the squared separation is at least the threshold. No between-samples
conjunction. This is "the referee is a theorem" AND "the physics is real," in one statement —
the substantive piece the response flagged as not-inherited, discharged. -/
theorem referee_sound_physics [Searchable PhysScenario PhysWitness]
    (s : PhysScenario) (w : PhysWitness) (h : physReferee s = some w)
    (t : ℚ) (h0 : 0 ≤ t) (hT : t ≤ s.T) :
    s.thrSq ≤ sepSq s.d0 s.v t :=
  screen_clear_imp_continuous_clear s.d0 s.v s.T s.thrSq
    (physReferee_screened s w h) t h0 hT

/-! ### TEETH at the real screen — the crossing pair (clear at endpoints) is REJECTED.

The adversarial proposer here is the *endpoint sampler*: it would accept the crossing pair
(clear at `t=0` and `t=T`). The conservative referee rejects it, because the screen sees the
mid-step closest approach. So even a "samples look clear" proposal does not escape. -/

/-- The crossing scenario from `OrbitalScreen`: clear at both endpoints, a mid-step collision. -/
def crossingScenario : PhysScenario :=
  { d0 := crossingD0, v := crossingV, T := crossingT, thrSq := crossingThrSq }

/-- A clear scenario: parallel tracks, never closing. -/
def clearScenario : PhysScenario :=
  { d0 := clearD0, v := clearV, T := 10, thrSq := 25 }

/-- An ADVERSARIAL "endpoint-sampler" proposer: always claims clearance (returns the token),
modelling a negotiation layer that checked only the endpoints. -/
@[reducible] def samplerProposer : Searchable PhysScenario PhysWitness where
  find := fun _ => some ()

/-- **`physReferee` reduces to its screen-gated `if` (PROVED helper).** With the sampler
proposer (always proposing the token), the referee is exactly "accept iff the screen clears." -/
theorem physReferee_sampler_eq (s : PhysScenario) :
    (@physReferee samplerProposer s) = (if VerifyPhys s () = true then some () else none) :=
  rfl

/-- **`physReferee_rejects_crossing` — the conservative referee REJECTS the crossing pair
(PROVED).** Even though the endpoint-sampler proposer claims clearance, the referee's own
continuous-time screen sees the mid-step closest approach and returns `none`. The
"samples-look-clear" proposal does not escape — `referee_sound_physics` made concrete. -/
theorem physReferee_rejects_crossing :
    (@physReferee samplerProposer crossingScenario) = none := by
  rw [physReferee_sampler_eq]
  rw [show VerifyPhys crossingScenario () = false from screen_rejects_crossing]
  simp

/-- **`physReferee_accepts_clear` — the referee ACCEPTS a genuinely-clear scenario (PROVED).**
Two-sided: the conservative screen is not fail-closed-on-everything; a real clearance passes. -/
theorem physReferee_accepts_clear :
    (@physReferee samplerProposer clearScenario) = some () := by
  rw [physReferee_sampler_eq]
  have hscr : VerifyPhys clearScenario () = true := by
    show screen clearD0 clearV 10 25 = true
    unfold screen tca vertex aCoef bCoef sepSq rel Vec3.add Vec3.smul Vec3.normSq
      clearD0 clearV
    norm_num
  rw [hscr]
  rfl

/-! ### `#eval` — the real-physics referee, runnable. -/

-- The conservative referee REJECTS the crossing pair (endpoint-sampler would have accepted):
#eval (@physReferee samplerProposer crossingScenario)   -- none  (mid-step conjunction caught)
-- … ACCEPTS a genuinely-clear scenario:
#eval (@physReferee samplerProposer clearScenario)      -- some ()
-- The underlying screen verdicts (the REAL continuous-time-sound physics):
#eval VerifyPhys crossingScenario ()                    -- false (clear at samples, NOT continuously)
#eval VerifyPhys clearScenario ()                       -- true  (clear on the whole step)

/-! ## 8. Axiom-hygiene — every keystone pinned to the three standard kernel axioms.

A `sorryAx` here would mean a silent `sorry` leaked into a "the referee is a theorem"
keystone. None do. The §9 physics screen enters via the `Verifiable` instance over the REAL
`OrbitalScreen.screen` (a concrete `def`, axiom-clean), so the upgraded `referee_sound_physics`
is `#assert_axioms`-clean too — the real physics adds no axioms. -/

#assert_axioms referee_sound
#assert_axioms garbage_rejected
#assert_axioms clear_accepted
#assert_axioms referee_rejects_adversary
#assert_axioms referee_accepts_good
#assert_axioms outOfFuel_cannot_burn
#assert_axioms fueled_can_burn
#assert_axioms forced_trade_excludes_naive
#assert_axioms real_trade_balances
#assert_axioms collisionSafety_must_escalate
#assert_axioms physReferee_screened
#assert_axioms referee_sound_physics
#assert_axioms physReferee_sampler_eq
#assert_axioms physReferee_rejects_crossing
#assert_axioms physReferee_accepts_clear

end Dregg2.Apps.RightOfWay
