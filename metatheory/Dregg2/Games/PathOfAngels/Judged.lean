/-
# Dregg2.Games.PathOfAngels.Judged — executable runtime admission

`JudgedRun` is abstract outside this module.  It is produced only by
`judgeActive`, which checks an exact active game/config projection, all content
and activation domains, the authenticated carrying-turn context, and the current
canonical player counter before invoking one concrete game judge.

The semantic judge remains publicly replayable.  Network authority is not source
secrecy and is not an unconstructible token: the adapter must derive
`FinalizedCarrier` from the already-finalized Dregg turn/receipt, then this module
checks every value it consumes.  A caller can model those inputs, but cannot forge
a `JudgedRun` constructor or bypass the executable equality retained below.
-/
import Dregg2.Games.PathOfAngels.SignalTriangulation
import Dregg2.Games.PathOfAngels.RelayRepair
import Dregg2.Games.PathOfAngels.SalvageLock
import Dregg2.Games.PathOfAngels.DeckDescent
import Dregg2.Games.PathOfAngels.VentCrawl
import Dregg2.Games.PathOfAngels.BlackBoxReconstruction
import Dregg2.Games.PathOfAngels.PlayerCounters
import Dregg2.Games.PathOfAngels.HiddenInstance

namespace Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-! ## Active configuration and authenticated carrying context -/

inductive ActiveGame where
  | signal (config : SignalTriangulation.Config)
  | relay (config : RelayRepair.Config)
  | salvage (config : SalvageLock.Config)
  | blackBox (config : BlackBoxReconstruction.Config)
  | deckDescent (config : DeckDescent.Config)
  | ventCrawl (config : VentCrawl.Config)

def ActiveGame.mission : ActiveGame → MissionSpec
  | .signal config => config.mission
  | .relay config => config.mission
  | .salvage config => config.mission
  | .blackBox config => config.mission
  | .deckDescent config => config.mission
  | .ventCrawl config => config.mission

/-- Proof fields are omitted, and — ⚠ CHANGED — so are the INSTANCE fields.

`signal` used to carry `target : Code` and `salvage` a `seed : Fin SEED_SPACE`.
A `RunClaim` is supplied by the game request, so requiring the client to state the
instance required the client to KNOW the instance, which is the hole this split
closes.  The instance is derived inside admission from the slot secret; the claim
states only what a player legitimately has.

`mission` is retained and it still carries `runSeed`, but a claim never supplies a
mission: `admissionChecks` compares the claim against `active.game.configClaim`,
and `active` is assembled by the node from authenticated state. -/
inductive GameConfigClaim where
  | signal (mission : MissionSpec) (reward : Contribution)
  | relay (mission : MissionSpec) (reward : Contribution)
  | salvage (mission : MissionSpec) (reward : Contribution)
  | blackBox (mission : MissionSpec) (reward : Contribution)
  | deckDescent (mission : MissionSpec) (reward : Contribution)
  /-- ⚠ No `reward`.  Vent Crawl has no fixed payout to claim: what a run pays is
  a function of the rung it banked from, computed by `VentCrawl.terminalOutput`
  and validated against the mission's own ceiling.  What IS claimable is the
  relic the bottom rung awards, which the mission must have allowlisted. -/
  | ventCrawl (mission : MissionSpec) (deepRelic : RelicId)
deriving DecidableEq

def ActiveGame.configClaim : ActiveGame → GameConfigClaim
  | .signal config => .signal config.mission config.reward
  | .relay config => .relay config.mission config.reward
  | .salvage config => .salvage config.mission config.reward
  | .blackBox config => .blackBox config.mission config.reward
  | .deckDescent config => .deckDescent config.mission config.reward
  | .ventCrawl config => .ventCrawl config.mission config.deepRelic

/-- Runtime state selected from the authenticated active catalog.  Domain fields
are repeated intentionally and checked against the mission: malformed decoded
state refuses rather than being silently repaired from `game`. -/
structure ActiveRunState where
  game : ActiveGame
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  /-- The beacon slot this run belongs to. -/
  slot : EpochId
  /-- The curator's secret for `slot`.  It reaches this structure from node state,
  never from a request, and no emitter renders it. -/
  slotSecret : HiddenInstance.SlotSecret
  /-- The commitment published in the slot opening.  Admission requires it to be
  the commitment OF `slotSecret`, so a node that swapped the secret after
  publishing cannot judge against the swapped one. -/
  slotCommitment : Digest32
  runSeed : Digest32
  world : WorldState
  playerCounters : PlayerCounterTable

/-- Values derived from the finalized carrying Dregg turn.  `playerKey` is its
signer and `actorRoot` is its AIR-bound pre-state commitment. -/
structure FinalizedCarrier where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  actorRoot : Digest32
  playerKey : Digest32
  currentPlayerCounter : PlayerCounter

/-- Untrusted receipt-shaped claims supplied by the game request.  They are all
compared with active state or the finalized carrier before replay. -/
structure RunClaim where
  config : GameConfigClaim
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  /-- ⚠ `runSeed` is GONE from the claim.  A client that could state the live run
  seed could compute its own instance, which is exactly what it must not be able
  to do.  What it states instead is the slot it played in and the commitment it
  was shown when its run opened. -/
  slot : EpochId
  slotCommitment : Digest32
  actorRoot : Digest32
  playerKey : Digest32
  claimedPreviousPlayerCounter : Nat

inductive SubmittedRun where
  | signal (actions : List SignalTriangulation.Action)
  | relay (actions : List RelayRepair.Action)
  | salvage (actions : List SalvageLock.Action)
  | blackBox (actions : List BlackBoxReconstruction.Action)
  | deckDescent (actions : List DeckDescent.Action)
  | ventCrawl (actions : List VentCrawl.Action)

def FinalizedCarrier.counterKey (carrier : FinalizedCarrier) : PlayerCounterKey where
  federationId := carrier.federationId
  contentSession := carrier.contentSession
  contentEpoch := carrier.contentEpoch
  playerKey := carrier.playerKey

/-- Every authority/configuration equality checked before the game judge runs. -/
def admissionChecks (active : ActiveRunState) (carrier : FinalizedCarrier)
    (claim : RunClaim) : Bool :=
  decide (
    claim.config = active.game.configClaim ∧
    active.federationId = active.game.mission.federationId ∧
    active.contentRoot = active.game.mission.contentRoot ∧
    active.activationDigest = active.game.mission.activationDigest ∧
    active.contentSession = active.game.mission.contentSession ∧
    active.contentEpoch = active.game.mission.epoch ∧
    active.runSeed = active.game.mission.runSeed ∧
    carrier.federationId = active.federationId ∧
    carrier.contentRoot = active.contentRoot ∧
    carrier.activationDigest = active.activationDigest ∧
    carrier.contentSession = active.contentSession ∧
    carrier.contentEpoch = active.contentEpoch ∧
    claim.federationId = carrier.federationId ∧
    claim.contentRoot = carrier.contentRoot ∧
    claim.activationDigest = carrier.activationDigest ∧
    claim.contentSession = carrier.contentSession ∧
    claim.contentEpoch = carrier.contentEpoch ∧
    claim.slot = active.slot ∧
    claim.slotCommitment = active.slotCommitment ∧
    active.slotCommitment = HiddenInstance.commit active.slotSecret active.slot ∧
    active.runSeed =
      HiddenInstance.runSeedFor
        { secret := active.slotSecret, slot := active.slot, playerKey := carrier.playerKey }
        (HiddenInstance.MissionContext.ofMission active.game.mission) ∧
    claim.actorRoot = carrier.actorRoot ∧
    claim.playerKey = carrier.playerKey ∧
    claim.claimedPreviousPlayerCounter = carrier.currentPlayerCounter.val ∧
    active.playerCounters.lookup carrier.counterKey = carrier.currentPlayerCounter ∧
    carrier.currentPlayerCounter.val + 1 < PLAYER_COUNTER_MODULUS)


/-- `admissionChecks` as a function equation, for `rw`. The pointwise equation lemma that
`simp only [admissionChecks]` generates is checked by the kernel against `decide (…)`; since
v4.35 `Decidable.decide` is a structure projection, the kernel unfolds it first and whnfs the
whole conjunction's instance, Poseidon2 commitments included. This form is closed by unfolding
`admissionChecks` once. -/
theorem admissionChecks_def :
    admissionChecks = fun (active : ActiveRunState) (carrier : FinalizedCarrier)
        (claim : RunClaim) =>
      decide (
        claim.config = active.game.configClaim ∧
        active.federationId = active.game.mission.federationId ∧
        active.contentRoot = active.game.mission.contentRoot ∧
        active.activationDigest = active.game.mission.activationDigest ∧
        active.contentSession = active.game.mission.contentSession ∧
        active.contentEpoch = active.game.mission.epoch ∧
        active.runSeed = active.game.mission.runSeed ∧
        carrier.federationId = active.federationId ∧
        carrier.contentRoot = active.contentRoot ∧
        carrier.activationDigest = active.activationDigest ∧
        carrier.contentSession = active.contentSession ∧
        carrier.contentEpoch = active.contentEpoch ∧
        claim.federationId = carrier.federationId ∧
        claim.contentRoot = carrier.contentRoot ∧
        claim.activationDigest = carrier.activationDigest ∧
        claim.contentSession = carrier.contentSession ∧
        claim.contentEpoch = carrier.contentEpoch ∧
        claim.slot = active.slot ∧
        claim.slotCommitment = active.slotCommitment ∧
        active.slotCommitment = HiddenInstance.commit active.slotSecret active.slot ∧
        active.runSeed =
          HiddenInstance.runSeedFor
            { secret := active.slotSecret, slot := active.slot, playerKey := carrier.playerKey }
            (HiddenInstance.MissionContext.ofMission active.game.mission) ∧
        claim.actorRoot = carrier.actorRoot ∧
        claim.playerKey = carrier.playerKey ∧
        claim.claimedPreviousPlayerCounter = carrier.currentPlayerCounter.val ∧
        active.playerCounters.lookup carrier.counterKey = carrier.currentPlayerCounter ∧
        carrier.currentPlayerCounter.val + 1 < PLAYER_COUNTER_MODULUS) := rfl

theorem admissionChecks_eq_true_iff (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) :
    admissionChecks active carrier claim = true ↔
      claim.config = active.game.configClaim ∧
      active.federationId = active.game.mission.federationId ∧
      active.contentRoot = active.game.mission.contentRoot ∧
      active.activationDigest = active.game.mission.activationDigest ∧
      active.contentSession = active.game.mission.contentSession ∧
      active.contentEpoch = active.game.mission.epoch ∧
      active.runSeed = active.game.mission.runSeed ∧
      carrier.federationId = active.federationId ∧
      carrier.contentRoot = active.contentRoot ∧
      carrier.activationDigest = active.activationDigest ∧
      carrier.contentSession = active.contentSession ∧
      carrier.contentEpoch = active.contentEpoch ∧
      claim.federationId = carrier.federationId ∧
      claim.contentRoot = carrier.contentRoot ∧
      claim.activationDigest = carrier.activationDigest ∧
      claim.contentSession = carrier.contentSession ∧
      claim.contentEpoch = carrier.contentEpoch ∧
      claim.slot = active.slot ∧
      claim.slotCommitment = active.slotCommitment ∧
      active.slotCommitment = HiddenInstance.commit active.slotSecret active.slot ∧
      active.runSeed =
        HiddenInstance.runSeedFor
          { secret := active.slotSecret, slot := active.slot, playerKey := carrier.playerKey }
          (HiddenInstance.MissionContext.ofMission active.game.mission) ∧
      claim.actorRoot = carrier.actorRoot ∧
      claim.playerKey = carrier.playerKey ∧
      claim.claimedPreviousPlayerCounter = carrier.currentPlayerCounter.val ∧
      active.playerCounters.lookup carrier.counterKey = carrier.currentPlayerCounter ∧
      carrier.currentPlayerCounter.val + 1 < PLAYER_COUNTER_MODULUS := by
  rw [admissionChecks_def]
  exact decide_eq_true_iff

private def signalContext (carrier : FinalizedCarrier) : SignalTriangulation.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val

private def relayContext (carrier : FinalizedCarrier) : RelayRepair.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val

private def salvageContext (carrier : FinalizedCarrier) : SalvageLock.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val

private def blackBoxContext (carrier : FinalizedCarrier) : BlackBoxReconstruction.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val

/-- ⚑ Deck Descent joined Vent Crawl in needing `active` as well as `carrier` on
2026-08-09: its MOUTH is a three-in-four reading of the ship's bilge, which is a
per-SLOT draw under `DayWater.SHIP_DOMAIN` — no mission, no player.  The bit is
derived here from the very `slotSecret` `admissionChecks` has already pinned to
the published commitment, so nothing new is trusted, and
`DeckDescent.judge_binds_the_day` refuses any config that names a different
night. -/
private def deckDescentContext (active : ActiveRunState) (carrier : FinalizedCarrier) :
    DeckDescent.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val
  bilge := (DayWater.shipDayFor active.slotSecret active.slot
    active.game.mission.federationId active.game.mission.contentSession).bilge

/-- ⚠ The only judge context built from `active` as well as `carrier`, and the
reason is the whole point of Vent Crawl: its hidden table is drawn once per SLOT
and is the same for every player, while `active.runSeed` is drawn per player.
There is no way to reach a shared draw through the per-player seed, so the day's
seed is derived here, from the very `slotSecret` that `admissionChecks` has
already pinned to the published `slotCommitment`.

Nothing new is trusted: a node that swapped the secret after publishing is
refused by `judgeActive_uncommitted_secret_refused`, and the same secret that
fixes the player's tape fixes the day's vein.

⚑ **ONE call, and it is the same call Deck Descent makes.**  Both games' contexts
are now built from `DayWater.shipDayFor` on the same four arguments, so "the two
games see one night" is a fact about these two definitions rather than about two
derivations that happen to agree.  `shipSeedFor` is `@[irreducible]` — never
`decide` through this. -/
private def ventCrawlContext (active : ActiveRunState) (carrier : FinalizedCarrier) :
    VentCrawl.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val
  day := DayWater.shipDayFor active.slotSecret active.slot
    active.game.mission.federationId active.game.mission.contentSession

/-! ## Abstract judged value with game-specific executable evidence -/

private inductive JudgedEvidence where
  | signal
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : SignalTriangulation.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List SignalTriangulation.Action)
      (run : SignalTriangulation.JudgedRun)
      (judged : SignalTriangulation.judge config active.world (signalContext carrier) actions = some run)
  | relay
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : RelayRepair.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List RelayRepair.Action)
      (run : RelayRepair.JudgedRun)
      (judged : RelayRepair.judge config active.world (relayContext carrier) actions = some run)
  | salvage
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : SalvageLock.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List SalvageLock.Action)
      (run : SalvageLock.JudgedRun)
      (judged : SalvageLock.judge config active.world (salvageContext carrier) actions = some run)
  | blackBox
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : BlackBoxReconstruction.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List BlackBoxReconstruction.Action)
      (run : BlackBoxReconstruction.JudgedRun)
      (judged : BlackBoxReconstruction.judge config active.world (blackBoxContext carrier) actions = some run)
  | deckDescent
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : DeckDescent.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List DeckDescent.Action)
      (run : DeckDescent.JudgedRun)
      (judged : DeckDescent.judge config active.world (deckDescentContext active carrier) actions = some run)
  | ventCrawl
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : VentCrawl.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List VentCrawl.Action)
      (run : VentCrawl.JudgedRun)
      (judged : VentCrawl.judge config active.world (ventCrawlContext active carrier) actions
        = some run)

/-- Public type, private constructor and payload. -/
structure JudgedRun where
  private mk ::
  private evidence : JudgedEvidence

def JudgedRun.receipt (judgedRun : JudgedRun) : RunReceipt :=
  match judgedRun.evidence with
  | .signal _ _ _ _ _ _ run _ => run.receipt
  | .relay _ _ _ _ _ _ run _ => run.receipt
  | .salvage _ _ _ _ _ _ run _ => run.receipt
  | .blackBox _ _ _ _ _ _ run _ => run.receipt
  | .deckDescent _ _ _ _ _ _ run _ => run.receipt
  | .ventCrawl _ _ _ _ _ _ run _ => run.receipt

/-- The exact game tag and executable judge, run against an admission fact the caller
already holds.  `judgeActive` below is `admissionChecks`-then-this and nothing else, so
this is a factoring and not a second door: `hadmitted` is the very proposition the `dite`
decides, and no inhabitant of `JudgedRun` can be built without one.

⚑ Why it is separate.  `admissionChecks` mentions `HiddenInstance.commit` and
`HiddenInstance.runSeedFor`, so *deciding* it evaluates two Poseidon2 sponges.  The
elaborator refuses that (both are `@[irreducible]`) and the KERNEL, which ignores
irreducibility, does it exponentially — MEASURED 47.6 GB / 68 min on one file; see the
`⚑` note in `HiddenInstance`.  A caller that already proved admission by compiled
evaluation therefore cannot use `judgeActive`, because reducing its `dite` recomputes
exactly that decision.  Through this entry the admission is a *proof argument*, erased
by reduction, and the judged run reduces at the cost of the game judge alone. -/
def judgeAdmitted (active : ActiveRunState) (carrier : FinalizedCarrier)
    (claim : RunClaim) (submitted : SubmittedRun)
    (hadmitted : admissionChecks active carrier claim = true) : Option JudgedRun :=
  match active.game, submitted with
  | .signal config, .signal actions =>
      match hjudged : SignalTriangulation.judge config active.world
          (signalContext carrier) actions with
      | some run => some ⟨.signal active carrier claim config hadmitted actions run hjudged⟩
      | none => none
  | .relay config, .relay actions =>
      match hjudged : RelayRepair.judge config active.world (relayContext carrier) actions with
      | some run => some ⟨.relay active carrier claim config hadmitted actions run hjudged⟩
      | none => none
  | .salvage config, .salvage actions =>
      match hjudged : SalvageLock.judge config active.world (salvageContext carrier) actions with
      | some run => some ⟨.salvage active carrier claim config hadmitted actions run hjudged⟩
      | none => none
  | .blackBox config, .blackBox actions =>
      match hjudged : BlackBoxReconstruction.judge config active.world
          (blackBoxContext carrier) actions with
      | some run => some ⟨.blackBox active carrier claim config hadmitted actions run hjudged⟩
      | none => none
  | .deckDescent config, .deckDescent actions =>
      match hjudged : DeckDescent.judge config active.world
          (deckDescentContext active carrier) actions with
      | some run => some ⟨.deckDescent active carrier claim config hadmitted actions run hjudged⟩
      | none => none
  | .ventCrawl config, .ventCrawl actions =>
      match hjudged : VentCrawl.judge config active.world
          (ventCrawlContext active carrier) actions with
      | some run => some ⟨.ventCrawl active carrier claim config hadmitted actions run hjudged⟩
      | none => none
  | _, _ => none

/-- The only constructor surface: checks first, exact game tag second, executable
judge third.  Every failure returns `none`. -/
def judgeActive (active : ActiveRunState) (carrier : FinalizedCarrier)
    (claim : RunClaim) (submitted : SubmittedRun) : Option JudgedRun :=
  if hadmitted : admissionChecks active carrier claim = true then
    judgeAdmitted active carrier claim submitted hadmitted
  else none

/-- The two entries are the same function wherever admission holds.  This is what
stops `judgeAdmitted` from being a weaker surface: a caller who takes it has, by its
own argument, everything `judgeActive` would have decided. -/
theorem judgeActive_eq_judgeAdmitted (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (hadmitted : admissionChecks active carrier claim = true) :
    judgeActive active carrier claim submitted =
      judgeAdmitted active carrier claim submitted hadmitted := by
  simp [judgeActive, hadmitted]

/-- Conversely, refusing admission refuses the run through either entry. -/
theorem judgeActive_eq_none_of_not_admitted (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (hrefused : admissionChecks active carrier claim ≠ true) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, hrefused]

/-- Constructive inhabitation bridge for the first live game: any genuinely
successful Signal judge under admitted active inputs produces an abstract
`JudgedRun`; no token, axiom, or unsafe constructor is involved. -/
theorem judgeActive_signal_of_exact {active : ActiveRunState}
    {carrier : FinalizedCarrier} {claim : RunClaim}
    {config : SignalTriangulation.Config} {actions : List SignalTriangulation.Action}
    {raw : SignalTriangulation.JudgedRun}
    (hgame : active.game = .signal config)
    (hadmitted : admissionChecks active carrier claim = true)
    (hjudged : SignalTriangulation.judge config active.world
      (signalContext carrier) actions = some raw) :
    ∃ run : JudgedRun,
      judgeActive active carrier claim (.signal actions) = some run ∧
      run.receipt = raw.receipt := by
  rw [judgeActive_eq_judgeAdmitted _ _ _ _ hadmitted]
  unfold judgeAdmitted
  simp only [hgame]
  split
  · rename_i found hfound
    rw [hfound] at hjudged
    injection hjudged with heq
    subst found
    exact ⟨_, rfl, rfl⟩
  · rename_i hnone
    rw [hnone] at hjudged
    contradiction

theorem judgeActive_success_admitted {active : ActiveRunState} {carrier : FinalizedCarrier}
    {claim : RunClaim} {submitted : SubmittedRun} {run : JudgedRun}
    (h : judgeActive active carrier claim submitted = some run) :
    admissionChecks active carrier claim = true := by
  unfold judgeActive at h
  split at h
  · assumption
  · contradiction

theorem judgeActive_wrong_activation_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.activationDigest ≠ carrier.activationDigest) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_wrong_config_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.config ≠ active.game.configClaim) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_inactive_activation_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : active.activationDigest ≠ active.game.mission.activationDigest) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_wrong_session_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.contentSession ≠ carrier.contentSession) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_wrong_epoch_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.contentEpoch ≠ carrier.contentEpoch) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_wrong_slot_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.slot ≠ active.slot) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

/-- A run played against a commitment the node did not publish for this slot is
refused: the client's opening and the node's active state must be the same one. -/
theorem judgeActive_wrong_commitment_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.slotCommitment ≠ active.slotCommitment) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

/-- ⚑ **The commitment binds the secret that is actually judged.**  A node that
published one commitment and then judged against a different slot secret is
refused, so "choose the instance after seeing the transcript" is not a move
available to the operator. -/
theorem judgeActive_uncommitted_secret_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : active.slotCommitment ≠ HiddenInstance.commit active.slotSecret active.slot) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

/-- ⚑ **The played instance is the derived one.**  The active run seed — which is
what every kernel binds its target, board or seed to — must be exactly
`runSeedFor` of the committed secret, this slot and THIS player.  A seed supplied
from anywhere else, including the `UNBOUND_RUN_SEED` a catalog template carries,
is refused. -/
theorem judgeActive_underived_seed_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : active.runSeed ≠
      HiddenInstance.runSeedFor
        { secret := active.slotSecret, slot := active.slot, playerKey := carrier.playerKey }
        (HiddenInstance.MissionContext.ofMission active.game.mission)) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_wrong_player_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.playerKey ≠ carrier.playerKey) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_wrong_actor_root_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.actorRoot ≠ carrier.actorRoot) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_stale_counter_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.claimedPreviousPlayerCounter ≠ carrier.currentPlayerCounter.val) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_wrong_current_counter_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : active.playerCounters.lookup carrier.counterKey ≠ carrier.currentPlayerCounter) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [h]

theorem judgeActive_counter_exhausted_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : PLAYER_COUNTER_MODULUS ≤ carrier.currentPlayerCounter.val + 1) :
    judgeActive active carrier claim submitted = none := by
  apply judgeActive_eq_none_of_not_admitted
  rw [Ne, admissionChecks_eq_true_iff]
  simp [Nat.not_lt.mpr h]

theorem judgeActive_wrong_game_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim)
    (config : SignalTriangulation.Config) (actions : List RelayRepair.Action)
    (hgame : active.game = .signal config) :
    judgeActive active carrier claim (.relay actions) = none := by
  unfold judgeActive
  split
  · unfold judgeAdmitted
    simp only [hgame]
  · rfl

/-- The sixth arm is tag-checked like the other five: a vent-crawl transcript
submitted against a descent game is refused before either judge runs, so the new
arm did not open a door that dispatches on the transcript. -/
theorem judgeActive_vent_crawl_against_descent_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim)
    (config : DeckDescent.Config) (actions : List VentCrawl.Action)
    (hgame : active.game = .deckDescent config) :
    judgeActive active carrier claim (.ventCrawl actions) = none := by
  unfold judgeActive
  split
  · unfold judgeAdmitted
    simp only [hgame]
  · rfl

/-- Every inhabitant retains an equality to one concrete executable judge. -/
theorem JudgedRun.has_executable_origin (run : JudgedRun) :
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : SignalTriangulation.Config) (actions : List SignalTriangulation.Action)
        (raw : SignalTriangulation.JudgedRun),
      SignalTriangulation.judge config active.world (signalContext carrier) actions = some raw ∧
      run.receipt = raw.receipt) ∨
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : RelayRepair.Config) (actions : List RelayRepair.Action)
        (raw : RelayRepair.JudgedRun),
      RelayRepair.judge config active.world (relayContext carrier) actions = some raw ∧
      run.receipt = raw.receipt) ∨
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : SalvageLock.Config) (actions : List SalvageLock.Action)
        (raw : SalvageLock.JudgedRun),
      SalvageLock.judge config active.world (salvageContext carrier) actions = some raw ∧
      run.receipt = raw.receipt) ∨
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : BlackBoxReconstruction.Config)
        (actions : List BlackBoxReconstruction.Action)
        (raw : BlackBoxReconstruction.JudgedRun),
      BlackBoxReconstruction.judge config active.world (blackBoxContext carrier) actions = some raw ∧
      run.receipt = raw.receipt) ∨
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : DeckDescent.Config)
        (actions : List DeckDescent.Action)
        (raw : DeckDescent.JudgedRun),
      DeckDescent.judge config active.world (deckDescentContext active carrier) actions = some raw ∧
      run.receipt = raw.receipt) ∨
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : VentCrawl.Config)
        (actions : List VentCrawl.Action)
        (raw : VentCrawl.JudgedRun),
      VentCrawl.judge config active.world (ventCrawlContext active carrier) actions = some raw ∧
      run.receipt = raw.receipt) := by
  obtain ⟨evidence⟩ := run
  cases evidence with
  | signal active carrier claim config admitted actions raw judged =>
      exact Or.inl ⟨active, carrier, config, actions, raw, judged, rfl⟩
  | relay active carrier claim config admitted actions raw judged =>
      exact Or.inr (Or.inl ⟨active, carrier, config, actions, raw, judged, rfl⟩)
  | salvage active carrier claim config admitted actions raw judged =>
      exact Or.inr (Or.inr (Or.inl ⟨active, carrier, config, actions, raw, judged, rfl⟩))
  | blackBox active carrier claim config admitted actions raw judged =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨active, carrier, config, actions, raw, judged, rfl⟩)))
  | deckDescent active carrier claim config admitted actions raw judged =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨active, carrier, config, actions, raw, judged, rfl⟩))))
  | ventCrawl active carrier claim config admitted actions raw judged =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨active, carrier, config, actions, raw, judged, rfl⟩))))

theorem JudgedRun.applied (run : JudgedRun) :
    applyContribution run.receipt.mission run.receipt.contribution
      run.receipt.preWorld = some run.receipt.postWorld :=
  run.receipt.applied

theorem JudgedRun.player_counter_positive (run : JudgedRun) :
    0 < run.receipt.playerCounter :=
  run.receipt.player_counter_positive

#assert_axioms admissionChecks_eq_true_iff
#assert_axioms judgeActive_eq_judgeAdmitted
#assert_axioms judgeActive_eq_none_of_not_admitted
#assert_axioms judgeActive_signal_of_exact
#assert_axioms judgeActive_success_admitted
#assert_axioms judgeActive_wrong_activation_refused
#assert_axioms judgeActive_wrong_config_refused
#assert_axioms judgeActive_inactive_activation_refused
#assert_axioms judgeActive_wrong_session_refused
#assert_axioms judgeActive_wrong_epoch_refused
#assert_axioms judgeActive_wrong_slot_refused
#assert_axioms judgeActive_wrong_commitment_refused
#assert_axioms judgeActive_uncommitted_secret_refused
#assert_axioms judgeActive_underived_seed_refused
#assert_axioms judgeActive_wrong_player_refused
#assert_axioms judgeActive_wrong_actor_root_refused
#assert_axioms judgeActive_stale_counter_refused
#assert_axioms judgeActive_wrong_current_counter_refused
#assert_axioms judgeActive_counter_exhausted_refused
#assert_axioms judgeActive_wrong_game_refused
#assert_axioms judgeActive_vent_crawl_against_descent_refused
#assert_axioms JudgedRun.has_executable_origin
#assert_axioms JudgedRun.applied
#assert_axioms JudgedRun.player_counter_positive

end Dregg2.Games.PathOfAngels
