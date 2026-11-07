/-
# Crew field mission — the hostility-lab EVALUATION, out of the crypto archive's build

`CrewFieldMission.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its laboratory ran sixty-three `native_decide` pins at elaboration — the
largest single population in the game cone — so any game-fixture regression was a hard failure
of every Rust proving target in the workspace (the compilation-unit coupling the stale-fixture
outage measured). The lab's STATEMENTS remain in `CrewFieldMission.lean`, beside the private
fixture world (`fixtureConfig`, `drive`, `completionFor?`, `katConfig`, the KAT envelopes) they
must see; THIS module is where they are RUN. It is rooted in the `PathOfAngelsGuards` library
and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. Two statement shapes arrive here, both evaluation-free in
the parent: pins whose statement was ALREADY a named public `Bool` definition are pinned under
that definition; the rest are pinned through the `check_<theorem_name> : Bool` definition the
parent now carries.

⚠ Five construction proofs did NOT move — `fixturePolicy.catalogue_bounded`,
`wrongArtifactPolicy.catalogue_bounded`, `fixture_config_valid`, `fixture_rekeyed_config_valid`
and `kat_config_valid`. `ActivityOutcome.Policy` carries its bound as a field and `Config`
carries `rawConfigValidB … = true` as a field, so those proofs must elaborate where the
fixture, rekeyed and KAT worlds are BUILT. They are the named residue; the lab header in
`CrewFieldMission.lean` records it. `fixture_run_seal_carries_the_fixture_session` also stays
there — it is `rfl`, and its `#assert_compiled` census line reflects the residue its statement
reaches through.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMission
import Batteries.Tactic.OpenPrivate

namespace Dregg2.Games.PathOfAngels.CrewFieldMission

set_option autoImplicit false
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition
open scoped Prod.Lex
-- The laboratory reads these runtime helpers; they stay private to the runtime module.
open private completionFor? drive fixtureAdmission fixtureBriefingDigest fixtureConfig
   fixtureExpectedSignature fixtureMessageDigest fixtureRawConfigBase signatureBytesPattern
   testHandoff? withFixtureBriefingCommitment from Dregg2.Games.PathOfAngels.CrewFieldMission

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

def wrongMissionArtifact : ArtifactRef := {
  fixtureMaintenanceArtifact with missionId := ⟨7002⟩ }

def wrongArtifactPolicy : ActivityOutcome.Policy where
  mission := DeckExpedition.fixtureMission
  allowedBeta := {fixtureMaintenanceArtifact, fixtureSignalArtifact,
    fixtureNaveArtifact, wrongMissionArtifact}
  resultLimit := ⟨1, by decide⟩
  catalogue_bounded := by native_decide

def wrongMissionOutcome : ActivityOutcome.Raw := {
  fixtureOutcome .maintenanceSpine .returnNow with
  betaCandidates := [wrongMissionArtifact] }

/-- Every terminal cost is individually within budget three, but mandatory
specialist play spends all three units before the quartermaster can act. -/
def globallyUnwinnableRouteOutcomes : List RouteOutcomeSpec :=
  [ ⟨.maintenanceSpine, .returnNow, 1, fixtureMaintenanceArtifact,
      fixtureOutcome .maintenanceSpine .returnNow⟩
  , ⟨.maintenanceSpine, .descendFurther, 1, fixtureMaintenanceArtifact,
      fixtureOutcome .maintenanceSpine .descendFurther⟩
  , ⟨.signalGallery, .returnNow, 2, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .returnNow⟩
  , ⟨.signalGallery, .descendFurther, 2, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .descendFurther⟩
  , ⟨.sealedNave, .returnNow, 3, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .returnNow⟩
  , ⟨.sealedNave, .descendFurther, 3, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .descendFurther⟩ ]

def wrongArtifactRouteOutcomes : List RouteOutcomeSpec :=
  [ ⟨.maintenanceSpine, .returnNow, 2, wrongMissionArtifact,
      wrongMissionOutcome⟩
  , ⟨.maintenanceSpine, .descendFurther, 5, fixtureMaintenanceArtifact,
      fixtureOutcome .maintenanceSpine .descendFurther⟩
  , ⟨.signalGallery, .returnNow, 3, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .returnNow⟩
  , ⟨.signalGallery, .descendFurther, 7, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .descendFurther⟩
  , ⟨.sealedNave, .returnNow, 11, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .returnNow⟩
  , ⟨.sealedNave, .descendFurther, 12, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .descendFurther⟩ ]

def globallyUnwinnableRawConfig : RawConfig :=
  withFixtureBriefingCommitment {
    fixtureRawConfigBase with
    operationalBudget := 3
    routeOutcomes := globallyUnwinnableRouteOutcomes }

/-- The authored fixture commitment IS the digest of the authored ordered deck.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_fixture_ordered_briefing_deck_is_commitment_bound : Bool :=
  decide (fixtureRawConfig.briefingCommitment = fixtureBriefingDigest.digest
    (briefingDeckPreimage fixtureRawConfig fixtureBriefings))

/-- Every terminal cost in the unwinnable table is individually affordable — the
premise that makes the refusal below a statement about GLOBAL reachability rather
than about one oversized row. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_unwinnable_terminal_costs_are_individually_within_budget : Bool :=
  globallyUnwinnableRouteOutcomes.all fun spec =>
    decide (0 < spec.operationalCost ∧
      spec.operationalCost ≤ globallyUnwinnableRawConfig.operationalBudget)

/-- No safe terminal survives the three mandatory survey handoffs.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_unwinnable_config_has_no_affordable_safe_terminal : Bool :=
  !(authoredSafeTerminalReachabilityFloorB globallyUnwinnableRawConfig)

/-- …and activation therefore refuses the whole config.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_globally_unwinnable_config_refused_at_activation : Bool :=
  !(rawConfigValidB globallyUnwinnableRawConfig fixtureBriefings fixtureBriefingDigest)

/-- Mutating any of the four mission-identity fields away from the policy mission
breaks activation. (Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem
name `raw_identity_fields_must_exactly_match_policy_mission`.) -/
def missionIdentityMutationsRefusedB : Bool :=
  let mutations : List RawConfig :=
    [ { fixtureRawConfigBase with federationId := digestFilled 241 }
    , { fixtureRawConfigBase with contentSession := digestFilled 242 }
    , { fixtureRawConfigBase with missionEpoch := ⟨243⟩ }
    , { fixtureRawConfigBase with missionId := ⟨244⟩ } ]
  mutations.all fun raw =>
    !(rawConfigValidB (withFixtureBriefingCommitment raw) fixtureBriefings
      fixtureBriefingDigest)

def wrongMissionArtifactRawConfig : RawConfig :=
  withFixtureBriefingCommitment {
    fixtureRawConfigBase with
    policy := wrongArtifactPolicy
    routeOutcomes := wrongArtifactRouteOutcomes }

/-- The honest control for the refusal below: the wrong-mission artifact is
otherwise a perfectly declared beta candidate of a perfectly valid outcome, so the
refusal is about the MISSION field and nothing else.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_wrong_mission_artifact_is_otherwise_declared_and_outcome_valid : Bool :=
  (ActivityOutcome.validate wrongArtifactPolicy wrongMissionOutcome).isSome &&
  decide (wrongMissionArtifact ∈ wrongMissionOutcome.betaCandidates)

/-- An artifact from another mission is refused at activation.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_artifact_mission_must_exactly_match_activated_mission : Bool :=
  !(rawConfigValidB wrongMissionArtifactRawConfig fixtureBriefings fixtureBriefingDigest)

def substitutedFixtureBriefings : List BriefingAssignment :=
  [ ⟨⟨0⟩, .pathfinder .sealedNave⟩
  , ⟨⟨1⟩, .engineer .signalGallery⟩
  , ⟨⟨2⟩, .containment .signalGallery⟩
  , ⟨⟨3⟩, .quartermaster .stable⟩ ]

/-- Substituting one same-role briefing breaks the activation commitment.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_same_role_briefing_substitution_breaks_activation_commitment : Bool :=
  !(rawConfigValidB fixtureRawConfig substitutedFixtureBriefings fixtureBriefingDigest)

def safePlan : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .signalGallery .chartPressureRoute)
  , (⟨1⟩, .specialist .signalGallery .braceTransit)
  , (⟨2⟩, .specialist .sealedNave .quietAnomaly)
  , (⟨3⟩, .finalize .signalGallery .returnNow .bankSupplies) ]

/-- The substitution moved the wallet keys and nothing else about who the crew
is.  Asserted here, next to the world it describes, so the world cannot quietly
become a copy of the authored one. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_fixture_rekeyed_roster_substitutes_only_the_player_keys : Bool :=
  decide (fixtureRekeyedRoster.map Seat.playerKey ≠ fixtureRoster.map Seat.playerKey) &&
  decide (fixtureRekeyedRoster.map Seat.id = fixtureRoster.map Seat.id) &&
  decide (fixtureRekeyedRoster.map Seat.role = fixtureRoster.map Seat.role) &&
  decide (fixtureRekeyedRoster.map Seat.credential = fixtureRoster.map Seat.credential) &&
  decide (fixtureRekeyedRoster.map Seat.initialCounter =
    fixtureRoster.map Seat.initialCounter)

/-- ⚑ The fixture briefing commitment does NOT separate these two crews: the
substituted roster carrying the authored commitment is still a valid config.
Recorded as a pin because it is the reason the seal has to be what refuses,
and because the opposite was asserted here first and was false.  This is a fact
about the eight-bit fixture digest, not about the design: a deployment digest
would separate them. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_the_fixture_briefing_commitment_does_not_separate_the_two_crews : Bool :=
  rawConfigValidB { fixtureRawConfig with roster := fixtureRekeyedRoster }
    fixtureBriefings fixtureBriefingDigest

/-- The two seals are for different sessions.  Without this the runtime's
cross-crew refusals could be comparing a world with itself.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_the_two_fixture_seals_carry_different_sessions : Bool :=
  decide (fixtureRekeyedRunSeal.session ≠ fixtureRunSeal.session)

/-- Both exported transcripts are a full crew of signed handoffs — and therefore
neither `getD []` fallback above fired.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_exported_fixture_transcripts_are_four_signed_handoffs_each : Bool :=
  decide (fixtureSafeMaintenanceTranscript.length = CREW_SIZE) &&
  decide (fixtureDeepTranscript.length = CREW_SIZE)

private def fixtureSeatSignature (seat : Seat) : SeatSignature :=
  { bytes := fixtureExpectedSignature 1 seat.playerKey seat.credential
      (fixtureMessageDigest.seatMessageDigest
        ((expectedAdmission fixtureConfig seat).signingPreimage
          fixtureConfig.raw.messageDigestSuiteId fixtureConfig.raw.signingSuiteId)) }

private def fixtureHandoffSignatureFor (seat : Seat) (preimage : HandoffSigningPreimage) :
    HandoffSignature :=
  { bytes := fixtureExpectedSignature 2 seat.playerKey seat.credential
      (fixtureMessageDigest.handoffMessageDigest preimage) }

/-- The prefix gap, stated: four proper prefixes at which the kernel has a state
and `replay?` has nothing to say, and one completed run where they agree.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`the_step_surface_answers_at_every_prefix_replay_refuses`.) -/
def stepAnswersEveryPrefixWhileReplayIsSilentB : Bool :=
  let transcript := fixtureDeepTranscript
  let views := (List.range (CREW_SIZE + 1)).map fun k =>
    fixtureRunSeal.step? (transcript.take k)
  let roots := views.filterMap fun view? => view?.map StepView.reachedRoot
  decide (roots.length = CREW_SIZE + 1) &&
  decide (roots.Nodup) &&
  ((List.range (CREW_SIZE + 1)).all fun k =>
    match fixtureRunSeal.step? (transcript.take k) with
    | none => false
    | some view =>
        decide (view.sequence = k) &&
        decide (view.session = fixtureRunSeal.session) &&
        decide (view.nextSeat.isSome = decide (k < CREW_SIZE)) &&
        decide (view.phase = if k = CREW_SIZE then MissionPhase.extracted else .active) &&
        decide ((fixtureRunSeal.replay? (transcript.take k)).isSome =
          decide (k = CREW_SIZE)))

/-- One handoff, produced through nothing but the public surface: ask the seal
what this seat must sign, sign exactly those bytes, and emit the trace.  No
caller-side transition, no caller-authored `preRoot`. -/
private def stepDrive : List HandoffTrace → List Decision → Option (List HandoffTrace)
  | transcript, [] => some transcript
  | transcript, decision :: rest => do
      let view ← fixtureRunSeal.step? transcript
      let seat ← view.nextSeat
      let seatSignature := fixtureSeatSignature seat
      let preimage ← fixtureRunSeal.nextSigningPreimage? transcript seatSignature decision
      let trace : HandoffTrace := {
        sequence := preimage.body.sequence
        seat := preimage.body.seat
        previousCounter := preimage.body.previousCounter
        counter := preimage.body.counter
        observation := preimage.body.observation
        decision := preimage.body.decision
        seatSignature
        signature := fixtureHandoffSignatureFor seat preimage }
      stepDrive (transcript ++ [trace]) rest

/-- ⚑ ONE SEAT'S SIGNED HANDOFF IS COMPLETABLE — four times over.  Driven from
the empty transcript through `step?` and `nextSigningPreimage?` alone, a client
that never reimplements the transition reconstructs the kernel's own signed
transcript byte for byte, and the seal admits the run it built.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`a_crew_plays_a_whole_run_one_signed_handoff_at_a_time`.) -/
def stepSurfaceDrivesAWholeSignedRunB : Bool :=
  match stepDrive [] (deepPlan.map Prod.snd) with
  | none => false
  | some transcript =>
      decide (transcript = fixtureDeepTranscript) &&
      (fixtureRunSeal.replay? transcript).isSome &&
      match fixtureRunSeal.step? transcript with
      | none => false
      | some view => decide (view.completion = fixtureRunSeal.replay? transcript)

/-- The mutation is asserted present (`other ≠ turn`) and the honest control is
in the same statement: seat 0's own admission envelope opens seat 0's briefing,
seat 1's does not.  Without the second conjunct's control this would pass for a
surface that refused everyone.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`the_step_surface_opens_a_briefing_only_to_its_own_seat`.) -/
def stepSurfaceRefusesAnotherSeatsAdmissionB : Bool :=
  let decision : Decision := .specialist .signalGallery .markSalvageRoute
  match fixtureRunSeal.step? [] with
  | none => false
  | some view =>
    match view.nextSeat, seatById? fixtureRawConfig.roster ⟨1⟩ with
    | some turn, some other =>
        decide (other ≠ turn) &&
        (fixtureRunSeal.nextSigningPreimage? [] (fixtureSeatSignature other) decision).isNone &&
        (fixtureRunSeal.nextSigningPreimage? [] (fixtureSeatSignature turn) decision).isSome
    | _, _ => false

/-- The seal admits the record the kernel itself produced.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`run_seal_admits_the_record_the_kernel_produced`.) -/
def sealAdmitsKernelProducedRecordB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record => fixtureRunSeal.admits record.toRaw

/-- ⚑ The fabrication check, and the reason `RunSeal` exists.  A caller that
asserts a terminal state — the exact defect `CrewFieldMissionRuntime.deriveRecord?`
had — is refused, because `admits` reaches that state by running `execute` rather
than by reading the claim.  The mutated root is built from the live record and
asserted different before the verdict is read.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`run_seal_refuses_a_terminal_state_the_kernel_did_not_reach`.) -/
def sealRefusesAssertedTerminalRootB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record =>
      let raw := record.toRaw
      let asserted : StateRoot := { raw.finalRoot with snapshot :=
        { raw.finalRoot.snapshot with
          operationalBudgetRemaining :=
            raw.finalRoot.snapshot.operationalBudgetRemaining + 1 } }
      decide (asserted ≠ raw.finalRoot) &&
      !fixtureRunSeal.admits { raw with finalRoot := asserted }

/-- The signature leg: one forged handoff signature and the seal refuses.  The
forgery is constructed from the live trace and asserted to differ from it, so
this cannot quietly become a comparison of a value with itself.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`run_seal_refuses_a_forged_handoff_signature`.) -/
def sealRefusesForgedHandoffSignatureB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record =>
      match record.toRaw.transcript with
      | [] => false
      | trace :: rest =>
          let forged : HandoffTrace :=
            { trace with signature := ⟨signatureBytesPattern 251⟩ }
          decide (forged.signature ≠ trace.signature) &&
          !fixtureRunSeal.admits { record.toRaw with transcript := forged :: rest }

/-- Safe extraction accepts two matching signed route recommendations.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_safe_extraction_accepts_two_matching_signed_recommendations : Bool :=
  (completionFor? safePlan).isSome

/-- A second authored safe route is reachable, so the safe terminal is not one
hard-coded branch. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_alternative_safe_route_is_reachable : Bool :=
  (completionFor? safeMaintenancePlan).isSome

/-- Deep recovery accepts full-crew consensus.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_deep_recovery_requires_and_accepts_full_crew_consensus : Bool :=
  (completionFor? deepPlan).isSome

/-- Route and extraction choices produce materially distinct records.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`route_and_extraction_choices_produce_materially_distinct_records`.) -/
def completedPlansDifferB : Bool :=
  match completionFor? safePlan, completionFor? deepPlan with
  | some safe, some deep =>
      decide (safe.extraction = .returnNow) &&
      decide (deep.extraction = .descendFurther) &&
      decide (safe.outcome.contribution ≠ deep.outcome.contribution) &&
      decide (safe.featuredBeta ∈ safe.outcome.betaCandidates) &&
      decide (deep.featuredBeta ∈ deep.outcome.betaCandidates)
  | _, _ => false

/-- Specialist steps and the final route are both charged exactly, and the
remaining budget closes the sum. (Pinned `= true` in `CrewFieldMissionFixtures`,
under the theorem name `specialist_steps_and_final_route_are_both_charged_exactly`.) -/
def completedBudgetAccountingB : Bool :=
  match completionFor? safePlan, completionFor? deepPlan with
  | some safe, some deep =>
      decide (safe.routeOperationalCost = 3) &&
      decide (safe.totalOperationalCost = 6) &&
      decide (safe.finalRoot.snapshot.operationalBudgetRemaining = 7) &&
      decide (safe.totalOperationalCost +
        safe.finalRoot.snapshot.operationalBudgetRemaining =
          fixtureRawConfig.operationalBudget) &&
      decide (deep.routeOperationalCost = 7) &&
      decide (deep.totalOperationalCost = 13) &&
      decide (deep.finalRoot.snapshot.operationalBudgetRemaining = 0) &&
      decide (deep.totalOperationalCost +
        deep.finalRoot.snapshot.operationalBudgetRemaining =
          fixtureRawConfig.operationalBudget)
  | _, _ => false

/-- Route is a material choice even with extraction held fixed: it changes
cost, bounded reward, and the exact beta candidate.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`route_changes_cost_reward_and_artifact_at_fixed_extraction`.) -/
def fixedExtractionRouteVariationB : Bool :=
  match completionFor? safePlan, completionFor? safeMaintenancePlan with
  | some signal, some maintenance =>
      decide (signal.extraction = .returnNow) &&
      decide (maintenance.extraction = .returnNow) &&
      decide (signal.route ≠ maintenance.route) &&
      decide (signal.routeOperationalCost ≠ maintenance.routeOperationalCost) &&
      decide (signal.totalOperationalCost ≠ maintenance.totalOperationalCost) &&
      decide (signal.finalRoot.snapshot.operationalBudgetRemaining ≠
        maintenance.finalRoot.snapshot.operationalBudgetRemaining) &&
      decide (signal.outcome.contribution ≠ maintenance.outcome.contribution) &&
      decide (signal.featuredBeta ≠ maintenance.featuredBeta)
  | _, _ => false

/-- All six authored route/extraction outcomes are bounded and declared.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`all_six_authored_route_extraction_outcomes_are_bounded_and_declared`.) -/
def allAuthoredOutcomesWellFormedB : Bool :=
  fixtureRouteOutcomes.all fun spec =>
    (ActivityOutcome.validate fixturePolicy spec.outcome).isSome &&
    decide (spec.featuredArtifact ∈ spec.outcome.betaCandidates) &&
    decide (0 < spec.operationalCost)

def overBudgetSafePrefix : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .sealedNave .chartPressureRoute)
  , (⟨1⟩, .specialist .sealedNave .braceTransit)
  , (⟨2⟩, .specialist .signalGallery .quietAnomaly) ]

/-- This branch satisfies the safe-return recommendation rule but its three
survey steps leave only ten units, less than the sealed-nave return cost eleven. -/
def overBudgetSafeFinalResult : Option Refusal := do
  let prefixResult ← drive (start fixtureAdmission) overBudgetSafePrefix
  let handoff ← testHandoff? prefixResult.state ⟨3⟩
    (.finalize .sealedNave .returnNow .bankSupplies)
  match execute fixtureConfig prefixResult.state handoff with
  | .error refusal => some refusal
  | .ok _ => none

/-- A recommendation-valid but over-budget route is refused at the LIVE budget
boundary, not at authoring time.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_recommendation_valid_but_over_budget_route_is_refused_at_live_budget_boundary : Bool :=
  decide (overBudgetSafeFinalResult = some Refusal.insufficientOperationalBudget)

def mixedStrategyPlan : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .signalGallery .markSalvageRoute)
  , (⟨1⟩, .specialist .signalGallery .braceTransit)
  , (⟨2⟩, .specialist .signalGallery .quietAnomaly)
  , (⟨3⟩, .finalize .signalGallery .returnNow .bankSupplies) ]

/-- A crew that mixes survey and salvage commands cannot complete a run.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_mixed_crew_strategy_refused : Bool :=
  (drive (start fixtureAdmission) mixedStrategyPlan).isNone

def splitDeepPlan : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .signalGallery .markSalvageRoute)
  , (⟨1⟩, .specialist .maintenanceSpine .overdriveCargoLift)
  , (⟨2⟩, .specialist .signalGallery .screenRecovery)
  , (⟨3⟩, .finalize .signalGallery .descendFurther .secureCache) ]

/-- Deep recovery without unanimity cannot complete a run.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_deep_recovery_without_unanimity_refused : Bool :=
  (drive (start fixtureAdmission) splitDeepPlan).isNone

private def firstState : State := start fixtureAdmission

private def firstHandoff? : Option (SignedHandoff fixtureConfig) :=
  testHandoff? firstState ⟨0⟩ (.specialist .signalGallery .chartPressureRoute)

def substitutedObservationResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forgedBody := { handoff.body with observation := .pathfinder .sealedNave }
  match execute fixtureConfig firstState { handoff with body := forgedBody } with
  | .error refusal => some refusal
  | .ok _ => none

/-- Substituting the private observation in a signed body is refused as an
observation mismatch. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_private_observation_substitution_refused : Bool :=
  decide (substitutedObservationResult = some Refusal.observationMismatch)

def staleRootResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forgedRoot : StateRoot := {
    handoff.body.preRoot with snapshot := {
      handoff.body.preRoot.snapshot with sequence := 1 } }
  let forgedBody := { handoff.body with preRoot := forgedRoot }
  match execute fixtureConfig firstState { handoff with body := forgedBody } with
  | .error refusal => some refusal
  | .ok _ => none

/-- A body addressed at a stale predecessor root is refused.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_stale_predecessor_root_refused : Bool :=
  decide (staleRootResult = some Refusal.staleRoot)

def substitutedSignatureResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forged := { handoff with signature := {
    bytes := signatureBytesPattern 250 } }
  match execute fixtureConfig firstState forged with
  | .error refusal => some refusal
  | .ok _ => none

/-- A substituted handoff signature is refused.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_handoff_signature_substitution_refused : Bool :=
  decide (substitutedSignatureResult = some Refusal.signatureRefused)

def unsignedDecisionSubstitutionResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forgedBody := { handoff.body with decision :=
    (Decision.specialist Route.maintenanceSpine Command.chartPressureRoute) }
  match execute fixtureConfig firstState { handoff with body := forgedBody } with
  | .error refusal => some refusal
  | .ok _ => none

/-- Substituting the decision the seat signed is caught by the signature.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_full_field_decision_substitution_refused_by_signature : Bool :=
  decide (unsignedDecisionSubstitutionResult = some Refusal.signatureRefused)

def otherSeatSignatureResult : Option Refusal := do
  let handoff ← firstHandoff?
  let messageDigest := fixtureMessageDigest.handoffMessageDigest
    (handoff.body.signingPreimage fixtureConfig.raw.messageDigestSuiteId
      fixtureConfig.raw.signingSuiteId)
  let forgedSignature : HandoffSignature := {
    bytes := fixtureExpectedSignature 2 fixtureSeat1.playerKey
      fixtureSeat1.credential messageDigest }
  match execute fixtureConfig firstState { handoff with signature := forgedSignature } with
  | .error refusal => some refusal
  | .ok _ => none

/-- A signature issued for another seat is refused.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_signature_issued_for_other_seat_refused : Bool :=
  decide (otherSeatSignatureResult = some Refusal.signatureRefused)

def wrongSigningSuiteResult : Option Refusal := do
  let handoff ← firstHandoff?
  let wrongPreimage := handoff.body.signingPreimage
    fixtureConfig.raw.messageDigestSuiteId (digestFilled 249)
  let forgedSignature : HandoffSignature := {
    bytes := fixtureExpectedSignature 2 handoff.capability.seat.playerKey
      handoff.capability.seat.credential
      (fixtureMessageDigest.handoffMessageDigest wrongPreimage) }
  match execute fixtureConfig firstState { handoff with signature := forgedSignature } with
  | .error refusal => some refusal
  | .ok _ => none

/-- A signature over a different signing-suite preimage is refused.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_signing_suite_substitution_refused : Bool :=
  decide (wrongSigningSuiteResult = some Refusal.signatureRefused)

private def digestDoubledAsSignatureBytes (digest : Digest32) : SignatureBytes where
  bytes := digest.bytes ++ digest.bytes ++
    List.replicate (SIGNATURE_BYTE_LENGTH - 64) 0
  length_eq := by
    simp only [List.length_append, List.length_replicate, digest.length_eq]
    decide

/-- A message digest is public and easy to compute.  Repeating its 32 bytes
(zero-padded to the envelope length) still provides no proof of key
possession. -/
def forgedMessageDigestAsSignatureResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forgedSignature : HandoffSignature := {
    bytes := digestDoubledAsSignatureBytes
      (handoff.body.messageDigest fixtureConfig) }
  match execute fixtureConfig firstState { handoff with signature := forgedSignature } with
  | .error refusal => some refusal
  | .ok _ => none

/-- The public message digest, repeated to envelope length, is not a signature.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_hostile_public_message_digest_submitted_as_signature_refused : Bool :=
  decide (forgedMessageDigestAsSignatureResult = some Refusal.signatureRefused)

/-- Substituting the route in a combined record breaks readmission.
(Pinned `= false` in `CrewFieldMissionFixtures`, under the theorem name
`hostile_combined_record_route_substitution_refused`.) -/
def tamperedRecordReadmitsB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record =>
      let raw := { record.toRaw with route := .sealedNave }
      (admitCombinedFieldRecord? fixtureAdmission raw).isSome

private def tamperFirstTrace : List HandoffTrace → List HandoffTrace
  | [] => []
  | trace :: traces =>
      { trace with decision := .specialist .maintenanceSpine .markSalvageRoute } :: traces

/-- Eleven mutations of the kernel-produced record, every one refused at
readmission. (Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem
name `hostile_expanded_record_mutation_matrix_refused`.) -/
def expandedRecordMutationsRefusedB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record =>
      let raw := record.toRaw
      let rootMutation := { raw.finalRoot with snapshot := {
        raw.finalRoot.snapshot with sequence := raw.finalRoot.snapshot.sequence + 1 } }
      let mutations : List RawCombinedFieldRecord :=
        [ { raw with route := .sealedNave }
        , { raw with extraction := .returnNow }
        , { raw with strategy := .survey }
        , { raw with routeOperationalCost := raw.routeOperationalCost + 1 }
        , { raw with totalOperationalCost := raw.totalOperationalCost + 1 }
        , { raw with
              outcome := fixtureOutcome .maintenanceSpine .descendFurther
              featuredBeta := fixtureMaintenanceArtifact }
        , { raw with featuredBeta := fixtureMaintenanceArtifact }
        , { raw with finalRoot := rootMutation }
        , { raw with transcript := tamperFirstTrace raw.transcript }
        , { raw with transcript := raw.transcript.reverse }
        , { raw with session := {
              raw.session with briefingCommitment := digestFilled 244 } } ]
      mutations.all fun mutated =>
        !(admitCombinedFieldRecord? fixtureAdmission mutated).isSome

/-! ## Activation: the authored deployment, and what activation refuses -/

theorem fixture_ordered_briefing_deck_is_commitment_bound :
    check_fixture_ordered_briefing_deck_is_commitment_bound = true := by native_decide

theorem hostile_unwinnable_terminal_costs_are_individually_within_budget :
    check_hostile_unwinnable_terminal_costs_are_individually_within_budget = true := by
  native_decide

theorem hostile_unwinnable_config_has_no_affordable_safe_terminal :
    check_hostile_unwinnable_config_has_no_affordable_safe_terminal = true := by native_decide

theorem hostile_globally_unwinnable_config_refused_at_activation :
    check_hostile_globally_unwinnable_config_refused_at_activation = true := by native_decide

theorem raw_identity_fields_must_exactly_match_policy_mission :
    missionIdentityMutationsRefusedB = true := by native_decide

theorem wrong_mission_artifact_is_otherwise_declared_and_outcome_valid :
    check_wrong_mission_artifact_is_otherwise_declared_and_outcome_valid = true := by
  native_decide

theorem artifact_mission_must_exactly_match_activated_mission :
    check_artifact_mission_must_exactly_match_activated_mission = true := by native_decide

theorem hostile_same_role_briefing_substitution_breaks_activation_commitment :
    check_hostile_same_role_briefing_substitution_breaks_activation_commitment = true := by
  native_decide

/-! ## The second sealed world — the rekeyed crew -/

theorem fixture_rekeyed_roster_substitutes_only_the_player_keys :
    check_fixture_rekeyed_roster_substitutes_only_the_player_keys = true := by native_decide

theorem the_fixture_briefing_commitment_does_not_separate_the_two_crews :
    check_the_fixture_briefing_commitment_does_not_separate_the_two_crews = true := by
  native_decide

theorem the_two_fixture_seals_carry_different_sessions :
    check_the_two_fixture_seals_carry_different_sessions = true := by native_decide

theorem exported_fixture_transcripts_are_four_signed_handoffs_each :
    check_exported_fixture_transcripts_are_four_signed_handoffs_each = true := by native_decide

/-! ## The step surface over a real signed transcript -/

theorem the_step_surface_answers_at_every_prefix_replay_refuses :
    stepAnswersEveryPrefixWhileReplayIsSilentB = true := by native_decide

theorem a_crew_plays_a_whole_run_one_signed_handoff_at_a_time :
    stepSurfaceDrivesAWholeSignedRunB = true := by native_decide

theorem the_step_surface_opens_a_briefing_only_to_its_own_seat :
    stepSurfaceRefusesAnotherSeatsAdmissionB = true := by native_decide

/-! ## The seal — satisfiable AND refutable -/

theorem run_seal_admits_the_record_the_kernel_produced :
    sealAdmitsKernelProducedRecordB = true := by native_decide

theorem run_seal_refuses_a_terminal_state_the_kernel_did_not_reach :
    sealRefusesAssertedTerminalRootB = true := by native_decide

theorem run_seal_refuses_a_forged_handoff_signature :
    sealRefusesForgedHandoffSignatureB = true := by native_decide

/-! ## Cooperative play, and what the authored table costs -/

theorem safe_extraction_accepts_two_matching_signed_recommendations :
    check_safe_extraction_accepts_two_matching_signed_recommendations = true := by native_decide

theorem alternative_safe_route_is_reachable :
    check_alternative_safe_route_is_reachable = true := by native_decide

theorem deep_recovery_requires_and_accepts_full_crew_consensus :
    check_deep_recovery_requires_and_accepts_full_crew_consensus = true := by native_decide

theorem route_and_extraction_choices_produce_materially_distinct_records :
    completedPlansDifferB = true := by native_decide

theorem specialist_steps_and_final_route_are_both_charged_exactly :
    completedBudgetAccountingB = true := by native_decide

theorem route_changes_cost_reward_and_artifact_at_fixed_extraction :
    fixedExtractionRouteVariationB = true := by native_decide

theorem all_six_authored_route_extraction_outcomes_are_bounded_and_declared :
    allAuthoredOutcomesWellFormedB = true := by native_decide

theorem combined_field_record_replays_every_signed_handoff_exactly :
    exactReplayB deepPlan = true := by native_decide

theorem unchecked_record_projection_readmits_after_exact_replay :
    readmitB deepPlan = true := by native_decide

/-! ## The hostile transitions -/

theorem recommendation_valid_but_over_budget_route_is_refused_at_live_budget_boundary :
    check_recommendation_valid_but_over_budget_route_is_refused_at_live_budget_boundary = true := by
  native_decide

theorem hostile_mixed_crew_strategy_refused :
    check_hostile_mixed_crew_strategy_refused = true := by native_decide

theorem hostile_deep_recovery_without_unanimity_refused :
    check_hostile_deep_recovery_without_unanimity_refused = true := by native_decide

theorem hostile_private_observation_substitution_refused :
    check_hostile_private_observation_substitution_refused = true := by native_decide

theorem hostile_stale_predecessor_root_refused :
    check_hostile_stale_predecessor_root_refused = true := by native_decide

theorem hostile_handoff_signature_substitution_refused :
    check_hostile_handoff_signature_substitution_refused = true := by native_decide

theorem hostile_full_field_decision_substitution_refused_by_signature :
    check_hostile_full_field_decision_substitution_refused_by_signature = true := by
  native_decide

theorem hostile_signature_issued_for_other_seat_refused :
    check_hostile_signature_issued_for_other_seat_refused = true := by native_decide

theorem hostile_signing_suite_substitution_refused :
    check_hostile_signing_suite_substitution_refused = true := by native_decide

theorem hostile_public_message_digest_submitted_as_signature_refused :
    check_hostile_public_message_digest_submitted_as_signature_refused = true := by
  native_decide

theorem hostile_combined_record_route_substitution_refused :
    tamperedRecordReadmitsB = false := by native_decide

theorem hostile_expanded_record_mutation_matrix_refused :
    expandedRecordMutationsRefusedB = true := by native_decide

#assert_compiled fixture_ordered_briefing_deck_is_commitment_bound
#assert_compiled hostile_unwinnable_terminal_costs_are_individually_within_budget
#assert_compiled hostile_unwinnable_config_has_no_affordable_safe_terminal
#assert_compiled hostile_globally_unwinnable_config_refused_at_activation
#assert_compiled raw_identity_fields_must_exactly_match_policy_mission
#assert_compiled wrong_mission_artifact_is_otherwise_declared_and_outcome_valid
#assert_compiled artifact_mission_must_exactly_match_activated_mission
#assert_compiled hostile_same_role_briefing_substitution_breaks_activation_commitment
#assert_compiled fixture_rekeyed_roster_substitutes_only_the_player_keys
#assert_compiled the_fixture_briefing_commitment_does_not_separate_the_two_crews
#assert_compiled the_two_fixture_seals_carry_different_sessions
#assert_compiled exported_fixture_transcripts_are_four_signed_handoffs_each
#assert_compiled the_step_surface_answers_at_every_prefix_replay_refuses
#assert_compiled a_crew_plays_a_whole_run_one_signed_handoff_at_a_time
#assert_compiled the_step_surface_opens_a_briefing_only_to_its_own_seat
#assert_compiled run_seal_admits_the_record_the_kernel_produced
#assert_compiled run_seal_refuses_a_terminal_state_the_kernel_did_not_reach
#assert_compiled run_seal_refuses_a_forged_handoff_signature
#assert_compiled safe_extraction_accepts_two_matching_signed_recommendations
#assert_compiled alternative_safe_route_is_reachable
#assert_compiled deep_recovery_requires_and_accepts_full_crew_consensus
#assert_compiled route_and_extraction_choices_produce_materially_distinct_records
#assert_compiled specialist_steps_and_final_route_are_both_charged_exactly
#assert_compiled route_changes_cost_reward_and_artifact_at_fixed_extraction
#assert_compiled all_six_authored_route_extraction_outcomes_are_bounded_and_declared
#assert_compiled combined_field_record_replays_every_signed_handoff_exactly
#assert_compiled unchecked_record_projection_readmits_after_exact_replay
#assert_compiled recommendation_valid_but_over_budget_route_is_refused_at_live_budget_boundary
#assert_compiled hostile_mixed_crew_strategy_refused
#assert_compiled hostile_deep_recovery_without_unanimity_refused
#assert_compiled hostile_private_observation_substitution_refused
#assert_compiled hostile_stale_predecessor_root_refused
#assert_compiled hostile_handoff_signature_substitution_refused
#assert_compiled hostile_full_field_decision_substitution_refused_by_signature
#assert_compiled hostile_signature_issued_for_other_seat_refused
#assert_compiled hostile_signing_suite_substitution_refused
#assert_compiled hostile_public_message_digest_submitted_as_signature_refused
#assert_compiled hostile_combined_record_route_substitution_refused
#assert_compiled hostile_expanded_record_mutation_matrix_refused

/-! ## The production ML-DSA-65 signing suite, and the cross-language KAT

These are the pins that run the REAL executable FIPS 204 verify over signatures the Rust
`fips204` crate produced.  They are the expensive half of this module and the reason the
coupling mattered: a stale KAT vector reddened the archive's own build. -/

namespace ProductionSigning
-- The laboratory reads these runtime helpers; they stay private to the runtime module.
open private fixtureBriefingDigest fixtureMessageDigestSuiteId fixtureSignatureSuiteId
   initialState katConfig katSeat0 katSeat0PublicKeyBytes signatureBytesPattern from Dregg2.Games.PathOfAngels.CrewFieldMission

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

private def allRoutes : List Route := [.maintenanceSpine, .signalGallery, .sealedNave]

private def allObservations : List PrivateObservation :=
  (allRoutes.map .pathfinder) ++ (allRoutes.map .engineer) ++
    (allRoutes.map .containment) ++ [.quartermaster .closing, .quartermaster .stable]

private def allCommands : List Command :=
  [.chartPressureRoute, .markSalvageRoute, .braceTransit, .overdriveCargoLift,
    .quietAnomaly, .screenRecovery, .bankSupplies, .secureCache]

private def allDecisions : List Decision :=
  (allRoutes.flatMap fun route => allCommands.map (Decision.specialist route)) ++
    (allRoutes.flatMap fun route => allCommands.flatMap fun command =>
      [Decision.finalize route .returnNow command,
       Decision.finalize route .descendFurther command])

private def codesInjectiveOnB {α : Type} [DecidableEq α]
    (code : α → Nat) (values : List α) : Bool :=
  values.all fun left => values.all fun right =>
    decide (code left = code right → left = right)

/-- `PrivateObservation.code` is injective over the COMPLETE finite observation
space, whose size is asserted in the same statement so the enumeration cannot
silently shrink. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_observation_codes_are_injective : Bool :=
  codesInjectiveOnB PrivateObservation.code allObservations &&
  decide (allObservations.length = 11)

/-- `Decision.code` is injective over the COMPLETE finite decision space, size
asserted in the same statement. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_decision_codes_are_injective : Bool :=
  codesInjectiveOnB Decision.code allDecisions &&
  decide (allDecisions.length = 72)

/-- Two labeled INSTANCES (not a general proof) that the shake output length is
exactly 32 — one empty input, one multi-block input.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_shake_digest_lengths_hold_on_instances : Bool :=
  (shakeDigest32? []).isSome && (shakeDigest32? (List.replicate 500 7)).isSome

/-- Distinct from each other AND from the fixture suite ids.  This is also the
tooth that proves the `labelDigest` fallback arm never fired (a fired fallback
would collapse two of these to the same constant).
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_production_suite_ids_are_distinct_and_not_the_fixture_ids : Bool :=
  decide (briefingSuiteId ≠ messageSuiteId) &&
  decide (briefingSuiteId ≠ signingSuiteId) &&
  decide (messageSuiteId ≠ signingSuiteId) &&
  decide (briefingSuiteId ≠ fixtureBriefingDigest.id) &&
  decide (messageSuiteId ≠ fixtureMessageDigestSuiteId) &&
  decide (signingSuiteId ≠ fixtureSignatureSuiteId)

private def katWrongPublicKeyBytes : List UInt8 :=
  CrewSigningVectors.katWrongPublicKey.toList

/-- Seat 0's player key IS the SHAKE-256 digest of the real ML-DSA-65 public key —
and therefore `katPlayerKey`'s `getD` fallback never fired.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_player_key_is_the_seat0_public_key_digest : Bool :=
  decide (shakeDigest32? katSeat0PublicKeyBytes = some katPlayerKey)

/-- The wrong keypair's digest is NOT seat 0's player key — the premise of the
wrong-key refutation below. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_wrong_public_key_digest_is_not_the_seat_key : Bool :=
  decide (shakeDigest32? katWrongPublicKeyBytes ≠ some katPlayerKey)

private def katState : State := initialState katConfig

private def katSeatBody : SeatAdmissionBody := expectedAdmission katConfig katSeat0

/-- Seat 0's first handoff body at the initial root — the exact thing a player
signs to act. -/
def katHandoffBody : HandoffBody := {
  session := katRawConfig.sessionDigest
  sequence := 0
  preRoot := katState.root
  seat := katSeat0
  previousCounter := katSeat0.initialCounter
  counter := katSeat0.initialCounter + 1
  observation := .pathfinder .signalGallery
  decision := .specialist .signalGallery .chartPressureRoute }

/-- The exact seat-admission message bytes (emitted for the cross-language
generator, and pinned back below once signed). -/
def katSeatMessage : List UInt8 :=
  seatPreimageMessage (katSeatBody.signingPreimage
    katRawConfig.messageDigestSuiteId katRawConfig.signingSuiteId)

/-- The exact handoff message bytes. -/
def katHandoffMessage : List UInt8 :=
  handoffPreimageMessage (katHandoffBody.signingPreimage
    katRawConfig.messageDigestSuiteId katRawConfig.signingSuiteId)

/-- The one public seal producer seals the KAT mission, for the KAT session.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_production_activation_seals_the_kat_mission : Bool :=
  decide ((activate? katRawConfig fixtureBriefings).map RunSeal.session =
    some katRawConfig.sessionDigest)

/-- The producer cannot mint a seal over the fixture suite: the authored
fixture config names the fixture briefing/message/signing suite ids and the
production validator refuses it. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_production_activation_refuses_the_fixture_suite_config : Bool :=
  (activate? fixtureRawConfig fixtureBriefings).isNone

private def envelope? (publicKey signature : Array UInt8) : Option SignatureBytes :=
  let bytes := (publicKey.toList ++ signature.toList).map
    fun b => (⟨b.toNat % 256, Nat.mod_lt _ (by omega)⟩ : Fin 256)
  if h : bytes.length = SIGNATURE_BYTE_LENGTH then some ⟨bytes, h⟩ else none

private def katSeatEnvelope : SignatureBytes :=
  (envelope? CrewSigningVectors.katSeat0PublicKey
    CrewSigningVectors.katSeatSignature).getD (signatureBytesPattern 0)

private def katHandoffEnvelope : SignatureBytes :=
  (envelope? CrewSigningVectors.katSeat0PublicKey
    CrewSigningVectors.katHandoffSignature).getD (signatureBytesPattern 0)

private def katWrongKeyEnvelope : SignatureBytes :=
  (envelope? CrewSigningVectors.katWrongPublicKey
    CrewSigningVectors.katWrongKeyHandoffSignature).getD (signatureBytesPattern 0)

/-- The pinned vectors really are envelope-sized — and therefore none of the
`getD` fallbacks above fired. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_envelopes_are_exact : Bool :=
  decide (envelope? CrewSigningVectors.katSeat0PublicKey
    CrewSigningVectors.katSeatSignature = some katSeatEnvelope) &&
  decide (envelope? CrewSigningVectors.katSeat0PublicKey
    CrewSigningVectors.katHandoffSignature = some katHandoffEnvelope) &&
  decide (envelope? CrewSigningVectors.katWrongPublicKey
    CrewSigningVectors.katWrongKeyHandoffSignature = some katWrongKeyEnvelope)

/-- The messages the Rust side signed are byte-identical to what the Lean
encoder emits TODAY.  If the encoder ever drifts, this goes red separately
from the verify pins, so encoder drift and verifier drift are distinguishable
at a glance. (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_messages_are_the_pinned_bytes : Bool :=
  decide (katSeatMessage = CrewSigningVectors.katSeatMessagePinned.toList) &&
  decide (katHandoffMessage = CrewSigningVectors.katHandoffMessagePinned.toList)

/-- ⚑ THE KEYSTONE, seat half: the honest seat-admission signature verifies
through the REAL executable FIPS 204 verify, over the production preimage
bytes, under the production suite — cross-language.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_seat_admission_signature_verifies_cross_language : Bool :=
  seatSignatureValidB katConfig katSeat0 katSeatBody ⟨katSeatEnvelope⟩

/-- ⚑ THE KEYSTONE, handoff half: the honest handoff signature verifies.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_handoff_signature_verifies_cross_language : Bool :=
  handoffSignatureValidB katConfig katSeat0 katHandoffBody ⟨katHandoffEnvelope⟩

/-- One seat's signed handoff, end to end through the kernel: the ML-DSA-65
seat admission mints the capability (`authenticateSeat?`), the briefing opens,
and `execute` ACCEPTS the ML-DSA-65-signed handoff and advances the mission to
sequence 1 (not yet complete — three seats remain).  This is the smallest real
crew action, judged by the kernel under real cryptography.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`kat_one_seats_signed_handoff_is_executed_by_the_kernel`.) -/
def katFirstHandoffExecutesB : Bool :=
  match authenticateSeat? katConfig ⟨0⟩ ⟨katSeatEnvelope⟩ with
  | none => false
  | some capability =>
    match briefingFor? katConfig capability with
    | none => false
    | some briefing =>
      match execute katConfig katState ⟨capability, briefing, katHandoffBody,
          ⟨katHandoffEnvelope⟩⟩ with
      | .error _ => false
      | .ok result =>
          decide (result.state.snapshot.sequence = 1) &&
          decide (result.completion = none)

/-- Refutation: one flipped byte in the ML-DSA signature half of the envelope,
asserted a real mutation, refused by `verifyCore`. -/
private def katTamperedEnvelope : SignatureBytes :=
  { katHandoffEnvelope with
    bytes := katHandoffEnvelope.bytes.set (MLDSA65_PUBLIC_KEY_BYTE_LENGTH + 100)
      ((katHandoffEnvelope.bytes.getD (MLDSA65_PUBLIC_KEY_BYTE_LENGTH + 100) 0) + 1)
    length_eq := by rw [List.length_set]; exact katHandoffEnvelope.length_eq }

/-- The mutation is asserted present before the refusal is read.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_tampered_signature_byte_is_refused : Bool :=
  decide (katTamperedEnvelope.bytes ≠ katHandoffEnvelope.bytes) &&
  !(handoffSignatureValidB katConfig katSeat0 katHandoffBody ⟨katTamperedEnvelope⟩)

/-- ⚑ Refutation with a GENUINE signature: the wrong-key envelope carries a
signature that `verifyCore` itself ACCEPTS under its own public key (first
conjunct — the signature is not broken), and the crew verifier still refuses
it for seat 0 (second conjunct).  Together with
`kat_wrong_public_key_digest_is_not_the_seat_key`, the refusal is the
two-source `SHAKE256(pk) = playerKey` pin doing its work — the case a
self-pinned verifier could never catch.
(Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_wrong_key_signature_is_genuine_but_refused_by_the_key_pin : Bool :=
  Dregg2.Crypto.MlDsaVerifyReal.verifyCore katWrongPublicKeyBytes katHandoffMessage
    HANDOFF_SIGNING_CONTEXT.toUTF8.toList
    CrewSigningVectors.katWrongKeyHandoffSignature.toList &&
  !(handoffSignatureValidB katConfig katSeat0 katHandoffBody ⟨katWrongKeyEnvelope⟩)

/-- Refutation: the honest signature does not transfer to a different body —
one counter increment, asserted different, refused. -/
private def katTamperedBody : HandoffBody :=
  { katHandoffBody with counter := katHandoffBody.counter + 1 }

/-- (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_signature_does_not_transfer_to_a_different_body : Bool :=
  decide (katTamperedBody ≠ katHandoffBody) &&
  !(handoffSignatureValidB katConfig katSeat0 katTamperedBody ⟨katHandoffEnvelope⟩)

/-- Refutation: signature-level domain separation — the genuine SEAT-admission
envelope is refused as a HANDOFF signature (distinct FIPS 204 `ctx`, distinct
preimage format). (Pinned `= true` in `CrewFieldMissionFixtures`.) -/
def check_kat_seat_admission_envelope_is_refused_as_a_handoff : Bool :=
  !(handoffSignatureValidB katConfig katSeat0 katHandoffBody ⟨katSeatEnvelope⟩)

private def katRunSeal? : Option RunSeal := activate? katRawConfig fixtureBriefings

/-- ⚑ THE COMPLETABLE HANDOFF, END TO END.  Seat 0 presents the ML-DSA-65
admission envelope the `fips204` crate produced; the surface returns the
preimage; its message bytes are EXACTLY the bytes that crate signed
(`katHandoffMessagePinned`, independently pinned as
`kat_messages_are_the_pinned_bytes`); the signature over those bytes verifies
through the real FIPS 204 verify; and the kernel executes the resulting handoff
to sequence 1.

That is the whole loop a live seat performs, with nothing computed twice: the
client never derives `preRoot`, never assembles a body, and never re-encodes a
preimage — it signs the bytes it was handed.  A drift in the encoder, the
transition, or the surface breaks it here.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`kat_step_surface_hands_back_exactly_the_bytes_the_crate_signed`.) -/
def katStepSurfaceHandsBackTheSignedBytesB : Bool :=
  match katRunSeal? with
  | none => false
  | some katSeal =>
    match katSeal.nextSigningPreimage? [] ⟨katSeatEnvelope⟩
        (.specialist .signalGallery .chartPressureRoute) with
    | none => false
    | some preimage =>
        decide (handoffPreimageMessage preimage =
          CrewSigningVectors.katHandoffMessagePinned.toList) &&
        decide (preimage.body = katHandoffBody) &&
        handoffSignatureValidB katConfig katSeat0 preimage.body ⟨katHandoffEnvelope⟩ &&
        (match authenticateSeat? katConfig ⟨0⟩ ⟨katSeatEnvelope⟩ with
         | none => false
         | some capability =>
           match briefingFor? katConfig capability with
           | none => false
           | some briefing =>
             match execute katConfig katState
                 ⟨capability, briefing, preimage.body, ⟨katHandoffEnvelope⟩⟩ with
             | .error _ => false
             | .ok result => decide (result.state.snapshot.sequence = 1))

/-- The production surface refuses a caller who is not the seat: the wrong
keypair's envelope is a GENUINE ML-DSA-65 seat signature (it verifies under its
own key) and it still opens nothing, because `authenticateSeat?` runs the same
`SHAKE256(pk) = playerKey` pin.  Control in the same statement: seat 0's own
envelope does open it.
(Pinned `= true` in `CrewFieldMissionFixtures`, under the theorem name
`kat_step_surface_refuses_a_genuine_signature_under_the_wrong_key`.) -/
def katStepSurfaceRefusesAWrongKeyEnvelopeB : Bool :=
  match katRunSeal? with
  | none => false
  | some katSeal =>
    let decision : Decision := .specialist .signalGallery .chartPressureRoute
    (katSeal.nextSigningPreimage? [] ⟨katWrongKeyEnvelope⟩ decision).isNone &&
    (katSeal.nextSigningPreimage? [] ⟨katSeatEnvelope⟩ decision).isSome

theorem observation_codes_are_injective :
    check_observation_codes_are_injective = true := by native_decide

theorem decision_codes_are_injective :
    check_decision_codes_are_injective = true := by native_decide

theorem shake_digest_lengths_hold_on_instances :
    check_shake_digest_lengths_hold_on_instances = true := by native_decide

theorem production_suite_ids_are_distinct_and_not_the_fixture_ids :
    check_production_suite_ids_are_distinct_and_not_the_fixture_ids = true := by native_decide

theorem kat_player_key_is_the_seat0_public_key_digest :
    check_kat_player_key_is_the_seat0_public_key_digest = true := by native_decide

theorem kat_wrong_public_key_digest_is_not_the_seat_key :
    check_kat_wrong_public_key_digest_is_not_the_seat_key = true := by native_decide

theorem production_activation_seals_the_kat_mission :
    check_production_activation_seals_the_kat_mission = true := by native_decide

theorem production_activation_refuses_the_fixture_suite_config :
    check_production_activation_refuses_the_fixture_suite_config = true := by native_decide

theorem kat_envelopes_are_exact :
    check_kat_envelopes_are_exact = true := by native_decide

theorem kat_messages_are_the_pinned_bytes :
    check_kat_messages_are_the_pinned_bytes = true := by native_decide

theorem kat_seat_admission_signature_verifies_cross_language :
    check_kat_seat_admission_signature_verifies_cross_language = true := by native_decide

theorem kat_handoff_signature_verifies_cross_language :
    check_kat_handoff_signature_verifies_cross_language = true := by native_decide

theorem kat_one_seats_signed_handoff_is_executed_by_the_kernel :
    katFirstHandoffExecutesB = true := by native_decide

theorem kat_tampered_signature_byte_is_refused :
    check_kat_tampered_signature_byte_is_refused = true := by native_decide

theorem kat_wrong_key_signature_is_genuine_but_refused_by_the_key_pin :
    check_kat_wrong_key_signature_is_genuine_but_refused_by_the_key_pin = true := by
  native_decide

theorem kat_signature_does_not_transfer_to_a_different_body :
    check_kat_signature_does_not_transfer_to_a_different_body = true := by native_decide

theorem kat_seat_admission_envelope_is_refused_as_a_handoff :
    check_kat_seat_admission_envelope_is_refused_as_a_handoff = true := by native_decide

theorem kat_step_surface_hands_back_exactly_the_bytes_the_crate_signed :
    katStepSurfaceHandsBackTheSignedBytesB = true := by native_decide

theorem kat_step_surface_refuses_a_genuine_signature_under_the_wrong_key :
    katStepSurfaceRefusesAWrongKeyEnvelopeB = true := by native_decide

#assert_compiled observation_codes_are_injective
#assert_compiled decision_codes_are_injective
#assert_compiled shake_digest_lengths_hold_on_instances
#assert_compiled production_suite_ids_are_distinct_and_not_the_fixture_ids
#assert_compiled kat_player_key_is_the_seat0_public_key_digest
#assert_compiled kat_wrong_public_key_digest_is_not_the_seat_key
#assert_compiled production_activation_seals_the_kat_mission
#assert_compiled production_activation_refuses_the_fixture_suite_config
#assert_compiled kat_envelopes_are_exact
#assert_compiled kat_messages_are_the_pinned_bytes
#assert_compiled kat_seat_admission_signature_verifies_cross_language
#assert_compiled kat_handoff_signature_verifies_cross_language
#assert_compiled kat_one_seats_signed_handoff_is_executed_by_the_kernel
#assert_compiled kat_tampered_signature_byte_is_refused
#assert_compiled kat_wrong_key_signature_is_genuine_but_refused_by_the_key_pin
#assert_compiled kat_signature_does_not_transfer_to_a_different_body
#assert_compiled kat_seat_admission_envelope_is_refused_as_a_handoff
#assert_compiled kat_step_surface_hands_back_exactly_the_bytes_the_crate_signed
#assert_compiled kat_step_surface_refuses_a_genuine_signature_under_the_wrong_key

end ProductionSigning

end Dregg2.Games.PathOfAngels.CrewFieldMission
