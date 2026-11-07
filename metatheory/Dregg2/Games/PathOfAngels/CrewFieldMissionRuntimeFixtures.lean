/-
# Crew field mission runtime — the activation laboratory, out of the crypto archive

`CrewFieldMissionRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root). Its executable activation laboratory — the fixture world, every hostile case, every
`check_*` statement and the twenty-five `native_decide` pins over them — lives HERE, rooted in
the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down;
  * and nothing here is linked into the node. Lean computes every compiled no-argument `def`
    when its module initializes, so while the 08-08 split left the `check_*` definitions and
    their fixtures in the runtime module, three of them (`fixtureSafeResult`,
    `fixtureDeepResult`, `check_callable_entrypoint_emits_the_exact_successful_receipt`, each a
    full `judge` run) cost ~117 s of every node start on hbox (#86, 2026-10-01).

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The construction proofs `fixture_activation_valid` and
`rekeyed_crew_activation_is_valid` moved with the activations they build.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime
import Batteries.Tactic.OpenPrivate

namespace Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition
-- The laboratory re-encodes the kernel's own transcripts with the runtime's wire encoders, which
-- stay private to it (`CrewFieldMissionRuntimeBoundary.wire_encoder_is_private`).
open private TraceWire.ofSemantic decisionToWire from Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime

set_option autoImplicit false

/-! ## The executable activation laboratory

The fixture world (`fixtureActivation`, `fixtureGenesis`, `fixtureSafeCommand`, the rekeyed
crew), every hostile case and every `check_*` statement live HERE, in a module `Dregg2.FFI`
does not reach. Lean computes every compiled no-argument `def` at module initialization, so a
fixture in the runtime module is a `judge` run on every node boot (#86); here it runs only where
it is pinned. The construction proofs `fixture_activation_valid` and
`rekeyed_crew_activation_is_valid` are here too, because the activations they build are. -/

private def fixtureDigest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureContentOfficers : List ContentContract.OfficerSeat :=
  [ ⟨⟨0⟩, ⟨10⟩, .pathfinder⟩
  , ⟨⟨1⟩, ⟨11⟩, .engineer⟩
  , ⟨⟨2⟩, ⟨12⟩, .containment⟩
  , ⟨⟨3⟩, ⟨13⟩, .quartermaster⟩ ]

private def fixtureContentBriefings : List ContentContract.BriefingShape :=
  [ ⟨.pathfinder, .mappedRoute, some ⟨1⟩, .privateUntilSignedHandoff⟩
  , ⟨.engineer, .structurallySoundRoute, some ⟨1⟩, .privateUntilSignedHandoff⟩
  , ⟨.containment, .hazardClearRoute, some ⟨1⟩, .privateUntilSignedHandoff⟩
  , ⟨.quartermaster, .extractionWindow, none, .privateUntilSignedHandoff⟩ ]

private def fixtureContentArtifacts : List ContentContract.ArtifactSpec :=
  [ ⟨⟨20⟩, none⟩, ⟨⟨21⟩, none⟩, ⟨⟨22⟩, none⟩ ]

private def fixtureContentEncounters : List ContentContract.EncounterSpec :=
  [ { id := ⟨10⟩, room := DeckGraph.fixtureRoomB.id,
      routes := [⟨0⟩, ⟨1⟩, ⟨2⟩], betaArtifacts := [⟨20⟩] }
  , { id := ⟨11⟩, room := DeckGraph.fixtureRoomC.id,
      routes := [⟨0⟩], betaArtifacts := [⟨20⟩] }
  , { id := ⟨12⟩, room := DeckGraph.fixtureRoomD.id,
      routes := [⟨1⟩], betaArtifacts := [⟨21⟩] }
  , { id := ⟨13⟩, room := DeckGraph.fixtureExtraction.id,
      routes := [⟨2⟩], betaArtifacts := [⟨22⟩] } ]

private def contentRoute : CrewFieldMission.Route → ContentContract.RouteId
  | .maintenanceSpine => ⟨0⟩
  | .signalGallery => ⟨1⟩
  | .sealedNave => ⟨2⟩

private def contentArtifact : CrewFieldMission.Route → ContentContract.ArtifactId
  | .maintenanceSpine => ⟨20⟩
  | .signalGallery => ⟨21⟩
  | .sealedNave => ⟨22⟩

private def contentRelics (relics : List RelicId) : List ContentContract.RelicId :=
  relics.map fun relic => ⟨relic.value⟩

private def fixtureContentOutcomes : List ContentContract.RouteOutcome :=
  CrewFieldMission.fixtureRouteOutcomes.map fun spec => {
    route := contentRoute spec.route
    extraction := toContentExtraction spec.extraction
    operationalCost := spec.operationalCost
    agreement := ContentContract.requiredAgreement (toContentExtraction spec.extraction)
    featuredArtifact := contentArtifact spec.route
    contribution := {
      intel := spec.outcome.contribution.intel
      supplies := spec.outcome.contribution.supplies
      cohesion := spec.outcome.contribution.cohesion
      influence := spec.outcome.contribution.influence
      score := spec.outcome.contribution.score
      relics := contentRelics spec.outcome.contribution.relics
    }
    recovery := if spec.extraction = .returnNow then ⟨40⟩ else ⟨41⟩
  }

private def fixtureRuntimeContent : ContentContract.RawContent := {
  ContentContract.fixtureContent with
  officers := fixtureContentOfficers
  briefings := fixtureContentBriefings
  encounters := fixtureContentEncounters
  artifacts := fixtureContentArtifacts
  outcomes := fixtureContentOutcomes
  relics := [⟨⟨447⟩, ⟨12⟩, true, false, none⟩]
  custodyPlans := [⟨⟨447⟩, .atEncounter ⟨12⟩, .quarantine,
    .fullCrewUnanimity, false⟩]
  promotionHooks :=
    [ ⟨.place ⟨50⟩, none⟩
    , ⟨.artifact ⟨20⟩, none⟩
    , ⟨.relic ⟨447⟩, none⟩ ]
  contributionBudget := {
    intel := 8, supplies := 4, cohesion := 6, influence := 0, score := 79,
    relicAllowlist := [⟨447⟩]
  }
}

/-- The fixture runtime content passes the content contract.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`fixture_runtime_content_valid`.  Public because the pin now lives in a sibling module;
nothing else reads it.) -/
def check_fixture_runtime_content_valid : Bool :=
  ContentContract.contentValidB fixtureRuntimeContent

private def fixtureRawActivation : RawActivation where
  activationId := CrewFieldMission.fixtureRawConfig.policy.mission.activationDigest
  rosterBinding := rosterBindingOf CrewFieldMission.fixtureRawConfig.roster
  contentDigest := CrewFieldMission.fixtureRawConfig.policy.mission.contentRoot
  fieldSession := CrewFieldMission.fixtureRawConfig.sessionDigest
  briefings := CrewFieldMission.fixtureBriefings
  content := fixtureRuntimeContent
  routeBindings :=
    [ ⟨.maintenanceSpine, ⟨0⟩⟩
    , ⟨.signalGallery, ⟨1⟩⟩
    , ⟨.sealedNave, ⟨2⟩⟩ ]
  artifactBindings :=
    [ ⟨CrewFieldMission.fixtureMaintenanceArtifact, ⟨20⟩⟩
    , ⟨CrewFieldMission.fixtureSignalArtifact, ⟨21⟩⟩
    , ⟨CrewFieldMission.fixtureNaveArtifact, ⟨22⟩⟩ ]
  relicBindings := [⟨DeckExpedition.fixtureRelic, ⟨447⟩⟩]
  ordinarySalvage :=
    [ ⟨.maintenanceSpine, .returnNow, ⟨900⟩, 2⟩
    , ⟨.signalGallery, .descendFurther, ⟨901⟩, 1⟩ ]
  replayVerifierId := fixtureDigest 222

private theorem fixture_activation_valid : activationValidB fixtureRawActivation = true := by
  native_decide

/-! ### The sealed fixture activation

⚑ 2026-08-06.  What stood here was a `ReplayAuthority` whose `verify` was

    decide (record.session = fixtureRawActivation.fieldSession) &&
    decide (record.transcript.length = CrewFieldMission.CREW_SIZE)

— a session comparison and a length check, standing in for the module's
"cryptographic trust boundary".  It verified no signature and replayed nothing,
and every `native_decide` result below was evidence about THAT.  The transcripts
it judged carried `fixtureSignature` in both signature fields: one constant byte
pattern, identical for all four seats.

The activation now holds `CrewFieldMission.fixtureRunSeal`, and the transcripts
are the ones the kernel itself signed, re-encoded to the wire.  `sealSessionExact`
holds by `rfl` because the seal's config and this activation's `fieldSession` are
both `CrewFieldMission.fixtureRawConfig.sessionDigest` — two spellings the
elaborator has to agree on, not a value copied from one to the other.

`Activation`'s constructor is private to the runtime module, so the laboratory builds its
activation the way every caller must: through `activate?`, which re-checks validity AND the seal
session. Admission is proved from `fixture_activation_valid` and the seal session's `rfl`, so
the laboratory rests on no oracle the old in-module construction did not. -/
private theorem fixture_activation_admitted :
    (activate? fixtureRawActivation CrewFieldMission.fixtureRunSeal).isSome = true := by
  rw [activate?, dif_pos fixture_activation_valid,
    dif_pos (show CrewFieldMission.fixtureRunSeal.session = fixtureRawActivation.fieldSession
      from rfl)]
  rfl

private def fixtureActivation : Activation :=
  (activate? fixtureRawActivation CrewFieldMission.fixtureRunSeal).get
    fixture_activation_admitted

private def fixtureSafeTranscript : List TraceWire :=
  CrewFieldMission.fixtureSafeMaintenanceTranscript.map TraceWire.ofSemantic

private def fixtureDeepTranscript : List TraceWire :=
  CrewFieldMission.fixtureDeepTranscript.map TraceWire.ofSemantic

/-- The wire encoder is a genuine inverse on the transcripts the kernel signed:
decoding the encoding returns the kernel's own traces.  Without this the
fixtures below could be exercising a transcript the runtime silently reinterprets.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_fixture_wire_transcripts_decode_back_to_the_kernel_traces : Bool :=
  decide (fixtureSafeTranscript.mapM (TraceWire.toSemantic? fixtureActivation) =
    some CrewFieldMission.fixtureSafeMaintenanceTranscript) &&
  decide (fixtureDeepTranscript.mapM (TraceWire.toSemantic? fixtureActivation) =
    some CrewFieldMission.fixtureDeepTranscript)

private def fixtureGenesis : StateWire := initialState fixtureActivation (fixtureDigest 223)

private def fixtureSafeCommand : CommandWire where
  activationId := fixtureRawActivation.activationId
  sequence := 0
  predecessor := fixtureGenesis.head
  admission := 1
  actor := CrewRelayExpedition.fixtureSeat0.playerKey
  officerSeat := 0
  claimedRoute := "maintenance-spine"
  claimedExtraction := "return-now"
  claimedContribution := ContributionWire.ofRaw
    (CrewFieldMission.fixtureOutcome .maintenanceSpine .returnNow).contribution
  claimedFeaturedArtifact := 20
  transcript := fixtureSafeTranscript

private def fixtureDeepCommand : CommandWire := {
  fixtureSafeCommand with
  claimedRoute := "signal-gallery"
  claimedExtraction := "descend-further"
  claimedContribution := ContributionWire.ofRaw
    (CrewFieldMission.fixtureOutcome .signalGallery .descendFurther).contribution
  claimedFeaturedArtifact := 21
  transcript := fixtureDeepTranscript
}

private def fixtureSafeResult : Except Refusal OutputWire :=
  judge fixtureActivation fixtureGenesis fixtureSafeCommand

private def fixtureDeepResult : Except Refusal OutputWire :=
  judge fixtureActivation fixtureGenesis fixtureDeepCommand

/-- The honest complete run emits exactly one ordinary salvage authorization and no
relic custody. (Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem
name `honest_complete_run_emits_one_ordinary_salvage_authorization`.) -/
def honestOrdinarySalvageB : Bool :=
  match fixtureSafeResult with
  | .error _ => false
  | .ok output => decide (
      output.receipt.ordinaryMints =
        [⟨⟨900⟩, 2, CrewRelayExpedition.fixtureSeat0.playerKey, true⟩] ∧
      output.receipt.relicCustody = [])

/-- The deep run separates exchangeable parts from non-market relic custody.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`deep_run_separates_exchangeable_parts_from_nonmarket_relic_custody`.) -/
def deepTaxonomyB : Bool :=
  match fixtureDeepResult with
  | .error _ => false
  | .ok output => decide (
      output.receipt.ordinaryMints =
        [⟨⟨901⟩, 1, CrewRelayExpedition.fixtureSeat0.playerKey, true⟩] ∧
      output.receipt.relicCustody =
        [⟨⟨447⟩, .quarantine, false, false⟩])

/-- The same admission and run cannot be replayed: the cursor is stale.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`hostile_same_admission_and_run_cannot_replay`.) -/
def replayRefusedB : Bool :=
  match fixtureSafeResult with
  | .error _ => false
  | .ok first => decide (judge fixtureActivation first.state fixtureSafeCommand =
      .error .staleCursor)

/-- A command carrying another activation's id is refused as `.wrongActivation`.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_cross_activation_command_refused : Bool :=
  decide (judge fixtureActivation fixtureGenesis
    { fixtureSafeCommand with activationId := fixtureDigest 250 } = .error .wrongActivation)

/-- A claimed route the signed transcript did not reach is refused.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_forged_route_refused : Bool :=
  decide (judge fixtureActivation fixtureGenesis
    { fixtureSafeCommand with claimedRoute := "sealed-nave" } = .error .invalidTranscript)

/-- A claimed outcome the signed transcript did not produce is refused.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_forged_outcome_refused : Bool :=
  decide (judge fixtureActivation fixtureGenesis
    { fixtureSafeCommand with claimedContribution :=
        { fixtureSafeCommand.claimedContribution with score := 999 } } =
      .error .invalidTranscript)

/-- An actor who is not the selected officer is refused.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_actor_who_is_not_the_selected_officer_refused : Bool :=
  decide (judge fixtureActivation fixtureGenesis
    { fixtureSafeCommand with actor := CrewRelayExpedition.fixtureSeat1.playerKey } =
      .error .unauthorizedOfficer)

/-- ⚑ The refusal MOVED, and that is the weld showing.  This used to be
`.invalidTranscript` — this module's own `traces.length = CREW_SIZE` check.  It
is now `.replayRefused`: three signed handoffs replay fine, the run simply never
reaches `.extracted`, so the kernel has no completed record to give back.  The
truncation is refused by the state machine rather than by a length comparison.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_truncated_crew_transcript_refused : Bool :=
  decide (judge fixtureActivation fixtureGenesis
    { fixtureSafeCommand with transcript := fixtureSafeTranscript.take 3 } =
      .error .replayRefused)

private def forgedSignatureBytes : CrewFieldMission.SignatureBytes where
  bytes := List.replicate CrewFieldMission.SIGNATURE_BYTE_LENGTH 7
  length_eq := by simp [CrewFieldMission.SIGNATURE_BYTE_LENGTH]

/-- ⚑ THE WELD, SHOWN.  This is the case the old code got wrong: substituting a
handoff signature changes neither the session nor the transcript length, so the
`ReplayAuthority` that stood here — `session = … && length = CREW_SIZE` — ACCEPTED
it, and `deriveRecord?` had already asserted the terminal state it was asked
about.  A forged run was admitted and would have minted salvage.

The kernel refuses it, because `replay?` rebuilds each `SignedHandoff` from the
trace and the signature has to verify.

The forgery is constructed from the live fixture trace and asserted DIFFERENT
before the verdict is read: if a fixture re-emit ever makes the mutation a
no-op, this goes red instead of quietly comparing a value with itself.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`hostile_forged_handoff_signature_refused_by_the_kernel`.) -/
def forgedHandoffSignatureRefusedB : Bool :=
  match fixtureSafeTranscript with
  | [] => false
  | wire :: rest =>
      let forged : TraceWire := { wire with handoffSignature := forgedSignatureBytes }
      decide (forged.handoffSignature ≠ wire.handoffSignature) &&
      decide (judge fixtureActivation fixtureGenesis
        { fixtureSafeCommand with transcript := forged :: rest } = .error .replayRefused)

/-- ⚑ Replaces `hostile_wrong_replay_authority_id_refused`, which checked that
`activate?` refused a `ReplayAuthority` whose `id` disagreed with the
activation's own `replayVerifierId` — two fields the same caller supplied.  This
is the check that has teeth: a seal minted for a DIFFERENT session cannot be
attached to this activation, and the two sessions are proved distinct in the
kernel (`the_two_fixture_seals_carry_different_sessions`).
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_seal_for_another_session_cannot_activate : Bool :=
  (activate? fixtureRawActivation CrewFieldMission.fixtureRekeyedRunSeal).isNone

private def hostileMarketContent : ContentContract.RawContent := {
  fixtureRuntimeContent with
  relics := [{ (fixtureRuntimeContent.relics.getD 0
    ⟨⟨447⟩, ⟨12⟩, true, false, none⟩) with marketEligible := true }]
}

private def hostileTradeContent : ContentContract.RawContent := {
  fixtureRuntimeContent with
  custodyPlans := [{ (fixtureRuntimeContent.custodyPlans.getD 0
    ⟨⟨447⟩, .atEncounter ⟨12⟩, .quarantine, .fullCrewUnanimity, false⟩) with
      directTradeAllowed := true }]
}

/-- A canon relic made market-eligible cannot be activated.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_canon_relic_market_activation_refused : Bool :=
  (activate? { fixtureRawActivation with content := hostileMarketContent }
    CrewFieldMission.fixtureRunSeal).isNone

/-- A canon relic with direct trade allowed cannot be activated.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_canon_relic_direct_trade_activation_refused : Bool :=
  (activate? { fixtureRawActivation with content := hostileTradeContent }
    CrewFieldMission.fixtureRunSeal).isNone

private def callerAuthoredMintBytes : String :=
  (fixtureSafeCommand.toJson.dropEnd 1).toString ++
    ",\"ordinary_mints\":[{\"part\":999,\"quantity\":64}]}"

/-- A caller who appends an `ordinary_mints` field is refused by the strict codec —
salvage is authorized by the judge, never claimed on the wire.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_caller_authored_salvage_field_refused_by_strict_codec : Bool :=
  (decodeCommand callerAuthoredMintBytes).isNone

/-- (Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`strict_command_roundtrip`.) -/
def check_strict_command_roundtrip : Bool :=
  decide (decodeCommand fixtureSafeCommand.toJson = some fixtureSafeCommand)

/-- (Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`strict_state_roundtrip`.) -/
def check_strict_state_roundtrip : Bool :=
  decide (decodeState fixtureGenesis.toJson = some fixtureGenesis)

/-! ### The step ABI, over the transcript the kernel signed

Every seat-admission envelope used below comes out of
`CrewFieldMission.fixtureDeepTranscript` — the kernel's own signed data — so
these are not requests the runtime authored for itself. -/

private def fixtureStepRequest? (k : Nat) : Option StepRequestWire := do
  let trace ← CrewFieldMission.fixtureDeepTranscript[k]?
  let (decision, decidedRoute, extraction, command) := decisionToWire trace.decision
  some {
    activationId := fixtureRawActivation.activationId
    rosterBinding := fixtureRawActivation.rosterBinding
    transcript := (CrewFieldMission.fixtureDeepTranscript.take k).map TraceWire.ofSemantic
    seatSignature := trace.seatSignature.bytes
    decision
    decidedRoute
    extraction
    command }

/-- The signing message the kernel's own step view yields for handoff `k`,
reached by the OTHER public route (`step?` then `StepView.nextBody?`) so the
assertion below is not the ABI agreeing with itself. -/
private def expectedStepSigningMessage? (k : Nat) : Option String := do
  let trace ← CrewFieldMission.fixtureDeepTranscript[k]?
  let view ← CrewFieldMission.fixtureRunSeal.step?
    (CrewFieldMission.fixtureDeepTranscript.take k)
  let body ← view.nextBody? trace.observation trace.decision
  some (CrewFieldMission.ProductionSigning.handoffPreimageJson
    (body.signingPreimage fixtureRawActivation.fieldSession.messageDigestSuiteId
      fixtureRawActivation.fieldSession.signingSuiteId))

/-- ⚑ The read a live crew needs: at every one of the four prefixes the
settlement ABI cannot parse, the step ABI answers, and the cursor it reports —
seat, previous counter, counter — is the one the kernel's own signed trace for
that handoff used.  The `signing_message` it carries is byte-identical to the
preimage the kernel's step view yields by the independent `nextBody?` route.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`the_step_abi_reports_the_cursor_the_signed_transcript_used`.) -/
def stepAbiAnswersEveryPrefixB : Bool :=
  (List.range CrewFieldMission.CREW_SIZE).all fun k =>
    match fixtureStepRequest? k, CrewFieldMission.fixtureDeepTranscript[k]?,
        expectedStepSigningMessage? k with
    | some request, some trace, some message =>
        decide (decodeStepRequest request.toJson = some request) &&
        (match stepJudge fixtureActivation request with
         | .error _ => false
         | .ok response =>
             decide (response.activationId = fixtureRawActivation.activationId) &&
             decide (response.rosterBinding = fixtureRawActivation.rosterBinding) &&
             decide (response.sequence = k) &&
             decide (response.complete = false) &&
             decide (response.nextPresent = true) &&
             decide (response.nextSeat = trace.seat.id.value) &&
             decide (response.nextPreviousCounter = trace.previousCounter) &&
             decide (response.nextCounter = trace.counter) &&
             decide (response.signingMessage = message) &&
             decide (stepProcess fixtureActivation request.toJson = some response.toJson))
    | _, _, _ => false

/-- Four refusals, each with its mutation asserted present in the same
statement, and the honest control that the unmutated request is accepted.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`the_step_abi_refuses_a_wrong_crew_a_wrong_seat_and_an_overlong_prefix`.) -/
def stepAbiRefusalsB : Bool :=
  match fixtureStepRequest? 0, fixtureStepRequest? 1 with
  | some request, some second =>
      -- the crew half of the durable key: same activation, wrong roster.
      decide ({ request with rosterBinding := fixtureDigest 199 } ≠ request) &&
      decide (stepProcess fixtureActivation
        { request with rosterBinding := fixtureDigest 199 }.toJson = none) &&
      decide (stepProcess fixtureActivation
        { request with activationId := fixtureDigest 198 }.toJson = none) &&
      -- another seat's admission envelope does not open seat 0's briefing.
      decide (second.seatSignature ≠ request.seatSignature) &&
      decide (stepProcess fixtureActivation
        { request with seatSignature := second.seatSignature }.toJson = none) &&
      -- the prefix bound is a bound: five handoffs is not a prefix of four.
      decide (stepProcess fixtureActivation
        { request with transcript := fixtureDeepTranscript ++ fixtureDeepTranscript.take 1 }.toJson
          = none) &&
      -- and the honest control, so the four refusals above are not vacuous.
      decide ((stepProcess fixtureActivation request.toJson).isSome = true)
  | _, _ => false

/-! ### The two-crews-one-key collision, and the binding that closes it

`activationId` is pinned only against `fieldSession.policy.mission.activationDigest`
— a field of the same caller-supplied record — and `MissionSpec` carries no
roster.  The seating that `judge` authorizes against therefore sat outside the
activation's identity entirely.  The fixtures below substitute the four wallet
keys and change nothing else.

⚑ 2026-08-06.  The substituted crew now comes from `CrewFieldMission`'s second
SEALED world rather than from a roster swapped in here.  It has to: since the
weld an `Activation` carries a `RunSeal`, and a seal can be minted only by the
kernel, because it holds a `Config` whose constructor is private.  The roster
substitution itself is unchanged — `CrewFieldMission.fixtureRekeyedRoster` is
the same four keys this file used to build inline, and
`fixture_rekeyed_roster_substitutes_only_the_player_keys` says so next to the
world it describes. -/

private def rekeyedRoster : List Seat := CrewFieldMission.fixtureRekeyedRoster

private def rekeyedSession : CrewFieldMission.SessionDigest :=
  CrewFieldMission.fixtureRekeyedRawConfig.sessionDigest

private def rekeyedRawActivation : RawActivation :=
  { fixtureRawActivation with
    fieldSession := rekeyedSession
    rosterBinding := rosterBindingOf rekeyedRoster }

/-- Guard against a falsifier that has stopped falsifying: the substitution must
really have happened, and must have moved *only* the player keys.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`rekeyed_crew_is_a_real_substitution_of_the_player_keys_alone`.) -/
def rekeySubstitutionRealB : Bool :=
  decide (rekeyedRoster ≠ CrewFieldMission.fixtureRawConfig.roster) &&
  decide (rekeyedRoster.map Seat.playerKey ≠
    CrewFieldMission.fixtureRawConfig.roster.map Seat.playerKey) &&
  decide (rekeyedRoster.map Seat.id =
    CrewFieldMission.fixtureRawConfig.roster.map Seat.id) &&
  decide (rekeyedRoster.map Seat.role =
    CrewFieldMission.fixtureRawConfig.roster.map Seat.role) &&
  decide (rekeyedRoster.map Seat.credential =
    CrewFieldMission.fixtureRawConfig.roster.map Seat.credential) &&
  decide (rekeyedRoster.map Seat.initialCounter =
    CrewFieldMission.fixtureRawConfig.roster.map Seat.initialCounter)

/-- The substituted crew is *admitted*, not rejected.  Without this the
collision below would be about an activation nothing accepts.
-/
theorem rekeyed_crew_activation_is_valid :
    activationValidB rekeyedRawActivation = true := by native_decide

/-- ⚑ The collision.  Two crews with disjoint wallet keys, both valid, carry the
same authored activation identity.  A durable host keyed by `activation_id`
alone would serve one state stream — one admission cursor — to both.  This
statement is expected to stay true: `activationDigest` is the digest of the
authored envelope and the roster is not in it.  It is the reason
`rosterBinding` exists. -/
theorem hostile_rekeyed_roster_shares_the_authored_activation_id :
    rekeyedRawActivation.activationId = fixtureRawActivation.activationId := rfl

/-- The computed binding is what separates them.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_rekeyed_roster_changes_the_computed_crew_binding : Bool :=
  decide (rekeyedRawActivation.rosterBinding ≠ fixtureRawActivation.rosterBinding)

/-- …and the pin refuses in the other direction too, so it is a statement about
the pin and not about one unlucky pairing.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_hostile_authored_seal_cannot_activate_the_substituted_crew : Bool :=
  (activate? rekeyedRawActivation CrewFieldMission.fixtureRunSeal).isNone

/-- The substituted crew is admitted through the same smart constructor, under its own seal. -/
private theorem rekeyed_crew_activation_admitted :
    (activate? rekeyedRawActivation CrewFieldMission.fixtureRekeyedRunSeal).isSome = true := by
  rw [activate?, dif_pos rekeyed_crew_activation_is_valid,
    dif_pos (show CrewFieldMission.fixtureRekeyedRunSeal.session =
      rekeyedRawActivation.fieldSession from rfl)]
  rfl

private def rekeyedActivation : Activation :=
  (activate? rekeyedRawActivation CrewFieldMission.fixtureRekeyedRunSeal).get
    rekeyed_crew_activation_admitted

/-- The refusal, decomposed so the *cause* is named: the authored crew's genesis
state still matches on `activation_id` — the old key really does still collide —
and is refused solely because the roster binding disagrees.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`cross_crew_state_refused_only_by_the_roster_binding`.) -/
def crossCrewStateRefusedOnRosterB : Bool :=
  decide (fixtureGenesis.activationId = rekeyedActivation.raw.activationId) &&
  decide (fixtureGenesis.rosterBinding ≠ rekeyedActivation.raw.rosterBinding) &&
  decide (StateWire.validB rekeyedActivation fixtureGenesis = false)

/-- End to end: a substituted officer, presenting the authored crew's durable
state, cannot consume that crew's admission. -/
private def rekeyedActorCommand : CommandWire :=
  { fixtureSafeCommand with
    actor := (rekeyedRoster.getD 0 CrewRelayExpedition.fixtureSeat0).playerKey }

/-- (Pinned `= true` in `CrewFieldMissionRuntimeFixtures`, under the theorem name
`hostile_substituted_crew_cannot_consume_the_authored_crews_admission`.) -/
def crossCrewRunRefusedB : Bool :=
  decide (judge rekeyedActivation fixtureGenesis rekeyedActorCommand = .error .invalidState)

/-- The callable entrypoint emits exactly the successful receipt the judge produced.
(Pinned `= true` in `CrewFieldMissionRuntimeFixtures`.) -/
def check_callable_entrypoint_emits_the_exact_successful_receipt : Bool :=
  decide (process fixtureActivation fixtureGenesis.toJson fixtureSafeCommand.toJson =
    fixtureSafeResult.toOption.map OutputWire.toJson)

/-! ## The authored activation and its wire transcripts -/

theorem fixture_runtime_content_valid :
    check_fixture_runtime_content_valid = true := by native_decide

theorem fixture_wire_transcripts_decode_back_to_the_kernel_traces :
    check_fixture_wire_transcripts_decode_back_to_the_kernel_traces = true := by native_decide

/-! ## Honest complete runs -/

theorem honest_complete_run_emits_one_ordinary_salvage_authorization :
    honestOrdinarySalvageB = true := by native_decide

theorem deep_run_separates_exchangeable_parts_from_nonmarket_relic_custody :
    deepTaxonomyB = true := by native_decide

/-! ## The hostile settlement cases -/

theorem hostile_same_admission_and_run_cannot_replay :
    replayRefusedB = true := by native_decide

theorem hostile_cross_activation_command_refused :
    check_hostile_cross_activation_command_refused = true := by native_decide

theorem hostile_forged_route_refused :
    check_hostile_forged_route_refused = true := by native_decide

theorem hostile_forged_outcome_refused :
    check_hostile_forged_outcome_refused = true := by native_decide

theorem hostile_actor_who_is_not_the_selected_officer_refused :
    check_hostile_actor_who_is_not_the_selected_officer_refused = true := by native_decide

theorem hostile_truncated_crew_transcript_refused :
    check_hostile_truncated_crew_transcript_refused = true := by native_decide

theorem hostile_forged_handoff_signature_refused_by_the_kernel :
    forgedHandoffSignatureRefusedB = true := by native_decide

theorem hostile_seal_for_another_session_cannot_activate :
    check_hostile_seal_for_another_session_cannot_activate = true := by native_decide

theorem hostile_canon_relic_market_activation_refused :
    check_hostile_canon_relic_market_activation_refused = true := by native_decide

theorem hostile_canon_relic_direct_trade_activation_refused :
    check_hostile_canon_relic_direct_trade_activation_refused = true := by native_decide

/-! ## The strict codec -/

theorem hostile_caller_authored_salvage_field_refused_by_strict_codec :
    check_hostile_caller_authored_salvage_field_refused_by_strict_codec = true := by
  native_decide

theorem strict_command_roundtrip :
    check_strict_command_roundtrip = true := by native_decide

theorem strict_state_roundtrip :
    check_strict_state_roundtrip = true := by native_decide

/-! ## The step ABI -/

theorem the_step_abi_reports_the_cursor_the_signed_transcript_used :
    stepAbiAnswersEveryPrefixB = true := by native_decide

theorem the_step_abi_refuses_a_wrong_crew_a_wrong_seat_and_an_overlong_prefix :
    stepAbiRefusalsB = true := by native_decide

/-! ## The two-crews-one-key collision, and the binding that closes it -/

theorem rekeyed_crew_is_a_real_substitution_of_the_player_keys_alone :
    rekeySubstitutionRealB = true := by native_decide

theorem rekeyed_roster_changes_the_computed_crew_binding :
    check_rekeyed_roster_changes_the_computed_crew_binding = true := by native_decide

theorem hostile_authored_seal_cannot_activate_the_substituted_crew :
    check_hostile_authored_seal_cannot_activate_the_substituted_crew = true := by native_decide

theorem cross_crew_state_refused_only_by_the_roster_binding :
    crossCrewStateRefusedOnRosterB = true := by native_decide

theorem hostile_substituted_crew_cannot_consume_the_authored_crews_admission :
    crossCrewRunRefusedB = true := by native_decide

theorem callable_entrypoint_emits_the_exact_successful_receipt :
    check_callable_entrypoint_emits_the_exact_successful_receipt = true := by native_decide

#assert_compiled fixture_runtime_content_valid
#assert_compiled fixture_wire_transcripts_decode_back_to_the_kernel_traces
#assert_compiled hostile_cross_activation_command_refused
#assert_compiled hostile_forged_route_refused
#assert_compiled hostile_forged_outcome_refused
#assert_compiled hostile_actor_who_is_not_the_selected_officer_refused
#assert_compiled hostile_truncated_crew_transcript_refused
#assert_compiled hostile_forged_handoff_signature_refused_by_the_kernel
#assert_compiled hostile_seal_for_another_session_cannot_activate
#assert_compiled hostile_canon_relic_market_activation_refused
#assert_compiled hostile_canon_relic_direct_trade_activation_refused
#assert_compiled hostile_caller_authored_salvage_field_refused_by_strict_codec
#assert_compiled strict_command_roundtrip
#assert_compiled strict_state_roundtrip
#assert_compiled the_step_abi_reports_the_cursor_the_signed_transcript_used
#assert_compiled the_step_abi_refuses_a_wrong_crew_a_wrong_seat_and_an_overlong_prefix
#assert_compiled rekeyed_crew_is_a_real_substitution_of_the_player_keys_alone
#assert_compiled rekeyed_roster_changes_the_computed_crew_binding
#assert_compiled hostile_authored_seal_cannot_activate_the_substituted_crew
#assert_compiled cross_crew_state_refused_only_by_the_roster_binding
#assert_compiled hostile_substituted_crew_cannot_consume_the_authored_crews_admission

-- `rfl` closes this one, but `CrewFieldMission.fixturePolicy` was itself built with
-- `native_decide`, so the statement inherits that axiom and pins in the compiled tier.
#assert_compiled hostile_rekeyed_roster_shares_the_authored_activation_id
#assert_compiled fixture_activation_valid
#assert_compiled rekeyed_crew_activation_is_valid

end Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime
