/-
# Galley maintenance daily runtime — the fixture EVALUATION, out of the crypto archive's build

`GalleyMaintenanceDailyRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's
build root), and until 2026-08-08 its adversarial/end-to-end fixture block ran seventeen
`native_decide` pins at elaboration — so any fixture regression was a hard failure of every Rust
proving target in the workspace (the compilation-unit coupling the stale-fixture outage
measured). The fixtures' STATEMENTS remain in `GalleyMaintenanceDailyRuntime.lean` as
evaluation-free `check_* : Bool` definitions, beside the private policy/viewer/carrier/authority
they exercise (which `GalleyMaintenanceDailyRuntimeBoundary.adversarial_fixtures_are_private`
requires stay private); THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose judge
call refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ Named residue: NONE. `fixture_sponsor_wire_refuses_valid_caller_json` stayed behind as a
theorem in the parent because it is `rfl` (the sponsor wire is unconditionally the empty
string), not an evaluation, and its `#assert_axioms` census line stayed with it.
-/
import Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime
import Batteries.Tactic.OpenPrivate

namespace Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime

set_option autoImplicit false
open Lean
open Dregg2.Games.PathOfAngels
-- The laboratory reads these runtime helpers; they stay private to the runtime module.
open private fixtureAuthority fixtureCarrier fixtureDigest fixturePolicy fixtureSponsorCommand
   fixtureState0 fixtureViewInput fixtureViewer nextEvent publicAction sponsorAction zeroDigest from Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

private def fixturePublicPayload : PayloadWire := {
  kind := "public-play"
  actor := fixtureViewer.player
  beneficiary := fixtureViewer.player
  activityId := fixturePolicy.publicActivityId
  grantNullifier := zeroDigest
  authorityCommitment := zeroDigest
  localService := fixturePolicy.publicService
}

private def fixturePublicEvent : EventWire :=
  nextEvent fixturePolicy fixtureState0 fixturePublicPayload

private def fixtureProjection1 : ProjectionWire := {
  sequence := 1
  publicPlayers := [fixtureViewer.player]
  sponsors := []
  spentGrantNullifiers := []
  publicPlayCount := 1
  sponsorshipCount := 0
  localServiceTotal := fixturePolicy.publicService
  powerRoot := fixturePolicy.powerRoot
  lootRoot := fixturePolicy.lootRoot
  canonRoot := fixturePolicy.canonRoot
  canonRevision := fixturePolicy.canonRevision
}

private def fixturePublicCommand : InputWire := {
  fixtureViewInput with
  mode := "command"
  action := {
    kind := "public-play"
    token := (publicAction fixturePolicy fixtureState0 fixtureViewer).token
  }
}

private def fixtureAfterView : InputWire := {
  fixtureViewInput with
  history := [fixturePublicEvent]
  claimedProjection := fixtureProjection1
}

private def fixtureWrongVersion : InputWire := {
  fixtureAfterView with
  history := [{ fixturePublicEvent with
    statement := { fixturePublicEvent.statement with version := STREAM_VERSION + 1 } }]
}

private def fixtureWrongPayloadDigest : InputWire := {
  fixtureAfterView with
  history := [{ fixturePublicEvent with
    statement := { fixturePublicEvent.statement with payloadDigest := zeroDigest } }]
}

private def fixtureStaleProjection : InputWire := {
  fixtureAfterView with
  claimedProjection := initialProjection fixturePolicy
}

private def fixtureForgedSponsor : InputWire := {
  fixtureViewInput with
  mode := "command"
  action := { kind := "holder-sponsor", token := fixtureDigest 99 }
}

/-- The authored fixture policy passes the wire validity predicate.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_policy_valid : Bool := fixturePolicy.validB

/-- The canonical input wire decodes back to the exact value that encoded it.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_input_roundtrip : Bool :=
  decide (decodeInput fixtureViewInput.toJson = some fixtureViewInput)

/-- A public view is judged. (Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_public_view_accepted : Bool :=
  (judgeBytesWithAuthority? fixtureViewInput.toJson 0 none).isSome

/-- A public play command is judged.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_public_command_accepted : Bool :=
  (judgeBytesWithAuthority? fixturePublicCommand.toJson 0 none).isSome

/-- The judged output bytes re-decode as an `OutputWire`.  Fail-closed: a refused command
answers `false`. (Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_public_output_redecodes : Bool :=
  match judgeBytesWithAuthority? fixturePublicCommand.toJson 0 none with
  | none => false
  | some bytes => (decodeOutput bytes).isSome

/-- Replaying the accepted event and claiming its projection is judged.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_replay_successor_accepted : Bool :=
  (judgeBytesWithAuthority? fixtureAfterView.toJson 0 none).isSome

/-- A holder sponsorship under a real admitted authority moves NO advantage anchor and issues a
receipt with zero power/loot/canon delta and bounded local service.  Fail-closed: a refused
command, or an accepted one with no receipt, answers `false`.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_beta_sponsor_accepted_without_advantage : Bool :=
  match judgeInput? fixtureSponsorCommand.toJson fixtureSponsorCommand 50 (some fixtureAuthority) with
  | none => false
  | some output =>
      output.projection.powerRoot = fixturePolicy.powerRoot &&
      output.projection.lootRoot = fixturePolicy.lootRoot &&
      output.projection.canonRoot = fixturePolicy.canonRoot &&
      output.projection.canonRevision = fixturePolicy.canonRevision &&
      match output.receipt with
      | none => false
      | some receipt => receipt.powerDelta = 0 && receipt.lootDelta = 0 &&
          receipt.canonRevisionDelta = 0 && receipt.localService ≤ MAX_LOCAL_SERVICE

/-- The beta holder seal carrier round-trips through its canonical encoding.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_beta_seal_roundtrip : Bool :=
  decide (decodeBetaHolderSeal fixtureCarrier.toJson = some fixtureCarrier)

/-- The internally-authored sponsor action really is among the actions the view offers, so
the token the command carries is not a fixture-only spelling.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_internal_sponsor_view_authors_token : Bool :=
  decide ((sponsorAction fixturePolicy fixtureState0 fixtureViewer fixtureAuthority) ∈
    (viewOf fixturePolicy fixtureState0 fixtureViewer 50 (some fixtureAuthority)).availableActions)

/-- The disabled sponsor wire's output is not decodable as an `OutputWire` — it cannot be
mistaken for a judged result. (Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_sponsor_wire_output_never_decodes : Bool :=
  (decodeOutput (runAdmittedBetaSponsorWire fixtureSponsorCommand.toJson
    fixtureCarrier.toJson)).isNone

/-- A history event at the wrong stream version is refused.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_wrong_version_refused : Bool :=
  (judgeBytesWithAuthority? fixtureWrongVersion.toJson 0 none).isNone

/-- A history event whose payload digest does not bind its payload is refused.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_wrong_payload_digest_refused : Bool :=
  (judgeBytesWithAuthority? fixtureWrongPayloadDigest.toJson 0 none).isNone

/-- A claimed projection that is stale for the submitted history is refused.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_stale_projection_refused : Bool :=
  (judgeBytesWithAuthority? fixtureStaleProjection.toJson 0 none).isNone

/-- A holder-sponsor command with a forged token and no admitted authority is refused.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_forged_sponsor_without_authority_refused : Bool :=
  (judgeBytesWithAuthority? fixtureForgedSponsor.toJson 0 none).isNone

/-- Canonical bytes plus one trailing space are not canonical.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_trailing_byte_refused : Bool :=
  (decodeInput (fixtureViewInput.toJson ++ " ")).isNone

/-- An unknown field is refused rather than ignored.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_unknown_field_refused : Bool :=
  (decodeInput "{\"format\":\"POA-GALLEY-DAILY-IN-1\",\"unknown\":0}").isNone

/-- The byte limit is enforced before parsing.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_tiny_byte_limit_refused : Bool :=
  (decodeInputWithLimit 4 fixtureViewInput.toJson).isNone

theorem fixture_policy_valid :
    check_fixture_policy_valid = true := by native_decide

theorem fixture_input_roundtrip :
    check_fixture_input_roundtrip = true := by native_decide

theorem fixture_public_view_accepted :
    check_fixture_public_view_accepted = true := by native_decide

theorem fixture_public_command_accepted :
    check_fixture_public_command_accepted = true := by native_decide

theorem fixture_public_output_redecodes :
    check_fixture_public_output_redecodes = true := by native_decide

theorem fixture_replay_successor_accepted :
    check_fixture_replay_successor_accepted = true := by native_decide

theorem fixture_beta_sponsor_accepted_without_advantage :
    check_fixture_beta_sponsor_accepted_without_advantage = true := by native_decide

theorem fixture_beta_seal_roundtrip :
    check_fixture_beta_seal_roundtrip = true := by native_decide

theorem fixture_internal_sponsor_view_authors_token :
    check_fixture_internal_sponsor_view_authors_token = true := by native_decide

theorem fixture_sponsor_wire_output_never_decodes :
    check_fixture_sponsor_wire_output_never_decodes = true := by native_decide

theorem hostile_wrong_version_refused :
    check_hostile_wrong_version_refused = true := by native_decide

theorem hostile_wrong_payload_digest_refused :
    check_hostile_wrong_payload_digest_refused = true := by native_decide

theorem hostile_stale_projection_refused :
    check_hostile_stale_projection_refused = true := by native_decide

theorem hostile_forged_sponsor_without_authority_refused :
    check_hostile_forged_sponsor_without_authority_refused = true := by native_decide

theorem hostile_trailing_byte_refused :
    check_hostile_trailing_byte_refused = true := by native_decide

theorem hostile_unknown_field_refused :
    check_hostile_unknown_field_refused = true := by native_decide

theorem hostile_tiny_byte_limit_refused :
    check_hostile_tiny_byte_limit_refused = true := by native_decide

#assert_compiled fixture_policy_valid
#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_public_view_accepted
#assert_compiled fixture_public_command_accepted
#assert_compiled fixture_public_output_redecodes
#assert_compiled fixture_replay_successor_accepted
#assert_compiled fixture_beta_sponsor_accepted_without_advantage
#assert_compiled fixture_beta_seal_roundtrip
#assert_compiled fixture_internal_sponsor_view_authors_token
#assert_compiled fixture_sponsor_wire_output_never_decodes
#assert_compiled hostile_wrong_version_refused
#assert_compiled hostile_wrong_payload_digest_refused
#assert_compiled hostile_stale_projection_refused
#assert_compiled hostile_forged_sponsor_without_authority_refused
#assert_compiled hostile_trailing_byte_refused
#assert_compiled hostile_unknown_field_refused
#assert_compiled hostile_tiny_byte_limit_refused

end Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime
