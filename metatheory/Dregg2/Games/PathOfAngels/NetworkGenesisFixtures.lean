/-
# Signal authority-head genesis — the fixture-pin EVALUATION, out of the crypto archive's build

`NetworkGenesis.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its thirty-five fixture pins ran `native_decide` at elaboration — the
live epoch-1 deployment byte pins plus the hostile ceremony fixtures — so any genesis
fixture regression (and this module's deployment constants are exactly what a re-genesis
staleifies) was a hard failure of every Rust proving target in the workspace. The pins'
STATEMENTS remain in `NetworkGenesis.lean` as evaluation-free `check_* : Bool`
definitions; THIS module is where they are RUN. It is rooted in the `PathOfAngelsGuards`
library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction there demands a proof as data.
-/
import Dregg2.Games.PathOfAngels.NetworkGenesis
import Batteries.Tactic.OpenPrivate

namespace Dregg2.Games.PathOfAngels.NetworkGenesis

set_option autoImplicit false
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire
open Dregg2.Games.PathOfAngels.NetworkGenesisWire
-- The laboratory reads these runtime helpers; they stay private to the runtime module.
open private emptyInitialState expectedCanon zeroDigest from Dregg2.Games.PathOfAngels.NetworkGenesis

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

private def digestOrZero (hex : String) : Digest32 :=
  (Emit.parseBytes32Hex? hex).getD zeroDigest

/-- Semantic output validation is exact authorized re-emission, not a second
partial checklist. This recomputes nested config/Canon bytes, both SHA-256
digests, all nine-lane coordinates, the external tuple bindings, and zero
history from the input and compares the complete output. -/
def validateGenesisOutput (input : GenesisInputWire) (output : GenesisOutputWire) : Bool :=
  match authorizeGenesis input with
  | some authorized => decide (output = authorized.output)
  | none => false

/-- Strictly decode both byte strings, authorize the input, and accept output
only when it is the exact complete Lean re-emission. By contrast,
`decodeGenesisOutputSyntax` establishes canonical syntax only. -/
def decodeValidatedGenesisOutput (inputBytes outputBytes : String) : Option GenesisOutputWire := do
  let input ← decodeGenesisInput inputBytes
  let output ← decodeGenesisOutputSyntax outputBytes
  if validateGenesisOutput input output then some output else none

abbrev FIXTURE_DEPLOYMENT_ID : String :=
  "4db835cc36cd0d3b722e742334dc1dde9557601fe1334c7499ab023de4d6d45d"
abbrev FIXTURE_DEPLOYMENT_DIGEST : String :=
  "893e03f5075a70b67902a46f9a7415bea29d321d0f3296e16f3e2623c0930691"
abbrev FIXTURE_FEDERATION_ID : String :=
  "70b7fa4cfbc3921bef2e1ddb1a42869c8dcef27539179c9cbdf6a6e6b1d07c1b"
abbrev FIXTURE_GENESIS_SHA256 : String :=
  "f7010ca2acf705a9d941cc27ae500b4274e958ec9529b364b8b678c3ce3ccdea"
abbrev FIXTURE_DEPLOYMENT_MANIFEST_SHA256 : String :=
  "85c5f58a8237333c6935374b5c8f40f479cb4e50bcbd91a4c4e8eb7a534dc7bb"
abbrev FIXTURE_DEPLOYMENT_POLICY_SHA256 : String := PRODUCTION_POLICY_ZERO_ISSUANCE_SHA256
abbrev FIXTURE_MANIFEST_SHA256 : String :=
  "d14e79e806af45834ffbf8e73fcaa01727454d7b886f4b66c21b1392e13c51c2"
abbrev FIXTURE_CONTENT_ROOT : String :=
  "fd22397fedd8ee0703e0548c349d194980f92ea0a40a1a32c9b830506b773e16"
abbrev FIXTURE_ACTIVATION_DIGEST : String :=
  "511837ba023f5636997368b0c6c698cb555eca3594d4c997076a10b2bbc62d9c"
abbrev FIXTURE_SOURCE_DIGEST : String :=
  "c2c82697e87c1b49338238cece11a3c9dc8b07eb3acc504746f78c87f766ad61"
abbrev FIXTURE_SIGNAL_DIGEST : String :=
  "b89d72fa3af6e64ac127f3ca6efe5ff3da0e0494ae843b05110798783614e5a2"
abbrev FIXTURE_CURATOR_KEY : String :=
  "3c757bafe5b819ea7a5d7059630b5fce3725f624fc1d560ff25dfd5059ac7b34"
/-- ⚠ RE-PINNED TWICE on 2026-08-05.  First when `Emit.signalMission` took its run seed
as a PARAMETER and the template began carrying `Emit.UNBOUND_RUN_SEED` (the hidden-instance
split); then again when the deployment was re-pointed at the live solo federation, because
the federation id is INSIDE the mission this config authorizes.  `FIXTURE_CANON_SHA256`
moved for the same reason — the canon state carries the federation id too.  Both were
recomputed with `sha256sum` over the exact UTF-8 bytes Lean emits, an independent
implementation from `sha256Wire?`, which is what makes the pin a gate rather than a
constant checked against its own definition.

⚠ RE-PINNED A THIRD TIME on 2026-08-08, by the relic-namespace partition of `049c1dab4`.
`signalMission.allowedRelics` and `signalReward.relics` are both `{relicSlot ⟨1⟩ 0}`, which
that commit moved from `1` to `1 * MISSION_RELIC_BLOCK + 0 = 16`, and BOTH are rendered
inside the authorized config — so the config bytes moved and this hash with them.
`FIXTURE_CANON_SHA256` did NOT move and is untouched below: the genesis canon carries an
EMPTY world, so it renders `"discovered_relics":[]` and holds no relic id at all.  That is
the check working: re-deriving it reproduced `f770d6bd…` byte-for-byte, which is what says
the recomputation below changed only what the namespace actually touched.

Recomputed over the exact UTF-8 bytes Lean emits, by `python3 hashlib` and by Node
`crypto.createHash("sha256")` independently — agreeing, and neither of them
`sha256Wire?`.

⚠ RE-PINNED A FOURTH TIME on 2026-10-01, BOTH hashes, with the content half above: the
config carries the content root and activation digest and the canon carries the content
binding, so both move with the counter-12 bundle.  Recomputed by `python3 hashlib` over the
`config_json` / `canon_json` strings the linked Lean evaluator emitted, not `sha256Wire?`. -/
abbrev FIXTURE_CONFIG_SHA256 : String :=
  "cd76188f330310a1c9e3eb94e8c83526b458e4fe692ab8eb6fdcb115941ca18a"
abbrev FIXTURE_CANON_SHA256 : String :=
  "9b2a9e91caffeef4d68d7a6e7d22cf829ae9f9f75d1157bac7198102881d90f1"

def fixtureDeploymentId := digestOrZero FIXTURE_DEPLOYMENT_ID
def fixtureDeploymentDigest := digestOrZero FIXTURE_DEPLOYMENT_DIGEST
def fixtureFederationId := digestOrZero FIXTURE_FEDERATION_ID
def fixtureGenesisSha256 := digestOrZero FIXTURE_GENESIS_SHA256
def fixtureDeploymentManifestSha256 := digestOrZero FIXTURE_DEPLOYMENT_MANIFEST_SHA256
def fixtureDeploymentPolicySha256 := digestOrZero FIXTURE_DEPLOYMENT_POLICY_SHA256
def fixtureManifestSha256 := digestOrZero FIXTURE_MANIFEST_SHA256
def fixtureContentRoot := digestOrZero FIXTURE_CONTENT_ROOT
def fixtureActivationDigest := digestOrZero FIXTURE_ACTIVATION_DIGEST
def fixtureSourceDigest := digestOrZero FIXTURE_SOURCE_DIGEST
def fixtureSignalDigest := digestOrZero FIXTURE_SIGNAL_DIGEST
def fixtureCuratorKey := digestOrZero FIXTURE_CURATOR_KEY
def fixtureConfigSha256 := digestOrZero FIXTURE_CONFIG_SHA256
def fixtureCanonSha256 := digestOrZero FIXTURE_CANON_SHA256

/-- The Signal arm of the fixture's config, named so the hostile variants below can
perturb ONE field of it — a `GameConfigWire` is a sum and has no record-update. -/
def fixtureSignalConfigWire : SignalConfigWire :=
  SignalConfigWire.ofSemantic
    (Emit.signalTemplateConfig fixtureFederationId fixtureSourceDigest
      fixtureSignalDigest fixtureContentRoot fixtureActivationDigest)

def fixtureInput : GenesisInputWire := {
  deployment := {
    schema := DEPLOYMENT_SCHEMA
    deploymentDomain := DEPLOYMENT_DOMAIN
    deploymentId := fixtureDeploymentId
    deploymentDigest := fixtureDeploymentDigest
    federationId := fixtureFederationId
    genesisSha256 := fixtureGenesisSha256
    manifestSha256 := fixtureDeploymentManifestSha256
    policySha256 := fixtureDeploymentPolicySha256
  }
  content := {
    signatureSchema := CONTENT_SIGNATURE_SCHEMA
    manifestSha256 := fixtureManifestSha256
    contentRoot := fixtureContentRoot
    activationDigest := fixtureActivationDigest
    sourceDigest := fixtureSourceDigest
    signalContentDigest := fixtureSignalDigest
    curatorKey := fixtureCuratorKey
    contentEpoch := 1
    activationCounter := 12
  }
  config := .signal fixtureSignalConfigWire
  initial := emptyInitialState
}

def fixtureInputBytes : String := fixtureInput.toJson

def fixtureConfigJson : String := fixtureInput.config.toJson

def fixtureCanonJson : String :=
  (CanonStateWire.ofSemantic (expectedCanon fixtureInput)).toJson

/-- `sha256(DEPLOYMENT_DOMAIN ‖ 0 ‖ fed ‖ 0 ‖ genesis)` reproduces the id the live
manifest carries — Lean and the JS that wrote the manifest agree without either being
told the answer. (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_deployment_id_rederived : Bool :=
  decide (sha256Wire? (deploymentIdPreimage fixtureInput) = some fixtureDeploymentId)

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_input_roundtrip : Bool :=
  decide (decodeGenesisInput fixtureInputBytes = some fixtureInput)

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_checks_accept : Bool := genesisChecks fixtureInput

/-- These two SHA-256 values were independently computed over the printed exact
UTF-8 strings (Node `crypto.createHash("sha256")`) before being pinned here.
They are not derived from `sha256Wire?` or from the expected-output definition.
(Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_config_sha256_external_pin : Bool :=
  decide (sha256Wire? fixtureConfigJson = some fixtureConfigSha256)

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_canon_sha256_external_pin : Bool :=
  decide (sha256Wire? fixtureCanonJson = some fixtureCanonSha256)

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_authorizes : Bool := (authorizeGenesis fixtureInput).isSome

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_authorized_hashes : Bool :=
  decide ((authorizeGenesis fixtureInput).map
    (fun genesis => (genesis.output.configSha256, genesis.output.canonSha256)) =
    some (fixtureConfigSha256, fixtureCanonSha256))

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_processes : Bool := (processNetworkGenesisWire fixtureInputBytes).isSome

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_ffi_nonempty : Bool := decide (networkGenesisFFI fixtureInputBytes ≠ "")

def fixtureOutputBytes : String := networkGenesisFFI fixtureInputBytes

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_output_is_semantically_validated : Bool :=
  (decodeValidatedGenesisOutput fixtureInputBytes fixtureOutputBytes).isSome

def fixtureTamperedOutputHash : String :=
  fixtureOutputBytes.replace FIXTURE_CONFIG_SHA256 FIXTURE_DEPLOYMENT_ID

/-- Canonical syntax is deliberately not authority: a correctly shaped output
with a substituted config hash parses, then fails exact authorized re-emission.
(Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_fixture_tampered_output_is_syntax_only : Bool :=
  (decodeGenesisOutputSyntax fixtureTamperedOutputHash).isSome &&
    (decodeValidatedGenesisOutput fixtureInputBytes fixtureTamperedOutputHash).isNone

def wrongRewardInput : GenesisInputWire := {
  fixtureInput with config := .signal { fixtureSignalConfigWire with
    reward := { fixtureSignalConfigWire.reward with score := 501 } }
}

def wrongSessionInput : GenesisInputWire := {
  fixtureInput with config := .signal { fixtureSignalConfigWire with mission := {
    fixtureSignalConfigWire.mission with contentSession := fixtureDeploymentId } }
}

def wrongFederationInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with federationId := fixtureDeploymentId }
}

def wrongDeploymentIdInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with deploymentId := fixtureContentRoot }
}

def wrongDeploymentDigestInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with deploymentDigest := fixtureContentRoot }
}

def wrongDeploymentManifestInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with manifestSha256 := fixtureContentRoot }
}

def wrongDeploymentPolicyInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with policySha256 := fixtureContentRoot }
}

def wrongGenesisShaInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with genesisSha256 := fixtureManifestSha256 }
}

def wrongEpochInput : GenesisInputWire := {
  fixtureInput with content := { fixtureInput.content with contentEpoch := 2 }
}

def wrongContentRootInput : GenesisInputWire := {
  fixtureInput with content := {
    fixtureInput.content with contentRoot := fixtureDeploymentId }
}

def wrongActivationInput : GenesisInputWire := {
  fixtureInput with content := {
    fixtureInput.content with activationDigest := fixtureDeploymentId }
}

def zeroActivationCounterInput : GenesisInputWire := {
  fixtureInput with content := { fixtureInput.content with activationCounter := 0 }
}

def terminalActivationCounterInput : GenesisInputWire := {
  fixtureInput with content := {
    fixtureInput.content with activationCounter := WIRE_NAT_LIMIT }
}

def nonzeroWorldInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with world := {
    fixtureInput.initial.world with intel := 1 } }
}

def nonzeroSequenceInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with world := {
    fixtureInput.initial.world with sequence := 1 } }
}

def nonzeroRevisionInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with canonRevision := 1 }
}

def nonzeroCuratorCounterInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with curatorCounter := 1 }
}

def nonzeroTransitionInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with transitionCount := 1 }
}

def nonzeroLastDigestInput : GenesisInputWire := {
  fixtureInput with initial := {
    fixtureInput.initial with lastTransitionDigest := fixtureDeploymentId }
}

def fixtureCounterRow : PlayerCounterRowWire := {
  federationId := fixtureFederationId
  contentSession := Emit.signalContentSession
  contentEpoch := 1
  playerKey := fixtureCuratorKey
  value := 1
}

def nonemptyCounterInput : GenesisInputWire := {
  fixtureInput with initial := {
    fixtureInput.initial with playerCounters := [fixtureCounterRow] }
}

def duplicateCounterInput : GenesisInputWire := {
  fixtureInput with initial := {
    fixtureInput.initial with playerCounters := [fixtureCounterRow, fixtureCounterRow] }
}

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_caller_chosen_reward_refused : Bool :=
  (processNetworkGenesisWire wrongRewardInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_inconsistent_content_session_refused : Bool :=
  (processNetworkGenesisWire wrongSessionInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_inconsistent_federation_refused : Bool :=
  (processNetworkGenesisWire wrongFederationInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_substituted_deployment_id_refused : Bool :=
  (processNetworkGenesisWire wrongDeploymentIdInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_substituted_deployment_digest_refused : Bool :=
  (processNetworkGenesisWire wrongDeploymentDigestInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_substituted_deployment_manifest_refused : Bool :=
  (processNetworkGenesisWire wrongDeploymentManifestInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_substituted_deployment_policy_refused : Bool :=
  (processNetworkGenesisWire wrongDeploymentPolicyInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_substituted_genesis_sha_refused : Bool :=
  (processNetworkGenesisWire wrongGenesisShaInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_inconsistent_epoch_refused : Bool :=
  (processNetworkGenesisWire wrongEpochInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_inconsistent_content_root_refused : Bool :=
  (processNetworkGenesisWire wrongContentRootInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_inconsistent_activation_refused : Bool :=
  (processNetworkGenesisWire wrongActivationInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_zero_activation_counter_refused : Bool :=
  (processNetworkGenesisWire zeroActivationCounterInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_terminal_activation_counter_refused : Bool :=
  (processNetworkGenesisWire terminalActivationCounterInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_nonzero_genesis_world_refused : Bool :=
  (processNetworkGenesisWire nonzeroWorldInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_nonzero_genesis_sequence_refused : Bool :=
  (processNetworkGenesisWire nonzeroSequenceInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_nonzero_genesis_revision_refused : Bool :=
  (processNetworkGenesisWire nonzeroRevisionInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_nonzero_genesis_curator_counter_refused : Bool :=
  (processNetworkGenesisWire nonzeroCuratorCounterInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_nonzero_genesis_transition_refused : Bool :=
  (processNetworkGenesisWire nonzeroTransitionInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_nonzero_genesis_last_digest_refused : Bool :=
  (processNetworkGenesisWire nonzeroLastDigestInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_nonempty_player_counter_refused : Bool :=
  (processNetworkGenesisWire nonemptyCounterInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_duplicate_player_counter_refused_by_syntax : Bool :=
  (decodeGenesisInput duplicateCounterInput.toJson).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_trailing_bytes_refused : Bool :=
  (processNetworkGenesisWire (fixtureInputBytes ++ "\n")).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_uppercase_digest_refused : Bool :=
  (processNetworkGenesisWire
    (fixtureInputBytes.replace FIXTURE_FEDERATION_ID
      (String.toUpper FIXTURE_FEDERATION_ID))).isNone

/-- (Pinned `= true` in `NetworkGenesisFixtures`.) -/
def check_unknown_top_level_field_refused : Bool :=
  (processNetworkGenesisWire
    (fixtureInputBytes.replace
      ("{\"format\":\"" ++ NetworkGenesisWire.INPUT_FORMAT ++ "\"")
      ("{\"format\":\"" ++ NetworkGenesisWire.INPUT_FORMAT ++ "\",\"unknown\":0"))).isNone

theorem fixture_deployment_id_rederived :
    check_fixture_deployment_id_rederived = true := by native_decide

theorem fixture_input_roundtrip :
    check_fixture_input_roundtrip = true := by native_decide

theorem fixture_checks_accept :
    check_fixture_checks_accept = true := by native_decide

theorem fixture_config_sha256_external_pin :
    check_fixture_config_sha256_external_pin = true := by native_decide

theorem fixture_canon_sha256_external_pin :
    check_fixture_canon_sha256_external_pin = true := by native_decide

theorem fixture_authorizes :
    check_fixture_authorizes = true := by native_decide

theorem fixture_authorized_hashes :
    check_fixture_authorized_hashes = true := by native_decide

theorem fixture_processes :
    check_fixture_processes = true := by native_decide

theorem fixture_ffi_nonempty :
    check_fixture_ffi_nonempty = true := by native_decide

theorem fixture_output_is_semantically_validated :
    check_fixture_output_is_semantically_validated = true := by native_decide

theorem fixture_tampered_output_is_syntax_only :
    check_fixture_tampered_output_is_syntax_only = true := by native_decide

theorem caller_chosen_reward_refused :
    check_caller_chosen_reward_refused = true := by native_decide

theorem inconsistent_content_session_refused :
    check_inconsistent_content_session_refused = true := by native_decide

theorem inconsistent_federation_refused :
    check_inconsistent_federation_refused = true := by native_decide

theorem substituted_deployment_id_refused :
    check_substituted_deployment_id_refused = true := by native_decide

theorem substituted_deployment_digest_refused :
    check_substituted_deployment_digest_refused = true := by native_decide

theorem substituted_deployment_manifest_refused :
    check_substituted_deployment_manifest_refused = true := by native_decide

theorem substituted_deployment_policy_refused :
    check_substituted_deployment_policy_refused = true := by native_decide

theorem substituted_genesis_sha_refused :
    check_substituted_genesis_sha_refused = true := by native_decide

theorem inconsistent_epoch_refused :
    check_inconsistent_epoch_refused = true := by native_decide

theorem inconsistent_content_root_refused :
    check_inconsistent_content_root_refused = true := by native_decide

theorem inconsistent_activation_refused :
    check_inconsistent_activation_refused = true := by native_decide

theorem zero_activation_counter_refused :
    check_zero_activation_counter_refused = true := by native_decide

theorem terminal_activation_counter_refused :
    check_terminal_activation_counter_refused = true := by native_decide

theorem nonzero_genesis_world_refused :
    check_nonzero_genesis_world_refused = true := by native_decide

theorem nonzero_genesis_sequence_refused :
    check_nonzero_genesis_sequence_refused = true := by native_decide

theorem nonzero_genesis_revision_refused :
    check_nonzero_genesis_revision_refused = true := by native_decide

theorem nonzero_genesis_curator_counter_refused :
    check_nonzero_genesis_curator_counter_refused = true := by native_decide

theorem nonzero_genesis_transition_refused :
    check_nonzero_genesis_transition_refused = true := by native_decide

theorem nonzero_genesis_last_digest_refused :
    check_nonzero_genesis_last_digest_refused = true := by native_decide

theorem nonempty_player_counter_refused :
    check_nonempty_player_counter_refused = true := by native_decide

theorem duplicate_player_counter_refused_by_syntax :
    check_duplicate_player_counter_refused_by_syntax = true := by native_decide

theorem trailing_bytes_refused :
    check_trailing_bytes_refused = true := by native_decide

theorem uppercase_digest_refused :
    check_uppercase_digest_refused = true := by native_decide

theorem unknown_top_level_field_refused :
    check_unknown_top_level_field_refused = true := by native_decide

#assert_compiled fixture_deployment_id_rederived
#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_checks_accept
#assert_compiled fixture_config_sha256_external_pin
#assert_compiled fixture_canon_sha256_external_pin
#assert_compiled fixture_authorizes
#assert_compiled fixture_authorized_hashes
#assert_compiled fixture_processes
#assert_compiled fixture_ffi_nonempty
#assert_compiled fixture_output_is_semantically_validated
#assert_compiled fixture_tampered_output_is_syntax_only
#assert_compiled caller_chosen_reward_refused
#assert_compiled inconsistent_content_session_refused
#assert_compiled inconsistent_federation_refused
#assert_compiled substituted_deployment_id_refused
#assert_compiled substituted_deployment_digest_refused
#assert_compiled substituted_deployment_manifest_refused
#assert_compiled substituted_deployment_policy_refused
#assert_compiled substituted_genesis_sha_refused
#assert_compiled inconsistent_epoch_refused
#assert_compiled inconsistent_content_root_refused
#assert_compiled inconsistent_activation_refused
#assert_compiled zero_activation_counter_refused
#assert_compiled terminal_activation_counter_refused
#assert_compiled nonzero_genesis_world_refused
#assert_compiled nonzero_genesis_sequence_refused
#assert_compiled nonzero_genesis_revision_refused
#assert_compiled nonzero_genesis_curator_counter_refused
#assert_compiled nonzero_genesis_transition_refused
#assert_compiled nonzero_genesis_last_digest_refused
#assert_compiled nonempty_player_counter_refused
#assert_compiled duplicate_player_counter_refused_by_syntax
#assert_compiled trailing_bytes_refused
#assert_compiled uppercase_digest_refused
#assert_compiled unknown_top_level_field_refused

end Dregg2.Games.PathOfAngels.NetworkGenesis
