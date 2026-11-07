/-
# Night-watch content emit driver

Renders the epoch-1 `poa.night-watch-campaign.config.v1` component and its
activated-content manifest from `NightWatchCampaignContent`, exactly as the galley's
`scripts/poa-galley-content.py` renders the galley policy — except there is no second
encoder: the bytes come from the SAME `configJson`/`Manifest.toJson` the admission
seam re-encodes against, so the only thing this driver can do wrong is refuse.

## The ceremony input

The config's `slot_commitment` is `HiddenInstance.commit` of a curator-drawn slot
secret.  The secret arrives as a FILE of 64 lowercase hex digits named by
`POA_NIGHT_WATCH_SECRET_FILE`; it is read, used, and never echoed — no artifact,
report line, or error message renders it.  The driver REFUSES the module's published
rehearsal secret, so the one instance any reader can derive can never back a shipped
artifact.

    umask 077; openssl rand -hex 32 > /path/outside/any/repo/night-watch-slot-1.secret
    POA_NIGHT_WATCH_SECRET_FILE=/path/outside/any/repo/night-watch-slot-1.secret \
      lake env lean --run Dregg2/Games/PathOfAngels/NightWatchCampaignContentEmitMain.lean

⚠ Custody: the secret must survive OUTSIDE every repository — the node's install
ceremony (the `poa_signal_slot_ceremony.rs` shape) will need it to open the
commitment, and a committed secret publishes every schedule of the slot.

## Fail-closed

Before anything is written the driver runs the ENTIRE shipped path over the real
commitment: structural activation, canonical decode round-trip, manifest decode,
`authorizeCampaignConfigForWorld?` against the derived world, `admitActivation?`
over a real draw, a full four-command watch through `replay`, and the exported
`judgeJson` accepting the final debrief.  Any refusal anywhere and no file moves.

## Modes

    emit  (default)             write config.json, manifest.json, world.json
    POA_NIGHT_WATCH_MODE=check  re-derive from the on-disk commitment and refuse on
                                drift — no secret needed, and the rehearsal
                                commitment is refused here too

Output dir: `POA_NIGHT_WATCH_OUT`, default `poa/artifacts/night-watch/epoch-1`
(relative to the working directory — run from the metatheory root's parent or set
the variable absolutely).
-/
import Dregg2.Games.PathOfAngels.NightWatchCampaignContent

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition
open Dregg2.Games.PathOfAngels.NightWatchCampaign
open Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission
open Dregg2.Games.PathOfAngels.NightWatchCampaignContent

set_option autoImplicit false

def writeAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  let staged := System.FilePath.mk (path.toString ++ ".partial")
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

def refuse {α : Type} (what : String) : IO α :=
  throw (IO.userError s!"REFUSED: {what}")

def require (what : String) : Bool → IO Unit
  | true => pure ()
  | false => refuse what

/-- The real draw the fail-closed watch uses: seat 0's authored key, the real
secret, the real derived seed. -/
def drawFor (secret : HiddenInstance.SlotSecret) (commitment : Digest32) :
    RawActivation :=
  { slot := authoredSlot
    slotSecret := secret
    slotCommitment := commitment
    playerKey := rehearsalPlayer
    mission := authoredMissionContext
    runSeed := HiddenInstance.runSeedFor
      { secret := secret, slot := authoredSlot, playerKey := rehearsalPlayer }
      authoredMissionContext }

/-- Every gate between a commitment and a written artifact.  Returns the config,
manifest and world bytes it verified.  ⚠ Refusals name the GATE, never a byte of
the secret. -/
def verifyChain (secret : Option HiddenInstance.SlotSecret) (commitment : Digest32) :
    IO (String × String × Digest32 × Digest32) := do
  require "the rehearsal commitment is published in NightWatchCampaignContent and is not deployable"
    (commitment != rehearsalCommitment)
  let raw := authoredRaw commitment
  let bytes := configJson raw
  require "the authored config does not activate" (activate? raw).isSome
  require "the config bytes do not round-trip through the canonical decoder"
    (decodeConfig bytes == some raw)
  let manifestBytes := authoredManifestBytes commitment
  let some validated := ActivatedContent.decodeManifest manifestBytes
    | refuse "the manifest bytes do not decode canonically"
  let some root := ActivatedContent.manifestRoot? (authoredManifest commitment)
    | refuse "the manifest root did not compute"
  let some componentSha := ActivatedContent.sha256Utf8? bytes
    | refuse "the component digest did not compute"
  let world := authoredWorld commitment authoredProvisionalActivationDigest
  let some member := authorizeCampaignConfigForWorld? world validated
    | refuse "the derived world does not admit the authored config"
  match secret with
  | none => pure ()
  | some secret => do
      require "the secret does not open the commitment"
        (HiddenInstance.commit secret authoredSlot == commitment)
      let draw := drawFor secret commitment
      let some activation := admitActivation? member.config draw
        | refuse "the real draw is not admitted"
      let .ok settled := replay activation (initialState activation) rehearsalWatch
        | refuse "the four-command watch does not settle"
      require "the settled watch is not at shift 1" (settled.shift == 1)
      require "the exported judge refuses the final debrief"
        (NightWatchCampaignWire.judgeJson (NightWatchCampaignWire.inputJson
          { world := world
            manifest := manifestBytes
            activation := draw
            history := rehearsalWatch.take 3
            command := { sequence := 3, nullifier := rehearsalNullifier 3
                         action := .debrief } })).isSome
  pure (bytes, manifestBytes, root, componentSha)

/-! ## Provenance -/

def q (value : String) : String := String.quote value

def preimageRendered (field label : String) : String :=
  (preimageOf field label).replace "\x00" "\\0"

def provenanceJson (commitment root componentSha : Digest32) : String :=
  let preimages := (derivedDigestCensus.filter fun pair => pair.1 != "rehearsal").map
    fun pair =>
      "    {\"field\":" ++ q pair.1 ++ ",\"label\":" ++ q pair.2 ++
      ",\"preimage_utf8\":" ++ q (preimageRendered pair.1 pair.2) ++
      ",\"sha256\":" ++ q (Emit.bytes32Hex (derivedDigest pair.1 pair.2)) ++ "}"
  "{\n" ++
  "  \"schema\": \"POA-NIGHT-WATCH-CONTENT-PROVENANCE-V1\",\n" ++
  "  \"note\": \"Provenance only. The world identity the curator signs is derived by the node's world preview (the poa-galley-world-preview shape), which supplies the real activation_digest; authorizeCampaignConfigForWorld? never reads it. The slot secret behind slot_commitment is curator-held, lives outside every repository, and is required by the future install ceremony.\",\n" ++
  "  \"deployment_id\": " ++ q DEPLOYMENT_ID_HEX ++ ",\n" ++
  "  \"federation_id\": " ++ q FEDERATION_ID_HEX ++ ",\n" ++
  "  \"content_session\": " ++ q CONTENT_SESSION_HEX ++ ",\n" ++
  "  \"content_session_ascii_tag\": " ++ q CONTENT_SESSION_TAG ++ ",\n" ++
  "  \"content_epoch\": " ++ toString CONTENT_EPOCH ++ ",\n" ++
  "  \"content_root\": " ++ q (Emit.bytes32Hex root) ++ ",\n" ++
  "  \"component_name\": " ++ q CONFIG_COMPONENT ++ ",\n" ++
  "  \"component_sha256\": " ++ q (Emit.bytes32Hex componentSha) ++ ",\n" ++
  "  \"mission_id\": " ++ toString AUTHORED_MISSION ++ ",\n" ++
  "  \"slot\": " ++ toString AUTHORED_SLOT ++ ",\n" ++
  "  \"slot_commitment\": " ++ q (Emit.bytes32Hex commitment) ++ ",\n" ++
  "  \"roster_note\": \"The four seat player keys are derived labels, not player-held keys. Seating real players re-emits the config, re-hashes the manifest, and requires a fresh signed world activation.\",\n" ++
  "  \"derive_domain\": " ++ q DERIVE_DOMAIN ++ ",\n" ++
  "  \"derived_digest_preimages\": [\n" ++
  String.intercalate ",\n" preimages ++ "\n" ++
  "  ]\n" ++
  "}\n"

/-! ## Modes -/

def outDir : IO System.FilePath := do
  pure (System.FilePath.mk
    ((← IO.getEnv "POA_NIGHT_WATCH_OUT").getD "poa/artifacts/night-watch/epoch-1"))

def emitMode : IO Unit := do
  let some secretPath ← IO.getEnv "POA_NIGHT_WATCH_SECRET_FILE"
    | refuse "POA_NIGHT_WATCH_SECRET_FILE is not set; the commitment needs a curator-drawn secret"
  let secretHex := (← IO.FS.readFile (System.FilePath.mk secretPath)).trimAscii.copy
  let some secretDigest := Emit.parseBytes32Hex? secretHex
    | refuse "the secret file is not 64 lowercase hex digits"
  let secret : HiddenInstance.SlotSecret := ⟨secretDigest⟩
  require "the secret file holds the PUBLISHED rehearsal secret; draw a real one"
    (secret != rehearsalSecret)
  let commitment := HiddenInstance.commit secret authoredSlot
  let (bytes, manifestBytes, root, componentSha) ← verifyChain (some secret) commitment
  let dir ← outDir
  IO.FS.createDirAll dir
  writeAtomic (dir / "config.json") bytes
  writeAtomic (dir / "manifest.json") manifestBytes
  writeAtomic (dir / "world.json") (provenanceJson commitment root componentSha)
  IO.println s!"wrote {dir}/config.json ({bytes.utf8ByteSize} bytes)"
  IO.println s!"wrote {dir}/manifest.json ({manifestBytes.utf8ByteSize} bytes)"
  IO.println s!"wrote {dir}/world.json"
  IO.println s!"content_root  = {Emit.bytes32Hex root}"
  IO.println s!"component_sha = {Emit.bytes32Hex componentSha}"
  IO.println s!"slot_commitment = {Emit.bytes32Hex commitment}"

def checkJsonField (json : Json) (key expected : String) : IO Unit := do
  match json.getObjValAs? String key with
  | .ok value =>
      require s!"world.json `{key}` does not match the re-derivation" (value == expected)
  | .error _ => refuse s!"world.json is missing `{key}`"

def checkMode : IO Unit := do
  let dir ← outDir
  let bytes ← IO.FS.readFile (dir / "config.json")
  let some raw := decodeConfig bytes
    | refuse "on-disk config.json does not decode canonically"
  require "on-disk config.json is not this module's authored content"
    (raw == authoredRaw raw.slotCommitment)
  let commitment := raw.slotCommitment
  let (expectedBytes, expectedManifest, root, componentSha) ←
    verifyChain none commitment
  require "on-disk config.json bytes drifted" (bytes == expectedBytes)
  let manifestBytes ← IO.FS.readFile (dir / "manifest.json")
  require "on-disk manifest.json bytes drifted" (manifestBytes == expectedManifest)
  let worldBytes ← IO.FS.readFile (dir / "world.json")
  let .ok worldJson := Json.parse worldBytes
    | refuse "world.json does not parse"
  checkJsonField worldJson "content_root" (Emit.bytes32Hex root)
  checkJsonField worldJson "component_sha256" (Emit.bytes32Hex componentSha)
  checkJsonField worldJson "slot_commitment" (Emit.bytes32Hex commitment)
  checkJsonField worldJson "federation_id" FEDERATION_ID_HEX
  IO.println "poa night-watch content artifacts are byte-exact"

def main : IO Unit := do
  match (← IO.getEnv "POA_NIGHT_WATCH_MODE").getD "emit" with
  | "emit" => emitMode
  | "check" => checkMode
  | other => refuse s!"unknown POA_NIGHT_WATCH_MODE `{other}`"
