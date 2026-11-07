/-
# Dregg2.Games.PathOfAngels.Emit — the POAG1 artifact boundary

This module is the single source of the bytes consumed by PoA hosts.  It projects
the Lean game declarations into a small, versioned bundle; TypeScript/Rust may
render these declarations, but they do not get a second copy of the rules.

`ingestManifest` is deliberately stricter than an ordinary JSON decoder:

* the object has exactly the POAG1 v1 fields;
* every artifact entry has exactly its five fields;
* the source digest is `sha256:` plus 64 lowercase hexadecimal digits;
* artifact paths, order, byte lengths, SHA-256 digests and FNV-1a byte pins must
  equal the bundle Lean itself renders.

The SHA-256 primitive is supplied by the reproducibility driver (which hashes the
named Lean sources and the signal descriptor bytes).  Lean parses the resulting
32-byte values, places them in `MissionSpec.ArtifactRef`, and owns every decision
about what those digests authorize.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.EmitDigestHex
import Dregg2.Games.PathOfAngels.RelicNamespace
import Dregg2.Games.PathOfAngels.SignalTriangulation
import Dregg2.Games.PathOfAngels.FiniteTables
import Dregg2.Games.PathOfAngels.BlackBoxReconstruction
import Dregg2.Games.PathOfAngels.HiddenInstance
import Dregg2.Games.PathOfAngels.EmitJson
import Dregg2.Games.PathOfAngels.DeckDescentEmit
import Dregg2.Games.PathOfAngels.ArtificerLogicEmit
import Dregg2.Games.PathOfAngels.VentCrawlEmit
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.Emit

open Lean
open Dregg2.Games.PathOfAngels
/- The JSON helpers, `exactKeys`, `instanceDeclarationJson` and the two shared
validators come from `EmitJson` — the private copies this module used to carry
were deleted 2026-08-07 when Deck Descent enrolled, exactly as the descent
lane's handover named: two copies of `instanceDeclarationJson` is two
descriptions of where an instance comes from. -/
open Dregg2.Games.PathOfAngels.EmitJson

abbrev FORMAT : String := "POAG1"
abbrev SCHEMA_VERSION : Nat := 1
abbrev AUTHORITY : String := "Dregg2.Games.PathOfAngels"

/-! ## The `Digest32` hex codec

⚑ `lowerHexDigit`, `hexNibble?`, `isLowerHexOfLength`, `validSha256`, `parseByte?`,
`parseDigestList?`, `parseDigest32?`, `parseBytes32Hex?`, `byteHex`, `bytes32Hex` and
`digestHex` MOVED to `Dregg2.Games.PathOfAngels.EmitDigestHex` (2026-08-09), in this same
namespace, so every `Emit.bytes32Hex` call site reads unchanged.  They are re-exported here
by the import above; nothing was copied.

The reason is the build graph, not the code.  This module imports every game's emit driver
— that is what an aggregate emitter is for — and seven RUNTIME/wire modules were importing
it to reach three codec functions, which put every game in the rack into the closure of
every crew/station guard module downstream (`CrewFieldMissionAdmissionFixtures`: 177 local
modules, unbuildable whenever Vent Crawl was).  An aggregator belongs in the closure of the
emitter binary and its pins, and nowhere else. -/

/-- Explicit non-deployment vector for deterministic emitter tests.  Canonical
artifacts never use it; their id is supplied only by verified PoA genesis. -/
abbrev TEST_FEDERATION_ID_HEX : String :=
  "a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1"

/-! ⚑ **THE EMITTER'S PINS NO LONGER EVALUATE IN THIS MODULE (2026-08-08).**  This module
is in the `Dregg2.FFI` closure — the crypto archive's build — and every `native_decide`
here (renders the whole bundle, parses it back, replays the black-box kernel over 3000
cells, draws eight Poseidon2 demonstration seeds per game) made a game-fixture regression a
hard failure of every Rust proving target.  The STATEMENTS stay here, each as an
evaluation-free `check_* : Bool` definition (a `def` body elaborates without running),
beside the render and validate functions they are about — the render defs themselves are
untouched.  The EVALUATION — each `check_* = true`, pinned by `native_decide` +
`#assert_compiled` — lives in `EmitFixtures.lean`, rooted in the `PathOfAngelsGuards`
library: a plain `lake build` still runs every pin, so a descriptor that stops matching its
own validator still reds, in the guard library instead of the archive.

⚠ Named residue, ONE proof: `signalRulesTable_cells_decode_to_the_kernel_bit` stays
`native_decide` HERE because it is the PREMISE of two general theorems that belong in this
module — `signalRulesCell_decodes_to_the_kernel_bit` and the marquee
`signalRulesCell_matches_step`.  Moving the evaluation would have moved those two general
statements out of the emitter with it.  Everything else moved. -/

/-- The explicit non-deployment federation vector parses.
(Pinned `= true` in `EmitFixtures`.) -/
def check_parseBytes32Hex_test_federation_vector : Bool :=
  (parseBytes32Hex? TEST_FEDERATION_ID_HEX).isSome

/-- A display label is not a federation id. (Pinned `= true` in `EmitFixtures`.) -/
def check_parseBytes32Hex_refuses_display_label : Bool :=
  (parseBytes32Hex? "POA-FED-1").isNone

/-! ## Stable byte pin -/

abbrev FNV_OFFSET : UInt64 := 14695981039346656037
abbrev FNV_PRIME : UInt64 := 1099511628211

/-- FNV-1a is an inexpensive deterministic drift/tamper pin, not a cryptographic
claim.  The source/content identities in `ArtifactRef` remain full SHA-256. -/
def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun acc byte => (acc ^^^ byte.toUInt64) * FNV_PRIME) FNV_OFFSET

private def uint64HexAux : Nat → UInt64 → List Char → List Char
  | 0, _, acc => acc
  | n + 1, x, acc =>
      uint64HexAux n (x / 16) (lowerHexDigit (x.toNat % 16) :: acc)

def fnv1a64Hex (s : String) : String :=
  String.ofList (uint64HexAux 16 (fnv1a64 s) [])

/-- The published FNV-1a 64 empty-string vector. (Pinned `= true` in `EmitFixtures`.) -/
def check_fnv1a64_empty_vector : Bool := decide (fnv1a64Hex "" = "cbf29ce484222325")

/-- The published FNV-1a 64 `"a"` vector. (Pinned `= true` in `EmitFixtures`.) -/
def check_fnv1a64_a_vector : Bool := decide (fnv1a64Hex "a" = "af63dc4c8601ec8c")

/-! ## POAG1 manifest and strict parser -/

structure ArtifactPin where
  path : String
  mediaType : String
  bytes : Nat
  sha256 : String
  fnv1a64 : String
deriving DecidableEq, Repr

structure Manifest where
  format : String
  schemaVersion : Nat
  sourceDigest : String
  authority : String
  artifacts : List ArtifactPin
deriving DecidableEq, Repr

structure ArtifactBytes where
  path : String
  mediaType : String
  contents : String
deriving DecidableEq, Repr

def ArtifactBytes.pin (a : ArtifactBytes) (sha256 : String) : ArtifactPin :=
  { path := a.path
    mediaType := a.mediaType
    bytes := a.contents.toUTF8.size
    sha256 := sha256
    fnv1a64 := fnv1a64Hex a.contents }

def ArtifactPin.toJson (p : ArtifactPin) : String :=
  "    {\"path\":" ++ jsonString p.path ++
    ",\"media_type\":" ++ jsonString p.mediaType ++
    ",\"bytes\":" ++ toString p.bytes ++
    ",\"sha256\":" ++ jsonString p.sha256 ++
    ",\"fnv1a64\":" ++ jsonString p.fnv1a64 ++ "}"

def Manifest.toJson (m : Manifest) : String :=
  "{\n  \"format\":" ++ jsonString m.format ++
    ",\n  \"schema_version\":" ++ toString m.schemaVersion ++
    ",\n  \"source_digest\":" ++ jsonString m.sourceDigest ++
    ",\n  \"authority\":" ++ jsonString m.authority ++
    ",\n  \"artifacts\":" ++ jsonPrettyArray (m.artifacts.map ArtifactPin.toJson) ++
    "\n}\n"

private def parseArtifactPin (j : Json) : Except String ArtifactPin := do
  exactKeys j ["path", "media_type", "bytes", "sha256", "fnv1a64"]
  pure {
    path := ← j.getObjValAs? String "path"
    mediaType := ← j.getObjValAs? String "media_type"
    bytes := ← j.getObjValAs? Nat "bytes"
    sha256 := ← j.getObjValAs? String "sha256"
    fnv1a64 := ← j.getObjValAs? String "fnv1a64"
  }

private def parseArtifactPins (j : Json) : Except String (List ArtifactPin) := do
  let xs ← j.getArr?
  xs.toList.mapM parseArtifactPin

private def parseManifestJson (j : Json) : Except String Manifest := do
  exactKeys j ["format", "schema_version", "source_digest", "authority", "artifacts"]
  pure {
    format := ← j.getObjValAs? String "format"
    schemaVersion := ← j.getObjValAs? Nat "schema_version"
    sourceDigest := ← j.getObjValAs? String "source_digest"
    authority := ← j.getObjValAs? String "authority"
    artifacts := ← parseArtifactPins (← j.getObjVal? "artifacts")
  }

def parseManifest (bytes : String) : Except String Manifest := do
  parseManifestJson (← Json.parse bytes)

/-! ## Lean-owned wire projections -/

def privacyGradeTag : PrivacyGrade → String
  | .public => "public"
  | .operatorVisibleHidingFri => "operator-visible-hiding-fri"
  | .processSeparatedThreshold => "process-separated-threshold"
  | .independentOperatorThreshold => "independent-operator-threshold"

def ballotRegimeTag : BallotRegime → String
  | .none => "none"
  | .onePlayerOneVoice => "one-player-one-voice"
  | .oneWalletOneVoice => "one-wallet-one-voice"
  | .cappedChoir => "capped-choir"
  | .predictionOracle => "prediction-oracle"

def artifactRefJson (a : ArtifactRef) : String :=
  "{\"mission_id\":" ++ toString a.missionId.value ++
    ",\"artifact_id\":" ++ toString a.artifactId.value ++
    ",\"source_digest\":" ++ jsonString (digestHex a.sourceDigest) ++
    ",\"content_digest\":" ++ jsonString (digestHex a.contentDigest) ++ "}"

/-- Exact wire projection used to regression-test the emitter independently of
Core's proof-carrying digest representation. -/
structure ArtifactRefProjection where
  missionId : Nat
  artifactId : Nat
  sourceDigest : String
  contentDigest : String
deriving DecidableEq, Repr

/-- Parse an emitted ArtifactRef and reject any missing or additional unique key. -/
def parseArtifactRefProjection (bytes : String) : Except String ArtifactRefProjection := do
  let j ← Json.parse bytes
  exactKeys j ["mission_id", "artifact_id", "source_digest", "content_digest"]
  pure {
    missionId := ← j.getObjValAs? Nat "mission_id"
    artifactId := ← j.getObjValAs? Nat "artifact_id"
    sourceDigest := ← j.getObjValAs? String "source_digest"
    contentDigest := ← j.getObjValAs? String "content_digest"
  }

private def artifactRefTestDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

private def artifactRefTestVector : ArtifactRef :=
  { missionId := ⟨7⟩
    artifactId := ⟨11⟩
    sourceDigest := artifactRefTestDigest
    contentDigest := artifactRefTestDigest }

/-- Exact bytes make a repeated `source_digest` (or any fifth field) observable,
even though ordinary JSON object parsers conventionally collapse duplicate keys.
(Pinned `= true` in `EmitFixtures`.) -/
def check_artifactRefJson_exact_four_key_vector : Bool :=
  decide (artifactRefJson artifactRefTestVector =
    "{\"mission_id\":7,\"artifact_id\":11,\"source_digest\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\",\"content_digest\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\"}")

/-- The emitted bytes parse back as the exact four-key projection.
(Pinned `= true` in `EmitFixtures`.) -/
def check_artifactRefJson_parses_as_exact_four_key_projection : Bool :=
  decide (parseArtifactRefProjection (artifactRefJson artifactRefTestVector) = .ok {
    missionId := 7
    artifactId := 11
    sourceDigest :=
      "sha256:0000000000000000000000000000000000000000000000000000000000000000"
    contentDigest :=
      "sha256:0000000000000000000000000000000000000000000000000000000000000000"
  })

def contributionBudgetJson (b : ContributionBudget) : String :=
  "{\"intel\":" ++ toString b.intel.val ++
    ",\"supplies\":" ++ toString b.supplies.val ++
    ",\"cohesion\":" ++ toString b.cohesion.val ++
    ",\"influence\":" ++ toString b.influence.val ++
    ",\"score\":" ++ toString b.score.val ++
    ",\"relics\":" ++ toString b.relics.val ++ "}"

def contributionJsonWithRelics (c : Contribution) (relics : RelicList c.relics) : String :=
  "{\"intel\":" ++ toString c.intel.val ++
    ",\"supplies\":" ++ toString c.supplies.val ++
    ",\"cohesion\":" ++ toString c.cohesion.val ++
    ",\"influence\":" ++ toString c.influence.val ++
    ",\"score\":" ++ toString c.score.val ++
    ",\"relics\":" ++ jsonArray (relics.numbers.map toString) ++ "}"

def worldStateJsonWith (w : WorldState) (relics : RelicList w.discoveredRelics)
    (artifacts : List ArtifactRef) : String :=
  "{\"intel\":" ++ toString w.intel.val ++
    ",\"supplies\":" ++ toString w.supplies.val ++
    ",\"cohesion\":" ++ toString w.cohesion.val ++
    ",\"influence\":" ++ toString w.influence.val ++
    ",\"score\":" ++ toString w.score.val ++
    ",\"discovered_relics\":" ++
      jsonArray (relics.numbers.map toString) ++
    ",\"beta_artifacts\":" ++
      jsonArray (artifacts.map artifactRefJson) ++
    ",\"sequence\":" ++ toString w.sequence ++ "}"

/-! ## Signal Triangulation executable descriptor and mission fixture -/

/-- Fixed-width domain identifiers for the beta devnet and this exact content
session.  They are identifiers, not hashes, so their wire spelling has no sha256
prefix. -/
private def taggedBytes32 (tag : List Nat) : Digest32 where
  bytes := List.ofFn fun i : Fin 32 =>
    match tag[i.val]? with
    | some n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩
    | none => 0
  length_eq := by simp

def signalContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 83, 73, 71, 45, 49]

/-! ## The instance is drawn per run, and no artifact carries it

⚠ `signalRunSeed`, `signalTarget`, `signalTarget_from_runSeed` and
`signalTarget_literal` are GONE, and so are `relayRunSeed`, `relayBoardIndex`,
`relayBoard`, `salvageRunSeed` and `salvageSeed` below.

Deleting the descriptor's `"target"` field alone would have closed nothing.  The
run seed was published in the descriptor AND in the catalog, and
`targetFromSeed` is public: a reader computed `[2,4,1]` either way.  The seed had
to stop being a constant, so it did.  `MissionSpec.runSeed` is now supplied per
run by `HiddenInstance.runSeedFor` from a slot secret the curator commits to
before the slot opens and opens after it closes.

Missions rendered into an artifact therefore carry `UNBOUND_RUN_SEED`, which is
not a seed and draws nothing.  A judge that is handed it produces the instance of
the all-zero seed, which is why `Judged.admissionChecks` requires the live seed to
equal the derivation and refuses this value outright. -/

/-- The run-seed slot of a template mission: thirty-two zero bytes, meaning "no
live draw has happened".  It is emitted nowhere; it exists so `MissionSpec` stays
total in the catalog. -/
def UNBOUND_RUN_SEED : Digest32 := taggedBytes32 []

/-- Every legal three-band submission, in stable low/mid/high lexicographic order. -/
def signalAllCodes : List SignalTriangulation.Code :=
  (List.finRange 6).flatMap fun low =>
    (List.finRange 6).flatMap fun mid =>
      (List.finRange 6).map fun high => { low, mid, high }

/-- The emitted code list is the complete 6x6x6 space. (Pinned `= true` in `EmitFixtures`.) -/
def check_signalAllCodes_length : Bool := decide (signalAllCodes.length = 216)

/-- No code is emitted twice. (Pinned `= true` in `EmitFixtures`.) -/
def check_signalAllCodes_nodup : Bool := decide signalAllCodes.Nodup

theorem signalAllCodes_complete (code : SignalTriangulation.Code) :
    code ∈ signalAllCodes := by
  rcases code with ⟨low, mid, high⟩
  simp [signalAllCodes]

/-! ### The rules, as the WHOLE oracle

The old descriptor carried `outcomes`: 216 rows of feedback against ONE target,
with the solving row flagged.  That table is the answer written out.

What is emitted instead is the complete function — a 216 by 216 table of feedback
classes, row indexed by target and column by guess.  It states every rule and
distinguishes no instance: every row solves at exactly its own index
(`signal_every_row_solves_at_exactly_its_own_index`), so the table is symmetric
under which row is live.  A real run learns one class per guess from the judge; a
practice run reads its own row, because it chose it.

Rows are strings over `class_alphabet`, one character per cell.  A cell the class
list cannot name renders `?`, and `validateSignalDescriptor` refuses it, so a
silent fold is impossible. -/

/-- The realizable feedback classes, generated in canonical `(exact, present)`
order and filtered by realizability against an all-distinct target — the richest
instance, which is why filtering against it does not lose a class.
`signalClassPairs_complete` is the check over the whole 216-by-216 domain. -/
def signalClassPairs : List (Nat × Nat) :=
  ((List.range 4).flatMap fun e => (List.range 4).map fun p => (e, p)).filter fun c =>
    signalAllCodes.any fun g =>
      let f := SignalTriangulation.feedback { low := 0, mid := 1, high := 2 } g
      f.exact == c.1 && f.present == c.2

abbrev SIGNAL_CLASS_ALPHABET : String := "0123456789"

/-- The character naming a feedback class.  `?` for a class the list cannot name;
the validator refuses that character, so the failure is loud rather than folded. -/
def signalClassChar (f : SignalTriangulation.Feedback) : Char :=
  match signalClassPairs.findIdx? (fun c => c.1 == f.exact && c.2 == f.present) with
  | some i => SIGNAL_CLASS_ALPHABET.toList.getD i '?'
  | none => '?'

def signalRulesRow (target : SignalTriangulation.Code) : String :=
  String.ofList (signalAllCodes.map fun g =>
    signalClassChar (SignalTriangulation.feedback target g))

def signalRulesTable : List String := signalAllCodes.map signalRulesRow

/-- Decode a rendered class character back to the `solved` bit its class carries.
`none` for a character `class_alphabet` does not name — a `?` cell decodes to a
REFUSAL, not to `false`, so a silent fold cannot survive the decode either. -/
def signalClassSolved? (c : Char) : Option Bool :=
  match SIGNAL_CLASS_ALPHABET.toList.findIdx? (fun a => a == c) with
  | some i => (signalClassPairs[i]?).map fun pair => pair.1 == 3
  | none => none

/-- The cell an emitted descriptor actually carries at (target, guess): row indexed by
the target's position in `rules.codes`, column by the guess's — exactly the lookup
`transition.on_submit` (`"rules.table[instance][guess]"`) tells a client to perform.
This reads the EMITTED table; it does not recompute `signalClassChar`. -/
def signalRulesCell (target guess : SignalTriangulation.Code) : Option Char :=
  match signalAllCodes.findIdx? (fun c => c == target),
        signalAllCodes.findIdx? (fun c => c == guess) with
  | some r, some c => (signalRulesTable[r]?).bind fun row => row.toList[c]?
  | _, _ => none

/-- Nine realizable feedback classes. (Pinned `= true` in `EmitFixtures`.) -/
def check_signalClassPairs_length : Bool := decide (signalClassPairs.length = 9)

/-- No cell of the emitted table is `?`: the nine classes name every feedback the
rules can produce over the complete 216-by-216 domain.
(Pinned `= true` in `EmitFixtures`.) -/
def check_signalClassPairs_complete : Bool :=
  signalAllCodes.all fun t => signalAllCodes.all fun g =>
    signalClassPairs.contains
      ((SignalTriangulation.feedback t g).exact,
       (SignalTriangulation.feedback t g).present)

theorem signalRulesTable_length : signalRulesTable.length = 216 := by
  simp [signalRulesTable, signalAllCodes]

/-- ⚑ Every row of the emitted table solves at exactly one column, and that column
is the row's own index.  The table therefore names no instance: it is the whole
function, and no field of it distinguishes the live row.
(Pinned `= true` in `EmitFixtures`.) -/
def check_signal_every_row_solves_at_exactly_its_own_index : Bool :=
  signalAllCodes.all fun t =>
    (signalAllCodes.filter fun g => (SignalTriangulation.feedback t g).exact == 3).length == 1

/-- The kernel fact underneath the table.  ⚠ RENAMED 2026-08-05: this carried the name
`signalClass_matches_step` and a docstring claiming the emitted cell agrees with the
kernel step, while its statement mentioned neither `signalRulesTable` nor
`signalClassChar` nor the descriptor.  It is a fact about `SignalTriangulation` alone,
and it is now named that.  The claim the old name made is
`signalRulesCell_matches_step` below, and it is proved. -/
theorem step_solved_is_exact_three (cfg : SignalTriangulation.Config)
    (s : SignalTriangulation.State) (guess : SignalTriangulation.Code)
    (hopen : SignalTriangulation.openB s = true) :
    (SignalTriangulation.step cfg s (.submit guess)).map (·.solved) =
      some ((SignalTriangulation.feedback cfg.target guess).exact == 3) := by
  simp [SignalTriangulation.step, hopen]

/-- Over the WHOLE 216-by-216 domain, the cell the emitted table carries — read the way
a client reads it, and decoded through the emitted alphabet — is exactly the kernel's
own `solved` bit.  Finite and total, so it is `native_decide`; the ∀-form below carries
it off the list.

⚠ NAMED RESIDUE, the only `native_decide` left in this module.  It is the PREMISE of
`signalRulesCell_decodes_to_the_kernel_bit` and of the marquee
`signalRulesCell_matches_step`, both general theorems that belong in the emitter; moving
the evaluation to `EmitFixtures` would have moved those two statements out with it. -/
theorem signalRulesTable_cells_decode_to_the_kernel_bit :
    (signalAllCodes.all fun t => signalAllCodes.all fun g =>
      (signalRulesCell t g).bind signalClassSolved? ==
        some ((SignalTriangulation.feedback t g).exact == 3)) = true := by
  native_decide

theorem signalRulesCell_decodes_to_the_kernel_bit
    (target guess : SignalTriangulation.Code) :
    (signalRulesCell target guess).bind signalClassSolved? =
      some ((SignalTriangulation.feedback target guess).exact == 3) := by
  have h := signalRulesTable_cells_decode_to_the_kernel_bit
  simp only [List.all_eq_true] at h
  have hrow := h target (signalAllCodes_complete target)
  simpa using hrow guess (signalAllCodes_complete guess)

/-- ⚑ **The emitted cell IS the rule.**  What a client reads out of `rules.table` at
(its instance row, its guess column) and decodes through `class_alphabet` is exactly
the `solved` bit `SignalTriangulation.step` computes, from every open state.  This is
the statement the descriptor's `transition.on_submit` clause promises, made about the
actually emitted table rather than about `feedback` on its own. -/
theorem signalRulesCell_matches_step (cfg : SignalTriangulation.Config)
    (s : SignalTriangulation.State) (guess : SignalTriangulation.Code)
    (hopen : SignalTriangulation.openB s = true) :
    (SignalTriangulation.step cfg s (.submit guess)).map (·.solved) =
      (signalRulesCell cfg.target guess).bind signalClassSolved? := by
  rw [signalRulesCell_decodes_to_the_kernel_bit]
  exact step_solved_is_exact_three cfg s guess hopen

#assert_axioms signalAllCodes_complete
#assert_axioms signalRulesTable_length
#assert_axioms step_solved_is_exact_three
-- The named residue and its two general consequences; every other pin lives in
-- `EmitFixtures.lean`, rooted in `PathOfAngelsGuards` — see the header note above.
#assert_compiled signalRulesTable_cells_decode_to_the_kernel_bit
#assert_compiled signalRulesCell_decodes_to_the_kernel_bit
#assert_compiled signalRulesCell_matches_step

private def signalCodeJson (c : SignalTriangulation.Code) : String :=
  "[" ++ toString c.low.val ++ "," ++ toString c.mid.val ++ "," ++
    toString c.high.val ++ "]"

private def signalClassJson (c : Nat × Nat) : String :=
  "{\"exact\":" ++ toString c.1 ++ ",\"present\":" ++ toString c.2 ++
    ",\"solved\":" ++ jsonBool (c.1 == 3) ++ "}"

def signalDescriptorJson : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"signal-triangulation\",\n" ++
  "  \"ruleset\":\"signal-v2\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.SignalTriangulation\",\n" ++
  "  \"action_limit\":" ++ toString SignalTriangulation.MAX_TURNS ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"oracle-only\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ instanceDeclarationJson "oracle-only" (symbolDrawJson "rejection" [6, 6, 6]) ++ ",\n" ++
  "  \"state\":{\"fields\":[\"turns\",\"solved\",\"last_feedback\"]},\n" ++
  "  \"action\":{\"tag\":\"submit\",\"code\":{\"bands\":3,\"alphabet\":6}},\n" ++
  "  \"feedback\":{\"exact_max\":3,\"present_max\":3,\"exact_plus_present_max\":3," ++
    "\"present_semantics\":\"multiplicity_intersection_minus_exact\",\"solved_when_exact\":3},\n" ++
  "  \"transition\":{\"open_when\":{\"solved\":false,\"turns_lt\":5}," ++
    "\"on_submit\":{\"lookup\":\"rules.table[instance][guess]\",\"turns\":\"increment\"," ++
    "\"solved\":\"class.solved\",\"last_feedback\":[\"class.exact\",\"class.present\"]}," ++
    "\"refuse_when\":[\"solved\",\"turns_gte_action_limit\"]},\n" ++
  "  \"output\":{\"requires\":\"solved\",\"contribution\":\"mission_reward\",\"artifact\":\"mission_artifact\"},\n" ++
  "  \"rules\":{\"class_alphabet\":" ++ jsonString SIGNAL_CLASS_ALPHABET ++
    ",\"classes\":" ++ jsonArray (signalClassPairs.map signalClassJson) ++
    ",\"codes\":" ++ jsonArray (signalAllCodes.map signalCodeJson) ++
    ",\"table\":" ++ jsonPrettyArray (signalRulesTable.map fun row => "    " ++ jsonString row) ++
    "}\n" ++
  "}\n"

/-! ## Finite-table descriptors -/

/-! ### Two demonstration secrets, and what they refute

The descriptor is a constant.  Proving "a constant does not depend on the seed" is
`rfl` and says nothing, so the claim is made the other way round: with everything
an artifact carries held FIXED — mission, federation, content session, slot,
player — two slot secrets draw two different instances.  A reader of the artifact
therefore cannot name the instance, not even up to the domain.

These are demonstration values.  They are not the deployment's secrets: a
deployment secret never enters this module, and there is no function here that
would render one. -/

private def demoSecret (tag : Nat) : HiddenInstance.SlotSecret :=
  ⟨taggedBytes32 [68, 69, 77, 79, tag]⟩

private def demoPlayer : Digest32 := taggedBytes32 [80, 76, 65, 89, 69, 82]
private def demoSlot : EpochId := ⟨11⟩

/-- The live seed a run would draw.  `mission` is the template the catalog carries,
so every published value is fixed and only the secret moves. -/
private def demoLiveSeed (mission : MissionSpec) (tag : Nat) : Digest32 :=
  HiddenInstance.runSeedFor ⟨demoSecret tag, demoSlot, demoPlayer⟩
    (HiddenInstance.MissionContext.ofMission mission)

private def relayStateJson (board : RelayRepair.Board) (state : RelayRepair.State) : String :=
  "    {\"id\":" ++ jsonString (FiniteTables.relayStateId state) ++
    ",\"terminal\":" ++ jsonBool (RelayRepair.routedB state.panel) ++
    ",\"view\":{\"installed\":" ++
      jsonArray ((FiniteTables.relayInstalledActionIds state.panel).map jsonString) ++
    ",\"spares\":" ++ toString (RelayRepair.sparesLeft board state.panel) ++
    ",\"turns\":" ++ toString state.turns ++
    ",\"solved\":" ++ jsonBool (RelayRepair.routedB state.panel) ++
    ",\"stranded\":" ++ jsonBool (RelayRepair.strandedB board state) ++ "}}"

private def relayActionJson (action : RelayRepair.Action) : String :=
  "    {\"id\":" ++ jsonString (FiniteTables.relayActionId action) ++
    ",\"label\":" ++ jsonString (FiniteTables.relayActionLabel action) ++
    ",\"from\":" ++ jsonString (FiniteTables.relayActionFrom action) ++
    ",\"to\":" ++ jsonString (FiniteTables.relayActionTo action) ++ "}"

private def relayTransitionJson (board : RelayRepair.Board)
    (transition : FiniteTables.RelayTransition) : String :=
  let nextId := transition.next.map FiniteTables.relayStateId
  let reason := FiniteTables.relayRefusalReason board transition.state transition.action
  "    {\"state\":" ++ jsonString (FiniteTables.relayStateId transition.state) ++
    ",\"action\":" ++ jsonString (FiniteTables.relayActionId transition.action) ++
    ",\"verdict\":" ++ jsonString (if nextId.isSome then "accept" else "refuse") ++
    ",\"next\":" ++ (match nextId with | none => "null" | some id => jsonString id) ++
    ",\"reason\":" ++ (match reason with | none => "null" | some value => jsonString value) ++ "}"

private def relayBoardJson (index : Nat) (board : RelayRepair.Board) : String :=
  "    {\"index\":" ++ toString index ++
    ",\"spares\":" ++ toString board.spares ++
    ",\"costs\":{" ++ String.intercalate "," (FiniteTables.relayActions.map fun action =>
      jsonString (FiniteTables.relayActionId action) ++ ":" ++
        toString (RelayRepair.cost board action)) ++ "}}"

/-- The whole board FAMILY and no draw.  ⚠ `seed_byte` and `selected` are GONE:
they said which board was live, and the run seed they were answerable to was
published beside them, so between them they printed the instance twice.

Relay is a perfect-information puzzle — its player has to read the damage report
to play at all — so its instance is DISCLOSED, to its own player, at run start,
through the run opening.  What the split changes is that it is disclosed per run
instead of printed once for everyone, which is what kills the memorised line.  The
family stays public because the family is the rules. -/
private def relayInstanceJson : String :=
  "{\"modulus\":8" ++
    ",\"source\":\"alpha\",\"sink\":\"omega\"" ++
    ",\"draw\":" ++ instanceDeclarationJson "per-run-open" (symbolDrawJson "modulo" [8]) ++
    ",\"boards\":" ++ jsonPrettyArray
      ((List.finRange 8).map fun index =>
        relayBoardJson index.val (RelayRepair.boardAt index)) ++
    "}"

private def relayMachineJson (index : Fin 8) : String :=
  let board := RelayRepair.boardAt index
  let states := FiniteTables.relayStates board
  let transitions := FiniteTables.relayTransitions board
  "    {\"board\":" ++ toString index.val ++
    ",\"states\":" ++ jsonPrettyArray (states.map (relayStateJson board)) ++
    ",\"transitions\":" ++
      jsonPrettyArray (transitions.map (relayTransitionJson board)) ++ "}"

def relayDescriptorJson : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"relay-repair\",\n" ++
  "  \"ruleset\":\"relay-v3\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.RelayRepair\",\n" ++
  "  \"action_limit\":" ++ toString RelayRepair.MAX_TURNS ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"per-run-open\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ relayInstanceJson ++ ",\n" ++
  "  \"state_machine\":{\n" ++
  "    \"initial_state\":" ++ jsonString (FiniteTables.relayStateId RelayRepair.initialState) ++ ",\n" ++
  "    \"actions\":" ++ jsonPrettyArray (FiniteTables.relayActions.map relayActionJson) ++ ",\n" ++
  "    \"machines\":" ++
    jsonPrettyArray ((List.finRange 8).map relayMachineJson) ++ "\n" ++
  "  },\n" ++
  "  \"output\":{\"requires\":\"terminal\",\"contribution\":\"mission_reward\"," ++
    "\"artifact\":\"mission_artifact\"}\n" ++
  "}\n"

private def salvageStateJson (state : SalvageLock.State) : String :=
  let exposed := match state.exposed with
    | none => "null"
    | some slot => toString slot.val
  "    {\"id\":" ++ jsonString (FiniteTables.salvageStateId state) ++
    ",\"terminal\":" ++ jsonBool (SalvageLock.solvedB state) ++
    ",\"view\":{\"cleared\":" ++
      jsonArray ((FiniteTables.salvageClearedSlots state).map (toString ·.val)) ++
    ",\"exposed\":" ++ exposed ++
    ",\"turns\":" ++ toString state.turns ++
    ",\"solved\":" ++ jsonBool (SalvageLock.solvedB state) ++ "}}"

/-- ⚠ `glyph_id` and `glyph_label` are GONE.  They named the glyph under each
plate, which is the whole board.  Removing them alone would have hidden nothing —
the successors said which exposures clear — which is why the transition rows below
changed shape at the same time. -/
private def salvageActionJson (action : SalvageLock.Action) : String :=
  "    {\"id\":" ++ jsonString (FiniteTables.salvageActionId action) ++
    ",\"label\":" ++ jsonString (FiniteTables.salvageActionLabel action) ++
    ",\"slot\":" ++ toString (SalvageLock.actionSlot action).val ++ "}"

/-- A parametric row.  `refuse` carries a reason and no successor; `accept` is a
first exposure and carries one; `resolve` is a second exposure and carries BOTH,
so the row states the rule and the judge's single bit states the instance. -/
private def salvageTransitionJson (transition : FiniteTables.ParametricTransition) : String :=
  let stateId := jsonString (FiniteTables.salvageStateId transition.state)
  let actionId := jsonString (FiniteTables.salvageActionId transition.action)
  let head :=
    "    {\"state\":" ++ stateId ++ ",\"action\":" ++ actionId ++ ",\"verdict\":"
  match transition.row with
  | .refuse reason =>
      head ++ "\"refuse\",\"reason\":" ++ jsonString reason ++
        ",\"next\":null,\"on_match\":null,\"on_mismatch\":null}"
  | .advance next =>
      head ++ "\"accept\",\"reason\":null,\"next\":" ++
        jsonString (FiniteTables.salvageStateId next) ++
        ",\"on_match\":null,\"on_mismatch\":null}"
  | .resolve onMatch onMismatch =>
      head ++ "\"resolve\",\"reason\":null,\"next\":null,\"on_match\":" ++
        jsonString (FiniteTables.salvageStateId onMatch) ++
        ",\"on_mismatch\":" ++ jsonString (FiniteTables.salvageStateId onMismatch) ++ "}"

/-- The whole ninety-board FAMILY, emitted so a browser can answer its OWN
practice run without carrying a second copy of `pairsOf` and `glyphNamesOf`.

Publishing the family is not publishing the instance.  The family was already
public — "six plates carrying two copies of each of three glyphs" determines it
completely, and `SalvageLock.seed_space_is_exactly_the_two_of_each_boards` proves
the ninety are exactly those boards.  What a reader cannot do is say which one a
given run drew.

A practice run picks a row here under a client-chosen seed and answers its own
match queries from it.  A judged run never touches this block: its bit comes from
the judge. -/
private def salvagePracticeBoardsJson : String :=
  jsonPrettyArray ((List.finRange SalvageLock.SEED_SPACE).map fun seed =>
    "    " ++ jsonArray ((SalvageLock.boardRow seed).map (toString ·.val)))

def salvageDescriptorJson : String :=
  let states := FiniteTables.salvageParametricStates
  let actions := FiniteTables.salvageActions
  let transitions := FiniteTables.salvageParametricTransitions
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"salvage-lock\",\n" ++
  "  \"ruleset\":\"salvage-v2\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.SalvageLock\",\n" ++
  "  \"action_limit\":" ++ toString SalvageLock.MAX_TURNS ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"oracle-only\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ instanceDeclarationJson "oracle-only" (symbolDrawJson "rejection" [5, 3, 3]) ++ ",\n" ++
  "  \"state_machine\":{\n" ++
  "    \"initial_state\":" ++ jsonString (FiniteTables.salvageStateId SalvageLock.initialState) ++ ",\n" ++
  "    \"states\":" ++ jsonPrettyArray (states.map salvageStateJson) ++ ",\n" ++
  "    \"actions\":" ++ jsonPrettyArray (actions.map salvageActionJson) ++ ",\n" ++
  "    \"transitions\":" ++ jsonPrettyArray (transitions.map salvageTransitionJson) ++ "\n" ++
  "  },\n" ++
  "  \"practice\":{\"instance_space\":" ++ toString SalvageLock.SEED_SPACE ++
    ",\"instance_shape\":\"two copies of each of three glyphs over six plates\"" ++
    ",\"scored\":false" ++
    ",\"boards\":" ++ salvagePracticeBoardsJson ++ "},\n" ++
  "  \"output\":{\"requires\":\"terminal\",\"contribution\":\"mission_reward\"," ++
    "\"artifact\":\"mission_artifact\"}\n" ++
  "}\n"

/-! ## Black Box Reconstruction — the ORACLE wire

Signal publishes a code-by-code feedback table; Salvage publishes a machine whose
second exposures name both branches.  Black Box can use neither shape.  Its state
is the SET of pairs a run has asked, so a total `(state, action)` table would have
`2^25` rows and cannot be written down at all.

What is small is the thing that actually matters: the ORACLE.  120 instances by 25
probes is 3000 cells, and those cells ARE the rules.  So the descriptor publishes
the complete question-and-answer function and says nothing whatever about which row
a given run drew — the client learns every rule and no instance.

`blackBox_table_is_the_kernel` reads the cells back out of the RENDERED descriptor
and compares each one against `BlackBoxReconstruction.hitB`, so the emitted table is
a projection of the kernel and not a second copy of the rules. -/

private def blackBoxProbes :
    List (BlackBoxReconstruction.Slot × BlackBoxReconstruction.Fragment) :=
  BlackBoxReconstruction.allSlots.flatMap fun slot =>
    BlackBoxReconstruction.allFragments.map fun fragment => (slot, fragment)

private def blackBoxProbeId
    (probe : BlackBoxReconstruction.Slot × BlackBoxReconstruction.Fragment) : String :=
  "probe-" ++ toString probe.1.val ++ "-" ++ toString probe.2.val

private def blackBoxProbeJson
    (probe : BlackBoxReconstruction.Slot × BlackBoxReconstruction.Fragment) : String :=
  "    {\"id\":" ++ jsonString (blackBoxProbeId probe) ++
    ",\"label\":" ++ jsonString ("Ask where position " ++ toString probe.1.val ++
      " sits relative to fragment " ++ toString probe.2.val) ++
    ",\"slot\":" ++ toString probe.1.val ++
    ",\"fragment\":" ++ toString probe.2.val ++ "}"

/-- One instance's answers to every probe, in `blackBoxProbes` order. -/
private def blackBoxOracleRow (order : Fin BlackBoxReconstruction.ORDER_SPACE) : String :=
  String.mk (blackBoxProbes.map fun probe =>
    (BlackBoxReconstruction.answerOf order probe).code)

private def blackBoxOracleTableJson : String :=
  jsonPrettyArray ((List.finRange BlackBoxReconstruction.ORDER_SPACE).map fun order =>
    "    " ++ jsonString (blackBoxOracleRow order))

private def blackBoxActionId (a : BlackBoxReconstruction.Action) : String :=
  blackBoxProbeId a.pair

/-- One refusal witness on the wire: the instance, the legal prefix, the further
probe, and the reason the kernel reports at it.  ⚠ The gate does NOT take the
reason on trust — it replays the prefix against the emitted oracle table and
re-derives the reason from the declared `settles` semantics.  A disagreement is a
hard failure there, which is the whole point of shipping the witness. -/
private def blackBoxWitnessJson (w : BlackBoxReconstruction.RefusalWitness) : String :=
  "    {\"reason\":" ++ jsonString w.reason.tag ++
    ",\"instance\":" ++ toString w.order.val ++
    ",\"history\":" ++ jsonArray (w.history.map (fun a => jsonString (blackBoxActionId a))) ++
    ",\"probe\":" ++ jsonString (blackBoxActionId w.probe) ++ "}"

private def blackBoxWitnessesJson : String :=
  jsonPrettyArray (BlackBoxReconstruction.refusalWitnesses.map blackBoxWitnessJson)

def blackBoxDescriptorJson : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"black-box-reconstruction\",\n" ++
  "  \"ruleset\":\"blackbox-v2\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.BlackBoxReconstruction\",\n" ++
  "  \"action_limit\":" ++ toString BlackBoxReconstruction.MAX_TURNS ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"oracle-only\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ instanceDeclarationJson "oracle-only" (symbolDrawJson "rejection" [5, 4, 3, 2]) ++ ",\n" ++
  "  \"oracle\":{\n" ++
  "    \"instance_space\":" ++ toString BlackBoxReconstruction.ORDER_SPACE ++ ",\n" ++
  "    \"instance_shape\":\"a permutation of five fragments over five positions\",\n" ++
  "    \"required_per_instance\":" ++ toString BlackBoxReconstruction.SLOT_COUNT ++ ",\n" ++
  "    \"settles\":\"slot-and-fragment\",\n" ++
  "    \"class_alphabet\":\"012\",\n" ++
  "    \"classes\":[{\"id\":\"earlier\",\"solving\":false}," ++
    "{\"id\":\"placed\",\"solving\":true}," ++
    "{\"id\":\"later\",\"solving\":false}],\n" ++
  "    \"probes\":" ++ jsonPrettyArray (blackBoxProbes.map blackBoxProbeJson) ++ ",\n" ++
  "    \"table\":" ++ blackBoxOracleTableJson ++ "\n" ++
  "  },\n" ++
  "  \"refusals\":" ++
    jsonArray (BlackBoxReconstruction.allRefusals.map
      (fun r => jsonString r.tag)) ++ ",\n" ++
  "  \"refusal_precedence\":\"first-applicable-in-declared-order\",\n" ++
  "  \"refusal_witnesses\":" ++ blackBoxWitnessesJson ++ ",\n" ++
  "  \"output\":{\"requires\":\"terminal\",\"contribution\":\"mission_reward\"," ++
    "\"artifact\":\"mission_artifact\"}\n" ++
  "}\n"

/-! Strict schema checks for the exact finite-table wire. -/

/-! ⚠ `run_seed` is no longer a descriptor key and `target_visibility` is no longer
a security key; `instance` is now required of every game.  The validators below
refuse the old shape rather than reinterpreting it, so a stale artifact fails to
load instead of being read as a hidden-instance one. -/

private def validateRelayTransitions (machine : Json) : Except String Unit := do
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  for transition in transitions do
    exactKeys transition ["state", "action", "verdict", "next", "reason"]

/-- ⚠ `seed_byte` and `selected` are refused, not ignored.  A relay descriptor that
still names a drawn board is the old shape and must not load. -/
private def validateRelayInstance (document : Json) : Except String Unit := do
  let block ← document.getObjVal? "instance"
  exactKeys block ["modulus", "source", "sink", "draw", "boards"]
  validateInstanceDeclaration (← block.getObjVal? "draw") "per-run-open"
  let modulus ← block.getObjValAs? Nat "modulus"
  let boards ← (block.getObjVal? "boards") >>= Json.getArr?
  if boards.size != modulus then
    throw s!"POAG1 relay instance declares {boards.size} boards for modulus {modulus}"
  let linkIds := FiniteTables.relayActions.map FiniteTables.relayActionId
  for board in boards do
    exactKeys board ["index", "spares", "costs"]
    exactKeys (← board.getObjVal? "costs") linkIds

def validateRelayDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  -- Relay's declaration lives inside `instance.draw`, so the outer instance block
  -- is checked by `validateRelayInstance` and the common check is told the shape.
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "state_machine", "output"]
  validateHiddenSecurity document "per-run-open"
  validateRelayInstance document
  let machine ← document.getObjVal? "state_machine"
  exactKeys machine ["initial_state", "actions", "machines"]
  exactKeys (← document.getObjVal? "output") ["requires", "contribution", "artifact"]
  let actions ← (machine.getObjVal? "actions") >>= Json.getArr?
  for action in actions do
    exactKeys action ["id", "label", "from", "to"]
  let machines ← (machine.getObjVal? "machines") >>= Json.getArr?
  if machines.size != 8 then
    throw s!"POAG1 relay emits {machines.size} board machines, expected 8"
  for board in machines do
    exactKeys board ["board", "states", "transitions"]
    let states ← (board.getObjVal? "states") >>= Json.getArr?
    for state in states do
      exactKeys state ["id", "terminal", "view"]
      exactKeys (← state.getObjVal? "view")
        ["installed", "spares", "turns", "solved", "stranded"]
    validateRelayTransitions board

def validateSalvageDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "state_machine", "practice", "output"]
  validateHiddenSecurity document "oracle-only"
  validateInstanceDeclaration (← document.getObjVal? "instance") "oracle-only"
  let practice ← document.getObjVal? "practice"
  exactKeys practice ["instance_space", "instance_shape", "scored", "boards"]
  let space ← practice.getObjValAs? Nat "instance_space"
  let boards ← (practice.getObjVal? "boards") >>= Json.getArr?
  if boards.size != space then
    throw s!"POAG1 salvage practice block emits {boards.size} boards for a space of {space}"
  let machine ← document.getObjVal? "state_machine"
  exactKeys machine ["initial_state", "states", "actions", "transitions"]
  exactKeys (← document.getObjVal? "output") ["requires", "contribution", "artifact"]
  let states ← (machine.getObjVal? "states") >>= Json.getArr?
  for state in states do
    exactKeys state ["id", "terminal", "view"]
    exactKeys (← state.getObjVal? "view") ["cleared", "exposed", "turns", "solved"]
  let actions ← (machine.getObjVal? "actions") >>= Json.getArr?
  for action in actions do
    -- No `glyph_id`: an action row that carries one is the old shape and refuses.
    exactKeys action ["id", "label", "slot"]
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  for transition in transitions do
    exactKeys transition ["state", "action", "verdict", "reason", "next",
      "on_match", "on_mismatch"]

/-- Black Box publishes an `oracle` block instead of a `state_machine`: its state
space is a subset lattice and no total transition table exists for it.  The key set
is pinned exactly, like every other descriptor here. -/
def validateBlackBoxDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "oracle", "refusals", "refusal_precedence",
    "refusal_witnesses", "output"]
  validateHiddenSecurity document "oracle-only"
  validateInstanceDeclaration (← document.getObjVal? "instance") "oracle-only"
  exactKeys (← document.getObjVal? "output") ["requires", "contribution", "artifact"]
  let declared ← (document.getObjVal? "refusals") >>= Json.getArr?
  if declared.size != BlackBoxReconstruction.allRefusals.length then
    throw s!"POAG1 black-box declares {declared.size} refusal reasons"
  let witnesses ← (document.getObjVal? "refusal_witnesses") >>= Json.getArr?
  if witnesses.size != declared.size then
    throw s!"POAG1 black-box carries {witnesses.size} refusal witnesses for \
      {declared.size} declared reasons"
  for witness in witnesses do
    exactKeys witness ["reason", "instance", "history", "probe"]
  let oracle ← document.getObjVal? "oracle"
  exactKeys oracle ["instance_space", "instance_shape", "required_per_instance",
    "settles", "class_alphabet", "classes", "probes", "table"]
  let space ← oracle.getObjValAs? Nat "instance_space"
  if space != BlackBoxReconstruction.ORDER_SPACE then
    throw s!"POAG1 black-box declares an instance space of {space}"
  let probes ← (oracle.getObjVal? "probes") >>= Json.getArr?
  if probes.size != blackBoxProbes.length then
    throw s!"POAG1 black-box emits {probes.size} probes"
  for probe in probes do
    exactKeys probe ["id", "label", "slot", "fragment"]
  let classes ← (oracle.getObjVal? "classes") >>= Json.getArr?
  -- ⚠ THREE since 2026-08-09.  A descriptor still carrying the two-class
  -- `mismatch`/`match` alphabet is the pre-repair shape and must not load: its
  -- table cannot say which SIDE of a named fragment the held one is on, which is
  -- the whole of the information the budget of eleven is priced against.
  if classes.size != BlackBoxReconstruction.allAnswers.length then
    throw s!"POAG1 black-box emits {classes.size} observation classes, expected \
      {BlackBoxReconstruction.allAnswers.length}"
  for cls in classes do
    exactKeys cls ["id", "solving"]
  let table ← (oracle.getObjVal? "table") >>= Json.getArr?
  if table.size != space then
    throw s!"POAG1 black-box emits {table.size} oracle rows for a space of {space}"

/-- ⚑ **The emitted oracle is the kernel's, cell by cell.**  This reads the table
back out of the RENDERED descriptor — the bytes a client actually fetches — and
compares all 3000 cells against `BlackBoxReconstruction.answerOf` — the whole
three-class answer, not just whether it settled.  Without it the artifact would be
an unchecked second statement of the rules, and a table that lost `earlier` /
`later` would still look well-formed. -/
def blackBoxTableRefinesKernel : Except String Unit := do
  let document ← Json.parse blackBoxDescriptorJson
  let oracle ← document.getObjVal? "oracle"
  let table ← (oracle.getObjVal? "table") >>= Json.getArr?
  for order in List.finRange BlackBoxReconstruction.ORDER_SPACE do
    match table[order.val]? with
    | none => throw s!"POAG1 black-box table has no row {order.val}"
    | some cell =>
        let row ← cell.getStr?
        let chars := row.toList
        if chars.length != blackBoxProbes.length then
          throw s!"POAG1 black-box row {order.val} is {chars.length} cells wide"
        for pair in blackBoxProbes.zip chars do
          if pair.2 != (BlackBoxReconstruction.answerOf order pair.1).code then
            throw s!"POAG1 black-box cell ({order.val}, {blackBoxProbeId pair.1}) \
              disagrees with the kernel"

private def blackBoxProbeOfId? (id : String) : Option BlackBoxReconstruction.Action :=
  (blackBoxProbes.find? (fun p => blackBoxProbeId p == id)).map
    (fun p => BlackBoxReconstruction.Action.probe p.1 p.2)

/-- ⚑ **The emitted refusal witnesses are the kernel's.**  Reads the witnesses back
out of the RENDERED descriptor, replays each prefix through `BlackBoxReconstruction.
replay`, and requires the kernel's own `refusal?` to report exactly the reason the
wire claims — and every declared reason to have a witness.  Without this the
witnesses would be a second, unchecked statement of which rules exist, which is the
shape the oracle table was already given a weld against. -/
def blackBoxWitnessesRefineKernel : Except String Unit := do
  let document ← Json.parse blackBoxDescriptorJson
  let witnesses ← (document.getObjVal? "refusal_witnesses") >>= Json.getArr?
  let declared ← (document.getObjVal? "refusals") >>= Json.getArr?
  let mut seen : List String := []
  for witness in witnesses do
    let reason ← witness.getObjValAs? String "reason"
    let row ← witness.getObjValAs? Nat "instance"
    if h : row < BlackBoxReconstruction.ORDER_SPACE then
      let order : Fin BlackBoxReconstruction.ORDER_SPACE := ⟨row, h⟩
      let historyJson ← (witness.getObjVal? "history") >>= Json.getArr?
      let mut history : List BlackBoxReconstruction.Action := []
      for entry in historyJson do
        let id ← entry.getStr?
        match blackBoxProbeOfId? id with
        | none => throw s!"POAG1 black-box witness names an unknown probe {id}"
        | some action => history := history ++ [action]
      let probeId ← witness.getObjValAs? String "probe"
      match blackBoxProbeOfId? probeId with
      | none => throw s!"POAG1 black-box witness names an unknown probe {probeId}"
      | some probe =>
          match BlackBoxReconstruction.replay order
              BlackBoxReconstruction.initialState history with
          | none => throw s!"POAG1 black-box witness for {reason} has an illegal prefix"
          | some state =>
              match BlackBoxReconstruction.refusal? order state probe with
              | none =>
                  throw s!"POAG1 black-box witness for {reason} ends in an ACCEPTED probe"
              | some fired =>
                  if fired.tag != reason then
                    throw s!"POAG1 black-box witness claims {reason}; the kernel \
                      reports {fired.tag}"
                  seen := seen ++ [reason]
    else
      throw s!"POAG1 black-box witness names instance {row}, outside the space"
  for entry in declared do
    let tag ← entry.getStr?
    if !seen.contains tag then
      throw s!"POAG1 black-box declares refusal {tag} and witnesses it nowhere"

/-- Signal's descriptor is validated the same way, with the rules table checked for
the one thing that could silently fold: an unnameable class rendering as `?`. -/
def validateSignalDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "state", "action", "feedback", "transition",
    "output", "rules"]
  validateHiddenSecurity document "oracle-only"
  validateInstanceDeclaration (← document.getObjVal? "instance") "oracle-only"
  let rules ← document.getObjVal? "rules"
  exactKeys rules ["class_alphabet", "classes", "codes", "table"]
  let alphabet ← rules.getObjValAs? String "class_alphabet"
  let classes ← (rules.getObjVal? "classes") >>= Json.getArr?
  for cls in classes do
    exactKeys cls ["exact", "present", "solved"]
  let codes ← (rules.getObjVal? "codes") >>= Json.getArr?
  let table ← (rules.getObjVal? "table") >>= Json.getArr?
  if table.size != codes.size then
    throw s!"POAG1 signal rules table has {table.size} rows for {codes.size} codes"
  let allowed := (alphabet.toList.take classes.size)
  for row in table do
    let text ← row.getStr?
    if text.length != codes.size then
      throw "POAG1 signal rules row is not one cell per code"
    if !text.toList.all (fun c => allowed.contains c) then
      throw "POAG1 signal rules table names a class outside the declared alphabet"

/-- The rendered relay descriptor satisfies its own strict schema.
(Pinned `= true` in `EmitFixtures`.) -/
def check_relayDescriptor_exact_schema : Bool :=
  decide (validateRelayDescriptor relayDescriptorJson = .ok ())

/-- (Pinned `= true` in `EmitFixtures`.) -/
def check_blackBoxDescriptor_exact_schema : Bool :=
  decide (validateBlackBoxDescriptor blackBoxDescriptorJson = .ok ())

/-- ⚑ All 3000 cells of the RENDERED oracle agree with `BlackBoxReconstruction.hitB`.
(Pinned `= true` in `EmitFixtures`.) -/
def check_blackBox_table_is_the_kernel : Bool :=
  decide (blackBoxTableRefinesKernel = .ok ())

/-- ⚑ Every rendered refusal witness replays to the reason the kernel reports.
(Pinned `= true` in `EmitFixtures`.) -/
def check_blackBox_witnesses_are_the_kernel : Bool :=
  decide (blackBoxWitnessesRefineKernel = .ok ())

/-- (Pinned `= true` in `EmitFixtures`.) -/
def check_salvageDescriptor_exact_schema : Bool :=
  decide (validateSalvageDescriptor salvageDescriptorJson = .ok ())

/-- (Pinned `= true` in `EmitFixtures`.) -/
def check_signalDescriptor_exact_schema : Bool :=
  decide (validateSignalDescriptor signalDescriptorJson = .ok ())

def signalBudget : ContributionBudget :=
  { intel := ⟨25, by decide⟩
    supplies := ⟨15, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨500, by decide⟩
    relics := ⟨1, by decide⟩ }

def signalReward : Contribution :=
  { intel := ⟨25, by decide⟩
    supplies := ⟨15, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨500, by decide⟩
    relics := {relicSlot ⟨1⟩ 0}
    relics_bounded := by decide }

theorem signalReward_within : signalReward.within signalBudget = true := by
  decide

#assert_axioms signalReward_within

def signalArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨1⟩
    artifactId := ⟨1⟩
    sourceDigest := sourceDigest
    contentDigest := contentDigest }

/-- ⚠ `runSeed` is now a PARAMETER.  Missions rendered into the catalog are given
`UNBOUND_RUN_SEED`; a judge is given `HiddenInstance.runSeedFor draw mission`.
There is no longer a mission whose seed is a constant of this module. -/
def signalMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨1⟩
    artifact := signalArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId := federationId
    contentRoot := contentRoot
    activationDigest := activationDigest
    contentSession := signalContentSession
    runSeed := runSeed
    budget := signalBudget
    allowedRelics := {relicSlot ⟨1⟩ 0}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by decide }

/-- The draw context of a Signal mission does not depend on its run seed.  Stated on
the ACTUAL emitter and over OPEN digests, so a caller that needs it does not have to
close a `rfl` that would evaluate a digest to check it — which is what a node fixture
deriving its own live seed would otherwise be asking the kernel to do. -/
theorem signalMission_context_ignores_the_run_seed
    (runSeed runSeed' federationId sourceDigest contentDigest contentRoot
      activationDigest : Digest32) :
    HiddenInstance.MissionContext.ofMission
        (signalMission runSeed federationId sourceDigest contentDigest contentRoot
          activationDigest) =
      HiddenInstance.MissionContext.ofMission
        (signalMission runSeed' federationId sourceDigest contentDigest contentRoot
          activationDigest) := rfl

theorem signalReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (signalMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution signalReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  constructor
  · exact signalReward_within
  · simp [signalMission, signalReward]

/-! ### Building a Signal configuration

⚑ **THE DRAW IS PARTIAL, AND THIS IS WHERE THAT IS ABSORBED.**
`SignalTriangulation.targetFromSeed?` can refuse (216 ∤ 2^256; see its docblock),
so there are exactly two honest ways to obtain a `Config` and both are here:

* `signalConfigWith` — the caller ALREADY HOLDS a target and a measurement of it.
  Total, and it reduces over whatever the caller measured.  This is what a fixture
  uses: it CARRIES the target its seed was measured to draw, so nothing downstream
  has to reduce the draw — or, when the seed is a sponge output, the sponge.
* `signalConfig?` — the caller holds only a seed.  The measurement comes from the
  `match` discriminant, so this costs no evaluation either; the caller pays by
  handling `none`.

There is no third one.  In particular there is no `signalConfig : … → Config`:
a total constructor could only exist by inventing a target for a refused seed. -/

/-- A configuration built around a target the caller has ALREADY measured.  The
measurement is the argument `htarget`, so this function neither performs nor
assumes a draw. -/
def signalConfigWith (runSeed : Digest32) (target : SignalTriangulation.Code)
    (htarget : some target = SignalTriangulation.targetFromSeed? runSeed)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    SignalTriangulation.Config :=
  { target := target
    mission := signalMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest
    reward := signalReward
    reward_accepted := signalReward_accepted runSeed federationId sourceDigest contentDigest
      contentRoot activationDigest
    target_eq := htarget }

/-- The configuration a seed determines, or `none` if the seed draws no instance.
The `match` binding IS the proof of `target_eq`; the same shape
`blackBoxConfig?` uses. -/
def signalConfig? (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option SignalTriangulation.Config :=
  match htarget : SignalTriangulation.targetFromSeed? runSeed with
  | none => none
  | some target =>
      some (signalConfigWith runSeed target htarget.symm federationId sourceDigest
        contentDigest contentRoot activationDigest)

/-- The judged target is the one the LIVE seed draws, for whatever seed the judge
was handed.  The kernel binding did not change; the seed did. -/
theorem signalConfig_target_from_live_seed (runSeed : Digest32)
    (target : SignalTriangulation.Code)
    (htarget : some target = SignalTriangulation.targetFromSeed? runSeed)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    some (signalConfigWith runSeed target htarget federationId sourceDigest contentDigest
      contentRoot activationDigest).target =
      SignalTriangulation.targetFromSeed?
        (signalConfigWith runSeed target htarget federationId sourceDigest contentDigest
          contentRoot activationDigest).mission.runSeed := htarget

/-- Whatever `signalConfig?` returns carries the draw of the seed it was given —
so a caller that goes through it cannot install a target of its own. -/
theorem signalConfig?_target_is_the_draw (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32)
    {cfg : SignalTriangulation.Config}
    (h : signalConfig? runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest = some cfg) :
    some cfg.target = SignalTriangulation.targetFromSeed? runSeed := by
  unfold signalConfig? at h
  split at h
  · contradiction
  · rename_i target htarget
    simp only [Option.some.injEq] at h
    subst h
    exact htarget.symm

/-- ⚑ `signalConfig?` REFUSES a seed the draw refuses.  Without this the partiality
could be decorative — a `none` branch nothing reaches. -/
theorem signalConfig?_refuses_a_refused_seed (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32)
    (h : SignalTriangulation.targetFromSeed? runSeed = none) :
    signalConfig? runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest = none := by
  unfold signalConfig?
  split
  · rfl
  · rename_i target htarget
    rw [h] at htarget
    exact absurd htarget (by simp)

/-! ### The template configuration

A catalog mission has no instance, so it carries `UNBOUND_RUN_SEED` — thirty-two
zero bytes.  Zero is below `SeedDraw.ceilingFor 6 = 252`, so the draw ACCEPTS it
and the template is a genuine configuration of a genuine instance rather than a
special case: `signalTemplateConfig` is total and kernel-clean, and every consumer
that used to build a template with `signalConfig UNBOUND_RUN_SEED …` still gets a
total `Config` with no `Option` and no `native_decide`.

⚠ That instance is `[0,0,0]`, which is in the `aaa` class the design gate reports
as unable to win within the budget.  That is not a fallback and not a regression —
it is what the all-zero seed has always drawn, and `Judged.admissionChecks` refuses
`UNBOUND_RUN_SEED` outright, so it is never played.  The value is reachable ONLY by
the template, never by a live draw. -/

/-- The all-zero seed's draw. -/
def UNBOUND_TARGET : SignalTriangulation.Code := { low := 0, mid := 0, high := 0 }

/-- MEASURED, in the kernel: the template's target is what the template's seed draws.
This is `signalTemplateConfig`'s `target_eq` and it costs no compiled evaluation. -/
theorem unbound_target_is_the_unbound_draw :
    some UNBOUND_TARGET = SignalTriangulation.targetFromSeed? UNBOUND_RUN_SEED := by decide

/-- The configuration of a mission with no live instance.  Total, because the
measurement above is total. -/
def signalTemplateConfig
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    SignalTriangulation.Config :=
  signalConfigWith UNBOUND_RUN_SEED UNBOUND_TARGET unbound_target_is_the_unbound_draw
    federationId sourceDigest contentDigest contentRoot activationDigest

/-- ⚑ **The artifact does not determine the code.**  Everything a client fetches is
held fixed here — the same template mission, the same federation, the same content
session, the same slot, the same player — and two slot secrets still draw two
different targets.  This is the statement `signalTarget_literal` could not make,
because there the published seed WAS the answer. (Pinned `= true` in `EmitFixtures`.) -/
def check_signalDescriptor_does_not_determine_the_target : Bool :=
  decide (SignalTriangulation.targetFromSeed?
      (demoLiveSeed (signalMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
        (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) 1) ≠
    SignalTriangulation.targetFromSeed?
      (demoLiveSeed (signalMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
        (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) 2))

/-- ⚠ And both of those seeds DRAW.  Without this, the inequality above would be
satisfiable by two refusals, and a draw that refused every live seed would read as
"the artifact does not determine the code". (Pinned `= true` in `EmitFixtures`.) -/
def check_signalDescriptor_demo_seeds_both_draw : Bool :=
  (SignalTriangulation.targetFromSeed?
      (demoLiveSeed (signalMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
        (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) 1)).isSome &&
  (SignalTriangulation.targetFromSeed?
      (demoLiveSeed (signalMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
        (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) 2)).isSome

#assert_axioms signalMission_context_ignores_the_run_seed
#assert_axioms signalReward_accepted
#assert_axioms signalConfig_target_from_live_seed
#assert_axioms signalConfig?_target_is_the_draw
#assert_axioms signalConfig?_refuses_a_refused_seed
#assert_axioms unbound_target_is_the_unbound_draw

def signalPreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (signalMission runSeed federationId sourceDigest contentDigest contentRoot activationDigest)
    signalReward
    WorldState.empty

def relayContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 82, 69, 76, 65, 89, 45, 49]

def relayBudget : ContributionBudget :=
  { intel := ⟨10, by decide⟩
    supplies := ⟨40, by decide⟩
    cohesion := ⟨20, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨650, by decide⟩
    relics := ⟨1, by decide⟩ }

def relayReward : Contribution :=
  { intel := ⟨10, by decide⟩
    supplies := ⟨40, by decide⟩
    cohesion := ⟨20, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨650, by decide⟩
    relics := {relicSlot ⟨2⟩ 0}
    relics_bounded := by decide }

theorem relayReward_within : relayReward.within relayBudget = true := by
  decide

def relayArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨2⟩
    artifactId := ⟨2⟩
    sourceDigest
    contentDigest }

def relayMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨2⟩
    artifact := relayArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId
    contentRoot
    activationDigest
    contentSession := relayContentSession
    runSeed := runSeed
    budget := relayBudget
    allowedRelics := {relicSlot ⟨2⟩ 0}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT] }

theorem relayReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (relayMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution relayReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  exact ⟨relayReward_within, by simp [relayMission, relayReward]⟩

def relayConfig (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    RelayRepair.Config :=
  { board := RelayRepair.boardAt (RelayRepair.boardFromRunSeed runSeed)
    mission := relayMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest
    reward := relayReward
    reward_accepted := relayReward_accepted runSeed federationId sourceDigest contentDigest
      contentRoot activationDigest
    board_eq := rfl }

/-- The judged board is the one the LIVE seed draws.  A host still cannot reprice
the relay after a transcript; what changed is that the client is not shown which
board is live until its own run opens. -/
theorem relayConfig_board_is_the_live_draw (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (relayConfig runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).board =
      RelayRepair.boardAt (RelayRepair.boardFromRunSeed runSeed) := rfl

/-- ⚑ **The artifact does not determine the board.**  Eight demonstration secrets
against the same published template draw more than one board, so the emitted
family of eight is not a family of one wearing eight hats.
(Pinned `= true` in `EmitFixtures`.) -/
def check_relayDescriptor_does_not_determine_the_board : Bool :=
  ((List.range 8).map fun tag =>
    (RelayRepair.boardFromRunSeed
      (demoLiveSeed (relayMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
        (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) tag)).val).eraseDups.length
    != 1

#assert_axioms relayConfig_board_is_the_live_draw

def relayPreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (relayMission runSeed federationId sourceDigest contentDigest contentRoot activationDigest)
    relayReward WorldState.empty

def salvageContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 83, 65, 76, 86, 65, 71, 69, 45, 49]

def salvageBudget : ContributionBudget :=
  { intel := ⟨30, by decide⟩
    supplies := ⟨25, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨15, by decide⟩
    score := ⟨750, by decide⟩
    relics := ⟨1, by decide⟩ }

def salvageReward : Contribution :=
  { intel := ⟨30, by decide⟩
    supplies := ⟨25, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨15, by decide⟩
    score := ⟨750, by decide⟩
    relics := {relicSlot ⟨3⟩ 0}
    relics_bounded := by decide }

theorem salvageReward_within : salvageReward.within salvageBudget = true := by
  decide

def salvageArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨3⟩
    artifactId := ⟨3⟩
    sourceDigest
    contentDigest }

def salvageMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨3⟩
    artifact := salvageArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId
    contentRoot
    activationDigest
    contentSession := salvageContentSession
    runSeed := runSeed
    budget := salvageBudget
    allowedRelics := {relicSlot ⟨3⟩ 0}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT] }

theorem salvageReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (salvageMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution salvageReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  exact ⟨salvageReward_within, by simp [salvageMission, salvageReward]⟩

/-- An `Option`, because a live seed whose byte stream is exhausted before the four
consuming draws finish names NO board.  That case refuses rather than folding to
board zero — the same discipline `SeedDraw` applies one level down. -/
def salvageConfig? (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option SalvageLock.Config :=
  match hseed : SalvageLock.seedFromRunSeed? runSeed with
  | none => none
  | some seed =>
      some
        { seed := seed
          mission := salvageMission runSeed federationId sourceDigest contentDigest contentRoot
            activationDigest
          reward := salvageReward
          reward_accepted := salvageReward_accepted runSeed federationId sourceDigest
            contentDigest contentRoot activationDigest
          seed_eq := hseed.symm }

/-- The board demonstration secret `tag` draws against the published salvage template.
`none` means that secret's byte stream was exhausted before the four consuming draws
finished, which names no board at all. -/
private def demoSalvageBoard? (tag : Nat) : Option Nat :=
  (SalvageLock.seedFromRunSeed?
    (demoLiveSeed (salvageMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
      (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) tag)).map Fin.val

/-- ⚑ **The artifact does not determine the board.**

⚠ RESTATED 2026-08-05, because the previous form was VACUOUS-COMPATIBLE.  It compared
`Option Nat` values and asked only that the deduped list not be a singleton — which a
mix of `none` and `some` satisfies.  It therefore passed even if every RESOLVING secret
drew the SAME board, provided one secret exhausted its stream.

What is stated now leaves no room for that: every one of the eight demonstration
secrets RESOLVES, so no `none` can stand in for a difference, AND the boards they
resolve to are at least two distinct ones.

(The relay twin `relayDescriptor_does_not_determine_the_board` was checked for the same
defect and does not have it: `RelayRepair.boardFromRunSeed` is total, so its list is
`List Nat` with no `none` to launder.) (Pinned `= true` in `EmitFixtures`.) -/
def check_salvageDescriptor_does_not_determine_the_board : Bool :=
  ((List.range 8).all fun tag => (demoSalvageBoard? tag).isSome) &&
    decide (2 ≤ ((List.range 8).filterMap demoSalvageBoard?).eraseDups.length)

def salvagePreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (salvageMission runSeed federationId sourceDigest contentDigest contentRoot activationDigest)
    salvageReward WorldState.empty

#assert_axioms relayReward_within
#assert_axioms relayReward_accepted
#assert_axioms salvageReward_within
#assert_axioms salvageReward_accepted

/-! ## Black Box Reconstruction — the fourth mission

The descriptor, its schema check and `blackBox_table_is_the_kernel` were already in
this module; what was missing was everything that puts the game IN the bundle.  A
descriptor that no artifact list names and no manifest pins carries no integrity at
all: it was emitted, and then nothing measured it.

⚠ **`games/black-box-reconstruction.json` sorts FIRST.**  It precedes every other
game path, so it is the first game entry in `canonicalArtifacts`, the first element
of `schemaJson`'s `content_root.paths`, and the first `content_paths` entry in
`scripts/check-poag1-artifacts.sh`.  The manifest validator requires strictly
path-ascending game artifacts and the content root is framed `path_ascending`, so an
appended-at-the-end mistake changes a digest rather than raising an error. -/

def blackBoxContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 66, 76, 65, 67, 75, 66, 79, 88, 45, 49]

def blackBoxBudget : ContributionBudget :=
  { intel := ⟨40, by decide⟩
    supplies := ⟨10, by decide⟩
    cohesion := ⟨15, by decide⟩
    influence := ⟨10, by decide⟩
    score := ⟨900, by decide⟩
    relics := ⟨1, by decide⟩ }

def blackBoxReward : Contribution :=
  { intel := ⟨40, by decide⟩
    supplies := ⟨10, by decide⟩
    cohesion := ⟨15, by decide⟩
    influence := ⟨10, by decide⟩
    score := ⟨900, by decide⟩
    relics := {relicSlot ⟨4⟩ 0}
    relics_bounded := by decide }

theorem blackBoxReward_within : blackBoxReward.within blackBoxBudget = true := by
  decide

def blackBoxArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨4⟩
    artifactId := ⟨4⟩
    sourceDigest
    contentDigest }

def blackBoxMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨4⟩
    artifact := blackBoxArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId
    contentRoot
    activationDigest
    contentSession := blackBoxContentSession
    runSeed := runSeed
    budget := blackBoxBudget
    allowedRelics := {relicSlot ⟨4⟩ 0}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT] }

theorem blackBoxReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (blackBoxMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution blackBoxReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  exact ⟨blackBoxReward_within, by simp [blackBoxMission, blackBoxReward]⟩

/-- An `Option`, for the same reason `salvageConfig?` is one: a live seed whose byte
stream is exhausted before the four rejection-sampled draws finish names NO order,
and that refuses rather than folding to order zero. -/
def blackBoxConfig? (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option BlackBoxReconstruction.Config :=
  match horder : BlackBoxReconstruction.orderFromRunSeed? runSeed with
  | none => none
  | some order =>
      some
        { order := order
          mission := blackBoxMission runSeed federationId sourceDigest contentDigest contentRoot
            activationDigest
          reward := blackBoxReward
          reward_accepted := blackBoxReward_accepted runSeed federationId sourceDigest
            contentDigest contentRoot activationDigest
          order_eq := horder.symm }

private def demoBlackBoxOrder? (tag : Nat) : Option Nat :=
  (BlackBoxReconstruction.orderFromRunSeed?
    (demoLiveSeed (blackBoxMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
      (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) tag)).map Fin.val

/-- ⚑ **The artifact does not determine the hidden order.**

Black Box publishes its ENTIRE rule set — all 3000 oracle cells — so this is the one
game where "the descriptor tells you everything" is nearly true, and the statement
that it still does not tell you the instance has to be made carefully.

Stated in the shape `salvageDescriptor_does_not_determine_the_board` was repaired
into, so a `none` cannot launder a missing difference: every one of the eight
demonstration secrets RESOLVES to an order, AND at least two of those orders differ.
(Pinned `= true` in `EmitFixtures`.) -/
def check_blackBoxDescriptor_does_not_determine_the_order : Bool :=
  ((List.range 8).all fun tag => (demoBlackBoxOrder? tag).isSome) &&
    decide (2 ≤ ((List.range 8).filterMap demoBlackBoxOrder?).eraseDups.length)

def blackBoxPreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (blackBoxMission runSeed federationId sourceDigest contentDigest contentRoot activationDigest)
    blackBoxReward WorldState.empty

#assert_axioms blackBoxReward_within
#assert_axioms blackBoxReward_accepted

/-! ## Deck Descent — the fifth mission

The descriptor, its exact-schema check, the row/view refinements against
`DeckDescent.rowFor` and the constructive falsifiers all live in
`Dregg2.Games.PathOfAngels.DeckDescentEmit`; this section is everything that puts
the game IN the bundle — mission, budget, artifact slot, and the wiring into
`catalogJson`, `schemaJson`, `canonicalArtifacts` and the manifest pins.

⚠ **`games/deck-descent.json` sorts SECOND**, after
`games/black-box-reconstruction.json` and before `games/relay-repair.json`.  It is
the second game entry in `canonicalArtifacts`, the second element of `schemaJson`'s
`content_root.paths` and the second `content_paths` entry in
`scripts/check-poag1-artifacts.sh` — while its MISSION (id 5) is the LAST entry of
`catalogJson`.  The two orders disagree on purpose, exactly as they do for Black
Box (first artifact, fourth mission). -/

def descentContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 68, 69, 83, 67, 69, 78, 84, 45, 49]

def descentBudget : ContributionBudget :=
  { intel := ⟨20, by decide⟩
    supplies := ⟨20, by decide⟩
    cohesion := ⟨15, by decide⟩
    influence := ⟨20, by decide⟩
    score := ⟨1050, by decide⟩
    relics := ⟨4, by decide⟩ }

/-- The preview reward banks the east pair — the one single-spur line that meets
`BANK_TARGET` — so its relic set is exactly what `Config.terminalContribution`
produces for a sling holding both east relics: `eastRelic` (slot 2 of mission 5)
and `eastSecondRelic` (slot 3). -/
def descentReward : Contribution :=
  { intel := ⟨20, by decide⟩
    supplies := ⟨20, by decide⟩
    cohesion := ⟨15, by decide⟩
    influence := ⟨20, by decide⟩
    score := ⟨1050, by decide⟩
    relics := {relicSlot ⟨5⟩ 2, relicSlot ⟨5⟩ 3}
    relics_bounded := by decide }

theorem descentReward_within : descentReward.within descentBudget = true := by
  decide

def descentArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨5⟩
    artifactId := ⟨5⟩
    sourceDigest
    contentDigest }

/-- Four allowed relics, because a descent Config declares four: the east spur
holds two (`Chamber.relicCount`), so slot 0 mouth, slot 1 west, slot 2 east, slot
3 east-second — all four inside mission 5's block (`RelicNamespace`), which is
what stops them colliding with missions 6 and 7 the way `{5,6,7,8}` did. -/
def descentMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨5⟩
    artifact := descentArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId
    contentRoot
    activationDigest
    contentSession := descentContentSession
    runSeed := runSeed
    budget := descentBudget
    allowedRelics := {relicSlot ⟨5⟩ 0, relicSlot ⟨5⟩ 1, relicSlot ⟨5⟩ 2, relicSlot ⟨5⟩ 3}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by decide }

theorem descentReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (descentMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution descentReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  refine ⟨descentReward_within, ?_⟩
  -- The allowlist of `descentMission` is a literal that ignores every digest
  -- argument, so the subset claim is closed by computation once stated over it.
  show descentReward.relics ⊆
    ({relicSlot ⟨5⟩ 0, relicSlot ⟨5⟩ 1, relicSlot ⟨5⟩ 2, relicSlot ⟨5⟩ 3} : Finset RelicId)
  decide

/-- Total, like `relayConfig`: `DeckDescent.boardFromRunSeed` is total, and
`draw_below_the_reading_never_rejects` records that its mouth-reading fallback is
dead code.

⚠ `bilge` is now a PARAMETER: the mouth is a reading of the day's water, which is
a per-slot draw the node supplies, so a descent config cannot be built without
naming the night.  `DeckDescent.judge` refuses a config whose night disagrees
with its context. -/
def descentConfig (bilge : Bool) (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    DeckDescent.Config :=
  { board := DeckDescent.boardFromRunSeed bilge runSeed
    bilge := bilge
    mission := descentMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest
    mouthRelic := relicSlot ⟨5⟩ 0
    westRelic := relicSlot ⟨5⟩ 1
    eastRelic := relicSlot ⟨5⟩ 2
    eastSecondRelic := relicSlot ⟨5⟩ 3
    reward := descentReward
    reward_accepted := descentReward_accepted runSeed federationId sourceDigest contentDigest
      contentRoot activationDigest
    relics_distinct := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
    relics_declared := by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [descentMission]
    board_eq := rfl }

/-- ⚑ The board a run is judged on is the one its precommitted seed draws. -/
theorem descentConfig_board_is_the_live_draw (bilge : Bool) (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (descentConfig bilge runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).board = DeckDescent.boardFromRunSeed bilge runSeed := rfl

private def demoDescentBoard (tag : Nat) : DeckDescent.Board :=
  DeckDescent.boardFromRunSeed (tag % 2 == 1)
    (demoLiveSeed (descentMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
      (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) tag)

/-- ⚑ **The artifact does not determine the board.**  Stated in the repaired
salvage shape — at least two DISTINCT boards, not merely "the deduped list is not
a singleton" — although `boardFromRunSeed` is total, so there is no `none` to
launder a missing difference in the first place. -/
def check_descentDescriptor_does_not_determine_the_board : Bool :=
  decide (2 ≤ (((List.range 8).map demoDescentBoard).eraseDups).length)

def descentPreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (descentMission runSeed federationId sourceDigest contentDigest contentRoot activationDigest)
    descentReward WorldState.empty

#assert_axioms descentReward_within
#assert_axioms descentReward_accepted
#assert_axioms descentConfig_board_is_the_live_draw

/-! ## Artificer Logic — the sixth mission

The descriptor, its exact-schema check, the manual/row/view refinements against
`ArtificerLogic` and the constructive falsifiers all live in
`Dregg2.Games.PathOfAngels.ArtificerLogicEmit`; this section is everything that
puts the game IN the bundle — mission, budget, artifact slot, and the wiring into
`catalogJson`, `schemaJson`, `canonicalArtifacts` and the manifest pins.

⚠ **`games/artificer-logic.json` sorts FIRST** — before
`games/black-box-reconstruction.json`, which held that slot until now.  It is the
first game entry in `canonicalArtifacts`, the first element of `schemaJson`'s
`content_root.paths` and the first `content_paths` entry in
`scripts/check-poag1-artifacts.sh` — while its MISSION (id 6) is second-to-last in
`catalogJson`.  The two orders disagree on purpose, as they already do for Black
Box (first artifact, fourth mission) and Deck Descent.

⚑ **Enrolling this game re-slots every other one.**  Black Box moves from artifact
index 2 to 3 and Deck Descent from 3 to 4; `canonicalPins` zips the artifact list
against `ArtifactHashes.inCanonicalOrder`, so `artificer` has to be inserted at the
matching position in BOTH or the pins pair a path with another game's digest. -/

def artificerContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 65, 82, 84, 73, 70, 73, 67, 69, 82, 45, 49]

def artificerBudget : ContributionBudget :=
  { intel := ⟨45, by decide⟩
    supplies := ⟨5, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨15, by decide⟩
    score := ⟨800, by decide⟩
    relics := ⟨1, by decide⟩ }

/-- The bench pays in INTEL, which is what the game produces: a documented
mechanism.  One relic, slot 0 of mission 6's block.  ⚠ It used to be ⟨6⟩ — the
bare mission id — under a convention that every game banks exactly one relic;
Deck Descent banks four, and that convention put relic 6 in two missions at once. -/
def artificerReward : Contribution :=
  { intel := ⟨45, by decide⟩
    supplies := ⟨5, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨15, by decide⟩
    score := ⟨800, by decide⟩
    relics := {relicSlot ⟨6⟩ 0}
    relics_bounded := by decide }

theorem artificerReward_within : artificerReward.within artificerBudget = true := by
  decide

def artificerArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨6⟩
    artifactId := ⟨6⟩
    sourceDigest
    contentDigest }

def artificerMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨6⟩
    artifact := artificerArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId
    contentRoot
    activationDigest
    contentSession := artificerContentSession
    runSeed := runSeed
    budget := artificerBudget
    allowedRelics := {relicSlot ⟨6⟩ 0}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT] }

theorem artificerReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (artificerMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution artificerReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  exact ⟨artificerReward_within, by simp [artificerMission, artificerReward]⟩

/-- The SIGNATURE of the rule a live seed would draw, not the rule itself: the
signature is the row of answers the mechanism gives to all eight legal charges, so
two demonstration secrets with different signatures are two mechanisms a player can
actually tell apart.  Comparing `Rule` values would have counted a difference no
experiment can see, which is the weaker claim. -/
private def demoArtificerSignature? (tag : Nat) : Option (List Bool) :=
  (ArtificerLogic.ruleFromRunSeed?
    (demoLiveSeed (artificerMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
      (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) tag)).map
    ArtificerLogic.signature

/-- ⚑ **The artifact does not determine the hidden rule.**

Artificer publishes its ENTIRE hypothesis space — all sixteen rules with the exact
charges each engages on — so "the descriptor tells you everything" is nearer true
here than anywhere else on the rack, and the statement that it still does not tell
you the INSTANCE has to be made carefully.

Stated in the shape `salvageDescriptor_does_not_determine_the_board` was repaired
into, so a `none` cannot launder a missing difference: every one of the eight
demonstration secrets RESOLVES to a rule, AND at least two of those rules are
separated by a legal experiment. (Pinned `= true` in `EmitFixtures`.) -/
def check_artificerDescriptor_does_not_determine_the_rule : Bool :=
  ((List.range 8).all fun tag => (demoArtificerSignature? tag).isSome) &&
    decide (2 ≤ ((List.range 8).filterMap demoArtificerSignature?).eraseDups.length)

def artificerPreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (artificerMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest)
    artificerReward WorldState.empty

#assert_axioms artificerReward_within
#assert_axioms artificerReward_accepted

/-! ## Vent Crawl — the seventh mission

The descriptor, its exact-schema check and the row/view refinements against
`VentCrawl` live in `Dregg2.Games.PathOfAngels.VentCrawlEmit`; this section is
everything that puts the game IN the bundle.

⚠ **`games/vent-crawl.json` sorts LAST**, after
`games/signal-triangulation.json` — the one game whose artifact position and
mission position happen to agree, and that agreement is a coincidence of the
alphabet rather than a rule anything may rely on.

⚠ **The hidden thing here is not shaped like the others.**  Signal, Relay, Salvage,
Black Box, Deck Descent and Artificer each hide a PER-PLAYER draw off
`mission.runSeed`.  Vent Crawl hides a PER-SLOT SHARED table — the day's vein —
drawn under `DayWater.SHIP_DOMAIN`, which takes no player and no mission, so
every crawler in the slot gets the same table and the per-player run seed only
draws the flood tape.  The theorem below is therefore stated over the DAY SEED, not
over `demoLiveSeed`. -/

def ventContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 86, 69, 78, 84, 45, 49]

def ventBudget : ContributionBudget :=
  { intel := ⟨10, by decide⟩
    supplies := ⟨45, by decide⟩
    cohesion := ⟨15, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨750, by decide⟩
    relics := ⟨1, by decide⟩ }

/-- The shaft pays in SUPPLIES, which is what a sling holds.  ⚠ The preview is the
mission's ceiling, not an outcome: an actual crawl banks whatever it banks and a
drowned one banks nothing, so this is the "solved-run preview" every other mission
publishes and it grants exactly as little. -/
def ventReward : Contribution :=
  { intel := ⟨10, by decide⟩
    supplies := ⟨45, by decide⟩
    cohesion := ⟨15, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨750, by decide⟩
    relics := {relicSlot ⟨7⟩ 0}
    relics_bounded := by decide }

theorem ventReward_within : ventReward.within ventBudget = true := by
  decide

def ventArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨7⟩
    artifactId := ⟨7⟩
    sourceDigest
    contentDigest }

def ventMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨7⟩
    artifact := ventArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId
    contentRoot
    activationDigest
    contentSession := ventContentSession
    runSeed := runSeed
    budget := ventBudget
    allowedRelics := {relicSlot ⟨7⟩ 0}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT] }

theorem ventReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (ventMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution ventReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  exact ⟨ventReward_within, by simp [ventMission, ventReward]⟩

/-! ### The emitted Vent Crawl configuration

The analogue of `signalConfigWith`, and it is TOTAL where that one is partial.
Signal's target is a draw that can refuse (216 ∤ 2^256), so a `Config` needs the
caller's own measurement of it.  Vent Crawl's per-player hidden thing is the FLOOD
TAPE, and `floodTapeFromRunSeed` is total: `VentCrawl.draw_below_eight_never_rejects`
says a bound of 8 divides 256 and rejects no byte, so every 32-byte seed draws a
tape.  There is therefore no `ventConfig?`, no measurement argument, and no `Option`.

⚠ **The VEIN is not here and must never be.**  It is a per-SLOT draw the node
derives into `VentCrawl.JudgeContext` from the committed slot secret
(`Judged.ventCrawlContext`).  A `Config` field for it would be a field a host could
set, which is exactly the hole `Judged.RunClaim` closed for Signal's target. -/
def ventDeepRelic : RelicId := relicSlot ⟨7⟩ 0

theorem ventDeepRelic_declared (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    ventDeepRelic ∈ (ventMission runSeed federationId sourceDigest contentDigest
      contentRoot activationDigest).allowedRelics := by
  simp [ventMission, ventDeepRelic]

def ventConfigWith (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    VentCrawl.Config :=
  { mission := ventMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest
    floods := VentCrawl.floodTapeFromRunSeed runSeed
    deepRelic := ventDeepRelic
    relic_declared := ventDeepRelic_declared runSeed federationId sourceDigest contentDigest
      contentRoot activationDigest
    floods_eq := rfl }

/-- The judged tape is the one the LIVE seed draws, for whatever seed the judge was
handed — the Vent Crawl twin of `signalConfig_target_from_live_seed`, and `rfl`
because `Config.floods_eq` is a field rather than a claim. -/
theorem ventConfig_tape_from_live_seed (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (ventConfigWith runSeed federationId sourceDigest contentDigest contentRoot
        activationDigest).floods =
      VentCrawl.floodTapeFromRunSeed
        (ventConfigWith runSeed federationId sourceDigest contentDigest contentRoot
          activationDigest).mission.runSeed := rfl

/-- ⚠ The mission context a Vent Crawl run derives its DAY from ignores the run
seed, exactly as Signal's does — so the per-slot vein cannot be moved by re-drawing
a player's own seed.  This is `signalMission_context_ignores_the_run_seed`'s twin and
it is what makes the day a per-slot value rather than a per-player one. -/
theorem ventMission_context_ignores_the_run_seed (runSeed runSeed' : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    HiddenInstance.MissionContext.ofMission
        (ventMission runSeed federationId sourceDigest contentDigest contentRoot
          activationDigest) =
      HiddenInstance.MissionContext.ofMission
        (ventMission runSeed' federationId sourceDigest contentDigest contentRoot
          activationDigest) := rfl

#assert_axioms ventDeepRelic_declared
#assert_axioms ventConfig_tape_from_live_seed
#assert_axioms ventMission_context_ignores_the_run_seed

private def demoDayContext : HiddenInstance.MissionContext :=
  HiddenInstance.MissionContext.ofMission
    (ventMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
      (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 []))

/-- The day's table, as its published tag.  ⚠ The ship draw takes NO player and
NO mission, so this takes neither: the whole point of the per-slot draw is that a
demonstration varying either would show a difference the real game does not have.
Only the federation and the content session enter, and those are the two lanes
`DayWater.shipHeaderBlock` keeps. -/
private def demoVeinTag (tag : Nat) : String :=
  (VentCrawl.veinFromShipDay
    (DayWater.shipDayFor (demoSecret tag) demoSlot
      demoDayContext.federationId demoDayContext.contentSession)).tag

/-- ⚑ **The artifact does not determine the day's vein.**

Vent Crawl's descriptor publishes ALL FOUR yield ladders in full — it has to, or a
client could not render the range a rung might pay — so the artifact names the
hypothesis space exactly and names the instance not at all.  Stated in the repaired
salvage shape: every demonstration secret RESOLVES to a vein, AND at least two of
those veins differ. (Pinned `= true` in `EmitFixtures`.)

⚠ The first conjunct changed shape on 2026-08-10 and is called out because the
lazy version would have been a TAUTOLOGY.  `veinFromShipDay` is total, so
`.isSome` on its result is `true` by construction and would have asserted
nothing.  What is still contingent — and is what the old `isSome` was really
carrying — is that the ship DRAW resolves without reaching its fallback, so that
is what is checked. -/
def check_ventDescriptor_does_not_determine_the_vein : Bool :=
  ((List.range 8).all fun tag =>
    (DayWater.shipDayFrom? (DayWater.shipSeedFor (demoSecret tag) demoSlot
      demoDayContext.federationId demoDayContext.contentSession)).isSome) &&
    decide (2 ≤ ((List.range 8).map demoVeinTag).eraseDups.length)

def ventPreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (ventMission runSeed federationId sourceDigest contentDigest contentRoot activationDigest)
    ventReward WorldState.empty

#assert_axioms ventReward_within
#assert_axioms ventReward_accepted

/-- ⚠ Every field here is a game whose descriptor is measured by the driver and
pinned in the manifest.  `blackBox` was added 2026-08-06, `deckDescent`
2026-08-07, and `artificer`/`ventCrawl` 2026-08-07; the emit driver requires
`POA_BLACKBOX_SHA256`, `POA_DECKDESCENT_SHA256`, `POA_ARTIFICER_SHA256` and
`POA_VENTCRAWL_SHA256` and there is no default for any of them, so a caller that
has not been taught a new game fails closed rather than emitting an unmeasured
bundle. -/
structure GameContentDigests where
  artificer : Digest32
  blackBox : Digest32
  deckDescent : Digest32
  signal : Digest32
  relay : Digest32
  salvage : Digest32
  ventCrawl : Digest32
deriving DecidableEq

/-- A mission AS PUBLISHED IN A SHARED BUNDLE.  The strings beside the spec are the
catalog's own columns; the last two fields are the reason this structure exists.

⚠ Until 2026-08-08 the emitter took `allowed_relics` as a free `List RelicId`
beside the mission, so every theorem about `mission.allowedRelics` was a theorem
about an object the rendered bytes did not have to agree with — Deck Descent could
have proved `{5,6,7,8}` accepted and emitted `[5]`, and nothing would have looked.
`relics` now CARRIES the proof that it is exactly the mission's allowlist, and
`owned` carries the proof that the allowlist stays inside this mission's relic
block.  A mission that claims a relic belonging to another mission cannot be made
into a `CatalogMission` at all: the emitter refuses to elaborate, rather than the
client refusing to load. -/
structure CatalogMission where
  mission : MissionSpec
  title : String
  engineModule : String
  ruleset : String
  actionLimit : Nat
  descriptorPath : String
  disclosure : String
  /-- The exact array rendered into `allowed_relics`, proved to be the allowlist. -/
  relics : RelicList mission.allowedRelics
  /-- ⚑ Every relic this mission declares is inside its own block. -/
  owned : mission.relicsOwned

/-- ⚑ **No two published missions can claim the same relic.**  Stated over ANY two
`CatalogMission`s with different ids, not over the seven in today's bundle, so the
eighth game inherits it without anyone re-checking the first seven.  This is the
theorem the client's `catalog-relic-collision` refusal mirrors. -/
theorem CatalogMission.allowlists_disjoint (a b : CatalogMission)
    (hne : a.mission.missionId ≠ b.mission.missionId) :
    Disjoint a.mission.allowedRelics b.mission.allowedRelics :=
  Dregg2.Games.PathOfAngels.allowlists_disjoint a.mission b.mission a.owned b.owned hne

/-- ⚑ **The catalog-level guarantee, general in the number of games.**  A list of
published missions with distinct ids has pairwise-disjoint allowlists.  Proved by
induction rather than over today's seven, so enrolling an eighth game re-proves
nothing: it inherits this the moment it carries a `CatalogMission.owned`. -/
theorem pairwise_disjoint_of_ids_nodup (entries : List CatalogMission)
    (h : (entries.map (fun entry => entry.mission.missionId)).Nodup) :
    entries.Pairwise
      (fun a b => Disjoint a.mission.allowedRelics b.mission.allowedRelics) := by
  induction entries with
  | nil => exact List.Pairwise.nil
  | cons entry rest ih =>
      rw [List.map_cons, List.nodup_cons] at h
      refine List.Pairwise.cons ?_ (ih h.2)
      intro other hother
      refine CatalogMission.allowlists_disjoint entry other (fun hEq => h.1 ?_)
      exact List.mem_map.mpr ⟨other, hother, hEq.symm⟩

/-- The same guarantee at the level of the rendered arrays: a relic NUMBER emitted
for one mission cannot be emitted for another. -/
theorem CatalogMission.rendered_relics_disjoint (a b : CatalogMission)
    (hne : a.mission.missionId ≠ b.mission.missionId)
    (relic : RelicId) (hra : relic ∈ a.relics.values) : relic ∉ b.relics.values := by
  rw [a.relics.mem_iff] at hra
  rw [b.relics.mem_iff]
  exact Finset.disjoint_left.mp (CatalogMission.allowlists_disjoint a b hne) hra

private def missionCatalogJson (entry : CatalogMission) : String :=
  let mission := entry.mission
  let title := entry.title
  let engineModule := entry.engineModule
  let ruleset := entry.ruleset
  let actionLimit := entry.actionLimit
  let descriptorPath := entry.descriptorPath
  let disclosure := entry.disclosure
  "    {\"mission_id\":" ++ toString mission.missionId.value ++
  ",\"title\":" ++ jsonString title ++
  ",\"engine_module\":" ++ jsonString engineModule ++
  ",\"ruleset\":" ++ jsonString ruleset ++
  ",\"reward_class\":\"non-economic-demo\"" ++
  ",\"action_limit\":" ++ toString actionLimit ++
  ",\"privacy_grade\":" ++ jsonString (privacyGradeTag mission.privacy) ++
  ",\"ballot_regime\":" ++ jsonString (ballotRegimeTag mission.ballot) ++
  ",\"epoch\":" ++ toString mission.epoch.value ++
  ",\"federation_id\":" ++ jsonString (bytes32Hex mission.federationId) ++
  ",\"content_root\":" ++ jsonString (digestHex mission.contentRoot) ++
  ",\"activation\":{\"state\":\"detached-signature-required\"," ++
    "\"digest_source\":\"POA-CONTENT-EPOCH-SIGNATURE-V1\"}" ++
  ",\"content_session\":" ++ jsonString (bytes32Hex mission.contentSession) ++
  /- ⚠ `run_seed` is GONE from the catalog.  It named the instance of every game
  to anyone who fetched the bundle, which is the hole this split closes; a value
  that changes per run cannot live in an artifact signed once per content epoch.
  What is published instead is where the seed comes from. -/
  ",\"instance\":{\"binding\":\"per-run-hidden-draw\",\"disclosure\":" ++
    jsonString disclosure ++
    ",\"derivation_module\":\"Dregg2.Games.PathOfAngels.HiddenInstance\"" ++
    ",\"commitment_published_in\":\"slot-opening\"}" ++
  ",\"budget\":" ++ contributionBudgetJson mission.budget ++
  /- Rendered from `entry.relics`, whose `complete` field proves it IS
  `mission.allowedRelics` and whose `ascending` field proves the order the curator
  requires.  There is no second list to drift from the first. -/
  ",\"allowed_relics\":" ++ jsonArray (entry.relics.numbers.map toString) ++
  ",\"descriptor_path\":" ++ jsonString descriptorPath ++
  ",\"allowed_beta_discoveries\":[" ++ artifactRefJson mission.artifact ++ "]}"

/-- Applying a contribution to the EMPTY world leaves exactly that contribution's
relics behind.  Needed so the preview fixture can render one relic list for both
the contribution and the world it produces without the two being free to differ. -/
theorem applyContribution_empty_discoveredRelics {mission : MissionSpec}
    {c : Contribution} {after : WorldState}
    (h : applyContribution mission c WorldState.empty = some after) :
    after.discoveredRelics = c.relics := by
  unfold applyContribution at h
  split at h
  · injection h with heq
    rw [← heq]
    simp [WorldState.empty]
  · contradiction

#assert_axioms applyContribution_empty_discoveredRelics

/-- ⚠ The preview world is COMPUTED here rather than passed in.  It is
`applyContribution mission reward WorldState.empty` — the same value the per-game
`xxxPreview` defs hold — and computing it is what lets the emitted
`discovered_relics` carry a proof that it is the contribution's own relic set. -/
private def previewFixtureJson (id : String) (mission : MissionSpec) (reward : Contribution)
    (relics : RelicList reward.relics) : String :=
  "    {\"id\":" ++ jsonString id ++
  ",\"mission_id\":" ++ toString mission.missionId.value ++
  ",\"base_world\":" ++
    worldStateJsonWith WorldState.empty ⟨[], by simp [WorldState.empty], by simp⟩ [] ++
  ",\"contribution\":" ++ contributionJsonWithRelics reward relics ++
  ",\"preview_world\":" ++
    (match h : applyContribution mission reward WorldState.empty with
     | none => "null"
     | some world =>
         worldStateJsonWith world
           ⟨relics.values,
            by rw [applyContribution_empty_discoveredRelics h]; exact relics.complete,
            relics.ascending⟩
           [mission.artifact]) ++ "}"

/-- The seven published missions, each carrying the two relic obligations.

⚠ MISSION order — `mission_id`-ascending — which is NOT the path-ascending order
the manifest and the content root use.  See the note in `canonicalArtifacts`. -/
def catalogMissions (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) : List CatalogMission :=
  /- The activation digest necessarily depends on the detached signature over the
  finished manifest, so it cannot occur inside that manifest without a hash cycle.
  Runtime activation replaces this zero only after signature verification. -/
  let inactiveActivation : Digest32 := taggedBytes32 []
  let unbound := UNBOUND_RUN_SEED
  [ { mission := signalMission unbound federationId sourceDigest digests.signal contentRoot
        inactiveActivation
      title := "Signal Triangulation"
      engineModule := "Dregg2.Games.PathOfAngels.SignalTriangulation"
      ruleset := "signal-v2"
      actionLimit := SignalTriangulation.MAX_TURNS
      descriptorPath := "games/signal-triangulation.json"
      disclosure := "oracle-only"
      relics := RelicList.ofLiteral [relicSlot ⟨1⟩ 0] {relicSlot ⟨1⟩ 0} rfl (by decide) (by decide)
      owned := relicsOwned_of_literals _ ⟨1⟩ {relicSlot ⟨1⟩ 0} rfl rfl (by decide) }
  , { mission := relayMission unbound federationId sourceDigest digests.relay contentRoot
        inactiveActivation
      title := "Relay Repair"
      engineModule := "Dregg2.Games.PathOfAngels.RelayRepair"
      ruleset := "relay-v3"
      actionLimit := RelayRepair.MAX_TURNS
      descriptorPath := "games/relay-repair.json"
      disclosure := "per-run-open"
      relics := RelicList.ofLiteral [relicSlot ⟨2⟩ 0] {relicSlot ⟨2⟩ 0} rfl (by decide) (by decide)
      owned := relicsOwned_of_literals _ ⟨2⟩ {relicSlot ⟨2⟩ 0} rfl rfl (by decide) }
  , { mission := salvageMission unbound federationId sourceDigest digests.salvage contentRoot
        inactiveActivation
      title := "Salvage Lock"
      engineModule := "Dregg2.Games.PathOfAngels.SalvageLock"
      ruleset := "salvage-v2"
      actionLimit := SalvageLock.MAX_TURNS
      descriptorPath := "games/salvage-lock.json"
      disclosure := "oracle-only"
      relics := RelicList.ofLiteral [relicSlot ⟨3⟩ 0] {relicSlot ⟨3⟩ 0} rfl (by decide) (by decide)
      owned := relicsOwned_of_literals _ ⟨3⟩ {relicSlot ⟨3⟩ 0} rfl rfl (by decide) }
  , { mission := blackBoxMission unbound federationId sourceDigest digests.blackBox contentRoot
        inactiveActivation
      title := "Black Box Reconstruction"
      engineModule := "Dregg2.Games.PathOfAngels.BlackBoxReconstruction"
      ruleset := "blackbox-v2"
      actionLimit := BlackBoxReconstruction.MAX_TURNS
      descriptorPath := "games/black-box-reconstruction.json"
      disclosure := "oracle-only"
      relics := RelicList.ofLiteral [relicSlot ⟨4⟩ 0] {relicSlot ⟨4⟩ 0} rfl (by decide) (by decide)
      owned := relicsOwned_of_literals _ ⟨4⟩ {relicSlot ⟨4⟩ 0} rfl rfl (by decide) }
  , { mission := descentMission unbound federationId sourceDigest digests.deckDescent contentRoot
        inactiveActivation
      title := "Deck Descent"
      engineModule := "Dregg2.Games.PathOfAngels.DeckDescent"
      ruleset := "descent-v1"
      actionLimit := DeckDescent.AIR
      descriptorPath := "games/deck-descent.json"
      disclosure := "oracle-only"
      /- ⚑ FOUR relics, and this is the mission that made the namespace visible.
      They are slots 0..3 of mission 5's own block, so a fifth game banking four
      relics collides with nothing by construction. -/
      relics := RelicList.ofLiteral
        [relicSlot ⟨5⟩ 0, relicSlot ⟨5⟩ 1, relicSlot ⟨5⟩ 2, relicSlot ⟨5⟩ 3]
        {relicSlot ⟨5⟩ 0, relicSlot ⟨5⟩ 1, relicSlot ⟨5⟩ 2, relicSlot ⟨5⟩ 3} rfl
        (by decide) (by decide)
      owned := relicsOwned_of_literals _ ⟨5⟩
        {relicSlot ⟨5⟩ 0, relicSlot ⟨5⟩ 1, relicSlot ⟨5⟩ 2, relicSlot ⟨5⟩ 3} rfl rfl
        (by decide) }
  , { mission := artificerMission unbound federationId sourceDigest digests.artificer contentRoot
        inactiveActivation
      title := "Artificer Logic"
      engineModule := "Dregg2.Games.PathOfAngels.ArtificerLogic"
      ruleset := "artificer-v1"
      actionLimit := ArtificerLogic.ACTION_LIMIT
      descriptorPath := "games/artificer-logic.json"
      disclosure := "oracle-only"
      relics := RelicList.ofLiteral [relicSlot ⟨6⟩ 0] {relicSlot ⟨6⟩ 0} rfl (by decide) (by decide)
      owned := relicsOwned_of_literals _ ⟨6⟩ {relicSlot ⟨6⟩ 0} rfl rfl (by decide) }
  , { mission := ventMission unbound federationId sourceDigest digests.ventCrawl contentRoot
        inactiveActivation
      title := "Vent Crawl"
      engineModule := "Dregg2.Games.PathOfAngels.VentCrawl"
      ruleset := "push-your-luck-v1"
      actionLimit := VentCrawl.ACTION_LIMIT
      descriptorPath := "games/vent-crawl.json"
      disclosure := "oracle-only"
      relics := RelicList.ofLiteral [relicSlot ⟨7⟩ 0] {relicSlot ⟨7⟩ 0} rfl (by decide) (by decide)
      owned := relicsOwned_of_literals _ ⟨7⟩ {relicSlot ⟨7⟩ 0} rfl rfl (by decide) } ]

/-- The published mission ids, independent of every digest the bundle binds — the
projection does not mention them, so this closes by `rfl`. -/
theorem catalogMissions_ids (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) :
    (catalogMissions federationId sourceDigest contentRoot digests).map
      (fun entry => entry.mission.missionId)
      = [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩] := rfl

/-- ⚑ **The emitted catalog cannot contain a relic collision.**  Distinct mission
ids (above, by `rfl`) plus the block discipline every entry carries
(`CatalogMission.owned`) give pairwise-disjoint allowlists.  This is the fact the
counter-9 bundle violated: Deck Descent's `{5,6,7,8}` met Artificer's `{6}` and
Vent Crawl's `{7}` in one signed catalog. -/
theorem catalogMissions_allowlists_pairwise_disjoint
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests) :
    (catalogMissions federationId sourceDigest contentRoot digests).Pairwise
      (fun a b => Disjoint a.mission.allowedRelics b.mission.allowedRelics) :=
  pairwise_disjoint_of_ids_nodup _
    (by rw [catalogMissions_ids federationId sourceDigest contentRoot digests]; decide)

#assert_axioms CatalogMission.allowlists_disjoint
#assert_axioms CatalogMission.rendered_relics_disjoint
#assert_axioms pairwise_disjoint_of_ids_nodup
#assert_axioms catalogMissions_ids
#assert_axioms catalogMissions_allowlists_pairwise_disjoint

def catalogJson (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) : String :=
  let inactiveActivation : Digest32 := taggedBytes32 []
  let unbound := UNBOUND_RUN_SEED
  let signal := signalMission unbound federationId sourceDigest digests.signal contentRoot inactiveActivation
  let relay := relayMission unbound federationId sourceDigest digests.relay contentRoot inactiveActivation
  let salvage := salvageMission unbound federationId sourceDigest digests.salvage contentRoot inactiveActivation
  let blackBox := blackBoxMission unbound federationId sourceDigest digests.blackBox contentRoot inactiveActivation
  let descent := descentMission unbound federationId sourceDigest digests.deckDescent contentRoot inactiveActivation
  let artificer := artificerMission unbound federationId sourceDigest digests.artificer contentRoot inactiveActivation
  let vent := ventMission unbound federationId sourceDigest digests.ventCrawl contentRoot inactiveActivation
  /- ⚠ MISSION order here is `mission_id`-ascending, which is NOT the path-ascending
  order the manifest and the content root use.  Black Box is mission 4, so it is
  fourth in this list and SECOND in `canonicalArtifacts`; Deck Descent is mission 5,
  so it is fifth here and THIRD there; Artificer Logic is mission 6, so it is sixth
  here and FIRST there.  Only Vent Crawl (mission 7, last artifact) happens to agree,
  and that is the alphabet, not a rule.  The curator refuses both a non-ascending
  mission list and a non-ascending artifact list, so the two orders have to disagree
  on purpose. -/
  let missions :=
    (catalogMissions federationId sourceDigest contentRoot digests).map missionCatalogJson
  /- Each preview renders ONE relic list for both the contribution and the world it
  produces, and that list carries a proof that it is the reward's own relic set.
  ⚠ Descent's preview banks TWO of its four declared relics — the east pair — which
  is why a preview is a SUBSET of the allowlist and never equal to it. -/
  let fixtures :=
    [ previewFixtureJson "signal-solved-preview-v1" signal signalReward
        ⟨[relicSlot ⟨1⟩ 0], by decide, by decide⟩
    , previewFixtureJson "relay-solved-preview-v1" relay relayReward
        ⟨[relicSlot ⟨2⟩ 0], by decide, by decide⟩
    , previewFixtureJson "salvage-solved-preview-v1" salvage salvageReward
        ⟨[relicSlot ⟨3⟩ 0], by decide, by decide⟩
    , previewFixtureJson "blackbox-solved-preview-v1" blackBox blackBoxReward
        ⟨[relicSlot ⟨4⟩ 0], by decide, by decide⟩
    , previewFixtureJson "descent-solved-preview-v1" descent descentReward
        ⟨[relicSlot ⟨5⟩ 2, relicSlot ⟨5⟩ 3], by decide, by decide⟩
    , previewFixtureJson "artificer-solved-preview-v1" artificer artificerReward
        ⟨[relicSlot ⟨6⟩ 0], by decide, by decide⟩
    , previewFixtureJson "vent-solved-preview-v1" vent ventReward
        ⟨[relicSlot ⟨7⟩ 0], by decide, by decide⟩ ]
  "{\n" ++
  "  \"format\":\"POAG1-CATALOG\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"missions\":" ++ jsonPrettyArray missions ++ ",\n" ++
  "  \"fixtures\":" ++ jsonPrettyArray fixtures ++ "\n" ++
  "}\n"

def schemaJson : String :=
  "{\n" ++
  "  \"format\":\"POAG1-SCHEMA\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"contract\":{\n" ++
  "    \"manifest_required\":[\"format\",\"schema_version\",\"source_digest\",\"authority\",\"artifacts\"],\n" ++
  "    \"artifact_pin_required\":[\"path\",\"media_type\",\"bytes\",\"sha256\",\"fnv1a64\"],\n" ++
  "    \"source_digest_pattern\":\"^sha256:[0-9a-f]{64}$\",\n" ++
  "    \"artifact_sha256_pattern\":\"^sha256:[0-9a-f]{64}$\",\n" ++
  "    \"bytes32_pattern\":\"^[0-9a-f]{64}$\",\n" ++
  "    \"fnv1a64_pattern\":\"^[0-9a-f]{16}$\",\n" ++
  "    \"content_root\":{\"algorithm\":\"sha256\"," ++
    "\"domain\":\"path-of-angels/content-root/v1\\u0000\"," ++
    "\"framing\":\"file_count_be64 || (path_len_be64 || path_utf8 || content_len_be64 || content_bytes)*\"," ++
    "\"entry_order\":\"path_ascending\"," ++
    "\"paths\":[\"games/artificer-logic.json\"," ++
      "\"games/black-box-reconstruction.json\",\"games/deck-descent.json\"," ++
      "\"games/relay-repair.json\",\"games/salvage-lock.json\"," ++
      "\"games/signal-triangulation.json\",\"games/vent-crawl.json\"]},\n" ++
  /- Relic ids are ONE namespace across every mission — the world holds a single
  `discovered_relics` set — so the rule that stops two missions naming the same relic
  has to be PUBLISHED rather than assumed.  `block_width` is rendered from
  `MISSION_RELIC_BLOCK` itself, so a client that pins a different width refuses a
  bundle it genuinely disagrees with rather than one it merely mis-copied. -/
  "    \"relic_namespace\":{\"scheme\":\"per-mission-block\"," ++
    "\"block_width\":" ++ toString MISSION_RELIC_BLOCK ++ "," ++
    "\"owner\":\"relic_id / block_width == mission_id\"," ++
    "\"cross_mission\":\"disjoint-by-construction\"," ++
    "\"authored_in\":\"Dregg2.Games.PathOfAngels.RelicNamespace\"," ++
    "\"violation\":\"refuse\"},\n" ++
  "    \"activation_digest\":{\"algorithm\":\"sha256\"," ++
    "\"domain\":\"pathofangels.network/activation-digest/v1\\u0000\"," ++
    "\"framing\":\"schema_len_be64 || schema_utf8 || manifest_sha256_raw32 || curator_pubkey_raw32 || content_epoch_be64 || counter_be64 || signature_raw64\"," ++
    "\"location\":\"detached verified activation; excluded from manifest preimage\"},\n" ++
  /- The instance a game is played against is derived per run and appears in no
  artifact.  What a client must be handed before a scored run, and what it must
  refuse without, is pinned here.  The bundle is signed once per content epoch and
  slots open afterwards, so a per-slot commitment cannot live inside it: it is
  published in the slot opening below, curator-signed, and a client that accepts a
  run without one has no binding at all. -/
  "    \"slot_opening\":{\"required\":[\"slot\",\"mission_id\",\"commitment\"," ++
    "\"curator_pubkey\",\"signature\"]," ++
    "\"commitment\":{\"algorithm\":\"poseidon2-babybear-w16\"," ++
      "\"domain\":\"POAC\",\"preimage\":\"domain || slot || slot_secret\"," ++
      "\"binding_bits\":124}," ++
    "\"opened_after_close\":[\"slot\",\"slot_secret\"]," ++
    "\"verify\":\"commit(slot_secret, slot) == commitment\"," ++
    "\"missing_opening\":\"refuse\"},\n" ++
  "    \"run_instance\":{\"derivation_module\":\"Dregg2.Games.PathOfAngels.HiddenInstance\"," ++
    "\"function\":\"runSeedFor(draw, mission)\"," ++
    "\"preimage\":\"POAD || purpose || slot || mission_id || epoch || slot_secret " ++
      "|| federation_id || content_session || player_key\"," ++
    "\"purposes\":{\"judged\":1,\"practice\":2}," ++
    "\"published_anywhere\":false," ++
    "\"operator_knows_instance\":true," ++
    "\"practice\":{\"seed\":\"client-chosen\",\"scored\":false," ++
      "\"transcript_field\":\"mode\",\"judge_accepts\":false}},\n" ++
  "    \"unknown_fields\":\"reject\",\n" ++
  "    \"unknown_artifacts\":\"reject\"\n" ++
  "  }\n" ++
  "}\n"

def canonicalArtifacts (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) :
    List ArtifactBytes :=
  /- ⚠ PATH-ASCENDING after schema/catalog, and the curator refuses any other order.
  `games/artificer-logic.json` sorts before `games/black-box-reconstruction.json`,
  which sorts before `games/deck-descent.json` — so the SIXTH game goes first here,
  the fourth second and the fifth third, and only the seventh (`vent-crawl`) is
  actually last. -/
  [ { path := "schema.json", mediaType := "application/schema+json", contents := schemaJson }
  , { path := "catalog.json", mediaType := "application/json",
      contents := catalogJson federationId sourceDigest contentRoot digests }
  , { path := "games/artificer-logic.json", mediaType := "application/json",
      contents := ArtificerLogicEmit.artificerLogicDescriptorJson }
  , { path := "games/black-box-reconstruction.json", mediaType := "application/json",
      contents := blackBoxDescriptorJson }
  , { path := "games/deck-descent.json", mediaType := "application/json",
      contents := DeckDescentEmit.deckDescentDescriptorJson }
  , { path := "games/relay-repair.json", mediaType := "application/json",
      contents := relayDescriptorJson }
  , { path := "games/salvage-lock.json", mediaType := "application/json",
      contents := salvageDescriptorJson }
  , { path := "games/signal-triangulation.json", mediaType := "application/json",
      contents := signalDescriptorJson }
  , { path := "games/vent-crawl.json", mediaType := "application/json",
      contents := VentCrawlEmit.ventCrawlDescriptorJson } ]

/-! SHA-256 is a deployed crypto primitive rather than a theorem implemented in
this emitter.  The driver measures these nine exact Lean-rendered byte strings;
the signed content epoch anchors the resulting manifest. -/
structure ArtifactHashes where
  schema : String
  catalog : String
  artificer : String
  blackBox : String
  deckDescent : String
  relay : String
  salvage : String
  signal : String
  ventCrawl : String
deriving DecidableEq, Repr

def ArtifactHashes.valid (h : ArtifactHashes) : Bool :=
  validSha256 h.schema && validSha256 h.catalog && validSha256 h.artificer &&
    validSha256 h.blackBox && validSha256 h.deckDescent && validSha256 h.relay &&
    validSha256 h.salvage && validSha256 h.signal && validSha256 h.ventCrawl

/-- The measured hashes in the SAME order `canonicalArtifacts` renders its entries.
This list and that one are the two halves of one pairing; nothing else may reorder
either of them. -/
def ArtifactHashes.inCanonicalOrder (h : ArtifactHashes) : List String :=
  [h.schema, h.catalog, h.artificer, h.blackBox, h.deckDescent, h.relay, h.salvage,
    h.signal, h.ventCrawl]

/-- ⚑ THE SIXTH ARTIFACT LANDMINE — REBUILT SO IT CANNOT BE RE-ARMED.

This used to `match` a LITERAL five-element artifact list and fall through to `[]`,
so a sixth artifact would not fail to compile: it would silently emit a manifest
**pinning nothing**.  Enrolling Black Box is exactly the change that would have
tripped it; Deck Descent has since enrolled through the rebuilt shape below, and
Containment Inspection is next.

Widening the literal match to six would have re-armed it at seven.  So the match is
gone: pins are the artifact list zipped against `ArtifactHashes.inCanonicalOrder`.
A shortfall now drops the unpaired tail instead of the whole list, and
`canonicalPins_pins_every_canonical_artifact` below still sees it. -/
def canonicalPins (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) : List ArtifactPin :=
  ((canonicalArtifacts federationId sourceDigest contentRoot digests).zip
      hashes.inCanonicalOrder).map fun pair => pair.1.pin pair.2

/-- ⚑ THE DETECTOR for the landmine described on `canonicalPins`.

It relates the pin list to the ARTIFACT LIST rather than to a literal count, so the
moment an eighth artifact is added without an eighth hash, `7 = 8` fails and the
BUILD goes red at the site of the mistake.  (Enrolling Deck Descent exercised
exactly this: `ArtifactHashes.deckDescent` and the artifact entry moved together,
and nothing here changed.)

Do not "fix" a failure here by changing an expected length — there is no expected
length in the statement, and introducing one is how this stops being a gate.  Add
the missing field to `ArtifactHashes` and to `inCanonicalOrder`, and this closes
again by itself. -/
theorem canonicalPins_pins_every_canonical_artifact
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) :
    (canonicalPins federationId sourceDigest contentRoot digests hashes).length
      = (canonicalArtifacts federationId sourceDigest contentRoot digests).length := by
  rfl

#assert_axioms canonicalPins_pins_every_canonical_artifact

/-! ## ⚑ The lists that must move together, and the two of them Lean can hold

Enrolling a game touches four path lists: `schemaJson` DECLARES the content-root set,
`canonicalArtifacts` RENDERS it, `scripts/check-poag1-artifacts.sh` MEASURES it, and
the curator's `SUPPORTED_GAME_PATHS` ACCEPTS it.  Two of those are outside Lean.  The
two that are inside it were, until now, related by nothing at all — a game added to
`canonicalArtifacts` and forgotten in `schemaJson` produces a bundle whose own
declared content root does not cover its own artifacts, and every downstream check
still passes, because each one reads only one of the two lists.

The ORDER is not decoration either.  The content root frames its entries
`path_ascending`; a wrong order does not fail, it computes a DIFFERENT root, which
every mission then binds and the curator then accepts. -/

/-- The game descriptor paths of a POAG1 v1 bundle, in the path-ascending order the
content root, the manifest and the check script all require.  ⚠ `artificer-logic`
sorts FIRST — appending a new game to the end of this list is right only if its
path actually sorts last, which of the seven is true for `vent-crawl` alone. -/
def POAG1_GAME_PATHS : List String :=
  [ "games/artificer-logic.json"
  , "games/black-box-reconstruction.json"
  , "games/deck-descent.json"
  , "games/relay-repair.json"
  , "games/salvage-lock.json"
  , "games/signal-triangulation.json"
  , "games/vent-crawl.json" ]

theorem POAG1_GAME_PATHS_strictly_ascending :
    (POAG1_GAME_PATHS.zip POAG1_GAME_PATHS.tail).all (fun pair => decide (pair.1 < pair.2))
      = true := by
  decide

def canonicalGamePaths (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) : List String :=
  ((canonicalArtifacts federationId sourceDigest contentRoot digests).map ArtifactBytes.path).drop 2

/-- The rendered artifact list carries exactly these game paths, in this order.
Stated over OPEN digests and closed by `rfl`, so it is a fact about the emitter and
not about one deployment's bundle. -/
theorem canonicalArtifacts_carry_the_canonical_game_paths
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests) :
    canonicalGamePaths federationId sourceDigest contentRoot digests = POAG1_GAME_PATHS := rfl

/-- Read back out of the RENDERED schema bytes — the ones a client fetches — rather
than out of the Lean value that produced them. -/
def schemaContentRootPaths : Except String (List String) := do
  let document ← Json.parse schemaJson
  let contract ← document.getObjVal? "contract"
  let contentRoot ← contract.getObjVal? "content_root"
  let paths ← (contentRoot.getObjVal? "paths") >>= Json.getArr?
  paths.toList.mapM Json.getStr?

/-- ⚑ The gate: the schema's declared content-root path set IS the artifact list's
game path set.  Two independent renderings, one statement.  A game enrolled in one
and not the other is a build failure. (Pinned `= true` in `EmitFixtures`.) -/
def check_schemaJson_declares_exactly_the_canonical_game_paths : Bool :=
  decide (schemaContentRootPaths = .ok POAG1_GAME_PATHS)

#assert_axioms POAG1_GAME_PATHS_strictly_ascending
#assert_axioms canonicalArtifacts_carry_the_canonical_game_paths

def manifestFor (sourceDigestString : String)
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) : Manifest :=
  { format := FORMAT
    schemaVersion := SCHEMA_VERSION
    sourceDigest := sourceDigestString
    authority := AUTHORITY
    artifacts := canonicalPins federationId sourceDigest contentRoot digests hashes }

/-- A manifest is accepted only if it is exactly the one reconstructed from the
Lean-owned artifact bytes and the externally measured full-width source digest. -/
def acceptsManifest (sourceDigestString : String)
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) (candidate : Manifest) : Bool :=
  validSha256 sourceDigestString &&
    hashes.valid &&
    decide (digestHex sourceDigest = sourceDigestString) &&
    decide (digestHex digests.artificer = hashes.artificer) &&
    decide (digestHex digests.blackBox = hashes.blackBox) &&
    decide (digestHex digests.deckDescent = hashes.deckDescent) &&
    decide (digestHex digests.signal = hashes.signal) &&
    decide (digestHex digests.relay = hashes.relay) &&
    decide (digestHex digests.salvage = hashes.salvage) &&
    decide (digestHex digests.ventCrawl = hashes.ventCrawl) &&
    decide (candidate =
      manifestFor sourceDigestString federationId sourceDigest contentRoot digests hashes)

theorem acceptsManifest_eq_true_iff
    (sourceDigestString : String) (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) (hashes : ArtifactHashes) (candidate : Manifest) :
    acceptsManifest sourceDigestString federationId sourceDigest contentRoot digests hashes candidate =
      true ↔
      validSha256 sourceDigestString = true ∧
      hashes.valid = true ∧
      digestHex sourceDigest = sourceDigestString ∧
      digestHex digests.artificer = hashes.artificer ∧
      digestHex digests.blackBox = hashes.blackBox ∧
      digestHex digests.deckDescent = hashes.deckDescent ∧
      digestHex digests.signal = hashes.signal ∧
      digestHex digests.relay = hashes.relay ∧
      digestHex digests.salvage = hashes.salvage ∧
      digestHex digests.ventCrawl = hashes.ventCrawl ∧
      candidate =
        manifestFor sourceDigestString federationId sourceDigest contentRoot digests hashes := by
  simp [acceptsManifest, and_assoc]

/-- ⚑ THE POSITIONAL LANDMINE, REMOVED.

`ingestManifest_exact` used to reach the candidate equality with a bare
`.2.2.2.2.2.2` — a positional index into the conjunction above.  Adding a digest
conjunct, which is exactly what enrolling Black Box did, shifts what that index
names, and the proof then fails somewhere other than the edit that broke it.

Every consumer goes through this lemma instead.  A new conjunct is one named change,
here, and the `obtain` pattern below fails on ARITY rather than on a type mismatch
six projections deep. -/
theorem acceptsManifest_determines_the_manifest
    (sourceDigestString : String) (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) (hashes : ArtifactHashes) (candidate : Manifest)
    (h : acceptsManifest sourceDigestString federationId sourceDigest contentRoot digests hashes
      candidate = true) :
    candidate =
      manifestFor sourceDigestString federationId sourceDigest contentRoot digests hashes := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcandidate⟩ :=
    (acceptsManifest_eq_true_iff _ _ _ _ _ _ _).mp h
  exact hcandidate

/-- Parse plus exact reconstruction.  A parse error, version drift, field drift,
pin mismatch, reordered file, unknown file, or source mismatch is an error. -/
def ingestManifest (sourceDigestString : String)
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) (bytes : String) : Except String Manifest := do
  let parsed ← parseManifest bytes
  if acceptsManifest sourceDigestString federationId sourceDigest contentRoot digests hashes parsed then
    pure parsed
  else
    throw "POAG1 manifest does not exactly match the Lean-emitted bundle"

theorem ingestManifest_exact
    (sourceDigestString : String) (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) (hashes : ArtifactHashes) (bytes : String) (accepted : Manifest)
    (h : ingestManifest sourceDigestString federationId sourceDigest contentRoot digests hashes bytes =
      .ok accepted) :
    accepted =
      manifestFor sourceDigestString federationId sourceDigest contentRoot digests hashes := by
  cases hm : parseManifest bytes with
  | error err =>
      simp only [ingestManifest, hm, bind, Except.bind] at h
      contradiction
  | ok parsed =>
      simp only [ingestManifest, hm, bind, Except.bind] at h
      split at h
      · rename_i ha
        injection h with h
        subst accepted
        exact acceptsManifest_determines_the_manifest _ _ _ _ _ _ _ ha
      · contradiction

#assert_axioms acceptsManifest_eq_true_iff
#assert_axioms acceptsManifest_determines_the_manifest
#assert_axioms ingestManifest_exact

end Dregg2.Games.PathOfAngels.Emit
