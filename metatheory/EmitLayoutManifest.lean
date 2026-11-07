/-
# EmitLayoutManifest — the EffectVM rotated LAYOUT, exported from Lean as Rust source.

Lean is the source of truth for the rotated column geometry: it defines the limb layout and it emits
the constraint descriptors that READ those columns. But the Rust side ALSO needs the layout — the
producer (`turn::rotation_witness`) WRITES witness values into those columns, and the audit gates
check them. Historically Rust re-declared the whole geometry by hand (~89 `pub const`s mirroring
these defs), and the two drifted:

* the REVOKED-ROOT flag day inserted `revoked_root` at base limb 37 and shifted every limb ≥ 37 by
  +1. The producer moved (`write_lanes([33, 38..=44])`); the Lean perms/VK completion welds did NOT
  (they still read limb 37 — which IS `revoked_root` lane-0). Every honest setPermissions /
  setVerificationKey turn was UNSAT in-circuit until that was found;
* `B_SPAN` grew 227 → 239 and a hand-pinned Rust audit column rotted 439 → 451 silently;
* the `vaultSat` satisfaction span grew 64 columns and its hand-pinned width rotted too.

Every one of those is a producer/constraint (or gate/artifact) disagreement about a number that has
exactly ONE true value. So this emitter prints the layout AS RUST, the emit pipeline installs it as
`circuit/src/effect_vm/layout_generated.rs`, and both sides read the same constants. A disagreement
becomes a compile-time impossibility rather than a soundness bug that proves fine on the members you
happened to test.

What stays hand-written: the SEMANTIC teeth (does a forged witness refuse, does the weld bite). Those
must remain independent — they test properties, not coordinates.

SCRATCH executable: `lake env lean --run EmitLayoutManifest.lean`
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.RotatedLayout
import Dregg2.Circuit.Emit.RotWideCompactS2
-- The key-nonet range widths (`KEY_LANE_BITS` / `KEY_TOP_BITS`) are exported below so the Rust
-- producer and the descriptor-drift check read the SAME two numbers the Lean envelope emits.
import Dregg2.Circuit.Emit.KeyCanonicity9Emit
-- ⚑ The KEY_COMMIT interleave matrix (`CarrierOctetGates.quadIdx`) is exported below. It used to be
-- a hand-typed `const QUAD_IDX` in `trace_rotated.rs` BESIDE the Lean one, and the two moved apart:
-- the AIR read eight octet lanes while the executor had been re-pointed at a different fold
-- entirely, so the deployed teeth could not separate a key from its negation and `makeSovereign`
-- stopped verifying. One emitted table, three readers.
import Dregg2.Circuit.Emit.CarrierOctetGates

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmit (EFFECT_VM_WIDTH)
open Dregg2.Circuit.Emit

namespace EmitLayoutManifest

/-- One exported constant: Rust name, value, and the doc line that travels with it. -/
structure Item where
  name : String
  value : Nat
  doc : String

/-! ### The chain-carrier base, READ OFF THE EMITTED SITE LIST (never a second literal)

`rotV3SitesAt` IS the object the descriptors are built from: its first site's `digestCol` is the
column the head absorption writes, i.e. the base of the chain-carrier band. Taking the value from
there — rather than restating `B_STATE_COMMIT + 1` — makes the exported constant a projection of
the emitted geometry, so a site-list change moves it instead of silently disagreeing with it.

This exists because the Rust side carried `pub const B_CHAIN_BASE: usize = 180;` by hand across the
178 → 184 flag day. The producer then wrote its chain digests OVER pre-limbs 180..183 and over the
iroot/state-commit carriers, and the descriptor audit read the carriers six columns below where the
committed descriptors put them. Every rotated member was UNSAT and the registry looked wrong. -/
def bChainBase : Nat := ((rotV3SitesAt 0).head?.map (·.digestCol)).getD 0

/-- The chain-carrier count is what is left of a block once the limbs, the iroot and the
state-commit carrier are accounted for. -/
def bNumChain : Nat := B_SPAN - bChainBase

-- REALITY GATES: the carrier band starts immediately past `state_commit`, every emitted site's
-- digest lands inside `[bChainBase, B_SPAN)` except the final one (which IS `B_STATE_COMMIT`), and
-- the band exactly fills the block's tail.
#guard bChainBase == B_STATE_COMMIT + 1
#guard bChainBase + bNumChain == B_SPAN
#guard ((rotV3SitesAt 0).dropLast.all (fun s => bChainBase ≤ s.digestCol && s.digestCol < B_SPAN))
#guard ((rotV3SitesAt 0).getLast?.map (·.digestCol)).getD 0 == B_STATE_COMMIT
#guard (rotV3SitesAt 0).length == bNumChain + 1

/-! ### The S2 deletion geometry, read off `RotWideCompactS2`'s own spec objects.

`s2_compact_generated.rs` advertises itself as `@generated`, but three of its constants were
string literals inside `scripts/emit_descriptors.py` (`179` / `60` / `840`) while the per-member
table came from Lean. They did not move with the flag day. Derived here from the SPEC LISTS so
there is no second place to re-type them. -/
def s2CarrierOff : Nat := ((Dregg2.Circuit.Emit.RotWideCompactS2.s2CarrierCols 0).head?).getD 0
def s2CarrierSpan : Nat := (Dregg2.Circuit.Emit.RotWideCompactS2.s2CarrierCols 0).length
def s2LaneSpan : Nat :=
  (Dregg2.Circuit.Emit.RotWideCompactS2.s2DeadCols 0 0).length - 2 * s2CarrierSpan

-- REALITY GATES: the deleted carrier band IS the state-commit carrier plus the whole chain band,
-- and `isDeadCol` (the computable form the emit gates ran on) agrees at both lane-band edges.
--
-- ⚑⚑ THESE TWO ARE RED AT THE 2026-08-01 KEY-NONET FLAG DAY, AND THAT IS THE GATE WORKING.
-- `rotatedNumPreLimbs` went 184 → 187, so `B_STATE_COMMIT` is 188 (was 185) and `bNumChain` is 62
-- (was 61). `RotWideCompactS2.s2CarrierCols` still reads `(List.range 62).map (base + 185 + ·)`
-- and `s2DeadCols`/`isDeadCol` still carry `247 / 432 / 494 / 868 / 992` as BARE LITERALS —
-- deliberately, because `omega` treats a `def` as an opaque atom. Those literals must become
-- `63 / 188 / 251 / 439 / 502 / 882 / 1008`. Until they do, the S2-compact emit deletes the WRONG
-- COLUMNS: it would strip pre-limbs 185/186/187 (contract_hash's ninth lane, the OWNER KEY's ninth
-- lane, and the iroot) and leave three real carriers behind.
--
-- ⚠ THIS IS EXACTLY THE 178 → 184 SCAR REPEATING. That flag day left `B_CHAIN_BASE = 180` behind
-- as a hand-written Rust literal, the producer wrote chain digests over four pre-limbs plus
-- iroot/state_commit, and every rotated member was UNSAT. Same class, same band, one file over.
-- DO NOT weaken or delete these two guards to get green; fix `RotWideCompactS2.lean`.
#guard s2CarrierOff == B_STATE_COMMIT
#guard s2CarrierSpan == bNumChain + 1
#guard Dregg2.Circuit.Emit.RotWideCompactS2.isDeadCol 0 100000 (100000 + s2LaneSpan - 1) == true
#guard Dregg2.Circuit.Emit.RotWideCompactS2.isDeadCol 0 100000 (100000 + s2LaneSpan) == false

/-- The rotated-layout spine. Each entry is a number the Rust side previously re-declared by hand. -/
def items : List Item :=
  [ { name := "EFFECT_VM_WIDTH", value := EFFECT_VM_WIDTH,
      doc := "the v1 EffectVM face width — the base every rotated member graduates from" }
  , { name := "NUM_PRE_LIMBS", value := rotated196.numPreLimbs,
      doc := "pre-iroot limbs in one rotated block — projected from the verified RotatedLayout" }
  , { name := "B_SPAN", value := B_SPAN,
      doc := "one rotated state block's span (BEFORE and AFTER each occupy B_SPAN columns)" }
  , { name := "AFTER_BLOCK_OFF", value := AFTER_BLOCK_OFF,
      doc := "column offset from a member's face to its AFTER block (= B_SPAN)" }
  , { name := "C_SPAN", value := C_SPAN,
      doc := "the caveat region's span" }
  , { name := "C_MANIFEST_COMMIT", value := C_MANIFEST_COMMIT,
      doc := "the 29-limb MANIFEST fold's carrier, in-region — an INTERMEDIATE of the chain, not the published commitment" }
  , { name := "C_RC_OFF", value := C_RC_OFF,
      doc := "the DFA route-commitment (rc) carrier, in-region — ABSORBED into the published caveat commitment (the rc FOLD), which is what forces these columns" }
  , { name := "C_RC_CARRIER", value := C_RC_CARRIER,
      doc := "the rc extension's first carrier: hash [manifest commit, rc0, rc1, rc2]" }
  , { name := "C_COMMIT", value := C_COMMIT,
      doc := "the PUBLISHED caveat commitment carrier, in-region — caveatCommitRc over the manifest AND the rc carrier; the column rotPins binds to PI piBase+3" }
  , { name := "CANON9_REGION_OFF", value := CANON9_REGION_OFF,
      doc := "in-appendix base of the FIELDS-CANONICITY region (= 2*B_SPAN + C_SPAN, past both blocks and the caveat region). Its 7 aux columns per (block, slot) are what makes Canonical9's NoWrap leg expressible; the producer MUST fill them or every honest turn is UNSAT." }
  , { name := "CANON9_PER_SLOT", value := 7,
      doc := "aux columns one (block, slot) canonicity gadget uses, in order: r, q0, q1, v0, v0b, v1, v1b" }
  , { name := "CANON9_SPAN", value := CANON9_SPAN,
      doc := "the fields-canonicity region's span (2 blocks * 8 slots * 7 aux columns)" }
  , { name := "APPENDIX_SPAN", value := APPENDIX_SPAN,
      doc := "2*B_SPAN + C_SPAN + CANON9_SPAN — the rotated appendix appended to the v1 face" }
  , { name := "ROT_APPENDIX_SITES", value := (rotV3Appendix EFFECT_VM_WIDTH).length,
      doc := "poseidon2-chip SITES the rotated appendix contributes (2 blocks + the caveat region incl. the rc fold). Graduation appends 7 lane columns per site, so this is the multiplier the Rust host width uses — it was a hand-carried arithmetic literal in trace_rotated.rs and it drifted." }
    -- the committed base limbs (pre-iroot)
  , { name := "B_RECORD_DIGEST", value := B_RECORD_DIGEST,
      doc := "committed record/authority digest limb" }
  , { name := "B_CAP_ROOT", value := B_CAP_ROOT, doc := "committed capability-root limb" }
  , { name := "B_NULLIFIER_ROOT_OFF", value := B_NULLIFIER_ROOT_OFF,
      doc := "committed nullifier-root limb" }
  , { name := "B_COMMITMENTS_ROOT", value := B_COMMITMENTS_ROOT,
      doc := "committed commitments-root limb" }
  , { name := "B_HEAP_ROOT", value := B_HEAP_ROOT, doc := "committed heap-root limb" }
  , { name := "B_LIFECYCLE", value := B_LIFECYCLE, doc := "committed lifecycle limb" }
  , { name := "B_EPOCH", value := B_EPOCH, doc := "committed epoch limb" }
  , { name := "B_COMMITTED_HEIGHT", value := B_COMMITTED_HEIGHT,
      doc := "last SCALAR pre-iroot limb (disc/perms/vk/mode/fields-root ride past it)" }
  , { name := "B_DISC", value := B_DISC, doc := "WAVE-1 committed discriminant limb" }
  , { name := "B_PERMS", value := B_PERMS,
      doc := "WAVE-2 committed permissions-digest limb (lane 0 of the faithful 8-felt group)" }
  , { name := "B_VK", value := B_VK,
      doc := "WAVE-2 committed verification-key-digest limb (lane 0 of the 8-felt group)" }
  , { name := "B_MODE", value := B_MODE, doc := "WAVE-3 committed mode limb" }
  , { name := "B_FIELDS_ROOT", value := B_FIELDS_ROOT,
      doc := "WAVE-3 committed fields-root digest limb" }
  , { name := "B_REVOKED_ROOT", value := B_REVOKED_ROOT,
      doc := "REVOKED-ROOT flag-day limb — inserted at 37, shifting every limb >= 37 by +1" }
    -- THE WELD OFFSETS. These are the numbers the setPerms/setVK bug lived in.
  , { name := "B_PERMS_COMPLETION", value := B_PERMS_COMPLETION,
      doc := "FIRST perms-digest completion limb; permsHash[1..7] ride B_PERMS_COMPLETION..+6. \
              The producer writes these lanes and the in-circuit weld reads them: ONE source." }
  , { name := "B_VK_COMPLETION", value := B_VK_COMPLETION,
      doc := "FIRST vk-digest completion limb; vkHash[1..7] ride B_VK_COMPLETION..+6" }
  , { name := "B_IROOT", value := B_IROOT, doc := "the iroot limb (pre-iroot limbs end here)" }
  , { name := "B_STATE_COMMIT", value := B_STATE_COMMIT, doc := "the state-commitment limb" }
  , { name := "B_CHAIN_BASE", value := bChainBase,
      doc := "in-block base of the chained-absorption carriers — READ OFF `rotV3SitesAt`'s first \
              emitted site, so the producer writes the columns the descriptors bind. Rust carried \
              this by hand and it rotted across the 178 -> 184 flag day (180 vs 186): the producer \
              overwrote four pre-limbs plus iroot/state_commit and every rotated member was UNSAT." }
  , { name := "B_NUM_CHAIN", value := bNumChain,
      doc := "chain carriers per block: they fill `[B_CHAIN_BASE, B_SPAN)` exactly" }
    -- THE S2 DELETION BANDS (`RotWideCompactS2`) — the Rust trace producer must drop exactly the
    -- columns the Lean emit deleted from the committed wide descriptors.
  , { name := "S2_CARRIER_OFF", value := s2CarrierOff,
      doc := "in-block offset of the first S2-deleted column (the 1-felt state_commit digest)" }
  , { name := "S2_CARRIER_SPAN", value := s2CarrierSpan,
      doc := "one S2-deleted carrier band's width (state_commit digest + B_NUM_CHAIN chain carriers)" }
  , { name := "S2_LANE_SPAN", value := s2LaneSpan,
      doc := "the S2-deleted graduated chip-lane band's width (7 lanes per deleted block site)" }
    -- THE OCTET → REGISTER QUERY + APP-PI LAYOUT (the field_key class — Rust reads, never re-derives).
    -- `FIELD_BASE` is the state register index the AFTER-block field octet's index 0 maps to; a consumer
    -- derives an octet index from a register slot via `octet_index_of_register` (emitted below).
  , { name := "FIELD_BASE", value := Dregg2.Circuit.Emit.EffectVmEmit.state.FIELD_BASE,
      doc := "state register index of the first committed field (fields[0]); the AFTER-block field \
              octet holds register r(FIELD_BASE+i) at octet index i, so octet_index(r) = r - FIELD_BASE" }
  , { name := "CUSTOM_APP_FIELD_ROT_BASE", value := CUSTOM_APP_FIELD_ROT_BASE,
      doc := "in-block column base of the AFTER-block committed fields[0..8] lane-0 octet (the app-root \
              weld octet): weldsAt maps base+CUSTOM_APP_FIELD_ROT_BASE+i ↔ stateBase+FIELD_BASE+i" }
  , { name := "CUSTOM_APP_FIELD_OCTET_LEN", value := CUSTOM_APP_FIELD_OCTET_LEN,
      doc := "width of the app-root field octet (8 field lane-0 limbs)" }
  , { name := "B_CHILD_VK_OCTET", value := B_CHILD_VK_OCTET,
      doc := "in-block base of the child_vk carrier octet (app-PI octet base 0 of [89, 97, 105])" }
  , { name := "B_CONTRACT_HASH_OCTET", value := B_CONTRACT_HASH_OCTET,
      doc := "in-block base of the contract_hash carrier octet (app-PI octet base 1 of [89, 97, 105])" }
  , { name := "B_PUBKEY_OCTET", value := B_PUBKEY_OCTET,
      doc := "in-block base of the public_key carrier octet (app-PI octet base 2 of [89, 97, 105])" }
    -- ⚑ THE CARRIER-OCTET NINTH LANES (key-nonet flag day 2026-08-01). Eight BabyBear lanes carry
    -- 247.26 bits against a 32-byte carrier's 256, and the deployed packer drops bits 6-7 of every
    -- fourth byte outright — among Ed25519 keys a key and its NEGATION pack to one octet. These
    -- three columns are the ninth lane of each carrier octet, and they are ABSORBED pre-limbs, so
    -- `wireCommitR` folds them into `state_commit`. A producer that does not fill them makes every
    -- honest turn UNSAT; a producer that fills them from an 8-lane packer re-opens the wound.
  , { name := "B_CHILD_VK_NINTH_LANE", value := B_CHILD_VK_NINTH_LANE,
      doc := "ninth lane of the child_vk carrier NONET (KeyLanes9.keyToLanes9 lane 8)" }
  , { name := "B_CONTRACT_HASH_NINTH_LANE", value := B_CONTRACT_HASH_NINTH_LANE,
      doc := "ninth lane of the contract_hash carrier NONET (KeyLanes9.keyToLanes9 lane 8)" }
  , { name := "B_PUBKEY_NINTH_LANE", value := B_PUBKEY_NINTH_LANE,
      doc := "ninth lane of the OWNER-KEY carrier NONET. The eight-lane octet at B_PUBKEY_OCTET \
              cannot injectively hold 32 bytes; this column is what makes the committed nonet \
              determine exactly one key (Emit.KeyCanonicity9Emit.keyCanon9_determines_the_owner_key_deployed)." }
  , { name := "KEY_LANE_BITS", value := Dregg2.Circuit.Emit.KeyCanonicity9Emit.KEY_LANE_BITS,
      doc := "range width of nonet lanes 0..7 (2^29 < p, so no lane reduces)" }
  , { name := "KEY_TOP_BITS", value := Dregg2.Circuit.Emit.KeyCanonicity9Emit.KEY_TOP_BITS,
      doc := "range width of nonet lane 8. NARROWER by construction: 2^256 / (2^29)^8 = 2^24. A \
              uniform 29-bit check on lane 8 admits [0,...,0,2^24], which decodes byte-for-byte to \
              the all-zero key — see keyCanon9_rejects_the_forged_nonet." }
  ]

/-- Emit one Rust `pub const`. -/
def renderItem (i : Item) : String :=
  s!"/// {i.doc}\npub const {i.name}: usize = {i.value};\n"

/-- Stable Rust API names for the verified layout's named groups. The values are not repeated here:
each Rust constant below indexes the one emitted `ROTATED_GROUP_TABLE`. -/
def groupRustName : GroupName → String
  | .authority   => "AUTHORITY_DIGEST_GROUP"
  | .cap         => "CAP_ROOT_GROUP"
  | .nullifier  => "NULLIFIER_ROOT_GROUP"
  | .commitments => "COMMITMENTS_ROOT_GROUP"
  | .heap        => "HEAP_ROOT_GROUP"
  | .perms       => "PERMS_GROUP"
  | .vk          => "VK_GROUP"
  | .fields      => "FIELDS_ROOT_GROUP"
  | .revoked     => "REVOKED_ROOT_GROUP"
  | .cells       => "CELLS_ROOT_GROUP"

def renderNatArray (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

/-- Emit the verified table as the sole Rust data value, then expose semantic names as const
indices into it. Reordering groups in Lean cannot silently retarget a Rust consumer because the
name→index declarations are generated in the same pass. -/
def renderGroupTable : String :=
  let rows := String.intercalate ",\n" (rotated196.groupTable.map (fun row => "    " ++ renderNatArray row)) ++ ","
  let names := String.intercalate "\n" <| rotated196.groups.zipIdx.map (fun p =>
    s!"pub const {groupRustName p.1.1}: Felt8Group = ROTATED_GROUP_TABLE[{p.2}];")
  s!"/// One faithful-8 group: lane 0 followed by seven completion columns.\n\
pub type Felt8Group = [usize; 8];\n\n\
/// Every named group, emitted verbatim from `rotated196.groupTable`.\n\
pub const ROTATED_GROUP_TABLE: [Felt8Group; {rotated196.groupTable.length}] = [\n{rows}\n];\n\n\
{names}\n\n\
/// Compatibility/readability alias used by the Rust disjointness tooth.\n\
pub const ALL_FELT8_GROUPS: [Felt8Group; {rotated196.groupTable.length}] = ROTATED_GROUP_TABLE;\n"

/-- The NON-GROUP regions of the verified tiling, emitted as data. The Rust disjointness tooth used
to hand-list these beside the generated group table (`[176, 177]` pads, `113..168` field lanes) — so
it re-stated the 178 layout and went red on the flag day for the one region it was NOT reading from
Lean. It now assembles its occupancy from these, which keeps it an artifact-integrity check on the
EMITTED table (a dropped or duplicated region still fails) without carrying a coordinate copy. -/
def renderRegions : String :=
  let singles := renderNatArray rotated196.singles
  let octets := renderNatArray rotated196.octets
  let ninths := renderNatArray rotated196.octetNinthLanes
  let fields := renderNatArray rotated196.fieldsOctet
  let pads := renderNatArray rotated196.pads
  let cellsC := renderNatArray rotated196.cellsCompletion
  let irootC := renderNatArray rotated196.irootCompletion
  s!"/// The scalar limbs that carry no faithful-8 completion group.\n\
pub const ROTATED_SINGLES: [usize; {rotated196.singles.length}] = {singles};\n\n\
/// The carrier-material octet BASES (each occupies `base .. base + 8`).\n\
pub const ROTATED_OCTET_BASES: [usize; {rotated196.octets.length}] = {octets};\n\n\
/// The NINTH lane of each carrier octet, positionally parallel to `ROTATED_OCTET_BASES`. \
NOT adjacent to its octet: never reconstruct with a stride. Each is an ABSORBED pre-limb, so \
`wireCommitR` folds it into `state_commit` — which is the whole point.\n\
pub const ROTATED_OCTET_NINTH_LANES: [usize; {rotated196.octetNinthLanes.length}] = {ninths};\n\n\
/// Every `fields[0..8]` completion lane column, in layout order (lanes 1..8 of each of the 8 \
slots — deliberately NON-CONTIGUOUS: the ninth lane of slot `j` is `176 + j`).\n\
pub const ROTATED_FIELDS_LANE_COLS: [usize; {rotated196.fieldsOctet.length}] = {fields};\n\n\
/// The legacy cells-completion slot (empty since `cells` became a named group).\n\
pub const ROTATED_CELLS_COMPLETION: [usize; {rotated196.cellsCompletion.length}] = {cellsC};\n\n\
/// Lanes 1..7 of the receipt-log root `iroot8` (lane 0 is `B_IROOT`). ABSORBED pre-limbs: the \
producers write `iroot8(..).limbs()[1..8]` here, so the signed anchor binds the receipt log at all \
eight lanes (the iroot-widening flag day, 187 -> 196).\n\
pub const ROTATED_IROOT_COMPLETION: [usize; {rotated196.irootCompletion.length}] = {irootC};\n\n\
/// Unoccupied pad columns: the two the 1-mod-3 body discipline leaves at 196 (the producers write \
zero).\n\
pub const ROTATED_PADS: [usize; {rotated196.pads.length}] = {pads};\n"

/-- **THE NONET PROJECTION, AS DATA.** `RotatedLayout.fieldLaneCol slot lane` for all 8 slots × 9
lanes. Its own docstring says "Consumers must read THIS, never `113 + 8·slot` — the nonet is
deliberately NON-CONTIGUOUS"; the Rust setField VALUE8 producer was computing exactly
`SETFIELD_VALUE8_LANE_BASE + LEN·slot + k`, which is that forbidden formula and which lands on the
neighbouring slot the moment `LEN` becomes 8. Emitting the table removes the formula. -/
def renderFieldLaneTable : String :=
  let rows := String.intercalate ",\n" <|
    (List.range 8).map (fun s =>
      "    " ++ renderNatArray ((List.range 9).map (fun l =>
        fieldLaneCol ⟨s % 8, by omega⟩ ⟨l % 9, by omega⟩)))
  s!"/// `ROTATED_FIELD_LANE_COL[slot][lane]` — the column carrying lane `lane` of `fields[slot]`.\n\
/// Lane 0 is the welded v1-face limb, lanes 1..7 the historical completion window, lane 8 the\n\
/// flag-day ninth lane. NON-CONTIGUOUS BY DESIGN: never reconstruct this with a stride.\n\
pub const ROTATED_FIELD_LANE_COL: [[usize; 9]; 8] = [\n{rows},\n];\n\n\
/// Completion lanes per committed field slot (lanes 1..=8 — the VALUE8/nonet weld width).\n\
pub const ROTATED_FIELD_COMPLETION_LANES: usize = 8;\n"

/-- **THE KEY_COMMIT INTERLEAVE, AS DATA.** `CarrierOctetGates.quadIdx q j` — quad `q`'s `j`-th
input LANE of the committed owner-key NONET. Emitting it is what makes
`effect_vm::helpers::key_commit_teeth_from_nonet` (which the executor's
`pubkey_to_witness_key_commit` and the producer's `append_sovereign_key_commit_rider` both call)
a READER of the AIR's matrix rather than a second copy of it.

Row 2 is `[8, 0, 4, 2]`: lane 8 — the ninth lane, the ONLY committed column that sees source bit
255, i.e. an Ed25519 key's x-sign — enters here and nowhere else
(`quadIdx_row2_reads_the_ninth_lane`), and every lane is covered (`quadIdx_covers_every_lane`). -/
def renderKeyCommitQuadIdx : String :=
  let rows := String.intercalate ",\n" <|
    (List.range 4).map (fun q =>
      "    " ++ renderNatArray ((List.range 4).map (fun j =>
        (Dregg2.Circuit.Emit.CarrierOctetGates.quadIdx ⟨q % 4, by omega⟩ ⟨j % 4, by omega⟩).val)))
  s!"/// `KEY_COMMIT_QUAD_IDX[q][j]` — quad `q`'s `j`-th input LANE of the committed owner-key\n/// NONET, emitted from the AIR's own `CarrierOctetGates.quadIdx`. The four published KEY_COMMIT\n/// teeth are `chip_absorb_all_lanes(4, [nonet[KEY_COMMIT_QUAD_IDX[q][j]]; 4])[0]`.\n///\n/// ⚑ EVERY lane 0..=8 appears (`quadIdx_covers_every_lane`), and lane 8 appears ONLY at `[2][0]`\n/// (`quadIdx_row2_reads_the_ninth_lane`). Lane 8 carries source bit 255 = an Ed25519 key's\n/// x-sign, so a matrix that omits it publishes identical teeth for a key and its negation — which\n/// is exactly what the deployed member did until 2026-08-08. NEVER hand-edit this table.\npub const KEY_COMMIT_QUAD_IDX: [[usize; 4]; 4] = [\n{rows},\n];\n\n/// The nonet lane count the KEY_COMMIT quads index into.\npub const KEY_NONET_LANES: usize = 9;\n"

def header : String :=
  "// @generated by metatheory/EmitLayoutManifest.lean — DO NOT EDIT BY HAND.\n\
   //\n\
   // The rotated EffectVM column layout, exported from the Lean that DEFINES it and that emits the\n\
   // constraint descriptors READING it. The Rust producer (`turn::rotation_witness`) WRITES these\n\
   // same columns, and the audit gates check them — so all three now read one source instead of\n\
   // three hand-maintained mirrors.\n\
   //\n\
   // This module exists because the mirrors drifted, and drift here is not a lint failure — it is a\n\
   // soundness bug. The perms/VK completion weld once read limb 37 (`revoked_root` lane-0) while the\n\
   // producer wrote limb 38, and every honest setPermissions/setVerificationKey turn was UNSAT.\n\
   //\n\
   // Regenerate with the ack-gated emit pipeline (`scripts/emit_descriptors.py`); never hand-edit.\n\n"

/-- The octet→register QUERY, emitted as a `const fn` so the Rust consumer READS the mapping instead
of re-deriving the `- FIELD_BASE` offset by hand (the `field_key` mirror the fold guessed wrong). -/
def footerLines : List String :=
  [ ""
  , "/// Derive the app-root field OCTET INDEX from a state register slot: the AFTER-block"
  , "/// `fields[0..8]` octet holds field register `r(FIELD_BASE + i)` at octet index `i`, so"
  , "/// `octet_index_of_register(r) == r - FIELD_BASE` — the single Lean-authored query the fold's"
  , "/// app-root weld reads (killing the hand `reg(\"winner\") - 3`)."
  , "pub const fn octet_index_of_register(reg: usize) -> usize {"
  , "    reg - FIELD_BASE"
  , "}"
  ]

def footer : String := String.intercalate "\n" footerLines ++ "\n"

def main : IO Unit := do
  IO.print header
  for i in items do
    IO.print (renderItem i)
    IO.print "\n"
  IO.print renderGroupTable
  IO.print "\n"
  IO.print renderRegions
  IO.print "\n"
  IO.print renderFieldLaneTable
  IO.print "\n"
  IO.print renderKeyCommitQuadIdx
  IO.print footer

end EmitLayoutManifest

def main : IO Unit := EmitLayoutManifest.main
