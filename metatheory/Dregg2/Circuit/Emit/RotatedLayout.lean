import Mathlib.Data.List.Nodup

/-
# RotatedLayout — the verified column allocator (Phase 1–2 of the verified-snarky foundation)

THE DISEASE (paid for in the revoked-root 178 migration, 2026-07): the rotated-block column layout was
a pile of hand-carried integers spread across ~14 emit files + two byte-identical Rust producers, and
the invariant that makes a layout *legal* — no two things write the same column — was an UNCHECKED
comment. So a flag-day was a 14-file act of faith that plonky3 audited *after* a VK regen instead of the
type system at construction.

THE CURE: make the layout a first-class object with an explicit machine-checked legality witness, whose
`groupCol` projection is the SINGLE SOURCE the emit reads its positions from. A flag-day becomes a new
`def` + `native_decide`; an ill-aligned / overlapping layout becomes UNCONSTRUCTABLE.

`rotated196` is the current geometry (178 until 2026-07-31's fields-nonet flag day, 184 until
2026-08-01's KEY-nonet flag day). `EffectVmEmitRotationV3` projects its group columns from this
object; `EmitLayoutManifest.lean` emits its `groupTable` to Rust; and both Rust producers plus the
circuit trace generator consume that generated table. The concrete integers therefore live here once.
-/

namespace Dregg2.Circuit.Emit

/-- The named faithful-8-felt roots the rotated block commits. -/
inductive GroupName
  | authority | cap | nullifier | commitments | heap | perms | vk | fields | revoked | cells
deriving DecidableEq, Repr

/-- One faithful-8-felt group: lane 0 (the scalar limb the root historically rode) plus the seven
    completion columns (which may be non-contiguous — e.g. `fields` reuses headroom limbs 19..23). -/
structure LayoutGroup where
  lane0      : Nat
  completion : List Nat   -- length 7
deriving DecidableEq, Repr

/-- The abstract rotated pre-iroot column layout: every occupied column, as data. -/
structure RotatedLayout where
  numPreLimbs     : Nat
  singles         : List Nat                    -- scalars with no completion group
  groups          : List (GroupName × LayoutGroup)  -- the faithful-8-felt roots, name-tagged
  octets          : List Nat                    -- octet BASES (each occupies base .. base+8)
  /-- ⚑ **KEY-NONET FLAG DAY 2026-08-01.** The NINTH lane of each carrier octet, positionally
      parallel to `octets`. A carrier octet holds 32 bytes in eight ≤30-bit lanes and therefore
      cannot be injective (`Dregg2.Circuit.KeyLanes9`); the ninth lane is what makes it a nonet, and
      it must be an ABSORBED PRE-LIMB (a column outside `preLimbsAt` never enters `wireCommitR`, so
      `state_commit` would still bind only the eight). -/
  octetNinthLanes : List Nat
  fieldsOctet     : List Nat                    -- the 64 fields[0..7] completion lanes (8 slots x lanes 1..8)
  cellsCompletion : List Nat                    -- legacy slot, now empty (cells is a named group)
  /-- ⚑ **IROOT-WIDENING FLAG DAY 2026-11-07.** Lanes 1..7 of the receipt-log root `iroot8`. Lane 0
      stays at `B_IROOT` (absorbed alone last); these seven are ABSORBED PRE-LIMBS, so `wireCommitR`
      and the wide chain fold them into `state_commit`. Before this the block had one receipt-root
      column and the signed anchor bound the receipt log at ONE felt (a lane-0 birthday collision
      was exhibited in 64,147 evaluations, `turn/tests/iroot_wide_old_admits_new_rejects.rs`). -/
  irootCompletion : List Nat
  pads            : List Nat
deriving Repr

/-- Every column an instance occupies, flattened — the domain of the disjointness obligation. -/
def RotatedLayout.occupied (L : RotatedLayout) : List Nat :=
  L.singles
    ++ L.groups.flatMap (fun p => p.2.lane0 :: p.2.completion)
    ++ L.octets.flatMap (fun b => (List.range 8).map (· + b))
    ++ L.octetNinthLanes
    ++ L.fieldsOctet
    ++ L.cellsCompletion
    ++ L.irootCompletion
    ++ L.pads

/-- **THE PROJECTION** — the single source the emit reads a group's within-block column from. Lane 0 is
    the scalar limb; lanes 1..7 index the completion list. `none` = the group/lane is absent. -/
def RotatedLayout.groupCol (L : RotatedLayout) (name : GroupName) (i : Fin 8) : Option Nat :=
  match L.groups.find? (fun p => p.1 = name) with
  | some p => if (i : Nat) = 0 then some p.2.lane0 else p.2.completion[(i : Nat) - 1]?
  | none   => none

/-- **THE CARRIER-OCTET NONET PROJECTION** — the single source a consumer reads lane `lane` of the
`o`-th carrier octet from. Lanes 0..7 are the contiguous octet window `base .. base+7`; lane 8 is
the flag-day ninth-lane column, which is NOT adjacent to them and must never be reconstructed with a
stride. `none` = the octet does not exist. -/
def RotatedLayout.octetLaneCol (L : RotatedLayout) (o : Nat) (lane : Fin 9) : Option Nat :=
  if (lane : Nat) = 8 then L.octetNinthLanes[o]?
  else (L.octets[o]?).map (· + (lane : Nat))

/-- **THE LEGALITY OBLIGATIONS** — all decidable, so a concrete layout discharges them by
    `native_decide`, and an illegal layout cannot be constructed. -/
structure Legal (L : RotatedLayout) : Prop where
  /-- Every named digest really is faithful-8: lane 0 plus exactly seven completion lanes. -/
  groupWidth  : ∀ p ∈ L.groups, p.2.completion.length = 7
  /-- Names are keys, not labels: `groupCol` must never silently select the first duplicate. -/
  groupNames  : (L.groups.map Prod.fst).Nodup
  /-- Every semantic group exists, so a consumer projection can never fall through `Option.getD`. -/
  groupCoverage : ∀ name : GroupName, name ∈ L.groups.map Prod.fst
  /-- ⚑ **EVERY CARRIER OCTET IS A NONET.** One ninth lane per octet base, positionally. A layout
      that grows an octet without allocating its ninth lane — the shape that let the deployed owner
      key ride eight lanes at 247.26 bits against 256 — is UNCONSTRUCTABLE. -/
  octetNonets : L.octetNinthLanes.length = L.octets.length
  /-- ⚑ **THE RECEIPT-LOG ROOT IS FAITHFUL-8.** Exactly seven completion lanes beside `B_IROOT`'s
      lane 0, so a layout that carries the receipt root at fewer lanes is UNCONSTRUCTABLE. -/
  irootWidth  : L.irootCompletion.length = 7
  /-- Disjointness: no two things write the same column. THE invariant that was a comment. -/
  disjoint    : L.occupied.Nodup
  /-- Bounds: every occupied column is a real pre-iroot limb. -/
  inBounds    : ∀ c ∈ L.occupied, c < L.numPreLimbs
  /-- The multiple-of-3 body discipline: the wire-commit chain folds the body (limbs `4 ..
      numPreLimbs-1`) in arity-3 groups after the arity-4 head; a leftover chunk is the arity-2/arity-9
      refuse the chip rejects — the exact 170-leftover fork we hit. -/
  bodyAligned : (L.numPreLimbs - 4) % 3 = 0

/-- The current pre-iroot extent. Keeping this scalar beside the instance avoids unfolding the full
layout through descriptor reduction while leaving a count flag-day in this one verified source file.

⚑ **FLAG DAY 2026-07-31: 178 → 184.** The fields octet became a fields NONET. `p = 2013265921`, so
`log₂ p = 30.907` and eight lanes carry 247.26 bits against a 32-byte field's 256 — **no 8-lane
encoding of 32 bytes is injective under any chunking**, pigeonhole, whatever the lanes contain. The
`fields[0..7]` lanes are the only binding those fields have (they are excluded from the byte-exact
authority residue, `cell/src/commitment.rs` — "bound by their own limbs"), so the deficit reached
`TurnReceipt::{pre,post}_state_hash`. `Dregg2.Circuit.FieldLanes9.fieldToLanes9_injective` is the
nine-lane encoder that closes it, and each field's NINTH lane needs a column.

The six extra columns come out of the two free pads (176, 177) plus 178..183, and **NOTHING SHIFTS**:
every column that had a meaning at 178 keeps it. `(184 - 4) % 3 = 0`, so `bodyAligned` survives — 186
would have been ILLEGAL and 187 costs four columns for nothing. Downstream: `B_SPAN` 239 → 247,
`APPENDIX_SPAN` 521 → 537, the chained absorption **59 → 61** carriers.

⚠ That last figure read "58 → 60" until 2026-07-31 and was off by one at BOTH ends — corrected
against the emitted constant rather than re-guessed. Carriers per block are `1 + (numPreLimbs - 4)/3`
(one arity-4 head site, then arity-3 body groups): `1 + 174/3 = 59` at 178, `1 + 180/3 = 61` at 184.
`layout_generated.rs` emits `B_NUM_CHAIN = 61` and `B_SPAN - B_CHAIN_BASE = 247 - 186 = 61` agrees.

⚑ **AND THE COST OF THE ALTERNATIVE, since it gets proposed.** `docs/DESIGN-canonical-byte-felt-codec.md`
recommends `Limbs16` (sixteen u16 limbs) as the tree's canonical byte→felt map, and it is the right
call at an ABSORBED site — 16 lanes is exactly one `CHIP_RATE` absorb, so the width is free there.
It is the wrong call HERE, because these are PERSISTENT COLUMNS, not absorb rate. Eight fields × 16
lanes is 128 columns against the nonet's 72: `numPreLimbs` 184 → 240, which **fails `bodyAligned`**
(`236 % 3 = 2`), so it would have to be 241 with a column wasted. That gives 80 carriers per block,
`B_SPAN` 323 and `APPENDIX_SPAN` 689 — **+152 columns on every one of the 174 members and +38
Poseidon2 absorptions per row** — to buy the same property the nonet already has, since both are
injective and the anchor's strength is the sponge's either way. And `Limbs16` cannot hold lane 0:
a 16-bit lane cannot carry the kernel's 32-bit u64-lane `lo32`, which `field_to_u64` and every
escrow/discharge/vault weld read. Nine is not a compromise here; it is the better encoding.

⚑⚑ **KEY-NONET FLAG DAY 2026-08-01: 184 → 187.** The same pigeonhole, at the three CARRIER OCTETS
(`child_vk` 89, `contract_hash` 97, `public_key` 105). The deployed packer
(`canonical_32_to_felts_8`) puts 32 bytes into eight lanes at `8+8+8+6 = 30` bits and DROPS bits 6-7
of bytes 3, 7, …, 31 — sixteen source bits — so it is not injective *trivially*, not merely by
counting; and among valid Ed25519 keys the collision cost is ZERO, because bit 7 of byte 31 is the
SIGN BIT and lies in the unread set, so a key and its negation pack to one octet and the negation is
a keypair the attacker holds the private half of. `Dregg2.Circuit.KeyLanes9.keyToLanes9` is the
base-`2^29` NONET that closes it (image EXACTLY `2^256`, injective by a machine-checked left
inverse), and each of the three octets needs a ninth column.

⚑ **AND IT GROWS BY THREE, NOT BY ONE.** `EffectVmEmitRotationV3.B_SPAN := n + 3 + (n − 4) / 3` is
`Nat` FLOOR division, while the real carrier chain is `chunk31`'s `chunkCount`, which steps every
three limbs and rounds UP. They agree exactly when `n ≡ 1 (mod 3)` — the invariant nobody had
written down. At `n = 185` the formula yields 60 carriers where `chunkCount` needs 61 and the block
is silently ONE CARRIER COLUMN SHORT; 186 is worse (62 vs 60) and also fails `bodyAligned`
(`182 % 3 = 2`). 187 is the next legal extent, `(187 − 4) % 3 = 0`, and it buys exactly the three
ninth lanes the three carrier octets demand. Downstream: `B_SPAN` 247 → 251, `B_IROOT` 184 → 187,
`B_STATE_COMMIT` 185 → 188, the chain band `186..246` → `189..250` (61 → 62 carriers),
`CANON9_REGION_OFF` 539 → 547, `APPENDIX_SPAN` 651 → 659, `CAVEAT_REGION_OFF` 494 → 502. Every
column `0..183` keeps its meaning; 184/185/186 are NEW. -/
def rotatedNumPreLimbs : Nat := 196

/-- The CURRENT deployed rotated geometry (196 pre-iroot limbs). This enumeration is a complete
tiling of `0..195`: every column once, the two pads 194, 195 included.

⚑⚑⚑ **IROOT-WIDENING FLAG DAY 2026-11-07: 187 → 196.** The receipt-log root's lanes 1..7 take the
new columns 187..193, and `Legal.bodyAligned` (`n ≡ 1 mod 3`) makes 194 illegal, so the extent is
196 and 194, 195 are pads (the producers write zero; a pad is absorbed, so a nonzero pad moves the
anchor, it cannot hide a state). Every column `0..186` keeps its meaning. -/
def rotated196 : RotatedLayout where
  numPreLimbs := rotatedNumPreLimbs
  singles := [1, 2, 3,                       -- r0/r1/r2 = bal_lo/nonce/bal_hi (cells lane-0 is a group)
              4, 5, 6, 7, 8, 9, 10, 11,      -- r3..r10 = fields[0..7] lane-0 (welded)
              29, 30, 31, 32, 35]            -- lifecycle, epoch, committed_height, disc, mode
  groups := [
    (.authority,   ⟨24, [12, 13, 14, 15, 16, 17, 18]⟩),
    (.cap,         ⟨25, [52, 53, 54, 55, 56, 57, 58]⟩),
    (.nullifier,   ⟨26, [68, 69, 70, 71, 72, 73, 74]⟩),
    (.commitments, ⟨27, [75, 76, 77, 78, 79, 80, 81]⟩),
    (.heap,        ⟨28, [59, 60, 61, 62, 63, 64, 65]⟩),
    (.perms,       ⟨33, [38, 39, 40, 41, 42, 43, 44]⟩),
    (.vk,          ⟨34, [45, 46, 47, 48, 49, 50, 51]⟩),
    (.fields,      ⟨36, [66, 67, 19, 20, 21, 22, 23]⟩),  -- non-contiguous: reuses headroom 19..23
    (.revoked,     ⟨37, [82, 83, 84, 85, 86, 87, 88]⟩),
    -- WOUND #23 (`docs/WOUND-felt-width-boundaries-2026-07-19.md`): this completion group used to be
    -- documented "circuit-only, producer-zero" — and it WAS zero in both Rust producers, which made
    -- the committed `cells_root` a ~31-bit COMPONENT inside the faithful 8-felt consensus anchor.
    -- Both producers (`rotation_witness::produce`, `commitment::compute_rotated_pre_limbs`) now fill
    -- all eight lanes on EVERY turn from the native `CanonicalHeapTree8` root; the
    -- createCell/factory/spawn trace generator still OVERWRITES the group with its own in-circuit
    -- accounts tree (the grow-gate's object). A layout slot is not a binding — read the WRITER.
    (.cells,       ⟨0, [169, 170, 171, 172, 173, 174, 175]⟩)]
  octets := [89, 97, 105]                    -- child_vk, contract_hash, pubkey octet bases
  -- ⚑ THE KEY-NONET FLAG DAY'S THREE NEW COLUMNS, positionally parallel to `octets`: child_vk's
  -- ninth lane is 184, contract_hash's is 185, and the OWNER KEY's is 186. All three are past the
  -- old extent, so nothing below 184 moves; all three are `< numPreLimbs`, so all three are
  -- ABSORBED by `wireCommitR` and reach `state_commit` (which is the entire point — an appendix
  -- column would leave the anchor binding 232 bits of a 256-bit key).
  octetNinthLanes := [184, 185, 186]
  -- ⚑ 56 → 64. Lanes 1..7 of each `fields[slot]` keep their historical window `113 + 7·slot .. +6`
  -- (113..168, UNMOVED); the NINTH lane of slot `j` is the new column `176 + j` (176..183). The
  -- first two of those were the layout's only free pads; the remaining six are the extent bump.
  fieldsOctet := (List.range 56).map (· + 113) ++ (List.range 8).map (· + 176)
  cellsCompletion := []                      -- (cells is now a group; kept for structural symmetry)
  irootCompletion := [187, 188, 189, 190, 191, 192, 193]   -- iroot8 lanes 1..7 (lane 0 is B_IROOT)
  pads := [194, 195]                         -- the 1-mod-3 body discipline's two spare columns

/-- **THE NINTH-LANE PROJECTION** — the single source a consumer reads a `fields[slot]` lane column
from. Lane 0 is the welded v1 face limb `4 + slot` (`gFieldWriteP1` / `param1` / `field_to_u64`);
lanes 1..7 are the historical completion window; lane 8 is the flag-day column `176 + slot`.

Consumers must read THIS, never `113 + 8·slot` — the nonet is deliberately NON-CONTIGUOUS so the
flag day shifts no existing column, exactly like the `fields` root group already reuses headroom
19..23. -/
def fieldLaneCol (slot : Fin 8) (lane : Fin 9) : Nat :=
  if lane.1 = 0 then 4 + slot.1
  else if lane.1 = 8 then 176 + slot.1
  else 113 + 7 * slot.1 + (lane.1 - 1)

/-- The current layout is LEGAL — every semantic group exists exactly once at width eight, every
    carrier octet is a NONET, and the complete tiling is disjoint, in-bounds, and body-aligned. -/
theorem rotated196_legal : Legal rotated196 where
  groupWidth  := by native_decide
  groupNames  := by native_decide
  groupCoverage := by intro name; cases name <;> native_decide
  octetNonets := by native_decide
  irootWidth  := by native_decide
  disjoint    := by native_decide
  inBounds    := by native_decide
  bodyAligned := by native_decide

/-- STRONGER than `Nodup`: the layout occupies EXACTLY 196 columns. With `disjoint` + `inBounds` this
    forces a complete tiling of `0..195` — no gaps, no reuse; the only unassigned columns are the
    two named pads. -/
theorem rotated196_complete : rotated196.occupied.length = 196 := by native_decide

/-- **THE RECEIPT-ROOT PROJECTION.** Lane 0 of `iroot8` is `B_IROOT = numPreLimbs`; lanes 1..7 are
the layout's `irootCompletion`. -/
def RotatedLayout.irootLaneCol (L : RotatedLayout) (lane : Fin 8) : Option Nat :=
  if (lane : Nat) = 0 then some L.numPreLimbs else L.irootCompletion[(lane : Nat) - 1]?

theorem iroot_lane_cols :
    (List.range 8).map (fun l => (rotated196.irootLaneCol ⟨l % 8, by omega⟩).getD 0)
      = [196, 187, 188, 189, 190, 191, 192, 193] := by native_decide

/-- ⚑ **AND THEY ARE ABSORBED**: lanes 1..7 are pre-limbs, so they enter `preLimbsAt` and reach
`state_commit` through `wireCommitR` / `wireCommitR8`; lane 0 is absorbed last at `B_IROOT`. -/
theorem iroot_completion_absorbed :
    ∀ c ∈ rotated196.irootCompletion, c ∈ List.range rotated196.numPreLimbs := by native_decide

theorem iroot_completion_is_new : ∀ c ∈ rotated196.irootCompletion, 187 ≤ c := by native_decide

/-- **THE FIELDS-NONET FLAG DAY (178 → 184) SHIFTED NOTHING**, and still does not: the ninth lane of
`fields[j]` is `176 + j`, all eight in `176..183`, every one at or above the old 178 extent's two
free pads. -/
theorem fields_ninth_lanes :
    (List.range 8).map (fun j => fieldLaneCol ⟨j % 8, by omega⟩ 8) = [176, 177, 178, 179, 180, 181, 182, 183] := by
  native_decide

theorem fields_ninth_lanes_are_new :
    ∀ c ∈ (List.range 8).map (fun j => fieldLaneCol ⟨j % 8, by omega⟩ 8), 176 ≤ c := by
  native_decide

/-- Every lane column the nonet projection names really is an occupied column of the layout, and the
72 of them (8 slots × 9 lanes) are pairwise distinct — the invariant that was a comment. -/
theorem fieldLaneCol_occupied :
    ∀ p ∈ (List.range 8).flatMap (fun j => (List.range 9).map (fun l =>
      fieldLaneCol ⟨j % 8, by omega⟩ ⟨l % 9, by omega⟩)), p ∈ rotated196.occupied := by
  native_decide

theorem fieldLaneCol_nodup :
    ((List.range 8).flatMap (fun j => (List.range 9).map (fun l =>
      fieldLaneCol ⟨j % 8, by omega⟩ ⟨l % 9, by omega⟩))).Nodup := by
  native_decide

/-! ### ⚑ THE KEY-NONET FLAG DAY (184 → 187), as facts rather than as prose. -/

/-- **THE THREE NEW COLUMNS, AND WHERE THEY GO.** `child_vk`'s ninth lane is 184,
`contract_hash`'s is 185, and the OWNER KEY's is 186 — read out of the layout's own
`octetNinthLanes`, not re-spelled. -/
theorem octet_ninth_lanes :
    (List.range 3).map (fun o => (rotated196.octetLaneCol o 8).getD 0) = [184, 185, 186] := by
  native_decide

/-- **THE OWNER KEY'S NINTH LANE.** `KeyCanonicity9Emit.deployedKeyCols` is instantiated at exactly
this in-block offset; `EffectVmEmitRotationV3.B_PUBKEY_NINTH_LANE` projects it. -/
theorem pubkey_octet_lane_cols :
    (List.range 9).map (fun l => (rotated196.octetLaneCol 2 ⟨l % 9, by omega⟩).getD 0)
      = [105, 106, 107, 108, 109, 110, 111, 112, 186] := by
  native_decide

/-- **THE THREE NEW COLUMNS ARE NEW.** Every ninth lane is at or past the old 184-column extent, so
no column that had a meaning at 184 acquires a second one. -/
theorem octet_ninth_lanes_are_new :
    ∀ c ∈ rotated196.octetNinthLanes, 184 ≤ c ∧ c < rotatedNumPreLimbs := by
  native_decide

/-- ⚑ **AND THEY ARE ABSORBED** — every ninth lane is a PRE-LIMB (`< numPreLimbs`), so it enters
`preLimbsAt`, is folded by `wireCommitR`, and reaches `state_commit`. An appendix column would
satisfy every other obligation in this file and bind NOTHING. -/
theorem octet_ninth_lanes_absorbed :
    ∀ c ∈ rotated196.octetNinthLanes, c ∈ List.range rotated196.numPreLimbs := by
  native_decide

/-- Every column the carrier-octet nonet projection names is an occupied column, and the 27 of them
(3 octets × 9 lanes) are pairwise distinct. -/
theorem octetLaneCol_occupied :
    ∀ p ∈ (List.range 3).flatMap (fun o => (List.range 9).map (fun l =>
      (rotated196.octetLaneCol o ⟨l % 9, by omega⟩).getD 0)), p ∈ rotated196.occupied := by
  native_decide

theorem octetLaneCol_nodup :
    ((List.range 3).flatMap (fun o => (List.range 9).map (fun l =>
      (rotated196.octetLaneCol o ⟨l % 9, by omega⟩).getD 0))).Nodup := by
  native_decide

/-- ⚑ **THE COUNTING INVARIANT, WRITTEN DOWN AT LAST.** `EffectVmEmitRotationV3.B_SPAN`'s
`(n − 4) / 3` is floor division; `chunk31`'s `chunkCount` rounds up. They agree exactly on
`n ≡ 1 (mod 3)`, and `Legal.bodyAligned` is that congruence. 185 and 186 are BOTH illegal — 185
would have left the block one carrier column short while every `#guard` in the emit still passed. -/
theorem the_extent_is_one_mod_three : rotatedNumPreLimbs % 3 = 1 := by native_decide

theorem neither_194_nor_195_is_body_aligned :
    (194 - 4) % 3 ≠ 0 ∧ (195 - 4) % 3 ≠ 0 ∧ (196 - 4) % 3 = 0 := by native_decide

theorem neither_185_nor_186_is_body_aligned :
    (185 - 4) % 3 ≠ 0 ∧ (186 - 4) % 3 ≠ 0 ∧ (187 - 4) % 3 = 0 := by native_decide

/-- Sanity: the projection agrees with the raw group data (nullifier lane 0 = limb 26, lane 1 = 68). A
    Phase-2 bridge theorem will pin each emit `*GroupCol` to exactly `rotated196.groupCol`. -/
example : rotated196.groupCol .nullifier 0 = some 26 := by native_decide
example : rotated196.groupCol .nullifier 1 = some 68 := by native_decide
example : rotated196.groupCol .fields 1 = some 66 := by native_decide  -- the non-contiguous case

/-- **EMIT-READY group table** — each group as `[lane0, completion_1 .. completion_7]`, in exactly the
    shape the Rust `[[usize; 8]; N]` layout wants. `EmitLayoutManifest.lean` exports this value into
    `layout_generated.rs`; Rust names are projections of the emitted table, never another data copy. -/
def RotatedLayout.groupTable (L : RotatedLayout) : List (List Nat) :=
  L.groups.map (fun p => p.2.lane0 :: p.2.completion)

/-- The emit-ready table for the current geometry, with its length pinned (10 faithful-8-felt groups). -/
theorem rotated196_groupTable_len : rotated196.groupTable.length = 10 := by native_decide

/-- Every emitted row has the Rust type's exact width. This is a `Legal` obligation, not an emitter
    convention that could fail only after generation. -/
theorem rotated196_groupTable_row_width :
    ∀ row ∈ rotated196.groupTable, row.length = 8 := by native_decide

/-- Ten faithful-8 groups contribute exactly 80 occupied columns. -/
theorem rotated196_groupTable_flatten_len : rotated196.groupTable.flatten.length = 80 := by native_decide

end Dregg2.Circuit.Emit
