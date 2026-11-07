/-
# Dregg2.Circuit.Emit.KeyCanonicity9Emit — `CanonicalKey9`, EMITTED.

## SUBSTRATE, SAID OUT LOUD

Lean-authored AIR. The constraints below are emitted from Lean; Rust re-reads the descriptor and
never hand-writes a gate, a lookup or an `air_accepts`.

## ⚑ READ `Dregg2.Circuit.KeyLanes9` FIRST — THIS FILE DOES NOT WRAP THE DEPLOYED ENCODER

The obvious task was "apply `FieldsCanonicity9Emit` to the owner-key octet". `KeyLanes9`
REFUTES that, with an exhibit: `eight_lane_canonicity_is_not_a_repair` produces two DISTINCT 32-byte
keys whose deployed octets are equal AND fully canonical (`canonical_32_to_felts_8` packs
`8+8+8+6 = 30` bits and drops bits 6-7 of every fourth byte). `keyCanonical8_iff_in_image` proves
`[0,2^30)^8` is EXACTLY that packer's image, so there is no missing leg to find and no stronger
eight-lane wrap to write. **A canonicity envelope on the deployed octet would force the columns into
the image of a map that is not injective on its domain** — a containment shipped while the real fix
is named as a later phase, which is the substitution this repo's own doctrine forbids.

So this file emits the envelope of the REPLACEMENT nine-lane encoder (`KeyLanes9.keyToLanes9`,
injective by a machine-checked left inverse), not of the deployed eight-lane one.

## The gadget — and there is no gadget

Per rotated block, NINE lookups and NOTHING ELSE:

```text
  lanes 0..7  < 2^29        -- eight lookups on the LANE table
  lane  8     < 2^24        -- ONE lookup, on a NARROWER table
```

Zero gates. Zero aux columns. Zero new hash sites. `KeyLanes9.canonicalKey9_iff_in_image` proves
those two legs are EXACTLY the image, so the wrap admits every honest key's nonet and no other
vector. The fields wrap needed seven aux columns, a cube gate and a doubled selector because its
lanes 0/1 were a `mod p` REDUCTION welded to the v1 face and therefore unmovable; the key octet is
welded to nothing (measured 2026-07-31: zero `colEq`, zero gate bodies, zero `pi_binding`s, zero
range lookups across all 117 rotated members), so the encoding was replaced wholesale and the
reduction — and with it `NoWrap`, the cube gate and the aux region — disappeared.

Two consequences worth stating because the fields wrap could not claim either:

  * **`keyCanon9_forces_canonical` needs no non-last-row hypothesis.** A `gate` is exempt on the last
    row until `hardenLastRow` lifts it; a `lookup` is not. Every leg here is a lookup.
  * **It needs no canonical-column envelope hypothesis either.** The fields forcing had to assume
    `0 ≤ col < p` for lanes 0/1 and the aux columns, because no lookup covered them. Here all NINE
    lanes are covered, so both bounds come from the emitted constraints themselves.

## ⚑ THE EXHIBIT, AND WHY LEG 2 IS NOT DECORATION

`forgedKeyNonet = [0,…,0,2^24]`. Every lane is below `2^29`, so the NAIVE wrap — nine lookups all at
the lane width, which is what "range-check the lanes" means to a reader who has not done the
arithmetic — accepts it. Its recomposed value is `2^24 · (2^29)^8 = 2^256` exactly: one full wrap of
the byte window, so the total decoder reads all thirty-two base-256 digits as zero and it decodes to
the ALL-ZERO key, byte for byte, while being a different committed vector.
`the_forged_nonet_passes_the_naive_wrap_and_is_unsat_here` bundles all three facts, and
`keyCanon9_rejects_the_forged_nonet` lifts the refusal to `¬ Satisfied2` over the emitted
constraints. The UNSAT is total: no assignment of anything else can rescue it, because the narrow
table simply does not contain the row.

## ⚑ WHAT RUNG THIS REACHES — say it exactly

**AUTHORED, PROVED, AND GEOMETRICALLY PLACED. NOT APPENDED TO ANY LIVE MEMBER'S CONSTRAINT LIST,
NOT RE-EMITTED INTO ANY DESCRIPTOR, AND NOT CONSUMED BY ANY VERIFIER.**

⚑ **CORRECTED 2026-08-01 (a) — the forcing and the capstone used to quantify over an arbitrary
`col : KeyColMap`.** Only lane 8's column was unknown; the other eight are `B_PUBKEY_OCTET` at stride
`B_SPAN`, which `deployedKeyCols` already recorded and four `#guard`s already knew. A theorem named
"determines the owner key" that quantifies over the column map determines whatever nine columns it
is handed — strictly weaker on the column axis than this file's own template
(`FieldsCanonicity9Emit.canon9_forces_canonical` takes a face width and reads the concrete
`laneColAt`), while the write-up presented the abstraction as scrupulousness. `§1.1` ties lanes 0..7
to the ABSORBED pre-limbs `wireCommitR` folds (`deployedKeyCols_octet_is_absorbed`). The old shape
was not merely unproved on that axis but REFUTABLE: with the block span free, `span := 0` put both
blocks' lanes on the BEFORE octet.

✅ **LANDED 2026-08-01 (b) — THE NINTH LANE NOW EXISTS.** `rotatedNumPreLimbs` went **184 → 187**
and `RotatedLayout.rotated196.octetNinthLanes = [184, 185, 186]` allocates one ninth lane per carrier
octet; the owner key's is in-block limb **186**. So `lane8Off` is no longer a parameter either:

  * `deployedKeyCanon9Cols w := deployedKeyCols w B_PUBKEY_NINTH_LANE` leaves nothing free but the
    face width, which genuinely differs member to member;
  * `deployed_nonet_is_absorbed` proves ALL NINE lanes are entries of `preLimbColsAt`, i.e. of the
    list `wireCommitR` folds into `state_commit`. An appendix column would have satisfied every
    other obligation here and bound nothing — `lane8_is_absorbed_iff` is that criterion as an IFF,
    and it was FALSE at every offset of the 184-limb geometry;
  * `keyCanon9_determines_the_owner_key_deployed` is the capstone stated against `preLimbsAt`
    entries rather than bare columns, so it is a sentence about what the consensus anchor binds;
  * `the_ninth_lane_offset_is_load_bearing` + `lane8_offset_plus_one_is_not_absorbed` are the
    mutation: **+1** lands on `B_IROOT` (not a pre-limb, so the lane leaves the absorbed region and
    the wrap would bind 232 bits while proving identically); **−1** lands on `contract_hash`'s ninth
    lane (an alias, which `Legal.disjoint` refuses).

**Why 187 and not 185.** `B_SPAN := n + 3 + (n − 4) / 3` is `Nat` FLOOR division while the real
carrier chain is `chunk31`'s `chunkCount`, which rounds UP. They agree exactly on `n ≡ 1 (mod 3)`.
At 185 the formula says 60 carriers where the chain needs 61 — the block is silently one column
short and every other `#guard` still passes. `EffectVmEmitRotationV3` now pins the formula against
the LITERAL `rotV3SitesAt` walk so that failure cannot be silent again.

**What this flag day breaks, and what must be redone.** Every `state_commit` moves, so this is a
**RE-GENESIS**: bump `persist`'s `CANONICAL_STATE_SCHEMA_EPOCH` (read the constant; do not
transcribe a remembered number) so a pre-flip image REFUSES TO LOAD rather than reinterpreting its
limbs. `B_IROOT` 184 → 187, `B_STATE_COMMIT` 185 → 188, the chain band `186..246` → `189..250`,
`B_SPAN` 247 → 251, `CAVEAT_REGION_OFF` 494 → 502, `CANON9_REGION_OFF` 539 → 547, `APPENDIX_SPAN`
651 → 659, appendix sites 136 → 138, `CUSTOM_COMMIT_TEETH_COL` 1791 → 1813. Re-emit every v3
descriptor, `layout_generated.rs`, the staged registry TSVs and every VK; re-pin every hand-carried
Rust literal in `trace_rotated.rs` / `exact_nullifier_aafi_rotated_trace.rs` /
`shielded_ring_clearing_air.rs` / `rotation_witness.rs` / `cell/src/commitment.rs`; add `29` to
`CUSTOM_RANGE_WIDTHS`; and write a Rust `key_limbs9` producer that FILLS limb 186 (and 184/185) —
without it every honest turn is UNSAT, and with an 8-lane packer behind it the wound is re-opened.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.FieldsCanonicity9Emit
import Dregg2.Circuit.KeyLanes9

namespace Dregg2.Circuit.Emit.KeyCanonicity9Emit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit (rotatedNumPreLimbs)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (rangeTidW)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (B_SPAN B_PUBKEY_OCTET B_PUBKEY_NINTH_LANE
  preLimbsAt)
open Dregg2.Circuit.Emit.FieldsCanonicity9Emit (faceWidthOfName)
open Dregg2.Circuit.FieldLanes9 (Bytes32)
open Dregg2.Circuit.KeyLanes9 (K KTOP Nonet CanonicalKey9 LanesRanged TopLaneRanged UniformRanged
  keyToLanes9 keyLanes9ToBytes keyToLanes9_injective canonicalKey9_iff_in_image forgedKeyNonet
  zeroKey keyLanes9ToBytes_keyToLanes9)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8000

/-! ## §0 — the two range widths this emit introduces. -/

/-- The nonet's lane width: `2^29 < p`, so a lane NEVER reduces. Eight lookups ride this. -/
def KEY_LANE_BITS : Nat := 29

/-- ⚑ **THE NARROW LEG.** `2^256 / (2^29)^8 = 2^24`, so the top lane's weight leaves exactly this
much room. A lane-width lookup on lane 8 would leave `2^5` whole wraps of the byte window
available — `forgedKeyNonet` is the first of them. -/
def KEY_TOP_BITS : Nat := 24

theorem widths_are_the_exact_fit : 2 ^ (8 * KEY_LANE_BITS + KEY_TOP_BITS) = 2 ^ 256 := by
  norm_num [KEY_LANE_BITS, KEY_TOP_BITS]

theorem lane_width_is_K : (2 : Nat) ^ KEY_LANE_BITS = K := by
  norm_num [KEY_LANE_BITS, Dregg2.Circuit.KeyLanes9.K]

theorem top_width_is_KTOP : (2 : Nat) ^ KEY_TOP_BITS = KTOP := by
  norm_num [KEY_TOP_BITS, Dregg2.Circuit.KeyLanes9.KTOP]

/-! ## §1 — the emitted columns. ⚑ `lane8Off` IS THE ONLY PARAMETER.

**This file used to quantify over an arbitrary `col : KeyColMap` everywhere, including in the
capstone, and that was strictly weaker than its own template.** `FieldsCanonicity9Emit` takes a face
width and reads the concrete `laneColAt`; here EIGHT of the nine columns are equally fixed and known
— `B_PUBKEY_OCTET` at stride `B_SPAN` — and a theorem named "determines the owner key" that
quantifies over the column map determines whatever nine columns it is handed. The abstraction was
justified by "lane 8's column does not exist", which is true of lane 8 and of nothing else.

So: `w` is the face width (exactly as the fields template takes it), `lane8Off` is the one genuinely
unallocated offset, and everything that claims anything about the OWNER KEY is stated at
`deployedKeyCols w lane8Off`. `KeyColMap` survives as the type of the column-agnostic PLUMBING in §2
and §3 (`blk_mem`, `lookup_forces`, the peel) — those name no key and claim none. -/

/-- The nine committed columns of each rotated block's owner-key nonet. -/
abbrev KeyColMap := Fin 2 → Fin 9 → Nat

/-- **THE DEPLOYED COLUMNS.** Lanes 0..7 at `B_PUBKEY_OCTET .. +8` of block `blk` at the verified
stride `B_SPAN` — both read from `EffectVmEmitRotationV3`, never re-spelled here — and lane 8 at a
caller-supplied in-block offset that the geometry move must allocate as an absorbed PRE-LIMB (not an
appendix column: see the header, and `lane8_is_absorbed_iff` below for that as a theorem). -/
def deployedKeyCols (w lane8Off : Nat) : KeyColMap := fun blk lane =>
  if lane.1 < 8 then w + blk.1 * B_SPAN + B_PUBKEY_OCTET + lane.1
  else w + blk.1 * B_SPAN + lane8Off

/-- Lane `l < 8` sits at the octet's `l`-th offset inside its block. -/
theorem deployedKeyCols_octet_col (w lane8Off : Nat) (blk : Fin 2) {l : Fin 9} (hl : l.1 < 8) :
    deployedKeyCols w lane8Off blk l = w + blk.1 * B_SPAN + (B_PUBKEY_OCTET + l.1) := by
  simp only [deployedKeyCols]
  rw [if_pos hl]
  omega

/-- …and lane 8 sits at the offset the geometry move has yet to allocate. -/
theorem deployedKeyCols_lane8_col (w lane8Off : Nat) (blk : Fin 2) :
    deployedKeyCols w lane8Off blk 8 = w + blk.1 * B_SPAN + lane8Off := by
  simp [deployedKeyCols]

/-- ⚑ **THE DEPLOYED NINTH-LANE OFFSET.** No longer a parameter and no longer an illustration: the
2026-08-01 key-nonet flag day took `rotatedNumPreLimbs` 184 → 187 and allocated in-block limb 186 to
the owner key's ninth lane. Read from `EffectVmEmitRotationV3`, which reads it from the verified
`RotatedLayout.octetLaneCol`; this file re-spells nothing. -/
abbrev deployedLane8Off : Nat := B_PUBKEY_NINTH_LANE

/-- **THE FULLY DEPLOYED COLUMN MAP** — nothing left free but the face width `w`, which is the one
thing that genuinely differs member to member. -/
def deployedKeyCanon9Cols (w : Nat) : KeyColMap := deployedKeyCols w deployedLane8Off

/-! ### The nine offsets, against the committed layout constants.

Rust twins `trace_rotated::B_PUBKEY_OCTET = 105` and `::B_PUBKEY_NINTH_LANE = 186`, both generated
from `EmitLayoutManifest`. Re-typed by hand against a committed artifact: the literals ARE the
review. At today's `188`-wide bare v1 face and `B_SPAN = 251` the BEFORE nonet is `293..300` + `374`
and the AFTER nonet is `544..551` + `625`.

⚑ These seven were `#guard`s until 2026-08-03 (`docs/GUARD-DISCIPLINE.md`). Every assertion below is
the one the guard made, over the same object, now named, citable and visible to `#assert_axioms` —
and the `Nodup` pin GAINED A `∀`: `deployed_nonet_cols_nodup` holds at EVERY face width, which the
`188` instance could not distinguish from "they happen not to collide at 188". -/

theorem B_PUBKEY_OCTET_is_105 : B_PUBKEY_OCTET = 105 := rfl

theorem deployedLane8Off_is_186 : deployedLane8Off = 186 := rfl

/-- `B_SPAN` as a numeral. Not a pin — it is a def against its own definition, which is decoration —
but the rewrite `omega` needs to see the block stride in `deployed_nonet_cols_distinct`. -/
private theorem b_span_is_263 : B_SPAN = 263 := rfl

theorem deployedKeyCanon9Cols_before_octet :
    (List.finRange 8).map (fun l => deployedKeyCanon9Cols 188 0 ⟨l.1, by omega⟩)
      = [293, 294, 295, 296, 297, 298, 299, 300] := by decide

theorem deployedKeyCanon9Cols_before_lane8 : deployedKeyCanon9Cols 188 0 8 = 374 := by decide

theorem deployedKeyCanon9Cols_after_octet :
    (List.finRange 8).map (fun l => deployedKeyCanon9Cols 188 1 ⟨l.1, by omega⟩)
      = [556, 557, 558, 559, 560, 561, 562, 563] := by decide

theorem deployedKeyCanon9Cols_after_lane8 : deployedKeyCanon9Cols 188 1 8 = 637 := by decide

/-- ⚑ **THE NONET OCCUPIES EIGHTEEN DISTINCT COLUMNS — AT EVERY FACE.** The general fact the `188`
`Nodup` pin was one instance of: a column of the deployed nonet determines both its BLOCK and its
LANE. Two lanes of one block cannot alias (the octet is contiguous and the ninth lane is `74` past
its end), and no lane of the BEFORE block can alias one of the AFTER block (the whole nonet spans
`81 < B_SPAN` columns). Stated at an arbitrary `w`, so a face-width move cannot collapse it. -/
theorem deployed_nonet_cols_distinct (w : Nat) {blk blk' : Fin 2} {l l' : Fin 9}
    (h : deployedKeyCanon9Cols w blk l = deployedKeyCanon9Cols w blk' l') :
    blk = blk' ∧ l = l' := by
  have hb := blk.isLt; have hb' := blk'.isLt
  have hl := l.isLt; have hl' := l'.isLt
  simp only [deployedKeyCanon9Cols, deployedKeyCols, b_span_is_263, B_PUBKEY_OCTET_is_105,
    deployedLane8Off_is_186] at h
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> (split_ifs at h with h1 h2 <;> omega)

/-- The eighteen committed nonet columns of the two rotated blocks are pairwise distinct, at every
face width. -/
theorem deployed_nonet_cols_nodup (w : Nat) :
    ((List.finRange 9).map (deployedKeyCanon9Cols w 0)
      ++ (List.finRange 9).map (deployedKeyCanon9Cols w 1)).Nodup := by
  refine List.Nodup.append ?_ ?_ ?_
  · exact List.Nodup.map (fun _ _ h => (deployed_nonet_cols_distinct w h).2) (by decide)
  · exact List.Nodup.map (fun _ _ h => (deployed_nonet_cols_distinct w h).2) (by decide)
  · intro a ha hb
    simp only [List.mem_map] at ha hb
    obtain ⟨l, -, rfl⟩ := ha
    obtain ⟨l', -, hEq⟩ := hb
    exact absurd (deployed_nonet_cols_distinct w hEq).1 (by decide)

/-- ⚑ THE OCTET DID NOT MOVE. `293..300` is byte-for-byte the BEFORE window the 184-limb geometry
had; what moved is the AFTER block (`540..547` → `544..551`, because `B_SPAN` 247 → 251) and the
whole absorption tail. Every `state_commit` therefore changes: this is a RE-GENESIS. (The instance
the `#guard` asserted, kept as a corollary so no assertion is lost.) -/
theorem deployed_nonet_cols_nodup_188 :
    ((List.finRange 9).map (deployedKeyCanon9Cols 188 0)
      ++ (List.finRange 9).map (deployedKeyCanon9Cols 188 1)).Nodup :=
  deployed_nonet_cols_nodup 188

#assert_axioms B_PUBKEY_OCTET_is_105
#assert_axioms deployedLane8Off_is_186
#assert_axioms deployedKeyCanon9Cols_before_octet
#assert_axioms deployedKeyCanon9Cols_before_lane8
#assert_axioms deployedKeyCanon9Cols_after_octet
#assert_axioms deployedKeyCanon9Cols_after_lane8
#assert_axioms deployed_nonet_cols_distinct
#assert_axioms deployed_nonet_cols_nodup
#assert_axioms deployed_nonet_cols_nodup_188

/-! ### ⚑ §1.1 — THE COLUMNS ARE THE ABSORBED OWNER-KEY LIMBS, from two sources that are not each
other.

Pinning the eight is not tidiness. `preLimbsAt` is the list `wireCommitR` folds into `state_commit`;
a column outside it is a free felt the anchor never sees, which is the whole reason the ninth lane
cannot ride the appendix. So "this wrap constrains the owner key" is exactly the claim that its
columns ARE entries of THAT list at the octet's position — a statement relating `deployedKeyCols`
here to `EffectVmEmitRotationV3.preLimbsAt` there, not a constant checked against its own def.

Before this section existed, no THEOREM in the file mentioned `B_PUBKEY_OCTET` — only the `def` and
four `#guard`s did — and the octet tie was not merely unproved but REFUTABLE: with the block span a
free parameter, taking `span := 0` collapses both blocks' lanes 0..7 onto the BEFORE octet. -/

/-- The absorbed pre-limb COLUMNS of the block at `base`, positionally — `preLimbsAt` read as
addresses rather than values. -/
def preLimbColsAt (base : Nat) : List Nat := (List.range rotatedNumPreLimbs).map (base + ·)

theorem preLimbsAt_eq_rangeMap (base : Nat) (a : Assignment) :
    preLimbsAt base a = (List.range rotatedNumPreLimbs).map (fun k => a (base + k)) := rfl

theorem preLimbsAt_getD (base k : Nat) (a : Assignment) (hk : k < rotatedNumPreLimbs) :
    (preLimbsAt base a).getD k 0 = a (base + k) := by
  rw [preLimbsAt_eq_rangeMap, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

/-- **THE TIE.** Lane `l < 8` of the wrapped nonet reads pre-limb `B_PUBKEY_OCTET + l` of the very
list the rotated absorption chain folds — so the eight lookups land on the owner-key limbs
`state_commit` binds, and not on eight columns of this file's own choosing. -/
theorem deployedKeyCols_octet_is_absorbed (w lane8Off : Nat) (a : Assignment) (blk : Fin 2)
    {l : Fin 9} (hl : l.1 < 8) :
    a (deployedKeyCols w lane8Off blk l)
      = (preLimbsAt (w + blk.1 * B_SPAN) a).getD (B_PUBKEY_OCTET + l.1) 0 := by
  rw [deployedKeyCols_octet_col w lane8Off blk hl,
    preLimbsAt_getD _ _ _ (by have := l.isLt; simp only [B_PUBKEY_OCTET, rotatedNumPreLimbs]; omega)]

/-- The same fact as membership: every one of the eight is an absorbed column. -/
theorem octet_cols_are_absorbed (w lane8Off : Nat) (blk : Fin 2) {l : Fin 9} (hl : l.1 < 8) :
    deployedKeyCols w lane8Off blk l ∈ preLimbColsAt (w + blk.1 * B_SPAN) := by
  rw [deployedKeyCols_octet_col w lane8Off blk hl]
  simp only [preLimbColsAt, List.mem_map, List.mem_range]
  refine ⟨B_PUBKEY_OCTET + l.1, ?_, rfl⟩
  have := l.isLt
  simp only [B_PUBKEY_OCTET, rotatedNumPreLimbs]
  omega

/-- ⚑ **WHERE THE NINTH LANE MAY LIVE — the criterion, as an IFF.** The ninth-lane column is
absorbed exactly when `lane8Off < rotatedNumPreLimbs`. Everything else is a free felt outside
`wireCommitR`, and in that case `state_commit` binds only the eight lanes — 232 bits of a 256-bit
key, which is the wound this wrap exists to close. At the 184-limb geometry NO offset satisfied it:
the pre-limb region was 184/184 occupied, so every choice was either an alias of a committed limb or
an appendix column. That is why the flag day had to move the EXTENT and not just add a lookup. -/
theorem lane8_is_absorbed_iff (w lane8Off : Nat) (blk : Fin 2) :
    deployedKeyCols w lane8Off blk 8 ∈ preLimbColsAt (w + blk.1 * B_SPAN)
      ↔ lane8Off < rotatedNumPreLimbs := by
  rw [deployedKeyCols_lane8_col]
  simp only [preLimbColsAt, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, hEq⟩; omega
  · intro h; exact ⟨lane8Off, h, rfl⟩

/-- ⚑ **AND THE DEPLOYED OFFSET SATISFIES IT.** Limb 186 is a pre-limb, so the owner key's ninth
lane is an entry of the very list `wireCommitR` folds. This is the sentence the whole flag day
exists to make true; it was FALSE at every offset of the 184-limb geometry. -/
theorem deployed_lane8_is_absorbed (w : Nat) (blk : Fin 2) :
    deployedKeyCanon9Cols w blk 8 ∈ preLimbColsAt (w + blk.1 * B_SPAN) :=
  (lane8_is_absorbed_iff w deployedLane8Off blk).mpr (by decide)

/-- **ALL NINE LANES ARE ABSORBED.** Not eight and a rider: the whole nonet is inside the domain
`state_commit` is a fold of. -/
theorem deployed_nonet_is_absorbed (w : Nat) (blk : Fin 2) (l : Fin 9) :
    deployedKeyCanon9Cols w blk l ∈ preLimbColsAt (w + blk.1 * B_SPAN) := by
  rcases Nat.lt_or_ge l.1 8 with h | h
  · exact octet_cols_are_absorbed w deployedLane8Off blk h
  · have : l = 8 := by apply Fin.ext; have := l.isLt; omega
    subst this
    exact deployed_lane8_is_absorbed w blk

/-- ⚑⚑ **THE MUTATION, BOTH DIRECTIONS.** The ninth lane's offset is load-bearing to ±1, and the
allocation is a choice and not an accident.

  * `+1` is `187`, lane 1 of the receipt-log root (the iroot-widening flag day, 187 -> 196, gave it
    that column). The pubkey nonet would ALIAS the receipt root, so neither would be injective.
    Placing the lane at `B_IROOT` (`= rotatedNumPreLimbs = 196`) instead is the other failure: that
    column is NOT a pre-limb, `wireCommitR` would never fold it as a key lane, and the emitted lookup
    would range-check a felt the anchor reads only as the receipt root —
    `lane8_at_B_IROOT_is_not_absorbed`.
  * `−1` is `contract_hash`'s ninth lane (185). The pubkey nonet would ALIAS another octet's nonet,
    so two 32-byte carriers would share a committed column and neither would be injective. The
    layout's `disjoint` obligation is what refuses that, and `RotatedLayout.octetLaneCol_nodup`
    exhibits the 27 projected columns as pairwise distinct.

Stated as facts a reader can check, not as prose. -/
theorem the_ninth_lane_offset_is_load_bearing :
    deployedLane8Off < rotatedNumPreLimbs
      ∧ ¬ (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_IROOT < rotatedNumPreLimbs)
      ∧ rotated196.irootLaneCol 1 = some (deployedLane8Off + 1)
      ∧ deployedLane8Off - 1
          = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_CONTRACT_HASH_NINTH_LANE := by
  refine ⟨by decide, by decide, rfl, by decide⟩

/-- The membership a misplacement breaks: put the ninth lane at `B_IROOT` and it LEAVES the
absorbed region, at every face width and both blocks. -/
theorem lane8_at_B_IROOT_is_not_absorbed (w : Nat) (blk : Fin 2) :
    deployedKeyCols w Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_IROOT blk 8
      ∉ preLimbColsAt (w + blk.1 * B_SPAN) := by
  intro h
  exact absurd ((lane8_is_absorbed_iff w _ blk).mp h) (by decide)

/-! ### The absorbed-region pins — ex-`#guard`s, and two of them were instances of theorems this
file had already proved three lines above. -/

theorem rotatedNumPreLimbs_is_196 : rotatedNumPreLimbs = 196 := rfl

theorem rotated196_pads : Dregg2.Circuit.Emit.rotated196.pads = [194, 195] := rfl

/-- ⚑ **THE EXTENT, AS A `∀`.** The absorbed-column list has exactly `rotatedNumPreLimbs` entries at
EVERY base — the guard fixed `188` and so could not tell a general fact about `preLimbColsAt` from a
coincidence at one face. -/
theorem preLimbColsAt_length (base : Nat) : (preLimbColsAt base).length = rotatedNumPreLimbs := by
  simp [preLimbColsAt]

theorem preLimbColsAt_length_188 : (preLimbColsAt 188).length = 196 := by
  rw [preLimbColsAt_length, rotatedNumPreLimbs_is_196]

/-- The whole NONET really is inside the absorbed region, at the BEFORE block — nine columns, not
eight. The `#guard`'s exact `Bool`, now discharged FROM `deployed_nonet_is_absorbed` rather than by
re-evaluating the list, which is what makes it visibly an instance. -/
theorem deployed_nonet_absorbed_before_188 :
    ((List.finRange 9).map (deployedKeyCanon9Cols 188 0)).all
      (fun c => (preLimbColsAt 188).contains c) = true := by
  simp only [List.all_eq_true, List.mem_map, List.contains_iff_mem]
  rintro c ⟨l, -, rfl⟩
  simpa using deployed_nonet_is_absorbed 188 0 l

/-- …and at the AFTER block. -/
theorem deployed_nonet_absorbed_after_188 :
    ((List.finRange 9).map (deployedKeyCanon9Cols 188 1)).all
      (fun c => (preLimbColsAt (188 + B_SPAN)).contains c) = true := by
  simp only [List.all_eq_true, List.mem_map, List.contains_iff_mem]
  rintro c ⟨l, -, rfl⟩
  simpa using deployed_nonet_is_absorbed 188 1 l

/-- …and the misplaced offset is NOT: the mutation, computably — the instance of
`lane8_at_B_IROOT_is_not_absorbed`. -/
theorem lane8_at_B_IROOT_not_absorbed_188 :
    (!(preLimbColsAt 188).contains
      (deployedKeyCols 188 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_IROOT 0 8)) = true := by
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
  simpa using lane8_at_B_IROOT_is_not_absorbed 188 0

#assert_axioms rotatedNumPreLimbs_is_196
#assert_axioms rotated196_pads
#assert_axioms preLimbColsAt_length
#assert_axioms preLimbColsAt_length_188
#assert_axioms deployed_nonet_absorbed_before_188
#assert_axioms deployed_nonet_absorbed_after_188
#assert_axioms lane8_at_B_IROOT_not_absorbed_188
#assert_axioms deployedKeyCols_octet_is_absorbed
#assert_axioms octet_cols_are_absorbed
#assert_axioms lane8_is_absorbed_iff
#assert_axioms deployed_lane8_is_absorbed
#assert_axioms deployed_nonet_is_absorbed
#assert_axioms the_ninth_lane_offset_is_load_bearing
#assert_axioms lane8_at_B_IROOT_is_not_absorbed

/-! ## §2 — the emitted constraints. -/

/-- A width-tagged range lookup (`EffectVmEmitV2.rangeLookupW`'s shape, at an explicit column). -/
def rangeLk (bits col : Nat) : VmConstraint2 := .lookup ⟨rangeTidW bits, [.var col]⟩

/-- One block's nine lookups: eight at the lane width, one at the narrow width. -/
def keyLookupsAt (col : KeyColMap) (blk : Fin 2) : List VmConstraint2 :=
  ((List.finRange 8).map (fun j => rangeLk KEY_LANE_BITS (col blk ⟨j.1, by have := j.isLt; omega⟩)))
    ++ [rangeLk KEY_TOP_BITS (col blk 8)]

/-- **THE EMIT** — `CanonicalKey9` over both rotated blocks' owner-key nonets. -/
def keyCanon9ConstraintsAt (col : KeyColMap) : List VmConstraint2 :=
  (List.finRange 2).flatMap fun blk => keyLookupsAt col blk

/-! ### 2 × 9 = 18 lookups, ZERO gates.

⚑ Three `#guard`s at `deployedKeyCanon9Cols 188` until 2026-08-03, and all three were instances of a
fact that does not mention the columns at all: the SHAPE of `keyCanon9ConstraintsAt` — two blocks,
eight-plus-one lookups each, no gate — is the same for EVERY column map. That is the general fact,
proved once; the `188` instances are the corollaries the guards asserted. -/

theorem keyCanon9ConstraintsAt_length (col : KeyColMap) :
    (keyCanon9ConstraintsAt col).length = 18 := rfl

theorem keyCanon9ConstraintsAt_length_188 :
    (keyCanon9ConstraintsAt (deployedKeyCanon9Cols 188)).length = 18 :=
  keyCanon9ConstraintsAt_length _

#assert_axioms keyCanon9ConstraintsAt_length
#assert_axioms keyCanon9ConstraintsAt_length_188

-- (the two `filter` counts are `keyCanon9ConstraintsAt_lookup_count` /
-- `…_gate_count` below, stated where `keyCanon9_all_lookups` — the theorem they are
-- corollaries of — is in scope.)

/-- **THE WRAP.** `traceWidth`-, `piCount`-, table-, site- and range-INVARIANT. -/
def keyCanonical9At (col : KeyColMap) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints ++ keyCanon9ConstraintsAt col }

/-! ### The shape, machine-checked. -/

theorem keyCanonical9At_traceWidth (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).traceWidth = d.traceWidth := rfl

theorem keyCanonical9At_piCount (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).piCount = d.piCount := rfl

theorem keyCanonical9At_tables (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).tables = d.tables := rfl

theorem keyCanonical9At_hashSites (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).hashSites = d.hashSites := rfl

theorem keyCanonical9At_ranges (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).ranges = d.ranges := rfl

theorem keyCanonical9At_constraints (col : KeyColMap) (d : EffectVmDescriptor2) :
    (keyCanonical9At col d).constraints = d.constraints ++ keyCanon9ConstraintsAt col := rfl

/-- Every emitted constraint is a `lookup` — no gate, so no last-row exemption anywhere in this
wrap, and no log moves. -/
theorem keyCanon9_all_lookups (col : KeyColMap) :
    ∀ c ∈ keyCanon9ConstraintsAt col, ∃ l, c = .lookup l := by
  intro c hc
  simp only [keyCanon9ConstraintsAt, List.mem_flatMap] at hc
  obtain ⟨blk, -, hc⟩ := hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h
    exact ⟨_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨_, rfl⟩

/-- All 18 emitted constraints survive a `lookup` filter — the ex-`#guard`'s census, discharged FROM
`keyCanon9_all_lookups` and therefore true at every column map, not just at `188`. -/
theorem keyCanon9ConstraintsAt_lookup_count (col : KeyColMap) :
    ((keyCanon9ConstraintsAt col).filter (fun c => match c with
      | .lookup _ => true | _ => false)).length = 18 := by
  rw [List.filter_eq_self.mpr, keyCanon9ConstraintsAt_length]
  intro c hc
  obtain ⟨l, rfl⟩ := keyCanon9_all_lookups col c hc
  simp

/-- …and NONE survives a `gate` filter, at every column map. This is the fact the last-row argument
rests on (`§3`: a `lookup` has no last-row exemption), so it is worth a term. -/
theorem keyCanon9ConstraintsAt_gate_count (col : KeyColMap) :
    ((keyCanon9ConstraintsAt col).filter (fun c => match c with
      | .base (.gate _) => true | _ => false)).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro c hc hgate
  obtain ⟨l, rfl⟩ := keyCanon9_all_lookups col c hc
  simp at hgate

theorem keyCanon9ConstraintsAt_lookup_count_188 :
    ((keyCanon9ConstraintsAt (deployedKeyCanon9Cols 188)).filter (fun c => match c with
      | .lookup _ => true | _ => false)).length = 18 :=
  keyCanon9ConstraintsAt_lookup_count _

theorem keyCanon9ConstraintsAt_gate_count_188 :
    ((keyCanon9ConstraintsAt (deployedKeyCanon9Cols 188)).filter (fun c => match c with
      | .base (.gate _) => true | _ => false)).length = 0 :=
  keyCanon9ConstraintsAt_gate_count _

#assert_axioms keyCanon9ConstraintsAt_lookup_count
#assert_axioms keyCanon9ConstraintsAt_gate_count
#assert_axioms keyCanon9ConstraintsAt_lookup_count_188
#assert_axioms keyCanon9ConstraintsAt_gate_count_188

private theorem memFilter_nil (l : List VmConstraint2) (hl : ∀ c ∈ l, ∃ x, c = .lookup x) :
    l.filterMap (fun c => match c with | .memOp m => some m | _ => none) = [] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨x, rfl⟩ := hl c (by simp)
    simpa using ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))

private theorem mapFilter_nil (l : List VmConstraint2) (hl : ∀ c ∈ l, ∃ x, c = .lookup x) :
    l.filterMap (fun c => match c with | .mapOp m => some m | _ => none) = [] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨x, rfl⟩ := hl c (by simp)
    simpa using ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem memOpsOf_keyCanonical9At (col : KeyColMap) (d : EffectVmDescriptor2) :
    memOpsOf (keyCanonical9At col d) = memOpsOf d := by
  show (d.constraints ++ keyCanon9ConstraintsAt col).filterMap
      (fun c => match c with | .memOp m => some m | _ => none)
    = d.constraints.filterMap (fun c => match c with | .memOp m => some m | _ => none)
  rw [List.filterMap_append, memFilter_nil _ (keyCanon9_all_lookups col), List.append_nil]

theorem mapOpsOf_keyCanonical9At (col : KeyColMap) (d : EffectVmDescriptor2) :
    mapOpsOf (keyCanonical9At col d) = mapOpsOf d := by
  show (d.constraints ++ keyCanon9ConstraintsAt col).filterMap
      (fun c => match c with | .mapOp m => some m | _ => none)
    = d.constraints.filterMap (fun c => match c with | .mapOp m => some m | _ => none)
  rw [List.filterMap_append, mapFilter_nil _ (keyCanon9_all_lookups col), List.append_nil]

/-- **THE PEEL** — `Satisfied2 (keyCanonical9At col d) ⟹ Satisfied2 d`. The wrap only APPENDS
constraints and leaves every log alone, so every existing per-effect keystone lifts. -/
theorem satisfied2_of_keyCanonical9At (hash : List ℤ → ℤ) (col : KeyColMap)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (keyCanonical9At col d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t := by
  have hmem : memLog (keyCanonical9At col d) t = memLog d t := by
    simp [memLog, memOpsOf_keyCanonical9At]
  have hmap : mapLog (keyCanonical9At col d) t = mapLog d t := by
    simp [mapLog, mapOpsOf_keyCanonical9At]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [keyCanonical9At_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-! ## §3 — THE FORCING: from `Satisfied2` to `CanonicalKey9`. -/

/-- Every emitted lookup of block `blk` is a constraint of the wrapped member. -/
theorem blk_mem (col : KeyColMap) (d : EffectVmDescriptor2) (blk : Fin 2)
    {c : VmConstraint2} (hc : c ∈ keyLookupsAt col blk) :
    c ∈ (keyCanonical9At col d).constraints :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨blk, List.mem_finRange _, hc⟩)

/-- A range lookup of the emit BINDS: its column lies in `[0, 2^bits)` on EVERY row. No non-last-row
side condition — that exemption belongs to gates, and this wrap emits none. -/
theorem lookup_forces {hash : List ℤ → ℤ} {col : KeyColMap} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At col d) minit mfin maddrs t)
    {bits c : Nat} (hrt : t.tf (rangeTidW bits) = rangeRows bits)
    {i : Nat} (hi : i < t.rows.length) {blk : Fin 2}
    (hc : rangeLk bits c ∈ keyLookupsAt col blk) :
    0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < (2 : ℤ) ^ bits := by
  have h := hsat.rowConstraints i hi _ (blk_mem col d blk hc)
  have h' : [(envAt t i).loc c] ∈ t.tf (rangeTidW bits) := by
    simpa [VmConstraint2.holdsAt, Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt, rangeLk,
      EmittedExpr.eval] using h
  rw [hrt] at h'
  exact (range_row_mem_iff _ bits).mp h'

/-- Both bounds on all nine columns of an ARBITRARY column map.

⚑ **THIS SAYS NOTHING ABOUT THE OWNER KEY, AND ITS NAME MUST NOT.** It is the column-agnostic core:
hand it any nine columns and it forces those nine. Everything that names the owner key is the
instance at `deployedKeyCols` below. The `0 ≤` half is not decoration — the `.toNat` in the
`CanonicalKey9` half reads a negative column as `0`, so without it the forcing would be satisfiable
by a column carrying a negative value. -/
theorem lane_bounds_atCols {hash : List ℤ → ℤ} {col : KeyColMap} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At col d) minit mfin maddrs t)
    (h29 : t.tf (rangeTidW KEY_LANE_BITS) = rangeRows KEY_LANE_BITS)
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2) :
    (∀ l : Fin 9, 0 ≤ (envAt t i).loc (col blk l))
      ∧ CanonicalKey9 (fun l => ((envAt t i).loc (col blk l)).toNat) := by
  have hlane : ∀ l : Fin 9, l.1 < 8 →
      0 ≤ (envAt t i).loc (col blk l) ∧ (envAt t i).loc (col blk l) < (2 : ℤ) ^ 29 := by
    intro l hl
    refine lookup_forces hsat h29 hi (blk := blk) ?_
    exact List.mem_append_left _
      (List.mem_map_of_mem (a := (⟨l.1, hl⟩ : Fin 8)) (List.mem_finRange _))
  have htop : 0 ≤ (envAt t i).loc (col blk 8)
      ∧ (envAt t i).loc (col blk 8) < (2 : ℤ) ^ 24 :=
    lookup_forces hsat h24 hi (blk := blk) (List.mem_append_right _ (by simp))
  have hsplit : ∀ l : Fin 9, l.1 < 8 ∨ l = 8 := by
    intro l
    rcases Nat.lt_or_ge l.1 8 with h | h
    · exact Or.inl h
    · exact Or.inr (by apply Fin.ext; have := l.isLt; omega)
  refine ⟨fun l => ?_, ?_, ?_⟩
  · rcases hsplit l with h | h
    · exact (hlane l h).1
    · subst h; exact htop.1
  · intro l hl
    have hj := hlane l hl
    simp only [Dregg2.Circuit.KeyLanes9.K]
    omega
  · simp only [Dregg2.Circuit.KeyLanes9.TopLaneRanged, Dregg2.Circuit.KeyLanes9.KTOP]
    have := htop
    norm_num at this
    omega

/-- **THE FORCING, AT THE DEPLOYED COLUMNS.** On ANY row of a `Satisfied2` witness of the
key-canonicity-welded member, against the two faithful width-tagged range tables, the nonet
committed at `B_PUBKEY_OCTET` of EVERY rotated block satisfies `KeyLanes9.CanonicalKey9` — which
`canonicalKey9_iff_in_image` proves is EXACTLY the nine-lane encoder's image. So the OWNER-KEY
columns are the lanes of SOME 32-byte key.

⚑ Note the two hypotheses that are ABSENT and were present in the fields analogue: no
non-last-row condition (no gate is emitted) and no canonical-column envelope (all nine lanes are
covered by a lookup, so both bounds are constraint-derived). -/
theorem keyCanon9_forces_canonical {hash : List ℤ → ℤ} {w lane8Off : Nat}
    {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At (deployedKeyCols w lane8Off) d) minit mfin maddrs t)
    (h29 : t.tf (rangeTidW KEY_LANE_BITS) = rangeRows KEY_LANE_BITS)
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2) :
    CanonicalKey9 (fun l => ((envAt t i).loc (deployedKeyCols w lane8Off blk l)).toNat) :=
  (lane_bounds_atCols hsat h29 h24 hi blk).2

/-- The capstone's predicate, said the two equivalent ways: as nine ℤ-equalities at the columns the
wrap constrains, and as "the eight absorbed owner-key pre-limbs plus the ninth lane". The proof of
the capstone runs through the first; the STATEMENT is the second, which is the one that mentions
`B_PUBKEY_OCTET` and `preLimbsAt`. -/
private theorem keySpec_iff (w lane8Off : Nat) (a : Assignment) (blk : Fin 2) (c : Bytes32) :
    ((∀ l : Fin 9, l.1 < 8 → ((keyToLanes9 c l : Nat) : ℤ)
        = (preLimbsAt (w + blk.1 * B_SPAN) a).getD (B_PUBKEY_OCTET + l.1) 0)
      ∧ ((keyToLanes9 c 8 : Nat) : ℤ) = a (w + blk.1 * B_SPAN + lane8Off))
    ↔ (∀ l : Fin 9, ((keyToLanes9 c l : Nat) : ℤ) = a (deployedKeyCols w lane8Off blk l)) := by
  constructor
  · rintro ⟨h8, htop⟩ l
    rcases Nat.lt_or_ge l.1 8 with hl | hl
    · rw [h8 l hl, deployedKeyCols_octet_is_absorbed w lane8Off a blk hl]
    · have hl8 : l = 8 := by apply Fin.ext; have := l.isLt; omega
      subst hl8
      rw [htop, deployedKeyCols_lane8_col]
  · intro h
    refine ⟨fun l hl => ?_, ?_⟩
    · rw [h l, deployedKeyCols_octet_is_absorbed w lane8Off a blk hl]
    · rw [h 8, deployedKeyCols_lane8_col]

/-- **THE CAPSTONE.** Under the emitted envelope, the eight ABSORBED owner-key pre-limbs
`B_PUBKEY_OCTET .. +8` of block `blk` — the ones `wireCommitR` folds into `state_commit` — together
with the ninth lane are the nine-lane encoding of EXACTLY ONE 32-byte key. That is the sentence
`keyToLanes9_injective` alone could not reach (it quantifies over VALUES; a prover writes COLUMNS)
and the sentence the deployed eight-lane octet cannot reach at all
(`KeyLanes9.eight_lane_canonicity_is_not_a_repair`).

⚑ Two things this statement does that its predecessor did not. It names the columns instead of
quantifying over them, so it is a claim about the owner key rather than about whatever nine columns
a caller supplies. And it equates ℤ to ℤ rather than through `.toNat`, so a negative committed value
cannot satisfy it by collapsing to `0`. -/
theorem keyCanon9_determines_the_owner_key {hash : List ℤ → ℤ} {w lane8Off : Nat}
    {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At (deployedKeyCols w lane8Off) d) minit mfin maddrs t)
    (h29 : t.tf (rangeTidW KEY_LANE_BITS) = rangeRows KEY_LANE_BITS)
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2) :
    ∃! b : Bytes32,
      (∀ l : Fin 9, l.1 < 8 → ((keyToLanes9 b l : Nat) : ℤ)
          = (preLimbsAt (w + blk.1 * B_SPAN) (envAt t i).loc).getD (B_PUBKEY_OCTET + l.1) 0)
      ∧ ((keyToLanes9 b 8 : Nat) : ℤ) = (envAt t i).loc (w + blk.1 * B_SPAN + lane8Off) := by
  obtain ⟨hnn, hcanon⟩ := lane_bounds_atCols hsat h29 h24 hi blk
  obtain ⟨b, hb⟩ := (canonicalKey9_iff_in_image _).mp hcanon
  have hlane : ∀ l : Fin 9,
      ((keyToLanes9 b l : Nat) : ℤ) = (envAt t i).loc (deployedKeyCols w lane8Off blk l) := by
    intro l
    rw [show keyToLanes9 b l = ((envAt t i).loc (deployedKeyCols w lane8Off blk l)).toNat from
      congrFun hb l]
    exact Int.toNat_of_nonneg (hnn l)
  refine ⟨b, (keySpec_iff w lane8Off _ blk b).mpr hlane, ?_⟩
  intro b' hb'
  apply keyToLanes9_injective
  funext l
  have hz : ((keyToLanes9 b' l : Nat) : ℤ) = ((keyToLanes9 b l : Nat) : ℤ) := by
    rw [(keySpec_iff w lane8Off _ blk b').mp hb' l, hlane l]
  exact_mod_cast hz

/-! ## §4 — ⚑ THE EXHIBIT, UNSAT ON THE EMITTED MEMBER. -/

/-- **THE NAIVE WRAP ACCEPTS IT AND THE DECODE IS A FORGERY.** Three facts about one vector:
(a) every lane is below the LANE width, so nine uniform `< 2^29` lookups — the reading of
"range-check the lanes" that does not do the arithmetic — admit it; (b) it decodes byte-for-byte to
the all-zero key, which is what the honest all-zero nonet decodes to, so it is a genuine
misdecode and not merely an odd vector; (c) the emitted NARROW leg refuses it. Leg 2 is the whole
difference between (a) and (c). -/
theorem the_forged_nonet_passes_the_naive_wrap_and_is_unsat_here :
    (∀ l : Fin 9, forgedKeyNonet l < 2 ^ KEY_LANE_BITS)
    ∧ keyLanes9ToBytes forgedKeyNonet = zeroKey
    ∧ ¬ (forgedKeyNonet 8 < 2 ^ KEY_TOP_BITS)
    ∧ ¬ CanonicalKey9 forgedKeyNonet := by
  refine ⟨?_, Dregg2.Circuit.KeyLanes9.the_forged_nonet_wraps_exactly_once.2.2, ?_, by decide⟩
  · intro l; simp only [KEY_LANE_BITS]; revert l; decide
  · simp only [KEY_TOP_BITS]; decide

/-- **⚑ UNSAT ON THE EMITTED MEMBER.** A witness whose owner-key lane 8 carries `2^24` — the vector
that passes a uniform nine-lane `< 2^29` check and still decodes to a different key's bytes — does
NOT satisfy the key-canonicity-welded member on ANY row. Not "is caught by a later check": the
narrow range table does not contain the row, so no assignment of anything else rescues it.

⚑ Note what this does NOT assume: nothing about lanes 0..7, no producer honesty, no row position.
Lane 8 alone. -/
theorem keyCanon9_rejects_the_forged_nonet {hash : List ℤ → ℤ} {w lane8Off : Nat}
    {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2)
    (hforged : (envAt t i).loc (w + blk.1 * B_SPAN + lane8Off) = 16777216) :
    ¬ Satisfied2 hash (keyCanonical9At (deployedKeyCols w lane8Off) d) minit mfin maddrs t := by
  intro hsat
  have htop : 0 ≤ (envAt t i).loc (deployedKeyCols w lane8Off blk 8)
      ∧ (envAt t i).loc (deployedKeyCols w lane8Off blk 8) < (2 : ℤ) ^ KEY_TOP_BITS :=
    lookup_forces hsat h24 hi (blk := blk) (List.mem_append_right _ (by simp))
  rw [deployedKeyCols_lane8_col, hforged] at htop
  simp only [KEY_TOP_BITS] at htop
  norm_num at htop

/-! ## §5 — ⚑ THE DEPLOYED INSTANCE. Nothing is a parameter here but the face width.

`§3`'s theorems already name `deployedKeyCols`; what was still free was `lane8Off`, because at the
184-limb geometry NO offset was admissible. The 2026-08-01 key-nonet flag day allocated in-block
limb 186, so this section restates the forcing, the capstone and the refusal with EVERY column
fixed — and states them against `preLimbsAt`, i.e. against the list `wireCommitR` folds into
`state_commit`, rather than against bare column indices. -/

/-- The in-block PRE-LIMB offset of nonet lane `l`: the octet window for lanes 0..7, the flag-day
ninth lane for lane 8. Every value is `< rotatedNumPreLimbs`, which is what makes the statements
below statements about the ANCHOR'S DOMAIN. -/
def keyLimbOff (l : Fin 9) : Nat :=
  if l.1 < 8 then B_PUBKEY_OCTET + l.1 else deployedLane8Off

theorem keyLimbOff_lt (l : Fin 9) : keyLimbOff l < rotatedNumPreLimbs := by
  rcases Nat.lt_or_ge l.1 8 with h | h
  · simp only [keyLimbOff, if_pos h, B_PUBKEY_OCTET, rotatedNumPreLimbs]; omega
  · have : l = 8 := by apply Fin.ext; have := l.isLt; omega
    subst this
    decide

/-- The nine in-block pre-limb offsets, as numerals — the ex-`#guard`. `keyLimbOff_lt` above is the
∀ this is an instance of; the numerals are the cross-check against the Rust twins. -/
theorem keyLimbOff_values :
    (List.finRange 9).map keyLimbOff = [105, 106, 107, 108, 109, 110, 111, 112, 186] := by decide

#assert_axioms keyLimbOff_values

/-- **EVERY LANE READS AN ABSORBED LIMB.** Column `deployedKeyCanon9Cols w blk l` IS entry
`keyLimbOff l` of `preLimbsAt` — the tie `§1.1` proved for lanes 0..7, now closed for all nine. -/
theorem deployedKeyCanon9Cols_is_absorbed_limb (w : Nat) (a : Assignment) (blk : Fin 2)
    (l : Fin 9) :
    a (deployedKeyCanon9Cols w blk l)
      = (preLimbsAt (w + blk.1 * B_SPAN) a).getD (keyLimbOff l) 0 := by
  rcases Nat.lt_or_ge l.1 8 with h | h
  · simp only [keyLimbOff, if_pos h, deployedKeyCanon9Cols]
    exact deployedKeyCols_octet_is_absorbed w deployedLane8Off a blk h
  · have hl : l = 8 := by apply Fin.ext; have := l.isLt; omega
    subst hl
    simp only [keyLimbOff, deployedKeyCanon9Cols]
    rw [deployedKeyCols_lane8_col, preLimbsAt_getD _ _ _ (by decide)]
    norm_num

/-- **THE FORCING, FULLY DEPLOYED.** No column is a parameter. -/
theorem keyCanon9_forces_canonical_deployed {hash : List ℤ → ℤ} {w : Nat}
    {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At (deployedKeyCanon9Cols w) d) minit mfin maddrs t)
    (h29 : t.tf (rangeTidW KEY_LANE_BITS) = rangeRows KEY_LANE_BITS)
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2) :
    CanonicalKey9 (fun l => ((envAt t i).loc (deployedKeyCanon9Cols w blk l)).toNat) :=
  (lane_bounds_atCols hsat h29 h24 hi blk).2

/-- **⚑ THE DEPLOYED CAPSTONE.** Under the emitted envelope, the NINE absorbed pre-limbs the owner
key rides — the octet `B_PUBKEY_OCTET .. +7` and the flag-day ninth lane, all of them entries of the
list `wireCommitR` folds into `state_commit` — are the nine-lane encoding of EXACTLY ONE 32-byte
key. Compared with `keyCanon9_determines_the_owner_key` this fixes the last free column AND states
lane 8 as a member of `preLimbsAt` rather than as a bare column, so the sentence is about what the
consensus anchor binds and not about where this file chose to look. -/
theorem keyCanon9_determines_the_owner_key_deployed {hash : List ℤ → ℤ} {w : Nat}
    {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9At (deployedKeyCanon9Cols w) d) minit mfin maddrs t)
    (h29 : t.tf (rangeTidW KEY_LANE_BITS) = rangeRows KEY_LANE_BITS)
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2) :
    ∃! b : Bytes32, ∀ l : Fin 9,
      ((keyToLanes9 b l : Nat) : ℤ)
        = (preLimbsAt (w + blk.1 * B_SPAN) (envAt t i).loc).getD (keyLimbOff l) 0 := by
  obtain ⟨hnn, hcanon⟩ := lane_bounds_atCols hsat h29 h24 hi blk
  obtain ⟨b, hb⟩ := (canonicalKey9_iff_in_image _).mp hcanon
  have hlane : ∀ l : Fin 9,
      ((keyToLanes9 b l : Nat) : ℤ) = (envAt t i).loc (deployedKeyCanon9Cols w blk l) := by
    intro l
    rw [show keyToLanes9 b l = ((envAt t i).loc (deployedKeyCanon9Cols w blk l)).toNat from
      congrFun hb l]
    exact Int.toNat_of_nonneg (hnn l)
  refine ⟨b, fun l => ?_, ?_⟩
  · rw [hlane l]
    exact deployedKeyCanon9Cols_is_absorbed_limb w (envAt t i).loc blk l
  · intro b' hb'
    apply keyToLanes9_injective
    funext l
    have hz : ((keyToLanes9 b' l : Nat) : ℤ) = ((keyToLanes9 b l : Nat) : ℤ) := by
      rw [hb' l, hlane l]
      exact (deployedKeyCanon9Cols_is_absorbed_limb w (envAt t i).loc blk l).symm
    exact_mod_cast hz

/-- **⚑ THE EXHIBIT, AT THE DEPLOYED COLUMNS AND AGAINST THE ABSORBED LIMB.** A witness whose owner
key's NINTH ABSORBED PRE-LIMB carries `2^24` — the vector that passes a uniform nine-lane `< 2^29`
check and still decodes to the all-zero key — does not satisfy the welded member on any row. The
hypothesis is stated as an entry of `preLimbsAt`, so it is a hypothesis about the datum
`state_commit` folds. -/
theorem keyCanon9_rejects_the_forged_nonet_deployed {hash : List ℤ → ℤ} {w : Nat}
    {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2)
    (hforged : (preLimbsAt (w + blk.1 * B_SPAN) (envAt t i).loc).getD deployedLane8Off 0
      = 16777216) :
    ¬ Satisfied2 hash (keyCanonical9At (deployedKeyCanon9Cols w) d) minit mfin maddrs t := by
  refine keyCanon9_rejects_the_forged_nonet (w := w) (lane8Off := deployedLane8Off) h24 hi blk ?_
  rw [← hforged, preLimbsAt_getD _ _ _ (by decide)]

#assert_axioms keyLimbOff_lt
#assert_axioms deployedKeyCanon9Cols_is_absorbed_limb
#assert_axioms keyCanon9_forces_canonical_deployed
#assert_axioms keyCanon9_determines_the_owner_key_deployed
#assert_axioms keyCanon9_rejects_the_forged_nonet_deployed

/-! ## §6 — ⚑ THE WIRE WRAP. The face the emit drivers apply, and the reason this file stopped
being decoration.

Everything above was true on 2026-08-01 and reached NOTHING: `keyCanonical9At` was applied by no
emitter, so not one committed descriptor carried a single range lookup on an owner-key lane, and
`state_commit` bound a nonet that no constraint required to be in the encoder's image. Measured
over the two committed registries at that HEAD: 10560 lookups on the 28-bit fields table, 960 on
the 24-bit table, and **zero on the 29-bit table** — the key nonet's lane width, which nothing had
ever emitted.

`keyCanonical9Wire` is the transform `EmitRotationV3.lean` (and the two wide registry probes) now
apply to EVERY rotated member, exactly as they already apply `ownerFreezeWire` and
`fieldsCanonical9Wire`. `faceWidthOfName` is shared from `FieldsCanonicity9Emit` — the Lean twin of
`trace_rotated::avail_pad_for_descriptor_name` — rather than re-spelled here, so the hardened
`…-v1-avail` members get their shifted base from the same single source `OwnerFreezeWire` reads.

**The wrap is geometry-invariant** (`traceWidth`, `piCount`, `tables`, `hashSites`, `ranges`, and
the member's NAME all `rfl`-unchanged): the nine columns are already allocated pre-limbs, and both
range widths ride width-tagged custom table ids the deployed IR-2 interpreter already realizes
(`descriptor_ir2::CUSTOM_RANGE_WIDTHS` carries 24 and 29). What DOES move is the main instance's
aux region — the interpreter appends `decomp_cols(29) = 9` limb columns per lane lookup and
`decomp_cols(24) = 6` for the narrow one, so `16·9 + 2·6 = 156` aux columns per member. That is a
descriptor re-emit and a VK rotation, not a schema move. -/

/-- **THE WIRE WRAP** — `CanonicalKey9` over the deployed owner-key nonet, at the v1-face width the
member's own NAME declares. This is the object the emit drivers print. -/
def keyCanonical9Wire (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  keyCanonical9At (deployedKeyCanon9Cols (faceWidthOfName d.name)) d

theorem keyCanonical9Wire_eq (d : EffectVmDescriptor2) :
    keyCanonical9Wire d
      = keyCanonical9At (deployedKeyCanon9Cols (faceWidthOfName d.name)) d := rfl

/-! ### Geometry does not move. -/

theorem keyCanonical9Wire_name (d : EffectVmDescriptor2) :
    (keyCanonical9Wire d).name = d.name := rfl
theorem keyCanonical9Wire_traceWidth (d : EffectVmDescriptor2) :
    (keyCanonical9Wire d).traceWidth = d.traceWidth := rfl
theorem keyCanonical9Wire_piCount (d : EffectVmDescriptor2) :
    (keyCanonical9Wire d).piCount = d.piCount := rfl
theorem keyCanonical9Wire_tables (d : EffectVmDescriptor2) :
    (keyCanonical9Wire d).tables = d.tables := rfl
theorem keyCanonical9Wire_hashSites (d : EffectVmDescriptor2) :
    (keyCanonical9Wire d).hashSites = d.hashSites := rfl
theorem keyCanonical9Wire_ranges (d : EffectVmDescriptor2) :
    (keyCanonical9Wire d).ranges = d.ranges := rfl
theorem keyCanonical9Wire_constraints (d : EffectVmDescriptor2) :
    (keyCanonical9Wire d).constraints
      = d.constraints ++ keyCanon9ConstraintsAt (deployedKeyCanon9Cols (faceWidthOfName d.name)) :=
  rfl

/-- **THE PEEL, AT THE WIRE.** Every per-effect keystone proved about the unwrapped member lifts
through the wire wrap unchanged: it only APPENDS lookups and moves no log. -/
theorem satisfied2_of_keyCanonical9Wire (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (keyCanonical9Wire d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t :=
  satisfied2_of_keyCanonical9At hash _ d h

/-- **⚑ THE CAPSTONE, ON THE EMITTED OBJECT.** For a member the drivers actually print: under the
wire wrap, the NINE absorbed pre-limbs the owner key rides — the octet `B_PUBKEY_OCTET .. +7` and
the flag-day ninth lane, every one an entry of the list `wireCommitR` folds into `state_commit` —
are the nine-lane encoding of EXACTLY ONE 32-byte key.

This is `keyCanon9_determines_the_owner_key_deployed` at `w := faceWidthOfName d.name`, which is
the whole content of the wiring: the same sentence, now about an object with a committed VK. -/
theorem keyCanon9Wire_determines_the_owner_key {hash : List ℤ → ℤ} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (keyCanonical9Wire d) minit mfin maddrs t)
    (h29 : t.tf (rangeTidW KEY_LANE_BITS) = rangeRows KEY_LANE_BITS)
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2) :
    ∃! b : Bytes32, ∀ l : Fin 9,
      ((keyToLanes9 b l : Nat) : ℤ)
        = (preLimbsAt (faceWidthOfName d.name + blk.1 * B_SPAN) (envAt t i).loc).getD
            (keyLimbOff l) 0 :=
  keyCanon9_determines_the_owner_key_deployed hsat h29 h24 hi blk

/-- **⚑ THE REFUSAL, ON THE EMITTED OBJECT.** A witness whose owner key's ninth absorbed pre-limb
carries `2^24` — the vector a uniform nine-lane `< 2^29` check admits, whose decode is byte-for-byte
another key's — does not satisfy the printed member on any row. -/
theorem keyCanon9Wire_rejects_the_forged_nonet {hash : List ℤ → ℤ} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h24 : t.tf (rangeTidW KEY_TOP_BITS) = rangeRows KEY_TOP_BITS)
    {i : Nat} (hi : i < t.rows.length) (blk : Fin 2)
    (hforged : (preLimbsAt (faceWidthOfName d.name + blk.1 * B_SPAN) (envAt t i).loc).getD
      deployedLane8Off 0 = 16777216) :
    ¬ Satisfied2 hash (keyCanonical9Wire d) minit mfin maddrs t :=
  keyCanon9_rejects_the_forged_nonet_deployed h24 hi blk hforged

/-! ### The four deployed faces, and the columns each lands the nonet on.

Re-typed against the wire names the registry TSV actually carries: bare members ride the 188-wide v1
face, the three hardened availability members ride their shifted bases, and the ninth lane travels
with them.

⚑ Eleven `#guard`s until 2026-08-03. Four gained only a name (the face-width pins are genuinely
about four specific strings). The other seven gained a `∀`: the census of the emitted constraint
list — 18 lookups, 16 on the lane table, 2 on the narrow one, 0 gates, landing exactly on the nine
columns of each block — holds for EVERY column map and therefore at every face, which is what the
four-face `.all` pin was reaching for one element at a time. -/

theorem faceWidth_cellseal :
    faceWidthOfName "dregg-effectvm-cellseal-v2-rot24-v3-staged" = 188 := by
  simp [faceWidthOfName, EFFECT_VM_WIDTH]

theorem faceWidth_transfer_avail :
    faceWidthOfName "dregg-effectvm-transfer-v1-avail-rot24-v3-staged" = 198 := by
  simp [faceWidthOfName, Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_WIDTH,
    Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_BASE, EFFECT_VM_WIDTH]

theorem faceWidth_burn_avail :
    faceWidthOfName "dregg-effectvm-burn-v1-avail-rot24-v3-staged" = 196 := by
  simp [faceWidthOfName, Dregg2.Circuit.Emit.EffectVmEmitBurn.AVAIL_WIDTH,
    Dregg2.Circuit.Emit.EffectVmEmitBurn.AVAIL_BASE, EFFECT_VM_WIDTH]

theorem faceWidth_transfer_fee_avail :
    faceWidthOfName "dregg-effectvm-transfer-v1-fee-avail-rot24-v3-staged" = 204 := by
  simp [faceWidthOfName, Dregg2.Circuit.Emit.EffectVmEmitTransfer.FEE_AVAIL_WIDTH,
    Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_BASE, EFFECT_VM_WIDTH]

/-- 18 lookups per member at EVERY face, and not one gate: the wrap cannot acquire a last-row
exemption no matter which member it rides. The four deployed faces, as the `#guard` listed them —
each an instance of `keyCanon9ConstraintsAt_length`, which needs no face at all. -/
theorem deployed_faces_carry_18_lookups :
    [188, 196, 198, 204].all (fun w =>
      (keyCanon9ConstraintsAt (deployedKeyCanon9Cols w)).length == 18) = true := by
  simp [keyCanon9ConstraintsAt_length]

theorem deployed_faces_carry_no_gate :
    [188, 196, 198, 204].all (fun w =>
      ((keyCanon9ConstraintsAt (deployedKeyCanon9Cols w)).filter (fun c => match c with
        | .base (.gate _) => true | _ => false)).length == 0) = true := by
  simp [keyCanon9ConstraintsAt_gate_count]

/-- ⚑ **THE TWO WIDTHS ARE NOT THE SAME TABLE**, and this is what keeps a later "uniformity" edit
from re-opening the encoding: eight lookups ride `rangeTidW 29`, exactly ONE rides `rangeTidW 24`,
per block. ⚑ Stated at an ARBITRARY column map — the split is a property of the emit, not of the
`188` face the `#guard` happened to evaluate. -/
theorem keyCanon9_lane_table_count (col : KeyColMap) :
    ((keyCanon9ConstraintsAt col).filter (fun c => match c with
      | .lookup l => l.table == rangeTidW KEY_LANE_BITS | _ => false)).length = 16 := rfl

theorem keyCanon9_top_table_count (col : KeyColMap) :
    ((keyCanon9ConstraintsAt col).filter (fun c => match c with
      | .lookup l => l.table == rangeTidW KEY_TOP_BITS | _ => false)).length = 2 := rfl

theorem keyCanon9_lane_table_count_188 :
    ((keyCanon9ConstraintsAt (deployedKeyCanon9Cols 188)).filter (fun c => match c with
      | .lookup l => l.table == rangeTidW KEY_LANE_BITS | _ => false)).length = 16 :=
  keyCanon9_lane_table_count _

theorem keyCanon9_top_table_count_188 :
    ((keyCanon9ConstraintsAt (deployedKeyCanon9Cols 188)).filter (fun c => match c with
      | .lookup l => l.table == rangeTidW KEY_TOP_BITS | _ => false)).length = 2 :=
  keyCanon9_top_table_count _

/-- The two widths really are two tables. Without this the counts above would be a partition of the
same table and the narrow leg would be decoration. -/
theorem lane_and_top_tables_differ : rangeTidW KEY_LANE_BITS ≠ rangeTidW KEY_TOP_BITS := by decide

/-- ⚑ **THE WRAP LANDS ON THE NONET AND NOTHING ELSE — at every column map.** The looked-up columns,
read back out of the EMITTED constraint list, are exactly the nine columns of block 0 followed by
the nine of block 1. The `#guard` checked the numerals at one face; this says the emit cannot look
anywhere but where `col` points, and the numerals are then the instance below. -/
theorem keyCanon9_lookup_cols (col : KeyColMap) :
    ((keyCanon9ConstraintsAt col).filterMap (fun c => match c with
      | .lookup ⟨_, [.var c']⟩ => some c' | _ => none))
      = (List.finRange 9).map (col 0) ++ (List.finRange 9).map (col 1) := rfl

/-- …and at the deployed face they are the absorbed owner-key pre-limbs of both blocks. -/
theorem keyCanon9_lookup_cols_188 :
    ((keyCanon9ConstraintsAt (deployedKeyCanon9Cols 188)).filterMap (fun c => match c with
      | .lookup ⟨_, [.var c']⟩ => some c' | _ => none))
      = [293, 294, 295, 296, 297, 298, 299, 300, 374,
         556, 557, 558, 559, 560, 561, 562, 563, 637] := by decide

#assert_axioms faceWidth_cellseal
#assert_axioms faceWidth_transfer_avail
#assert_axioms faceWidth_burn_avail
#assert_axioms faceWidth_transfer_fee_avail
#assert_axioms deployed_faces_carry_18_lookups
#assert_axioms deployed_faces_carry_no_gate
#assert_axioms keyCanon9_lane_table_count
#assert_axioms keyCanon9_top_table_count
#assert_axioms keyCanon9_lane_table_count_188
#assert_axioms keyCanon9_top_table_count_188
#assert_axioms lane_and_top_tables_differ
#assert_axioms keyCanon9_lookup_cols
#assert_axioms keyCanon9_lookup_cols_188

#assert_axioms satisfied2_of_keyCanonical9Wire
#assert_axioms keyCanon9Wire_determines_the_owner_key
#assert_axioms keyCanon9Wire_rejects_the_forged_nonet

/-- The exhibit's lane 8 really is the top-lane ceiling, one above the largest admissible value. -/
theorem forged_lane8_is_the_ceiling :
    forgedKeyNonet 8 = 16777216 ∧ (16777216 : Nat) = 2 ^ KEY_TOP_BITS := by
  refine ⟨rfl, by norm_num [KEY_TOP_BITS]⟩

#assert_axioms keyCanon9_all_lookups
#assert_axioms satisfied2_of_keyCanonical9At
#assert_axioms blk_mem
#assert_axioms lookup_forces
#assert_axioms lane_bounds_atCols
#assert_axioms keyCanon9_forces_canonical
#assert_axioms keyCanon9_determines_the_owner_key
#assert_axioms the_forged_nonet_passes_the_naive_wrap_and_is_unsat_here
#assert_axioms keyCanon9_rejects_the_forged_nonet
#assert_axioms forged_lane8_is_the_ceiling

end Dregg2.Circuit.Emit.KeyCanonicity9Emit
