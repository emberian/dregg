/-
# Dregg2.Circuit.Emit.FieldsCanonicity9Emit — `Canonical9`, EMITTED.

## The gap this closes, stated exactly

`Dregg2.Circuit.FieldLanes9.fieldToLanes9_injective` proves the nine-lane fields encoder is an
INJECTION — a total decoder plus a machine-checked left inverse, not a hash bound. It quantifies
over 32-byte **VALUES**.

**An adversarial prover never applies the encoder.** It writes nine committed columns directly, and
until this file NOTHING in the deployed AIR forced those columns into the encoder's image: audited
2026-07-31 across all 186 emitted members, every `"ranges"` was `[]` and not one `range`-semantics
lookup landed on a rotated block column. `< 2^28` on a free lane was a PRODUCER invariant, which
establishes nothing for the party relying on the proof. Witness versus constraint.

`FieldLanes9.canonical9_iff_in_image` says what an AIR must force instead, and proves the three legs
are EXACTLY the image (not a superset that merely contains it):

1. `FreeLanesRanged` — lanes 2..8 below `2^28`. **Seven range lookups per (block, slot).**
2. `PinnedLanesField` — lanes 0/1 are BabyBear elements. Free in-AIR; a committed column IS one. It
   arrives here as the deployed canonical-element hypothesis (`0 ≤ col < p`), the same envelope
   every mod-p forcing theorem in this tree carries — named, not laundered.
3. `NoWrap` — `decLo`/`decHi` (the pinned lanes with the carry digit's discarded `mod p` quotient
   restored) below `2^32`. ⚑ **NOT a range check on any lane** — a JOINT condition on lane 0, lane 1
   and lane 8's top nibble.

Leg 3 is why "7 × `< 2^28` lookups per field" is necessary and **NOT sufficient**, and the
counterexample is one lane wide (`FieldLanes9.free_lane_ranges_alone_do_not_force_the_image`):
`forgedLanes = [0,…,0, 3·2^24]` passes all seven, and its carry digit `3` makes the decoder restore
`decLo = 3p = 6039797763 ≥ 2^32`, which wraps to the honest `v = 1744830467`. The welded v1 face
column then reads **0** while the committed nonet decodes to **1744830467** — one accepted proof,
two answers to "what is `fields[slot]`".

## The gadget

Per `(block, slot)`, seven aux columns in the fields-canonicity region (`CANON9_REGION_OFF`, past
both rotated blocks and the caveat region) and seven gates:

```text
  r q0 q1 v0 v0b v1 v1b                       -- the seven aux columns
  L8  = (q0 + 4·q1)·2^24 + r                  -- the carry digit split off lane 8's top nibble
  q·(q−1)·(q−2) = 0                     × 2   -- q0, q1 ∈ {0,1,2}: the ONLY honest quotients
  2·v = q·(q−1)·L                       × 2   -- v = L when q = 2, else 0  (2 is a unit mod p)
  vb  = v + q·(q−1)                     × 2   -- vb = L + 2 when q = 2, else 0
```

with twelve lookups: `L2 .. L8 < 2^28` (leg 1, the seven), `r < 2^24`, and `v0, v0b, v1, v1b < 2^28`.

**Why that reads `NoWrap` exactly.** Under leg 1 the decoder's carry digit is `decCarry = L8 / 2^24`
— the free lanes below lane 8 contribute under `2^168`, so base-256 digit 24 of `decWord` IS lane
8's top nibble — and `NoWrap` is `L0 + (c % 4)·p < 2^32 ∧ L1 + (c / 4)·p < 2^32`. With `q ∈ {0,1,2}`:

  * `q ≤ 1` — `L + q·p ≤ (p−1) + p < 2^32` for free; and `q(q−1) = 0` forces `v = vb = 0`, so the
    gadget imposes nothing further. Exactly right: there is nothing to impose.
  * `q = 2`  — `q(q−1) = 2`, so `v ≡ L` and `vb ≡ L + 2`. `v < 2^28` pins `L = v` on the nose (both
    canonical), and `vb < 2^28` then pins `L + 2 < 2^28`, i.e. `L < 2^28 − 2 = 2^32 − 2p`. That is
    `L + 2p < 2^32` — `NoWrap`, with no slack in either direction.

Both lookups are load-bearing. `vb` alone would let `L ∈ {p−2, p−1}` wrap to `{0,1}` and pass; `v`
alone stops at `L < 2^28`, two short of the bound.

⚑ **`q = 3` IS THE EXHIBIT, AND IT IS UNSAT.** `forgedLanes`'s lane 8 is `3·2^24`, so `r = 0` and
`q0 + 4·q1 = 3` with `q0, q1 ∈ {0,1,2}` — impossible (`q1 = 0 ⟹ q0 = 3`). No aux fill exists.
`forged_nonet_admits_no_witness` is that, and `canon9_rejects_the_forged_nonet` lifts it to
`¬ Satisfied2` over the emitted constraints.

## Geometry

The aux region rides PAST both blocks and the caveat region (`CANON9_REGION_OFF = 2·B_SPAN +
C_SPAN`), so **the pre-limb geometry and the absorption chain are untouched**: 184 pre-iroot limbs,
`B_SPAN = 247`, every `rotV3SitesAt` / `caveatV3SitesAt` site at its old in-block offset, no
committed limb moved, no new hash site, no new PI. What moves is `APPENDIX_SPAN` (539 → 651) and,
downstream of it, each member's `traceWidth` and every wrapper anchored at it. **A descriptor
re-emit and a VK rotation, NOT a re-genesis** — `CANONICAL_STATE_SCHEMA_EPOCH` stays 14.

The wrap itself is `traceWidth`- and `piCount`-INVARIANT (the columns are already allocated by
`rotateV3`'s widened appendix), so it composes with every other wrapper in any order.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. `Nat.Prime 2013265921` is DISCHARGED by
`norm_num`, not assumed.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.FieldLanes9

namespace Dregg2.Circuit.Emit.FieldsCanonicity9Emit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (rangeTidW)
open Dregg2.Circuit.Emit (fieldLaneCol)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (B_SPAN CANON9_REGION_OFF CANON9_SPAN)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8000

/-! ## §0 — the two range widths this emit introduces. -/

/-- The free lanes' radix width — leg 1's lookup, and the width `v`/`vb` ride. -/
def LANE_BITS : Nat := 28

/-- The carry-digit remainder's width: `L8 = c·2^24 + r`, so `r < 2^24`. -/
def R_BITS : Nat := 24

/-- BabyBear's modulus is prime. Discharged, not assumed — the cube gate's trichotomy is a
statement about a FIELD and would be false in a ring with zero divisors. -/
theorem P_prime : Nat.Prime 2013265921 := by norm_num

/-! ## §1 — the emitted columns. -/

/-- Lane `lane` of `fields[slot]` in rotated block `blk` of a member whose v1 face is `w` wide.
Reads `Emit.fieldLaneCol`, the verified layout's SINGLE SOURCE — never `113 + 8·slot`; the nonet is
deliberately non-contiguous and a stride would silently address the next slot's window. -/
def laneColAt (w : Nat) (blk : Fin 2) (slot : Fin 8) (lane : Fin 9) : Nat :=
  w + blk.1 * B_SPAN + fieldLaneCol slot lane

/-- Aux column `k` of `(blk, slot)`: `0 = r, 1 = q0, 2 = q1, 3 = v0, 4 = v0b, 5 = v1, 6 = v1b`. -/
def auxColAt (w : Nat) (blk : Fin 2) (slot : Fin 8) (k : Fin 7) : Nat :=
  w + CANON9_REGION_OFF + blk.1 * 56 + slot.1 * 7 + k.1

/-- Every aux column the region carries, in emission order. -/
def auxColsAt (w : Nat) : List Nat :=
  (List.finRange 2).flatMap fun blk =>
    (List.finRange 8).flatMap fun slot => (List.finRange 7).map (auxColAt w blk slot)

-- The region is a complete, gap-free, duplicate-free tiling of the 112 columns
-- `[w + CANON9_REGION_OFF, w + CANON9_REGION_OFF + CANON9_SPAN)` — no aux column lands on a
-- committed limb, a caveat felt, or another slot's aux.
#guard (auxColsAt 188).length == CANON9_SPAN
#guard (auxColsAt 188).Nodup
#guard auxColsAt 188 == (List.range CANON9_SPAN).map (· + (188 + CANON9_REGION_OFF))
-- …and no aux column collides with any fields-lane column of either block.
#guard ((List.finRange 2).flatMap fun blk => (List.finRange 8).flatMap fun slot =>
    (List.finRange 9).map (laneColAt 188 blk slot)).all
  (fun c => !(auxColsAt 188).contains c)

/-! ## §2 — the emitted constraints. -/

private def eSub (a b : EmittedExpr) : EmittedExpr := .add a (.mul (.const (-1)) b)
private def eK (k : ℤ) : EmittedExpr := .const k
private def eV (c : Nat) : EmittedExpr := .var c

/-- `q·(q−1)` — the DOUBLED selector `2·t`, where `t = q(q−1)/2` is `1` at `q = 2` and `0` at
`q ∈ {0,1}`. Kept doubled throughout so the emit never needs the field inverse of 2. -/
private def twoSel (q : Nat) : EmittedExpr := .mul (eV q) (eSub (eV q) (eK 1))

/-- The seven gate bodies of one `(block, slot)`, over abstract columns. -/
def gadgetBodies (l0 l1 l8 r q0 q1 v0 v0b v1 v1b : Nat) : List EmittedExpr :=
  [ -- the carry-digit split: lane 8 = (q0 + 4·q1)·2^24 + r
    eSub (eV l8) (.add (.mul (.add (eV q0) (.mul (eK 4) (eV q1))) (eK 16777216)) (eV r))
    -- q0, q1 ∈ {0,1,2}
  , .mul (eV q0) (.mul (eSub (eV q0) (eK 1)) (eSub (eV q0) (eK 2)))
  , .mul (eV q1) (.mul (eSub (eV q1) (eK 1)) (eSub (eV q1) (eK 2)))
    -- 2·v = q(q−1)·L
  , eSub (.mul (eK 2) (eV v0)) (.mul (twoSel q0) (eV l0))
  , eSub (.mul (eK 2) (eV v1)) (.mul (twoSel q1) (eV l1))
    -- vb = v + q(q−1)
  , eSub (eV v0b) (.add (eV v0) (twoSel q0))
  , eSub (eV v1b) (.add (eV v1) (twoSel q1)) ]

/-- A width-tagged range lookup (`EffectVmEmitV2.rangeLookupW`'s shape, at an explicit column). -/
def rangeLk (bits col : Nat) : VmConstraint2 := .lookup ⟨rangeTidW bits, [.var col]⟩

/-- The twelve lookups of one `(block, slot)`: leg 1's seven free lanes, then the gadget's five. -/
def gadgetLookups (lanes : List Nat) (r v0 v0b v1 v1b : Nat) : List VmConstraint2 :=
  lanes.map (rangeLk LANE_BITS)
    ++ [ rangeLk R_BITS r
       , rangeLk LANE_BITS v0, rangeLk LANE_BITS v0b
       , rangeLk LANE_BITS v1, rangeLk LANE_BITS v1b ]

/-- The seven free lanes (2..8) of `fields[slot]` in block `blk`. -/
def freeLaneColsAt (w : Nat) (blk : Fin 2) (slot : Fin 8) : List Nat :=
  (List.finRange 7).map (fun i => laneColAt w blk slot ⟨i.1 + 2, by omega⟩)

/-- One `(block, slot)`'s constraints: seven gates then twelve lookups. -/
def slotConstraintsAt (w : Nat) (blk : Fin 2) (slot : Fin 8) : List VmConstraint2 :=
  (gadgetBodies (laneColAt w blk slot 0) (laneColAt w blk slot 1) (laneColAt w blk slot 8)
      (auxColAt w blk slot 0) (auxColAt w blk slot 1) (auxColAt w blk slot 2)
      (auxColAt w blk slot 3) (auxColAt w blk slot 4)
      (auxColAt w blk slot 5) (auxColAt w blk slot 6)).map (fun b => .base (.gate b))
    ++ gadgetLookups (freeLaneColsAt w blk slot)
        (auxColAt w blk slot 0) (auxColAt w blk slot 3) (auxColAt w blk slot 4)
        (auxColAt w blk slot 5) (auxColAt w blk slot 6)

/-- **THE EMIT** — `Canonical9` over both rotated blocks' eight fields slots. -/
def canon9ConstraintsAt (w : Nat) : List VmConstraint2 :=
  (List.finRange 2).flatMap fun blk =>
    (List.finRange 8).flatMap fun slot => slotConstraintsAt w blk slot

-- 16 × (7 gates + 12 lookups) = 112 gates + 192 lookups.
#guard (canon9ConstraintsAt 188).length == 16 * 19
#guard ((canon9ConstraintsAt 188).filter (fun c => match c with
  | .base (.gate _) => true | _ => false)).length == 112
#guard ((canon9ConstraintsAt 188).filter (fun c => match c with
  | .lookup _ => true | _ => false)).length == 192

/-- **THE WRAP.** `traceWidth`-, `piCount`-, table-, site- and range-INVARIANT: the columns are
already allocated by `rotateV3`'s widened appendix, and the two range widths ride the width-tagged
custom ids (`rangeTidW 24` / `rangeTidW 28`), realized by the deployed nibble-decomposition path
exactly as the availability weld's 15-bit teeth already are. -/
def fieldsCanonical9At (w : Nat) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints ++ canon9ConstraintsAt w }

/-- **The v1-face width a member's rotated appendix rides at, read off its WIRE NAME.** The exact
Lean twin of `trace_rotated::avail_pad_for_descriptor_name`: the hardened availability members carry
a wider v1 face (their borrow-weld witness columns sit at `[EFFECT_VM_WIDTH, AVAIL_WIDTH)`), so
`rotateV3` appended their whole appendix — and therefore the canonicity region — at that shifted
base. Every rotation / refuse / rc / cap-open wrapper only APPENDS name suffixes, so the mark
survives to the registry TSV name. Derived from the name, never a literal beside it.

⚠ ORDER MATTERS ONLY IN APPEARANCE: `"…-transfer-v1-fee-avail"` does not start with
`"…-transfer-v1-avail"` (the `f` breaks the prefix), so the two arms are disjoint — the Rust twin
has the same apparent hazard and the same non-hazard. -/
def faceWidthOfName (n : String) : Nat :=
  if n.startsWith "dregg-effectvm-transfer-v1-avail" then
    Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_WIDTH
  else if n.startsWith "dregg-effectvm-transfer-v1-fee-avail" then
    Dregg2.Circuit.Emit.EffectVmEmitTransfer.FEE_AVAIL_WIDTH
  else if n.startsWith "dregg-effectvm-burn-v1-avail" then
    Dregg2.Circuit.Emit.EffectVmEmitBurn.AVAIL_WIDTH
  else EFFECT_VM_WIDTH

-- The four faces, pinned against the Rust twin's pads (0 / 10 / 16 / 8 past the 188-wide v1 face).
#guard faceWidthOfName "dregg-effectvm-transfer-v1-rot24-v3-staged" == 188
#guard faceWidthOfName "dregg-effectvm-transfer-v1-avail-rot24-v3-staged" == 198
#guard faceWidthOfName "dregg-effectvm-transfer-v1-fee-avail-rot24-v3-staged" == 204
#guard faceWidthOfName "dregg-effectvm-burn-v1-avail-rot24-v3-staged" == 196

/-- **THE WIRE WRAP.** `fieldsCanonical9At` at the face width the member's own name declares — the
one transform the emit driver applies to EVERY rotated member, bare or hardened. -/
def fieldsCanonical9Wire (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  fieldsCanonical9At (faceWidthOfName d.name) d

/-- The deployed instance: a bare cohort member's v1 face is `EFFECT_VM_WIDTH` wide. A hardened
`…-v1-avail` member's face is `AVAIL_WIDTH`, and takes `fieldsCanonical9At` at THAT width — the same
shift `AvailWireMembers.withDfaRcPinsAt` / `cavBaseOf` already carry. -/
def fieldsCanonical9 : EffectVmDescriptor2 → EffectVmDescriptor2 :=
  fieldsCanonical9At EFFECT_VM_WIDTH

/-! ### The shape, machine-checked. -/

theorem fieldsCanonical9At_traceWidth (w : Nat) (d : EffectVmDescriptor2) :
    (fieldsCanonical9At w d).traceWidth = d.traceWidth := rfl

theorem fieldsCanonical9At_piCount (w : Nat) (d : EffectVmDescriptor2) :
    (fieldsCanonical9At w d).piCount = d.piCount := rfl

theorem fieldsCanonical9At_tables (w : Nat) (d : EffectVmDescriptor2) :
    (fieldsCanonical9At w d).tables = d.tables := rfl

theorem fieldsCanonical9At_hashSites (w : Nat) (d : EffectVmDescriptor2) :
    (fieldsCanonical9At w d).hashSites = d.hashSites := rfl

theorem fieldsCanonical9At_ranges (w : Nat) (d : EffectVmDescriptor2) :
    (fieldsCanonical9At w d).ranges = d.ranges := rfl

theorem fieldsCanonical9At_constraints (w : Nat) (d : EffectVmDescriptor2) :
    (fieldsCanonical9At w d).constraints = d.constraints ++ canon9ConstraintsAt w := rfl

/-- Every emitted constraint is a row-local `gate` or a `lookup` — nothing else, so no log moves. -/
theorem canon9_gate_or_lookup (w : Nat) :
    ∀ c ∈ canon9ConstraintsAt w, (∃ b, c = .base (.gate b)) ∨ (∃ l, c = .lookup l) := by
  intro c hc
  simp only [canon9ConstraintsAt, List.mem_flatMap] at hc
  obtain ⟨blk, -, hc⟩ := hc
  obtain ⟨slot, -, hc⟩ := hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨b, rfl⟩
  · right
    simp only [gadgetLookups, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h
      exact ⟨_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- A gate/lookup-only list contributes no mem-op. -/
private theorem memFilter_nil (l : List VmConstraint2)
    (hl : ∀ c ∈ l, (∃ b, c = .base (.gate b)) ∨ (∃ x, c = .lookup x)) :
    l.filterMap (fun c => match c with | .memOp m => some m | _ => none) = [] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hc := hl c (by simp)
    have hcs : ∀ x ∈ cs, (∃ b, x = .base (.gate b)) ∨ (∃ y, x = .lookup y) :=
      fun x hx => hl x (List.mem_cons_of_mem c hx)
    rcases hc with ⟨b, rfl⟩ | ⟨x, rfl⟩ <;> simpa using ih hcs

/-- A gate/lookup-only list contributes no map-op. -/
private theorem mapFilter_nil (l : List VmConstraint2)
    (hl : ∀ c ∈ l, (∃ b, c = .base (.gate b)) ∨ (∃ x, c = .lookup x)) :
    l.filterMap (fun c => match c with | .mapOp m => some m | _ => none) = [] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hc := hl c (by simp)
    have hcs : ∀ x ∈ cs, (∃ b, x = .base (.gate b)) ∨ (∃ y, x = .lookup y) :=
      fun x hx => hl x (List.mem_cons_of_mem c hx)
    rcases hc with ⟨b, rfl⟩ | ⟨x, rfl⟩ <;> simpa using ih hcs

/-- The wrap contributes no mem-op (the mem log is unchanged). -/
theorem memOpsOf_fieldsCanonical9At (w : Nat) (d : EffectVmDescriptor2) :
    memOpsOf (fieldsCanonical9At w d) = memOpsOf d := by
  show (d.constraints ++ canon9ConstraintsAt w).filterMap
      (fun c => match c with | .memOp m => some m | _ => none)
    = d.constraints.filterMap (fun c => match c with | .memOp m => some m | _ => none)
  rw [List.filterMap_append, memFilter_nil _ (canon9_gate_or_lookup w), List.append_nil]

/-- The wrap contributes no map-op (the map log is unchanged). -/
theorem mapOpsOf_fieldsCanonical9At (w : Nat) (d : EffectVmDescriptor2) :
    mapOpsOf (fieldsCanonical9At w d) = mapOpsOf d := by
  show (d.constraints ++ canon9ConstraintsAt w).filterMap
      (fun c => match c with | .mapOp m => some m | _ => none)
    = d.constraints.filterMap (fun c => match c with | .mapOp m => some m | _ => none)
  rw [List.filterMap_append, mapFilter_nil _ (canon9_gate_or_lookup w), List.append_nil]

/-- **THE PEEL** — `Satisfied2 (fieldsCanonical9At w d) ⟹ Satisfied2 d`. The wrap only APPENDS
constraints and leaves every log alone, so every existing per-effect keystone lifts to the
canonicity-welded member by peeling first. -/
theorem satisfied2_of_fieldsCanonical9At (hash : List ℤ → ℤ) (w : Nat) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (fieldsCanonical9At w d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t := by
  have hmem : memLog (fieldsCanonical9At w d) t = memLog d t := by
    simp [memLog, memOpsOf_fieldsCanonical9At]
  have hmap : mapLog (fieldsCanonical9At w d) t = mapLog d t := by
    simp [mapLog, mapOpsOf_fieldsCanonical9At]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [fieldsCanonical9At_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-! ## §3 — THE GADGET, over abstract VALUES.

Proved ONCE and instantiated sixteen times. Stated on ℤ under the deployed mod-p gate denotation;
the pinned lanes' and aux columns' canonicality (`0 ≤ · < p`) is leg 2 — the committed-column
envelope, a hypothesis here because `Assignment` is ℤ-valued while a deployed column is a BabyBear
element. -/

/-- A multiple of `p` strictly inside `(−p, p)` is zero. -/
private theorem zero_of_dvd_of_lt {y : ℤ} (h : (2013265921 : ℤ) ∣ y)
    (hlo : -2013265921 < y) (hhi : y < 2013265921) : y = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hk : k = 0 := by nlinarith
  simp [hk]

/-- Two canonical values whose difference vanishes mod `p` are EQUAL over ℤ. -/
private theorem eq_of_sub_modEq_zero {a b : ℤ} (ha : 0 ≤ a) (ha' : a < 2013265921)
    (hb : 0 ≤ b) (hb' : b < 2013265921) (h : a - b ≡ 0 [ZMOD 2013265921]) : a = b := by
  have hd : (2013265921 : ℤ) ∣ a - b := Int.modEq_zero_iff_dvd.mp h
  have := zero_of_dvd_of_lt hd (by omega) (by omega)
  omega

/-- BabyBear as an integral domain: `p` is prime over ℤ. -/
private theorem P_prime_int : Prime (2013265921 : ℤ) := by
  rw [Int.prime_iff_natAbs_prime]; simpa using P_prime

/-- **The cube gate has exactly three roots.** A canonical column satisfying
`q(q−1)(q−2) ≡ 0 [ZMOD p]` is `0`, `1` or `2` — the honest quotient range, and the reason the
forged nonet's `q = 3` has no witness. -/
theorem cube_root_trichotomy {x : ℤ} (hx : 0 ≤ x) (hlt : x < 2013265921)
    (h : x * (x - 1) * (x - 2) ≡ 0 [ZMOD 2013265921]) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have hdvd : (2013265921 : ℤ) ∣ x * (x - 1) * (x - 2) := Int.modEq_zero_iff_dvd.mp h
  rcases P_prime_int.dvd_mul.mp hdvd with h1 | h2
  · rcases P_prime_int.dvd_mul.mp h1 with h3 | h4
    · exact Or.inl (zero_of_dvd_of_lt h3 (by omega) (by omega))
    · have := zero_of_dvd_of_lt h4 (by omega) (by omega)
      exact Or.inr (Or.inl (by omega))
  · have := zero_of_dvd_of_lt h2 (by omega) (by omega)
    exact Or.inr (Or.inr (by omega))

/-- **THE CARRY-DIGIT SPLIT, FORCED.** Under the split gate, the free-lane range lookup on lane 8
and the `r` lookup, the aux quotients are EXACTLY the decoder's: `q0 = decCarry % 4` and
`q1 = decCarry / 4` for `decCarry = L8 / 2^24`. -/
theorem carry_split_forced {L8 r q0 q1 : ℤ}
    (hL8 : 0 ≤ L8) (hL8' : L8 < 268435456)
    (hr : 0 ≤ r) (hr' : r < 16777216)
    (hq0 : q0 = 0 ∨ q0 = 1 ∨ q0 = 2) (hq1 : q1 = 0 ∨ q1 = 1 ∨ q1 = 2)
    (g1 : L8 - ((q0 + 4 * q1) * 16777216 + r) ≡ 0 [ZMOD 2013265921]) :
    L8 = (q0 + 4 * q1) * 16777216 + r ∧ q0 = L8 / 16777216 % 4 ∧ q1 = L8 / 16777216 / 4 := by
  have hsplit : L8 = (q0 + 4 * q1) * 16777216 + r :=
    eq_of_sub_modEq_zero hL8 (by omega) (by rcases hq0 with rfl|rfl|rfl <;>
      rcases hq1 with rfl|rfl|rfl <;> omega)
      (by rcases hq0 with rfl|rfl|rfl <;> rcases hq1 with rfl|rfl|rfl <;> omega) g1
  refine ⟨hsplit, ?_, ?_⟩ <;>
    rcases hq0 with rfl|rfl|rfl <;> rcases hq1 with rfl|rfl|rfl <;> omega

/-- **THE `NoWrap` HALF, FORCED, for one pinned lane.** Given the quotient `q ∈ {0,1,2}`, the two
`v`-gates and their two `< 2^28` lookups, the pinned lane's restored word stays a `u32`:
`L + q·p < 2^32`. This is leg 3, and it is where the forgery lives. -/
theorem noWrap_half_forced {L q v vb : ℤ}
    (hL : 0 ≤ L) (hL' : L < 2013265921)
    (hv : 0 ≤ v) (hv' : v < 268435456) (hvb : 0 ≤ vb) (hvb' : vb < 268435456)
    (hq : q = 0 ∨ q = 1 ∨ q = 2)
    (gv : 2 * v - (q * (q - 1)) * L ≡ 0 [ZMOD 2013265921])
    (gvb : vb - (v + q * (q - 1)) ≡ 0 [ZMOD 2013265921]) :
    L + q * 2013265921 < 4294967296 := by
  rcases hq with rfl | rfl | rfl
  · -- q = 0: the selector is dead, and nothing is needed — `L < p < 2^32`.
    omega
  · -- q = 1: still dead, and `L + p ≤ 2p − 1 < 2^32`.
    omega
  · -- q = 2: the selector is LIVE. `2·v ≡ 2·L` and `p` odd give `v = L`; then `vb = L + 2 < 2^28`.
    have hsel : (2 : ℤ) * (2 - 1) = 2 := by norm_num
    rw [hsel] at gv gvb
    have hdvd : (2013265921 : ℤ) ∣ 2 * (v - L) := by
      have h := Int.modEq_zero_iff_dvd.mp gv
      have heq : (2 : ℤ) * v - 2 * L = 2 * (v - L) := by ring
      rwa [heq] at h
    -- ⚠ `linarith`, not `omega`, from here down: `omega` reifies the `Int.ModEq` / `∣`
    -- hypotheses still in context and times out at `whnf` on them (measured, 200k heartbeats).
    have hvl : v = L := by
      rcases P_prime_int.dvd_mul.mp hdvd with h | h
      · exact absurd (Int.le_of_dvd (by norm_num) h) (by norm_num)
      · have hlo : -2013265921 < v - L := by linarith
        have hhi : v - L < 2013265921 := by linarith
        have h0 : v - L = 0 := zero_of_dvd_of_lt h hlo hhi
        linarith
    have hb1 : (0 : ℤ) ≤ v + 2 := by linarith
    have hb2 : v + 2 < 2013265921 := by linarith
    have hvb2 : vb = v + 2 := eq_of_sub_modEq_zero hvb (by linarith) hb1 hb2 gvb
    linarith

/-- **THE FORGED NONET HAS NO WITNESS.** With lane 8 at `3·2^24` (the exhibit
`FieldLanes9.forgedLanes`), the split gate demands `q0 + 4·q1 = 3` while the cube gates confine both
quotients to `{0,1,2}` — and `q1 = 0 ⟹ q0 = 3`. There is no aux fill, at ANY canonical values, so
the member is UNSAT on that witness. -/
theorem forged_nonet_admits_no_witness {r q0 q1 : ℤ}
    (hr : 0 ≤ r) (hr' : r < 16777216)
    (hq0 : 0 ≤ q0) (hq0' : q0 < 2013265921) (hq1 : 0 ≤ q1) (hq1' : q1 < 2013265921)
    (g1 : (50331648 : ℤ) - ((q0 + 4 * q1) * 16777216 + r) ≡ 0 [ZMOD 2013265921])
    (g2 : q0 * (q0 - 1) * (q0 - 2) ≡ 0 [ZMOD 2013265921])
    (g3 : q1 * (q1 - 1) * (q1 - 2) ≡ 0 [ZMOD 2013265921]) : False := by
  have h0 := cube_root_trichotomy hq0 hq0' g2
  have h1 := cube_root_trichotomy hq1 hq1' g3
  obtain ⟨hsplit, -, -⟩ := carry_split_forced (by norm_num) (by norm_num) hr hr' h0 h1 g1
  rcases h0 with rfl|rfl|rfl <;> rcases h1 with rfl|rfl|rfl <;> omega

/-! ## §3b — THE BRIDGE: the gadget's `q0`/`q1` ARE `FieldLanes9.decCarry`'s two halves.

Without this the gadget would only be *shaped like* `NoWrap`. `Canonical9`'s third leg is stated
over the DECODER's carry digit — base-256 digit 24 of `decWord` — and the emitted gates split lane
8's top nibble. These are the same number, and that is a theorem, not a comment. -/

open Dregg2.Circuit.FieldLanes9 (Lanes9 FreeLanesRanged PinnedLanesField NoWrap Canonical9
  digitsN ofDigits ofDigits_append ofDigits_lt decWord decDigits decCarry decLo decHi laneList CH P)

/-- Digit `j` of a `k`-digit base-`b` expansion is `n / b^j % b`. -/
theorem digitsN_getD (b : Nat) (hb : 0 < b) :
    ∀ (k j n : Nat), j < k → (digitsN b k n).getD j 0 = n / b ^ j % b := by
  intro k
  induction k with
  | zero => intro j n hj; omega
  | succ k ih =>
    intro j n hj
    cases j with
    | zero => simp [digitsN]
    | succ j =>
      have hjk : j < k := by omega
      simp only [digitsN, List.getD_cons_succ, ih j (n / b) hjk]
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (b ^ j) b]

/-- **THE BRIDGE.** Under leg 1 the decoder's disambiguation digit IS lane 8's top nibble: the six
lanes below it contribute strictly under `2^168 = CH^6`, so base-256 digit 24 of `decWord` is
`L 8 / 2^24`. This is what makes the emitted split gate a statement about `decCarry` — and hence
about `NoWrap` — rather than about a coincidentally similar number. -/
theorem decCarry_eq_lane8_top {L : Lanes9} (h : FreeLanesRanged L) :
    decCarry L = L 8 / 16777216 := by
  have h8 : L 8 < CH := h 8 (by decide)
  have hsplit : decWord L = ofDigits CH [L 2, L 3, L 4, L 5, L 6, L 7] + CH ^ 6 * L 8 := by
    have := ofDigits_append CH [L 2, L 3, L 4, L 5, L 6, L 7] [L 8]
    simpa [decWord, laneList, ofDigits] using this
  have hlow : ofDigits CH [L 2, L 3, L 4, L 5, L 6, L 7] < CH ^ 6 := by
    have := ofDigits_lt CH (by decide) [L 2, L 3, L 4, L 5, L 6, L 7] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> exact h _ (by decide))
    simpa using this
  set A := ofDigits CH [L 2, L 3, L 4, L 5, L 6, L 7] with hA
  have hCH6 : CH ^ 6 = 374144419156711147060143317175368453031918731001856 := by
    simp only [CH]; norm_num
  have hpos : 0 < CH ^ 6 := by rw [hCH6]; norm_num
  have hd : (A + CH ^ 6 * L 8) / CH ^ 6 = L 8 := by
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlow, Nat.zero_add]
  have h256 : (256 : Nat) ^ 24 = CH ^ 6 * 16777216 := by rw [hCH6]; norm_num
  have hcarry : decWord L / 256 ^ 24 = L 8 / 16777216 := by
    rw [hsplit, h256, ← Nat.div_div_eq_div_mul, hd]
  have hlt16 : L 8 / 16777216 < 256 := by
    have : L 8 < 268435456 := by simpa [CH] using h8
    omega
  have hgetd : decCarry L = decWord L / 256 ^ 24 % 256 := by
    rw [decCarry, decDigits]
    exact digitsN_getD 256 (by norm_num) 25 24 (decWord L) (by norm_num)
  rw [hgetd, hcarry, Nat.mod_eq_of_lt hlt16]

/-- The two halves of the split are exactly the decoder's two restored quotients. -/
theorem decLo_decHi_eq {L : Lanes9} (h : FreeLanesRanged L) :
    decLo L = L 0 + (L 8 / 16777216 % 4) * P ∧ decHi L = L 1 + (L 8 / 16777216 / 4) * P := by
  rw [decLo, decHi, decCarry_eq_lane8_top h]
  exact ⟨rfl, rfl⟩

#assert_axioms digitsN_getD
#assert_axioms decCarry_eq_lane8_top
#assert_axioms decLo_decHi_eq

/-! ## §4 — THE EMIT, FORCED: from `Satisfied2` to `Canonical9`.

The extraction is deliberately mechanical: a lookup gives an ℤ interval through
`range_row_mem_iff`, a gate gives a mod-p congruence through `holdsVm_gate_of_notLast`, and §3
does the arithmetic. What this section adds is that the constraints really ARE constraints of the
wrapped member — the step a "declared but never consulted" pin would fail. -/

/-- Every emitted constraint of `(blk, slot)` is a constraint of the wrapped member. -/
theorem slot_mem (w : Nat) (d : EffectVmDescriptor2) (blk : Fin 2) (slot : Fin 8)
    {c : VmConstraint2} (hc : c ∈ slotConstraintsAt w blk slot) :
    c ∈ (fieldsCanonical9At w d).constraints :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨blk, List.mem_finRange _,
    List.mem_flatMap.mpr ⟨slot, List.mem_finRange _, hc⟩⟩)

/-- A range lookup of the emit BINDS: its column lies in `[0, 2^bits)` on every row. -/
theorem lookup_forces {hash : List ℤ → ℤ} {w : Nat} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (fieldsCanonical9At w d) minit mfin maddrs t)
    {bits col : Nat} (hrt : t.tf (rangeTidW bits) = rangeRows bits)
    {i : Nat} (hi : i < t.rows.length) {blk : Fin 2} {slot : Fin 8}
    (hc : rangeLk bits col ∈ slotConstraintsAt w blk slot) :
    0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < (2 : ℤ) ^ bits := by
  have h := hsat.rowConstraints i hi _ (slot_mem w d blk slot hc)
  have h' : [(envAt t i).loc col] ∈ t.tf (rangeTidW bits) := by
    simpa [VmConstraint2.holdsAt, Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt, rangeLk,
      EmittedExpr.eval] using h
  rw [hrt] at h'
  exact (range_row_mem_iff _ bits).mp h'

/-- A gate of the emit BINDS on every non-last row: its body vanishes mod `p`. (The deployed wire
runs `LastRowFrameHardening.hardenLastRow` OVER this emit, which lifts each body onto the whole
domain — so on the wire the last row is bound too. Stated here at the unhardened resolution, which
is the weaker and therefore honest one.) -/
theorem gate_forces {hash : List ℤ → ℤ} {w : Nat} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (fieldsCanonical9At w d) minit mfin maddrs t)
    {b : EmittedExpr} {i : Nat} (hi : i < t.rows.length)
    (hnl : (i + 1 == t.rows.length) = false) {blk : Fin 2} {slot : Fin 8}
    (hc : VmConstraint2.base (.gate b) ∈ slotConstraintsAt w blk slot) :
    b.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints i hi _ (slot_mem w d blk slot hc)
  rw [VmConstraint2.holdsAt, holdsVm_gate_of_notLast _ _ _ _ hnl] at h
  exact h

/-- Rewrite a mod-`p` vanishing along a ring identity. -/
private theorem modEq_zero_congr {a b : ℤ} (h : a = b) (hb : a ≡ 0 [ZMOD 2013265921]) :
    b ≡ 0 [ZMOD 2013265921] := h ▸ hb

/-- **THE FORCING.** On any non-last row of a `Satisfied2` witness of the canonicity-welded member,
against the two faithful width-tagged range tables and the deployed canonical-column envelope, the
committed nonet of EVERY `(block, slot)` satisfies `FieldLanes9.Canonical9` — which
`FieldLanes9.canonical9_iff_in_image` proves is EXACTLY the nine-lane encoder's image. So the
committed columns are the lanes of SOME 32-byte value, and by `lanes9ToField_injOn_canonical` of
exactly one. That is the sentence `fieldToLanes9_injective` could not reach. -/
theorem canon9_forces_canonical {hash : List ℤ → ℤ} {w : Nat} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (fieldsCanonical9At w d) minit mfin maddrs t)
    (h28 : t.tf (rangeTidW LANE_BITS) = rangeRows LANE_BITS)
    (h24 : t.tf (rangeTidW R_BITS) = rangeRows R_BITS)
    {i : Nat} (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c : Nat, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (blk : Fin 2) (slot : Fin 8) :
    Canonical9 (fun l => ((envAt t i).loc (laneColAt w blk slot l)).toNat) := by
  set E := envAt t i with hE
  -- leg 1: the seven free-lane lookups, indexed by their own `Fin 7`
  have hfree7 : ∀ j : Fin 7,
      0 ≤ E.loc (laneColAt w blk slot ⟨j.1 + 2, by omega⟩)
      ∧ E.loc (laneColAt w blk slot ⟨j.1 + 2, by omega⟩) < (2 : ℤ) ^ 28 := by
    intro j
    refine lookup_forces hsat h28 hi (blk := blk) (slot := slot) ?_
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_map_of_mem (List.mem_map_of_mem (List.mem_finRange j))))
  have hfree : ∀ l : Fin 9, 2 ≤ l.1 →
      0 ≤ E.loc (laneColAt w blk slot l) ∧ E.loc (laneColAt w blk slot l) < (2 : ℤ) ^ 28 := by
    intro l hl
    have hj : l = ⟨(l.1 - 2) + 2, by omega⟩ := by apply Fin.ext; simp; omega
    rw [hj]
    exact hfree7 ⟨l.1 - 2, by omega⟩
  have hL8 := hfree 8 (by decide)
  -- the five aux lookups
  have haux : ∀ k : Fin 7, k.1 ≠ 1 → k.1 ≠ 2 →
      0 ≤ E.loc (auxColAt w blk slot k)
      ∧ E.loc (auxColAt w blk slot k) < (2 : ℤ) ^ (if k.1 = 0 then 24 else 28) := by
    intro k h1 h2
    fin_cases k
    · exact lookup_forces hsat h24 hi (blk := blk) (slot := slot)
        (List.mem_append_right _ (List.mem_append_right _ (by simp)))
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact lookup_forces hsat h28 hi (blk := blk) (slot := slot)
        (List.mem_append_right _ (List.mem_append_right _ (by simp)))
    · exact lookup_forces hsat h28 hi (blk := blk) (slot := slot)
        (List.mem_append_right _ (List.mem_append_right _ (by simp)))
    · exact lookup_forces hsat h28 hi (blk := blk) (slot := slot)
        (List.mem_append_right _ (List.mem_append_right _ (by simp)))
    · exact lookup_forces hsat h28 hi (blk := blk) (slot := slot)
        (List.mem_append_right _ (List.mem_append_right _ (by simp)))
  have hr : 0 ≤ E.loc (auxColAt w blk slot 0) ∧ E.loc (auxColAt w blk slot 0) < (2 : ℤ) ^ 24 :=
    haux 0 (by decide) (by decide)
  have hv0 : 0 ≤ E.loc (auxColAt w blk slot 3) ∧ E.loc (auxColAt w blk slot 3) < (2 : ℤ) ^ 28 :=
    haux 3 (by decide) (by decide)
  have hv0b : 0 ≤ E.loc (auxColAt w blk slot 4) ∧ E.loc (auxColAt w blk slot 4) < (2 : ℤ) ^ 28 :=
    haux 4 (by decide) (by decide)
  have hv1 : 0 ≤ E.loc (auxColAt w blk slot 5) ∧ E.loc (auxColAt w blk slot 5) < (2 : ℤ) ^ 28 :=
    haux 5 (by decide) (by decide)
  have hv1b : 0 ≤ E.loc (auxColAt w blk slot 6) ∧ E.loc (auxColAt w blk slot 6) < (2 : ℤ) ^ 28 :=
    haux 6 (by decide) (by decide)
  -- the seven gates
  have gs : ∀ b ∈ gadgetBodies (laneColAt w blk slot 0) (laneColAt w blk slot 1)
      (laneColAt w blk slot 8) (auxColAt w blk slot 0) (auxColAt w blk slot 1)
      (auxColAt w blk slot 2) (auxColAt w blk slot 3) (auxColAt w blk slot 4)
      (auxColAt w blk slot 5) (auxColAt w blk slot 6),
      b.eval E.loc ≡ 0 [ZMOD 2013265921] := fun b hb =>
    gate_forces hsat hi hnl (blk := blk) (slot := slot)
      (List.mem_append_left _ (List.mem_map_of_mem hb))
  simp only [gadgetBodies, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at gs
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := gs
  simp only [eSub, eK, eV, twoSel, EmittedExpr.eval] at g1 g2 g3 g4 g5 g6 g7
  -- name the ℤ values
  set x0 := E.loc (laneColAt w blk slot 0) with hx0
  set x1 := E.loc (laneColAt w blk slot 1) with hx1
  set x8 := E.loc (laneColAt w blk slot 8) with hx8
  set xr := E.loc (auxColAt w blk slot 0) with hxr
  set xq0 := E.loc (auxColAt w blk slot 1) with hxq0
  set xq1 := E.loc (auxColAt w blk slot 2) with hxq1
  set xv0 := E.loc (auxColAt w blk slot 3) with hxv0
  set xv0b := E.loc (auxColAt w blk slot 4) with hxv0b
  set xv1 := E.loc (auxColAt w blk slot 5) with hxv1
  set xv1b := E.loc (auxColAt w blk slot 6) with hxv1b
  have g1' : x8 - ((xq0 + 4 * xq1) * 16777216 + xr) ≡ 0 [ZMOD 2013265921] :=
    modEq_zero_congr (by ring) g1
  have g2' : xq0 * (xq0 - 1) * (xq0 - 2) ≡ 0 [ZMOD 2013265921] :=
    modEq_zero_congr (by ring) g2
  have g3' : xq1 * (xq1 - 1) * (xq1 - 2) ≡ 0 [ZMOD 2013265921] :=
    modEq_zero_congr (by ring) g3
  have g4' : 2 * xv0 - (xq0 * (xq0 - 1)) * x0 ≡ 0 [ZMOD 2013265921] :=
    modEq_zero_congr (by ring) g4
  have g5' : 2 * xv1 - (xq1 * (xq1 - 1)) * x1 ≡ 0 [ZMOD 2013265921] :=
    modEq_zero_congr (by ring) g5
  have g6' : xv0b - (xv0 + xq0 * (xq0 - 1)) ≡ 0 [ZMOD 2013265921] :=
    modEq_zero_congr (by ring) g6
  have g7' : xv1b - (xv1 + xq1 * (xq1 - 1)) ≡ 0 [ZMOD 2013265921] :=
    modEq_zero_congr (by ring) g7
  have hq0t : xq0 = 0 ∨ xq0 = 1 ∨ xq0 = 2 :=
    cube_root_trichotomy (hcanon _).1 (hcanon _).2 g2'
  have hq1t : xq1 = 0 ∨ xq1 = 1 ∨ xq1 = 2 :=
    cube_root_trichotomy (hcanon _).1 (hcanon _).2 g3'
  obtain ⟨-, hq0e, hq1e⟩ := carry_split_forced hL8.1 (by norm_num at hL8; omega) hr.1
    (by norm_num at hr; omega) hq0t hq1t g1'
  have hlo : x0 + xq0 * 2013265921 < 4294967296 :=
    noWrap_half_forced (hcanon _).1 (hcanon _).2 hv0.1 (by norm_num at hv0; omega) hv0b.1
      (by norm_num at hv0b; omega) hq0t g4' g6'
  have hhi : x1 + xq1 * 2013265921 < 4294967296 :=
    noWrap_half_forced (hcanon _).1 (hcanon _).2 hv1.1 (by norm_num at hv1; omega) hv1b.1
      (by norm_num at hv1b; omega) hq1t g5' g7'
  have hL8b : 0 ≤ x8 ∧ x8 < 268435456 := ⟨hL8.1, by norm_num at hL8; omega⟩
  -- assemble `Canonical9` on the Nat view
  have hFLR : FreeLanesRanged (fun l => (E.loc (laneColAt w blk slot l)).toNat) := by
    intro l hl
    have h := hfree l hl
    have h2 : E.loc (laneColAt w blk slot l) < 268435456 := by norm_num at h; omega
    simp only [CH]
    omega
  refine ⟨hFLR, ⟨?_, ?_⟩, ?_, ?_⟩
  · have := (hcanon (laneColAt w blk slot 0)); simp only [P, ← hx0] at *; omega
  · have := (hcanon (laneColAt w blk slot 1)); simp only [P, ← hx1] at *; omega
  · rw [(decLo_decHi_eq hFLR).1]
    simp only [P, ← hx0, ← hx8]
    have hc0 := hcanon (laneColAt w blk slot 0)
    omega
  · rw [(decLo_decHi_eq hFLR).2]
    simp only [P, ← hx1, ← hx8]
    have hc1 := hcanon (laneColAt w blk slot 1)
    omega

/-- **⚑ THE FORGED NONET IS UNSAT ON THE EMITTED MEMBER.** A witness whose `fields[slot]` lane 8
carries `3·2^24` — `FieldLanes9.forgedLanes`, the vector that passes all seven free-lane range
lookups and still makes the welded v1 face and the decode disagree — does NOT satisfy the
canonicity-welded member on any non-last row. Not "is caught by a check": there is NO aux fill, at
any canonical values, because the split gate demands `q0 + 4·q1 = 3` while the cube gates confine
both quotients to `{0,1,2}`.

⚑ Note what this does NOT assume: nothing about the other eight lanes, nothing about lanes 0/1,
and no honesty of the producer. Lane 8 alone is enough. -/
theorem canon9_rejects_the_forged_nonet {hash : List ℤ → ℤ} {w : Nat} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h24 : t.tf (rangeTidW R_BITS) = rangeRows R_BITS)
    {i : Nat} (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c : Nat, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (blk : Fin 2) (slot : Fin 8)
    (hforged : (envAt t i).loc (laneColAt w blk slot 8) = 50331648) :
    ¬ Satisfied2 hash (fieldsCanonical9At w d) minit mfin maddrs t := by
  intro hsat
  set E := envAt t i with hE
  have hr : 0 ≤ E.loc (auxColAt w blk slot 0) ∧ E.loc (auxColAt w blk slot 0) < (2 : ℤ) ^ 24 :=
    lookup_forces hsat h24 hi (blk := blk) (slot := slot)
      (List.mem_append_right _ (List.mem_append_right _ (by simp)))
  have gs : ∀ b ∈ gadgetBodies (laneColAt w blk slot 0) (laneColAt w blk slot 1)
      (laneColAt w blk slot 8) (auxColAt w blk slot 0) (auxColAt w blk slot 1)
      (auxColAt w blk slot 2) (auxColAt w blk slot 3) (auxColAt w blk slot 4)
      (auxColAt w blk slot 5) (auxColAt w blk slot 6),
      b.eval E.loc ≡ 0 [ZMOD 2013265921] := fun b hb =>
    gate_forces hsat hi hnl (blk := blk) (slot := slot)
      (List.mem_append_left _ (List.mem_map_of_mem hb))
  simp only [gadgetBodies, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at gs
  obtain ⟨g1, g2, g3, -, -, -, -⟩ := gs
  simp only [eSub, eK, eV, twoSel, EmittedExpr.eval, hforged] at g1 g2 g3
  set xr := E.loc (auxColAt w blk slot 0) with hxr
  set xq0 := E.loc (auxColAt w blk slot 1) with hxq0
  set xq1 := E.loc (auxColAt w blk slot 2) with hxq1
  have g1' : (50331648 : ℤ) - ((xq0 + 4 * xq1) * 16777216 + xr) ≡ 0 [ZMOD 2013265921] :=
    modEq_zero_congr (by ring) g1
  have g2' : xq0 * (xq0 - 1) * (xq0 - 2) ≡ 0 [ZMOD 2013265921] := modEq_zero_congr (by ring) g2
  have g3' : xq1 * (xq1 - 1) * (xq1 - 2) ≡ 0 [ZMOD 2013265921] := modEq_zero_congr (by ring) g3
  exact forged_nonet_admits_no_witness hr.1 (by norm_num at hr; omega)
    (hcanon _).1 (hcanon _).2 (hcanon _).1 (hcanon _).2 g1' g2' g3'

#assert_axioms canon9_rejects_the_forged_nonet

#assert_axioms slot_mem
#assert_axioms lookup_forces
#assert_axioms gate_forces
#assert_axioms canon9_forces_canonical

/-- Lane 8 of the exhibit really is `3·2^24`, and its Lean twin is `FieldLanes9.forgedLanes`. -/
theorem forged_lane8_is_three_times_2p24 :
    Dregg2.Circuit.FieldLanes9.forgedLanes 8 = 50331648
    ∧ (50331648 : Nat) = 3 * 16777216 := ⟨rfl, by norm_num⟩

#assert_axioms P_prime
#assert_axioms cube_root_trichotomy
#assert_axioms carry_split_forced
#assert_axioms noWrap_half_forced
#assert_axioms forged_nonet_admits_no_witness
#assert_axioms canon9_gate_or_lookup
#assert_axioms satisfied2_of_fieldsCanonical9At

end Dregg2.Circuit.Emit.FieldsCanonicity9Emit
