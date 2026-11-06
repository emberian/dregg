/-
# `Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir` — **THE 2 381 CHUNK BITS STOP BEING FREE.**

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this is a **Lean-authored AIR**. `bodyBitsDesc` is
`EffectLower.lowerTiedAir` applied to the `EffectAir` source `bodyBitsAir` (§3). There is **no
hand-written `VmConstraint2` in this file** and Rust authors nothing; Rust proves the artifact.

## ⚑⚑ THE HOLE THIS CLOSES

`MinaStateBodyHashChain` §8 residual 2, in its own words:

> *"**`pack_to_fields` IS NOT IN CIRCUIT.** … nothing gates that they are the packing of 819
> width-declared chunks, and in particular **nothing forces each chunk `< 2^n`**, without which the
> packing is not injective. That is the next rung and it is cheap: 781 of the 819 chunks are ONE
> BIT."*

`Bridge.MinaPackInjective` proves the arithmetic half — `packing_is_injective`, and
`the_range_hypothesis_is_load_bearing` exhibits the alias that follows when the hypothesis is
dropped:

    packToFields ⟨[], [(1, 1), (0, 1)]⟩ = [2] = packToFields ⟨[], [(0, 1), (2, 1)]⟩

Same 49 absorbed elements, same `state_body_hash`, same 25-link chain, same root — **and every link
honest.** This file is the gate that discharges the hypothesis.

## ⚑ THE SHAPE, AND WHY IT IS BITS AND NOT CHUNKS

The brief for this rung read *"booleanity for the 781, declared-width for the rest"*. Re-derived on
the deployed field: **a declared width IS a bit count, and at BabyBear a 32- or 64-bit chunk has no
column to live in** (`p ≈ 2^31`). So every chunk is carried as its own bit slice and the 38 wide
chunks are gated by the SAME `x·(x−1) = 0` the 781 booleans are. `MinaPackInjective.bitsToNat_lt` is
that identification as a theorem: `n` boolean columns cannot denote a value `≥ 2^n`, whatever the
prover writes.

⚑ **AND THE PRICE MOVED THE OTHER WAY FROM THE BRIEF.** The brief warned *"your chunk gates ADD
range lookups; price them in committed width"* — because `MainLayout::build` appends a nibble aux
block per range lookup and range decomposition was 71.7% of the unnarrowed accumulator row. **This
descriptor declares NO table and emits NO lookup.** A booleanity gate is a degree-2 window gate, not
a bus query, so the committed width is the declared width: **2 683 declared, 2 683 committed, 1.00×**
(`the_committed_width_is_the_declared_width`, and `circuit/tests/mina_body_preimage_bits_proves.rs`
re-derives it from `decomp_cols_pub` on the emitted bytes). Against `dregg-pasta-fp-chainlink::v1`'s
469 → 1 037 (2.21×) and the accumulator's 3 048 → 10 756 (3.53×), the chunk gates are the first rung
in this cone whose aux block is empty.

## Layout — ONE ROW, and the row is the whole packed preimage

    col 0 .. 2380         BIT j      the j-th bit of the packed half of `Body.to_input`,
                                     chunks in append order, MSB-first WITHIN each chunk
    col 2381 .. 2682      PLIMB e k  limb k of packed field element 38+e, base 256, k = 0 lowest
                                     (e < 11, k < ⌈W_e/8⌉ — 32,29,29,29,32,29,28,32,28,25,9)

    PI 0 .. 301           PLIMB e k, published so a recursion fold can reach it from
                          `air_public_targets` — the layout `MinaStateBodyHashChain`'s absorbed
                          block already speaks (`SK = 32` eight-bit limbs an element)

⚑ **WHY THE BIT COLUMNS ARE 2 381 AND NOT 11 × 254.** A packed element is `⌈W_e/8⌉` bytes wide and
the eleven runs have DIFFERENT widths (254, 226, 229, 229, 254, 227, 224, 254, 223, 194, 67). Giving
every element a uniform 254 bit columns would leave `254 − W_e` columns that the honest witness sets
to zero and nothing refuses — a PHANTOM CHUNK, and an element that is the packing of no in-range
stream at all. The bit columns are exactly the stream's, so the phantom is unrepresentable rather
than gated.

⚑ **THE SCHEDULE IS DESCRIPTOR SHAPE, NOT WITNESS — AND THAT IS LOAD-BEARING.**
`MinaPackInjective.the_schedule_hypothesis_is_load_bearing` exhibits `[(1,1)]` and `[(1,2)]`: both in
range, both packing to `[1]`. A prover who may DECLARE the widths chooses the reading. Here the
widths are the slice lengths of a constant partition
(`the_run_schedule_is_the_real_blocks_packing`), and `MinaStateHashPackPrice.
the_packing_control_flow_reads_only_the_width` is why that is legitimate: `packStep`'s branch is a
function of `(n, accN)` and never of a value, so the chunk boundaries of a `Protocol_state.Body` are
fixed by its TYPE and are the same for every Mina block.

## ⚑ WHAT THIS BUYS, IN THE UNITS THE CAMPAIGN USES — AND WHAT IT DOES NOT

**Of the `state_body_hash` preimage — 38 whole field elements and 819 width-declared chunks — this
rung constrains ALL FORTY-NINE ABSORBED ELEMENTS SINCE 2026-08-09**: the 819 chunks by booleanity,
and the 38 whole field elements by the felt-level `.limbs` gate.

  * ⚑ **CONSTRAINED: 2 381 bits.** Every chunk is a bit slice of a boolean vector, so every chunk is
    below its declared width (`MinaPackInjective.the_boolean_gates_force_the_range`), so
    `packing_is_injective` applies and the eleven packed elements determine all 819 chunk values
    exactly once (`MinaPackInjective.the_gated_bits_are_determined_by_the_packing`).
  * ⚑⚑ **CONSTRAINED SINCE 2026-08-09: the 38 whole field elements.** They pass through
    `packToFields` untouched and have no declared width — so the gate that fits them is not a chunk
    gate but the FELT-level one, `AirLeg.limbs`, the same construct `minaLcVerifyDesc` spends
    eighteen range lookups on for its two state hashes. Each element gets `SK = 32` base-256 limb
    columns and ONE `.limbs` leg at `bits := 8` (`fieldLimbsLeg`), so a row this descriptor accepts
    denotes 38 values BELOW `2^256` — which is exactly `Seam.Renders`' canonicality hypothesis and
    therefore exactly what an elementwise 32-limb weld needs to carry a whole value with no digest
    (`Seam.limb_inj`). ⚠ Say the price out loud: **1 216 range lookups where this descriptor
    previously had zero**, and the committed width stops being the declared width
    (`the_field_gates_are_the_whole_lookup_bill`).
  * ⚑⚑ **AND THE WELD EXISTS SINCE 2026-08-09.** `MinaBodyPreimageSeams.bodyPreimageSeam j` is the
    25-seam family that connects this descriptor's 1 518 published limb slots to
    `MinaStateBodyHashChain`'s twenty-five links' ABSORBED blocks, elementwise, with the
    `32 − ⌈W_e/8⌉` high limbs of each packed element and all 32 limbs of the odd-tail pad zero-pinned
    on the chain side. S1 names the published slots on both ends; S2 (`bodyPreimageSeamCertifies`)
    is refutable (`body_preimage_seam_S2_needs_the_seam`). What was an executor comparison is a
    seam-forced conjunct.

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

**2026-08-08 — A NEW DESCRIPTOR, `dregg-mina-body-preimage-bits::v1`.** Nothing existing changes
shape. It emits `circuit/descriptors/by-name/dregg-mina-body-preimage-bits-v1.json` and MINTS a VK
for it; no VK rotates, nothing re-genesises, and `PROVENANCE.json` gains no row that this file
stamps — the stamp is the operator's ceremony and four rows already await it.

⚑ **2026-08-09 — THAT DESCRIPTOR CHANGES SHAPE, AND EVERY BYTE OF IT MOVES.** `trace_width`
**2 683 → 3 899**, `piCount` **302 → 1 518**, `tables` `[] → [range_w8]`, constraints
**2 985 → 4 239**. The PI vector is now the ABSORB ORDER of `packToFields` — slots `[0, 1216)` are
the 38 whole field elements' 32 limbs each and slots `[1216, 1518)` are the eleven packed elements'
`⌈W_e/8⌉` — so `PI_PLIMB e k` MOVED by `+1216` and any consumer reading the old base reads field
element 38's limbs. RE-EMITS: `circuit/descriptors/by-name/dregg-mina-body-preimage-bits-v1.json`,
its VK, and `circuit/tests/mina_body_preimage_bits_proves.rs`' width/pi/constraint pins. The old
shape REFUSES to load: a 302-slot claim cannot satisfy `pinsFit 1518`, and the seam reader
(`seam.rs::SeamEnd::require_matches`) RECOMPUTES the fingerprint lanes and refuses the stale
descriptor by name-and-lanes rather than accepting it silently.

## Import line for the root: `import Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir`
-/
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.Emit.PastaFieldSound
import Dregg2.Circuit.GateExpr
import Dregg2.Bridge.MinaPackInjective

namespace Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir

open Dregg2.Circuit (Assignment Expr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB limbAt)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg WindowLeg LimbsLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Bridge.MinaStateHashDerive
open Dregg2.Bridge.MinaPackInjective (bitsToNat chunksOfSlices InRange PositiveWidths
  the_boolean_gates_force_the_range the_gated_bits_are_determined_by_the_packing)

set_option autoImplicit false
set_option maxRecDepth 2000000
-- ⚑ 3 085 legs through `lowerAir`, and the `rfl` shape pins below reduce the whole emitted list.
set_option maxHeartbeats 3200000

/-! ## §1 — ⚑ THE RUN SCHEDULE, AS SHAPE — AND TIED TO THE REAL BLOCK'S PACKING. -/

/-- `packStep`'s boundary rule, read as a grouping of the WIDTH schedule alone. ⚑ Legitimate
because `MinaStateHashPackPrice.the_packing_control_flow_reads_only_the_width` proves the branch
never reads a value. -/
def runsOfWidths (ws : List Nat) : List (List Nat) :=
  let step : (List (List Nat) × List Nat × Nat) → Nat → (List (List Nat) × List Nat × Nat) :=
    fun (done, cur, accN) n =>
      if n + accN < fieldSizeInBits then (done, cur ++ [n], n + accN) else (done ++ [cur], [n], n)
  match ws.foldl step ([], [], 0) with
  | (done, cur, accN) => if accN > 0 then done ++ [cur] else done

/-- ⚑ **THE ELEVEN RUN WIDTHS.** How many bits of the chunk stream each packed field element holds.
Not uniform, and that is why the bit columns are the STREAM's rather than eleven fixed blocks. -/
def RUN_WIDTH : List Nat := [254, 226, 229, 229, 254, 227, 224, 254, 223, 194, 67]

/-- The stream-bit offset each run starts at — the running sum of `RUN_WIDTH`. -/
def RUN_START : List Nat := [0, 254, 480, 709, 938, 1192, 1419, 1643, 1897, 2120, 2314]

def NELEM : Nat := 11
def NBITS : Nat := 2381

/-- ⚑ **HOW MANY LIMBS EACH ELEMENT GETS — `⌈W_e/8⌉`, AND NOT A UNIFORM 32.**

⚠ This is not a saving, it is a REFUSAL. A uniform 32-limb block would give element 10 (67 bits)
twenty-three limbs whose gate is `PLIMB = 0` — a published column no gate joins to any other, i.e.
**twenty-three decorative anchors**, fifty across the eleven elements. `LightClientAnchorConnectivity`
measures exactly that and `scripts/check-descriptor-anchor-inertness.py` is the ratchet. Allocating
`⌈W_e/8⌉` makes the empty limb unrepresentable instead of published-and-inert.

⚠ **AND SAY WHAT THAT LEAVES OWED**, because it moves an obligation rather than removing one: the
chain's absorbed block is `SK = 32` limbs an element, so the weld must connect these `⌈W_e/8⌉` and
pin the remaining `32 − ⌈W_e/8⌉` chain-side limbs to ZERO. `the_high_limbs_of_the_real_elements_are_
zero` is that they are zero in the honest witness; forcing it is the weld's job and §7 names it. -/
def LIMB_COUNT : List Nat := [32, 29, 29, 29, 32, 29, 28, 32, 28, 25, 9]

/-- The PI offset each element's limb block starts at — the running sum of `LIMB_COUNT`. -/
def LIMB_BASE : List Nat := [0, 32, 61, 90, 119, 151, 180, 208, 240, 268, 293]

def NLIMB : Nat := 302

def limbCount (e : Nat) : Nat := LIMB_COUNT.getD e 0
def limbBase (e : Nat) : Nat := LIMB_BASE.getD e 0

def runWidth (e : Nat) : Nat := RUN_WIDTH.getD e 0
def runStart (e : Nat) : Nat := RUN_START.getD e 0

/-- ⚑ The limb allocation IS `⌈W_e/8⌉`, and the bases are its running sum — derived from
`RUN_WIDTH`, not written down beside it. -/
theorem the_limb_allocation_is_the_run_widths :
    (∀ e < NELEM, limbCount e = (runWidth e + 7) / 8)
      ∧ (∀ e < NELEM, limbBase e + limbCount e = limbBase (e + 1) ∨ e + 1 = NELEM)
      ∧ LIMB_COUNT.foldl (· + ·) 0 = NLIMB
      ∧ limbBase 10 + limbCount 10 = NLIMB := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> decide




/-- The eleven runs partition the 2 381 bits with nothing left over and nothing counted twice. -/
theorem the_runs_partition_the_stream :
    RUN_WIDTH.length = NELEM ∧ RUN_START.length = NELEM
      ∧ RUN_WIDTH.foldl (· + ·) 0 = NBITS
      ∧ ∀ e < NELEM, runStart e + runWidth e = runStart (e + 1) ∨ e + 1 = NELEM := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  decide

/-- ⚑⚑ **AND THE SCHEDULE IS THE REAL BLOCK'S**, not a transcription of a printout: grouping the
devnet block's own 819 declared widths by `packStep`'s boundary rule gives exactly these eleven
runs. ⚠ Compiled: it reduces the 1 544-byte binprot parse, a two-block SHA-256 and the 819-chunk
assembly — the same object `MinaStateHashPackPrice` measures compiled. -/
theorem the_run_schedule_is_the_real_blocks_packing :
    (runsOfWidths Dregg2.Bridge.MinaStateHashPackPrice.chunkWidths).map
        (fun r => r.foldl (· + ·) 0) = RUN_WIDTH := by native_decide

/-! ## §2 — the column layout and the PI slots. -/

/-- **`BIT j`** — bit `j` of the packed half of `Body.to_input`, chunks in append order and MSB-first
within each chunk (the order `packStep`'s `acc · 2^n + x` places them in). -/
def BIT (j : Nat) : Nat := j

/-- **`PLIMB e k`** — limb `k` of packed field element `38 + e`, base 256, `k = 0` least
significant. ⚑ The `SK = 32` eight-bit limbs `MinaStateBodyHashChain.bodyAbsorbedBlock` already
publishes for the same element, so a weld is a slice comparison and no re-encoding. -/
def PLIMB (e k : Nat) : Nat := NBITS + limbBase e + k

/-! ### ⚑⚑ THE 38 WHOLE FIELD ELEMENTS — the half this descriptor had no column for.

`packToFields c = c.fields ++ …` (`MinaStateHashDerive` §1): the 38 whole field elements ride
through the packing UNTOUCHED. They have no declared width, so the chunk gate above cannot reach
them and giving them 254 bit columns apiece would cost 9 652 more booleanity legs. The gate that
FITS a felt is the felt-level one — `AirLeg.limbs`, `SK` base-256 limbs at `bits := 8`, the same
construct `LightClientMinaAir.lowLanesLeg` uses eighteen times for `minaLcVerifyDesc`'s two state
hashes. -/

/-- How many whole field elements a `Protocol_state.Body` preimage carries. -/
def NFIELD : Nat := 38

/-- All the limbs of all the whole field elements. -/
def NFLIMB : Nat := NFIELD * SK

/-- **`FLIMB f k`** — limb `k` of WHOLE field element `f` (`f < 38`), base 256, `k = 0` least
significant. Same encoding as `PLIMB` and as `MinaStateBodyHashChain.bodyAbsorbedBlock`, so the
weld is a slice comparison at both ends of the preimage. -/
def FLIMB (f k : Nat) : Nat := NBITS + NLIMB + SK * f + k

/-- Trace width: the stream's bits, the eleven packed limb blocks, the 38 whole-field limb blocks. -/
def BODY_BITS_WIDTH : Nat := NBITS + NLIMB + NFLIMB

/-- ⚑ PI slot of `FLIMB f k` — slots `[0, 1216)`. **The PI vector is the ABSORB ORDER**: element
`n < 38` is a whole field element and element `38 + e` is a packed one, exactly the order
`packToFields` emits and `MinaStateBodyHashChain.bodyPacked` absorbs, so a seam against a chain
link's absorbed block is a contiguous slice on both sides. -/
def PI_FLIMB (f k : Nat) : Nat := SK * f + k

/-- PI slot of `PLIMB e k` — slots `[1216, 1518)`. ⚠ **MOVED by `+NFLIMB` on 2026-08-09**; the old
base was `0` and a consumer reading it now reads field element 38's limbs. -/
def PI_PLIMB (e k : Nat) : Nat := NFLIMB + limbBase e + k

def BODY_BITS_PI_COUNT : Nat := NFLIMB + NLIMB

/-- ⚑ **THE PI SLOT OF ABSORBED ELEMENT `n`'s LIMB `k`** — one function over the whole
49-element preimage, so the seam's index arithmetic has a single author on this side too. -/
def PI_ABSORBED (n k : Nat) : Nat :=
  if n < NFIELD then PI_FLIMB n k else PI_PLIMB (n - NFIELD) k

/-- How many limbs absorbed element `n` publishes: `SK` for a whole field element, `⌈W_e/8⌉` for a
packed one. ⚠ The DIFFERENCE is the obligation the weld carries as zero-pins. -/
def absorbedLimbCount (n : Nat) : Nat :=
  if n < NFIELD then SK else limbCount (n - NFIELD)

theorem the_layout_is_wellformed :
    BODY_BITS_WIDTH = 3899 ∧ BODY_BITS_PI_COUNT = 1518
      ∧ BIT 0 = 0 ∧ BIT (NBITS - 1) = 2380
      ∧ PLIMB 0 0 = 2381 ∧ PLIMB 10 8 = 2682
      ∧ FLIMB 0 0 = 2683 ∧ FLIMB 37 31 = 3898
      ∧ PLIMB 10 8 < BODY_BITS_WIDTH ∧ FLIMB 37 31 < BODY_BITS_WIDTH
      ∧ PI_PLIMB 10 8 < BODY_BITS_PI_COUNT ∧ PI_FLIMB 37 31 < BODY_BITS_PI_COUNT := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE PI VECTOR IS THE ABSORB ORDER, WITH NO GAP AND NO OVERLAP.** Element `n`'s published
block starts where element `n−1`'s ended, and the 49 blocks exactly fill the 1 518 slots. This is
the theorem the seam's slice arithmetic rests on; without it "a contiguous slice" is a hope. -/
theorem the_pi_vector_is_the_absorb_order :
    PI_ABSORBED 0 0 = 0
      ∧ (∀ n < 49, PI_ABSORBED n 0 + absorbedLimbCount n = PI_ABSORBED (n + 1) 0 ∨ n + 1 = 49)
      ∧ PI_ABSORBED 48 (absorbedLimbCount 48 - 1) + 1 = BODY_BITS_PI_COUNT
      ∧ ((List.range 49).map absorbedLimbCount).foldl (· + ·) 0 = BODY_BITS_PI_COUNT := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  decide

/-! ## §3 — the SOURCE legs. Every one of them is a window gate; not one is a lookup. -/

open WindowExpr (loc)

/-- ⚑ **THE BOOLEANITY LEG** — `x·(x−1) = 0`, `GateExpr.gBool`'s five-node encoding, at `.all` so a
padding row is pinned too. This is the leg that, 2 381 times, discharges
`MinaPackInjective.packing_is_injective`'s range hypothesis. -/
def bitBoolLeg (j : Nat) : AirLeg :=
  .window ⟨RowSel.all, Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gBool (.leaf (.loc (BIT j))))⟩

theorem bitBoolLeg_eq (j : Nat) :
    bitBoolLeg j
      = .window ⟨RowSel.all, .mul (loc (BIT j)) (.add (loc (BIT j)) (.const (-1)))⟩ := rfl

/-- The `(coefficient, bit column)` terms of limb `k` of element `e`: the eight bits of that byte,
skipped where the run has already ended. ⚑ `runStart e + runWidth e - 1 - m` is bit-exponent `m`'s
STREAM index — the run's bits are the element's binary expansion MSB-first. -/
def limbTerms (e k : Nat) : List (Nat × Nat) :=
  (List.range 8).filterMap fun j =>
    if 8 * k + j < runWidth e then
      some (2 ^ j, BIT (runStart e + runWidth e - 1 - (8 * k + j)))
    else none

/-- `Σ cᵢ · BIT colᵢ`, right-folded. -/
def termSum : List (Nat × Nat) → WindowExpr
  | [] => .const 0
  | (c, col) :: rest => .add (.mul (.const (c : ℤ)) (loc col)) (termSum rest)

/-- ⚑ **THE LIMB LEG** — `PLIMB e k − Σ 2^j · BIT(…) = 0`. Affine in the trace: no product of two
columns anywhere, so this descriptor inherits nothing from the Pasta cone
(`bodyBits_products_are_empty`, §3b). -/
def limbLeg (e k : Nat) : AirLeg :=
  .window ⟨RowSel.all, .add (loc (PLIMB e k)) (.mul (.const (-1)) (termSum (limbTerms e k)))⟩

/-- The 302 first-row PI pins of the packed elements. -/
def limbPin (e k : Nat) : AirLeg := .pin ⟨VmRow.first, PLIMB e k, PI_PLIMB e k⟩

/-- All `(e, k)` pairs, in publication order. -/
def limbIdx : List (Nat × Nat) :=
  (List.range NELEM).flatMap fun e => (List.range (limbCount e)).map fun k => (e, k)

/-! ### §3a — ⚑⚑ THE FELT-LEVEL GATE, AND IT IS A `.limbs` LEG. -/

/-- The width-tagged range table this descriptor declares. ⚑ `RANGE_W_TID_BASE = 64` is
`EffectVmEmitV2`'s own family base — the `range_w29`/`range_w22` tables `minaLcVerifyDesc` queries
are `.custom 93` / `.custom 86` in the SAME family, so an 8-bit limb table is `.custom 72` and not a
private numbering. ⚠ `LimbsLeg.mainRailOk` refuses `bits ≥ 30` (a range table at 30+ bits contains
the whole BabyBear field and refuses nothing); 8 is wrap-free by a wide margin. -/
def BODY_LIMB_BITS : Nat := 8

def bodyLimbTid : TableId := .custom (64 + BODY_LIMB_BITS)

def bodyLimbTable : TableDef := ⟨bodyLimbTid, "range_w8", 1, .rangeLimb BODY_LIMB_BITS⟩

/-- The `SK` limb columns of whole field element `f`, LEAST-significant first — the order
`LimbsLeg.cols` is defined in and the order `limbAt` indexes. -/
def fieldCols (f : Nat) : List Nat := (List.range SK).map (fun k => FLIMB f k)

/-- ⚑⚑ **THE FELT-LEVEL GATE** — one `.limbs` leg per whole field element: `SK = 32` base-256 limb
columns, each range-checked at `BODY_LIMB_BITS = 8`. This is what makes a row of this descriptor
denote a value BELOW `2^256` for the half of the preimage that has no declared width, which is
`Seam.Renders`' canonicality hypothesis and therefore the reason an elementwise 32-limb weld carries
the whole element with no digest and no birthday bound (`Seam.limb_inj`). -/
def fieldLimbsLeg (f : Nat) : AirLeg :=
  .limbs { cols := fieldCols f, bits := BODY_LIMB_BITS, table := bodyLimbTid }

/-- The 1 216 first-row PI pins of the whole field elements. -/
def fieldPin (f k : Nat) : AirLeg := .pin ⟨VmRow.first, FLIMB f k, PI_FLIMB f k⟩

/-- All `(f, k)` pairs, in publication order. -/
def fieldIdx : List (Nat × Nat) :=
  (List.range NFIELD).flatMap fun f => (List.range SK).map fun k => (f, k)

theorem fieldIdx_length : fieldIdx.length = 1216 := by rfl

/-- ⚑ **THE GATE IS THE `.limbs` LEG AND IT IS THE ONE THE MAIN RAIL ADMITS.** Decided on the leg,
not described: 32 columns, 8 bits, the declared table, and `mainRailOk`. -/
theorem the_field_gate_is_a_limbs_leg (f : Nat) :
    fieldLimbsLeg f = .limbs ⟨(List.range SK).map (fun k => FLIMB f k), 8, bodyLimbTid⟩
      ∧ (fieldLimbsLeg f).mainRailOk = true
      ∧ (LimbsLeg.lookupCount ⟨fieldCols f, BODY_LIMB_BITS, bodyLimbTid⟩) = 32
      ∧ (LimbsLeg.capacityBits ⟨fieldCols f, BODY_LIMB_BITS, bodyLimbTid⟩) = 256 := by
  -- ⚑ TWO unfolds were missing, and the pair is why this read as a hard goal.
  -- (1) `AirLeg.mainRailOk`, not `LimbsLeg.mainRailOk` — the original simp set carried the
  --     inner one, but the goal is the OUTER dispatch `| .limbs l => l.mainRailOk`, so it
  --     never reached the leg at all.
  -- (2) `SK`, so `(List.range SK).map` is visibly non-nil for `!cols.isEmpty`.
  -- The content is `!cols.isEmpty && 0 < bits && bits ≤ 29` at 32 columns and 8 bits —
  -- trivially true. With either unfold missing it survives as a bare `.mainRailOk = true`,
  -- which READS LIKE A MISSING LEMMA rather than a missing unfold. That presentation is
  -- how it reached HEAD carrying unsolved goals and an axiom-hygiene FAIL.
  refine ⟨rfl, ?_, ?_, ?_⟩ <;>
    simp [fieldLimbsLeg, fieldCols, AirLeg.mainRailOk, LimbsLeg.mainRailOk,
      LimbsLeg.lookupCount, LimbsLeg.capacityBits, BODY_LIMB_BITS, PastaFieldSound.SK]

/-- ⚑⚑ **NO PUBLISHED COLUMN IS INERT.** Every limb slot this descriptor publishes has at least one
bit under it, so its gate names TWO columns and the emitted `pi_binding`'s column is in a component
larger than itself. This is `LightClientAnchorConnectivity.decorativeAnchors = []` decided on the
SOURCE, before any byte — and it is why the limb allocation is `⌈W_e/8⌉`. -/
theorem no_published_limb_is_inert : ∀ p ∈ limbIdx, limbTerms p.1 p.2 ≠ [] := by decide

/-- ⚑ **THE SOURCE.** 38 felt-level `.limbs` legs, 302 packed-limb legs, 2 381 booleanity legs, then
the 1 216 + 302 pins.

⚠ The ORDER is not cosmetic: `EffectAir.pinsTied` resolves each pin by scanning the leg list from
the front, so putting the two DERIVING families first is what keeps the tie verdict a kernel
`decide` instead of a scan behind 2 381 booleanity legs. -/
def bodyBitsAir : EffectAir :=
  { tables := [bodyLimbTable]
  , legs :=
      ((List.range NFIELD).map fieldLimbsLeg)
        ++ (limbIdx.map fun p => limbLeg p.1 p.2)
        ++ ((List.range NBITS).map bitBoolLeg)
        ++ (fieldIdx.map fun p => fieldPin p.1 p.2)
        ++ (limbIdx.map fun p => limbPin p.1 p.2) }

-- Counts over the concrete 4 239-leg list and the emitted descriptor are checked by compiled
-- evaluation (`native_decide`, pinned `#assert_compiled`). `mainRailOk` stays a kernel check because
-- the `TiedAir` certificate below is built from it.
theorem bodyBitsAir_leg_count : bodyBitsAir.legs.length = 4239 := by native_decide

theorem bodyBitsAir_mainRailOk : bodyBitsAir.mainRailOk = true := by decide +kernel

theorem bodyBitsAir_pinsFit : bodyBitsAir.pinsFit BODY_BITS_PI_COUNT = true := by native_decide

/-- ⚑⚑ **THE WHOLE LOOKUP BILL IS THE FELT GATE, AND NOTHING ELSE MOVED.** Decided on the source:
the 819 chunks still cost ZERO range lookups (a booleanity assertion is a degree-2 window gate, not
a bus query), and every one of the 1 216 lookups this descriptor now issues belongs to the 38
`.limbs` legs — `38 × SK`. ⚠ So the 2026-08-08 headline "committed width = declared width, 1.00×"
is RETIRED by this rung and replaced by a bill with one line item, said rather than absorbed. -/
theorem the_field_gates_are_the_whole_lookup_bill :
    bodyBitsAir.limbsCount = NFIELD
      ∧ bodyBitsAir.totalRangeLookups = NFIELD * SK
      ∧ bodyBitsAir.totalRangeLookups = 1216
      ∧ bodyBitsAir.ranges = []
      ∧ bodyBitsAir.tables = [bodyLimbTable]
      ∧ bodyBitsAir.maxLimbedCapacityBits = SK * SB := by
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩ <;> native_decide

/-- ⚑⚑ **THE TIE VERDICT, BY EXHIBITING THE READER — not by scanning for one.**

`EffectAir.pinsTied` is `O(pins × legs)`, and this is the widest block in the tree: **1 518 pins
over 4 239 legs**. Until 2026-11-06 it was closed by `decide`, which ran that scan inside the
elaborator's `whnf`: 213 s, and the reason this module peaked at 25.9 GB (measured on dregg-build2,
`metatheory/docs/MINA-PICKLES-RESCUE.md`).

The proof below never scans the leg list. Every pin's reader is known by construction: a field pin
publishes `FLIMB f k`, and `fieldLimbsLeg f` (the `.limbs` leg whose `cols` IS `fieldCols f`) reads
it; a limb pin publishes `PLIMB e k`, and `limbLeg e k` reads it as the `loc` leaf of its own
composition gate. The three deriving families contain no `pin` leg at all. Membership of each reader
in `bodyBitsAir.legs` comes from the index lists, so the argument is about `f < NFIELD`, `k < SK`
and `(e, k) ∈ limbIdx`, not about 4 239 concrete legs. -/
theorem bodyBitsAir_pinsTied : bodyBitsAir.pinsTied = true := by
  unfold EffectAir.pinsTied
  refine List.all_eq_true.mpr fun l hl => ?_
  cases l with
  | pin p =>
    -- the pin is a field pin or a limb pin; the three deriving families carry no `pin` leg
    simp only [bodyBitsAir, List.mem_append, List.mem_map] at hl
    rcases hl with (((⟨f, -, h⟩ | ⟨q, -, h⟩) | ⟨j, -, h⟩) | ⟨q, hq, h⟩) | ⟨q, hq, h⟩
    · simp [fieldLimbsLeg] at h
    · simp [limbLeg] at h
    · simp [bitBoolLeg] at h
    · -- a field pin: its reader is `fieldLimbsLeg q.1`, whose `cols` IS `fieldCols q.1`
      simp only [fieldPin, AirLeg.pin.injEq] at h
      subst h
      obtain ⟨f, hf, k, hk, rfl⟩ : ∃ f, f < NFIELD ∧ ∃ k, k < SK ∧ q = (f, k) := by
        simpa [fieldIdx, List.mem_flatMap, List.mem_map, List.mem_range, eq_comm] using hq
      refine List.any_eq_true.mpr ⟨fieldLimbsLeg f, ?_, ?_⟩
      · simp only [bodyBitsAir, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, hf, rfl⟩)))
      · simp only [fieldLimbsLeg, AirLeg.readCols, fieldCols, decide_eq_true_eq]
        exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
    · -- a limb pin: its reader is `limbLeg q.1 q.2`, whose body's first leaf is `loc (PLIMB …)`
      simp only [limbPin, AirLeg.pin.injEq] at h
      subst h
      refine List.any_eq_true.mpr ⟨limbLeg q.1 q.2, ?_, ?_⟩
      · simp only [bodyBitsAir, List.mem_append, List.mem_map]
        exact Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩)))
      · simp [limbLeg, AirLeg.readCols, Dregg2.Circuit.EffectAirIR.windowCols]
  | gate _ => rfl
  | lookup _ => rfl
  | window _ => rfl
  | limbs _ => rfl
  | chal _ => rfl
  | bind _ => rfl

/-- ⚑ **THE TIED SOURCE** — every published column is derived by another leg, carried in the type.
Both verdicts are SUPPLIED: `mainRailOk` by `rfl` fifteen lines above, `pinsTied` by the
witness-exhibiting proof above. Left blank, the two `autoParam`s re-derive both over 4 239 legs. -/
def bodyBitsTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := bodyBitsAir
  ok   := bodyBitsAir_mainRailOk
  tied := bodyBitsAir_pinsTied

/-- **`bodyBitsDesc` — COMPILER OUTPUT.** -/
def bodyBitsDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-body-preimage-bits::v1" BODY_BITS_WIDTH BODY_BITS_PI_COUNT [] bodyBitsTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — stated in the SOURCE's vocabulary
and never mentioning the lowering, so it is not `P → P`. -/
theorem bodyBitsDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines bodyBitsDesc [] bodyBitsAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-body-preimage-bits::v1" BODY_BITS_WIDTH BODY_BITS_PI_COUNT [] bodyBitsTiedAir).property

theorem bodyBitsDesc_name : bodyBitsDesc.name = "dregg-mina-body-preimage-bits::v1" := rfl
theorem bodyBitsDesc_width : bodyBitsDesc.traceWidth = 3899 := rfl
theorem bodyBitsDesc_piCount : bodyBitsDesc.piCount = 1518 := rfl
theorem bodyBitsDesc_tables : bodyBitsDesc.tables = [bodyLimbTable] := rfl
theorem bodyBitsDesc_ranges : bodyBitsDesc.ranges = [] := rfl
theorem bodyBitsDesc_hashSites : bodyBitsDesc.hashSites = [] := rfl
theorem bodyBitsDesc_constraint_count : bodyBitsDesc.constraints.length = 5417 := by
  native_decide

/-- ⚑⚑ **THE COMMITTED WIDTH IS NO LONGER THE DECLARED WIDTH, AND HERE IS THE BILL.**
`MainLayout::build` appends `decomp_cols(bits)` columns per RANGE lookup and `2 · SUBMASK_BITS` per
submask lookup. The 2026-08-08 shape emitted neither and this file's headline was *"2 683 declared,
2 683 committed, 1.00×"*. ⚠ **That headline is RETIRED by this rung**: binding the 38 whole field
elements costs `NFIELD × SK = 1 216` eight-bit range lookups, and that is the ENTIRE lookup bill —
the 819 chunks still cost zero, because a booleanity assertion is a degree-2 window gate and not a
bus query.

Decided on the compiler's OUTPUT rather than described: the number of emitted `lookup` constraints
is exactly `NFIELD * SK`, so nothing else acquired a bus query while the felt gate landed. -/
theorem the_lookup_bill_is_exactly_the_field_gate :
    (bodyBitsDesc.constraints.filter fun c =>
      match c with | .lookup _ => true | _ => false).length = NFIELD * SK
    ∧ bodyBitsDesc.tables = [bodyLimbTable]
    ∧ bodyBitsDesc.traceWidth = 3899 := by
  refine ⟨?_, rfl, rfl⟩
  native_decide

/-! ### §3b — decided on the emitted bytes. -/

/-- Does this body read a trace cell? -/
def readsCell : WindowExpr → Bool
  | .loc _ => true
  | .nxt _ => true
  | .const _ => false
  | .add a b => readsCell a || readsCell b
  | .mul a b => readsCell a || readsCell b

def cellCols : WindowExpr → List Nat
  | .loc c => [c]
  | .nxt c => [c]
  | .const _ => []
  | .add a b => cellCols a ++ cellCols b
  | .mul a b => cellCols a ++ cellCols b

/-- Columns under a product of two cell-reading factors — the limb-product signature. -/
def prodCols : WindowExpr → List Nat
  | .loc _ => []
  | .nxt _ => []
  | .const _ => []
  | .add a b => prodCols a ++ prodCols b
  | .mul a b =>
      (if readsCell a && readsCell b then cellCols a ++ cellCols b else []) ++
        prodCols a ++ prodCols b

def constraintProdCols : VmConstraint2 → List Nat
  | .windowGate w => prodCols w.body
  | _ => []

/-- ⚑ **EVERY TWO-SIDED PRODUCT IS A BOOLEANITY PIN ON ONE COLUMN.** The limb legs are affine, so
the only columns under a product are the bit columns squaring themselves. A non-native Pasta
multiply would put two DIFFERENT indices in one gate; none does. -/
theorem bodyBits_products_are_only_the_bits :
    (bodyBitsDesc.constraints.all fun c =>
      (constraintProdCols c).eraseDups.length ≤ 1) = true := by native_decide

/-! ## §4 — ⚑ THE ROW PREDICATE, AND IT IS THE THREE LEG FAMILIES. -/

/-- The value limb `(e, k)`'s gate says the limb is, at a row. -/
def limbValueOf (row : Nat → ℤ) (e k : Nat) : ℤ :=
  (limbTerms e k).foldr (fun t acc => (t.1 : ℤ) * row t.2 + acc) 0

/-- ⚑ **`bodyBitsRowOk` — the emitted constraint set's content, as a verdict.** FIVE conjuncts, one
per leg family: booleanity on every bit column, each packed limb the exact byte its bits compose,
every packed limb published, ⚑ **every WHOLE-FIELD limb inside the declared 8-bit range table** (the
`.limbs` leg — `0 ≤ x < 2^8` is what a `rangeLimb 8` row set says of a queried value), and every
whole-field limb published. -/
def bodyBitsRowOk (row pub : Nat → ℤ) : Prop :=
  (∀ j < NBITS, row (BIT j) * (row (BIT j) - 1) = 0)
  ∧ (∀ p ∈ limbIdx, row (PLIMB p.1 p.2) = limbValueOf row p.1 p.2)
  ∧ (∀ p ∈ limbIdx, pub (PI_PLIMB p.1 p.2) = row (PLIMB p.1 p.2))
  ∧ (∀ p ∈ fieldIdx, 0 ≤ row (FLIMB p.1 p.2) ∧ row (FLIMB p.1 p.2) < 2 ^ BODY_LIMB_BITS)
  ∧ (∀ p ∈ fieldIdx, pub (PI_FLIMB p.1 p.2) = row (FLIMB p.1 p.2))

/-- ⚑⚑⚑ **THE FELT GATE FORCES `Renders`' CANONICALITY HYPOTHESIS.** A row this descriptor accepts
publishes, for every whole field element, `SK` limbs each inside `[0, 2^SB)` — so the value those
limbs denote is below `2^(SB·SK)`, which is precisely `Seam.Renders`' bound and precisely what
`Seam.limb_inj` needs to make an elementwise 32-limb weld carry a whole value with no digest.

⚠ Said as the arithmetic it is rather than as a slogan: **without this leg the published limbs are
arbitrary BabyBear residues**, `Seam.Renders` is not inhabited at them, and the weld the next file
builds would transport nothing. This is the hypothesis, discharged. -/
theorem the_field_gate_bounds_every_whole_element_limb {row pub : Nat → ℤ}
    (h : bodyBitsRowOk row pub) :
    ∀ f < NFIELD, ∀ k < SK, 0 ≤ pub (PI_FLIMB f k) ∧ pub (PI_FLIMB f k) < 2 ^ SB := by
  intro f hf k hk
  have hmem : (f, k) ∈ fieldIdx :=
    List.mem_flatMap.mpr ⟨f, List.mem_range.mpr hf,
      List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩
  have hpub := h.2.2.2.2 (f, k) hmem
  have hrng := h.2.2.2.1 (f, k) hmem
  have hSB : (2 : ℤ) ^ SB = 2 ^ BODY_LIMB_BITS := by norm_num [SB, BODY_LIMB_BITS]
  rw [hpub, hSB]
  exact hrng

/-- ⚑⚑⚑ **THE ROW PREDICATE FORCES THE RANGE HYPOTHESIS.** A row this descriptor accepts denotes a
BOOLEAN bit vector, so every chunk read off it as a bit slice is below its declared width, so
`MinaPackInjective.packing_is_injective` applies to the stream this row denotes. This is the
theorem that makes the gate and the arithmetic one object rather than two files that agree. -/
theorem the_row_gates_force_boolean_bits {row pub : Nat → ℤ} (h : bodyBitsRowOk row pub) :
    ∀ j < NBITS, row (BIT j) = 0 ∨ row (BIT j) = 1 := by
  intro j hj
  have := h.1 j hj
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-! ## §5 — ⚑ THE REAL BLOCK'S WITNESS, AND BOTH POLARITIES.

⚠ Every theorem below is about the REAL devnet block (540221) rather than a hand-built row: the bit
stream is `bodyInput.packeds` expanded MSB-first, and `the_real_slices_are_the_real_chunks` is the
statement that the expansion is the block's own chunk stream and not a re-transcription. -/

/-- The per-chunk bit slices of the real block, MSB-first within each chunk. -/
def realSlices : List (List Nat) :=
  Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.packeds.map fun p =>
    (List.range p.2).map fun t => (p.1 >>> (p.2 - 1 - t)) &&& 1

/-- The flattened 2 381-bit stream — column `j` of the honest row. -/
def realBits : List Nat := realSlices.flatten

/-- ⚑⚑ **THE SLICES ARE THE BLOCK'S OWN CHUNKS.** Re-reading the bit slices as
`(bitsToNat, length)` pairs reproduces `bodyInput.packeds` exactly — so the object this descriptor
gates IS the chunk stream `packToFields` consumes, not a parallel encoding of it. ⚠ Without this the
whole rung is a theorem about the wrong object. -/
theorem the_real_slices_are_the_real_chunks :
    chunksOfSlices realSlices = Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.packeds := by
  native_decide

/-- …and the stream really is 2 381 bits, all boolean. -/
theorem the_real_bits_are_boolean_and_count :
    realBits.length = NBITS ∧ realBits.all (fun b => b == 0 || b == 1) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- ⚑ **AND THE HIGH LIMBS OF EVERY PACKED ELEMENT ARE ZERO** — element `38+e` is below `2^(W_e)`,
so its base-256 digits above `⌈W_e/8⌉` are all zero. ⚠ This is the obligation the `⌈W_e/8⌉` limb
allocation MOVES rather than removes: the chain's absorbed block is 32 limbs an element, so a weld
connects these `⌈W_e/8⌉` and must pin the remaining `32 − ⌈W_e/8⌉` chain-side limbs to ZERO. Stated
here so the weld has a target that is checkable rather than assumed. -/
theorem the_high_limbs_of_the_real_elements_are_zero :
    ∀ e < NELEM,
      (packToFields Dregg2.Bridge.MinaStateHashPackPrice.bodyInput).getD (38 + e) 0
        < 2 ^ runWidth e := by
  have h : ((List.range NELEM).all fun e => decide
      ((packToFields Dregg2.Bridge.MinaStateHashPackPrice.bodyInput).getD (38 + e) 0
        < 2 ^ runWidth e)) = true := by native_decide
  intro e he
  have := List.all_eq_true.mp h e (List.mem_range.mpr he)
  simpa using this

/-- ⚑ **THE 38 WHOLE FIELD ELEMENTS OF THE REAL BLOCK** — `bodyInput.fields`, the list
`packToFields` prepends untouched and `MinaStateBodyHashChain.bodyPacked` absorbs as elements 0..37.
Not re-transcribed: the same object the price file measured. -/
def realFields : List Nat := Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.fields

/-- ⚑ **AND THEY ARE 38, AND EVERY ONE IS BELOW `2^(SB·SK)`** — so `Seam.Renders` is inhabited at
the honest claim and the felt gate is satisfiable rather than merely stated. -/
theorem the_real_field_block_is_thirty_eight_canonical_elements :
    realFields.length = NFIELD
      ∧ realFields.all (fun v => decide (v < 2 ^ (SB * SK))) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- The honest row: the stream bits, the eleven packed elements' limbs as their gates compute them,
then the 38 whole field elements' base-256 limbs. -/
def realRow : Nat → ℤ := fun c =>
  if c < NBITS then (realBits.getD c 0 : ℤ)
  else if c < NBITS + NLIMB then
    let i := c - NBITS
    let e := (List.range NELEM).findIdx (fun e => i < limbBase e + limbCount e)
    let k := i - limbBase e
    if e < NELEM then
      ((limbTerms e k).foldr (fun t acc => (t.1 : ℤ) * (realBits.getD t.2 0 : ℤ) + acc) 0)
    else 0
  else if c < BODY_BITS_WIDTH then
    let i := c - (NBITS + NLIMB)
    limbAt (realFields.getD (i / SK) 0) (i % SK)
  else 0

/-- The honest claim: the PI vector in ABSORB order — 38 whole-field limb blocks, then eleven packed
ones. Each slot is its column, by construction rather than by coincidence
(`the_honest_claim_is_the_honest_row`). -/
def realPub : Nat → ℤ := fun s =>
  if s < NFLIMB then realRow (NBITS + NLIMB + s)
  else if s < BODY_BITS_PI_COUNT then realRow (NBITS + (s - NFLIMB))
  else 0

/-- ⚑⚑ **THE HONEST ROW IS ACCEPTED.** The real block's own preimage — both halves — gated. -/
theorem the_real_preimage_row_is_accepted : bodyBitsRowOk realRow realPub := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : ((List.range NBITS).all fun j =>
        decide (realRow (BIT j) * (realRow (BIT j) - 1) = 0)) = true := by native_decide
    intro j hj
    have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    simpa using this
  · have h : (limbIdx.all fun p =>
        decide (realRow (PLIMB p.1 p.2) = limbValueOf realRow p.1 p.2)) = true := by native_decide
    intro p hp
    have := List.all_eq_true.mp h p hp
    simpa using this
  · have h : (limbIdx.all fun p =>
        decide (realPub (PI_PLIMB p.1 p.2) = realRow (PLIMB p.1 p.2))) = true := by native_decide
    intro p hp
    have := List.all_eq_true.mp h p hp
    simpa using this
  · have h : (fieldIdx.all fun p =>
        decide (0 ≤ realRow (FLIMB p.1 p.2)
          ∧ realRow (FLIMB p.1 p.2) < 2 ^ BODY_LIMB_BITS)) = true := by native_decide
    intro p hp
    have := List.all_eq_true.mp h p hp
    simpa using this
  · have h : (fieldIdx.all fun p =>
        decide (realPub (PI_FLIMB p.1 p.2) = realRow (FLIMB p.1 p.2))) = true := by native_decide
    intro p hp
    have := List.all_eq_true.mp h p hp
    simpa using this

/-- ⚑⚑ **AND THE HONEST CLAIM RENDERS THE BLOCK'S OWN FIELD ELEMENTS** — the published limb block of
whole field element `f` IS `limbAt (realFields[f])`, so the seam's left end carries the value and
not a re-encoding of it. This is the `Seam.Renders` premise, at the real block. -/
theorem the_honest_claim_renders_the_whole_field_elements :
    (fieldIdx.all fun p =>
      decide (realPub (PI_FLIMB p.1 p.2) = limbAt (realFields.getD p.1 0) p.2)) = true := by
  native_decide

/-- ⚑ **THE FALSIFIER'S TARGET.** Bit column 23 is the FIRST `1` in the real block's chunk stream —
the first twenty-three bits are the low bits of `Non_snark.digest`'s first bytes and are zero. ⚠ A
control aimed at one of those would move a zero into something, which is how a sibling lane's first
falsifier died; this one moves a value that is there. -/
def FALSIFIER_BIT : Nat := 23

/-- The forged row: bit 23 carries `2` while declaring ONE bit — an over-wide chunk, and exactly
the left half of `MinaPackInjective.the_range_hypothesis_is_load_bearing`. -/
def forgedBitRow : Nat → ℤ := fun c => if c = BIT FALSIFIER_BIT then 2 else realRow c

/-- The forged row whose published limb is not what its bits compose. -/
def forgedLimbRow : Nat → ℤ := fun c => if c = PLIMB 0 0 then realRow c + 1 else realRow c

/-- ⚑ **THE FELT-GATE FORGERY: A WHOLE FIELD ELEMENT'S LIMB ABOVE ITS DECLARED WIDTH.** `256` is
outside `range_w8`'s row set, so it is refused by the `.limbs` leg's own bus query — and it differs
from EVERY honest value the gate admits, so this control cannot degenerate into a no-op the way a
`replacen` that no longer matches did (`minted-a-falsifier-that-stopped-falsifying`). ⚠ The forgery
matters because an unbounded limb is exactly what breaks `Seam.Renders`: a prover who may write
`2^8` into one limb column can render TWO values with one limb vector once the weld transports it. -/
def forgedFieldRow : Nat → ℤ := fun c => if c = FLIMB 0 0 then 2 ^ BODY_LIMB_BITS else realRow c

/-- A forged CLAIM: the published slot of whole field element 0's low limb is not the column it
pins. Refused by the pin conjunct, which is what keeps the felt gate from bounding a column the
claim does not carry. -/
def forgedFieldPub : Nat → ℤ := fun s => if s = PI_FLIMB 0 0 then realPub s + 1 else realPub s

/-- ⚑ **THE FALSIFIERS FALSIFY.** Both targets carry a NON-ZERO honest value and both mutations
MOVE it — checked, not assumed. -/
theorem the_falsifier_targets_are_non_zero_and_move :
    realRow (BIT FALSIFIER_BIT) = 1
      ∧ forgedBitRow (BIT FALSIFIER_BIT) = 2
      ∧ realRow (PLIMB 0 0) ≠ 0
      ∧ forgedLimbRow (PLIMB 0 0) ≠ realRow (PLIMB 0 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑⚑ **THE FORGERY THE OLD SHAPE WAVED THROUGH: A CHUNK ABOVE ITS DECLARED WIDTH.** A one-bit
chunk carrying `2`. The booleanity gate refuses it, and the refusal is the AIR's: no lookup, no
table, no producer pre-flight — one degree-2 gate. -/
theorem an_over_wide_chunk_bit_is_refused : ¬ bodyBitsRowOk forgedBitRow realPub := by
  intro h
  have hbad : ¬ (forgedBitRow (BIT FALSIFIER_BIT) * (forgedBitRow (BIT FALSIFIER_BIT) - 1) = 0) := by
    native_decide
  exact hbad (h.1 FALSIFIER_BIT (by decide))

/-- ⚑ **AND A LIMB THAT IS NOT ITS BITS IS REFUSED.** Move the published limb `PLIMB 0 0` by one and
leave every bit alone: the composition gate refuses, so a prover cannot publish an element the bits
do not compose. ⚠ This is the half that keeps the booleanity from being a gate on columns nobody
reads. -/
theorem a_limb_that_is_not_its_bits_is_refused : ¬ bodyBitsRowOk forgedLimbRow realPub := by
  intro h
  have hmem : ((0 : Nat), (0 : Nat)) ∈ limbIdx := by decide
  have hbad : forgedLimbRow (PLIMB 0 0) ≠ limbValueOf forgedLimbRow 0 0 := by native_decide
  exact hbad (h.2.1 (0, 0) hmem)

/-- ⚑ **THE FELT FALSIFIER FALSIFIES, AND IT CANNOT DEGENERATE.** Every honest whole-field limb is
inside `[0, 2^8)` and the forgery is `2^8` — so the mutation MOVES the value at every possible
honest witness, not merely at this block's. Checked, not assumed. -/
theorem the_field_falsifier_moves_a_value_the_gate_admits :
    (fieldIdx.all fun p =>
      decide (0 ≤ realRow (FLIMB p.1 p.2)
        ∧ realRow (FLIMB p.1 p.2) < 2 ^ BODY_LIMB_BITS)) = true
    ∧ forgedFieldRow (FLIMB 0 0) = 2 ^ BODY_LIMB_BITS
    ∧ forgedFieldRow (FLIMB 0 0) ≠ realRow (FLIMB 0 0)
    ∧ forgedFieldPub (PI_FLIMB 0 0) ≠ realPub (PI_FLIMB 0 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑⚑ **AND A WHOLE FIELD ELEMENT'S LIMB ABOVE ITS DECLARED WIDTH IS REFUSED.** The refusal is the
`.limbs` leg's — a bus query against the `range_w8` table this descriptor DECLARES, not a producer
pre-flight. This is the half that binds the 38 elements the 2026-08-08 shape had no column for. -/
theorem an_over_wide_field_limb_is_refused : ¬ bodyBitsRowOk forgedFieldRow realPub := by
  intro h
  have hmem : ((0 : Nat), (0 : Nat)) ∈ fieldIdx := by decide
  have hbad : ¬ (0 ≤ forgedFieldRow (FLIMB 0 0)
      ∧ forgedFieldRow (FLIMB 0 0) < 2 ^ BODY_LIMB_BITS) := by native_decide
  exact hbad (h.2.2.2.1 (0, 0) hmem)

/-- ⚑ **AND A CLAIM THAT DOES NOT PUBLISH ITS OWN COLUMN IS REFUSED** — the pin conjunct, on the
whole-field half. Without it the felt gate would bound columns the seam never reads. -/
theorem a_field_claim_that_is_not_its_column_is_refused :
    ¬ bodyBitsRowOk realRow forgedFieldPub := by
  intro h
  have hmem : ((0 : Nat), (0 : Nat)) ∈ fieldIdx := by decide
  have hbad : forgedFieldPub (PI_FLIMB 0 0) ≠ realRow (FLIMB 0 0) := by native_decide
  exact hbad (h.2.2.2.2 (0, 0) hmem)

/-- ⚑ **BOTH POLARITIES, AS ONE STATEMENT — now over BOTH HALVES of the preimage.** -/
theorem body_bits_discriminates :
    bodyBitsRowOk realRow realPub
      ∧ ¬ bodyBitsRowOk forgedBitRow realPub
      ∧ ¬ bodyBitsRowOk forgedLimbRow realPub
      ∧ ¬ bodyBitsRowOk forgedFieldRow realPub
      ∧ ¬ bodyBitsRowOk realRow forgedFieldPub :=
  ⟨the_real_preimage_row_is_accepted, an_over_wide_chunk_bit_is_refused,
   a_limb_that_is_not_its_bits_is_refused, an_over_wide_field_limb_is_refused,
   a_field_claim_that_is_not_its_column_is_refused⟩

/-! ## §6 — ⚑⚑⚑ THE CONCLUSION, IN THE UNITS THE CAMPAIGN USES. -/

/-- ⚑⚑⚑ **WHAT THE GATE BUYS: THE 819 CHUNKS ARE DETERMINED BY THE ELEVEN PACKED ELEMENTS.**
`MinaPackInjective.the_gated_bits_are_determined_by_the_packing` at THIS block's slicing: two rows
this descriptor accepts, sliced by the SAME schedule, whose packings agree, denote the same 819
chunk values. So the eleven packed field elements the body-hash chain absorbs pin all 2 381 bits.

⚠ **AND THE 38 FIELD ELEMENTS ARE NOT IN THIS STATEMENT, DELIBERATELY.** `fields` is a parameter
that rides through untouched on both sides, because injectivity of the PACKING is a statement about
the chunk half alone. What binds the field half is a different object and a different kind of
statement: the felt gate (`the_field_gate_bounds_every_whole_element_limb`) plus the weld
(`MinaBodyPreimageSeams`), not `packing_is_injective`. Conflating the two is how "the packing is
injective" would come to sound like "the preimage is determined". -/
theorem the_eleven_packed_elements_pin_the_2381_bits (fields : List Nat)
    (sa sb : List (List Nat))
    (hsched : sa.map List.length = sb.map List.length)
    (hba : ∀ s ∈ sa, ∀ b ∈ s, b ≤ 1) (hbb : ∀ s ∈ sb, ∀ b ∈ s, b ≤ 1)
    (hpa : ∀ s ∈ sa, 0 < s.length) (hpb : ∀ s ∈ sb, 0 < s.length)
    (h : packToFields ⟨fields, chunksOfSlices sa⟩ = packToFields ⟨fields, chunksOfSlices sb⟩) :
    chunksOfSlices sa = chunksOfSlices sb :=
  the_gated_bits_are_determined_by_the_packing fields sa sb hsched hba hbb hpa hpb h

/-- …and the real block's slicing satisfies every hypothesis of it, so the conclusion is about the
object the chain absorbs and not about an empty premise. -/
theorem the_real_slicing_satisfies_the_hypotheses :
    (∀ s ∈ realSlices, ∀ b ∈ s, b ≤ 1) ∧ (∀ s ∈ realSlices, 0 < s.length) := by
  constructor
  · have h : (realSlices.all fun s => s.all fun b => decide (b ≤ 1)) = true := by native_decide
    intro s hs b hb
    have hs' := List.all_eq_true.mp h s hs
    have := List.all_eq_true.mp hs' b hb
    simpa using this
  · have h : (realSlices.all fun s => decide (0 < s.length)) = true := by native_decide
    intro s hs
    have := List.all_eq_true.mp h s hs
    simpa using this

/-! ## §7 — ⚠ RESIDUALS, NAMED — AND TWO OF THE FOUR CLOSED ON 2026-08-09.

1. ✅ **THE WELD IS HERE.** `MinaBodyPreimageSeams.bodyPreimageSeam j` connects these 1 518 slots to
   the twenty-five links' absorbed blocks, elementwise, with the high limbs zero-pinned; S2 is a
   named theorem and `body_preimage_seam_S2_needs_the_seam` proves the seam-dropped form FALSE.
   ⚠ It is a `SeamSpec` a fold READS (`seam.rs::apply_seam`), so it is recursion wiring with a
   theorem attached — not an in-descriptor constraint, and it inherits the FRI floor like every
   other seam in this cone.
2. ✅ **THE 38 WHOLE FIELD ELEMENTS.** Gated, `fieldLimbsLeg`, 1 216 range lookups.
3. ⚠ **NOTHING SAYS A BODY IS REAL.** That is `PICKLES_OPENING_WITNESSED`, unchanged — and it is
   now the ONLY thing between "a 49-element stream this descriptor gates and that chain absorbs"
   and "a `Protocol_state.Body`". ⚑ **What a prover still chooses is stated in §7a.**
4. ⚠ **THE RECURSION BOUNDARY.** That a verifying STARK implies its statement is the FRI obligation
   this whole stack carries. This rung stands at exactly that resolution.

## §7a — ⚑⚑⚑ WHAT A PROVER STILL CHOOSES, IN THE ONLY HONEST FORM: THE CHOICE MOVED TWICE AND HAS
NOT DISAPPEARED.

  * 2026-08-07 moved it from **`BODYHASH` — one felt** to **its 49-element preimage.**
  * 2026-08-08 moved it from "any 49 elements" to "any 49 elements whose last eleven are the packing
    of 819 chunks of the declared widths" — the chunk half.
  * 2026-08-09 (this rung) removes the freedom to make the published limbs *disagree with the
    chain's absorbed stream*, and bounds the whole-field half to `2^256`.

⚠ **WHAT REMAINS IS NOT SMALL AND IS NOT AN ENCODING QUESTION.** A prover still chooses **the 2 381
bits and the 38 field elements themselves** — i.e. the whole `Protocol_state.Body` — subject only to
its SHAPE (819 chunks at the type's fixed widths, 38 canonical felts) and to the requirement that
the same body run through the chain. Nothing here says the epoch ledger hash is an epoch ledger
hash, that the VRF output verifies, or that the global slot is consistent. **Every one of the 857
pieces is a consensus-rule obligation of the Mina daemon, and this circuit constrains their SHAPE
and their AGREEMENT, not their CONTENT.** The one object that would speak to content is
`PICKLES_OPENING_WITNESSED`, which is a witness carrier, not a check.
-/

#assert_axioms the_runs_partition_the_stream
#assert_axioms the_limb_allocation_is_the_run_widths
#assert_axioms the_layout_is_wellformed
#assert_axioms the_pi_vector_is_the_absorb_order
#assert_axioms no_published_limb_is_inert
#assert_axioms bitBoolLeg_eq
#assert_axioms the_field_gate_is_a_limbs_leg
#assert_axioms fieldIdx_length
#assert_compiled bodyBitsAir_leg_count
#assert_axioms bodyBitsAir_mainRailOk
#assert_compiled bodyBitsAir_pinsFit
#assert_compiled the_field_gates_are_the_whole_lookup_bill
#assert_axioms bodyBitsDesc_name
#assert_axioms bodyBitsDesc_width
#assert_axioms bodyBitsDesc_piCount
#assert_axioms bodyBitsDesc_tables
#assert_compiled bodyBitsDesc_constraint_count
#assert_compiled the_lookup_bill_is_exactly_the_field_gate
#assert_axioms the_field_gate_bounds_every_whole_element_limb
#assert_compiled bodyBits_products_are_only_the_bits
#assert_axioms the_row_gates_force_boolean_bits
#assert_axioms the_eleven_packed_elements_pin_the_2381_bits

-- ⚑ COMPILER-TRUSTED, and said out loud: each reduces the 1 544-byte binprot parse, a two-block
-- SHA-256 and the 819-chunk assembly, or evaluates 3 085 gates at the real block's row.
#assert_compiled the_run_schedule_is_the_real_blocks_packing
#assert_compiled the_real_slices_are_the_real_chunks
#assert_compiled the_high_limbs_of_the_real_elements_are_zero
#assert_compiled the_real_bits_are_boolean_and_count
#assert_compiled the_real_preimage_row_is_accepted
#assert_compiled the_falsifier_targets_are_non_zero_and_move
#assert_compiled an_over_wide_chunk_bit_is_refused
#assert_compiled a_limb_that_is_not_its_bits_is_refused
#assert_compiled the_real_slicing_satisfies_the_hypotheses
#assert_compiled the_real_field_block_is_thirty_eight_canonical_elements
#assert_compiled the_honest_claim_renders_the_whole_field_elements
#assert_compiled the_field_falsifier_moves_a_value_the_gate_admits
#assert_compiled an_over_wide_field_limb_is_refused
#assert_compiled a_field_claim_that_is_not_its_column_is_refused

end Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir
