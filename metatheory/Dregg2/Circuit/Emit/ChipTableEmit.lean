/-
# `Dregg2.Circuit.Emit.ChipTableEmit` — the Poseidon2 CHIP table's AIR, AUTHORED IN LEAN.

## What this replaces

`Ir2Air::Chip | Ir2Air::ChipState16` (`circuit/src/descriptor_ir2.rs:3464-3741`) is the shared
hash table every IR-v2 proof rides: ONE table per batch serves every hash fact — the main trace's
hash-site lookups, the map-ops leaf absorbs, the Merkle-chain facts, and (on the state16 instance)
the raw 16→16 permutation transition. Its ~280 lines of `builder.assert_zero(..)` plus the 352
constraints of `poseidon2_permute_expr_lanes` are hand-authored Rust algebra, which architectural
law #1 forbids: *"circuits are emitted from Lean; Rust only INTERPRETS."*

`chipTable` and `chipState16Table` below ARE those two AIRs. The permutation half lives in
`Dregg2.Circuit.Emit.Poseidon2RoundGates`; this file authors the arity/selector algebra, the
seeding, the output binding and the bus interface, and splices the two together.

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `TExpr`. Nothing in this cutover hand-writes a Rust constraint.

## ⚑ WHAT THE PORT FOUND — read §7 before trusting the Rust comments

A port has to read every comment as a CLAIM. Four of them are wrong, and §7 proves it on the
emitted object:

  1. **`p7`/`p11`/`p16` are described BACKWARDS, three times** (`descriptor_ir2.rs:3255`, `:3269`,
     `:3283`). *"p7 ≠ 0 ⇔ arity ∈ {0,2,3,4,11,16} (= 0 exactly at arity 7)"* is exactly inverted —
     `p7` VANISHES on all six of those and is nonzero **only** at arity 7. The stated reason
     refutes the stated conclusion: read literally it says `p7·(1−big)` forces `big` HIGH on pad
     rows. The CODE is right; the sentence explaining why is upside down, and the NEXT sentence of
     the same comment (*"(a−11)/(a−16) adjoined so p7 also vanishes the wide + node8 rows"*)
     contradicts it. `forcing_products_vanish_off_their_own_arity` and `p7_comment_is_inverted`.
  2. **`seed456 ∈ {0,1}` is credited to the wrong gate** (`:3292`). *"the membership gate forces
     distinct arity values 7/11/16"* — the membership gate is not needed; the three
     `flag·(arity − c)` pins alone force it, and `seed456_is_boolean` uses only those.
  3. **`arity ∈ {0,2,3,4,7,11,16}` is a claim about RESIDUES, not integers.** §8b exhibits an
     ACCEPTED row carrying `arity = 2013265921`. Nothing is broken by it (the bus matches on field
     elements too), but a future range check that trusted the sentence would check the wrong thing.
  4. **The `(1 − is_fact)` factor on the state16 bus multiplicity is DEAD**
     (`state16_bus_guard_is_dead`). No satisfying row can have `mult_state16 ≢ 0` and
     `is_fact ≡ 1`, so that factor never differs from `1` anywhere it could matter.

And the column-layout comments are stale on SEVEN constants — `CHIP_OUT // 9` (17),
`CHIP_MULT // 17` (25), `CHIP_IS_FACT // 18` (26), `CHIP_BIG // 12` (27), `CHIP_S4/S5/S6 // 13,14,15`
(28/29/30) — with two more next door: `plonky3_prover.rs:292` `PARENT_COL // 245` (357) and
`descriptor_ir2.rs:889` *"`CHIP_RATE` = 11"* (16). §1 derives every offset from the arithmetic.

## ⚑ WHAT THE PORT COST — and what the sharing node bought. §10, `Poseidon2RoundGates` §7

The first pass of this file measured a blocker and stopped rather than cutting: `TExpr` was a TREE
with no sharing node, the Rust interpreter's `eval_expr` a naive recursive walk, and the deployed
hand-written arm shares its 16 per-round S-box values as `AB::Expr` VALUES. `TableAirIR` now has a
`shr` leaf and a per-table `defs` list, and the chip emits with the sharing the Rust arm has —
measured on both spellings, in §10, in this file:

|                    | TREE      | SHARED (emitted) | ratio |
|--------------------|-----------|------------------|-------|
| expression nodes   | 141,439   | **7,355**        | 19.2× |
| **arithmetic ops** | **70,524**| **2,943**        | **24.0×** |
| emitted JSON       | 3,098,882 B | **159,180 B**  | 19.5× |
| definitions        | —         | 1,078            |       |

⚑ **`opCount` is what the prover pays**, once per row of the quotient domain at blow-up 64, and
2,943 is the deployed arm's own 2,316 field operations plus exactly one multiplication per gate
(`TExpr` encodes `a − b` as `a + (−1)·b`; 391 gates). The algebra is the deployed one and this file
does NOT trade it for a cheaper arithmetization — that would be inventing a different circuit.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. `Nat.Prime 2013265921` is DISCHARGED by `norm_num`,
not assumed — it is what makes "a product vanishes ⇒ a factor vanishes" available, and every
`exactly` claim in §7 rests on it.
-/
import Dregg2.Circuit.Emit.Poseidon2RoundGates

namespace Dregg2.Circuit.Emit.ChipTableEmit

open Dregg2.Circuit.TableAirIR (TRowEnv)

open Dregg2.Circuit.TableAirIR
  (TExpr BusOp BusInteraction TableAir TableGate emitTableAirJson v k s eSub eOneMinus gBool gAll)
open Dregg2.Circuit.Emit.Poseidon2RoundGates
  (WIDTH POSEIDON2_AUX_COLS TOTAL_ROUNDS permGateBodies permEmission permOutLane permFinalState
   permBlocks permAuxWitness nodeCount opCount totalNodes)

set_option autoImplicit false

/-! ## §1 — The deployed column layout, DERIVED.

⚠ The trailing `// 9`, `// 17`, `// 12`, `// 13`, `// 14`, `// 15`, `// 18` comments on the Rust
`CHIP_*` constants (`descriptor_ir2.rs:2695-2736`) are STALE — every one of them describes a
pre-widening layout. Nothing below is transcribed from them; each offset is the arithmetic the Rust
`const` actually computes, and the `#guard`s are that arithmetic evaluated. -/

/-- `CHIP_RATE` — the chip's input-lane count (one full permutation seed). -/
def CHIP_RATE : Nat := 16
/-- `CHIP_OUT_LANES` — permutation output lanes on the wire. -/
def CHIP_OUT_LANES : Nat := 8
/-- `CHIP_WIDE_ARITY` — the Phase B-GATE-INPUT wide step (8-felt carrier ‖ 3 limbs). -/
def CHIP_WIDE_ARITY : Nat := 11
/-- `CHIP_NODE8_ARITY` — the Phase H3 full-width `L8 ‖ R8` compression. -/
def CHIP_NODE8_ARITY : Nat := 16

def CHIP_ARITY : Nat := 0
def CHIP_IN0 : Nat := 1
def CHIP_OUT : Nat := CHIP_IN0 + CHIP_RATE
def CHIP_MULT : Nat := CHIP_OUT + CHIP_OUT_LANES
def CHIP_IS_FACT : Nat := CHIP_MULT + 1
def CHIP_BIG : Nat := CHIP_IS_FACT + 1
def CHIP_S4 : Nat := CHIP_BIG + 1
def CHIP_S5 : Nat := CHIP_S4 + 1
def CHIP_S6 : Nat := CHIP_S5 + 1
def CHIP_WIDE : Nat := CHIP_S6 + 1
def CHIP_NODE8 : Nat := CHIP_WIDE + 1
def CHIP_AUX0 : Nat := CHIP_NODE8 + 1
/-- `CHIP_MULT_NARROW` — the `BUS_P2_1` service count, APPENDED past the aux block. -/
def CHIP_MULT_NARROW : Nat := CHIP_AUX0 + POSEIDON2_AUX_COLS
/-- ⚑ `CHIP_MULT_STATE16` is the SAME column: the state16 variant reuses the final column so the
ordinary chip width and every existing descriptor/VK shape are unchanged. -/
def CHIP_MULT_STATE16 : Nat := CHIP_MULT_NARROW
def CHIP_WIDTH : Nat := CHIP_MULT_NARROW + 1

/-- The chip tuple arity on `BUS_P2`: `1 (arity) + CHIP_RATE (inputs) + 8 (output lanes)`. -/
def CHIP_TUPLE_LEN : Nat := CHIP_RATE + 1 + CHIP_OUT_LANES
/-- The narrow tuple: `[arity, ins, out0]`. -/
def CHIP_NARROW_TUPLE_LEN : Nat := 1 + CHIP_RATE + 1
/-- The raw-transition tuple: `[16, complete input state, complete output state]`. -/
def CHIP_STATE16_TUPLE_LEN : Nat := 1 + WIDTH + WIDTH

/-- `FACT_MARK = 0xFACF` — the fact-row domain marker seeded into lane 5. -/
def FACT_MARK : ℤ := 64207
/-- `q01` on the pad row (arity 0): `(−2)(−3)(−4)(−7)(−11)(−16) = +29568 = 1848 · CHIP_NODE8_ARITY`
— six negative factors, so positive. This is the value the `is_fact` term cancels. -/
def Q01_PAD : ℤ := 1848 * 16

-- Every offset, derived. A layout drift on either side moves one of these.
#guard CHIP_OUT == 17
#guard CHIP_MULT == 25
#guard CHIP_IS_FACT == 26
#guard CHIP_BIG == 27
#guard CHIP_S4 == 28
#guard CHIP_S5 == 29
#guard CHIP_S6 == 30
#guard CHIP_WIDE == 31
#guard CHIP_NODE8 == 32
#guard CHIP_AUX0 == 33
#guard CHIP_MULT_NARROW == 385
#guard CHIP_MULT_STATE16 == 385
#guard CHIP_WIDTH == 386
#guard CHIP_TUPLE_LEN == 25
#guard CHIP_NARROW_TUPLE_LEN == 18
#guard CHIP_STATE16_TUPLE_LEN == 33
#guard FACT_MARK == 0xFACF
#guard Q01_PAD == 29568

/-- The bus names, verbatim from the Rust `BUS_*` constants (`descriptor_ir2.rs:412-427`). -/
def BUS_P2 : String := "ir2_p2"
def BUS_P2_1 : String := "ir2_p2_narrow"
def BUS_P2_STATE16 : String := "ir2_p2_state16"
def BUS_FACT : String := "ir2_fact"

/-! ## §2 — The arity products, emitted ONCE.

Ten of the arm's gates are the SAME shape: a left-associated product `(a − c₀)(a − c₁)…` over a
subset of the declared arities, where a `c = 0` factor is the bare column (the Rust writes
`arity.clone()`, not `arity − zero`). Emitting them from one function is what makes the ADJUDICATION
in §7 a statement about all ten rather than ten re-readings. -/

/-- `arity` and the four selector flags, as expressions. -/
def eArity : TExpr := v CHIP_ARITY
def eIsFact : TExpr := v CHIP_IS_FACT
def eBig : TExpr := v CHIP_BIG
def eWide : TExpr := v CHIP_WIDE
def eNode8 : TExpr := v CHIP_NODE8
/-- `seed456 = big + wide + node8`, left-associated as the Rust builds it. -/
def eSeed456 : TExpr := .add (.add eBig eWide) eNode8

/-- `ae − c`, with `c = 0` the bare expression — the Rust `arity.clone()` factor. -/
def eMinus (ae : TExpr) (c : ℤ) : TExpr := if c = 0 then ae else eSub ae (k c)

/-- `(ae − c₀)·(ae − c₁)·…`, left-associated exactly as the Rust `arity.clone() * (arity − two) * …`
accumulates it. -/
def eProdMinus (ae : TExpr) : List ℤ → TExpr
  | []        => k 1
  | c :: rest => rest.foldl (fun acc c' => .mul acc (eMinus ae c')) (eMinus ae c)

/-- The ℤ twin of `eProdMinus`, same association. -/
def prodMinus (a : ℤ) : List ℤ → ℤ
  | []        => 1
  | c :: rest => rest.foldl (fun acc c' => acc * (a - c')) (a - c)

/-- The seven declared arities: `0` (pad/fact), `2`, `3` (cap node), `4`, `7` (cap leaf), `11`
(wide MD step), `16` (`node8` compression). -/
def ARITIES : List ℤ := [0, 2, 3, 4, 7, 11, 16]
/-- `p7`'s roots — every declared arity BUT 7. -/
def P7_ROOTS : List ℤ := [0, 2, 3, 4, 11, 16]
/-- `p11`'s roots. -/
def P11_ROOTS : List ℤ := [0, 2, 3, 4, 7, 16]
/-- `p16`'s roots. -/
def P16_ROOTS : List ℤ := [0, 2, 3, 4, 7, 11]
/-- `q01`'s roots — every declared arity BUT 0, so `q01` is nonzero exactly on the arity-0 row. -/
def Q01_ROOTS : List ℤ := [2, 3, 4, 7, 11, 16]

/-- The input-lane zeroing multiplier for lane `i`: the arities that REACH lane `i`, as roots. Lane
0/1 are the `q01` special case (they carry the fact row's `l`/`r`) and are not built here. -/
def inputRoots (i : Nat) : List ℤ :=
  if i < 3 then [3, 4, 7, 11, 16]
  else if i < 4 then [4, 7, 11, 16]
  else if i < 7 then [7, 11, 16]
  else if i < CHIP_WIDE_ARITY then [11, 16]
  else [16]

/-! ## §3 — The gate bodies, in the deployed emission order.

Each is named so §7 can talk about a gate rather than an index, and so a drift names the gate. -/

/-- `is_fact` is boolean. -/
def gIsFactBool : TExpr := gBool CHIP_IS_FACT
/-- The arity MEMBERSHIP product — degree 7, the S-box budget. -/
def gArityMember : TExpr := eProdMinus eArity ARITIES
/-- ⚑ The state16-ONLY pin: a row with nonzero state-bus multiplicity is arity 16. -/
def gState16Pin : TExpr := .mul (v CHIP_MULT_STATE16) (eSub eArity (k 16))
/-- A fact row carries arity 0. -/
def gFactArity : TExpr := .mul eIsFact eArity
def gBigBool : TExpr := gBool CHIP_BIG
/-- `big` high ⇒ arity 7. -/
def gBigPin : TExpr := .mul eBig (eSub eArity (k 7))
/-- arity 7 ⇒ `big` high. -/
def gBigForce : TExpr := .mul (eProdMinus eArity P7_ROOTS) (eOneMinus eBig)
def gWideBool : TExpr := gBool CHIP_WIDE
def gWidePin : TExpr := .mul eWide (eSub eArity (k 11))
def gWideForce : TExpr := .mul (eProdMinus eArity P11_ROOTS) (eOneMinus eWide)
def gNode8Bool : TExpr := gBool CHIP_NODE8
def gNode8Pin : TExpr := .mul eNode8 (eSub eArity (k 16))
def gNode8Force : TExpr := .mul (eProdMinus eArity P16_ROOTS) (eOneMinus eNode8)

/-- The `q01` multiplier: zero on every absorb arity, `+29568` on the pad row, and CANCELLED on a
fact row by the `−29568·is_fact` term. -/
def eQ01Guard : TExpr := eSub (eProdMinus eArity Q01_ROOTS) (.mul (k Q01_PAD) eIsFact)

/-- The zeroing gate of input lane `i`. Lanes 0/1 ride `eQ01Guard`; the rest ride `inputRoots`. -/
def gInputZero (i : Nat) : TExpr :=
  if i < 2 then .mul (v (CHIP_IN0 + i)) eQ01Guard
  else .mul (v (CHIP_IN0 + i)) (eProdMinus eArity (inputRoots i))

/-- `S4 = seed456·in4 + (1 − seed456)·arity`. -/
def gS4 : TExpr :=
  eSub (v CHIP_S4) (.add (.mul eSeed456 (v (CHIP_IN0 + 4))) (.mul (eOneMinus eSeed456) eArity))
/-- `S5 = seed456·in5 + (1 − seed456)·is_fact·FACT_MARK`. -/
def gS5 : TExpr :=
  eSub (v CHIP_S5)
    (.add (.mul eSeed456 (v (CHIP_IN0 + 5)))
          (.mul (.mul (eOneMinus eSeed456) eIsFact) (k FACT_MARK)))
/-- `S6 = seed456·in6 + (1 − seed456)·is_fact`. -/
def gS6 : TExpr :=
  eSub (v CHIP_S6) (.add (.mul eSeed456 (v (CHIP_IN0 + 6))) (.mul (eOneMinus eSeed456) eIsFact))

/-- **The ARITY/SELECTOR/SEEDING gates**, in the Rust emission order. `servesState16` inserts the
one extra gate the state16 variant adds, at the position the Rust emits it (right after the
membership gate) — the two variants SHARE this list rather than copying it. -/
def chipSelectorBodies (servesState16 : Bool) : List TExpr :=
  [gIsFactBool, gArityMember] ++
  (if servesState16 then [gState16Pin] else []) ++
  [ gFactArity
  , gBigBool, gBigPin, gBigForce
  , gWideBool, gWidePin, gWideForce
  , gNode8Bool, gNode8Pin, gNode8Force ] ++
  (List.range CHIP_NODE8_ARITY).map gInputZero ++
  [gS4, gS5, gS6]

/-- ⚑ The 16 SEED LANES. Lanes 0..3 read the inputs directly; lanes 4..6 read the DEDICATED
`S4`/`S5`/`S6` columns (each a single column read, degree 1, so the first `x⁷` S-box stays inside
the degree-7 budget — that is the whole reason those columns exist); lanes 7..15 read the wide
carrier / `node8` second-child tail, which every narrow arity pins to zero. -/
def chipSeedState : List TExpr :=
  (List.range 4).map (fun i => v (CHIP_IN0 + i)) ++
  [v CHIP_S4, v CHIP_S5, v CHIP_S6] ++
  (List.range (CHIP_NODE8_ARITY - 7)).map (fun i => v (CHIP_IN0 + 7 + i))

/-- ⚑ **THE EMITTED PERMUTATION** — the 1,078 SHARED DEFINITIONS and the 352 gate bodies that read
them, at the chip's aux base and seeding. The chip declares no definitions of its own, so the
permutation's start at index 0 and `chipDefs` IS the table's whole `defs` list.

⚠ The chip's own selector/seeding/output gates share NOTHING, and that is correct rather than an
oversight: `arity`, `is_fact` and the flags are single column reads (a `shr` of a `loc` costs a slot
and saves nothing), and each arity product is read once. The sharing is entirely in the permutation,
which is where the duplication was. `chipSelectorBodies` and `chipOutBodies` are therefore
share-free, which is also what lets §6's sub-tables carry their verdicts back to the emitted table
(`TableAir.rowHoldsWith_of_shareFree`). -/
def chipEmission : List TExpr × List TExpr := permEmission CHIP_AUX0 0 chipSeedState

/-- The shared definitions the emitted chip table carries. -/
def chipDefs : List TExpr := chipEmission.1

/-- The 352 permutation gates, at the chip's aux base and seeding. -/
def chipPermBodies : List TExpr := chipEmission.2

/-- ⚠ The TREE spelling of the same 352 gates — NOT emitted. Kept as §10's measurement baseline and
as the agreement oracle `Poseidon2RoundGates` §6b runs. -/
def chipPermBodiesTree : List TExpr := permGateBodies CHIP_AUX0 chipSeedState

/-- The 8 OUTPUT BINDINGS `out[i] − lanes[i]`. ⚑ After the permutation's final rebind these
`lanes[i]` ARE aux columns, so each is an equality binding to an already-constrained column — which
is exactly what makes a forged `out[i]` unsatisfiable (§7). -/
def chipOutBodies : List TExpr :=
  (List.range CHIP_OUT_LANES).map (fun i => eSub (v (CHIP_OUT + i)) (permOutLane CHIP_AUX0 i))

/-- The whole gate-body list of either variant. -/
def chipGateBodies (servesState16 : Bool) : List TExpr :=
  chipSelectorBodies servesState16 ++ chipPermBodies ++ chipOutBodies

/-! ## §4 — The bus interface.

⚠ `.provide` is load-bearing: the chip SERVES every one of its buses (`LookupBus::table_entry`,
p3 `count_weight = 0`). A `.query` here would make each bus unsatisfiable in one direction and
vacuous in the other. §5 pins `busCountOp` on both sides. -/

/-- The 25-wide absorb tuple `[arity, ins(16), out0..out7]`. -/
def chipTuple : List TExpr :=
  eArity :: ((List.range CHIP_RATE).map (fun i => v (CHIP_IN0 + i)) ++
             (List.range CHIP_OUT_LANES).map (fun i => v (CHIP_OUT + i)))

/-- The 18-wide narrow tuple `[arity, ins(16), out0]` — the SAME row serving single-output sites. -/
def chipNarrowTuple : List TExpr :=
  eArity :: ((List.range CHIP_RATE).map (fun i => v (CHIP_IN0 + i)) ++ [v CHIP_OUT])

/-- The 33-wide raw-transition tuple `[16, complete input state, complete output state]`. ⚑ The
output block is the FINAL aux block (`aux[POSEIDON2_AUX_COLS − 16 ..]`), which the permutation
gates already constrain — exposing it adds no witness columns and leaves lanes 8..15 not free. -/
def chipState16Tuple : List TExpr :=
  k (CHIP_NODE8_ARITY : ℤ) ::
    ((List.range WIDTH).map (fun i => v (CHIP_IN0 + i)) ++ permFinalState CHIP_AUX0)

/-- The legacy instance's three served buses. Fact rows provide ZERO on the absorb buses and vice
versa — no fact digest can serve a hash-site lookup. -/
def chipInteractions : List BusInteraction :=
  [ ⟨BUS_P2,   .provide, .mul (v CHIP_MULT) (eOneMinus eIsFact), chipTuple⟩
  , ⟨BUS_P2_1, .provide, .mul (v CHIP_MULT_NARROW) (eOneMinus eIsFact), chipNarrowTuple⟩
  , ⟨BUS_FACT, .provide, .mul (v CHIP_MULT) eIsFact,
      [v CHIP_IN0, v (CHIP_IN0 + 1), v CHIP_OUT]⟩ ]

/-- The additive instance's single served bus. ⚠ §7 proves the `(1 − is_fact)` factor here is
DEAD: no satisfying row has `mult_state16 ≢ 0` and `is_fact ≡ 1`. -/
def chipState16Interactions : List BusInteraction :=
  [ ⟨BUS_P2_STATE16, .provide, .mul (v CHIP_MULT_STATE16) (eOneMinus eIsFact), chipState16Tuple⟩ ]

/-- **`chipTable`** — `Ir2Air::Chip`, as a Lean object. -/
def chipTable : TableAir :=
  { name         := "dregg-ir2-chip-v1"
  , width        := CHIP_WIDTH
  , prepWidth    := 0
  , defs         := chipDefs
  , gates        := (chipGateBodies false).map gAll
  , interactions := chipInteractions }

/-- **`chipState16Table`** — `Ir2Air::ChipState16`. Same width, same permutation, ONE extra gate
and a different bus interface. -/
def chipState16Table : TableAir :=
  { name         := "dregg-ir2-chip-state16-v1"
  , width        := CHIP_WIDTH
  , prepWidth    := 0
  , defs         := chipDefs
  , gates        := (chipGateBodies true).map gAll
  , interactions := chipState16Interactions }

/-! ## §5 — Shape pins.

Counts DERIVED from the layout: `2 + 1 + 9 + 16 + 3 = 31` selector gates (`+1` on state16), `352`
permutation gates, `8` output bindings. -/

#guard chipTable.width == 386
#guard chipState16Table.width == 386
#guard (chipSelectorBodies false).length == 31
#guard (chipSelectorBodies true).length == 32
#guard chipPermBodies.length == 352
#guard chipOutBodies.length == 8
#guard chipTable.gates.length == 391
#guard chipState16Table.gates.length == 392

-- ⚑ SELECTOR pins: this table is purely ROW-LOCAL (the deployed arm calls `builder.assert_zero`
-- directly, never a row filter, and reads no `nxt` column). `TableGate.transition_weakens` says a
-- re-scope accepts strictly MORE and leaves the algebra byte-identical, so it is pinned.
#guard chipTable.gateCountSel .all == 391
#guard chipTable.gateCountSel .transition == 0
#guard chipTable.gateCountSel .first == 0
#guard chipTable.gateCountSel .last == 0
#guard chipState16Table.gateCountSel .all == 392
#guard chipTable.isRowLocal == true
#guard chipState16Table.isRowLocal == true

-- ⚑ BUS-SIDE pins: every leg is a `.provide`. A flipped side would be invisible to the totals.
#guard chipTable.busCount == 3
#guard chipTable.busCountOp "ir2_p2" .provide == 1
#guard chipTable.busCountOp "ir2_p2_narrow" .provide == 1
#guard chipTable.busCountOp "ir2_fact" .provide == 1
#guard chipTable.busCountOp "ir2_p2" .query == 0
#guard chipTable.busCountOn "ir2_p2_state16" == 0
#guard chipState16Table.busCount == 1
#guard chipState16Table.busCountOp "ir2_p2_state16" .provide == 1
#guard chipState16Table.busCountOp "ir2_p2_state16" .query == 0
#guard chipState16Table.busCountOn "ir2_p2" == 0
#guard chipState16Table.busCountOn "ir2_fact" == 0

-- Tuple widths, derived from the layout rather than transcribed.
#guard chipTuple.length == CHIP_TUPLE_LEN
#guard chipNarrowTuple.length == CHIP_NARROW_TUPLE_LEN
#guard chipState16Tuple.length == CHIP_STATE16_TUPLE_LEN
#guard chipSeedState.length == WIDTH

/-- ⚑ **THE TWO VARIANTS SHARE EVERYTHING BUT ONE GATE**, stated rather than commented: dropping
the state16 pin from the state16 body list gives the legacy list back, exactly. A copy-paste port
would make this false without moving any count. -/
theorem variants_differ_by_one_gate :
    chipGateBodies true = [gIsFactBool, gArityMember] ++ [gState16Pin] ++
      ((chipGateBodies false).drop 2) := by
  simp [chipGateBodies, chipSelectorBodies, List.append_assoc]

/-- …and the legacy variant is the state16 one with that gate removed. -/
theorem legacy_is_state16_minus_pin :
    chipGateBodies false = [gIsFactBool, gArityMember] ++ ((chipGateBodies true).drop 3) := by
  simp [chipGateBodies, chipSelectorBodies, List.append_assoc]

/-! ### §5b — Column coverage: which columns the emission actually reads.

⚑ A DERIVED finding, not a comment: `chipTable` reads every one of its 386 columns, and
`chipState16Table` reads all but ONE — `CHIP_MULT` (25), the legacy absorb/fact multiplicity, which
the state16 variant declares and then uses nowhere. A free column is not a soundness hole, but it is
a column the witness generator must fill and the commitment must carry. -/

/-- The distinct columns an emitted table reads, over DEFINITIONS, gates AND interactions. One pass,
hash-consed — `readsColIn` per column would be a 386× walk over a thousand definitions.

⚑ The definition pass is not bookkeeping: with the sharing node, every column the permutation reads
is read THROUGH a `shr`, so a coverage scan that stopped at gate bodies would report the chip
reading 34 of its 386 columns. Each `shr i` contributes the columns of `defs[i]`, and because the
list is topologically ordered a single left-to-right pass is enough (the `defs` loop runs FIRST and
accumulates into the same set). -/
def readCols (t : TableAir) : List Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut dcols : Array (Std.HashSet Nat) := Array.emptyWithCapacity t.defs.length
  let rec go (e : TExpr) (dv : Array (Std.HashSet Nat)) (s : Std.HashSet Nat) : Std.HashSet Nat :=
    match e with
    | .loc c => s.insert c
    | .nxt c => s.insert c
    | .const _ => s
    | .shr i => (dv.getD i {}).fold (fun acc c => acc.insert c) s
    -- ⚠ A `prep` reads a DIFFERENT column space, so it contributes NO committed column here. The
    -- chip declares `prepWidth = 0` and has none; the case exists because the grammar does.
    | .prep _ => s
    | .add a b => go b dv (go a dv s)
    | .mul a b => go b dv (go a dv s)
  for d in t.defs do
    dcols := dcols.push (go d dcols {})
  for g in t.gates do seen := go g.body dcols seen
  for i in t.interactions do
    seen := go i.mult dcols seen
    for e in i.tuple do seen := go e dcols seen
  return (List.range t.width).filter (fun c => seen.contains c)

#guard (readCols chipTable).length == CHIP_WIDTH
#guard (List.range CHIP_WIDTH).filter (fun c => !(readCols chipState16Table).contains c)
     == [CHIP_MULT]

/-! ## §6 — THE ANALYSIS SUB-TABLES.

⚠ **NOT EMITTED, and not artifacts.** The emitted chip carries 1,078 definitions and 391 gates, so a
KERNEL `decide` against it is not viable. These three tables are built from the SAME body lists the
emission splices, so a `decide` against them is a decision about the emitted gates — and
`selector_of_chip` / `out_of_chip` carry the verdict back to `chipTable` itself rather than leaving
the sub-table an unconnected model.

⚑ **AND WITH A DEFINITION LIST IN PLAY THAT TRANSPORT IS A REAL OBLIGATION.** The sub-tables declare
`defs := []` while the emitted table resolves 1,078, so a verdict about the sub-table is a verdict
about a different machine UNLESS the block it covers reads no definition. It does not — the
selector, seeding and output gates are share-free, all the sharing is in the permutation — and that
is DISCHARGED by `decide` on the emitted gate list (`selector_block_is_share_free` below), not
assumed. Without it these three theorems would be vacuously about `#[]`. -/

/-- The 31 arity/selector/seeding gates of the LEGACY variant. -/
def chipSelectorTable : TableAir :=
  { name := "chip-selectors (ANALYSIS ONLY, not emitted)"
  , width := CHIP_WIDTH, prepWidth := 0, defs := [], gates := (chipSelectorBodies false).map gAll, interactions := [] }

/-- The 32 arity/selector/seeding gates of the STATE16 variant. -/
def chipState16SelectorTable : TableAir :=
  { name := "chip-state16-selectors (ANALYSIS ONLY, not emitted)"
  , width := CHIP_WIDTH, prepWidth := 0, defs := [], gates := (chipSelectorBodies true).map gAll, interactions := [] }

/-- The 8 output bindings. -/
def chipOutTable : TableAir :=
  { name := "chip-out-bindings (ANALYSIS ONLY, not emitted)"
  , width := CHIP_WIDTH, prepWidth := 0, defs := [], gates := chipOutBodies.map gAll, interactions := [] }

/-- ⚑ **THE HYPOTHESIS THE TRANSPORT NEEDS, DECIDED.** Not one gate of the three sub-tables reads a
shared definition, so their verdicts are independent of the definition vector. A future edit that
shared a selector sub-expression would turn this red rather than silently making the three theorems
below statements about an empty vector. -/
theorem selector_block_is_share_free :
    chipSelectorTable.gates.all (fun g => g.body.maxShare == none) = true ∧
    chipState16SelectorTable.gates.all (fun g => g.body.maxShare == none) = true ∧
    chipOutTable.gates.all (fun g => g.body.maxShare == none) = true := by
  refine ⟨by decide, by decide, by decide⟩

-- ⚠ THE CONTROL: the permutation half is NOT share-free, so the predicate above is discriminating
-- rather than trivially true of every gate list. (A `#guard`, i.e. a compiled evaluation — the
-- permutation block is far too large for the kernel and `native_decide` is not used in this tree.)
#guard (chipPermBodies.map gAll).all (fun g => g.body.maxShare == none) == false

/-- The emitted gate list really is the selector block followed by the rest. -/
theorem chipTable_gates_split :
    chipTable.gates = chipSelectorTable.gates ++ ((chipPermBodies ++ chipOutBodies).map gAll) := by
  simp [chipTable, chipSelectorTable, chipGateBodies, List.map_append, List.append_assoc]

/-- …so anything the selector sub-table refuses, the EMITTED table refuses. -/
theorem selector_of_chip {env : TRowEnv} {f l : Bool} (h : chipTable.RowHolds env f l) :
    chipSelectorTable.RowHolds env f l := by
  refine TableAir.rowHoldsWith_of_shareFree selector_block_is_share_free.1
    (sv := chipTable.shareVals env) ?_
  intro g hg
  exact h g (by rw [chipTable_gates_split]; exact List.mem_append_left _ hg)

/-- The same for the state16 variant. -/
theorem chipState16Table_gates_split :
    chipState16Table.gates
      = chipState16SelectorTable.gates ++ ((chipPermBodies ++ chipOutBodies).map gAll) := by
  simp [chipState16Table, chipState16SelectorTable, chipGateBodies, List.map_append,
    List.append_assoc]

theorem state16_selector_of_chip {env : TRowEnv} {f l : Bool}
    (h : chipState16Table.RowHolds env f l) : chipState16SelectorTable.RowHolds env f l := by
  refine TableAir.rowHoldsWith_of_shareFree selector_block_is_share_free.2.1
    (sv := chipState16Table.shareVals env) ?_
  intro g hg
  exact h g (by rw [chipState16Table_gates_split]; exact List.mem_append_left _ hg)

/-- …and the OUTPUT bindings are the emitted table's tail. -/
theorem out_of_chip {env : TRowEnv} {f l : Bool} (h : chipTable.RowHolds env f l) :
    chipOutTable.RowHolds env f l := by
  refine TableAir.rowHoldsWith_of_shareFree selector_block_is_share_free.2.2
    (sv := chipTable.shareVals env) ?_
  intro g hg
  refine h g ?_
  rw [chipTable_gates_split]
  refine List.mem_append_right _ ?_
  simp only [List.map_append]
  exact List.mem_append_right _ hg

/-! ## §7 — THE ADJUDICATIONS.

Each comment-only claim of the Rust arm, decided on the EMITTED object. Where the answer is TRUE it
is a theorem with a satisfiable premise AND an exhibited refutation; where it is FALSE the witness
is here.

`Nat.Prime 2013265921` is what makes "a product vanishes ⇒ a factor vanishes" available at all, and
every `exactly` below rests on it. It is discharged, not assumed. -/

set_option maxRecDepth 8192 in
/-- BabyBear is prime, discharged by `norm_num`. -/
theorem P_prime : Nat.Prime 2013265921 := by norm_num

/-- …and prime over ℤ, which is the form `Prime.dvd_mul` needs. -/
theorem pPrimeInt : Prime (2013265921 : ℤ) := by
  exact_mod_cast Nat.prime_iff_prime_int.mp P_prime

private theorem modEq_of_dvd_sub {a c : ℤ} (h : (2013265921 : ℤ) ∣ a - c) :
    a ≡ c [ZMOD 2013265921] := (Int.modEq_iff_dvd.mpr h).symm

private theorem dvd_sub_of_modEq {a c : ℤ} (h : a ≡ c [ZMOD 2013265921]) :
    (2013265921 : ℤ) ∣ a - c := (Int.modEq_iff_dvd.mp h.symm)

/-- A small nonzero integer is not a multiple of `p` — the shape every "the forcing product does
not vanish here" step needs. -/
private theorem not_dvd_small {q : ℤ} (hq : q ≠ 0) (hlt : q.natAbs < 2013265921) :
    ¬ ((2013265921 : ℤ) ∣ q) := by
  intro hd
  have := Int.le_of_dvd (by positivity) (Int.dvd_natAbs.mpr hd)
  omega

/-! ### §7.0 — Reading a gate off the emitted list. -/

private theorem sel_gate {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) {b : TExpr}
    (hb : b ∈ chipSelectorBodies false) : b.evalWith #[] env ≡ 0 [ZMOD 2013265921] :=
  h (gAll b) (List.mem_map_of_mem hb)

private theorem mem_sel (b : TExpr) (hb : b ∈ chipSelectorBodies false) :
    b ∈ chipSelectorBodies false := hb

/-- Evaluation of the emitted product expression IS the integer product. -/
private theorem eMinus_eval (ae : TExpr) (c : ℤ) (env : TRowEnv) :
    (eMinus ae c).evalWith #[] env = ae.evalWith #[] env - c := by
  unfold eMinus
  split
  · next h => simp [h]
  · simp [eSub, k, TExpr.evalWith]; ring

private theorem fold_eval (ae : TExpr) (env : TRowEnv) :
    ∀ (cs : List ℤ) (acc : TExpr),
      (cs.foldl (fun a c => TExpr.mul a (eMinus ae c)) acc).evalWith #[] env
        = cs.foldl (fun a c => a * (ae.evalWith #[] env - c)) (acc.evalWith #[] env) := by
  intro cs
  induction cs with
  | nil => intro acc; simp
  | cons c rest ih =>
    intro acc
    simpa [TExpr.evalWith, eMinus_eval] using ih (TExpr.mul acc (eMinus ae c))

theorem eProdMinus_eval (ae : TExpr) (env : TRowEnv) (cs : List ℤ) :
    (eProdMinus ae cs).evalWith #[] env = prodMinus (ae.evalWith #[] env) cs := by
  cases cs with
  | nil => simp [eProdMinus, prodMinus, k, TExpr.evalWith]
  | cons c rest => simpa [eProdMinus, prodMinus, eMinus_eval] using fold_eval ae env rest (eMinus ae c)

/-! ### §7.1 — ⚑ REFUTED: `p7` / `p11` / `p16` are described BACKWARDS.

The Rust comment reads *"p7 ≠ 0 ⇔ arity ∈ {0,2,3,4,11,16} (= 0 exactly at arity 7)"*, and the same
sentence appears for `p11` and `p16`. It is exactly inverted. `p7` is the product over ALL the
declared arities EXCEPT 7, so it VANISHES on all six of them and is nonzero ONLY at arity 7 — which
is what makes `p7·(1−big)` force `big` high there and leave it free (and hence LOW, via `gBigPin`)
everywhere else.

Read literally, the comment says `p7·(1−big) = 0` forces `big` HIGH on the pad row. The next
sentence of the same comment — *"`(a−11)`/`(a−16)` adjoined so p7 also vanishes the wide + node8
rows"* — contradicts it. The CODE is correct; the explanation is upside down. -/

/-- The forcing products, evaluated at every declared arity. Each is nonzero at EXACTLY one arity —
its own — and zero at the other six. -/
theorem forcing_products_vanish_off_their_own_arity :
    ARITIES.map (fun a => prodMinus a P7_ROOTS)  = [0, 0, 0, 0, 15120, 0, 0] ∧
    ARITIES.map (fun a => prodMinus a P11_ROOTS) = [0, 0, 0, 0, 0, -110880, 0] ∧
    ARITIES.map (fun a => prodMinus a P16_ROOTS) = [0, 0, 0, 0, 0, 0, 1572480] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ THE REFUTATION, stated as the comment states it: the claim *"p7 ≠ 0 ⇔ arity ∈
{0,2,3,4,11,16}"* is FALSE at every one of the six arities it names. -/
theorem p7_comment_is_inverted : ∀ a ∈ P7_ROOTS, prodMinus a P7_ROOTS = 0 := by decide

/-- …and `q01` is the ONE product of the family that IS nonzero at arity 0 — the comment about it
(`+29568`, six negative factors) is correct, which is what makes the inversion above a comment bug
rather than a systematic sign error. -/
theorem q01_is_29568_on_the_pad_row : prodMinus 0 Q01_ROOTS = Q01_PAD := by decide

/-! ### §7.2 — TRUE: each flag is EXACTLY `[arity == c]`.

Proved once, for all three flags, on the emitted gates. The `exactly` is genuine and needs primality
in both directions: `flag ⇒ arity` splits `flag·(arity − c)`, `arity ⇒ flag` needs the forcing
product to be a NON-multiple of `p` at `arity ≡ c`, which §7.1's values supply. -/

/-- The flag pattern, proved once for all three flags. ⚑ Both directions need primality: `flag ⇒
arity` splits `flag·(arity − c)`, and `arity ⇒ flag` needs the forcing product to be a NON-multiple
of `p` at `arity ≡ c` — which is exactly what §7.1's values supply, and exactly what the inverted
comment denies. -/
theorem flag_exact {A F Q c q : ℤ}
    (hpin : F * (A - c) ≡ 0 [ZMOD 2013265921])
    (hforce : Q * (1 - F) ≡ 0 [ZMOD 2013265921])
    (hQ : A ≡ c [ZMOD 2013265921] → Q ≡ q [ZMOD 2013265921])
    (hq : ¬ ((2013265921 : ℤ) ∣ q)) :
    (F ≡ 1 [ZMOD 2013265921]) ↔ (A ≡ c [ZMOD 2013265921]) := by
  constructor
  · intro hF
    rw [Int.modEq_zero_iff_dvd] at hpin
    rcases pPrimeInt.dvd_mul.mp hpin with hd | hd
    · exfalso
      have h0 : F ≡ 0 [ZMOD 2013265921] := (Int.modEq_zero_iff_dvd).mpr hd
      have h1 : (1 : ℤ) ≡ 0 [ZMOD 2013265921] := hF.symm.trans h0
      exact not_dvd_small (by norm_num) (by norm_num) ((Int.modEq_zero_iff_dvd).mp h1)
    · exact modEq_of_dvd_sub hd
  · intro hA
    rw [Int.modEq_zero_iff_dvd] at hforce
    rcases pPrimeInt.dvd_mul.mp hforce with hd | hd
    · exfalso
      have hQ0 : Q ≡ 0 [ZMOD 2013265921] := (Int.modEq_zero_iff_dvd).mpr hd
      exact hq ((Int.modEq_zero_iff_dvd).mp ((hQ hA).symm.trans hQ0))
    · exact (modEq_of_dvd_sub hd).symm

/-- The FORWARD half alone — `flag ⇒ arity`. Split out because §7.4 needs exactly this and NOT the
forcing product, which is what shows the `seed456` comment credits the wrong gate. -/
theorem flag_high_imp_arity {A F c : ℤ}
    (hpin : F * (A - c) ≡ 0 [ZMOD 2013265921]) (hF : F ≡ 1 [ZMOD 2013265921]) :
    A ≡ c [ZMOD 2013265921] := by
  rw [Int.modEq_zero_iff_dvd] at hpin
  rcases pPrimeInt.dvd_mul.mp hpin with hd | hd
  · exfalso
    have h1 : (1 : ℤ) ≡ 0 [ZMOD 2013265921] := hF.symm.trans ((Int.modEq_zero_iff_dvd).mpr hd)
    exact not_dvd_small (by norm_num) (by norm_num) ((Int.modEq_zero_iff_dvd).mp h1)
  · exact modEq_of_dvd_sub hd

/-- A boolean gate really does force `{0, 1}` — over a FIELD. -/
theorem bool_of_gate {x : ℤ} (h : x * (x - 1) ≡ 0 [ZMOD 2013265921]) :
    x ≡ 0 [ZMOD 2013265921] ∨ x ≡ 1 [ZMOD 2013265921] := by
  rw [Int.modEq_zero_iff_dvd] at h
  rcases pPrimeInt.dvd_mul.mp h with hd | hd
  · exact Or.inl ((Int.modEq_zero_iff_dvd).mpr hd)
  · exact Or.inr (modEq_of_dvd_sub hd)

/-- Congruence of a six-root product — the shape `p7`/`p11`/`p16`/`q01` all have. -/
private theorem prodMinus_congr6 {A c : ℤ} (h : A ≡ c [ZMOD 2013265921]) (r0 r1 r2 r3 r4 r5 : ℤ) :
    prodMinus A [r0, r1, r2, r3, r4, r5] ≡ prodMinus c [r0, r1, r2, r3, r4, r5]
      [ZMOD 2013265921] := by
  simp only [prodMinus, List.foldl]
  exact ((((h.sub_right r0).mul (h.sub_right r1)).mul (h.sub_right r2)).mul
    (h.sub_right r3)).mul (h.sub_right r4) |>.mul (h.sub_right r5)

/-! ### §7.0b — Gate bodies, evaluated. -/

private theorem gBool_eval (c : Nat) (env : TRowEnv) :
    (gBool c).evalWith #[] env = env.loc c * (env.loc c - 1) := by
  simp only [gBool, v, k, TExpr.evalWith]; ring

private theorem gArityMember_eval (env : TRowEnv) :
    gArityMember.evalWith #[] env = prodMinus (env.loc CHIP_ARITY) ARITIES := by
  simp [gArityMember, eProdMinus_eval, eArity, v, TExpr.evalWith]

private theorem gFactArity_eval (env : TRowEnv) :
    gFactArity.evalWith #[] env = env.loc CHIP_IS_FACT * env.loc CHIP_ARITY := by
  simp [gFactArity, eIsFact, eArity, v, TExpr.evalWith]

private theorem gPin_eval (fc : Nat) (c : ℤ) (env : TRowEnv) :
    (TExpr.mul (v fc) (eSub eArity (k c))).evalWith #[] env
      = env.loc fc * (env.loc CHIP_ARITY - c) := by
  simp only [eArity, eSub, k, v, TExpr.evalWith]; ring

private theorem gForce_eval (roots : List ℤ) (fc : Nat) (env : TRowEnv) :
    (TExpr.mul (eProdMinus eArity roots) (eOneMinus (v fc))).evalWith #[] env
      = prodMinus (env.loc CHIP_ARITY) roots * (1 - env.loc fc) := by
  simp only [eOneMinus, eSub, k, v, TExpr.evalWith, eProdMinus_eval, eArity]; ring

private theorem eQ01Guard_eval (env : TRowEnv) :
    eQ01Guard.evalWith #[] env
      = prodMinus (env.loc CHIP_ARITY) Q01_ROOTS - Q01_PAD * env.loc CHIP_IS_FACT := by
  simp [eQ01Guard, eSub, k, v, TExpr.evalWith, eProdMinus_eval, eArity, eIsFact]; ring

/-- The input-zeroing gate of lane `i` is one of the emitted selector gates. Split out because it
is the one gate reached through a `List.map`, not a literal. -/
private theorem sel_inputZero {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) (i : Nat) (hi : i < CHIP_NODE8_ARITY) :
    (gInputZero i).evalWith #[] env ≡ 0 [ZMOD 2013265921] := by
  refine sel_gate h ?_
  simp only [chipSelectorBodies, Bool.false_eq_true, if_false]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (List.mem_range.mpr hi)))

/-! ### §7.2 — TRUE: each flag is EXACTLY `[arity == c]`, on the emitted gates. -/

/-- `big` is high EXACTLY on arity 7 — both directions, on the emitted gate list. -/
theorem big_high_iff_arity_seven {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) :
    (env.loc CHIP_BIG ≡ 1 [ZMOD 2013265921]) ↔ (env.loc CHIP_ARITY ≡ 7 [ZMOD 2013265921]) := by
  have hpin := sel_gate h (b := gBigPin) (by simp [chipSelectorBodies])
  have hforce := sel_gate h (b := gBigForce) (by simp [chipSelectorBodies])
  rw [show gBigPin = TExpr.mul (v CHIP_BIG) (eSub eArity (k 7)) from rfl, gPin_eval] at hpin
  rw [show gBigForce = TExpr.mul (eProdMinus eArity P7_ROOTS) (eOneMinus (v CHIP_BIG))
        from rfl, gForce_eval] at hforce
  refine flag_exact (q := 15120) hpin hforce (fun hA => ?_) (not_dvd_small (by norm_num) (by norm_num))
  simpa [P7_ROOTS, show prodMinus (7 : ℤ) [0, 2, 3, 4, 11, 16] = 15120 from by decide] using
    prodMinus_congr6 hA 0 2 3 4 11 16

/-- `wide` is high EXACTLY on arity 11. -/
theorem wide_high_iff_arity_eleven {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) :
    (env.loc CHIP_WIDE ≡ 1 [ZMOD 2013265921]) ↔ (env.loc CHIP_ARITY ≡ 11 [ZMOD 2013265921]) := by
  have hpin := sel_gate h (b := gWidePin) (by simp [chipSelectorBodies])
  have hforce := sel_gate h (b := gWideForce) (by simp [chipSelectorBodies])
  rw [show gWidePin = TExpr.mul (v CHIP_WIDE) (eSub eArity (k 11)) from rfl, gPin_eval] at hpin
  rw [show gWideForce = TExpr.mul (eProdMinus eArity P11_ROOTS) (eOneMinus (v CHIP_WIDE))
        from rfl, gForce_eval] at hforce
  refine flag_exact (q := -110880) hpin hforce (fun hA => ?_)
    (not_dvd_small (by norm_num) (by norm_num))
  simpa [P11_ROOTS, show prodMinus (11 : ℤ) [0, 2, 3, 4, 7, 16] = -110880 from by decide] using
    prodMinus_congr6 hA 0 2 3 4 7 16

/-- `node8` is high EXACTLY on arity 16. -/
theorem node8_high_iff_arity_sixteen {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) :
    (env.loc CHIP_NODE8 ≡ 1 [ZMOD 2013265921]) ↔ (env.loc CHIP_ARITY ≡ 16 [ZMOD 2013265921]) := by
  have hpin := sel_gate h (b := gNode8Pin) (by simp [chipSelectorBodies])
  have hforce := sel_gate h (b := gNode8Force) (by simp [chipSelectorBodies])
  rw [show gNode8Pin = TExpr.mul (v CHIP_NODE8) (eSub eArity (k 16)) from rfl,
    gPin_eval] at hpin
  rw [show gNode8Force = TExpr.mul (eProdMinus eArity P16_ROOTS) (eOneMinus (v CHIP_NODE8))
        from rfl, gForce_eval] at hforce
  refine flag_exact (q := 1572480) hpin hforce (fun hA => ?_)
    (not_dvd_small (by norm_num) (by norm_num))
  simpa [P16_ROOTS, show prodMinus (16 : ℤ) [0, 2, 3, 4, 7, 11] = 1572480 from by decide] using
    prodMinus_congr6 hA 0 2 3 4 7 11

/-! ### §7.3 — The arity membership: TRUE over residues, REFUTED over the integers.

The gate is a degree-7 product over a FIELD, so it has EXACTLY the seven declared roots and no
others — no extra roots are admitted, which is the interesting half of the question. But the roots
are RESIDUE classes, and the comment reads as a claim about the column's value. §7.3b exhibits an
accepted row whose `arity` column holds `2013265921`. -/

/-- **TRUE, over residues.** An accepting row's arity is congruent to one of the seven declared
values — and to nothing else. Primality is what rules out extra roots. -/
theorem arity_in_declared_set {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) :
    ∃ c ∈ ARITIES, env.loc CHIP_ARITY ≡ c [ZMOD 2013265921] := by
  have hg := sel_gate h (b := gArityMember) (by simp [chipSelectorBodies])
  rw [gArityMember_eval, Int.modEq_zero_iff_dvd] at hg
  simp only [prodMinus, ARITIES, List.foldl, sub_zero] at hg
  rcases pPrimeInt.dvd_mul.mp hg with hg | hd
  · rcases pPrimeInt.dvd_mul.mp hg with hg | hd
    · rcases pPrimeInt.dvd_mul.mp hg with hg | hd
      · rcases pPrimeInt.dvd_mul.mp hg with hg | hd
        · rcases pPrimeInt.dvd_mul.mp hg with hg | hd
          · rcases pPrimeInt.dvd_mul.mp hg with hg | hd
            · exact ⟨0, by simp [ARITIES], (Int.modEq_zero_iff_dvd).mpr hg⟩
            · exact ⟨2, by simp [ARITIES], modEq_of_dvd_sub hd⟩
          · exact ⟨3, by simp [ARITIES], modEq_of_dvd_sub hd⟩
        · exact ⟨4, by simp [ARITIES], modEq_of_dvd_sub hd⟩
      · exact ⟨7, by simp [ARITIES], modEq_of_dvd_sub hd⟩
    · exact ⟨11, by simp [ARITIES], modEq_of_dvd_sub hd⟩
  · exact ⟨16, by simp [ARITIES], modEq_of_dvd_sub hd⟩

/-! ### §7.4 — TRUE: `seed456 ∈ {0,1}` — but NOT for the stated reason.

The Rust comment says *"at most one flag is high — the membership gate forces distinct arity values
7/11/16"*. The membership gate is NOT used below: the three `flag·(arity − c)` PINS alone do it,
via `flag_high_imp_arity`. Crediting the membership gate is wrong, and it matters, because it is the
gate a future narrowing of the arity set would touch. -/

/-- At most one selector flag is high, so `seed456` is boolean. -/
theorem seed456_is_boolean {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) :
    (eSeed456.evalWith #[] env ≡ 0 [ZMOD 2013265921]) ∨
    (eSeed456.evalWith #[] env ≡ 1 [ZMOD 2013265921]) := by
  have hbb := bool_of_gate (x := env.loc CHIP_BIG) (by
    simpa [gBigBool, gBool_eval] using
      (sel_gate h (b := gBigBool) (by simp [chipSelectorBodies])))
  have hwb := bool_of_gate (x := env.loc CHIP_WIDE) (by
    simpa [gWideBool, gBool_eval] using
      (sel_gate h (b := gWideBool) (by simp [chipSelectorBodies])))
  have hnb := bool_of_gate (x := env.loc CHIP_NODE8) (by
    simpa [gNode8Bool, gBool_eval] using
      (sel_gate h (b := gNode8Bool) (by simp [chipSelectorBodies])))
  have hbp := sel_gate h (b := gBigPin) (by simp [chipSelectorBodies])
  have hwp := sel_gate h (b := gWidePin) (by simp [chipSelectorBodies])
  have hnp := sel_gate h (b := gNode8Pin) (by simp [chipSelectorBodies])
  rw [show gBigPin = TExpr.mul (v CHIP_BIG) (eSub eArity (k 7)) from rfl, gPin_eval] at hbp
  rw [show gWidePin = TExpr.mul (v CHIP_WIDE) (eSub eArity (k 11)) from rfl,
    gPin_eval] at hwp
  rw [show gNode8Pin = TExpr.mul (v CHIP_NODE8) (eSub eArity (k 16)) from rfl,
    gPin_eval] at hnp
  -- ⚑ ONLY the three `flag·(arity − c)` PINS are used below. The membership gate, which the Rust
  -- comment credits, is never touched: two high flags already force two distinct arity residues.
  have clash : ∀ {c d : ℤ}, env.loc CHIP_ARITY ≡ c [ZMOD 2013265921] →
      env.loc CHIP_ARITY ≡ d [ZMOD 2013265921] → (c - d).natAbs < 2013265921 → c = d := by
    intro c d hc hd hlt
    by_contra hne
    exact not_dvd_small (sub_ne_zero.mpr hne) hlt (dvd_sub_of_modEq (hc.symm.trans hd))
  have heval : eSeed456.evalWith #[] env
      = env.loc CHIP_BIG + env.loc CHIP_WIDE + env.loc CHIP_NODE8 := by
    simp only [eSeed456, eBig, eWide, eNode8, v, TExpr.evalWith]
  rw [heval]
  rcases hbb with hb | hb <;> rcases hwb with hw | hw <;> rcases hnb with hn | hn
  · exact Or.inl (by simpa using (hb.add hw).add hn)
  · exact Or.inr (by simpa using (hb.add hw).add hn)
  · exact Or.inr (by simpa using (hb.add hw).add hn)
  · exact absurd (clash (flag_high_imp_arity hwp hw) (flag_high_imp_arity hnp hn) (by decide))
      (by decide)
  · exact Or.inr (by simpa using (hb.add hw).add hn)
  · exact absurd (clash (flag_high_imp_arity hbp hb) (flag_high_imp_arity hnp hn) (by decide))
      (by decide)
  · exact absurd (clash (flag_high_imp_arity hbp hb) (flag_high_imp_arity hwp hw) (by decide))
      (by decide)
  · exact absurd (clash (flag_high_imp_arity hbp hb) (flag_high_imp_arity hwp hw) (by decide))
      (by decide)

/-! ### §7.5 — TRUE: the `q01` cancellation cancels, on every arity. -/

/-- `q01` is nonzero at EXACTLY one declared arity — the pad/fact arity 0 — and its value there is
the literal the Rust subtracts. Both halves derived, neither transcribed. -/
theorem q01_at_every_arity :
    ARITIES.map (fun a => prodMinus a Q01_ROOTS) = [Q01_PAD, 0, 0, 0, 0, 0, 0] := by decide

/-- A fact row carries arity 0 — the gate that makes no hybrid absorb/fact state expressible. -/
theorem fact_row_has_arity_zero {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) (hf : env.loc CHIP_IS_FACT ≡ 1 [ZMOD 2013265921]) :
    env.loc CHIP_ARITY ≡ 0 [ZMOD 2013265921] := by
  have hg := sel_gate h (b := gFactArity) (by simp [chipSelectorBodies])
  rw [gFactArity_eval, Int.modEq_zero_iff_dvd] at hg
  rcases pPrimeInt.dvd_mul.mp hg with hd | hd
  · exfalso
    have h1 : (1 : ℤ) ≡ 0 [ZMOD 2013265921] := hf.symm.trans ((Int.modEq_zero_iff_dvd).mpr hd)
    exact not_dvd_small (by norm_num) (by norm_num) ((Int.modEq_zero_iff_dvd).mp h1)
  · exact (Int.modEq_zero_iff_dvd).mpr hd

/-- **THE CANCELLATION CANCELS.** On a fact row the whole `q01` guard vanishes, so `in0`/`in1` are
FREE there — which is what lets a fact row carry `l` and `r`. -/
theorem q01_guard_vanishes_on_fact_rows {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) (hf : env.loc CHIP_IS_FACT ≡ 1 [ZMOD 2013265921]) :
    eQ01Guard.evalWith #[] env ≡ 0 [ZMOD 2013265921] := by
  have hA := fact_row_has_arity_zero h hf
  rw [eQ01Guard_eval]
  have h1 : prodMinus (env.loc CHIP_ARITY) Q01_ROOTS ≡ Q01_PAD [ZMOD 2013265921] := by
    simpa [Q01_ROOTS, show prodMinus (0 : ℤ) [2, 3, 4, 7, 11, 16] = Q01_PAD from by decide] using
      prodMinus_congr6 hA 2 3 4 7 11 16
  have h2 : Q01_PAD * env.loc CHIP_IS_FACT ≡ Q01_PAD * 1 [ZMOD 2013265921] :=
    Int.ModEq.mul_left _ hf
  simpa using h1.sub h2

/-- …and on a PAD row (arity 0, not a fact) it does NOT vanish, so `in0`/`in1` are forced to zero.
The two poles of the same guard — a cancellation that cancelled everywhere would be a hole. -/
theorem pad_row_zeroes_in0_and_in1 {env : TRowEnv} {f l : Bool}
    (h : chipSelectorTable.RowHolds env f l) (hf : env.loc CHIP_IS_FACT ≡ 0 [ZMOD 2013265921])
    (hA : env.loc CHIP_ARITY ≡ 0 [ZMOD 2013265921]) :
    env.loc CHIP_IN0 ≡ 0 [ZMOD 2013265921] ∧
    env.loc (CHIP_IN0 + 1) ≡ 0 [ZMOD 2013265921] := by
  have hguard : eQ01Guard.evalWith #[] env ≡ Q01_PAD [ZMOD 2013265921] := by
    rw [eQ01Guard_eval]
    have h1 : prodMinus (env.loc CHIP_ARITY) Q01_ROOTS ≡ Q01_PAD [ZMOD 2013265921] := by
      simpa [Q01_ROOTS, show prodMinus (0 : ℤ) [2, 3, 4, 7, 11, 16] = Q01_PAD from by decide] using
        prodMinus_congr6 hA 2 3 4 7 11 16
    have h2 : Q01_PAD * env.loc CHIP_IS_FACT ≡ Q01_PAD * 0 [ZMOD 2013265921] :=
      Int.ModEq.mul_left _ hf
    simpa using h1.sub h2
  have step : ∀ (i : Nat), i < 2 → env.loc (CHIP_IN0 + i) ≡ 0 [ZMOD 2013265921] := by
    intro i hi
    have hg := sel_inputZero h i (by simp only [CHIP_NODE8_ARITY]; omega)
    rw [show gInputZero i = TExpr.mul (v (CHIP_IN0 + i)) eQ01Guard from by
      simp [gInputZero, hi], TExpr.evalWith] at hg
    rw [Int.modEq_zero_iff_dvd] at hg
    rcases pPrimeInt.dvd_mul.mp hg with hd | hd
    · simpa [v, TExpr.evalWith] using (Int.modEq_zero_iff_dvd).mpr hd
    · exact absurd ((Int.modEq_zero_iff_dvd).mp (hguard.symm.trans
        ((Int.modEq_zero_iff_dvd).mpr hd)))
        (not_dvd_small (by decide) (by decide))
  exact ⟨step 0 (by norm_num), step 1 (by norm_num)⟩

/-! ### §7.6 — TRUE: a forged output lane is UNSAT (the anti-laundering crux). -/

/-- Each output lane is bound to the FINAL aux block — the permutation's own already-constrained
output — and not to a free column or a copy of lane 0. -/
theorem out_binds_final_aux (i : Nat) :
    chipOutBodies.getD i (k 0) = eSub (v (CHIP_OUT + i)) (v (CHIP_AUX0 + 336 + i))
      ∨ CHIP_OUT_LANES ≤ i := by
  by_cases hi : i < CHIP_OUT_LANES
  · left
    have : chipOutBodies.getD i (k 0)
        = eSub (v (CHIP_OUT + i)) (Dregg2.Circuit.Emit.Poseidon2RoundGates.permOutLane CHIP_AUX0 i) := by
      simp [chipOutBodies, List.getD, hi]
    rw [this]; rfl
  · exact Or.inr (by omega)

/-- **THE ANTI-LAUNDERING CRUX.** A witness whose `out[i]` is not the permutation's `i`-th final
lane is refused by the EMITTED table. Stated over `chipTable` (not the sub-table) via
`out_of_chip`. -/
theorem forged_out_lane_is_unsat {env : TRowEnv} {f l : Bool} (i : Nat) (hi : i < CHIP_OUT_LANES)
    (hne : ¬ (env.loc (CHIP_OUT + i) ≡ env.loc (CHIP_AUX0 + 336 + i) [ZMOD 2013265921])) :
    ¬ chipTable.RowHolds env f l := by
  intro h
  refine hne ?_
  have hg := out_of_chip h (gAll (eSub (v (CHIP_OUT + i))
      (Dregg2.Circuit.Emit.Poseidon2RoundGates.permOutLane CHIP_AUX0 i)))
    (List.mem_map_of_mem (List.mem_map_of_mem (List.mem_range.mpr hi)))
  have : (eSub (v (CHIP_OUT + i))
      (Dregg2.Circuit.Emit.Poseidon2RoundGates.permOutLane CHIP_AUX0 i)).evalWith #[] env
      ≡ 0 [ZMOD 2013265921] := hg
  rw [show (Dregg2.Circuit.Emit.Poseidon2RoundGates.permOutLane CHIP_AUX0 i)
      = v (CHIP_AUX0 + 336 + i) from rfl] at this
  simp only [eSub, v, TExpr.evalWith] at this
  have := (Int.modEq_zero_iff_dvd).mp this
  exact modEq_of_dvd_sub (by simpa [sub_eq_add_neg] using this)

/-! ### §7.7 — The `ChipState16` pin, and ⚑ THE DEAD MULTIPLICITY FACTOR. -/

/-- **On a ZERO-multiplicity row the state16 pin forces NOTHING** — not even mod `p`: the body is
literally `0`. That is intended (a zero-multiplicity pad stays free to be the arity-0 chip row), and
it is the answer to "what does it force there": nothing at all. -/
theorem state16_pin_vacuous_at_zero_multiplicity (env : TRowEnv)
    (h : env.loc CHIP_MULT_STATE16 = 0) : gState16Pin.evalWith #[] env = 0 := by
  simp [gState16Pin, eArity, eSub, k, v, TExpr.evalWith, h]

/-- On a NONZERO-multiplicity row it pins arity to 16 — so the fixed length tag cannot be laundered
through a seed-from-zero absorb row. -/
theorem state16_nonzero_mult_forces_arity_sixteen {env : TRowEnv} {f l : Bool}
    (h : chipState16SelectorTable.RowHolds env f l)
    (hm : ¬ (env.loc CHIP_MULT_STATE16 ≡ 0 [ZMOD 2013265921])) :
    env.loc CHIP_ARITY ≡ 16 [ZMOD 2013265921] := by
  have hg := h (gAll gState16Pin) (List.mem_map_of_mem (by simp [chipSelectorBodies]))
  have hg : gState16Pin.evalWith #[] env ≡ 0 [ZMOD 2013265921] := hg
  rw [show gState16Pin = TExpr.mul (v CHIP_MULT_STATE16) (eSub eArity (k 16)) from rfl,
    gPin_eval, Int.modEq_zero_iff_dvd] at hg
  rcases pPrimeInt.dvd_mul.mp hg with hd | hd
  · exact absurd ((Int.modEq_zero_iff_dvd).mpr hd) hm
  · exact modEq_of_dvd_sub hd

/-- ⚑ **THE `(1 − is_fact)` FACTOR ON THE STATE16 BUS IS DEAD.** The Rust guards the state16
multiplicity with `mult_state16 · (1 − is_fact)`. But the gates make `mult_state16 ≢ 0 ∧
is_fact ≡ 1` UNSATISFIABLE — the pin forces arity 16, `is_fact` forces arity 0, and `16 ≢ 0`. So on
every satisfying row the guard equals `mult_state16` exactly and cannot fire. It is not WRONG; it is
a factor that can never do anything, which this repo's own doctrine says not to keep. -/
theorem state16_bus_guard_is_dead {env : TRowEnv} {f l : Bool}
    (h : chipState16SelectorTable.RowHolds env f l)
    (hm : ¬ (env.loc CHIP_MULT_STATE16 ≡ 0 [ZMOD 2013265921])) :
    env.loc CHIP_IS_FACT ≡ 0 [ZMOD 2013265921] ∧
    (TExpr.mul (v CHIP_MULT_STATE16) (eOneMinus eIsFact)).evalWith #[] env
      ≡ env.loc CHIP_MULT_STATE16 [ZMOD 2013265921] := by
  have h16 := state16_nonzero_mult_forces_arity_sixteen h hm
  have hfb0 : gIsFactBool.evalWith #[] env ≡ 0 [ZMOD 2013265921] :=
    h (gAll gIsFactBool) (List.mem_map_of_mem (by simp [chipSelectorBodies]))
  have hfb := bool_of_gate (x := env.loc CHIP_IS_FACT) (by
    simpa [gIsFactBool, gBool_eval] using hfb0)
  have hf0 : env.loc CHIP_IS_FACT ≡ 0 [ZMOD 2013265921] := by
    rcases hfb with h0 | h1
    · exact h0
    · exfalso
      have hga := h (gAll gFactArity) (List.mem_map_of_mem (by simp [chipSelectorBodies]))
      have hga : gFactArity.evalWith #[] env ≡ 0 [ZMOD 2013265921] := hga
      rw [gFactArity_eval, Int.modEq_zero_iff_dvd] at hga
      have hA0 : env.loc CHIP_ARITY ≡ 0 [ZMOD 2013265921] := by
        rcases pPrimeInt.dvd_mul.mp hga with hd | hd
        · exact absurd ((Int.modEq_zero_iff_dvd).mp (h1.symm.trans
            ((Int.modEq_zero_iff_dvd).mpr hd))) (not_dvd_small (by norm_num) (by norm_num))
        · exact (Int.modEq_zero_iff_dvd).mpr hd
      have h16_0 : (16 : ℤ) ≡ 0 [ZMOD 2013265921] := h16.symm.trans hA0
      exact not_dvd_small (q := (16 : ℤ)) (by norm_num) (by norm_num)
        ((Int.modEq_zero_iff_dvd).mp h16_0)
  refine ⟨hf0, ?_⟩
  simp only [eOneMinus, eSub, eIsFact, k, v, TExpr.evalWith]
  have : env.loc CHIP_MULT_STATE16 * (1 + -1 * env.loc CHIP_IS_FACT)
      ≡ env.loc CHIP_MULT_STATE16 * (1 + -1 * 0) [ZMOD 2013265921] :=
    Int.ModEq.mul_left _ (Int.ModEq.add_left _ (Int.ModEq.mul_left _ hf0))
  simpa using this

/-! ## §8 — NON-VACUITY: both poles, decided against the EMITTED gates.

`selRow` covers the 33 columns the selector gates read (a `getD`-defaulted row is zero past its
end), so these are kernel `decide`s against `chipSelectorTable`, whose gates ARE the emitted ones
(`chipTable_gates_split`). The whole-table poles, which the kernel cannot carry, are in §9. -/

/-- A row of the columns the SELECTOR gates read: `[arity, ins(16), out(8)=0, mult=0, is_fact, big,
S4, S5, S6, wide, node8]`. -/
def selRow (arity isFact big s4 s5 s6 wide node8 : ℤ) (ins : List ℤ) : List ℤ :=
  arity :: (ins ++ List.replicate CHIP_OUT_LANES 0 ++
    [0, isFact, big, s4, s5, s6, wide, node8])

/-- A row vector, as a window (`nxt`/`pub` unused: this table is row-local). -/
def rowEnv (row : List ℤ) : TRowEnv := ⟨fun c => row.getD c 0, fun _ => 0, fun _ => 0⟩

#guard (selRow 0 0 0 0 0 0 0 0 (List.replicate 16 0)).length == CHIP_NODE8 + 1

/-- TRUE pole — the bare PAD row (arity 0, no flags, every input zero). -/
theorem accepts_pad_row :
    chipSelectorTable.RowHolds (rowEnv (selRow 0 0 0 0 0 0 0 0 (List.replicate 16 0)))
      false false := by decide

/-- TRUE pole — a FACT row: arity 0, `is_fact` high, `in0`/`in1` carrying `l`/`r`, and the marker
seeding `S5 = FACT_MARK`, `S6 = 1`. This is the row the `q01` cancellation exists for. -/
theorem accepts_fact_row :
    chipSelectorTable.RowHolds
      (rowEnv (selRow 0 1 0 0 FACT_MARK 1 0 0 ([5, 9] ++ List.replicate 14 0))) false false := by
  decide

/-- TRUE pole — a RATE-4 absorb: arity 4, lane 4 carrying the arity tag. -/
theorem accepts_rate4_row :
    chipSelectorTable.RowHolds
      (rowEnv (selRow 4 0 0 4 0 0 0 0 ([1, 2, 3, 4] ++ List.replicate 12 0))) false false := by
  decide

/-- TRUE pole — the RATE-8 leaf: arity 7, `big` high, lanes 4..6 seeded from the inputs. -/
theorem accepts_leaf_row :
    chipSelectorTable.RowHolds
      (rowEnv (selRow 7 0 1 5 6 7 0 0 ([1, 2, 3, 4, 5, 6, 7] ++ List.replicate 9 0)))
      false false := by decide

/-- TRUE pole — the WIDE step: arity 11, `wide` high, lanes 7..10 genuinely used. -/
theorem accepts_wide_row :
    chipSelectorTable.RowHolds
      (rowEnv (selRow 11 0 0 5 6 7 1 0
        ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] ++ List.replicate 5 0))) false false := by decide

/-- TRUE pole — the `node8` compression: arity 16, `node8` high, all sixteen lanes free. -/
theorem accepts_node8_row :
    chipSelectorTable.RowHolds
      (rowEnv (selRow 16 0 0 5 6 7 0 1 [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]))
      false false := by decide

/-- FALSE pole — an UNDECLARED arity is refused (the membership gate bites). -/
theorem refuses_arity_five :
    ¬ chipSelectorTable.RowHolds (rowEnv (selRow 5 0 0 5 0 0 0 0 (List.replicate 16 0)))
      false false := by decide

/-- FALSE pole — arity 7 with `big` LOW is refused. ⚑ This is the gate the inverted `p7` comment
describes backwards: `p7` is nonzero HERE, which is what forces `big` high. -/
theorem refuses_arity_seven_with_big_low :
    ¬ chipSelectorTable.RowHolds
        (rowEnv (selRow 7 0 0 7 0 0 0 0 ([1,2,3,4,5,6,7] ++ List.replicate 9 0)))
        false false := by decide

/-- FALSE pole — arity 16 with `node8` LOW is refused. -/
theorem refuses_arity_sixteen_with_node8_low :
    ¬ chipSelectorTable.RowHolds
        (rowEnv (selRow 16 0 0 16 0 0 0 0 [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]))
        false false := by decide

/-- FALSE pole — a PAD row with a nonzero `in0` is refused (the `q01` guard does NOT cancel there). -/
theorem refuses_pad_row_with_dirty_in0 :
    ¬ chipSelectorTable.RowHolds
        (rowEnv (selRow 0 0 0 0 0 0 0 0 (7 :: List.replicate 15 0))) false false := by decide

/-- FALSE pole — a RATE-4 row with junk past the arity is refused (the padTo discipline). -/
theorem refuses_rate4_row_with_dirty_in5 :
    ¬ chipSelectorTable.RowHolds
        (rowEnv (selRow 4 0 0 4 0 0 0 0 ([1,2,3,4,0,9] ++ List.replicate 10 0))) false false := by
  decide

/-- FALSE pole — a FACT row that drops the `FACT_MARK` seeding is refused, so a fact digest cannot
be re-seeded as an ordinary absorb. -/
theorem refuses_fact_row_without_marker :
    ¬ chipSelectorTable.RowHolds
        (rowEnv (selRow 0 1 0 0 0 1 0 0 ([5, 9] ++ List.replicate 14 0))) false false := by decide

/-- FALSE pole — a FACT row with a nonzero arity is refused (no hybrid absorb/fact state). -/
theorem refuses_fact_row_with_arity_four :
    ¬ chipSelectorTable.RowHolds
        (rowEnv (selRow 4 1 0 4 0 0 0 0 ([5, 9] ++ List.replicate 14 0))) false false := by decide

/-! ### §8a — The `ChipState16` pin, both poles.

`selRow` stops at column 32, and `rowEnv` defaults to zero past a row's end, so the state
multiplicity would be zero — i.e. the pin would be vacuous and these would prove nothing.
`selRow16` carries it at its own column (385) instead. -/

/-- A state16 selector row: the selector columns, the aux span (unread by these gates), then the
state multiplicity at `CHIP_MULT_STATE16`. -/
def selRow16 (arity isFact big s4 s5 s6 wide node8 : ℤ) (ins : List ℤ) (multState : ℤ) :
    List ℤ :=
  selRow arity isFact big s4 s5 s6 wide node8 ins ++
    List.replicate (CHIP_MULT_STATE16 - (CHIP_NODE8 + 1)) 0 ++ [multState]

#guard (selRow16 0 0 0 0 0 0 0 0 (List.replicate 16 0) 0).length == CHIP_WIDTH

/-- TRUE pole — arity 16 at a NONZERO state multiplicity. -/
theorem state16_accepts_arity16_at_nonzero_mult :
    chipState16SelectorTable.RowHolds
      (rowEnv (selRow16 16 0 0 5 6 7 0 1 [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] 3))
      false false := by decide

/-- FALSE pole — an arity-4 absorb row at a NONZERO state multiplicity is REFUSED, so the fixed
length tag cannot be laundered through a seed-from-zero absorb row. -/
theorem state16_refuses_arity4_at_nonzero_mult :
    ¬ chipState16SelectorTable.RowHolds
        (rowEnv (selRow16 4 0 0 4 0 0 0 0 ([1,2,3,4] ++ List.replicate 12 0) 3))
        false false := by decide

/-- ⚑ …and the SAME row at ZERO state multiplicity is ACCEPTED. That is the answer to "what does
the pin force on a zero-multiplicity row": NOTHING — a zero-multiplicity pad stays free to be the
genuine arity-0/arity-4 chip row, exactly as the Rust comment says. -/
theorem state16_accepts_arity4_at_zero_mult :
    chipState16SelectorTable.RowHolds
      (rowEnv (selRow16 4 0 0 4 0 0 0 0 ([1,2,3,4] ++ List.replicate 12 0) 0))
      false false := by decide

/-! ### §8b — ⚑ REFUTED: the arity claim is about RESIDUES.

*"arity ∈ {0, 2, 3, 4, 7, 11, 16}"* reads as a claim about the column's VALUE. It is not: the gate
constrains the residue class. Here is an ACCEPTED row whose `arity` column holds `2013265921`,
which is in no sense one of the seven. Nothing is broken by it — the bus matches on field elements
too — but the sentence is false as written, and a future range-check that trusted it would be
checking the wrong thing. -/

/-- The witness. `arity = p ≡ 0`, so it behaves as a pad row and every gate accepts. -/
theorem accepts_arity_equal_to_p :
    chipSelectorTable.RowHolds
      (rowEnv (selRow 2013265921 0 0 2013265921 0 0 0 0 (List.replicate 16 0)))
      false false := by decide

/-- …and `2013265921` is not one of the seven declared arities. -/
theorem p_is_not_a_declared_arity : (2013265921 : ℤ) ∉ ARITIES := by decide

/-! ## §9 — THE WHOLE TABLE, against the KAT-pinned permutation.

⚠ `chipTable` carries 140,850 expression nodes, so a KERNEL `decide` is not viable; these are
`#guard`s over a COMPILED `decide` of the EMITTED `RowHolds` — the same instrument
`Poseidon2BabyBearW16`'s own KATs use, and it fails the build when it goes red. The witnesses are
built from that module's permutation, so an emission that diverged from the deployed hash by one
limb would be caught here. -/

/-- A full chip row: `[arity, ins(16), outs(8), mult, is_fact, big, S4, S5, S6, wide, node8,
aux(352), mult_last]`. -/
def chipRow (arity isFact big s4 s5 s6 wide node8 mult multLast : ℤ)
    (ins outs aux : List ℤ) : List ℤ :=
  arity :: (ins ++ outs ++ [mult, isFact, big, s4, s5, s6, wide, node8] ++ aux ++ [multLast])

/-- An HONEST chip row: given the row's flags, its declared inputs and its 16 SEED lanes, the aux
block is the permutation's own intermediate states and the outputs its final block's first eight
lanes. `S4`/`S5`/`S6` are seed lanes 4/5/6 by construction of the seeding. -/
def honestRow (arity isFact big wide node8 mult multLast : ℤ)
    (ins seed : List Nat) : List ℤ :=
  let outs := (((permBlocks seed).getLastD []).take CHIP_OUT_LANES).map (fun x => (x : ℤ))
  chipRow arity isFact big (seed.getD 4 0 : ℤ) (seed.getD 5 0 : ℤ) (seed.getD 6 0 : ℤ)
    wide node8 mult multLast (ins.map (fun x => (x : ℤ))) outs (permAuxWitness seed)

/-- The honest `node8` compression row (arity 16, all sixteen lanes genuine). -/
def honestNode8Row : List ℤ :=
  let ins : List Nat := [3,1,4,1,5,9,2,6,5,3,5,8,9,7,9,3]
  honestRow 16 0 0 0 1 1 3 ins ins

/-- The honest FACT row: `state = (l, r, 0, 0, 0, FACT_MARK, 1, 0…)` via the `S4`/`S5`/`S6`
seeding. -/
def honestFactRow : List ℤ :=
  let ins : List Nat := [11, 22] ++ List.replicate 14 0
  honestRow 0 1 0 0 0 1 0 ins ([11, 22, 0, 0, 0, 64207, 1] ++ List.replicate 9 0)

/-- The honest RATE-4 absorb: `state = (in0..in3, arity tag)`. -/
def honestRate4Row : List ℤ :=
  let ins : List Nat := [7, 8, 9, 10] ++ List.replicate 12 0
  honestRow 4 0 0 0 0 1 2 ins ([7, 8, 9, 10, 4, 0, 0] ++ List.replicate 9 0)

/-- The honest RATE-8 leaf (arity 7, `big` high, lanes 4..6 seeded from the inputs). -/
def honestLeafRow : List ℤ :=
  let ins : List Nat := [1,2,3,4,5,6,7] ++ List.replicate 9 0
  honestRow 7 0 1 0 0 1 0 ins ins

/-- The honest WIDE step (arity 11, `wide` high). -/
def honestWideRow : List ℤ :=
  let ins : List Nat := [1,2,3,4,5,6,7,8,9,10,11] ++ List.replicate 5 0
  honestRow 11 0 0 1 0 1 0 ins ins

/-- Does the EMITTED table accept this row? `decide` over `TableAir.RowHolds`, compiled. -/
def rowAccepts (t : TableAir) (row : List ℤ) : Bool :=
  decide (t.RowHolds (rowEnv row) false false)

/-- Bump one column of a row by one — the perturbation the FALSE poles use. -/
def bump (row : List ℤ) (c : Nat) : List ℤ :=
  (List.range row.length).map (fun i => if i = c then row.getD i 0 + 1 else row.getD i 0)

#guard honestNode8Row.length == CHIP_WIDTH
#guard honestFactRow.length == CHIP_WIDTH
#guard honestRate4Row.length == CHIP_WIDTH

-- ⚑ THE TRUE POLE, on the WHOLE emitted table: every one of the 391 gates vanishes on a witness
-- the KAT-pinned permutation produced.
#guard rowAccepts chipTable honestNode8Row
#guard rowAccepts chipTable honestFactRow
#guard rowAccepts chipTable honestRate4Row
#guard rowAccepts chipTable honestLeafRow
#guard rowAccepts chipTable honestWideRow
-- …and the state16 variant accepts the arity-16 row at a NONZERO state multiplicity (3), which is
-- the only setting in which its extra gate is not vacuous.
#guard rowAccepts chipState16Table honestNode8Row
-- ⚠ …but REFUSES the arity-4 row at nonzero state multiplicity — the extra gate is not decoration.
#guard rowAccepts chipState16Table honestRate4Row == false

-- ⚑ THE FALSE POLE. A forged output lane, a perturbed aux limb, a perturbed input, a flipped flag.
#guard rowAccepts chipTable (bump honestNode8Row CHIP_OUT) == false
#guard rowAccepts chipTable (bump honestNode8Row (CHIP_OUT + 7)) == false
#guard rowAccepts chipTable (bump honestNode8Row CHIP_AUX0) == false
#guard rowAccepts chipTable (bump honestNode8Row (CHIP_AUX0 + 176)) == false
#guard rowAccepts chipTable (bump honestNode8Row (CHIP_AUX0 + 336)) == false
#guard rowAccepts chipTable (bump honestNode8Row CHIP_IN0) == false
#guard rowAccepts chipTable (bump honestNode8Row CHIP_NODE8) == false
#guard rowAccepts chipTable (bump honestFactRow CHIP_S5) == false
-- …and the instrument is not always-false: the two MULTIPLICITY columns are genuinely free.
#guard rowAccepts chipTable (bump honestNode8Row CHIP_MULT)
#guard rowAccepts chipTable (bump honestNode8Row CHIP_MULT_NARROW)

/-! ## §10 — The wire pins, and the emission's cost.

The byte length plus the structural pins of §5 fix the emission: any edit to a definition, a gate
body, a tuple, a multiplicity or an offset moves the length, and any edit to the SHAPE moves §5. A
full byte golden is deliberately not inlined — 159 KB of literal would be absurd — so this is a pin,
not an identity. -/

/-- The wire string the Rust interpreter ingests for the chip. -/
def CHIP_JSON : String := emitTableAirJson chipTable
/-- …and for the state16 variant. -/
def CHIP_STATE16_JSON : String := emitTableAirJson chipState16Table

/-- ⚑ The emitted node total: the shared DEFINITIONS plus the gate bodies that read them. -/
def chipNodeTotal : Nat := totalNodes chipDefs + totalNodes (chipGateBodies false)

/-- ⚑ **THE PROVER'S PER-ROW WORK** — field operations, each definition counted ONCE however many
times it is read. This is the number the sharing node exists for; `chipNodeTotal` is a proxy. -/
def chipOpTotal : Nat :=
  (chipDefs.foldl (fun acc b => acc + opCount b) 0) +
  ((chipGateBodies false).foldl (fun acc b => acc + opCount b) 0)

/-- The TREE spelling's node total — the `before`, kept so the win is a ratio of two measured
objects in one file rather than a number quoted from a previous commit. -/
def chipTreeNodeTotal : Nat :=
  totalNodes (chipSelectorBodies false ++ chipPermBodiesTree ++ chipOutBodies)

/-- …and the tree spelling's operation total. -/
def chipTreeOpTotal : Nat :=
  (chipSelectorBodies false ++ chipPermBodiesTree ++ chipOutBodies).foldl
    (fun acc b => acc + opCount b) 0

/-- The hash-consed floor of the tree spelling. -/
def chipDagSize : Nat :=
  Dregg2.Circuit.Emit.Poseidon2RoundGates.dagSize
    (chipSelectorBodies false ++ chipPermBodiesTree ++ chipOutBodies)

-- ⚑ THE COST, BEFORE AND AFTER, both measured here.
#guard chipTreeNodeTotal == 141439
#guard chipTreeOpTotal == 70524
#guard chipDagSize == 3318
#guard chipDefs.length == 1078
#guard chipNodeTotal == 7355
#guard chipOpTotal == 2943
#guard totalNodes chipDefs + totalNodes (chipGateBodies true) == 7362
-- The wins, as ratios rather than as four numbers a reader has to divide.
#guard chipTreeNodeTotal / chipNodeTotal == 19
#guard chipTreeOpTotal / chipOpTotal == 23      -- 70524 / 2943 = 23.96

-- ⚑ WELL-FORMEDNESS OF THE EMITTED DEFINITION LIST. A forward reference or an out-of-range share
-- would make the one-pass resolution wrong; both are refused, here and by the Rust decoder.
#guard chipTable.wellFormed == true
#guard chipState16Table.wellFormed == true
#guard chipTable.defCount == 1078
#guard chipState16Table.defCount == 1078

-- ⚑ THE WIRE PIN. Byte LENGTH plus the structural `#guard`s of §5 (391/392 gates, 3/1 interactions
-- in a fixed per-bus split, width 386, 1078 definitions): any edit to a definition, a gate body, a
-- tuple, a multiplicity or an offset moves the length, and any edit to the SHAPE moves §5.
-- ⚠ 159 KB each, against 3,098,882 / 3,098,539 for the tree spelling — **19.5×**. The wire shrink
-- is the SIDE EFFECT; the point is `chipOpTotal`.
#guard CHIP_JSON.length == 159195
#guard CHIP_STATE16_JSON.length == 158852

/-- The emission is not empty and not a stub — the shape that would satisfy every count pin above
while asserting nothing. -/
theorem chipTable_is_not_empty : chipTable.gates ≠ [] := by
  simp [chipTable, chipGateBodies, chipSelectorBodies]

theorem chipState16Table_is_not_empty : chipState16Table.gates ≠ [] := by
  simp [chipState16Table, chipGateBodies, chipSelectorBodies]

-- ⚑ …and neither is the DEFINITION list DEAD, which a count pin alone would not distinguish from a
-- table that declares a thousand definitions and reads none of them. (`#guard`s: the emitted table
-- is far past what the kernel will reduce, and this file does not use `native_decide` — same
-- instrument as §9's whole-table poles.)
#guard chipTable.defs.isEmpty == false
#guard (chipGateBodies false).any (fun b => b.maxShare != none)
#guard (chipGateBodies true).any (fun b => b.maxShare != none)
-- …and the sharing is REACHED, not merely present: the last definition is read by a gate.
#guard (chipGateBodies false).any (fun b => b.maxShare == some (chipDefs.length - 1))

/-! ## §11 — ⚠ WHAT REMAINS.

**This file closes law #1 for the chip, and the design fork that blocked it is closed too.**

**1. ✅ THE SHARING NODE — DONE (2026-08-02).** `TableAirIR.TExpr` has a `shr` leaf and `TableAir` a
`defs` list; the fork (widen the MAIN descriptor's `WindowExpr` versus give `TableAir` its own
grammar) is decided in `TableAirIR` §1b, on the evidence there. The chip emits **1,078 definitions**
and its per-row work falls from **70,524 field operations to 2,943 — 24.0×** — landing on the
deployed hand-written arm's own op count plus exactly one multiplication per gate (`Poseidon2RoundGates`
§7b). The artifacts are **159 KB** each, not 3.1 MB.

⚠ **The earlier estimate here said "~70 KB"; the measurement says 159 KB.** The estimate assumed a
share reference costs what a column read costs, and `{"t":"shr","i":1077}` is longer than
`{"t":"loc","c":40}`. Said as a correction rather than left to look like a hit.

**2. The integration.** Routing `chipTable` / `chipState16Table` into `EmitTableAirs.lean`, cutting
`circuit/descriptors/table-airs/dregg-ir2-chip{,-state16}-v1.json`, and replacing the
`Ir2Air::Chip | Ir2Air::ChipState16` arm with `Ir2Air::LeanTable`.

**THE FLAG DAY, said out loud.** The table-air WIRE FORMAT gained a `defs` key, so all eight
pre-existing artifacts re-emit (each gaining exactly `,"defs":[]` after its width and changing in no
other byte); two new artifacts land; `air_fingerprint()` and
`verifier_source_closure_fingerprint()` both move because both splice the table-air artifacts whole;
every chip-bearing VK rotates; re-genesis. A table-air JSON in the pre-`defs` grammar now REFUSES to
load. -/

end Dregg2.Circuit.Emit.ChipTableEmit
