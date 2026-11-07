/-
# `Dregg2.Circuit.Emit.Poseidon2RoundGates` — the deployed Poseidon2-w16 permutation's
ROUND-BY-ROUND ARITHMETIZATION, authored in Lean.

## What this is

`circuit/src/plonky3_prover.rs::poseidon2_permute_expr_lanes` is the hand-written Rust gadget every
in-circuit hash in IR-v2 rides through: it emits `(1 + TOTAL_ROUNDS) · 16 = 352` `assert_eq`
constraints binding each round's output to a witness column, and returns the first 8 lanes of the
final state. It is called from `Ir2Air::Chip | Ir2Air::ChipState16`, and — being Rust-authored AIR —
it is exactly what architectural law #1 forbids.

This file is the Lean author of that algebra. `permEmission aux0 base seed` IS the 352 gate bodies
plus the SHARED DEFINITIONS they read, in the Rust emission order; `ChipTableEmit` splices them into
the chip's `TableAir` and the Rust side only INTERPRETS.

## ⚑ TWO EMISSIONS LIVE HERE. `permEmission` (§5b) IS THE DEPLOYED ONE.

`permEmissionNarrow` (§8) is the same permutation committing **141 lanes instead of 352**: an
internal round's fifteen affine lanes and the initial linear layer's sixteen are carried as
EXPRESSIONS rather than columns. Same round algebra, same KATs, same
`max_constraint_degree = 7` (§8c pins the degree on both emitted objects); measured 2.11× prover,
1.28× verifier, 2.34× committed cells at 2^16 permutations. **§8e is the safety argument as
theorems** — each of the 195 dropped internal lanes is a UNIT MULTIPLE of the gate that survives,
the 16 dropped initial lanes are a definition rather than a constraint, and the two equation
systems have the same solutions under the projection. The chip cutover is a flag day; §8g is the
list, and the Rust witness generator is the item that blocks it.

⚠ `permGateBodies` — the TREE spelling of the same 352 polynomials — is kept, and it is NOT emitted.
It is §7's measurement baseline and §6b's agreement oracle: the shared emission is checked against
it gate by gate, so "the DAG denotes the tree" is a computation on both objects rather than a claim
about the emitter.

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every constraint below is a Lean `TExpr`. Nothing here hand-writes a Rust constraint.

## Where the constants come from — and why they are not re-transcribed

`Dregg2.Circuit.Poseidon2BabyBearW16` already holds the round constants
(`rcExtInitial`/`rcInternal`/`rcExtFinal`), the linear layers (`mdsLight`/`internalRound`) and the
S-box, KAT-pinned bit-exact against the deployed Rust permutation
(`default_babybear_poseidon2_16().permute(·)`, three `#guard`s at that file's §6). §2 and §3 below
build the emitter's constant tables FROM THOSE, so there is one transcription of the hex in the
tree, not two.

⚠ The one table that is NOT already in Lean in usable form is the internal diagonal: the Lean
`internalRound` carries its coefficients as SHIFTS (`fhalve`, `fdiv2exp _ 27`), while the emitted
expression needs canonical RESIDUES (`state[i] · V[i]`, the Rust `internal_linear_layer_expr`
shape). §3 therefore transcribes `INTERNAL_DIAG` (`circuit/src/poseidon2.rs:92`) and pins it against
the shift form — two INDEPENDENT sources, not a constant checked against its own definition.

## ⚑ THE COST OF A TREE IR, MEASURED — AND CLOSED. §5b, §6b, §7

The Rust gadget gets its size from EXPRESSION SHARING: within a round the 16 S-boxed values are
`AB::Expr` VALUES referenced 35× each by the linear layer (7 from the `MDSMat4` block plus 28 from
the four column sums), and only the round OUTPUT is rebound to a column. A TREE IR pays that as
literal duplication, and the first pass of this file measured it: **140,850 nodes against a
hash-consed DAG of 3,194 — 44.1×**, 70,249 of them arithmetic, evaluated once per row of the
quotient domain at blow-up 64.

**`TableAirIR.TExpr` now has a `shr` leaf and `TableAir` a `defs` list**, so §5b emits the SAME
polynomials with the SAME sharing the Rust gadget has — value for value, not by a hash-consing pass
over the tree. Each `exp_const_u64::<7>` is four definitions because that is its four
multiplications; each `external_linear_layer_expr` is forty because that is what it holds in
`state` and `sums`. §7 measures both spellings side by side.

## Axiom hygiene
No `sorry`, no new axiom. `#eval` appears only in §7, as MEASUREMENT — never as evidence for a
claim.

⚠ **§8 DOES use `native_decide`, and says so with `#assert_compiled` on every one.** §1–§7 are
kernel-clean; §8's counts, layout tiling, degree, KAT agreement, teeth and model differential are
compiled evaluation — the same engine the `#guard`s above run on, named rather than silent. §8's
RELATING theorems (`wide_internal_lane_is_a_unit_multiple`, `narrowSat_iff`,
`narrow_accepts_exactly_the_wide_witnesses`, …) are kernel-clean and pinned with `#assert_axioms`.
-/
import Dregg2.Circuit.TableAirIR
import Dregg2.Circuit.Poseidon2BabyBearW16

namespace Dregg2.Circuit.Emit.Poseidon2RoundGates

open Dregg2.Circuit.TableAirIR (TRowEnv)

open Dregg2.Circuit.TableAirIR (TExpr v k eSub shareVals)
open Dregg2.Circuit.TableAirIR.TExpr (sharesBelow)

namespace P2 export Dregg2.Circuit.Poseidon2BabyBearW16 (
  P inv2 fadd fsub fmul fhalve fdiv2exp sbox mat4 mdsLight internalRound externalRound
  rcExtInitial rcExtFinal rcInternal perm compress g) end P2

set_option autoImplicit false

/-! ## §1 — The permutation geometry.

Every number is DERIVED from the two the deployed permutation actually fixes (`WIDTH = 16`,
`EXTERNAL_ROUNDS = 8`, `INTERNAL_ROUNDS = 13`) and `#guard`ed, so a drift moves an arithmetic pin
rather than a comment. Source: `circuit/src/poseidon2.rs:21-30`,
`circuit/src/plonky3_prover.rs:{POSEIDON2_PERM_AUX_COLS, POSEIDON2_WIDTH}`. -/

/-- `WIDTH` — the permutation state width. -/
def WIDTH : Nat := 16
/-- `EXTERNAL_ROUNDS` — full rounds, split half before / half after the internal block. -/
def EXTERNAL_ROUNDS : Nat := 8
/-- `HALF_EXTERNAL`. -/
def HALF_EXTERNAL : Nat := EXTERNAL_ROUNDS / 2
/-- `INTERNAL_ROUNDS` — partial rounds (S-box on lane 0 only). -/
def INTERNAL_ROUNDS : Nat := 13
/-- `TOTAL_ROUNDS`. -/
def TOTAL_ROUNDS : Nat := EXTERNAL_ROUNDS + INTERNAL_ROUNDS
/-- `ROUND_COLS` — witness columns one round's output costs. -/
def ROUND_COLS : Nat := WIDTH
/-- `POSEIDON2_AUX_COLS` — the whole aux block: the post-initial-linear-layer state plus one
block per round. -/
def POSEIDON2_AUX_COLS : Nat := (TOTAL_ROUNDS + 1) * ROUND_COLS
/-- The S-box exponent. -/
def SBOX_ALPHA : Nat := 7

#guard HALF_EXTERNAL == 4
#guard TOTAL_ROUNDS == 21
#guard POSEIDON2_AUX_COLS == 352

/-- The round index is EXTERNAL exactly on the first and last `HALF_EXTERNAL` rounds — the Rust
gadget's three loops, as one predicate. -/
def isExternalRound (r : Nat) : Bool :=
  decide (r < HALF_EXTERNAL) || decide (HALF_EXTERNAL + INTERNAL_ROUNDS ≤ r)

#guard (List.range TOTAL_ROUNDS).filter isExternalRound == [0, 1, 2, 3, 17, 18, 19, 20]
#guard ((List.range TOTAL_ROUNDS).filter (fun r => !isExternalRound r)).length == INTERNAL_ROUNDS

/-! ## §2 — The round constants, from the KAT-pinned Lean tables.

`compute_round_constants` (`circuit/src/poseidon2.rs:117`) concatenates: the four
`RC_EXT_INIT` rows, then thirteen rows whose ONLY nonzero lane is `rc[0] = RC_INTERNAL[round]`,
then the four `RC_EXT_FINAL` rows. The hex is `Poseidon2BabyBearW16`'s already — that module's
`perm` is `#guard`ed bit-exact against the deployed Rust permutation, so reusing its tables makes
the KAT the source of these constants rather than a second transcription of the same hex. -/

/-- The 21 round-constant rows, in the deployed order. Internal rounds carry a constant on lane 0
and zero elsewhere — the shape `compute_round_constants` builds. -/
def roundConstants : List (List ℤ) :=
  P2.rcExtInitial.map (fun row => row.map (fun x => (x : ℤ))) ++
  P2.rcInternal.map (fun c => (c : ℤ) :: List.replicate (WIDTH - 1) (0 : ℤ)) ++
  P2.rcExtFinal.map (fun row => row.map (fun x => (x : ℤ)))

/-- `rc[r][j]`. -/
def rcAt (r j : Nat) : ℤ := (roundConstants.getD r []).getD j 0

#guard roundConstants.length == TOTAL_ROUNDS
#guard roundConstants.all (fun row => row.length == WIDTH)
-- The internal block really is lane-0-only: rounds 4..16 have fifteen zero lanes.
#guard ((List.range TOTAL_ROUNDS).filter (fun r => !isExternalRound r)).all
  (fun r => ((roundConstants.getD r []).drop 1).all (fun x => x == 0))
-- …and the external rows are NOT (a table that silently zeroed would pass the count pins).
#guard ((List.range TOTAL_ROUNDS).filter isExternalRound).all
  (fun r => ((roundConstants.getD r []).drop 1).any (fun x => x != 0))
-- Boundary values, so a splice at the wrong offset moves a pin.
#guard rcAt 0 0 == 0x69cbb6af
#guard rcAt 3 15 == 0x1e36ea47
#guard rcAt 4 0 == 0x5a8053c0
#guard rcAt 16 0 == 0x241af16d
#guard rcAt 17 0 == 0x7290a80d
#guard rcAt 20 15 == 0x608758b8

/-! ## §3 — The internal diagonal, from TWO independent sources.

`internal_linear_layer_expr` (`circuit/src/plonky3_prover.rs:337`) is
`state[i] ← sum + state[i] · (INTERNAL_DIAG[i] − 1)`, i.e. it needs the canonical RESIDUE of each
`V[i] = d[i] − 1`. `Poseidon2BabyBearW16.internalRound` carries the SAME coefficients in shift form
(`fhalve`, `fdiv2exp _ 8`, …) because that is how p3's specialized BabyBear layer computes them.

So: `internalDiag` transcribes `circuit/src/poseidon2.rs:92`, `Vshift` re-derives the same vector
from the KAT-pinned Lean field arithmetic, and the `#guard` is the AGREEMENT of two independent
sources. A pin of a constant against its own definition would be decoration. -/

/-- `INTERNAL_DIAG` (`circuit/src/poseidon2.rs:92`), canonical residues. -/
def internalDiag : List Nat :=
  [ 2013265920, 2, 3, 1006632962, 4, 5, 1006632961, 2013265919,
    2013265918, 2005401602, 1509949442, 1761607682, 2013265907, 7864321, 125829121, 16 ]

/-- `V[i] = INTERNAL_DIAG[i] − 1` — the coefficient the emitted internal layer multiplies by. -/
def V : List ℤ := internalDiag.map (fun d => (d : ℤ) - 1)

/-- `V[i]`. -/
def vCoef (i : Nat) : ℤ := V.getD i 0

/-- The SAME vector `V`, re-derived from `Poseidon2BabyBearW16`'s shift arithmetic — the form the
KAT'd `internalRound` actually applies: `[−2, 1, 2, ½, 3, 4, −½, −3, −4, 2⁻⁸, ¼, ⅛, 2⁻²⁷, −2⁻⁸,
−1/16, −2⁻²⁷]`, canonicalized. -/
def Vshift : List Nat :=
  [ P2.P - 2, 1, 2, P2.inv2, 3, 4, P2.P - P2.inv2, P2.P - 3, P2.P - 4,
    P2.fdiv2exp 1 8, P2.fdiv2exp 1 2, P2.fdiv2exp 1 3, P2.fdiv2exp 1 27,
    P2.P - P2.fdiv2exp 1 8, P2.P - P2.fdiv2exp 1 4, P2.P - P2.fdiv2exp 1 27 ]

-- ⚑ THE TWO-SOURCE PIN: the Rust residue table and the Lean shift arithmetic agree, lane for lane.
#guard Vshift == internalDiag.map (fun d => d - 1)
#guard V.length == WIDTH
-- …and the shift form is genuinely shift-shaped: these are real inverses, not coincident numbers.
#guard P2.fmul 2 P2.inv2 == 1
#guard P2.fmul 16 (P2.fdiv2exp 1 4) == 1
#guard P2.fmul 256 (P2.fdiv2exp 1 8) == 1
#guard P2.fmul 134217728 (P2.fdiv2exp 1 27) == 1

/-! ## §4 — The expression emitters.

Each mirrors its Rust function OPERATION FOR OPERATION, so the emitted polynomial is the deployed
one and the association order is the deployed one too. (Addition is associative in the polynomial
ring, so a re-association would be sound; matching Rust's is what makes a future byte-identity
claim cheap rather than a re-derivation.) -/

/-- `x ↦ x⁷`, exactly as p3's `exp_const_u64::<7>` builds it (`p3-field/src/field.rs:249`):
`x2 = x·x`, `x3 = x2·x`, `x4 = x2·x2`, result `x3·x4`. Seven leaf copies of `x`, six `mul` nodes —
the duplication §7 measures. -/
def eSbox (x : TExpr) : TExpr :=
  let x2 : TExpr := .mul x x
  let x3 : TExpr := .mul x2 x
  let x4 : TExpr := .mul x2 x2
  .mul x3 x4

/-- Read state lane `i`, `0` past the end (the Lean `g`, so an under-length state is a ZERO lane
rather than a panic — and `#guard`s below fix the lengths so it never fires). -/
def gx (s : List TExpr) (i : Nat) : TExpr := s.getD i (k 0)

/-- `external_linear_layer_expr` (`circuit/src/plonky3_prover.rs:296`): the `MDSMat4` circulant on
each block of four, then the outer column sums. Left-associated exactly as the Rust `s += …` loop
accumulates `sums[k]`. -/
def extLayer (s : List TExpr) : List TExpr :=
  let blk : Nat → TExpr × TExpr × TExpr × TExpr := fun b =>
    let x0 := gx s (4 * b); let x1 := gx s (4 * b + 1)
    let x2 := gx s (4 * b + 2); let x3 := gx s (4 * b + 3)
    let t01 : TExpr := .add x0 x1
    let t23 : TExpr := .add x2 x3
    let t0123 : TExpr := .add t01 t23
    let t01123 : TExpr := .add t0123 x1
    let t01233 : TExpr := .add t0123 x3
    ( .add t01123 t01
    , .add (.add t01123 x2) x2
    , .add t01233 t23
    , .add (.add t01233 x0) x0 )
  let m : Nat → TExpr := fun i =>
    let q := blk (i / 4)
    match i % 4 with
    | 0 => q.1
    | 1 => q.2.1
    | 2 => q.2.2.1
    | _ => q.2.2.2
  let sums : Nat → TExpr := fun r =>
    .add (.add (.add (m r) (m (4 + r))) (m (8 + r))) (m (12 + r))
  (List.range WIDTH).map (fun i => .add (m i) (sums (i % 4)))

/-- `internal_linear_layer_expr` (`circuit/src/plonky3_prover.rs:337`): `sum = Σ state[i]`
(left-associated from `state[0]`, as the Rust `sum +=` loop), then `state[i] = sum + state[i]·V[i]`. -/
def intLayer (s : List TExpr) : List TExpr :=
  let sum : TExpr :=
    (List.range (WIDTH - 1)).foldl (fun acc i => .add acc (gx s (i + 1))) (gx s 0)
  (List.range WIDTH).map (fun i => .add sum (.mul (gx s i) (k (vCoef i))))

/-- One round applied to a state of expressions. External rounds add the row constant to every
lane, S-box every lane, then the external layer; internal rounds touch lane 0 only, then the
diagonal layer. -/
def roundOut (r : Nat) (s : List TExpr) : List TExpr :=
  if isExternalRound r then
    extLayer ((List.range WIDTH).map (fun j => eSbox (.add (gx s j) (k (rcAt r j)))))
  else
    intLayer ((List.range WIDTH).map (fun j =>
      if j = 0 then eSbox (.add (gx s 0) (k (rcAt r 0))) else gx s j))

/-! ## §5 — The 352 gates.

`poseidon2_permute_expr_lanes` walks the aux block in `ROUND_COLS`-sized steps: block 0 is the
POST-INITIAL-LINEAR-LAYER state, block `r+1` the output of round `r`. Each step emits
`assert_eq(state[j], aux[off+j])` — body `state[j] − aux[off+j]` — and then REBINDS
`state[j] := aux[off+j]`, which is why every round's input is a bare column read and the emitted
degree stays at the S-box budget of 7. -/

/-- Aux column of block `b`, lane `j`, for an aux block based at `aux0`. -/
def auxLane (aux0 b j : Nat) : TExpr := v (aux0 + ROUND_COLS * b + j)

/-- The block-`b` state, as the 16 columns the rebinding leaves it at. -/
def auxState (aux0 b : Nat) : List TExpr := (List.range WIDTH).map (auxLane aux0 b)

/-- **THE 352 PERMUTATION GATE BODIES**, in the Rust emission order: the initial linear layer's 16,
then 16 per round for 21 rounds. `seed` is the input state (whatever the calling table seeds its
lanes from); `aux0` is the first aux column. -/
def permGateBodies (aux0 : Nat) (seed : List TExpr) : List TExpr :=
  let init := extLayer seed
  ((List.range WIDTH).map (fun j => eSub (gx init j) (auxLane aux0 0 j))) ++
  ((List.range TOTAL_ROUNDS).flatMap (fun r =>
    let out := roundOut r (auxState aux0 r)
    (List.range WIDTH).map (fun j => eSub (gx out j) (auxLane aux0 (r + 1) j))))

/-- The permutation's exposed output lanes. ⚑ After the FINAL rebind `state[j] := aux[off+j]`, the
returned `state[0..8]` ARE aux columns — which is why the chip's `out[i] − lanes[i]` gates are
equality bindings to a constrained column and not a re-derivation. -/
def permOutLane (aux0 i : Nat) : TExpr := auxLane aux0 TOTAL_ROUNDS i

/-- The FINAL permutation state, all 16 lanes — what `Ir2Air::ChipState16` puts on the wire
(`aux[POSEIDON2_AUX_COLS − WIDTH ..]`). -/
def permFinalState (aux0 : Nat) : List TExpr := auxState aux0 TOTAL_ROUNDS

#guard (permGateBodies 33 (auxState 1000 0)).length == POSEIDON2_AUX_COLS
#guard (permFinalState 33).length == WIDTH
-- The final block really is the last `WIDTH` columns of the aux span. (`TExpr` has no `BEq`,
-- so the pin is on the wire rendering — which is the thing the Rust decoder reads anyway.)
#guard (permOutLane 33 0).toJson == (v (33 + POSEIDON2_AUX_COLS - WIDTH)).toJson
#guard (permFinalState 33).map TExpr.toJson
     == ((List.range WIDTH).map (fun i => v (33 + POSEIDON2_AUX_COLS - WIDTH + i))).map TExpr.toJson

/-! ## §5b — ⚑ **THE SAME 352 GATES, SHARED.** This is what gets emitted.

The emitters below are §4's, re-cut so that every value the Rust gadget holds in a variable is a
`TableAir` DEFINITION rather than a duplicated subtree. The correspondence is deliberate and exact,
because the fidelity claim is that the emitted DAG is the deployed gadget's own sharing:

| Rust (`plonky3_prover.rs`)                      | definitions                       |
|-------------------------------------------------|-----------------------------------|
| `state[j] + rc_f`                                | 16 per external round             |
| `exp_const_u64::<7>` (`x2`,`x3`,`x4`,`x3·x4`)    | 4 per S-boxed lane                |
| `external_linear_layer_expr` (`t*`, `state`, `sums`) | 20 + 16 + 4 = 40 per layer    |
| `internal_linear_layer_expr` (`sum`)             | 1 per internal round              |

⚠ **The S-box is FOUR definitions, not one.** A single definition holding the whole `x³·x⁴` tree is
the same polynomial and the same node count, but it is SIX multiplications instead of four —
`x2` occurs in both `x3` and `x4` and a tree recomputes it. The prover's cost metric is
`opCount`, not `nodeCount`, and this is where the difference between them bites.

⚠ **Every definition list here is in TOPOLOGICAL ORDER by construction** (`TableAir.defsAcyclic`):
each block's definitions reference only strictly earlier indices, which is what makes the
interpreter's single left-to-right pass a resolution rather than a guess. `#guard`s in §5c pin it.

`base` is the index the FIRST definition of an emission receives; a caller that prepends its own
definitions passes its own count. -/

/-- ⚑ The x⁷ S-box as p3's own FOUR multiplications, each a definition:
`x2 = x·x` (`base`), `x3 = x2·x` (`base+1`), `x4 = x2·x2` (`base+2`), `sb = x3·x4` (`base+3`).
Returns the definitions and the expression naming the result. -/
def sboxDefs (base : Nat) (x : TExpr) : List TExpr × TExpr :=
  ( [ .mul x x
    , .mul (.shr base) x
    , .mul (.shr base) (.shr base)
    , .mul (.shr (base + 1)) (.shr (base + 2)) ]
  , .shr (base + 3) )

/-- Definitions one external linear layer costs: 5 temporaries per `MDSMat4` block (20), the 16
chunk-mixed lanes, then the 4 column sums. -/
def EXT_LAYER_DEFS : Nat := 20 + WIDTH + 4

/-- ⚑ `external_linear_layer_expr`, as DEFINITIONS. Layout from `base`:
`+5b+0…4` the block-`b` temporaries `t01,t23,t0123,t01123,t01233`; `+20+i` the chunk-mixed lane `i`
(the value the Rust leaves in `state[i]`); `+36+r` the column sum `sums[r]`. The 16 layer OUTPUTS
are `m[i] + sums[i%4]`, each read once, so they are expressions rather than definitions — exactly
where the Rust stops sharing too. -/
def extLayerDefs (base : Nat) (s : List TExpr) : List TExpr × List TExpr :=
  let tI : Nat → Nat → Nat := fun b i => base + 5 * b + i
  let mI : Nat → Nat := fun i => base + 20 + i
  let sI : Nat → Nat := fun r => base + 20 + WIDTH + r
  let temps : List TExpr := (List.range 4).flatMap (fun b =>
    let x0 := gx s (4 * b); let x1 := gx s (4 * b + 1)
    let x2 := gx s (4 * b + 2); let x3 := gx s (4 * b + 3)
    [ .add x0 x1                                          -- t01
    , .add x2 x3                                          -- t23
    , .add (.shr (tI b 0)) (.shr (tI b 1))                -- t0123
    , .add (.shr (tI b 2)) x1                             -- t01123
    , .add (.shr (tI b 2)) x3 ])                          -- t01233
  let ms : List TExpr := (List.range WIDTH).map (fun i =>
    let b := i / 4
    match i % 4 with
    | 0 => .add (.shr (tI b 3)) (.shr (tI b 0))
    | 1 => .add (.add (.shr (tI b 3)) (gx s (4 * b + 2))) (gx s (4 * b + 2))
    | 2 => .add (.shr (tI b 4)) (.shr (tI b 1))
    | _ => .add (.add (.shr (tI b 4)) (gx s (4 * b))) (gx s (4 * b)))
  let sums : List TExpr := (List.range 4).map (fun r =>
    .add (.add (.add (.shr (mI r)) (.shr (mI (4 + r)))) (.shr (mI (8 + r)))) (.shr (mI (12 + r))))
  ( temps ++ ms ++ sums
  , (List.range WIDTH).map (fun i => .add (.shr (mI i)) (.shr (sI (i % 4)))) )

/-- Definitions one EXTERNAL round costs: the 16 round-constant adds, four per S-boxed lane, then
the external layer. -/
def EXT_ROUND_DEFS : Nat := WIDTH + 4 * WIDTH + EXT_LAYER_DEFS
/-- Definitions one INTERNAL round costs: the lane-0 constant add, its S-box, and the column sum. -/
def INT_ROUND_DEFS : Nat := 1 + 4 + 1

#guard EXT_LAYER_DEFS == 40
#guard EXT_ROUND_DEFS == 120
#guard INT_ROUND_DEFS == 6

/-- ⚑ One round, as `(definitions, the 16 output expressions)`. External rounds add the row constant
to every lane, S-box every lane, then run the external layer; internal rounds touch lane 0 only,
then the diagonal layer — the same split `roundOut` makes, at the same constants. -/
def roundDefs (r base : Nat) (s : List TExpr) : List TExpr × List TExpr :=
  if isExternalRound r then
    let adds : List TExpr := (List.range WIDTH).map (fun j => .add (gx s j) (k (rcAt r j)))
    let sboxes : List TExpr := (List.range WIDTH).flatMap (fun j =>
      (sboxDefs (base + WIDTH + 4 * j) (.shr (base + j))).1)
    let sbOut : List TExpr := (List.range WIDTH).map (fun j => .shr (base + WIDTH + 4 * j + 3))
    let (ld, lo) := extLayerDefs (base + WIDTH + 4 * WIDTH) sbOut
    (adds ++ sboxes ++ ld, lo)
  else
    let a0 : TExpr := .add (gx s 0) (k (rcAt r 0))
    let sboxes : List TExpr := (sboxDefs (base + 1) (.shr base)).1
    let st : List TExpr := (List.range WIDTH).map (fun i =>
      if i = 0 then .shr (base + 4) else gx s i)
    let sumDef : TExpr :=
      (List.range (WIDTH - 1)).foldl (fun acc i => .add acc (gx st (i + 1))) (gx st 0)
    ( a0 :: (sboxes ++ [sumDef])
    , (List.range WIDTH).map (fun i => .add (.shr (base + 5)) (.mul (gx st i) (k (vCoef i)))) )

/-- **THE EMITTED PERMUTATION**: `(definitions, the 352 gate bodies)`, in the Rust emission order,
with the first definition at index `base`. Gate order is `permGateBodies`' exactly — the initial
linear layer's 16, then 16 per round for 21 rounds — so a splice offset moves the same pins. -/
def permEmission (aux0 base : Nat) (seed : List TExpr) : List TExpr × List TExpr :=
  let (initDefs, initOut) := extLayerDefs base seed
  let initGates := (List.range WIDTH).map (fun j => eSub (gx initOut j) (auxLane aux0 0 j))
  let step : (Nat × List TExpr × List TExpr) → Nat → (Nat × List TExpr × List TExpr) :=
    fun st r =>
      let (b, ds, gs) := st
      let (rd, ro) := roundDefs r b (auxState aux0 r)
      ( b + rd.length
      , ds ++ rd
      , gs ++ (List.range WIDTH).map (fun j => eSub (gx ro j) (auxLane aux0 (r + 1) j)) )
  let (_, ds, gs) :=
    (List.range TOTAL_ROUNDS).foldl step (base + initDefs.length, initDefs, initGates)
  (ds, gs)

/-- The definition count of a permutation emission, derived rather than measured: the initial
layer, then eight external rounds and thirteen internal ones. -/
def PERM_DEFS : Nat :=
  EXT_LAYER_DEFS + EXTERNAL_ROUNDS * EXT_ROUND_DEFS + INTERNAL_ROUNDS * INT_ROUND_DEFS

#guard PERM_DEFS == 1078
#guard (permEmission 33 0 ((List.range WIDTH).map (fun i => v (1 + i)))).1.length == PERM_DEFS
#guard (permEmission 33 0 ((List.range WIDTH).map (fun i => v (1 + i)))).2.length
     == POSEIDON2_AUX_COLS
-- …and the gate count is the tree emission's, so a splice cannot lose or gain a constraint.
#guard (permEmission 33 0 ((List.range WIDTH).map (fun i => v (1 + i)))).2.length
     == (permGateBodies 33 ((List.range WIDTH).map (fun i => v (1 + i)))).length

/-! ## §6 — AGREEMENT WITH THE KAT-PINNED PERMUTATION.

The emitted algebra is worthless if it is not the deployed permutation's. `Poseidon2BabyBearW16` is
bit-exact against the deployed Rust hash by three KATs; this section evaluates the EMITTED
EXPRESSIONS on the witness that module's own functions produce, so the emission is checked against
the KAT rather than against a re-reading of the Rust.

⚠ These are `#guard`s, i.e. they are checked by evaluation at elaboration time and fail the build
when they diverge — the same instrument `Poseidon2BabyBearW16`'s KATs use. The FORCING claims (what
an accepting witness implies) are theorems, in `ChipTableEmit`. -/

/-- The 22 intermediate states the deployed permutation passes through: block 0 is the
post-initial-linear-layer state, block `r+1` is round `r`'s output. This is the Lean twin of
`poseidon2_permute_aux_witness` (`circuit/src/plonky3_prover.rs:492`), built out of
`Poseidon2BabyBearW16`'s own round functions so it inherits their KAT. -/
def permBlocks (input : List Nat) : List (List Nat) :=
  let rounds : List (List Nat → List Nat) :=
    P2.rcExtInitial.map (fun rc => P2.externalRound rc) ++
    P2.rcInternal.map (fun c => P2.internalRound c) ++
    P2.rcExtFinal.map (fun rc => P2.externalRound rc)
  rounds.foldl (fun acc f => acc ++ [f (acc.getLastD [])]) [P2.mdsLight input]

/-- The flattened aux witness, `POSEIDON2_AUX_COLS` field values. -/
def permAuxWitness (input : List Nat) : List ℤ :=
  (permBlocks input).flatMap (fun blk => blk.map (fun x => (x : ℤ)))

-- The trace really is 22 blocks and really ends at the KAT-pinned permutation output.
#guard (permBlocks (List.range 16)).length == TOTAL_ROUNDS + 1
#guard (permBlocks (List.range 16)).getLastD [] == P2.perm (List.range 16)
#guard (permBlocks (List.replicate 16 0)).getLastD [] == P2.perm (List.replicate 16 0)
#guard (permAuxWitness (List.range 16)).length == POSEIDON2_AUX_COLS

/-- The row window a permutation witness induces: the input state at `in0`, the aux block at
`aux0`, everything else zero. -/
def permEnv (in0 aux0 : Nat) (input : List Nat) :
    Dregg2.Circuit.TableAirIR.TRowEnv :=
  let inv : List ℤ := input.map (fun x => (x : ℤ))
  let aux : List ℤ := permAuxWitness input
  let loc : Nat → ℤ := fun c =>
    if c < in0 then 0
    else if c < in0 + WIDTH then inv.getD (c - in0) 0
    else if c < aux0 then 0
    else aux.getD (c - aux0) 0
  ⟨loc, fun _ => 0, fun _ => 0⟩

/-- The S-box emitter agrees with the KAT'd `sbox`, and the layer emitters agree with `mdsLight` /
the diagonal half of `internalRound`, on a concrete state. Cheap, and it names WHICH piece moved if
the whole-permutation check below ever goes red. -/
private def katState : List Nat := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3]

private def evalAt (e : TExpr) (s : List Nat) : ℤ :=
  e.evalWith #[] ⟨fun c => (s.getD c 0 : ℤ), fun _ => 0, fun _ => 0⟩ % 2013265921

#guard evalAt (eSbox (v 5)) katState == (P2.sbox (katState.getD 5 0) : ℤ)
#guard ((List.range WIDTH).map (fun i => evalAt (gx (extLayer ((List.range WIDTH).map v)) i) katState))
     == (P2.mdsLight katState).map (fun x => (x : ℤ))

/-- ⚑ **THE WHOLE 352-GATE ARITHMETIZATION ACCEPTS THE KAT-PINNED WITNESS.** Every emitted gate
body vanishes mod `p` on the row the deployed permutation itself produces. This is the check that
the round constants, both linear layers, the S-box, the round SPLIT (4/13/4) and the aux offsets are
all the deployed ones at once — anchored on `Poseidon2BabyBearW16`'s KAT rather than on a re-reading
of the Rust. -/
def permGatesAcceptWitness (in0 aux0 : Nat) (input : List Nat) : Bool :=
  let env := permEnv in0 aux0 input
  (permGateBodies aux0 ((List.range WIDTH).map (fun i => v (in0 + i)))).all
    (fun b => b.evalWith #[] env % 2013265921 == 0)

#guard permGatesAcceptWitness 1 33 (List.range 16)
#guard permGatesAcceptWitness 1 33 (List.replicate 16 0)
#guard permGatesAcceptWitness 1 33 katState

/-- ⚠ NON-VACUITY, the FALSE pole: the arithmetization can go RED. Perturbing ONE aux limb of the
honest witness breaks it. A check that no witness refutes is decoration. -/
def permGatesAcceptPerturbed (in0 aux0 : Nat) (input : List Nat) (col : Nat) : Bool :=
  let base := permEnv in0 aux0 input
  let env : Dregg2.Circuit.TableAirIR.TRowEnv :=
    ⟨fun c => if c == col then base.loc c + 1 else base.loc c, base.nxt, base.prep⟩
  (permGateBodies aux0 ((List.range WIDTH).map (fun i => v (in0 + i)))).all
    (fun b => b.evalWith #[] env % 2013265921 == 0)

-- A bump in the FIRST aux block, in the middle, and in the LAST — each refused.
#guard permGatesAcceptPerturbed 1 33 katState 33 == false
#guard permGatesAcceptPerturbed 1 33 katState (33 + 16 * 11 + 7) == false
#guard permGatesAcceptPerturbed 1 33 katState (33 + 336) == false
-- …and an INPUT bump is refused too (the input is not free once the aux block is fixed).
#guard permGatesAcceptPerturbed 1 33 katState 1 == false
#guard permGatesAcceptPerturbed 1 33 katState 16 == false
-- Sanity that the perturbation instrument is not always-false: a column OUTSIDE the gadget
-- (neither input nor aux) changes nothing.
#guard permGatesAcceptPerturbed 1 33 katState 400 == true

/-! ## §6b — ⚑ THE SHARED EMISSION DENOTES THE TREE EMISSION.

The sharing node is only worth having if the DAG is the SAME 352 polynomials. That is not asserted
here: it is COMPUTED, gate by gate, comparing VALUES rather than verdicts.

⚠ **On the honest witness alone the check would be vacuous** — both spellings evaluate to zero
everywhere, so an emission that dropped every gate would pass. The perturbed rows are the content:
there the values are NONZERO and the two spellings still agree number for number, which no dropped
or re-associated gate would survive. -/

private def measSeed : List TExpr := (List.range WIDTH).map (fun i => v (1 + i))

/-- The 352 gate VALUES of the shared emission on a row window. -/
def sharedGateValues (aux0 : Nat) (env : Dregg2.Circuit.TableAirIR.TRowEnv) : List ℤ :=
  let (ds, gs) := permEmission aux0 0 measSeed
  let sv := shareVals ds env
  gs.map (fun b => b.evalWith sv env % 2013265921)

/-- …and of the TREE emission on the same window. -/
def treeGateValues (aux0 : Nat) (env : Dregg2.Circuit.TableAirIR.TRowEnv) : List ℤ :=
  (permGateBodies aux0 measSeed).map (fun b => b.evalWith #[] env % 2013265921)

/-- The KAT witness, perturbed at one column (`0` = unperturbed). -/
private def bumpEnv (col d : Nat) (input : List Nat) :
    Dregg2.Circuit.TableAirIR.TRowEnv :=
  let base := permEnv 1 33 input
  ⟨fun c => if c == col then base.loc c + (d : ℤ) else base.loc c, base.nxt, base.prep⟩

private def katState' : List Nat := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3]

-- ⚑ AGREEMENT, on the honest witness (all 352 values zero on both sides)…
#guard sharedGateValues 33 (permEnv 1 33 katState') == treeGateValues 33 (permEnv 1 33 katState')
#guard (sharedGateValues 33 (permEnv 1 33 katState')).all (· == 0)
-- …and on FIVE perturbed witnesses, where the values are nonzero and still agree exactly. A
-- dropped, re-associated or mis-shared gate cannot survive these.
#guard sharedGateValues 33 (bumpEnv 40 7 katState') == treeGateValues 33 (bumpEnv 40 7 katState')
#guard (sharedGateValues 33 (bumpEnv 40 7 katState')).any (· != 0)
#guard sharedGateValues 33 (bumpEnv 1 1 katState') == treeGateValues 33 (bumpEnv 1 1 katState')
#guard (sharedGateValues 33 (bumpEnv 1 1 katState')).any (· != 0)
#guard sharedGateValues 33 (bumpEnv 33 3 katState') == treeGateValues 33 (bumpEnv 33 3 katState')
#guard (sharedGateValues 33 (bumpEnv 33 3 katState')).any (· != 0)
#guard sharedGateValues 33 (bumpEnv 200 5 katState') == treeGateValues 33 (bumpEnv 200 5 katState')
#guard (sharedGateValues 33 (bumpEnv 200 5 katState')).any (· != 0)
#guard sharedGateValues 33 (bumpEnv 368 9 katState') == treeGateValues 33 (bumpEnv 368 9 katState')
#guard (sharedGateValues 33 (bumpEnv 368 9 katState')).any (· != 0)
-- ⚠ …and the instrument is not always-true: comparing the shared values against the tree values of
-- a DIFFERENT witness disagrees, so `==` here is discriminating.
#guard (sharedGateValues 33 (bumpEnv 40 7 katState')
        == treeGateValues 33 (permEnv 1 33 katState')) == false

/-- ⚑ THE DEFINITION LIST IS TOPOLOGICALLY ORDERED — the property that makes the interpreter's one
left-to-right pass a resolution rather than a guess, stated over the emitted list. -/
def permDefsAcyclic (aux0 base : Nat) : Bool :=
  ((permEmission aux0 base measSeed).1.zipIdx.all
    (fun p => p.1.sharesBelow (base + p.2)))

#guard permDefsAcyclic 33 0
-- …and at a nonzero splice base, which is the case a table with its own leading definitions hits.
#guard permDefsAcyclic 33 17

/-! ## §7 — ⚑ THE TREE BLOW-UP, MEASURED — AND WHAT THE SHARING NODE BOUGHT.

The tree spelling (`permGateBodies`, §5) duplicates: within one round the 16 S-boxed lanes are each
referenced 35 times by the external linear layer (7 from the `MDSMat4` block plus 28 from the four
column sums), and each S-box is itself seven copies of its argument. The shared spelling
(`permEmission`, §5b) holds exactly what the Rust gadget holds. Both are measured here, on the
emitted objects, and every number is a `#guard`.

|                       | TREE (§5) | SHARED (§5b) | ratio |
|-----------------------|-----------|--------------|-------|
| expression nodes      | 140,850   | **6,766**    | 20.8× |
| **arithmetic ops**    | **70,249**| **2,668**    | **26.3×** |
| definitions           | —         | 1,078        |       |
| gate bodies           | 352       | 352          |       |

⚑ **`opCount` is the number that matters, not `nodeCount`.** The prover evaluates this per row of
the quotient domain at blow-up 64, and what it pays there is field multiplications and additions —
which is why the S-box is FOUR definitions (p3's own `x2,x3,x4,x3·x4`) and not one definition
holding the 13-node tree: same nodes, six multiplications instead of four.

⚑ **AND THE SHARED EMISSION LANDS ON THE DEPLOYED GADGET'S OWN OP COUNT, exactly.** Counted from
`poseidon2_permute_expr_lanes` itself — 8 external rounds at (16 constant adds + 64 S-box
multiplications + 72 linear-layer adds + 16 `assert_eq` subtractions) = 1,344, 13 internal rounds at
(1 + 4 + 15 + 32 + 16) = 884, plus the initial layer's 88 — the Rust arm performs **2,316** field
operations per row. The emission performs **2,668**, and the difference is **exactly 352**: one
multiplication per gate, because `TExpr` encodes `a − b` as `a + (−1)·b` and has no `sub` node.
`352 = POSEIDON2_AUX_COLS`, and that is the whole residual.

⚠ **THE FORK INSIDE THE FORK, ALSO MEASURED.** A sharing node scoped to ONE EXPRESSION (a `let`
inside `TExpr`, sharing within a gate body but not across gates) is the obvious cheaper design and
it does not work: each of a round's 16 gates reads all 16 S-box values, so a per-gate `let` hoists
the same 16 sixteen times. Measured as the sum of the per-gate hash-consed DAGs — which is exactly
what a per-expression `let` can reach — it is **28,064 nodes, 5.0×**, against the table-level
definition list's 20.8×. That is why `defs` sits on `TableAir` and not inside `TExpr`.

⚑ **THIS PARAGRAPH USED TO DECLINE THE CHEAPER ARITHMETIZATION, AND THAT WAS THE MISTAKE.** It read:
*"none of this is a licence to re-arithmetize … a cheaper circuit would be a DIFFERENT circuit."*
True, and not an objection: **§8 lands the different circuit.** `permEmissionNarrow` commits 141
lanes where this one commits 352, at the SAME `max_constraint_degree = 7` (§8c pins both), for a
measured 2.11× prover / 1.28× verifier / 2.34× committed cells. Everything the old paragraph was
protecting is still protected — the round ALGEBRA does not move, §6's KATs carry over unchanged
(§8d replays them on the narrow arm), and §8e proves the 211 dropped lanes carry no constraint the
141 survivors do not.

**Both emissions live here on purpose, and `permEmission` is the DEPLOYED one** — `ChipTableEmit`
splices it, `CHIP_WIDTH` is 386, `CHIP_TABLE_AIR_JSON` carries its 352 gates. The narrow arm is
landed and related, and the cutover is a flag day whose list is §8g; the item that actually blocks
it is the Rust witness generator, which writes 352 values per permutation and would have to write
141. Keeping the wide arm after the cutover would be the two-shapes-that-agree-today error — it
stays only until §8g's list is discharged, and this is the note that says so. -/

/-- Nodes in a `TExpr` tree — the unit the prover's per-row constraint evaluation pays, once
per row of the quotient domain (blow-up 64). -/
def nodeCount : TExpr → Nat
  | .loc _ | .nxt _ | .const _ | .shr _ | .prep _ => 1
  | .add a b => 1 + nodeCount a + nodeCount b
  | .mul a b => 1 + nodeCount a + nodeCount b

/-- Total nodes over a gate-body list. -/
def totalNodes (bs : List TExpr) : Nat := (bs.map nodeCount).foldl (· + ·) 0

/-- The permutation's node total at the chip's geometry — the number §7 is about. -/
def permNodeTotal : Nat := totalNodes (permGateBodies 33 ((List.range WIDTH).map (fun i => v (1 + i))))

-- The measured shape, pinned so a "harmless" re-association of a layer cannot move the prover's
-- cost silently. An EXTERNAL round body is ~14× an INTERNAL one; that ratio IS the finding.
#guard nodeCount (eSbox (v 0)) == 13
#guard permNodeTotal == 140850
#guard totalNodes (permGateBodies 33 ((List.range WIDTH).map (fun i => v (1 + i)))) == 140850

/-- Per-round node totals, so the blow-up is attributable rather than aggregate. -/
def roundNodeTotal (r : Nat) : Nat :=
  totalNodes ((List.range WIDTH).map (fun j =>
    eSub (gx (roundOut r (auxState 33 r)) j) (auxLane 33 (r + 1) j)))

/-- Nodes that are ARITHMETIC — the prover's actual per-row work, leaves excluded. -/
def opCount : TExpr → Nat
  | .loc _ | .nxt _ | .const _ | .shr _ | .prep _ => 0
  | .add a b => 1 + opCount a + opCount b
  | .mul a b => 1 + opCount a + opCount b

/-- ⚑ **THE SHARED-DAG SIZE** — what the SAME polynomial costs with a share/`let` node, measured by
hash-consing the emitted trees bottom-up. The gap between this and `totalNodes` is exactly what a
tree IR pays, and it is the price tag on the design fork §7's closing note names. -/
def dagSize (bs : List TExpr) : Nat := Id.run do
  let mut tbl : Std.HashMap String Nat := {}
  let rec go (e : TExpr) (t : Std.HashMap String Nat) : Nat × Std.HashMap String Nat :=
    match e with
    | .loc c => key s!"L{c}" t
    | .nxt c => key s!"N{c}" t
    | .const z => key s!"K{z}" t
    | .shr i => key s!"S{i}" t
    | .prep c => key s!"P{c}" t
    | .add a b => let (ia, t) := go a t; let (ib, t) := go b t; key s!"+{ia},{ib}" t
    | .mul a b => let (ia, t) := go a t; let (ib, t) := go b t; key s!"*{ia},{ib}" t
  for b in bs do
    let (_, t) := go b tbl
    tbl := t
  return tbl.size
where
  key (s : String) (t : Std.HashMap String Nat) : Nat × Std.HashMap String Nat :=
    match t[s]? with
    | some i => (i, t)
    | none   => let i := t.size; (i, t.insert s i)

/-- The permutation's ARITHMETIC total — the ops a naive tree walk performs per row. -/
def permOpTotal : Nat :=
  (permGateBodies 33 ((List.range WIDTH).map (fun i => v (1 + i)))).foldl
    (fun acc b => acc + opCount b) 0

/-- The permutation's SHARED-DAG size at the chip's geometry. -/
def permDagSize : Nat := dagSize (permGateBodies 33 ((List.range WIDTH).map (fun i => v (1 + i))))

-- ⚑ THE MEASUREMENT, pinned. Every one of these is derived from the emitted trees.
#guard roundNodeTotal 0 == 15728     -- an EXTERNAL round: 16 gates × 983 nodes
#guard roundNodeTotal 4 == 1066      -- an INTERNAL round — 14.8× smaller
#guard roundNodeTotal 20 == 15728    -- the last external round
#guard totalNodes ((List.range WIDTH).map (fun j =>
      eSub (gx (extLayer ((List.range WIDTH).map (fun i => v (1 + i)))) j) (auxLane 33 0 j)))
     == 1168                         -- the initial linear layer, over bare column reads
-- …and those three account for the whole total, so the number is attributable.
#guard 8 * 15728 + 13 * 1066 + 1168 == permNodeTotal
#guard permOpTotal == 70249
-- The SAME polynomial, hash-consed, is 3194 distinct subexpressions — the theoretical floor a
-- perfect DAG would reach. It is quoted as a floor and NOT as this emission's target: §5b shares
-- what the Rust gadget shares, which is a fidelity property, and hash-consing further would share
-- things the deployed arm recomputes.
#guard permDagSize == 3194
#guard permNodeTotal / permDagSize == 44

/-! ### §7b — ⚑ THE SHARED EMISSION, MEASURED AGAINST THE TREE.

Every number in the module header's table, derived from the emitted objects. -/

/-- Nodes in the emitted DEFINITION list. -/
def permSharedDefNodes : Nat := totalNodes (permEmission 33 0 measSeed).1
/-- Nodes in the emitted GATE bodies. -/
def permSharedGateNodes : Nat := totalNodes (permEmission 33 0 measSeed).2
/-- The emission's total node count. -/
def permSharedNodeTotal : Nat := permSharedDefNodes + permSharedGateNodes
/-- ⚑ The emission's ARITHMETIC total — the field operations the prover performs per row, each
definition ONCE however many times it is read. -/
def permSharedOpTotal : Nat :=
  ((permEmission 33 0 measSeed).1.foldl (fun acc b => acc + opCount b) 0) +
  ((permEmission 33 0 measSeed).2.foldl (fun acc b => acc + opCount b) 0)

/-- ⚑ **THE PER-GATE-`let` ALTERNATIVE, PRICED.** The sum of each gate's OWN hash-consed DAG is
exactly what a sharing node scoped to one expression could reach. It is the design that does NOT
work, and this is why. -/
def permPerGateLetTotal : Nat :=
  ((permGateBodies 33 measSeed).map (fun b => dagSize [b])).foldl (· + ·) 0

-- ⚑ THE AFTER MEASUREMENT, pinned.
#guard (permEmission 33 0 measSeed).1.length == 1078
#guard permSharedDefNodes == 3886
#guard permSharedGateNodes == 2880
#guard permSharedNodeTotal == 6766
#guard permSharedOpTotal == 2668
-- The wins, as ratios rather than as two numbers a reader has to divide.
#guard permNodeTotal / permSharedNodeTotal == 20
#guard permOpTotal / permSharedOpTotal == 26
-- ⚑ THE RESIDUAL AGAINST THE DEPLOYED GADGET: 2,316 field operations in
-- `poseidon2_permute_expr_lanes`, 2,668 here, and the gap is ONE MULTIPLICATION PER GATE — the
-- `a + (−1)·b` encoding of `a − b`. Stated as an equation so a drift in either term is visible.
#guard permSharedOpTotal == 2316 + POSEIDON2_AUX_COLS
-- ⚠ …and the per-gate-`let` design reaches only 5.0×, which is the measurement that put `defs` on
-- `TableAir` rather than a `let` inside `TExpr`.
#guard permPerGateLetTotal == 28064
#guard permNodeTotal / permPerGateLetTotal == 5

/-! ## §8 — ⚑⚑ **THE NARROW EMISSION**: the same permutation, 141 committed lanes instead of 352.

§7 used to close by declining this, verbatim — *"a cheaper circuit would be a DIFFERENT circuit"*.
It is a different circuit, and it is the one to run. **211 of the wide arm's 352 committed lanes
(59.9%) carry no nonlinearity at all**, and §8e proves that dropping them drops no constraint:

| block | wide arm | narrow arm | why |
|---|---|---|---|
| initial linear layer | 16 committed | **0** | a linear map of a seed the caller already holds |
| external round ×8 | 16 each | 16 each | S-box on all sixteen lanes — unchanged |
| **internal round ×13** | **16 each** | **1 each** | S-box on lane 0 ONLY; lanes 1..15 are affine |
| | **352** | **141** | |

Measured at 2^16 permutations on matched config (`circuit/tests/poseidon2_virtualization_measure.rs`,
`zkml-research/notes/poseidon2-virtualization.md`): **2.11× prove, 1.28× verify, 1.25× proof bytes,
2.34× committed cells**, at IDENTICAL `max_constraint_degree` — §8b pins the degree at **7 on both
arms**, on the emitted objects. Strictly Pareto; there is no trade to price. Upstream
`p3-poseidon2-air` (rev 82cfad73, `air.rs:259-278`) arithmetizes exactly this way.

## ⚑ WHICH ONE IS DEPLOYED

**`permEmission` (§5b) is deployed.** `ChipTableEmit.chipEmission` splices it, `CHIP_WIDTH` is 386,
and `CHIP_TABLE_AIR_JSON` carries its 352 gates. `permEmissionNarrow` is landed, measured and
related to it here; cutting the chip over is a flag day — see the closing note.

## ⚠ THE SHARING NODE IS A PRECONDITION HERE, NOT AN OPTIMISATION

The wide arm has a TREE spelling (`permGateBodies`) because every round's input is a bare column
read, so the tree is 140,850 nodes and §6b can use it as an agreement oracle. **The narrow arm has
no such spelling.** Its internal-round state is carried as expressions, and one internal round
multiplies a tree state by **16×** (`intLayer` reads all sixteen lanes into `sum` and once more into
lane `i`): measured on the emitted objects, `[1104, 17900, 286670, …]` for zero, one and two
internal rounds (§8b). Thirteen of them is ~5·10^18 nodes. So there is no tree twin to check the
DAG against, and the narrow arm's instruments are §8d's KAT, §8e's theorems and §8f's differential
against the value model instead.

## What is PROVED here, and what is CHECKED

* **§8e is proof, general in the state, the environment and the committed value.** The 195 dropped
  internal lanes are each a UNIT MULTIPLE of the one gate that survives, and the 16 dropped initial
  lanes are a DEFINITION rather than a constraint. Then `narrowSat_iff` /
  `narrow_accepts_exactly_the_wide_witnesses`: the narrow equation system accepts exactly the
  projections of the wide system's accepting assignments.
* **§8b/§8c/§8d/§8f are COMPILED EVALUATION** — `native_decide` + `#assert_compiled`, the same
  engine a `#guard` runs on, said out loud. Counts, layout tiling, degree, KAT agreement, teeth.
* ⚠ **One bridge is NOT closed**: that `permEmissionNarrow`'s literal gate list, resolved through
  `shareVals`, IS the equation system §8e reasons about. The gate bodies read `shr` leaves, and
  tying `shareVals`'s resolution of those indices to `nStateVal` needs a `shareVals` prefix lemma
  plus a fold invariant over the emitter's 21 steps. **That is undone work, not a boundary** — it
  is the next thing to do here. §8f case-checks it on six row windows in the meantime, which is a
  falsifier for an offset or def-index slip and is NOT a proof. -/

/-! ### §8a — the geometry, and the layout that TILES. -/

/-- `NARROW_AUX_COLS` — the aux block the NARROW arm commits: one 16-lane block per EXTERNAL round,
ONE lane per INTERNAL round, and NOTHING for the initial linear layer. -/
def NARROW_AUX_COLS : Nat := EXTERNAL_ROUNDS * WIDTH + INTERNAL_ROUNDS

/-- Committed lanes round `r` costs the narrow arm. -/
def narrowBlockWidth (r : Nat) : Nat := if isExternalRound r then WIDTH else 1

/-- The first aux column of round `r`'s narrow block: the four opening external blocks, then the
thirteen single internal lanes, then the four closing external blocks. -/
def narrowBase (r : Nat) : Nat :=
  if r < HALF_EXTERNAL then WIDTH * r
  else if r < HALF_EXTERNAL + INTERNAL_ROUNDS then WIDTH * HALF_EXTERNAL + (r - HALF_EXTERNAL)
  else WIDTH * HALF_EXTERNAL + INTERNAL_ROUNDS + WIDTH * (r - HALF_EXTERNAL - INTERNAL_ROUNDS)

/-- Aux column of round `r`'s narrow block, lane `j`. -/
def narrowLane (aux0 r j : Nat) : TExpr := v (aux0 + narrowBase r + j)

/-- Round `r`'s narrow block as the sixteen columns the rebinding leaves it at (external rounds). -/
def narrowState (aux0 r : Nat) : List TExpr := (List.range WIDTH).map (narrowLane aux0 r)

theorem narrow_aux_cols_is_141 : NARROW_AUX_COLS = 141 := by rfl
#assert_axioms narrow_aux_cols_is_141

/-- ⚑ **THE LAYOUT TILES `[0, 141)` EXACTLY** — every committed lane of every round lands on its own
column, with no overlap and no gap. A mis-derived `narrowBase` would either alias two rounds onto
one column (a soundness hole invisible to a count) or leave a hole (a wasted column); this is the
pin that sees both, and it is a `decide` in the kernel rather than a compiled evaluation. -/
theorem narrow_blocks_tile :
    ((List.range TOTAL_ROUNDS).flatMap (fun r =>
        (List.range (narrowBlockWidth r)).map (fun j => narrowBase r + j)))
      = List.range NARROW_AUX_COLS := by decide
#assert_axioms narrow_blocks_tile

/-! ### §8b — the emission.

An EXTERNAL round is **`roundDefs` unchanged** — the narrow arm re-uses §5b's emitter verbatim, so
nothing about the full rounds is re-authored. An INTERNAL round is the one that changes: it binds
ONE column (the post-S-box lane 0) and carries the diagonal layer's sixteen outputs as
DEFINITIONS. That is the 16:1, and it is also why the narrow arm has MORE definitions than the wide
one (1,286 against 1,078) while committing 2.5× fewer columns: a definition is a per-row field
operation, a column is a commitment.

⚠ **Lane 0 of the post-layer state is the COMMITTED column, not the S-box expression.** Feeding the
expression forward instead would be the same polynomial and would push the state to degree 7, then
49 at the next round; reading the column keeps every round's input at degree 1 and the whole arm at
degree 7. This is `p3-poseidon2-air`'s `state[0] = partial_round.post_sbox.into()`, and it is what
§8c's degree pin measures. -/

/-- Definitions one INTERNAL round costs the narrow arm: the lane-0 constant add, its four S-box
multiplications, the column sum, and the SIXTEEN diagonal-layer outputs — definitions here because
no column holds them. -/
def INT_ROUND_DEFS_NARROW : Nat := 1 + 4 + 1 + WIDTH

/-- ⚑ One INTERNAL round of the narrow arm, as `(definitions, the ONE gate body, the sixteen output
expressions)`. Layout from `base`: `+0` the constant add, `+1…+4` the S-box, `+5` the column sum,
`+6…+21` the diagonal layer's outputs. `y` is the committed post-S-box lane. -/
def intRoundDefsNarrow (r base : Nat) (s : List TExpr) (y : TExpr) :
    List TExpr × TExpr × List TExpr :=
  let a0 : TExpr := .add (gx s 0) (k (rcAt r 0))
  let sb : List TExpr := (sboxDefs (base + 1) (.shr base)).1
  let st : List TExpr := (List.range WIDTH).map (fun i => if i = 0 then y else gx s i)
  let sumDef : TExpr :=
    (List.range (WIDTH - 1)).foldl (fun acc i => .add acc (gx st (i + 1))) (gx st 0)
  let outs : List TExpr := (List.range WIDTH).map (fun i =>
    .add (.shr (base + 5)) (.mul (gx st i) (k (vCoef i))))
  ( a0 :: (sb ++ (sumDef :: outs))
  , eSub (.shr (base + 4)) y
  , (List.range WIDTH).map (fun i => .shr (base + 6 + i)) )

/-- ⚑ **THE NARROW EMISSION**: `(definitions, the 141 gate bodies)`, in the same round order
`permEmission` uses. The initial linear layer emits NO gate and NO column — its sixteen outputs are
carried into round 0 as expressions. -/
def permEmissionNarrow (aux0 base : Nat) (seed : List TExpr) : List TExpr × List TExpr :=
  let (initDefs, initOut) := extLayerDefs base seed
  let step : (Nat × List TExpr × List TExpr × List TExpr) → Nat →
      (Nat × List TExpr × List TExpr × List TExpr) :=
    fun st r =>
      let (b, ds, gs, s) := st
      if isExternalRound r then
        let (rd, ro) := roundDefs r b s
        ( b + rd.length
        , ds ++ rd
        , gs ++ (List.range WIDTH).map (fun j => eSub (gx ro j) (narrowLane aux0 r j))
        , narrowState aux0 r )
      else
        let (rd, g, ro) := intRoundDefsNarrow r b s (narrowLane aux0 r 0)
        (b + rd.length, ds ++ rd, gs ++ [g], ro)
  let (_, ds, gs, _) :=
    (List.range TOTAL_ROUNDS).foldl step (base + initDefs.length, initDefs, [], initOut)
  (ds, gs)

/-- The narrow emission's definition count, derived: the initial layer, eight external rounds at
`roundDefs`' own cost, thirteen internal rounds at `INT_ROUND_DEFS_NARROW`. -/
def NARROW_PERM_DEFS : Nat :=
  EXT_LAYER_DEFS + EXTERNAL_ROUNDS * EXT_ROUND_DEFS + INTERNAL_ROUNDS * INT_ROUND_DEFS_NARROW

/-- The narrow arm's exposed output lanes — the LAST external block, which is a committed block in
both arms, so `permOutLane`'s meaning is unchanged and only its column index moves. -/
def permOutLaneNarrow (aux0 i : Nat) : TExpr := narrowLane aux0 (TOTAL_ROUNDS - 1) i

/-- The narrow arm's FINAL permutation state, all sixteen lanes. -/
def permFinalStateNarrow (aux0 : Nat) : List TExpr := narrowState aux0 (TOTAL_ROUNDS - 1)

theorem narrow_perm_defs_is_1286 : NARROW_PERM_DEFS = 1286 := by rfl
#assert_axioms narrow_perm_defs_is_1286

/-- ⚑ The emitted shape: 1,286 definitions, **141 gate bodies — one per committed column** — the
definition list in topological order at base 0 and at a nonzero splice base, and the output block
sitting at the last sixteen aux columns. -/
theorem narrow_emission_shape :
    ((permEmissionNarrow 33 0 measSeed).1.length == NARROW_PERM_DEFS) &&
    ((permEmissionNarrow 33 0 measSeed).2.length == NARROW_AUX_COLS) &&
    ((permEmissionNarrow 33 0 measSeed).1.zipIdx.all (fun p => p.1.sharesBelow p.2)) &&
    ((permEmissionNarrow 33 17 measSeed).1.zipIdx.all (fun p => p.1.sharesBelow (17 + p.2))) &&
    ((permOutLaneNarrow 33 0).toJson == (v (33 + NARROW_AUX_COLS - WIDTH)).toJson) &&
    ((permFinalStateNarrow 33).map TExpr.toJson
       == ((List.range WIDTH).map (fun i => v (33 + NARROW_AUX_COLS - WIDTH + i))).map
            TExpr.toJson) = true := by
  native_decide
#assert_compiled narrow_emission_shape

/-! ### §8c — ⚑ MEASURED ON THE EMITTED OBJECTS: the ops, the nodes, and the DEGREE. -/

/-- The DEGREE of an emitted expression in the committed columns, resolving `shr` through a vector
of already-computed definition degrees — the same one-pass resolution `shareVals` uses, and the
Lean twin of the Rust `def_degrees`. -/
def degWith (dv : Array Nat) : TExpr → Nat
  | .loc _ | .nxt _ => 1
  | .const _ | .prep _ => 0
  | .shr i => dv.getD i 0
  | .add a b => max (degWith dv a) (degWith dv b)
  | .mul a b => degWith dv a + degWith dv b

/-- Per-definition degrees, one left-to-right pass. -/
def defDegs (ds : List TExpr) : Array Nat :=
  ds.foldl (fun acc d => acc.push (degWith acc d)) (Array.emptyWithCapacity ds.length)

/-- The maximum degree over an emission's gate bodies — what `max_constraint_degree` reads, and
what fixes the `log_blowup` floor. -/
def maxGateDeg (ds gs : List TExpr) : Nat :=
  let dv := defDegs ds
  gs.foldl (fun acc g => max acc (degWith dv g)) 0

/-- Field operations an emission performs per row: every definition ONCE, plus the gate bodies. -/
def emissionOps (p : List TExpr × List TExpr) : Nat :=
  (p.1.foldl (fun acc b => acc + opCount b) 0) + (p.2.foldl (fun acc b => acc + opCount b) 0)

/-- Nodes an emission holds. -/
def emissionNodes (p : List TExpr × List TExpr) : Nat := totalNodes p.1 + totalNodes p.2

/-- ⚑ **THE DEGREE IS UNCHANGED — 7 ON BOTH ARMS.** This is the whole "strictly Pareto" claim's
load-bearing half: the narrow arm buys 2.5× fewer committed columns at the SAME
`max_constraint_degree`, hence the same `log_blowup ≥ 3` floor and the same FRI ledger. Measured on
the emitted objects rather than argued, because "no degree accumulation" is exactly the property a
virtualization gets wrong. -/
theorem the_degree_is_seven_on_both_arms :
    (maxGateDeg (permEmissionNarrow 33 0 measSeed).1 (permEmissionNarrow 33 0 measSeed).2 == 7) &&
    (maxGateDeg (permEmission 33 0 measSeed).1 (permEmission 33 0 measSeed).2 == 7) = true := by
  native_decide
#assert_compiled the_degree_is_seven_on_both_arms

/-- ⚑ **THE COST, BOTH ARMS, ON THE EMITTED OBJECTS.** 2,246 field operations per row against
2,668 — and the residual law is the wide arm's own: the deployed Rust gadget's counted 2,105
operations for this arithmetization plus **exactly one multiplication per gate** (`TExpr` encodes
`a − b` as `a + (−1)·b`), `141 = NARROW_AUX_COLS`. Stated as an equation so a drift in either term
is visible. -/
theorem narrow_cost_measured :
    (emissionOps (permEmissionNarrow 33 0 measSeed) == 2246) &&
    (emissionOps (permEmissionNarrow 33 0 measSeed) == 2105 + NARROW_AUX_COLS) &&
    (emissionNodes (permEmissionNarrow 33 0 measSeed) == 5919) &&
    (totalNodes (permEmissionNarrow 33 0 measSeed).1 == 4958) &&
    (totalNodes (permEmissionNarrow 33 0 measSeed).2 == 961) &&
    (emissionOps (permEmission 33 0 measSeed) == 2668) = true := by
  native_decide
#assert_compiled narrow_cost_measured

/-- ⚠ **WHY THERE IS NO TREE SPELLING OF THE NARROW ARM.** One internal round applied to a TREE
state multiplies it by ~16 — `intLayer` reads all sixteen lanes into `sum` and each lane once more.
Pinned at zero, one and two internal rounds; thirteen of them is ~5·10^18 nodes, which is why §6b's
tree-vs-DAG oracle has no narrow counterpart and §8f's differential stands in for it. -/
def narrowTreeState : Nat → List TExpr
  | 0 => extLayer measSeed
  | n + 1 => intLayer ((List.range WIDTH).map
      (fun i => if i = 0 then v (900 + n) else gx (narrowTreeState n) i))

theorem the_narrow_tree_spelling_explodes :
    ((List.range 3).map (fun n => totalNodes (narrowTreeState n)) == [1104, 17900, 286670]) = true := by
  native_decide
#assert_compiled the_narrow_tree_spelling_explodes

/-! ### §8d — ⚑ AGREEMENT WITH THE KAT-PINNED PERMUTATION, AND BOTH POLES.

Same instrument §6 uses on the wide arm, on the same `Poseidon2BabyBearW16` KAT: the narrow witness
is the SAME `permBlocks` trace, projected — the eight external blocks whole, and for each internal
round the single post-S-box lane-0 value. -/

/-- The 141 committed values of the narrow arm, projected from the SAME `permBlocks` trace §6 uses.
`P2.sbox (P2.fadd state[0] rc)` is `internalRound`'s own first line, so this is a projection of the
KAT'd permutation and not a second computation of it. -/
def narrowAuxWitness (input : List Nat) : List ℤ :=
  let blks := permBlocks input
  (List.range TOTAL_ROUNDS).flatMap (fun r =>
    if isExternalRound r then (blks.getD (r + 1) []).map (fun x => (x : ℤ))
    else [((P2.sbox (P2.fadd (P2.g (blks.getD r []) 0)
             (P2.rcInternal.getD (r - HALF_EXTERNAL) 0))) : ℤ)])

/-- The row window a narrow permutation witness induces. -/
def narrowEnv (in0 aux0 : Nat) (input : List Nat) : TRowEnv :=
  let inv : List ℤ := input.map (fun x => (x : ℤ))
  let aux : List ℤ := narrowAuxWitness input
  ⟨fun c =>
      if c < in0 then 0
      else if c < in0 + WIDTH then inv.getD (c - in0) 0
      else if c < aux0 then 0
      else aux.getD (c - aux0) 0
  , fun _ => 0, fun _ => 0⟩

/-- The seed a caller at `in0` supplies. -/
def narrowSeed (in0 : Nat) : List TExpr := (List.range WIDTH).map (fun i => v (in0 + i))

/-- The EMITTED narrow arm's verdict on a row window, definitions resolved once. -/
def narrowAcceptsAt (in0 aux0 : Nat) (env : TRowEnv) : Bool :=
  let (ds, gs) := permEmissionNarrow aux0 0 (narrowSeed in0)
  let sv := shareVals ds env
  gs.all (fun b => b.evalWith sv env % 2013265921 == 0)

/-- The honest witness, perturbed at one column. -/
def narrowBumpEnv (in0 aux0 col : Nat) (d : ℤ) (input : List Nat) : TRowEnv :=
  let base := narrowEnv in0 aux0 input
  ⟨fun c => if c == col then base.loc c + d else base.loc c, base.nxt, base.prep⟩

/-- ⚑ **THE WHOLE 141-GATE ARITHMETIZATION ACCEPTS THE KAT-PINNED WITNESS**, on three inputs — and
the witness's last block IS the deployed permutation's output. -/
theorem narrow_gates_accept_the_kat :
    ((narrowAuxWitness (List.range 16)).length == NARROW_AUX_COLS) &&
    narrowAcceptsAt 1 33 (narrowEnv 1 33 (List.range 16)) &&
    narrowAcceptsAt 1 33 (narrowEnv 1 33 (List.replicate 16 0)) &&
    narrowAcceptsAt 1 33 (narrowEnv 1 33 katState) &&
    (((narrowAuxWitness katState).drop (NARROW_AUX_COLS - WIDTH))
       == (P2.perm katState).map (fun x => (x : ℤ))) = true := by
  native_decide
#assert_compiled narrow_gates_accept_the_kat

/-- ⚠ **THE FALSE POLE.** One bumped limb in each region the narrow arm commits — the opening
external block, the first and last of the thirteen single internal lanes, the OUTPUT block, and an
input lane — every one refused. And the instrument is not always-false: a column outside the gadget
changes nothing. ⚑ The internal-lane teeth are the ones that matter: those are the columns whose
fifteen wide siblings no longer exist, and a witness is still pinned there. -/
theorem narrow_gates_refuse_a_forgery :
    (!narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 33 1 katState)) &&
    (!narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 (33 + 64) 1 katState)) &&
    (!narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 (33 + 76) 1 katState)) &&
    (!narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 (33 + 140) 1 katState)) &&
    (!narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 1 1 katState)) &&
    narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 400 1 katState) = true := by
  native_decide
#assert_compiled narrow_gates_refuse_a_forgery

/-! ### §8e — ⚑⚑ **THE RELATING THEOREM.** This is the safety argument, and it is not a comment.

Two halves, both general in the state, the row window and the committed value:

1. **The sixteen wide gates of an internal round are ONE gate, up to units.** Instantiate the wide
   arm's sixteen free columns at what the narrow arm computes for them — `intLayer` of the state
   with lane 0 set to the committed post-S-box value — and the `j`-th wide gate body becomes
   `c_j · δ` where `δ` is the narrow arm's single gate body and `c_j = 1` for `j ≠ 0`, `p − 1` for
   `j = 0`. Both are units mod `p`, so no single wide gate is stronger than the narrow one and all
   sixteen together are not either. **That is 13 × 15 = 195 of the 211.**
2. **The sixteen initial-block gates are a DEFINITION.** They say exactly "these sixteen columns
   equal this linear function of the seed", and nothing else. **That is the remaining 16.**

Then the equation systems: `narrowSat_iff` shows the narrow system's solutions are exactly the
projections of the unique round chain, and `narrow_accepts_exactly_the_wide_witnesses` states it
against an ARBITRARY wide-accepting assignment rather than against the canonical one — so it is not
an ∃-over-a-witness in disguise.

⚠ The value-level round functions here are DEFINED BY EVALUATING §4's emitters on a state of
sixteen numbers (`roundOutVal r xs = evalSt (valEnv xs) (roundOut r varState)`). They are the
emitted algebra's own denotation, not a second transcription of the round. -/

set_option maxRecDepth 8192 in
/-- BabyBear is prime, discharged by `norm_num`. -/
theorem P_prime : Nat.Prime 2013265921 := by norm_num
/-- …and prime over ℤ, the form `Prime.dvd_mul` needs. -/
theorem P_prime_int : Prime (2013265921 : ℤ) := by
  exact_mod_cast Nat.prime_iff_prime_int.mp P_prime

theorem range_WIDTH : List.range WIDTH = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := by rfl
theorem range_WIDTH_pred : List.range (WIDTH - 1)
    = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] := by rfl

/-- A state with lane 0 replaced — the shape both arms feed the diagonal layer. -/
def setL0 (s : List TExpr) (y : TExpr) : List TExpr :=
  (List.range WIDTH).map (fun i => if i = 0 then y else gx s i)

/-- The value an internal round S-boxes: `(state[0] + rc)^7`. The narrow arm commits it; the wide
arm commits the sixteen lanes downstream of it. -/
def intSboxIn (r : Nat) (s : List TExpr) : TExpr := eSbox (.add (gx s 0) (k (rcAt r 0)))

/-- §4's `roundOut`, on an internal round, IS the diagonal layer of the lane-0-substituted state. -/
theorem roundOut_internal (r : Nat) (s : List TExpr) (hr : isExternalRound r = false) :
    roundOut r s = intLayer (setL0 s (intSboxIn r s)) := by
  simp [roundOut, hr, setL0, intSboxIn]

/-- ⚑ `p − 1` is a UNIT: the lane-0 multiplier cancels. Without this the lane-0 wide gate could in
principle be strictly stronger than the narrow one, and the 16:1 would lose information. -/
theorem lane_zero_multiplier_is_a_unit (x : ℤ) :
    (2013265920 : ℤ) * x ≡ 0 [ZMOD 2013265921] ↔ x ≡ 0 [ZMOD 2013265921] := by
  simp only [Int.modEq_zero_iff_dvd]
  constructor
  · intro hd
    rcases (P_prime_int.dvd_mul).mp hd with h1 | h2
    · exact absurd h1 (by decide)
    · exact h2
  · intro hd; exact Dvd.dvd.mul_left hd _
#assert_axioms lane_zero_multiplier_is_a_unit

set_option linter.unnecessarySeqFocus false in
/-- ⚑⚑ **EACH OF THE SIXTEEN WIDE INTERNAL-ROUND GATES IS A SCALAR MULTIPLE OF THE ONE NARROW
GATE**, with the scalar `1` on fifteen lanes and `p − 1` on lane 0. General in `r`, the state `s`,
the committed value `y`, the definition vector and the row window — an identity over ℤ, not a
congruence, so nothing is hidden in a modulus. -/
theorem wide_internal_lane_is_a_unit_multiple
    (r : Nat) (s : List TExpr) (y : TExpr) (sv : Array ℤ) (env : TRowEnv)
    (hr : isExternalRound r = false) (j : Nat) (hj : j < WIDTH) :
    (eSub (gx (roundOut r s) j) (gx (intLayer (setL0 s y)) j)).evalWith sv env
      = (if j = 0 then (2013265920 : ℤ) else 1)
        * (eSub (intSboxIn r s) y).evalWith sv env := by
  rw [roundOut_internal r s hr]
  have hj' : j < 16 := hj
  clear hj
  interval_cases j <;>
    simp [intLayer, setL0, gx, eSub, TExpr.evalWith, vCoef, V, internalDiag,
      range_WIDTH, range_WIDTH_pred, Dregg2.Circuit.TableAirIR.k] <;> ring
#assert_axioms wide_internal_lane_is_a_unit_multiple

/-- ⚑ …hence the narrow arm's ONE internal gate holds exactly when all sixteen of the wide arm's
do. **The 195 dropped lanes carry no constraint the surviving one does not.** -/
theorem narrow_internal_gate_is_the_whole_wide_round
    (r : Nat) (s : List TExpr) (y : TExpr) (sv : Array ℤ) (env : TRowEnv)
    (hr : isExternalRound r = false) :
    (∀ j, j < WIDTH →
        (eSub (gx (roundOut r s) j) (gx (intLayer (setL0 s y)) j)).evalWith sv env
          ≡ 0 [ZMOD 2013265921])
      ↔ (eSub (intSboxIn r s) y).evalWith sv env ≡ 0 [ZMOD 2013265921] := by
  constructor
  · intro h
    have h1 := h 1 (by decide)
    rw [wide_internal_lane_is_a_unit_multiple r s y sv env hr 1 (by decide)] at h1
    simpa using h1
  · intro h j hj
    rw [wide_internal_lane_is_a_unit_multiple r s y sv env hr j hj]
    by_cases hj0 : j = 0
    · subst hj0
      simpa only [if_pos rfl, if_true] using (lane_zero_multiplier_is_a_unit _).mpr h
    · simpa only [if_neg hj0, one_mul] using h
#assert_axioms narrow_internal_gate_is_the_whole_wide_round

/-- ⚑ **THE INITIAL BLOCK IS A DEFINITION, NOT A CONSTRAINT.** Each of the wide arm's sixteen
block-0 gates says exactly "this column equals this linear function of the seed" — so deleting the
columns and the gates together deletes a definition, and the remaining 16 of the 211 are accounted
for. -/
theorem wide_initial_block_is_a_definition
    (seed : List TExpr) (aux0 : Nat) (sv : Array ℤ) (env : TRowEnv) (j : Nat) :
    (eSub (gx (extLayer seed) j) (auxLane aux0 0 j)).evalWith sv env ≡ 0 [ZMOD 2013265921]
      ↔ (gx (extLayer seed) j).evalWith sv env ≡ env.loc (aux0 + j) [ZMOD 2013265921] := by
  simp only [eSub, auxLane, ROUND_COLS, Nat.mul_zero, Nat.add_zero,
    Dregg2.Circuit.TableAirIR.v, TExpr.evalWith, Int.modEq_iff_dvd]
  ring_nf
#assert_axioms wide_initial_block_is_a_definition

/-! #### §8e′ — the two equation systems, and the theorem that they have the same solutions. -/

/-- Columns `0 … WIDTH−1` as a state — what the value-level round functions read. -/
def varState : List TExpr := (List.range WIDTH).map v

/-- The row window assigning `xs` to columns `0 … WIDTH−1` and zero elsewhere. -/
def valEnv (xs : List ℤ) : TRowEnv :=
  ⟨fun c => if c < WIDTH then xs.getD c 0 else 0, fun _ => 0, fun _ => 0⟩

/-- The values a state of expressions takes on a window. -/
def evalSt (env : TRowEnv) (s : List TExpr) : List ℤ := s.map (fun e => e.evalWith #[] env)

/-- The initial linear layer, as a function of sixteen numbers — §4's emitter, evaluated. -/
def extLayerVal (xs : List ℤ) : List ℤ := evalSt (valEnv xs) (extLayer varState)
/-- The diagonal layer, as a function of sixteen numbers. -/
def intLayerVal (xs : List ℤ) : List ℤ := evalSt (valEnv xs) (intLayer varState)
/-- One round, as a function of sixteen numbers. -/
def roundOutVal (r : Nat) (xs : List ℤ) : List ℤ := evalSt (valEnv xs) (roundOut r varState)
/-- The value an internal round commits. -/
def sboxValAt (r : Nat) (xs : List ℤ) : ℤ := (intSboxIn r varState).evalWith #[] (valEnv xs)
/-- Lane-0 substitution, on values. -/
def setL0Val (xs : List ℤ) (z : ℤ) : List ℤ :=
  (List.range WIDTH).map (fun i => if i = 0 then z else xs.getD i 0)

theorem evalSt_getD (env : TRowEnv) (s : List TExpr) (j : Nat) :
    (evalSt env s).getD j 0 = (gx s j).evalWith #[] env := by
  simp only [evalSt, gx, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : s[j]? <;> simp [TExpr.evalWith, Dregg2.Circuit.TableAirIR.k]

theorem gx_rangeW_map (f : Nat → TExpr) (j : Nat) (hj : j < WIDTH) :
    gx ((List.range WIDTH).map f) j = f j := by
  have hj' : j < 16 := hj
  clear hj
  interval_cases j <;> simp [gx, range_WIDTH]

theorem gx_varState (xs : List ℤ) (j : Nat) (hj : j < WIDTH) :
    (gx varState j).evalWith #[] (valEnv xs) = xs.getD j 0 := by
  rw [varState, gx_rangeW_map _ j hj]
  simp [Dregg2.Circuit.TableAirIR.v, TExpr.evalWith, valEnv, hj]

/-- ⚑ Evaluation respects a row window that agrees only MOD `p` — the structural induction that
makes every value-level congruence below a one-liner instead of sixteen `ring`s. -/
theorem evalWith_modEq (sv : Array ℤ) {env env' : TRowEnv}
    (hl : ∀ c, env.loc c ≡ env'.loc c [ZMOD 2013265921])
    (hn : ∀ c, env.nxt c ≡ env'.nxt c [ZMOD 2013265921])
    (hp : ∀ c, env.prep c ≡ env'.prep c [ZMOD 2013265921]) :
    ∀ e : TExpr, e.evalWith sv env ≡ e.evalWith sv env' [ZMOD 2013265921]
  | .loc c => hl c
  | .nxt c => hn c
  | .const z => Int.ModEq.refl z
  | .shr _ => Int.ModEq.refl _
  | .prep c => hp c
  | .add a b => Int.ModEq.add (evalWith_modEq sv hl hn hp a) (evalWith_modEq sv hl hn hp b)
  | .mul a b => Int.ModEq.mul (evalWith_modEq sv hl hn hp a) (evalWith_modEq sv hl hn hp b)

/-- Two states agree in the field the gates are asserted over. -/
def ValEq (a b : List ℤ) : Prop :=
  ∀ j, j < WIDTH → a.getD j 0 ≡ b.getD j 0 [ZMOD 2013265921]

theorem ValEq.refl (a : List ℤ) : ValEq a a := fun _ _ => Int.ModEq.refl _
theorem ValEq.symm {a b : List ℤ} (h : ValEq a b) : ValEq b a := fun j hj => (h j hj).symm
theorem ValEq.trans {a b c : List ℤ} (h : ValEq a b) (h' : ValEq b c) : ValEq a c :=
  fun j hj => (h j hj).trans (h' j hj)

theorem valEnv_modEq {a b : List ℤ} (h : ValEq a b) (c : Nat) :
    (valEnv a).loc c ≡ (valEnv b).loc c [ZMOD 2013265921] := by
  by_cases hc : c < WIDTH
  · simpa [valEnv, hc] using h c hc
  · simp [valEnv, hc]

theorem roundOutVal_congr (r : Nat) {a b : List ℤ} (h : ValEq a b) :
    ValEq (roundOutVal r a) (roundOutVal r b) := by
  intro j _
  rw [roundOutVal, roundOutVal, evalSt_getD, evalSt_getD]
  exact evalWith_modEq #[] (valEnv_modEq h) (fun _ => Int.ModEq.refl _)
    (fun _ => Int.ModEq.refl _) _

theorem intLayerVal_congr {a b : List ℤ} (h : ValEq a b) :
    ValEq (intLayerVal a) (intLayerVal b) := by
  intro j _
  rw [intLayerVal, intLayerVal, evalSt_getD, evalSt_getD]
  exact evalWith_modEq #[] (valEnv_modEq h) (fun _ => Int.ModEq.refl _)
    (fun _ => Int.ModEq.refl _) _

theorem sboxValAt_congr (r : Nat) {a b : List ℤ} (h : ValEq a b) :
    sboxValAt r a ≡ sboxValAt r b [ZMOD 2013265921] :=
  evalWith_modEq #[] (valEnv_modEq h) (fun _ => Int.ModEq.refl _) (fun _ => Int.ModEq.refl _) _

theorem setL0Val_getD (xs : List ℤ) (z : ℤ) (j : Nat) (hj : j < WIDTH) :
    (setL0Val xs z).getD j 0 = if j = 0 then z else xs.getD j 0 := by
  rw [setL0Val]
  have hj' : j < 16 := hj
  clear hj
  interval_cases j <;> simp [range_WIDTH]

theorem setL0Val_congr {a b : List ℤ} {z z' : ℤ} (h : ValEq a b)
    (hz : z ≡ z' [ZMOD 2013265921]) : ValEq (setL0Val a z) (setL0Val b z') := by
  intro j hj
  rw [setL0Val_getD _ _ j hj, setL0Val_getD _ _ j hj]
  by_cases hj0 : j = 0
  · simpa [hj0] using hz
  · simpa [hj0] using h j hj

theorem intLayer_eval_congr {s t : List TExpr} {sv sv' : Array ℤ} {env env' : TRowEnv}
    (h : ∀ i, i < WIDTH → (gx s i).evalWith sv env = (gx t i).evalWith sv' env')
    (j : Nat) (hj : j < WIDTH) :
    (gx (intLayer s) j).evalWith sv env = (gx (intLayer t) j).evalWith sv' env' := by
  simp only [intLayer]
  rw [gx_rangeW_map _ j hj, gx_rangeW_map _ j hj]
  simp only [range_WIDTH_pred, List.foldl_cons, List.foldl_nil, TExpr.evalWith,
    Dregg2.Circuit.TableAirIR.k, h 0 (by decide), h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
    h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide),
    h 13 (by decide), h 14 (by decide), h 15 (by decide), h j hj]

/-- ⚑ An internal round, at the value level, IS the diagonal layer of the lane-0-substituted
state — the fact that lets the narrow arm commit one number where the wide arm commits sixteen. -/
theorem roundOutVal_internal (r : Nat) (xs : List ℤ) (hr : isExternalRound r = false)
    (j : Nat) (hj : j < WIDTH) :
    (roundOutVal r xs).getD j 0 = (intLayerVal (setL0Val xs (sboxValAt r xs))).getD j 0 := by
  rw [roundOutVal, evalSt_getD, roundOut_internal r varState hr, intLayerVal, evalSt_getD]
  refine intLayer_eval_congr ?_ j hj
  intro i hi
  rw [setL0, gx_rangeW_map _ i hi, gx_varState _ i hi, setL0Val_getD _ _ i hi]
  by_cases hi0 : i = 0
  · subst hi0; rfl
  · simp only [if_neg hi0]; exact gx_varState xs i hi

/-- The round chain a seed determines — the WIDE arm's 22 blocks, as values. ⚠ Never evaluate this
at a large `r`: the round function is degree 7 over ℤ with no reduction, so `blocksVal seedv 21`
is an integer with ~10^11 bits. It is a statement-level object. -/
def blocksVal (seedv : List ℤ) : Nat → List ℤ
  | 0 => extLayerVal seedv
  | r + 1 => roundOutVal r (blocksVal seedv r)

/-- The NARROW arm's state entering round `r`, driven by what it actually commits: `ext r` for an
external round's sixteen lanes, `yv r` for an internal round's one. -/
def nStateVal (seedv : List ℤ) (ext : Nat → List ℤ) (yv : Nat → ℤ) : Nat → List ℤ
  | 0 => extLayerVal seedv
  | r + 1 =>
      if isExternalRound r then ext r
      else intLayerVal (setL0Val (nStateVal seedv ext yv r) (yv r))

/-- **The WIDE arm's 352 equations**, as conditions on the 22 committed blocks. -/
def WideSat (seedv : List ℤ) (blk : Nat → List ℤ) : Prop :=
  ValEq (blk 0) (extLayerVal seedv) ∧
  ∀ r, r < TOTAL_ROUNDS → ValEq (blk (r + 1)) (roundOutVal r (blk r))

/-- **The NARROW arm's 141 equations**, as conditions on the eight committed blocks and the
thirteen committed lanes. -/
def NarrowSat (seedv : List ℤ) (ext : Nat → List ℤ) (yv : Nat → ℤ) : Prop :=
  ∀ r, r < TOTAL_ROUNDS →
    (isExternalRound r = true → ValEq (ext r) (roundOutVal r (nStateVal seedv ext yv r))) ∧
    (isExternalRound r = false →
      yv r ≡ sboxValAt r (nStateVal seedv ext yv r) [ZMOD 2013265921])

theorem wideSat_blocksVal (seedv : List ℤ) : WideSat seedv (blocksVal seedv) :=
  ⟨ValEq.refl _, fun _ _ => ValEq.refl _⟩
#assert_axioms wideSat_blocksVal

/-- The wide system has exactly one solution per seed: the round chain. -/
theorem wideSat_iff (seedv : List ℤ) (blk : Nat → List ℤ) :
    WideSat seedv blk ↔ ∀ r, r ≤ TOTAL_ROUNDS → ValEq (blk r) (blocksVal seedv r) := by
  constructor
  · rintro ⟨h0, hs⟩ r
    induction r with
    | zero => intro _; exact h0
    | succ r ih =>
        intro _
        have hr : r < TOTAL_ROUNDS := by omega
        exact (hs r hr).trans (roundOutVal_congr r (ih (by omega)))
  · intro h
    refine ⟨h 0 (by omega), fun r hr => ?_⟩
    exact (h (r + 1) (by omega)).trans (roundOutVal_congr r (h r (by omega)).symm)
#assert_axioms wideSat_iff

private theorem nState_step_internal {seedv : List ℤ} {ext : Nat → List ℤ} {yv : Nat → ℤ}
    {r : Nat} (hf : isExternalRound r = false)
    (ihr : ValEq (nStateVal seedv ext yv r) (blocksVal seedv r))
    (hyv : yv r ≡ sboxValAt r (blocksVal seedv r) [ZMOD 2013265921]) :
    ValEq (intLayerVal (setL0Val (nStateVal seedv ext yv r) (yv r))) (blocksVal seedv (r + 1)) := by
  refine (intLayerVal_congr (setL0Val_congr ihr hyv)).trans ?_
  intro j hj
  simp only [blocksVal]
  rw [roundOutVal_internal r (blocksVal seedv r) hf j hj]

/-- ⚑ **THE 141 EQUATIONS FORCE THE WHOLE 352-VALUE CHAIN.** Nothing is left free by the lanes the
narrow arm stopped committing. -/
theorem narrowSat_forces_the_trace {seedv : List ℤ} {ext : Nat → List ℤ} {yv : Nat → ℤ}
    (h : NarrowSat seedv ext yv) :
    ∀ r, r ≤ TOTAL_ROUNDS → ValEq (nStateVal seedv ext yv r) (blocksVal seedv r) := by
  intro r
  induction r with
  | zero => intro _; exact ValEq.refl _
  | succ r ih =>
      intro _
      have hr : r < TOTAL_ROUNDS := by omega
      have ihr := ih (by omega)
      rw [nStateVal]
      by_cases hx : isExternalRound r = true
      · rw [if_pos hx]; exact ((h r hr).1 hx).trans (roundOutVal_congr r ihr)
      · have hf : isExternalRound r = false := by simpa using hx
        rw [if_neg (by simp [hf])]
        exact nState_step_internal hf ihr (((h r hr).2 hf).trans (sboxValAt_congr r ihr))
#assert_axioms narrowSat_forces_the_trace

theorem nStateVal_of_projection {seedv : List ℤ} {ext : Nat → List ℤ} {yv : Nat → ℤ}
    (hx : ∀ r, r < TOTAL_ROUNDS → isExternalRound r = true →
      ValEq (ext r) (blocksVal seedv (r + 1)))
    (hy : ∀ r, r < TOTAL_ROUNDS → isExternalRound r = false →
      yv r ≡ sboxValAt r (blocksVal seedv r) [ZMOD 2013265921]) :
    ∀ r, r ≤ TOTAL_ROUNDS → ValEq (nStateVal seedv ext yv r) (blocksVal seedv r) := by
  intro r
  induction r with
  | zero => intro _; exact ValEq.refl _
  | succ r ih =>
      intro _
      have hr : r < TOTAL_ROUNDS := by omega
      have ihr := ih (by omega)
      rw [nStateVal]
      by_cases hxb : isExternalRound r = true
      · rw [if_pos hxb]; exact hx r hr hxb
      · have hf : isExternalRound r = false := by simpa using hxb
        rw [if_neg (by simp [hf])]
        exact nState_step_internal hf ihr (hy r hr hf)

/-- ⚑ The narrow system's solutions are EXACTLY the projections of the round chain: the eight
external blocks whole, and one post-S-box value per internal round. -/
theorem narrowSat_iff (seedv : List ℤ) (ext : Nat → List ℤ) (yv : Nat → ℤ) :
    NarrowSat seedv ext yv ↔
      ((∀ r, r < TOTAL_ROUNDS → isExternalRound r = true →
          ValEq (ext r) (blocksVal seedv (r + 1))) ∧
       (∀ r, r < TOTAL_ROUNDS → isExternalRound r = false →
          yv r ≡ sboxValAt r (blocksVal seedv r) [ZMOD 2013265921])) := by
  constructor
  · intro h
    have hstate := narrowSat_forces_the_trace h
    refine ⟨fun r hr hxb => ?_, fun r hr hf => ?_⟩
    · exact ((h r hr).1 hxb).trans (roundOutVal_congr r (hstate r (by omega)))
    · exact ((h r hr).2 hf).trans (sboxValAt_congr r (hstate r (by omega)))
  · rintro ⟨hx, hy⟩
    have hstate := nStateVal_of_projection hx hy
    intro r hr
    refine ⟨fun hxb => ?_, fun hf => ?_⟩
    · exact (hx r hr hxb).trans (roundOutVal_congr r (hstate r (by omega)).symm)
    · exact (hy r hr hf).trans (sboxValAt_congr r (hstate r (by omega)).symm)
#assert_axioms narrowSat_iff

/-- ⚑⚑ **THE RELATING THEOREM.** For ANY assignment the WIDE arm accepts, the NARROW arm accepts a
committed vector exactly when that vector is the wide one's projection — the eight external blocks
kept whole, one post-S-box lane kept per internal round, the initial block and the 195 affine lanes
dropped. Stated against an arbitrary `blk` rather than against the canonical chain, so it is not an
existential over a witness wearing a theorem's clothes. -/
theorem narrow_accepts_exactly_the_wide_witnesses
    (seedv : List ℤ) (blk : Nat → List ℤ) (ext : Nat → List ℤ) (yv : Nat → ℤ)
    (hw : WideSat seedv blk) :
    NarrowSat seedv ext yv ↔
      ((∀ r, r < TOTAL_ROUNDS → isExternalRound r = true → ValEq (ext r) (blk (r + 1))) ∧
       (∀ r, r < TOTAL_ROUNDS → isExternalRound r = false →
          yv r ≡ sboxValAt r (blk r) [ZMOD 2013265921])) := by
  have hb := (wideSat_iff seedv blk).mp hw
  rw [narrowSat_iff]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨fun r hr hxb => (hx r hr hxb).trans (hb (r + 1) (by omega)).symm,
           fun r hr hf => (hy r hr hf).trans (sboxValAt_congr r (hb r (by omega)).symm)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨fun r hr hxb => (hx r hr hxb).trans (hb (r + 1) (by omega)),
           fun r hr hf => (hy r hr hf).trans (sboxValAt_congr r (hb r (by omega)))⟩
#assert_axioms narrow_accepts_exactly_the_wide_witnesses

/-! #### §8e″ — ⚠ BOTH POLES OF THE EQUATION SYSTEMS.

`narrowSat_iff` would read the same if `NarrowSat` were unsatisfiable or trivially true, so both
are exhibited. The refutations probe at round 0 deliberately: `blocksVal` past a few rounds is an
integer with astronomically many bits, so a refutation deeper in the chain is not computable and a
`native_decide` that appeared to do it would be measuring something else. -/

theorem extLayerVal_probe :
    (extLayerVal (1 :: List.replicate 15 (0:ℤ))).getD 0 0 = 4 := by native_decide
#assert_compiled extLayerVal_probe

theorem wideSat_is_refutable :
    ¬ WideSat (1 :: List.replicate 15 (0:ℤ)) (fun _ => []) := by
  intro h
  have h0 := h.1 0 (by decide)
  rw [extLayerVal_probe] at h0
  simp only [List.getD_nil] at h0
  exact absurd h0 (by decide)
#assert_compiled wideSat_is_refutable

theorem roundOutVal_probe :
    (roundOutVal 0 (extLayerVal (1 :: List.replicate 15 (0:ℤ)))).getD 0 0 % 2013265921 ≠ 0 := by
  native_decide
#assert_compiled roundOutVal_probe

theorem narrowSat_is_refutable :
    ¬ NarrowSat (1 :: List.replicate 15 (0:ℤ)) (fun _ => []) (fun _ => 0) := by
  intro h
  have h0 := (h 0 (by decide)).1 (by decide) 0 (by decide)
  simp only [List.getD_nil, nStateVal] at h0
  exact roundOutVal_probe (by simpa [Int.ModEq, Int.zero_emod] using h0.symm)
#assert_compiled narrowSat_is_refutable

theorem narrowSat_is_satisfiable (seedv : List ℤ) :
    NarrowSat seedv (fun r => blocksVal seedv (r + 1)) (fun r => sboxValAt r (blocksVal seedv r)) :=
  (narrowSat_iff seedv _ _).mpr ⟨fun _ _ _ => ValEq.refl _, fun _ _ _ => Int.ModEq.refl _⟩
#assert_axioms narrowSat_is_satisfiable

/-! ### §8f — ⚠ THE UNPROVED BRIDGE, CASE-CHECKED.

§8e reasons about `NarrowSat` — the 141 equations. `permEmissionNarrow` emits 141 gate BODIES whose
content sits in a 1,286-entry definition list that `shareVals` resolves. **That the two are the same
system is not proved here.** It needs a `shareVals` prefix lemma (`foldl` over an append) plus a
fold invariant carrying "round `r`'s definitions start at index `base + Σ earlier`" through the
emitter's 21 steps — real work, not a boundary, and the next thing to do in this file.

Below is the falsifier that stands in for it: the EMITTED arm's verdict and the value model's
verdict, on the honest window and on five perturbed ones. An aux-offset slip, a `narrowBase` error
or a wrong `shr` index moves one and not the other. It is case-testing and it is labelled as such;
it proves nothing about all windows. -/

/-- The value model's verdict on a concrete row window — the same 141 equations, read off the
committed COLUMN VALUES rather than off the emitted gate list. -/
def narrowModelAccepts (in0 aux0 : Nat) (env : TRowEnv) : Bool :=
  let seedv : List ℤ := (List.range WIDTH).map (fun i => env.loc (in0 + i))
  let ext : Nat → List ℤ := fun r =>
    (List.range WIDTH).map (fun j => env.loc (aux0 + narrowBase r + j))
  let yv : Nat → ℤ := fun r => env.loc (aux0 + narrowBase r)
  (List.range TOTAL_ROUNDS).all (fun r =>
    if isExternalRound r then
      (List.range WIDTH).all (fun j =>
        ((ext r).getD j 0 - (roundOutVal r (nStateVal seedv ext yv r)).getD j 0)
          % 2013265921 == 0)
    else
      ((yv r - sboxValAt r (nStateVal seedv ext yv r)) % 2013265921 == 0))

theorem narrow_model_accepts_the_kat :
    narrowModelAccepts 1 33 (narrowEnv 1 33 katState) = true := by native_decide
#assert_compiled narrow_model_accepts_the_kat

/-- The emitted DAG and the value model return the SAME verdict on six row windows — the honest one
and five perturbations, one in each region the narrow arm commits. -/
theorem narrow_emission_agrees_with_the_model :
    (narrowAcceptsAt 1 33 (narrowEnv 1 33 katState)
       == narrowModelAccepts 1 33 (narrowEnv 1 33 katState)) &&
    (narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 33 1 katState)
       == narrowModelAccepts 1 33 (narrowBumpEnv 1 33 33 1 katState)) &&
    (narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 (33 + 64) 3 katState)
       == narrowModelAccepts 1 33 (narrowBumpEnv 1 33 (33 + 64) 3 katState)) &&
    (narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 (33 + 76) 5 katState)
       == narrowModelAccepts 1 33 (narrowBumpEnv 1 33 (33 + 76) 5 katState)) &&
    (narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 (33 + 140) 7 katState)
       == narrowModelAccepts 1 33 (narrowBumpEnv 1 33 (33 + 140) 7 katState)) &&
    (narrowAcceptsAt 1 33 (narrowBumpEnv 1 33 1 1 katState)
       == narrowModelAccepts 1 33 (narrowBumpEnv 1 33 1 1 katState)) = true := by
  native_decide
#assert_compiled narrow_emission_agrees_with_the_model

/-! ### §8g — ⚑ THE FLAG DAY, NAMED.

Cutting the chip over to `permEmissionNarrow` breaks these, on purpose, and each must be re-emitted
rather than reinterpreted:

* **`CHIP_WIDTH` 386 → 175** (`CHIP_AUX0` 33 + `NARROW_AUX_COLS` 141 + 1). `CHIP_MULT_NARROW`,
  `CHIP_OUT` and every derived offset in `ChipTableEmit` move with it.
* **`CHIP_TABLE_AIR_JSON` re-emits** — 391 gates → 180, 1,078 definitions → 1,286, and the
  `chipState16Table` variant with it. The AIR fingerprint changes, so **the VK rotates**; the old
  artifact must REFUSE to load, not be reinterpreted.
* **The Rust witness generator is the real work, and it does not exist yet.**
  `poseidon2_permute_aux_witness` (`circuit/src/plonky3_prover.rs:492`) writes 352 values per
  permutation; the narrow layout needs 141 — the eight external blocks plus one post-S-box lane per
  internal round. Until that lands, the cutover is not routable, and saying "the Lean is landed"
  would be the proven-in-Lean-is-not-routable error.
* **`sbox_registers: 1`** (`descriptor_ir2.rs:3524-3528`) is currently a pin describing a layout the
  chip deliberately does not use. This is the moment to make it mean something or delete it.
* **Every fixture carrying a chip trace re-generates**, and the devnet re-genesises.

The v1 hash sites (`lean_descriptor_air.rs:1754`, `POSEIDON2_PERM_AUX_COLS = 352`) are a SEPARATE
and Rust-authored spelling of the same algebra; they are debt already, and the narrow cutover does
not touch them. -/

end Dregg2.Circuit.Emit.Poseidon2RoundGates
