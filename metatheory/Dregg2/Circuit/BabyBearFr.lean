/-
# Dregg2.Circuit.BabyBearFr — the BabyBear-in-BN254 field gadget over the R1csFr foundation.

The deployed Go verifier (`chain/gnark/babybear.go` + `chain/gnark/babybear_ext.go`) carries
each BabyBear element (p = 2^31 − 2^27 + 1 = 2013265921) as ONE BN254 witness variable holding
its canonical residue, and reduces raw sums/products by the hinted Euclidean decomposition
`x = q·p + r` with `r` range-checked canonical and `q` range-checked small (`BBApi.ReduceBounded`).
The degree-4 extension is BabyBear[X]/(X⁴ − 11) (`BBExtW = 11`, plonky3 ground truth cited in
`babybear_ext.go`), multiplied schoolbook with ONE `ReduceBounded(·, 68)` per output coefficient.

This module is that gadget over `R1csFr.Wire` — the SAME frontend op-DAG the foundation lowers
to genuine R1CS — in two synchronized layers:

  * **Value layer** (`bbAdd`/`bbSub`/`bbMul`/`bbPow7`, `extMulV`/`extAddV`/`extSubV`) — a ℕ
    mirror of `babybear_ref.go`/`babybear_ext_ref.go`, branch-for-branch (conditional subtract,
    pre-reduced product accumulation).
  * **Gadget layer** (`gAdd`/`gSub`/`gMul`/`gPow7`, `gExtMul`/`gExtAdd`/`gExtSub`) — a
    `StateM` circuit builder that mints hint variables (the Lean twin of `bbDivModHint`,
    solved HONESTLY like gnark's `test.IsSolved` engine), emits the exact constraint shapes of
    `ReduceBounded`/`AssertIsCanonical`/`ExtMul` as `Wire` asserts, and tracks alongside each
    wire the ℕ value it evaluates to. `runM` yields the `Circuit` + the generated `Assignment`.

**KAT (bit-exactness vs the DEPLOYED Go).** Every `#guard` literal below was produced by
RUNNING the deployed reference (`go test` over `bbAddRef`/`bbSubRef`/`bbMulRef`/`bbPow7Ref`/
`bbExtMulRef`/`bbExtAddRef`/`bbExtSubRef` in `chain/gnark`, 2026-07-17) on the deterministic
vectors of `babybear_test.go`/`babybear_ext_test.go` (boundary pairs, the X³·X³ = 11·X²
binomial pin, the {123,456,789,1011}·{2021,2223,2425,2627} vector) plus two wide extra
vectors. The guards check, per vector: the value layer is bit-exact, the gadget's emitted
circuit is SATISFIED by the generated witness, the output wire EVALUATES to that exact value,
and the output is canonical. Reject polarity mirrors the Go reject tests (non-canonical
ingestion refused; tampered outputs refused). One vector is additionally pushed through the
FULL `R1csFr` lowering (`Circuit.lower`/`extend`) so the gadget rides the proven
frontend ↔ R1CS bridge (`gHolds`), not just frontend evaluation.

Classified seams (named, not silent):
  * gnark's deployed range checker (`rangecheck.New`) is a commitment/lookup argument; here
    `rangeCheck` realizes the SAME semantic contract (value < 2^bits) as bit decomposition —
    booleanity + recomposition asserts, expressible in the `Wire` language. Semantics
    identical, constraint realization differs.
  * hints are solved honestly (as gnark's test engine solves them); the KATs are
    completeness + bit-exactness evidence. Adversarial-witness soundness of the reduce
    gadget (the `q·p + r` no-wrap argument in `babybear.go`'s header) as a Lean theorem is
    the follow-up lane; NOTE the emitted `Circuit` already inherits `lower_sound` for the
    frontend→R1CS leg for free.
-/
import Mathlib.Data.ZMod.Basic
import Dregg2.Tactics
import Dregg2.Circuit.R1csFr

namespace Dregg2.Circuit.BabyBearFr

open Dregg2.Circuit.R1csFr

/-! ## §1 Constants — `BabyBearP` and the binomial `W` (babybear.go:25, babybear_ext.go:19). -/

/-- The BabyBear prime `p = 2^31 − 2^27 + 1 = 2013265921` (`BabyBearP`, babybear.go:25). -/
def pBB : ℕ := 2013265921

#guard pBB = 2 ^ 31 - 2 ^ 27 + 1

/-- The degree-4 binomial constant: `X⁴ = W = 11` (`BBExtW`, babybear_ext.go:19; plonky3
`BinomialExtensionData<4> for BabyBearParameters`). -/
def wExt : ℕ := 11

/-! ## §2 Value layer — ℕ mirror of `babybear_ref.go` / `babybear_ext_ref.go`. -/

/-- `bbAddRef` (babybear_ref.go:7): add then one conditional subtract. -/
def bbAdd (a b : ℕ) : ℕ :=
  let s := a + b
  if pBB ≤ s then s - pBB else s

/-- `bbSubRef` (babybear_ref.go:16): `a + p − b` then one conditional subtract. -/
def bbSub (a b : ℕ) : ℕ :=
  let s := a + pBB - b
  if pBB ≤ s then s - pBB else s

/-- `bbMulRef` (babybear_ref.go:25): full product mod `p`. -/
def bbMul (a b : ℕ) : ℕ := a * b % pBB

/-- `bbPow7Ref` (babybear_ref.go:39) — the Poseidon2 S-box chain a²→a³→a⁶→a⁷. -/
def bbPow7 (a : ℕ) : ℕ :=
  let a2 := bbMul a a
  let a3 := bbMul a2 a
  let a6 := bbMul a3 a3
  bbMul a6 a

/-- A degree-4 extension element, coefficients little-endian in X (mirrors `bbExtRef`). -/
structure ExtV where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
deriving BEq, DecidableEq, Repr

/-- `bbExtAddRef` (babybear_ext_ref.go:9): coefficient-wise `bbAdd`. -/
def extAddV (a b : ExtV) : ExtV :=
  ⟨bbAdd a.c0 b.c0, bbAdd a.c1 b.c1, bbAdd a.c2 b.c2, bbAdd a.c3 b.c3⟩

/-- `bbExtSubRef` (babybear_ext_ref.go:17): coefficient-wise `bbSub`. -/
def extSubV (a b : ExtV) : ExtV :=
  ⟨bbSub a.c0 b.c0, bbSub a.c1 b.c1, bbSub a.c2 b.c2, bbSub a.c3 b.c3⟩

/-- `bbExtMulRef` (babybear_ext_ref.go:25): schoolbook with wraparound `X⁴ = 11`,
pre-reduced products accumulated then one mod per coefficient — accumulation order
exactly the Go `(i, j)` loop. -/
def extMulV (a b : ExtV) : ExtV :=
  ⟨(bbMul a.c0 b.c0 + wExt * bbMul a.c1 b.c3 + wExt * bbMul a.c2 b.c2
      + wExt * bbMul a.c3 b.c1) % pBB,
   (bbMul a.c0 b.c1 + bbMul a.c1 b.c0 + wExt * bbMul a.c2 b.c3
      + wExt * bbMul a.c3 b.c2) % pBB,
   (bbMul a.c0 b.c2 + bbMul a.c1 b.c1 + bbMul a.c2 b.c0
      + wExt * bbMul a.c3 b.c3) % pBB,
   (bbMul a.c0 b.c3 + bbMul a.c1 b.c2 + bbMul a.c2 b.c1 + bbMul a.c3 b.c0) % pBB⟩

/-! ## §3 Gadget layer — the circuit builder over `R1csFr.Wire`.

A `BB` is one BabyBear element in the circuit: its frontend wire plus the ℕ value that wire
evaluates to under the generated (honest-hint) witness — the Lean twin of gnark's solver
tracking values alongside variables. -/

/-- One BabyBear element in the circuit: wire + tracked canonical value. -/
structure BB where
  wire : Wire
  val  : ℕ

/-- Builder state: the minted variable assignments (index = `Var`, in mint order) and the
accumulated `assertIsEqual` pairs. -/
structure St where
  assigns : List Fr
  asserts : List (Wire × Wire)

/-- The gadget-builder monad. -/
abbrev M := StateM St

/-- Mint a fresh frontend variable carrying value `v` (the hint-output twin: gnark's
`bbDivModHint` outputs are witness variables the solver fills; here we fill them honestly). -/
def freshVar (v : Fr) : M Wire := do
  let s ← get
  set { s with assigns := s.assigns ++ [v] }
  pure (.var s.assigns.length)

/-- Emit one `assertIsEqual`. -/
def assertEq (l r : Wire) : M Unit :=
  modify fun s => { s with asserts := s.asserts ++ [(l, r)] }

/-- `rc.Check(w, bits)` — the range-check contract `value(w) < 2^bits`, realized as bit
decomposition: mint `bits` bit variables (honest bits of `v`), assert each boolean
(`b·b = b`) and assert recomposition `w = Σ 2^i·bᵢ`. (Deployed gnark realizes the same
contract as a commitment/lookup argument — the classified seam in the header.) -/
def rangeCheck (w : Wire) (v : ℕ) (bits : ℕ) : M Unit := do
  let mut recomp : Wire := .const 0
  for i in List.range bits do
    let bw ← freshVar (((v >>> i) &&& 1 : ℕ) : Fr)
    assertEq (.mul bw bw) bw
    recomp := .add recomp (.mul (.const ((2 ^ i : ℕ) : Fr)) bw)
  assertEq w recomp

/-- `BBApi.AssertIsCanonical` (babybear.go:69): BOTH `w < 2^31` AND `(p−1) − w < 2^31`,
together pinning `w ∈ [0, p)`. The second check's wire is `(p−1) + (−1)·w` (gnark
`api.Sub(BabyBearP-1, v)`); its honest value is `p − 1 − v` (ℕ-truncated for non-canonical
`v`, in which case the recomposition assert FAILS — the reject polarity below). -/
def assertIsCanonical (w : Wire) (v : ℕ) : M Unit := do
  rangeCheck w v 31
  rangeCheck (.add (.const ((pBB - 1 : ℕ) : Fr)) (.mul (.const (-1)) w)) (pBB - 1 - v) 31

/-- `BBApi.ReduceBounded` (babybear.go:86): hint `(q, r)` with `x = q·p + r`, constrain
exactly that equation, `r` canonical, and `q` boolean (when `boundBits ≤ 31`) or
range-checked to `boundBits − 30` bits — branch-for-branch the Go. -/
def reduceBounded (x : Wire) (xv : ℕ) (boundBits : ℕ) : M BB := do
  let boundBits := if boundBits < 31 then 31 else boundBits
  let q := xv / pBB
  let r := xv % pBB
  let wq ← freshVar (q : Fr)
  let wr ← freshVar (r : Fr)
  assertEq x (.add (.mul wq (.const (pBB : ℕ))) wr)
  assertIsCanonical wr r
  if boundBits ≤ 31 then
    assertEq (.mul wq wq) wq        -- api.AssertIsBoolean q
  else
    rangeCheck wq q (boundBits - 30)
  pure ⟨wr, r⟩

/-- `BBApi.FromCanonicalU32` (babybear.go:76): witness ingestion — mint the input variable
and assert it canonical. -/
def inputU32 (v : ℕ) : M BB := do
  let w ← freshVar (v : Fr)
  assertIsCanonical w v
  pure ⟨w, v⟩

/-- `BBApi.Add` (babybear.go:113): raw sum `< 2^32`, reduce at 32 bits. -/
def gAdd (a b : BB) : M BB :=
  reduceBounded (.add a.wire b.wire) (a.val + b.val) 32

/-- `BBApi.Sub` (babybear.go:118): `a + (p − b) < 2^32`, reduce at 32 bits. -/
def gSub (a b : BB) : M BB :=
  reduceBounded (.add a.wire (.add (.const ((pBB : ℕ) : Fr)) (.mul (.const (-1)) b.wire)))
    (a.val + (pBB - b.val)) 32

/-- `BBApi.Mul` (babybear.go:123): raw product `< 2^62`, reduce at 62 bits. -/
def gMul (a b : BB) : M BB :=
  reduceBounded (.mul a.wire b.wire) (a.val * b.val) 62

/-- The Poseidon2 S-box a⁷ as the `bbPow7Ref` chain of gadget `Mul`s (composition mirror). -/
def gPow7 (a : BB) : M BB := do
  let a2 ← gMul a a
  let a3 ← gMul a2 a
  let a6 ← gMul a3 a3
  gMul a6 a

/-! ### The degree-4 extension gadget (`babybear_ext.go`). -/

/-- One extension element in the circuit (mirrors `BBExt`). -/
structure GExt where
  e0 : BB
  e1 : BB
  e2 : BB
  e3 : BB

/-- Ingest an extension element: four canonical coefficients (the Go test circuits'
`ExtAssertIsCanonical` ingestion). -/
def inputExt (v : ExtV) : M GExt := do
  pure ⟨← inputU32 v.c0, ← inputU32 v.c1, ← inputU32 v.c2, ← inputU32 v.c3⟩

/-- The tracked values of an extension element. -/
def GExt.vals (e : GExt) : ExtV := ⟨e.e0.val, e.e1.val, e.e2.val, e.e3.val⟩

/-- `ExtAdd` (babybear_ext.go:31): coefficient-wise gadget `Add`. -/
def gExtAdd (a b : GExt) : M GExt := do
  pure ⟨← gAdd a.e0 b.e0, ← gAdd a.e1 b.e1, ← gAdd a.e2 b.e2, ← gAdd a.e3 b.e3⟩

/-- `ExtSub` (babybear_ext.go:40): coefficient-wise gadget `Sub`. -/
def gExtSub (a b : GExt) : M GExt := do
  pure ⟨← gSub a.e0 b.e0, ← gSub a.e1 b.e1, ← gSub a.e2 b.e2, ← gSub a.e3 b.e3⟩

/-- A raw (unreduced) product/sum node: wire + exact ℕ value. -/
private def rawMul (x y : BB) : BB := ⟨.mul x.wire y.wire, x.val * y.val⟩
private def rawAdd (x y : BB) : BB := ⟨.add x.wire y.wire, x.val + y.val⟩
private def rawMulW (x : BB) : BB := ⟨.mul (.const ((wExt : ℕ) : Fr)) x.wire, wExt * x.val⟩

/-- `ExtMul` (babybear_ext.go:67): all 16 raw products, the four schoolbook accumulations
with `W = 11` wraparound, ONE `ReduceBounded(·, 68)` per coefficient — node-for-node the Go:

    c0 = p₀₀ + W·(p₁₃ + p₂₂ + p₃₁)
    c1 = p₀₁ + p₁₀ + W·(p₂₃ + p₃₂)
    c2 = p₀₂ + p₁₁ + p₂₀ + W·p₃₃
    c3 = p₀₃ + p₁₂ + p₂₁ + p₃₀ -/
def gExtMul (a b : GExt) : M GExt := do
  let p00 := rawMul a.e0 b.e0; let p01 := rawMul a.e0 b.e1
  let p02 := rawMul a.e0 b.e2; let p03 := rawMul a.e0 b.e3
  let p10 := rawMul a.e1 b.e0; let p11 := rawMul a.e1 b.e1
  let p12 := rawMul a.e1 b.e2; let p13 := rawMul a.e1 b.e3
  let p20 := rawMul a.e2 b.e0; let p21 := rawMul a.e2 b.e1
  let p22 := rawMul a.e2 b.e2; let p23 := rawMul a.e2 b.e3
  let p30 := rawMul a.e3 b.e0; let p31 := rawMul a.e3 b.e1
  let p32 := rawMul a.e3 b.e2; let p33 := rawMul a.e3 b.e3
  let c0 := rawAdd p00 (rawMulW (rawAdd p13 (rawAdd p22 p31)))
  let c1 := rawAdd p01 (rawAdd p10 (rawMulW (rawAdd p23 p32)))
  let c2 := rawAdd p02 (rawAdd p11 (rawAdd p20 (rawMulW p33)))
  let c3 := rawAdd p03 (rawAdd p12 (rawAdd p21 p30))
  pure ⟨← reduceBounded c0.wire c0.val 68, ← reduceBounded c1.wire c1.val 68,
        ← reduceBounded c2.wire c2.val 68, ← reduceBounded c3.wire c3.val 68⟩

/-! ## §4 Running the builder — circuit + generated witness. -/

/-- The result of running a gadget computation: its output, the emitted `Circuit`, and the
generated honest-hint `Assignment`. -/
structure RunOut (α : Type) where
  out  : α
  circ : Circuit
  asg  : Assignment

/-- Run a builder from the empty state. -/
def runM {α : Type} (m : M α) : RunOut α :=
  let (a, s) := m.run ⟨[], []⟩
  let arr := s.assigns.toArray
  ⟨a, ⟨s.asserts⟩, fun v => arr.getD v 0⟩

/-- Full check of one base-field output: the emitted circuit is satisfied by the generated
witness, the output WIRE evaluates to exactly the tracked value, and that value is
canonical. -/
def okBB (ro : RunOut BB) : Bool :=
  decide (ro.circ.satisfied ro.asg)
    && decide (ro.out.wire.eval ro.asg = (ro.out.val : Fr))
    && decide (ro.out.val < pBB)

/-- Full check of one extension output (all four coefficients). -/
def okExt (ro : RunOut GExt) : Bool :=
  decide (ro.circ.satisfied ro.asg)
    && [ro.out.e0, ro.out.e1, ro.out.e2, ro.out.e3].all fun c =>
        decide (c.wire.eval ro.asg = (c.val : Fr)) && decide (c.val < pBB)

/-- Run a binary base-field gadget op on two ingested inputs. -/
def runBin (op : BB → BB → M BB) (a b : ℕ) : ℕ × Bool :=
  let ro := runM (do op (← inputU32 a) (← inputU32 b))
  (ro.out.val, okBB ro)

/-- Run the S-box chain on one ingested input. -/
def runPow7 (a : ℕ) : ℕ × Bool :=
  let ro := runM (do gPow7 (← inputU32 a))
  (ro.out.val, okBB ro)

/-- Run a binary extension gadget op on two ingested inputs. -/
def runExt (op : GExt → GExt → M GExt) (a b : ExtV) : ExtV × Bool :=
  let ro := runM (do op (← inputExt a) (← inputExt b))
  (ro.out.vals, okExt ro)

/-! ## §5 KAT — bit-exact vs the DEPLOYED Go reference.

Every literal below is deployed-Go OUTPUT (`chain/gnark` `bbAddRef`/`bbSubRef`/`bbMulRef`/
`bbPow7Ref`/`bbExtMulRef`/`bbExtAddRef`/`bbExtSubRef`, executed 2026-07-17) on the
deterministic vectors of `babybear_test.go`/`babybear_ext_test.go` plus two wide extras.
Format: `(a, b, add, sub, mul)`. -/

/-- Base-field KAT table (Go-produced outputs). -/
def baseKAT : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [ (0, 0, 0, 0, 0),
    (0, 1, 1, 2013265920, 0),
    (1, 0, 1, 1, 0),
    (2013265920, 2013265920, 2013265919, 0, 1),
    (2013265920, 1, 0, 2013265919, 2013265920),
    (1, 2013265920, 0, 2, 2013265920),
    (1234567890, 987654321, 208956290, 246913569, 65001160),
    (2013265920, 1006632960, 1006632959, 1006632960, 1006632961) ]

-- Value layer bit-exact to the deployed Go reference.
#guard baseKAT.all fun (a, b, wadd, wsub, wmul) =>
  bbAdd a b == wadd && bbSub a b == wsub && bbMul a b == wmul

-- Gadget layer: same outputs, AND the emitted circuit satisfied + wire-eval exact + canonical.
#guard baseKAT.all fun (a, b, wadd, wsub, wmul) =>
  runBin gAdd a b == (wadd, true)
    && runBin gSub a b == (wsub, true)
    && runBin gMul a b == (wmul, true)

/-- Poseidon2-S-box KAT `(a, a⁷ mod p)` (Go-produced). -/
def pow7KAT : List (ℕ × ℕ) :=
  [ (0, 0), (1, 1), (2, 128), (3, 2187),
    (12345, 1571848398), (2013265920, 2013265920), (1006632961, 1997537281) ]

#guard pow7KAT.all fun (a, w) => bbPow7 a == w
#guard pow7KAT.all fun (a, w) => runPow7 a == (w, true)

/-- Extension KAT table `(a, b, mul, add, sub)` (Go-produced). Vector 1 is the Go test's
binomial pin X³·X³ = 11·X²; vector 3 is `babybear_ext_test.go`'s
{123,456,789,1011}·{2021,2223,2425,2627}. -/
def extKAT : List (ExtV × ExtV × ExtV × ExtV × ExtV) :=
  [ (⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 1⟩,
     ⟨0, 0, 11, 0⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 0⟩),
    (⟨1, 0, 0, 0⟩, ⟨5, 6, 7, 8⟩,
     ⟨5, 6, 7, 8⟩, ⟨6, 6, 7, 8⟩,
     ⟨2013265917, 2013265915, 2013265914, 2013265913⟩),
    (⟨123, 456, 789, 1011⟩, ⟨2021, 2223, 2425, 2627⟩,
     ⟨59194173, 50963163, 32121399, 5226099⟩,
     ⟨2144, 2679, 3214, 3638⟩,
     ⟨2013264023, 2013264154, 2013264285, 2013264305⟩),
    (⟨2013265920, 2013265920, 2013265920, 2013265920⟩,
     ⟨2013265920, 2013265920, 2013265920, 2013265920⟩,
     ⟨34, 24, 14, 4⟩,
     ⟨2013265919, 2013265919, 2013265919, 2013265919⟩,
     ⟨0, 0, 0, 0⟩),
    (⟨1234567890, 11111111, 222222222, 1999999999⟩,
     ⟨987654321, 1888888888, 333333333, 44444444⟩,
     ⟨1452839557, 1186696208, 1270223996, 361142714⟩,
     ⟨208956290, 1899999999, 555555555, 31178522⟩,
     ⟨246913569, 135488144, 1902154810, 1955555555⟩) ]

#guard extKAT.all fun (a, b, wm, wa, ws) =>
  extMulV a b == wm && extAddV a b == wa && extSubV a b == ws

#guard extKAT.all fun (a, b, wm, wa, ws) =>
  runExt gExtMul a b == (wm, true)
    && runExt gExtAdd a b == (wa, true)
    && runExt gExtSub a b == (ws, true)

/-! ## §6 The R1csFr bridge exercised — the gadget's circuit through the FULL lowering.

The gadget emits an `R1csFr.Circuit`, so `gHolds` applies verbatim: the lowered genuine
R1CS is satisfied by the canonical extension of the generated witness. Exercised concretely
on a gadget mul (aux minting, bilinear constraints, the whole rail). -/

#guard
  (let ro := runM (do gMul (← inputU32 1234567890) (← inputU32 987654321))
   r1csSatisfied ro.circ.lower (ro.circ.extend ro.asg))

/-! ## §7 Reject polarity — mirrors of the Go reject tests. -/

/-- Whether ingesting `v` as canonical succeeds under the honest solver (the Lean twin of
gnark `test.IsSolved` on `bbCanonicalCircuit`). -/
def runCanon (v : ℕ) : Bool :=
  let ro := runM (inputU32 v)
  decide (ro.circ.satisfied ro.asg)

-- `TestBBFromCanonicalU32Accepts`: 0, 1, 2^27, p−1 accepted.
#guard runCanon 0 && runCanon 1 && runCanon (2 ^ 27) && runCanon (pBB - 1)
-- `TestBBFromCanonicalU32Rejects`: p itself, the [p, 2^31) gap, 2^31, and the huge
-- BN254-modulus−5 value whose (p−1)−v wraps back small — ALL refused.
#guard !runCanon pBB && !runCanon (pBB + 12345) && !runCanon (2 ^ 31)
  && !runCanon (rBN254 - 5)

/-- Tamper the output variable of a gadget mul to `val + 1` — the recomposition assert
pins the output; the tampered witness must NOT satisfy (Go
`TestBBCircuitOpsRejectWrongAndNonCanonicalResults`, same `a = p−2, b = p−3`). -/
def runMulTampered (a b : ℕ) : Bool :=
  let ro := runM (do gMul (← inputU32 a) (← inputU32 b))
  let k := match ro.out.wire with | .var k => k | _ => 0
  let asg' : Assignment := fun v => if v = k then ((ro.out.val + 1 : ℕ) : Fr) else ro.asg v
  decide (ro.circ.satisfied asg')

#guard runMulTampered (pBB - 2) (pBB - 3) == false

/-- Tamper coefficient 2 of an extension mul (Go `TestBBExtCircuitRejects`, same vectors). -/
def runExtMulTampered (a b : ExtV) : Bool :=
  let ro := runM (do gExtMul (← inputExt a) (← inputExt b))
  let k := match ro.out.e2.wire with | .var k => k | _ => 0
  let asg' : Assignment :=
    fun v => if v = k then ((ro.out.e2.val + 1 : ℕ) : Fr) else ro.asg v
  decide (ro.circ.satisfied asg')

#guard runExtMulTampered ⟨123, 456, 789, 1011⟩ ⟨2021, 2223, 2425, 2627⟩ == false

/-! ## §8 Value-layer theorems — the reference IS mod-p arithmetic on canonical inputs. -/

theorem bbAdd_eq_mod {a b : ℕ} (ha : a < pBB) (hb : b < pBB) :
    bbAdd a b = (a + b) % pBB := by
  simp only [bbAdd]
  split <;> simp only [pBB] at * <;> omega

theorem bbSub_eq_mod {a b : ℕ} (ha : a < pBB) (hb : b < pBB) :
    bbSub a b = (pBB + a - b) % pBB := by
  simp only [bbSub]
  split <;> simp only [pBB] at * <;> omega

theorem bbMul_eq_mod (a b : ℕ) : bbMul a b = a * b % pBB := rfl

theorem bbAdd_lt {a b : ℕ} (ha : a < pBB) (hb : b < pBB) : bbAdd a b < pBB := by
  simp only [bbAdd]
  split <;> simp only [pBB] at * <;> omega

theorem bbSub_lt {a b : ℕ} (ha : a < pBB) (hb : b < pBB) : bbSub a b < pBB := by
  simp only [bbSub]
  split <;> simp only [pBB] at * <;> omega

theorem bbMul_lt (a b : ℕ) : bbMul a b < pBB := Nat.mod_lt _ (by decide)

#assert_axioms bbAdd_eq_mod
#assert_axioms bbSub_eq_mod
#assert_axioms bbMul_eq_mod
#assert_axioms bbAdd_lt
#assert_axioms bbSub_lt
#assert_axioms bbMul_lt

end Dregg2.Circuit.BabyBearFr
