/-
# Dregg2.Circuit.Emit.GnarkVerifier.BatchTableEmit — the BATCH-TABLE verifier check
emitted as a Lean-authored R1CS, leaf-refined against the deployed spec.

THE CHECK (deployed: `chain/gnark/stark_verify_native.go` `VerifyShrinkStarkAlgebra` +
`stark_constraint_interp.go` `evalSymbolicFoldedNative`): the batch-STARK constraint
evaluation at the out-of-domain point ζ — per instance the QUOTIENT IDENTITY over the
alpha-folded constraint value and the recomposed quotient, plus the global LOGUP
cumulative-sum balance. The Lean spec it must refine is the check `verifyAlgoUnified`
consumes (`FriChallengerUnified.lean:162`):
`BatchTablesSingleAir.batchTablesCheckUnified` — per instance `singleAirOk` (degree pin,
vanishing recompute `Z_H(ζ)+1 = ζ^{2^db}`, genuine-inverse pin `Z_H·inv = 1`, quotient
identity `foldedConstraints · inv = recomposedQuotient`) and the bus balance
`busSumSA = 0`.

**The rail is REUSED, not re-authored.** The constraint algebra rides the SAME
symbolic-DAG form the deployed verifier consumes (`fixtures/shrink_symbolic_constraints
.json`, interpreted by `evalSymbolicFoldedRef`/`Native`): `RawNode` mirrors the Go
`SymNode` taxonomy (`var` main/pre/pub · `permvar` · `ch` · `pv` · `sel` · consts ·
`add`/`sub`/`mul`/`neg`), `resolveNode` is the Go leaf resolution (including the
verifier's ZERO SUBSTITUTION for unopened next rows, mod.rs:563-581), and `symVals` /
`symFolded` is the generic topological interpreter + alpha fold (`acc·α + C` in emitted
global order, folder.rs:174-181). Instantiated TWICE off one rail:

  * at `ExtV` (the `BabyBearFr` value layer, itself KAT-bit-exact vs the deployed Go
    `bbExt*Ref`): `#guard` KATs pin the interpreter against GOLD outputs of the deployed
    `evalSymbolicFoldedRef` run on the REAL emitted `const`-table DAG (39 nodes, 3
    constraints) — accept AND tamper polarity;
  * at `Fr`: the interpreter's evaluations become the `constraintEvals` of the
    `SingleAirOpening`s the spec checks, and the whole check is EMITTED as a
    `GnarkCircuitData` op-DAG over the `R1csFr` foundation.

**THE LEAF-REFINEMENT THEOREM** (a genuine ∀, not a KAT — over every instance list,
every DAG, every witness datum):

    batchTable_refines :
      gHolds (batchTableData (insts.map Prod.fst)) (encodeBatchTable insts)
        ↔ batchTablesCheckUnified frArith (openingsOf insts) = true

plus the wire form (`batchTable_refines_emitted`, composing the proven `emit_faithful`)
and the reject polarity as theorems (`batchTable_rejects_tampered_quotient`,
`batchTable_rejects_unbalanced_bus`: a tampered quotient identity or an unbalanced bus
makes `gHolds` FALSE). The circuit is emitted from the SHAPE only (the emitted DAG file
+ VK-side counts — exactly the deployed split where the sym file is verifier input and
the opened values are witness); every intermediate slot (DAG node values, the ζ-squaring
chain) is FORCED by its defining equation over earlier variables, so no range-check hint
machinery is needed anywhere in this check.

Classified seams (named, not silent):
  * The `Fr` leg instantiates the GENERIC-field spec (`batchTablesCheckUnified` at
    `F := Fr`), i.e. the same posture as the whole `FriVerifier`/`FriChallengerUnified`
    spec stack. The deployed Go additionally EMULATES BabyBear-extension arithmetic
    inside Fr (`babybear_ext.go` ReduceBounded); that emulation layer is the
    `BabyBearFr` gadget lane and its in-circuit composition with this check is the
    named follow-up. The DAG-algebra leg is anchored to the deployed Go HERE via the
    `ExtV` KATs (bit-exact value layer + real emitted DAG + gold folded outputs).
  * ζ, α and the Lagrange selectors ride as witness inputs of this leaf; binding them
    to the challenger replay (and the selectors to their ζ-rational recompute) is the
    transcript-bind composition seam already named in `BatchTablesSingleAir` §residual.
-/
import Mathlib.Data.ZMod.Basic
import Dregg2.Tactics
import Dregg2.Circuit.R1csFr
import Dregg2.Circuit.BabyBearFr
import Dregg2.Circuit.BatchTablesSingleAir
import Dregg2.Circuit.Emit.GnarkVerifier.EmitFaithful

namespace Dregg2.Circuit.Emit.GnarkVerifier

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.FriVerifier (FieldArith)
open Dregg2.Circuit.BatchTablesSingleAir

instance : NeZero rBN254 := ⟨by norm_num [rBN254]⟩

/-! ## §0 List plumbing (getD over append; the region splitter). -/

private theorem getD_append_lt {α : Type} (xs ys : List α) (i : ℕ) (d : α)
    (h : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_ge {α : Type} (xs ys : List α) (i : ℕ) (d : α)
    (h : xs.length ≤ i) : (xs ++ ys).getD i d = ys.getD (i - xs.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- Split a variable-region agreement over a concatenation into the two subregions. -/
private theorem region_split (a : Assignment) (B : ℕ) (xs ys : List Fr)
    (h : ∀ i, i < (xs ++ ys).length → a (B + i) = (xs ++ ys).getD i 0) :
    (∀ i, i < xs.length → a (B + i) = xs.getD i 0) ∧
    (∀ i, i < ys.length → a (B + xs.length + i) = ys.getD i 0) := by
  constructor
  · intro i hi
    have h1 := h i (by simp only [List.length_append]; omega)
    rwa [getD_append_lt _ _ _ _ hi] at h1
  · intro i hi
    have h1 := h (xs.length + i) (by simp only [List.length_append]; omega)
    rw [getD_append_ge _ _ _ _ (by omega)] at h1
    simp only [Nat.add_sub_cancel_left] at h1
    rw [show B + xs.length + i = B + (xs.length + i) by omega]
    exact h1

/-- ℕ-cast injectivity below the modulus (the degree-pin tooth's engine). -/
private theorem cast_inj_lt {x y : ℕ} (hx : x < rBN254) (hy : y < rBN254)
    (h : (x : Fr) = (y : Fr)) : x = y := by
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hx, ZMod.val_cast_of_lt hy] at h'

private theorem foldl_ext {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (i : β), (∀ b, ∀ x ∈ l, f b x = g b x) → l.foldl f i = l.foldl g i
  | [], _, _ => rfl
  | x :: l, i, h => by
      simp only [List.foldl_cons, h i x List.mem_cons_self]
      exact foldl_ext f g l _ fun b y hy => h b y (List.mem_cons_of_mem _ hy)

/-! ## §1 The symbolic-DAG rail — the Go `SymNode` mirror, leaf resolution, and the
generic topological interpreter (`stark_constraint_interp.go`, one rail, any field). -/

/-- The generic op bundle the interpreter consumes (`neg x` is Go's `ExtSub(zero, x)`). -/
structure SymArith (F : Type) where
  add : F → F → F
  sub : F → F → F
  mul : F → F → F
  zero : F

/-- A RESOLVED DAG node: leaves are indices into the instance's flat opened-input
vector (`inp`) or already-embedded constants (`cst` — Go `c`/`ec` after canonicity
validation, and the verifier's zero substitution); interior nodes reference earlier
node slots by index, exactly the Go expression DAG. -/
inductive SNode (F : Type) where
  | inp : ℕ → SNode F
  | cst : F → SNode F
  | add : ℕ → ℕ → SNode F
  | sub : ℕ → ℕ → SNode F
  | mul : ℕ → ℕ → SNode F
  | neg : ℕ → SNode F

/-- One node's value given the flat inputs and the already-computed slots. -/
def SNode.val {F : Type} (A : SymArith F) (flat acc : List F) : SNode F → F
  | .inp k => flat.getD k A.zero
  | .cst v => v
  | .add x y => A.add (acc.getD x A.zero) (acc.getD y A.zero)
  | .sub x y => A.sub (acc.getD x A.zero) (acc.getD y A.zero)
  | .mul x y => A.mul (acc.getD x A.zero) (acc.getD y A.zero)
  | .neg x => A.sub A.zero (acc.getD x A.zero)

/-- Topological evaluation, slot by slot (Go's `vals` array fill). -/
def symValsAux {F : Type} (A : SymArith F) (flat : List F) :
    List F → List (SNode F) → List F
  | acc, [] => acc
  | acc, n :: rest => symValsAux A flat (acc ++ [n.val A flat acc]) rest

/-- All node values of a DAG (the Go `vals` array). -/
def symVals {F : Type} (A : SymArith F) (flat : List F) (nodes : List (SNode F)) :
    List F :=
  symValsAux A flat [] nodes

/-- The alpha-folded constraint value over the emitted GLOBAL order
(`folded = folded·α + vals[root]`, folder.rs:174-181 / the Go interpreter's tail). -/
def symFolded {F : Type} (A : SymArith F) (flat : List F) (nodes : List (SNode F))
    (roots : List ℕ) (alpha : F) : F :=
  roots.foldl (fun acc r => A.add (A.mul acc alpha) ((symVals A flat nodes).getD r A.zero))
    A.zero

private theorem symValsAux_length {F : Type} (A : SymArith F) (flat : List F) :
    ∀ (ns : List (SNode F)) (acc : List F),
      (symValsAux A flat acc ns).length = acc.length + ns.length
  | [], acc => by simp [symValsAux]
  | n :: ns, acc => by
      rw [symValsAux, symValsAux_length A flat ns]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

private theorem symValsAux_prefix {F : Type} (A : SymArith F) (flat : List F) :
    ∀ (ns : List (SNode F)) (acc : List F) (j : ℕ) (d : F), j < acc.length →
      (symValsAux A flat acc ns).getD j d = acc.getD j d
  | [], _, _, _, _ => rfl
  | n :: ns, acc, j, d, hj => by
      rw [symValsAux, symValsAux_prefix A flat ns _ j d (by simp; omega),
        getD_append_lt _ _ _ _ hj]

theorem symVals_length {F : Type} (A : SymArith F) (flat : List F)
    (nodes : List (SNode F)) : (symVals A flat nodes).length = nodes.length := by
  rw [symVals, symValsAux_length]; simp

/-! ### The RAW Go taxonomy + leaf resolution (`stark_constraint_interp.go` SymNode →
resolved `SNode`, including the zero substitution for unopened next rows). -/

/-- Verbatim mirror of the Go `SymNode` op taxonomy (constants already embedded). -/
inductive RawNode (F : Type) where
  | varMain : ℕ → ℕ → RawNode F   -- row, col (row 0 = at ζ, row 1 = at ζ·g)
  | varPre : ℕ → ℕ → RawNode F
  | varPub : ℕ → RawNode F
  | permvar : ℕ → ℕ → RawNode F
  | ch : ℕ → RawNode F
  | pv : ℕ → RawNode F
  | selFirst | selLast | selTrans : RawNode F
  | cst : F → RawNode F
  | add : ℕ → ℕ → RawNode F
  | sub : ℕ → ℕ → RawNode F
  | mul : ℕ → ℕ → RawNode F
  | neg : ℕ → RawNode F

/-- The per-instance opened-stream shape (`StarkInstanceShape` + the pinned
`ShrinkVkShape` next-row flags): stream lengths in the flat layout order. -/
structure RestShape where
  nTrace : ℕ
  traceNextOpen : Bool
  nPre : ℕ
  preNextOpen : Bool
  nPerm : ℕ
  nCh : ℕ
  nPv : ℕ
  nPub : ℕ

namespace RestShape

def nTraceNext (s : RestShape) : ℕ := if s.traceNextOpen then s.nTrace else 0
def nPreNext (s : RestShape) : ℕ := if s.preNextOpen then s.nPre else 0
def traceOff (_ : RestShape) : ℕ := 0
def traceNextOff (s : RestShape) : ℕ := s.nTrace
def preOff (s : RestShape) : ℕ := s.traceNextOff + s.nTraceNext
def preNextOff (s : RestShape) : ℕ := s.preOff + s.nPre
def permOff (s : RestShape) : ℕ := s.preNextOff + s.nPreNext
def permNextOff (s : RestShape) : ℕ := s.permOff + s.nPerm
def chOff (s : RestShape) : ℕ := s.permNextOff + s.nPerm
def pvOff (s : RestShape) : ℕ := s.chOff + s.nCh
def pubOff (s : RestShape) : ℕ := s.pvOff + s.nPv
def selOff (s : RestShape) : ℕ := s.pubOff + s.nPub
def size (s : RestShape) : ℕ := s.selOff + 3

end RestShape

/-- The Go leaf resolution (`evalSymbolicFoldedRef`'s `var`/`permvar`/`ch`/`pv`/`sel`
switch): map each leaf into the flat opened-input vector at `base`, substituting ZERO
for unopened next rows (mod.rs:563-581, the `src == nil` branch). -/
def resolveNode {F : Type} (z : F) (s : RestShape) (base : ℕ) : RawNode F → SNode F
  | .varMain r c =>
      if r = 0 then .inp (base + s.traceOff + c)
      else if s.traceNextOpen then .inp (base + s.traceNextOff + c) else .cst z
  | .varPre r c =>
      if r = 0 then .inp (base + s.preOff + c)
      else if s.preNextOpen then .inp (base + s.preNextOff + c) else .cst z
  | .varPub c => .inp (base + s.pubOff + c)
  | .permvar r c =>
      if r = 0 then .inp (base + s.permOff + c) else .inp (base + s.permNextOff + c)
  | .ch c => .inp (base + s.chOff + c)
  | .pv c => .inp (base + s.pvOff + c)
  | .selFirst => .inp (base + s.selOff)
  | .selLast => .inp (base + s.selOff + 1)
  | .selTrans => .inp (base + s.selOff + 2)
  | .cst v => .cst v
  | .add x y => .add x y
  | .sub x y => .sub x y
  | .mul x y => .mul x y
  | .neg x => .neg x

/-! ## §2 KAT — the rail anchored against the DEPLOYED Go interpreter.

`extSym` instantiates the rail at the `BabyBearFr` VALUE layer (`ExtV` with
`extAddV`/`extSubV`/`extMulV` — themselves `#guard`-bit-exact vs the deployed
`bbExtAddRef`/`bbExtSubRef`/`bbExtMulRef`, see `BabyBearFr` §5). The DAG below is the
REAL emitted `const`-table instance of `fixtures/shrink_symbolic_constraints.json`
(39 nodes, constraint roots [2, 29, 38]), transliterated node-for-node. The GOLD folded
outputs were produced by RUNNING the deployed `evalSymbolicFoldedRef`
(`stark_constraint_interp.go`, `go test` in `chain/gnark`, 2026-07-17) on the input
vectors below. Vector A: small consecutive coordinates; vector B: coordinates near
`p = 2013265921` (exercises the modular wraparound in every op). Tamper polarity: a
single perturbed opened input moves the folded value off gold. -/

open Dregg2.Circuit.BabyBearFr (ExtV extAddV extSubV extMulV)

/-- The rail at the BabyBear-extension VALUE layer (KAT leg). -/
def extSym : SymArith ExtV :=
  { add := extAddV, sub := extSubV, mul := extMulV, zero := ⟨0, 0, 0, 0⟩ }

/-- The `const` table's opened-stream shape (width 4, preprocessed 2, 1 lookup, 2 bus
challenges, 1 cumulative sum, no public values, next rows NOT opened —
`ShrinkVk.NumLookups[0] = 1`, `TraceNext[0] = PreNext[0] = false`). -/
def constRestShape : RestShape :=
  { nTrace := 4, traceNextOpen := false, nPre := 2, preNextOpen := false,
    nPerm := 1, nCh := 2, nPv := 1, nPub := 0 }

/-- The REAL emitted `const`-instance DAG (shrink_symbolic_constraints.json instance 0,
transliterated node-for-node; version 2). -/
def constRawDag : List (RawNode ExtV) :=
  [ .permvar 0 0, .selFirst, .mul 0 1,
    .permvar 1 0, .permvar 0 0, .sub 3 4,
    .ch 0, .varMain 0 3, .varMain 0 2,
    .varMain 0 1, .varMain 0 0, .varPre 0 1,
    .ch 1, .mul 11 12, .add 10 13,
    .ch 1, .mul 14 15, .add 9 16,
    .ch 1, .mul 17 18, .add 8 19,
    .ch 1, .mul 20 21, .add 7 22,
    .sub 6 23, .mul 5 24, .varPre 0 0,
    .sub 25 26, .selTrans, .mul 27 28,
    .pv 0, .permvar 0 0, .sub 30 31,
    .sub 6 23, .mul 32 33, .varPre 0 0,
    .sub 34 35, .selLast, .mul 36 37 ]

/-- The `const` instance's constraint roots, in emitted GLOBAL fold order. -/
def constRoots : List ℕ := [2, 29, 38]

/-- The resolved `const` DAG (leaf resolution at flat base 0). -/
def constDag : List (SNode ExtV) :=
  constRawDag.map (resolveNode extSym.zero constRestShape 0)

/-- KAT input vector A, in flat layout order: traceLocal(4) ++ preLocal(2) ++
permLocal(1) ++ permNext(1) ++ challenges(2) ++ permValues(1) ++ [selFirst, selLast,
selTrans]. Base value `k` yields `{k, k+1, k+2, k+3}`. -/
def katFlatA : List ExtV :=
  [ ⟨101, 102, 103, 104⟩, ⟨105, 106, 107, 108⟩, ⟨109, 110, 111, 112⟩,
    ⟨113, 114, 115, 116⟩,
    ⟨201, 202, 203, 204⟩, ⟨205, 206, 207, 208⟩,
    ⟨301, 302, 303, 304⟩,
    ⟨401, 402, 403, 404⟩,
    ⟨501, 502, 503, 504⟩, ⟨505, 506, 507, 508⟩,
    ⟨601, 602, 603, 604⟩,
    ⟨701, 702, 703, 704⟩, ⟨705, 706, 707, 708⟩, ⟨709, 710, 711, 712⟩ ]

/-- KAT input vector B (coordinates near `p`; same layout). -/
def katFlatB : List ExtV :=
  [ ⟨2013265820, 2013265813, 6619237, 2000027749⟩,
    ⟨2013265816, 2013265809, 6881385, 1999503465⟩,
    ⟨2013265812, 2013265805, 7143533, 1998979181⟩,
    ⟨2013265808, 2013265801, 7405681, 1998454897⟩,
    ⟨2013265720, 2013265713, 13172937, 1986920649⟩,
    ⟨2013265716, 2013265709, 13435085, 1986396365⟩,
    ⟨2013265620, 2013265613, 19726637, 1973813549⟩,
    ⟨2013265520, 2013265513, 26280337, 1960706449⟩,
    ⟨2013265420, 2013265413, 32834037, 1947599349⟩,
    ⟨2013265416, 2013265409, 33096185, 1947075065⟩,
    ⟨2013265320, 2013265313, 39387737, 1934492249⟩,
    ⟨2013265220, 2013265213, 45941437, 1921385149⟩,
    ⟨2013265216, 2013265209, 46203585, 1920860865⟩,
    ⟨2013265212, 2013265205, 46465733, 1920336581⟩ ]

-- GOLD (deployed Go `evalSymbolicFoldedRef` output on the real const DAG): vector A
-- with α = {901,902,903,904}.
#guard symFolded extSym katFlatA constDag constRoots ⟨901, 902, 903, 904⟩
  == ⟨1544233506, 737594499, 2002318200, 1256329788⟩
-- GOLD vector B with α = {2013265918, 0, 2013265920, 12345}.
#guard symFolded extSym katFlatB constDag constRoots ⟨2013265918, 0, 2013265920, 12345⟩
  == ⟨1305355499, 1617426602, 1693711511, 466581550⟩
-- Tamper polarity: perturbing ONE opened input (permLocal, flat index 6) moves the
-- folded value off gold.
#guard !(symFolded extSym (katFlatA.set 6 ⟨300, 302, 303, 304⟩) constDag constRoots
    ⟨901, 902, 903, 904⟩
  == ⟨1544233506, 737594499, 2002318200, 1256329788⟩)
-- Tamper polarity: perturbing the fold challenge α moves the folded value off gold.
#guard !(symFolded extSym katFlatA constDag constRoots ⟨902, 902, 903, 904⟩
  == ⟨1544233506, 737594499, 2002318200, 1256329788⟩)

/-! ## §3 The Fr leg — arithmetic bundles and the circuit compilation of the rail. -/

/-- The spec's field-op bundle at `Fr` (the generic-field spec instantiated at the
gnark scalar field — the same `FieldArith` posture as `FriVerifier.fullChecks`). -/
def frArith : FieldArith Fr :=
  { add := (· + ·), mul := (· * ·), pow := fun b n => b ^ n, zero := 0, one := 1 }

@[simp] private theorem frArith_add (x y : Fr) : frArith.add x y = x + y := rfl
@[simp] private theorem frArith_mul (x y : Fr) : frArith.mul x y = x * y := rfl
@[simp] private theorem frArith_pow (x : Fr) (n : ℕ) : frArith.pow x n = x ^ n := rfl
@[simp] private theorem frArith_zero : frArith.zero = 0 := rfl
@[simp] private theorem frArith_one : frArith.one = 1 := rfl

/-- The rail at `Fr`. -/
def frSym : SymArith Fr := { add := (· + ·), sub := (· - ·), mul := (· * ·), zero := 0 }

@[simp] private theorem frSym_add (x y : Fr) : frSym.add x y = x + y := rfl
@[simp] private theorem frSym_sub (x y : Fr) : frSym.sub x y = x - y := rfl
@[simp] private theorem frSym_mul (x y : Fr) : frSym.mul x y = x * y := rfl
@[simp] private theorem frSym_zero : frSym.zero = 0 := rfl

/-- Compile one resolved node to its defining WIRE: leaves read input variables at
`B + k` (or bake the constant), interior ops read earlier slot variables at
`slotBase + i`. `sub`/`neg` are spelled with `+ (−1)·` (the `Wire` language has no
subtraction node, mirroring gnark's `api.Sub` lowering). -/
def SNode.wire (B slotBase : ℕ) : SNode Fr → Wire
  | .inp k => .var (B + k)
  | .cst v => .const v
  | .add x y => .add (.var (slotBase + x)) (.var (slotBase + y))
  | .sub x y => .add (.var (slotBase + x)) (.mul (.const (-1)) (.var (slotBase + y)))
  | .mul x y => .mul (.var (slotBase + x)) (.var (slotBase + y))
  | .neg x => .mul (.const (-1)) (.var (slotBase + x))

/-- Node well-formedness at position `j` over `nIn` inputs: leaf indices in range,
children STRICTLY EARLIER (the Go loader's fail-closed topological validation,
`LoadSymbolicConstraints`). -/
def SNode.wf {F : Type} (nIn j : ℕ) : SNode F → Prop
  | .inp k => k < nIn
  | .cst _ => True
  | .add x y => x < j ∧ y < j
  | .sub x y => x < j ∧ y < j
  | .mul x y => x < j ∧ y < j
  | .neg x => x < j

/-- The DAG slot asserts: slot `j` is the fresh variable `slotBase + j`, pinned to its
defining wire (`var (slotBase+j) = wire(node j)`). Every slot is FORCED — no free hint. -/
def dagAsserts (B slotBase : ℕ) : ℕ → List (SNode Fr) → List (Wire × Wire)
  | _, [] => []
  | k, n :: rest =>
      (Wire.var (slotBase + k), n.wire B slotBase) :: dagAsserts B slotBase (k + 1) rest

private theorem nodeWire_eval (a : Assignment) (flat acc : List Fr) (B slotBase : ℕ)
    (hin : ∀ i, i < flat.length → a (B + i) = flat.getD i 0)
    (hacc : ∀ j, j < acc.length → a (slotBase + j) = acc.getD j 0)
    (n : SNode Fr) (hwf : n.wf flat.length acc.length) :
    (n.wire B slotBase).eval a = n.val frSym flat acc := by
  cases n with
  | inp k => simpa [SNode.wire, SNode.val, Wire.eval] using hin k hwf
  | cst v => rfl
  | add x y =>
      obtain ⟨hx, hy⟩ := hwf
      simp [SNode.wire, SNode.val, Wire.eval, hacc x hx, hacc y hy]
  | sub x y =>
      obtain ⟨hx, hy⟩ := hwf
      simp only [SNode.wire, SNode.val, Wire.eval, hacc x hx, hacc y hy, frSym_sub,
        frSym_zero]
      ring
  | mul x y =>
      obtain ⟨hx, hy⟩ := hwf
      simp [SNode.wire, SNode.val, Wire.eval, hacc x hx, hacc y hy]
  | neg x =>
      simp only [SNode.wire, SNode.val, Wire.eval, hacc x hwf, frSym_sub, frSym_zero]
      ring

/-- Under the canonical slot fill (the DAG's own topological evaluation), EVERY slot
assert is satisfied — the DAG region of the circuit is complete by construction. -/
private theorem dag_sat_aux (a : Assignment) (flat : List Fr) (B slotBase : ℕ)
    (hin : ∀ i, i < flat.length → a (B + i) = flat.getD i 0) :
    ∀ (rest : List (SNode Fr)) (acc : List Fr),
      (∀ j, j < (symValsAux frSym flat acc rest).length →
        a (slotBase + j) = (symValsAux frSym flat acc rest).getD j 0) →
      (∀ m, m < rest.length → (rest.getD m (.cst 0)).wf flat.length (acc.length + m)) →
      ∀ p ∈ dagAsserts B slotBase acc.length rest, p.1.eval a = p.2.eval a
  | [], _, _, _, _, hp => by simp [dagAsserts] at hp
  | n :: rest, acc, hvals, hwf, p, hp => by
      have hstep : symValsAux frSym flat acc (n :: rest)
          = symValsAux frSym flat (acc ++ [n.val frSym flat acc]) rest := rfl
      have hlenfull : (symValsAux frSym flat acc (n :: rest)).length
          = acc.length + rest.length + 1 := by
        rw [symValsAux_length]
        simp only [List.length_cons]
        omega
      have hacc : ∀ j, j < acc.length → a (slotBase + j) = acc.getD j 0 := by
        intro j hj
        have h1 := hvals j (by omega)
        rw [hstep, symValsAux_prefix _ _ _ _ _ _ (by simp; omega),
          getD_append_lt _ _ _ _ hj] at h1
        exact h1
      have hwf0 : n.wf flat.length acc.length := by
        have := hwf 0 (by simp)
        simpa using this
      rcases List.mem_cons.mp hp with heq | hp'
      · subst heq
        have hslot : a (slotBase + acc.length) = n.val frSym flat acc := by
          have h1 := hvals acc.length (by omega)
          rw [hstep, symValsAux_prefix _ _ _ _ _ _ (by simp),
            getD_append_ge _ _ _ _ (le_refl _)] at h1
          simpa using h1
        simpa [Wire.eval, hslot] using
          (nodeWire_eval a flat acc B slotBase hin hacc n hwf0).symm
      · have hvals' : ∀ j, j < (symValsAux frSym flat
            (acc ++ [n.val frSym flat acc]) rest).length →
            a (slotBase + j) = (symValsAux frSym flat
              (acc ++ [n.val frSym flat acc]) rest).getD j 0 := by
          intro j hj
          rw [← hstep] at hj ⊢
          exact hvals j hj
        have hwf' : ∀ m, m < rest.length →
            (rest.getD m (.cst 0)).wf flat.length
              ((acc ++ [n.val frSym flat acc]).length + m) := by
          intro m hm
          have h1 := hwf (m + 1) (by simp; omega)
          rw [List.getD_cons_succ] at h1
          have hidx : (acc ++ [n.val frSym flat acc]).length + m
              = acc.length + (m + 1) := by simp; omega
          rw [hidx]
          exact h1
        have := dag_sat_aux a flat B slotBase hin rest
          (acc ++ [n.val frSym flat acc]) hvals' hwf' p
        rw [show (acc ++ [n.val frSym flat acc]).length = acc.length + 1 by simp] at this
        exact this hp'

/-! ### The ζ-squaring chain (`ζ^{2^db}` in `db` forced squarings — the linear-size
sharing the deployed circuit gets from its DAG form). -/

/-- The wire holding `ζ^{2^k}`: the input ζ for `k = 0`, else squaring slot `k−1`. -/
def sqPrevWire (zetaVar sqBase : ℕ) : ℕ → Wire
  | 0 => .var zetaVar
  | k + 1 => .var (sqBase + k)

/-- The squaring-chain asserts: slot `k` holds `ζ^{2^{k+1}}`, pinned to the square of
the previous stage. -/
def sqAsserts (zetaVar sqBase : ℕ) : ℕ → List (Wire × Wire)
  | 0 => []
  | k + 1 => sqAsserts zetaVar sqBase k ++
      [(.var (sqBase + k),
        .mul (sqPrevWire zetaVar sqBase k) (sqPrevWire zetaVar sqBase k))]

/-- The canonical squaring-chain values `[ζ^2, ζ^4, …, ζ^{2^edb}]`. -/
def sqVals (zeta : Fr) (edb : ℕ) : List Fr :=
  (List.range edb).map fun k => zeta ^ 2 ^ (k + 1)

private theorem sqVals_getD (zeta : Fr) (edb k : ℕ) (hk : k < edb) :
    (sqVals zeta edb).getD k 0 = zeta ^ 2 ^ (k + 1) := by
  simp [sqVals, List.getD_eq_getElem?_getD, hk]

private theorem sqPrev_eval (a : Assignment) (zv sqBase edb : ℕ) (zeta : Fr)
    (hz : a zv = zeta)
    (hsq : ∀ k, k < edb → a (sqBase + k) = zeta ^ 2 ^ (k + 1)) :
    ∀ k, k ≤ edb → (sqPrevWire zv sqBase k).eval a = zeta ^ 2 ^ k
  | 0, _ => by simp [sqPrevWire, Wire.eval, hz]
  | k + 1, h => by simpa [sqPrevWire, Wire.eval] using hsq k (by omega)

private theorem sq_sat (a : Assignment) (zv sqBase edb : ℕ) (zeta : Fr)
    (hz : a zv = zeta)
    (hsq : ∀ k, k < edb → a (sqBase + k) = zeta ^ 2 ^ (k + 1)) :
    ∀ k, k ≤ edb → ∀ p ∈ sqAsserts zv sqBase k, p.1.eval a = p.2.eval a
  | 0, _, p, hp => by simp [sqAsserts] at hp
  | k + 1, hk, p, hp => by
      rw [sqAsserts] at hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact sq_sat a zv sqBase edb zeta hz hsq k (by omega) p hp'
      · have hp'' : p = (.var (sqBase + k),
            .mul (sqPrevWire zv sqBase k) (sqPrevWire zv sqBase k)) := by
          simpa using hp'
        subst hp''
        have hprev := sqPrev_eval a zv sqBase edb zeta hz hsq k (by omega)
        have hpow : zeta ^ 2 ^ (k + 1) = zeta ^ 2 ^ k * zeta ^ 2 ^ k := by
          rw [← pow_add]
          congr 1
          have := Nat.pow_succ 2 k
          omega
        simp [Wire.eval, hprev, hsq k (by omega), hpow]

/-! ### The Horner RLC fold and the zps·chunk dot recomposition as wire trees. -/

/-- The alpha-Horner fold over the constraint-root SLOT variables
(`acc·α + vals[root]`, the deployed global fold order). -/
def hornerWire (alphaVar slotBase : ℕ) (roots : List ℕ) : Wire :=
  roots.foldl (fun acc r => .add (.mul acc (.var alphaVar)) (.var (slotBase + r)))
    (.const 0)

private theorem hornerWire_eval_aux (a : Assignment) (av sb : ℕ) :
    ∀ (roots : List ℕ) (init : Wire),
      ((roots.foldl (fun acc r => Wire.add (.mul acc (.var av)) (.var (sb + r)))
        init).eval a)
        = roots.foldl (fun acc r => acc * a av + a (sb + r)) (init.eval a)
  | [], _ => rfl
  | r :: roots, init => by
      rw [List.foldl_cons, List.foldl_cons,
        hornerWire_eval_aux a av sb roots (.add (.mul init (.var av)) (.var (sb + r)))]
      rfl

/-- The `Σ zps_i · chunk_i` recomposition wire over `n` input pairs. -/
def dotWire (zOff cOff : ℕ) : ℕ → Wire
  | 0 => .const 0
  | n + 1 => .add (dotWire zOff cOff n) (.mul (.var (zOff + n)) (.var (cOff + n)))

/-- The value middleman: `Σ_{i<n} xs[i]·ys[i]`. -/
def dotVal (xs ys : List Fr) : ℕ → Fr
  | 0 => 0
  | n + 1 => dotVal xs ys n + xs.getD n 0 * ys.getD n 0

private theorem dotWire_eval (a : Assignment) (zOff cOff : ℕ) (xs ys : List Fr) :
    ∀ n, (∀ i, i < n → a (zOff + i) = xs.getD i 0) →
      (∀ i, i < n → a (cOff + i) = ys.getD i 0) →
      (dotWire zOff cOff n).eval a = dotVal xs ys n
  | 0, _, _ => rfl
  | n + 1, hx, hy => by
      have ih := dotWire_eval a zOff cOff xs ys n
        (fun i hi => hx i (Nat.lt_succ_of_lt hi))
        (fun i hi => hy i (Nat.lt_succ_of_lt hi))
      rw [dotWire, dotVal]
      simp only [Wire.eval, ih, hx n (Nat.lt_succ_self n), hy n (Nat.lt_succ_self n)]

private theorem dotVal_cons (x y : Fr) (xs ys : List Fr) :
    ∀ n, dotVal (x :: xs) (y :: ys) (n + 1) = x * y + dotVal xs ys n
  | 0 => by simp [dotVal]
  | n + 1 => by
      rw [dotVal, dotVal_cons x y xs ys n, dotVal]
      simp only [List.getD_cons_succ]
      ring

private theorem zip_foldr_eq_dotVal :
    ∀ (xs ys : List Fr),
      (xs.zip ys).foldr (fun p acc => p.1 * p.2 + acc) 0
        = dotVal xs ys (min xs.length ys.length)
  | [], ys => by simp [dotVal]
  | x :: xs, [] => by simp [dotVal]
  | x :: xs, y :: ys => by
      simp only [List.zip_cons_cons, List.foldr_cons, zip_foldr_eq_dotVal xs ys,
        List.length_cons, Nat.succ_min_succ, dotVal_cons]

/-! ## §4 The per-instance emission: shape, data, layout, asserts. -/

/-- The VK-side SHAPE of one instance — everything the emitted circuit is built from
(the emitted DAG file + the pinned counts; NO witness values): the flat opened-input
count, the zps/quotient-chunk counts, the VK-expected degree bits, and the resolved
constraint DAG with its fold-order roots. -/
structure InstShape where
  nIn : ℕ
  nZps : ℕ
  nChunks : ℕ
  edb : ℕ
  nodes : List (SNode Fr)
  roots : List ℕ

/-- The WITNESS data of one instance: the transcript scalars (ζ, α), the declared
degree bits, the opened vanishing/inverse pair, the LogUp cumulative sum, the Lagrange
chunk-selector coefficients + opened quotient chunks, and the remaining flat opened
stream (`rest`: trace/pre/perm/challenge/pv/pub/selector lanes, in layout order —
the streams the DAG leaves read). -/
structure InstData where
  zeta : Fr
  alpha : Fr
  vanishing : Fr
  invVanishing : Fr
  cumSum : Fr
  degreeBits : ℕ
  zps : List Fr
  chunks : List Fr
  rest : List Fr

/-- The flat input vector of one instance: 6 pinned scalar lanes, then zps, chunks,
and the opened streams. -/
def flatInputs (d : InstData) : List Fr :=
  [d.zeta, d.alpha, ((d.degreeBits : ℕ) : Fr), d.vanishing, d.invVanishing, d.cumSum]
    ++ (d.zps ++ (d.chunks ++ d.rest))

private theorem flatInputs_length (d : InstData) :
    (flatInputs d).length = 6 + d.zps.length + d.chunks.length + d.rest.length := by
  simp [flatInputs]; omega

/-- Total variable count of one instance: inputs, DAG slots, squaring slots. -/
def instSize (sh : InstShape) : ℕ := sh.nIn + sh.nodes.length + sh.edb

/-- The DAG slot values of one instance (the rail's evaluation at `Fr`). -/
def dagValsOf (sh : InstShape) (d : InstData) : List Fr :=
  symVals frSym (flatInputs d) sh.nodes

/-- The canonical witness values of one instance, in variable order. -/
def instVals (sh : InstShape) (d : InstData) : List Fr :=
  flatInputs d ++ (dagValsOf sh d ++ sqVals d.zeta sh.edb)

/-- **Instance well-formedness** — the fail-closed conditions the deployed loader
enforces (`LoadSymbolicConstraints` + the shape-drift panics of
`VerifyShrinkStarkAlgebra`): stream lengths match the pinned shape, the DAG is
topological with in-range leaves, roots are in range, and the degree-bit lanes are
small enough for the field cast to be injective (deployed: `u32`). -/
def InstWF (sh : InstShape) (d : InstData) : Prop :=
  d.zps.length = sh.nZps ∧ d.chunks.length = sh.nChunks
    ∧ sh.nIn = 6 + sh.nZps + sh.nChunks + d.rest.length
    ∧ (∀ m, m < sh.nodes.length → (sh.nodes.getD m (.cst 0)).wf sh.nIn m)
    ∧ (∀ r ∈ sh.roots, r < sh.nodes.length)
    ∧ d.degreeBits < rBN254 ∧ sh.edb < rBN254

/-- The `SingleAirOpening` this instance denotes — `constraintEvals` DERIVED by the
rail (the DAG's evaluations at ζ), everything else carried, `expectedDegreeBits` from
the VK-side shape. This is the object the committed spec checks. -/
def openingOf (sh : InstShape) (d : InstData) : SingleAirOpening Fr :=
  { zeta := d.zeta, degreeBits := d.degreeBits, expectedDegreeBits := sh.edb,
    alpha := d.alpha,
    constraintEvals := sh.roots.map fun r => (dagValsOf sh d).getD r 0,
    zps := d.zps, quotientChunks := d.chunks,
    vanishing := d.vanishing, invVanishing := d.invVanishing,
    logupCumSum := d.cumSum }

/-- The four CHECK asserts of one instance (each `singleAirOk` conjunct, in order):
degree pin, vanishing recompute, genuine-inverse pin, quotient identity. -/
def finalAsserts (sh : InstShape) (B : ℕ) : List (Wire × Wire) :=
  [ (.var (B + 2), .const ((sh.edb : ℕ) : Fr)),
    (.add (.var (B + 3)) (.const 1),
      sqPrevWire B (B + sh.nIn + sh.nodes.length) sh.edb),
    (.mul (.var (B + 3)) (.var (B + 4)), .const 1),
    (.mul (hornerWire (B + 1) (B + sh.nIn) sh.roots) (.var (B + 4)),
      dotWire (B + 6) (B + 6 + sh.nZps) (min sh.nZps sh.nChunks)) ]

/-- All asserts of one instance at base `B`. -/
def instAsserts (sh : InstShape) (B : ℕ) : List (Wire × Wire) :=
  dagAsserts B (B + sh.nIn) 0 sh.nodes
    ++ (sqAsserts B (B + sh.nIn + sh.nodes.length) sh.edb ++ finalAsserts sh B)

private theorem instVals_length (sh : InstShape) (d : InstData) (hwf : InstWF sh d) :
    (instVals sh d).length = instSize sh := by
  obtain ⟨hz, hc, hn, _, _, _, _⟩ := hwf
  simp only [instVals, instSize, List.length_append, flatInputs_length,
    dagValsOf, symVals_length, sqVals, List.length_map, List.length_range]
  omega

/-! ## §5 The per-instance refinement. -/

private theorem inst_refines (sh : InstShape) (d : InstData) (B : ℕ) (a : Assignment)
    (hwf : InstWF sh d)
    (ha : ∀ i, i < (instVals sh d).length → a (B + i) = (instVals sh d).getD i 0) :
    ((∀ p ∈ instAsserts sh B, p.1.eval a = p.2.eval a)
      ↔ singleAirOk frArith (openingOf sh d) = true) := by
  obtain ⟨hzl, hcl, hnin, hnodes, hroots, hdb, hedb⟩ := hwf
  have hflatlen : (flatInputs d).length = sh.nIn := by
    rw [flatInputs_length]; omega
  have hdaglen : (dagValsOf sh d).length = sh.nodes.length := by
    rw [dagValsOf, symVals_length]
  -- split the region agreement into inputs / DAG slots / squaring slots
  obtain ⟨hin0, hrest0⟩ := region_split a B (flatInputs d)
    (dagValsOf sh d ++ sqVals d.zeta sh.edb) (by
      intro i hi
      exact ha i (by simpa [instVals] using hi))
  rw [hflatlen] at hrest0
  obtain ⟨hdag0, hsq0⟩ := region_split a (B + sh.nIn) (dagValsOf sh d)
    (sqVals d.zeta sh.edb) hrest0
  rw [hdaglen] at hsq0
  have hin : ∀ i, i < (flatInputs d).length → a (B + i) = (flatInputs d).getD i 0 :=
    hin0
  -- the six scalar input lanes
  have h0 : a B = d.zeta := by
    have := hin 0 (by rw [hflatlen]; omega)
    rwa [Nat.add_zero] at this
  have h1 : a (B + 1) = d.alpha := hin 1 (by rw [hflatlen]; omega)
  have h2 : a (B + 2) = ((d.degreeBits : ℕ) : Fr) := hin 2 (by rw [hflatlen]; omega)
  have h3 : a (B + 3) = d.vanishing := hin 3 (by rw [hflatlen]; omega)
  have h4 : a (B + 4) = d.invVanishing := hin 4 (by rw [hflatlen]; omega)
  -- zps / chunks lanes
  have hzps : ∀ i, i < d.zps.length → a (B + 6 + i) = d.zps.getD i 0 := by
    intro i hi
    have h := hin (6 + i) (by rw [hflatlen]; omega)
    have hgd : (flatInputs d).getD (6 + i) 0 = d.zps.getD i 0 := by
      rw [show (6 : ℕ) + i = i + 6 by omega]
      show (d.zps ++ (d.chunks ++ d.rest)).getD i 0 = d.zps.getD i 0
      exact getD_append_lt _ _ _ _ hi
    rw [hgd] at h
    rw [show B + 6 + i = B + (6 + i) by omega]
    exact h
  have hchunks : ∀ i, i < d.chunks.length →
      a (B + 6 + sh.nZps + i) = d.chunks.getD i 0 := by
    intro i hi
    have h := hin (6 + (sh.nZps + i)) (by rw [hflatlen]; omega)
    have hgd : (flatInputs d).getD (6 + (sh.nZps + i)) 0 = d.chunks.getD i 0 := by
      rw [show (6 : ℕ) + (sh.nZps + i) = (sh.nZps + i) + 6 by omega]
      show (d.zps ++ (d.chunks ++ d.rest)).getD (sh.nZps + i) 0 = d.chunks.getD i 0
      rw [getD_append_ge _ _ _ _ (by omega), show sh.nZps + i - d.zps.length = i by omega]
      exact getD_append_lt _ _ _ _ hi
    rw [hgd] at h
    rw [show B + 6 + sh.nZps + i = B + (6 + (sh.nZps + i)) by omega]
    exact h
  -- the DAG region is satisfied and its slots carry the rail's evaluations
  have hdagsat : ∀ p ∈ dagAsserts B (B + sh.nIn) 0 sh.nodes,
      p.1.eval a = p.2.eval a := by
    have := dag_sat_aux a (flatInputs d) B (B + sh.nIn)
      (fun i hi => hin i hi) sh.nodes []
      (by
        intro j hj
        rw [symValsAux_length] at hj
        simp only [List.length_nil, Nat.zero_add] at hj
        have := hdag0 j (by rwa [hdaglen])
        rwa [dagValsOf, symVals] at this)
      (by
        intro m hm
        have := hnodes m hm
        rwa [List.length_nil, Nat.zero_add, ← hflatlen] at *
        )
    simpa using this
  -- the squaring chain is satisfied and its top wire is ζ^{2^edb}
  have hsqv : ∀ k, k < sh.edb →
      a (B + sh.nIn + sh.nodes.length + k) = d.zeta ^ 2 ^ (k + 1) := by
    intro k hk
    have := hsq0 k (by simp [sqVals, hk])
    rwa [sqVals_getD _ _ _ hk] at this
  have hsqsat : ∀ p ∈ sqAsserts B (B + sh.nIn + sh.nodes.length) sh.edb,
      p.1.eval a = p.2.eval a :=
    sq_sat a B (B + sh.nIn + sh.nodes.length) sh.edb d.zeta h0 hsqv sh.edb (le_refl _)
  have hsqtop : (sqPrevWire B (B + sh.nIn + sh.nodes.length) sh.edb).eval a
      = d.zeta ^ 2 ^ sh.edb :=
    sqPrev_eval a B (B + sh.nIn + sh.nodes.length) sh.edb d.zeta h0 hsqv sh.edb
      (le_refl _)
  -- the Horner fold wire evaluates to the spec's derived foldedConstraints
  have hhorner : (hornerWire (B + 1) (B + sh.nIn) sh.roots).eval a
      = foldedConstraints frArith (openingOf sh d) := by
    rw [hornerWire, hornerWire_eval_aux]
    have hstep : sh.roots.foldl
        (fun acc r => acc * a (B + 1) + a (B + sh.nIn + r)) ((Wire.const 0).eval a)
        = sh.roots.foldl
          (fun acc r => acc * d.alpha + (dagValsOf sh d).getD r 0) 0 := by
      show sh.roots.foldl _ ((0 : Fr)) = _
      apply foldl_ext
      intro b r hr
      rw [h1, hdag0 r (by rw [hdaglen]; exact hroots r hr)]
    rw [hstep]
    simp only [foldedConstraints, openingOf, frArith_add, frArith_mul, frArith_zero,
      List.foldl_map]
  -- the dot wire evaluates to the spec's derived recomposedQuotient
  have hdot : (dotWire (B + 6) (B + 6 + sh.nZps) (min sh.nZps sh.nChunks)).eval a
      = recomposedQuotient frArith (openingOf sh d) := by
    have hxs : ∀ i, i < min sh.nZps sh.nChunks → a (B + 6 + i) = d.zps.getD i 0 := by
      intro i hi
      exact hzps i (by omega)
    have hys : ∀ i, i < min sh.nZps sh.nChunks →
        a (B + 6 + sh.nZps + i) = d.chunks.getD i 0 := by
      intro i hi
      exact hchunks i (by omega)
    rw [dotWire_eval a (B + 6) (B + 6 + sh.nZps) d.zps d.chunks
      (min sh.nZps sh.nChunks) hxs hys]
    simp only [recomposedQuotient, openingOf, frArith_add, frArith_mul, frArith_zero]
    rw [zip_foldr_eq_dotVal, hzl, hcl]
  -- collapse the always-satisfied regions
  rw [instAsserts, List.forall_mem_append, List.forall_mem_append,
    and_iff_right hdagsat, and_iff_right hsqsat]
  -- the four final asserts against the four spec conjuncts
  have hfinal : (∀ p ∈ finalAsserts sh B, p.1.eval a = p.2.eval a)
      ↔ (((d.degreeBits : ℕ) : Fr) = ((sh.edb : ℕ) : Fr)
        ∧ d.vanishing + 1 = d.zeta ^ 2 ^ sh.edb
        ∧ d.vanishing * d.invVanishing = 1
        ∧ foldedConstraints frArith (openingOf sh d) * d.invVanishing
            = recomposedQuotient frArith (openingOf sh d)) := by
    simp [finalAsserts, Wire.eval, h2, h3, h4, hsqtop, hhorner, hdot]
  rw [hfinal]
  -- strip the `decide`s before rewriting their arguments (the instances keep the unrewritten type)
  simp only [singleAirOk, Bool.and_eq_true, decide_eq_true_eq]
  simp only [openingOf, frArith_add, frArith_mul, frArith_pow, frArith_one]
  constructor
  · rintro ⟨hp, hv, hi, hq⟩
    have hpe : d.degreeBits = sh.edb := cast_inj_lt hdb hedb hp
    refine ⟨⟨⟨hpe, ?_⟩, hi⟩, hq⟩
    rw [hpe]
    exact hv
  · rintro ⟨⟨⟨hp, hv⟩, hi⟩, hq⟩
    refine ⟨by rw [hp], ?_, hi, hq⟩
    rw [← hp]
    exact hv

/-! ## §6 The batch: all instances + the global LogUp balance. -/

/-- All instance asserts, bases threaded left to right. -/
def batchAsserts : List InstShape → ℕ → List (Wire × Wire)
  | [], _ => []
  | sh :: rest, B => instAsserts sh B ++ batchAsserts rest (B + instSize sh)

/-- The global cumulative-sum wire: `Σ_i var(B_i + 5)` (each instance's LogUp lane). -/
def balWire : List InstShape → ℕ → Wire
  | [], _ => .const 0
  | sh :: rest, B => .add (.var (B + 5)) (balWire rest (B + instSize sh))

/-- The canonical witness values of the whole batch, in variable order. -/
def batchVals : List (InstShape × InstData) → List Fr
  | [] => []
  | (sh, d) :: rest => instVals sh d ++ batchVals rest

private theorem batch_aux :
    ∀ (insts : List (InstShape × InstData)) (B : ℕ) (a : Assignment),
      (∀ p ∈ insts, InstWF p.1 p.2) →
      (∀ i, i < (batchVals insts).length → a (B + i) = (batchVals insts).getD i 0) →
      ((∀ p ∈ batchAsserts (insts.map Prod.fst) B, p.1.eval a = p.2.eval a)
        ↔ ∀ p ∈ insts, singleAirOk frArith (openingOf p.1 p.2) = true)
      ∧ (balWire (insts.map Prod.fst) B).eval a
          = (insts.map fun p => p.2.cumSum).foldr (· + ·) 0
  | [], B, a, _, _ => by
      constructor
      · simp [batchAsserts]
      · simp [balWire, Wire.eval]
  | (sh, d) :: insts, B, a, hwf, ha => by
      have hwfh : InstWF sh d := hwf (sh, d) List.mem_cons_self
      have hwft : ∀ p ∈ insts, InstWF p.1 p.2 :=
        fun p hp => hwf p (List.mem_cons_of_mem _ hp)
      obtain ⟨hah, hat0⟩ := region_split a B (instVals sh d) (batchVals insts)
        (by intro i hi; exact ha i (by simpa [batchVals] using hi))
      rw [instVals_length sh d hwfh] at hat0
      obtain ⟨hiff, hbal⟩ := batch_aux insts (B + instSize sh) a hwft hat0
      have hcum : a (B + 5) = d.cumSum := by
        have h5 := hah 5 (by
          rw [instVals_length sh d hwfh]
          obtain ⟨_, _, hnin, _⟩ := hwfh
          simp only [instSize]
          omega)
        have hgd : (instVals sh d).getD 5 0 = d.cumSum := by
          rw [instVals, getD_append_lt _ _ _ _ (by
            rw [flatInputs_length]
            omega)]
          rfl
        rwa [hgd] at h5
      constructor
      · rw [List.map_cons, batchAsserts, List.forall_mem_append,
          inst_refines sh d B a hwfh hah, hiff]
        constructor
        · rintro ⟨hh, ht⟩ p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact hh
          · exact ht p hp'
        · intro h
          exact ⟨h (sh, d) List.mem_cons_self,
            fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
      · rw [List.map_cons, balWire]
        simp only [Wire.eval, hcum, hbal, List.map_cons, List.foldr_cons]

/-! ## §7 THE DELIVERABLE — the emitted package and the leaf-refinement theorem. -/

/-- The gadget-invocation records: one per instance (base, one-past-end), plus the
global balance record. -/
def batchGadgets : List InstShape → ℕ → List GadgetInvocation
  | [], _ => [⟨"LogUpBalance", []⟩]
  | sh :: rest, B => ⟨"BatchTableInstance", [B, B + instSize sh]⟩
      :: batchGadgets rest (B + instSize sh)

/-- The full batch-table circuit: every instance's asserts plus the global
cumulative-sum balance assert (`Σ cumSums = 0`, mod.rs:623-643). -/
def batchTableCircuit (shapes : List InstShape) : Circuit :=
  ⟨batchAsserts shapes 0 ++ [(balWire shapes 0, .const 0)]⟩

/-- **The emission package** — built from the VK-side SHAPES only (the emitted DAG
file + pinned counts; the deployed split where `shrink_symbolic_constraints.json` is
verifier input and the opened values are witness). ζ/α transcript binding is the named
composition seam, so no lane is declared public here. -/
def batchTableData (shapes : List InstShape) : GnarkCircuitData :=
  { name := "batch_table_check_v1"
    publicInputs := []
    gadgets := batchGadgets shapes 0
    circuit := batchTableCircuit shapes }

/-- The canonical witness encoding of the batch. -/
def encodeBatchTable (insts : List (InstShape × InstData)) : Assignment :=
  fun i => (batchVals insts).getD i 0

/-- The `SingleAirOpening`s the batch denotes (constraint evals derived by the rail). -/
def openingsOf (insts : List (InstShape × InstData)) : List (SingleAirOpening Fr) :=
  insts.map fun p => openingOf p.1 p.2

/-- Batch well-formedness: every instance passes the deployed loader's fail-closed
validation. -/
def BatchWF (insts : List (InstShape × InstData)) : Prop :=
  ∀ p ∈ insts, InstWF p.1 p.2

instance (d : GnarkCircuitData) (a : Assignment) : Decidable (gHolds d a) :=
  inferInstanceAs (Decidable (r1csSatisfied _ _))

/-- **`batchTable_refines` — THE LEAF-REFINEMENT THEOREM.** The lowered genuine R1CS of
the emitted batch-table package, under the canonical witness encoding, is satisfied IFF
the committed spec check `batchTablesCheckUnified` (the check `verifyAlgoUnified`
consumes: per instance the degree pin + vanishing recompute + genuine-inverse pin +
quotient identity over the rail-derived constraint evaluations, plus the global LogUp
balance) accepts — for EVERY well-formed instance list: every DAG, every shape, every
witness datum. Both polarities ride the ↔: any tamper that flips the spec (wrong
quotient chunk, forged inverse, wrong degree, unbalanced bus, perturbed opened column)
makes `gHolds` FALSE. -/
theorem batchTable_refines (insts : List (InstShape × InstData)) (hwf : BatchWF insts) :
    gHolds (batchTableData (insts.map Prod.fst)) (encodeBatchTable insts)
      ↔ batchTablesCheckUnified frArith (openingsOf insts) = true := by
  unfold gHolds
  rw [← R1csFr.gHolds]
  obtain ⟨hiff, hbal⟩ := batch_aux insts 0 (encodeBatchTable insts) hwf
    (by
      intro i _
      show encodeBatchTable insts (0 + i) = _
      rw [Nat.zero_add]
      rfl)
  show (∀ p ∈ (batchTableCircuit (insts.map Prod.fst)).asserts,
      p.1.eval (encodeBatchTable insts) = p.2.eval (encodeBatchTable insts)) ↔ _
  rw [batchTableCircuit]
  show (∀ p ∈ batchAsserts (insts.map Prod.fst) 0
      ++ [(balWire (insts.map Prod.fst) 0, Wire.const 0)], _) ↔ _
  rw [List.forall_mem_append, List.forall_mem_singleton, hiff]
  have hbus : busSumSA frArith (openingsOf insts)
      = (insts.map fun p => p.2.cumSum).foldr (· + ·) 0 := by
    simp only [busSumSA, openingsOf, List.map_map]
    rfl
  rw [batchTablesCheckUnified, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  simp only [Wire.eval, hbal, hbus, frArith_zero]
  rw [openingsOf, List.forall_mem_map]

/-- The same refinement at the EMITTED wire form (composing the proven
`emit_faithful`): the bytes the JSON grammar renders denote exactly the spec check. -/
theorem batchTable_refines_emitted (insts : List (InstShape × InstData))
    (hwf : BatchWF insts) :
    satisfiedEmitted (emit (batchTableData (insts.map Prod.fst)))
        (encodeBatchTable insts)
      ↔ batchTablesCheckUnified frArith (openingsOf insts) = true :=
  (emit_faithful _ _).symm.trans (batchTable_refines insts hwf)

/-! ### The reject polarity as theorems (composing the spec's proven teeth). -/

/-- **Tampered-quotient reject.** If ANY instance's derived quotient identity fails —
a tampered opened quotient chunk, constraint column, α, or a forged folded value — the
emitted R1CS admits NO satisfaction under the canonical encoding. -/
theorem batchTable_rejects_tampered_quotient (insts : List (InstShape × InstData))
    (hwf : BatchWF insts) (p : InstShape × InstData) (hp : p ∈ insts)
    (h : frArith.mul (foldedConstraints frArith (openingOf p.1 p.2))
        (openingOf p.1 p.2).invVanishing
      ≠ recomposedQuotient frArith (openingOf p.1 p.2)) :
    ¬ gHolds (batchTableData (insts.map Prod.fst)) (encodeBatchTable insts) := by
  rw [batchTable_refines insts hwf,
    batchTablesCheckUnified_rejects_tampered_quotient frArith (openingsOf insts)
      (openingOf p.1 p.2) (by exact List.mem_map_of_mem hp) h]
  simp

/-- **Unbalanced-bus reject.** If the LogUp cumulative sums do not net to zero, the
emitted R1CS admits NO satisfaction under the canonical encoding. -/
theorem batchTable_rejects_unbalanced_bus (insts : List (InstShape × InstData))
    (hwf : BatchWF insts)
    (h : busSumSA frArith (openingsOf insts) ≠ frArith.zero) :
    ¬ gHolds (batchTableData (insts.map Prod.fst)) (encodeBatchTable insts) := by
  rw [batchTable_refines insts hwf,
    batchTablesCheckUnified_rejects_unbalanced_bus frArith (openingsOf insts) h]
  simp

#assert_axioms batchTable_refines
#assert_axioms batchTable_refines_emitted
#assert_axioms batchTable_rejects_tampered_quotient
#assert_axioms batchTable_rejects_unbalanced_bus

/-! ## §8 Teeth — decidable samples at both polarities (the ∀-theorem subsumes these;
the guards pin that the DEFINITIONS compute, through the FULL R1CS lowering). -/

/-- Toy instance 1 (edb 0): ζ = 2 so `Z_H = ζ − 1 = 1`, `inv = 1`; DAG multiplies two
opened lanes (3·5 = 15); one chunk with `zps = [3]`, chunk `5` recomposes `15`;
identity `15·1 = 15`; bus lane `0`. -/
def toyShape : InstShape :=
  { nIn := 10, nZps := 1, nChunks := 1, edb := 0,
    nodes := [.inp 8, .inp 9, .mul 0 1], roots := [2] }

def toyData : InstData :=
  { zeta := 2, alpha := 7, vanishing := 1, invVanishing := 1, cumSum := 0,
    degreeBits := 0, zps := [3], chunks := [5], rest := [3, 5] }

/-- Toy instance 2 (edb 2, exercises the squaring chain): ζ = 2, `ζ^{2^2} = 16`,
`Z_H = 15`, genuine inverse `15⁻¹ mod r`; folded = 30 (one root, direct lane);
`30·15⁻¹ = 2 = zps·chunk = 1·2`; bus lane `0`. -/
def toyShape2 : InstShape :=
  { nIn := 9, nZps := 1, nChunks := 1, edb := 2, nodes := [.inp 8], roots := [0] }

def toyData2 : InstData :=
  { zeta := 2, alpha := 11, vanishing := 15,
    invVanishing :=
      2918432382911903362966187432700970011806448586722137912493093891543441132749,
    cumSum := 0, degreeBits := 2, zps := [1], chunks := [2], rest := [30] }

def toyBatch : List (InstShape × InstData) := [(toyShape, toyData), (toyShape2, toyData2)]

-- The spec accepts the honest two-instance batch…
#guard batchTablesCheckUnified frArith (openingsOf toyBatch)
-- …and the emitted circuit accepts the canonical encoding, at the frontend AND through
-- the FULL genuine-R1CS lowering (`gHolds` = lowered system + canonical extension).
#guard decide ((batchTableCircuit (toyBatch.map Prod.fst)).satisfied
  (encodeBatchTable toyBatch))
#guard decide (gHolds (batchTableData (toyBatch.map Prod.fst))
  (encodeBatchTable toyBatch))
-- Reject polarity, same circuit (emitted from shape only), tampered witness data:
-- a tampered quotient chunk…
#guard !decide (gHolds (batchTableData (toyBatch.map Prod.fst))
  (encodeBatchTable [(toyShape, { toyData with chunks := [6] }), (toyShape2, toyData2)]))
-- …an unbalanced LogUp bus…
#guard !decide (gHolds (batchTableData (toyBatch.map Prod.fst))
  (encodeBatchTable [(toyShape, { toyData with cumSum := 1 }), (toyShape2, toyData2)]))
-- …a wrong declared degree…
#guard !decide (gHolds (batchTableData (toyBatch.map Prod.fst))
  (encodeBatchTable [(toyShape, { toyData with degreeBits := 1 }), (toyShape2, toyData2)]))
-- …and a forged vanishing inverse.
#guard !decide (gHolds (batchTableData (toyBatch.map Prod.fst))
  (encodeBatchTable [(toyShape, toyData), (toyShape2, { toyData2 with invVanishing := 2 })]))
-- The spec rejects each of the same tampers (the ↔ is exercised on both sides).
#guard !batchTablesCheckUnified frArith
  (openingsOf [(toyShape, { toyData with chunks := [6] }), (toyShape2, toyData2)])
#guard !batchTablesCheckUnified frArith
  (openingsOf [(toyShape, { toyData with cumSum := 1 }), (toyShape2, toyData2)])

end Dregg2.Circuit.Emit.GnarkVerifier
