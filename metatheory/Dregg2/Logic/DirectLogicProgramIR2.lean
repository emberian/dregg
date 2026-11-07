/-
# Dregg2.Logic.DirectLogicProgramIR2 -- the direct-logic front end, authored in Lean

This is the compiler behind `circuit/src/direct_logic_frontend.rs::compile_logic_program`.
The Rust function no longer builds a constraint: it sends the canonical source bytes to this
module (through `lake exe direct_logic_compile`, root `DirectLogicCompile.lean`) and parses the
reply.  Everything the Rust compiler used to author is defined here:

* the typed source language (Booleans, nonempty finite enumerations, fail-closed unbounded
  integers; equality, truth-table predicates, connectives, bounded quantifiers);
* finite-domain one-hot input encoding with one linear sum-to-one gate per enumeration input;
* deterministic quantifier expansion with the same balanced reductions and constant folding;
* the descriptor name `dregg-direct-logic-v1-<BLAKE3 of the canonical source bytes>`, computed
  by `Dregg2.Crypto.Blake3Compute` from the bytes this module decoded and re-encoded;
* the width-at-least-one rule: a program with no atoms gets one Boolean padding column.

The descriptor reuses `FiniteLogicDescriptorIR2`'s gates (always-on booleanity per column, the
always-on acceptance gate on the formula polynomial) and adds the one-hot gates.  The theorems:

* `lower_eval` -- the grounded Boolean source evaluates, under the canonical atom encoding of
  well-typed values, to the source meaning `evalFormula` (one-hot terms, equality, truth-table
  predicates through row-major decoding, quantifier expansion, the folding constructors);
* `program_sound` -- every row of a canonical `Satisfied2` trace of the compiled descriptor IS the
  encoding of well-typed source values (booleanity plus one-hot gates force it) that make the
  program true;
* `program_complete` -- every well-typed true input has a one-row witness, padding included;
* `compileBytes_spec` / `compileBytes_source_identity` / `compileBytes_sound` -- an accepted
  request compiles exactly the program its bytes canonically encode, named by BLAKE3 of those
  bytes;
* `sample_satisfied` (honest witness) and `booleanOnly_accepts_twoHot` /
  `program_refuses_twoHot` (the control: the Boolean polynomial alone accepts a two-hot row that
  encodes no source value; the compiled descriptor refuses it).

Differences from the retired Rust compiler, all on refusals: limit checks use totals computed
before expansion (same accept/refuse decision on well-typed programs; the reported count is the
total rather than Rust's first exceeding partial count), type errors are reported before limit
errors, and the atom limit is additionally capped at `atomCeiling` below the field.  Booleanity
uses the corpus-canonical `binaryBody` rendering, so descriptor bytes differ from the Rust ones.
-/

import Dregg2.Logic.FiniteLogicDescriptorIR2
import Dregg2.Crypto.Blake3Compute

namespace Dregg2.Logic.DirectLogicProgramIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Logic.FiniteLogicDescriptorIR2

set_option autoImplicit false

abbrev Source := Cert.Source

/-! ## 1. Source syntax (the Rust `LogicProgram`, constructor for constructor) -/

inductive LType where
  | bool
  | finite (cardinality : Nat)
  | unbounded
  deriving Repr, DecidableEq

/-- De Bruijn terms: `bound 0` is the innermost binder. -/
inductive Term where
  | input (index : Nat)
  | bound (index : Nat)
  | const (ty : LType) (value : Nat)
  deriving Repr, DecidableEq

/-- Row-major truth table: `index = ((a0 * |A1|) + a1) * |A2| + a2 ...`. -/
structure PredTable where
  name : String
  argTypes : List LType
  values : List Bool
  deriving Repr, DecidableEq

inductive Formula where
  | top
  | bot
  | eq (left right : Term)
  | pred (table : PredTable) (args : List Term)
  | not (p : Formula)
  | and (p q : Formula)
  | or (p q : Formula)
  | all (binder : LType) (body : Formula)
  | ex (binder : LType) (body : Formula)
  deriving Repr, DecidableEq

structure InputDecl where
  name : String
  ty : LType
  deriving Repr, DecidableEq

structure Program where
  inputs : List InputDecl
  formula : Formula
  deriving Repr, DecidableEq

structure Limits where
  maxSourceNodes : Nat
  maxAtoms : Nat
  maxPredicateEntries : Nat
  maxQuantifierInstances : Nat
  maxExpandedNodes : Nat
  deriving Repr, DecidableEq

def Limits.default : Limits := ⟨2048, 4096, 65536, 65536, 250000⟩

inductive Error where
  | emptyFiniteDomain
  | unboundedDomain
  | duplicateInputName (name : String)
  | sourceTooLarge (nodes maximum : Nat)
  | tooManyAtoms (atoms maximum : Nat)
  | predicateTooLarge (entries maximum : Nat)
  | predicateShapeMismatch (expected actual : Nat)
  | predicateArityMismatch (expected actual : Nat)
  | quantifierExpansionTooLarge (instances maximum : Nat)
  | expandedRelationTooLarge (nodes maximum : Nat)
  | inputOutOfRange (index available : Nat)
  | boundVariableOutOfRange (index depth : Nat)
  | constantOutOfRange (value cardinality : Nat)
  | typeMismatch (expected actual : LType)
  | malformedRequest (why : String)
  deriving Repr, DecidableEq

/-- The number of values of a type; `0` only for the refused types. -/
def LType.card : LType -> Nat
  | .bool => 2
  | .finite n => n
  | .unbounded => 0

/-- The checked cardinality (Rust `LogicType::cardinality`). -/
def LType.checkCard : LType -> Except Error Nat
  | .bool => .ok 2
  | .finite 0 => .error .emptyFiniteDomain
  | .finite n => .ok n
  | .unbounded => .error .unboundedDomain

theorem LType.checkCard_ok {ty : LType} {n : Nat} (h : ty.checkCard = .ok n) :
    n = ty.card /\ 0 < n := by
  cases ty with
  | bool => cases h; exact ⟨rfl, by decide⟩
  | finite m =>
      cases m with
      | zero => cases h
      | succ m => cases h; exact ⟨rfl, Nat.succ_pos m⟩
  | unbounded => cases h

/-- Atom columns an input occupies: one for a Boolean, one per value of an enumeration. -/
def LType.atomCount : LType -> Nat
  | .bool => 1
  | .finite n => n
  | .unbounded => 0

/-! ## 2. Reference semantics -/

/-- Row-major flat index exactly as the Rust evaluator computes it (Horner, left to right). -/
def horner (acc : Nat) : List (Nat × Nat) -> Nat
  | [] => acc
  | (card, value) :: rest => horner (acc * card + value) rest

/-- Term value.  A Boolean is `0`/`1`; an enumeration value is its index. -/
def evalTerm (vals : List Nat) (bvals : List Nat) : Term -> Nat
  | .input i => vals.getD i 0
  | .bound i => bvals.getD i 0
  | .const _ v => v

/-- The source meaning of a formula under input values `vals` and binder values `bvals`
(innermost first).  Quantifiers range over every value of their binder type. -/
def evalFormula (vals : List Nat) : List Nat -> Formula -> Bool
  | _, .top => true
  | _, .bot => false
  | bvals, .eq l r => evalTerm vals bvals l == evalTerm vals bvals r
  | bvals, .pred table args =>
      table.values.getD
        (horner 0 (table.argTypes.map LType.card |>.zip (args.map (evalTerm vals bvals)))) false
  | bvals, .not p => !(evalFormula vals bvals p)
  | bvals, .and p q => evalFormula vals bvals p && evalFormula vals bvals q
  | bvals, .or p q => evalFormula vals bvals p || evalFormula vals bvals q
  | bvals, .all ty body => (List.range ty.card).all (fun v => evalFormula vals (v :: bvals) body)
  | bvals, .ex ty body => (List.range ty.card).any (fun v => evalFormula vals (v :: bvals) body)

/-- Well-typed source values: one per input, each below its type's cardinality. -/
def ValuesOk (inputs : List InputDecl) (vals : List Nat) : Prop :=
  vals.length = inputs.length /\
    forall i (hi : i < inputs.length), vals.getD i 0 < inputs[i].ty.card

/-- Well-typed binder values: one per binder, each below its binder type's cardinality. -/
def BvalsOk (ctx : List LType) (bvals : List Nat) : Prop :=
  bvals.length = ctx.length /\ forall i (hi : i < ctx.length), bvals.getD i 0 < ctx[i].card

/-- The one-hot bits of one source value (a Boolean is its own single column). -/
def inputBits : LType -> Nat -> List Bool
  | .bool, v => [v == 1]
  | .finite n, v => (List.range n).map (· == v)
  | .unbounded, _ => []

/-- The canonical encoding of source values as atom columns. -/
def encodeRow : List InputDecl -> List Nat -> List Bool
  | d :: ds, v :: vs => inputBits d.ty v ++ encodeRow ds vs
  | _, _ => []

/-- The atom environment of source values; columns past the atoms (padding) are false. -/
def atomEnv (inputs : List InputDecl) (vals : List Nat) (a : Nat) : Bool :=
  (encodeRow inputs vals).getD a false

def evalProgram (p : Program) (vals : List Nat) : Bool := evalFormula vals [] p.formula

/-! ## 3. Type checking (no expansion; typing never depends on binder values) -/

def requireSame (expected actual : LType) : Except Error Unit :=
  if expected = actual then .ok () else .error (.typeMismatch expected actual)

/-- `ctx` is the binder type stack, innermost first. -/
def termType (inputs : List InputDecl) (ctx : List LType) : Term -> Except Error LType
  | .input i =>
      match inputs[i]? with
      | some d => .ok d.ty
      | none => .error (.inputOutOfRange i inputs.length)
  | .bound i =>
      match ctx[i]? with
      | some ty => .ok ty
      | none => .error (.boundVariableOutOfRange i ctx.length)
  | .const ty v => do
      let n <- ty.checkCard
      if v < n then .ok ty else .error (.constantOutOfRange v n)

def checkArgs (inputs : List InputDecl) (ctx : List LType) :
    List LType -> List Term -> Except Error Unit
  | expected :: tys, arg :: args => do
      let _ <- expected.checkCard
      let actual <- termType inputs ctx arg
      requireSame expected actual
      checkArgs inputs ctx tys args
  | _, _ => .ok ()

def checkFormula (limits : Limits) (inputs : List InputDecl) :
    List LType -> Formula -> Except Error Unit
  | _, .top => .ok ()
  | _, .bot => .ok ()
  | ctx, .eq l r => do
      let lt <- termType inputs ctx l
      let rt <- termType inputs ctx r
      requireSame lt rt
  | ctx, .pred table args => do
      if table.argTypes.length != args.length then
        throw (.predicateArityMismatch table.argTypes.length args.length)
      checkArgs inputs ctx table.argTypes args
      let entries := (table.argTypes.map LType.card).prod
      if limits.maxPredicateEntries < entries then
        throw (.predicateTooLarge entries limits.maxPredicateEntries)
      if table.values.length != entries then
        throw (.predicateShapeMismatch entries table.values.length)
  | ctx, .not p => checkFormula limits inputs ctx p
  | ctx, .and p q => do checkFormula limits inputs ctx p; checkFormula limits inputs ctx q
  | ctx, .or p q => do checkFormula limits inputs ctx p; checkFormula limits inputs ctx q
  | ctx, .all ty body => do let _ <- ty.checkCard; checkFormula limits inputs (ty :: ctx) body
  | ctx, .ex ty body => do let _ <- ty.checkCard; checkFormula limits inputs (ty :: ctx) body

/-! ## 4. Expansion costs (the Rust lowering's two counters, totalled before expanding) -/

/-- Source nodes (Rust `formula_node_count`). -/
def sourceNodes : Formula -> Nat
  | .top | .bot => 1
  | .eq _ _ => 3
  | .pred _ args => 1 + args.length
  | .not p => 1 + sourceNodes p
  | .and p q | .or p q => 1 + sourceNodes p + sourceNodes q
  | .all _ b | .ex _ b => 1 + sourceNodes b

/-- Quantifier instances the expansion visits (Rust `quantifier_instances`). -/
def quantInstances : Formula -> Nat
  | .not p => quantInstances p
  | .and p q | .or p q => quantInstances p + quantInstances q
  | .all ty b | .ex ty b => ty.card + ty.card * quantInstances b
  | _ => 0

/-- Construction steps the expansion spends (Rust `Lowering::spend`): one per formula visit
and one per term lowering. -/
def expansionSteps : Formula -> Nat
  | .top | .bot => 1
  | .eq _ _ => 3
  | .pred _ args => 1 + args.length
  | .not p => 1 + expansionSteps p
  | .and p q | .or p q => 1 + expansionSteps p + expansionSteps q
  | .all ty b | .ex ty b => 1 + ty.card * expansionSteps b

/-! ## 5. Lowering to the Boolean source of `FiniteLogicDescriptorIR2` -/

def constS (b : Bool) : Source := if b then .top else .bot

/-- Rust `not`: folds constants and double negation. -/
def mkNot : Source -> Source
  | .top => .bot
  | .bot => .top
  | .not inner => inner
  | other => .not other

/-- Rust `and`: absorbing `false`, identity `true`, idempotence. -/
def mkAnd : Source -> Source -> Source
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, v => v
  | v, .top => v
  | l, r => if l = r then l else .and l r

/-- Rust `or`: absorbing `true`, identity `false`, idempotence. -/
def mkOr : Source -> Source -> Source
  | .top, _ => .top
  | _, .top => .top
  | .bot, v => v
  | v, .bot => v
  | l, r => if l = r then l else .or l r

/-- One balanced round: combine adjacent pairs, carry an odd tail. -/
def pairUp {α : Type} (f : α -> α -> α) : List α -> List α
  | a :: b :: rest => f a b :: pairUp f rest
  | xs => xs

theorem pairUp_length_lt {α : Type} (f : α -> α -> α) (a b : α) (rest : List α) :
    (pairUp f (a :: b :: rest)).length < (a :: b :: rest).length := by
  induction rest using List.twoStepInduction generalizing a b with
  | nil => simp [pairUp]
  | singleton c => simp [pairUp]
  | cons_cons c d rest ih _ =>
      have := ih c d
      simp only [pairUp, List.length_cons] at this ⊢
      omega

/-- Balanced rounds with explicit fuel (structural, so the kernel can evaluate it). -/
def reduceBalancedAux {α : Type} (identity : α) (f : α -> α -> α) : Nat -> List α -> α
  | _, [] => identity
  | _, [x] => x
  | 0, _ :: _ :: _ => identity
  | n + 1, a :: b :: rest => reduceBalancedAux identity f n (pairUp f (a :: b :: rest))

/-- Rust `reduce_balanced`: halve until one value remains.  Each round shortens a list of two or
more, so its length is enough fuel. -/
def reduceBalanced {α : Type} (identity : α) (f : α -> α -> α) (xs : List α) : α :=
  reduceBalancedAux identity f xs.length xs

def allS (xs : List Source) : Source := reduceBalanced .top mkAnd xs
def anyS (xs : List Source) : Source := reduceBalanced .bot mkOr xs

/-- Row-major decoding, most significant digit first (`decode_row_major`). -/
def decodeRowMajor : List Nat -> Nat -> List Nat
  | [], _ => []
  | _ :: cards, flat =>
      flat / cards.prod :: decodeRowMajor cards (flat % cards.prod)

/-- First atom and atom count of each input, in declaration order. -/
def layoutFrom (next : Nat) : List InputDecl -> List (Nat × Nat)
  | [] => []
  | d :: ds => (next, d.ty.atomCount) :: layoutFrom (next + d.ty.atomCount) ds

def layout (inputs : List InputDecl) : List (Nat × Nat) := layoutFrom 0 inputs

def atomTotal (inputs : List InputDecl) : Nat := (inputs.map (fun d => d.ty.atomCount)).sum

/-- One-hot bits of a term: entry `k` is true exactly when the term's value is `k`.  A Boolean
input contributes `[not a, a]`; an enumeration input its own columns; a bound variable or a
constant the constant vector (binder values are known during expansion). -/
def termBits (inputs : List InputDecl) (bvals : List Nat) (ctx : List LType) : Term -> List Source
  | .input i =>
      match inputs[i]?, (layout inputs)[i]? with
      | some d, some (first, _) =>
          match d.ty with
          | .bool => [mkNot (.atom first), .atom first]
          | .finite n => (List.range n).map (fun k => .atom (first + k))
          | .unbounded => []
      | _, _ => []
  | .bound i => (List.range ((ctx.getD i .unbounded).card)).map (fun v => constS (v == bvals.getD i 0))
  | .const ty v => (List.range ty.card).map (fun c => constS (c == v))

/-- Ground the formula into a Boolean source over atom columns. -/
def lower (inputs : List InputDecl) : List Nat -> List LType -> Formula -> Source
  | _, _, .top => .top
  | _, _, .bot => .bot
  | bvals, ctx, .eq l r =>
      anyS ((termBits inputs bvals ctx l).zipWith mkAnd (termBits inputs bvals ctx r))
  | bvals, ctx, .pred table args =>
      let cards := table.argTypes.map LType.card
      let argBits := args.map (termBits inputs bvals ctx)
      anyS ((List.range table.values.length).filterMap fun flat =>
        if table.values.getD flat false then
          some (allS ((decodeRowMajor cards flat).zipIdx.map fun (sel, i) =>
            ((argBits.getD i []).getD sel .bot)))
        else none)
  | bvals, ctx, .not p => mkNot (lower inputs bvals ctx p)
  | bvals, ctx, .and p q => mkAnd (lower inputs bvals ctx p) (lower inputs bvals ctx q)
  | bvals, ctx, .or p q => mkOr (lower inputs bvals ctx p) (lower inputs bvals ctx q)
  | bvals, ctx, .all ty body =>
      allS ((List.range ty.card).map fun v => lower inputs (v :: bvals) (ty :: ctx) body)
  | bvals, ctx, .ex ty body =>
      anyS ((List.range ty.card).map fun v => lower inputs (v :: bvals) (ty :: ctx) body)

/-- Rust `BoolExpr::node_count`. -/
def sourceSize : Source -> Nat
  | .atom _ | .top | .bot => 1
  | .not p => 1 + sourceSize p
  | .and p q | .or p q => 1 + sourceSize p + sourceSize q

/-! ## 6. The compiled descriptor -/

/-- Rust `sum_window`: a balanced sum (`0` for the empty list). -/
def sumW (xs : List WindowExpr) : WindowExpr := reduceBalanced (.const 0) .add xs

/-- `sum_k col(first + k) - 1`: exactly one of an enumeration input's columns is set. -/
def oneHotBody (first n : Nat) : WindowExpr :=
  .add (sumW ((List.range n).map fun k => .loc (first + k))) (.const (-1))

def oneHotConstraint (first n : Nat) : WindowConstraint :=
  { body := oneHotBody first n, onTransition := false }

def oneHotGates : List (InputDecl × (Nat × Nat)) -> List VmConstraint2
  | [] => []
  | (d, (first, _)) :: rest =>
      match d.ty with
      | .finite n => .windowGate (oneHotConstraint first n) :: oneHotGates rest
      | _ => oneHotGates rest

/-- Main-trace width: the atoms, or one Boolean padding column when there are none (the live
AIR admits no zero-width trace). -/
def traceWidthOf (inputs : List InputDecl) : Nat := max 1 (atomTotal inputs)

def programConstraints (inputs : List InputDecl) (relation : Source) : List VmConstraint2 :=
  (List.range (traceWidthOf inputs)).map (fun c => .windowGate (binaryConstraint c)) ++
    oneHotGates (inputs.zip (layout inputs)) ++ [.windowGate (acceptConstraint relation)]

def programDescriptor (name : String) (inputs : List InputDecl) (relation : Source) :
    EffectVmDescriptor2 :=
  { name := name
  , traceWidth := traceWidthOf inputs
  , piCount := 0
  , tables := [mainTableDef (traceWidthOf inputs)]
  , constraints := programConstraints inputs relation
  , hashSites := []
  , ranges := [] }

structure Compiled where
  descriptor : EffectVmDescriptor2
  relation : Source
  layout : List (Nat × Nat)
  logicalAtoms : Nat

/-- A hard ceiling below the BabyBear modulus, whatever limits the caller passes: the one-hot
argument needs every enumeration's column count to be smaller than the field. -/
def atomCeiling : Nat := 2 ^ 24

def Limits.atomMax (limits : Limits) : Nat := min limits.maxAtoms atomCeiling

/-- Atom columns of an admitted input type. -/
def inputAtoms : LType -> Except Error Nat
  | .bool => .ok 1
  | .finite n => (LType.finite n).checkCard
  | .unbounded => .error .unboundedDomain

/-- Input admission, in Rust order: duplicate names, empty/unbounded domains, the atom limit. -/
def checkInputs (limits : Limits) : List String -> Nat -> List InputDecl -> Except Error Unit
  | _, _, [] => .ok ()
  | seen, next, d :: ds => do
      if seen.contains d.name then throw (.duplicateInputName d.name)
      let n <- inputAtoms d.ty
      if limits.atomMax < next + n then throw (.tooManyAtoms (next + n) limits.atomMax)
      checkInputs limits (d.name :: seen) (next + n) ds

/-- The front end.  `name` is the descriptor name (section 7 derives it from the source bytes). -/
def compileProgram (limits : Limits) (name : String) (p : Program) : Except Error Compiled := do
  let nodes := sourceNodes p.formula
  if limits.maxSourceNodes < nodes then throw (.sourceTooLarge nodes limits.maxSourceNodes)
  checkInputs limits [] 0 p.inputs
  checkFormula limits p.inputs [] p.formula
  let qi := quantInstances p.formula
  if limits.maxQuantifierInstances < qi then
    throw (.quantifierExpansionTooLarge qi limits.maxQuantifierInstances)
  let steps := expansionSteps p.formula
  if limits.maxExpandedNodes < steps then
    throw (.expandedRelationTooLarge steps limits.maxExpandedNodes)
  let relation := lower p.inputs [] [] p.formula
  let size := sourceSize relation
  if limits.maxExpandedNodes < size then
    throw (.expandedRelationTooLarge size limits.maxExpandedNodes)
  pure { descriptor := programDescriptor name p.inputs relation
       , relation := relation
       , layout := layout p.inputs
       , logicalAtoms := atomTotal p.inputs }

/-! ## 7. Canonical source bytes (Rust `canonical_source_bytes`) and the request wire -/

def u64le (n : Nat) : List UInt8 := (List.range 8).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

def putBytes (bs : List UInt8) : List UInt8 := u64le bs.length ++ bs

def encType : LType -> List UInt8
  | .bool => [0]
  | .finite n => 1 :: u64le n
  | .unbounded => [2]

def encTerm : Term -> List UInt8
  | .input i => 0 :: u64le i
  | .bound i => 1 :: u64le i
  | .const ty v => 2 :: (encType ty ++ u64le v)

def encFormula : Formula -> List UInt8
  | .top => [0]
  | .bot => [1]
  | .eq l r => 2 :: (encTerm l ++ encTerm r)
  | .pred t args =>
      3 :: (putBytes t.name.toUTF8.toList ++ u64le t.argTypes.length ++
        t.argTypes.flatMap encType ++ u64le t.values.length ++
        t.values.map (fun b => if b then 1 else 0) ++ u64le args.length ++ args.flatMap encTerm)
  | .not p => 4 :: encFormula p
  | .and p q => 5 :: (encFormula p ++ encFormula q)
  | .or p q => 6 :: (encFormula p ++ encFormula q)
  | .all ty b => 7 :: (encType ty ++ encFormula b)
  | .ex ty b => 8 :: (encType ty ++ encFormula b)

def frontendVersion : Nat := 1

def sourceMagic : List UInt8 := "dregg-direct-logic-source".toUTF8.toList ++ [0]

def encodeProgram (p : Program) : List UInt8 :=
  sourceMagic ++ u64le frontendVersion ++ u64le p.inputs.length ++
    p.inputs.flatMap (fun d => putBytes d.name.toUTF8.toList ++ encType d.ty) ++
    encFormula p.formula

abbrev Dec := StateT (List UInt8) Option

def decByte : Dec UInt8 := fun s =>
  match s with
  | b :: rest => some (b, rest)
  | [] => none

def decTake (n : Nat) : Dec (List UInt8) := fun s =>
  if n ≤ s.length then some (s.take n, s.drop n) else none

def decU64 : Dec Nat := do
  let bs <- decTake 8
  pure (bs.foldr (fun b acc => b.toNat + 256 * acc) 0)

def decString : Dec String := do
  let n <- decU64
  let bs <- decTake n
  match String.fromUTF8? (ByteArray.mk bs.toArray) with
  | some s => pure s
  | none => failure

def decList {α : Type} (d : Dec α) : Nat -> Dec (List α)
  | 0 => pure []
  | n + 1 => do
      let x <- d
      let xs <- decList d n
      pure (x :: xs)

def decType : Dec LType := do
  match (<- decByte) with
  | 0 => pure .bool
  | 1 => return .finite (<- decU64)
  | 2 => pure .unbounded
  | _ => failure

def decTerm : Dec Term := do
  match (<- decByte) with
  | 0 => return .input (<- decU64)
  | 1 => return .bound (<- decU64)
  | 2 => do let ty <- decType; return .const ty (<- decU64)
  | _ => failure

def decBit : Dec Bool := do
  match (<- decByte) with
  | 0 => pure false
  | 1 => pure true
  | _ => failure

def decFormula : Nat -> Dec Formula
  | 0 => failure
  | fuel + 1 => do
      match (<- decByte) with
      | 0 => pure .top
      | 1 => pure .bot
      | 2 => do let l <- decTerm; return .eq l (<- decTerm)
      | 3 => do
          let name <- decString
          let tys <- decList decType (<- decU64)
          let values <- decList decBit (<- decU64)
          let args <- decList decTerm (<- decU64)
          pure (.pred ⟨name, tys, values⟩ args)
      | 4 => return .not (<- decFormula fuel)
      | 5 => do let p <- decFormula fuel; return .and p (<- decFormula fuel)
      | 6 => do let p <- decFormula fuel; return .or p (<- decFormula fuel)
      | 7 => do let ty <- decType; return .all ty (<- decFormula fuel)
      | 8 => do let ty <- decType; return .ex ty (<- decFormula fuel)
      | _ => failure

def decInput : Dec InputDecl := do
  let name <- decString
  return ⟨name, <- decType⟩

def decProgramBody (fuel : Nat) : Dec Program := do
  let magic <- decTake sourceMagic.length
  if magic != sourceMagic then failure
  if (<- decU64) != frontendVersion then failure
  let inputs <- decList decInput (<- decU64)
  return ⟨inputs, <- decFormula fuel⟩

/-- Canonical decoding: the bytes must parse completely AND be exactly the re-encoding of what
was parsed, so a decoded program is a function of its bytes and vice versa. -/
def decodeProgram (bytes : List UInt8) : Option Program :=
  match decProgramBody bytes.length bytes with
  | some (p, []) => if encodeProgram p = bytes then some p else none
  | _ => none

def sourceHash (bytes : List UInt8) : ByteArray :=
  Dregg2.Crypto.Blake3.hash (ByteArray.mk bytes.toArray)

def descriptorNameOf (bytes : List UInt8) : String :=
  "dregg-direct-logic-v" ++ toString frontendVersion ++ "-" ++
    Dregg2.Crypto.Blake3.toHex (sourceHash bytes)

/-- The whole compile step on canonical source bytes. -/
def compileBytes (limits : Limits) (bytes : List UInt8) : Except Error (Program × Compiled) :=
  match decodeProgram bytes with
  | none => .error (.malformedRequest "source bytes are not a canonical direct-logic program")
  | some p => do
      let c <- compileProgram limits (descriptorNameOf bytes) p
      pure (p, c)

def requestTag : String := "DIRECT-LOGIC-COMPILE-1"
def replyTag : String := "DIRECT-LOGIC-COMPILED-1"

/-- `DIRECT-LOGIC-COMPILE-1 <src nodes> <atoms> <pred entries> <quant instances> <expanded> <hex>` -/
def parseRequest (line : String) : Except Error (Limits × List UInt8) :=
  match (line.splitOn " ") with
  | [tag, a, b, c, d, e, hex] =>
      if tag != requestTag then .error (.malformedRequest "unknown request tag") else
      match a.toNat?, b.toNat?, c.toNat?, d.toNat?, e.toNat?,
          Dregg2.Crypto.Blake3.ofHex hex with
      | some a, some b, some c, some d, some e, some bytes => .ok (⟨a, b, c, d, e⟩, bytes.toList)
      | _, _, _, _, _, _ => .error (.malformedRequest "bad request field")
  | _ => .error (.malformedRequest "request needs seven space-separated fields")

def renderType : LType -> String
  | .bool => "bool"
  | .finite n => "finite:" ++ toString n
  | .unbounded => "unbounded"

def renderError : Error -> String
  | .emptyFiniteDomain => "EmptyFiniteDomain"
  | .unboundedDomain => "UnboundedDomain"
  | .duplicateInputName n => "DuplicateInputName " ++ Dregg2.Crypto.Blake3.toHex n.toUTF8
  | .sourceTooLarge a b => s!"SourceTooLarge {a} {b}"
  | .tooManyAtoms a b => s!"TooManyAtoms {a} {b}"
  | .predicateTooLarge a b => s!"PredicateTooLarge {a} {b}"
  | .predicateShapeMismatch a b => s!"PredicateShapeMismatch {a} {b}"
  | .predicateArityMismatch a b => s!"PredicateArityMismatch {a} {b}"
  | .quantifierExpansionTooLarge a b => s!"QuantifierExpansionTooLarge {a} {b}"
  | .expandedRelationTooLarge a b => s!"ExpandedRelationTooLarge {a} {b}"
  | .inputOutOfRange a b => s!"InputOutOfRange {a} {b}"
  | .boundVariableOutOfRange a b => s!"BoundVariableOutOfRange {a} {b}"
  | .constantOutOfRange a b => s!"ConstantOutOfRange {a} {b}"
  | .typeMismatch a b => "TypeMismatch " ++ renderType a ++ " " ++ renderType b
  | .malformedRequest why => "MalformedRequest " ++ Dregg2.Crypto.Blake3.toHex why.toUTF8

/-- Postfix tokens: `A<n>` atom, `T`/`F` constants, `N` not, `&` and, `|` or. -/
def rpn : Source -> List String -> List String
  | .atom a, acc => ("A" ++ toString a) :: acc
  | .top, acc => "T" :: acc
  | .bot, acc => "F" :: acc
  | .not p, acc => rpn p ("N" :: acc)
  | .and p q, acc => rpn p (rpn q ("&" :: acc))
  | .or p q, acc => rpn p (rpn q ("|" :: acc))

/-- The reply: one record per line; the descriptor line is exactly `emitVmJson2`. -/
def reply (r : Except Error (Program × Compiled)) (bytes : List UInt8) : String :=
  match r with
  | .error e => replyTag ++ "\nerror " ++ renderError e ++ "\n"
  | .ok (_, c) =>
      replyTag ++ "\nok\nsource_blake3 " ++ Dregg2.Crypto.Blake3.toHex (sourceHash bytes) ++
      "\nlogical_atom_count " ++ toString c.logicalAtoms ++
      "\ninputs" ++ String.join (c.layout.map fun (f, n) => " " ++ toString f ++ ":" ++ toString n) ++
      "\nrelation " ++ " ".intercalate (rpn c.relation []) ++
      "\ndescriptor " ++ emitVmJson2 c.descriptor ++ "\n"

def respond (line : String) : String :=
  match parseRequest line with
  | .error e => reply (.error e) []
  | .ok (limits, bytes) => reply (compileBytes limits bytes) bytes

/-! ## 8. Concrete checks against the Rust front end's pinned sample -/

def sampleProgram : Program :=
  let colorTy := LType.finite 3
  let allowed : PredTable := ⟨"allowed", [.bool, colorTy], [true, true, false, false, true, true]⟩
  let hasWitness : PredTable :=
    ⟨"has-witness", [.bool, colorTy], [true, false, false, false, false, true]⟩
  { inputs := [⟨"flag", .bool⟩, ⟨"color", colorTy⟩]
  , formula := .and (.pred allowed [.input 0, .input 1])
      (.all .bool (.ex colorTy (.pred hasWitness [.bound 1, .bound 0]))) }

-- The Rust test pins this BLAKE3 of the canonical source bytes.
#guard Dregg2.Crypto.Blake3.toHex (sourceHash (encodeProgram sampleProgram)) ==
  "dedc2cf1fbf6548930b4217eee7e6373b055a0bfb1164f6845d442079affdb90"
#guard decodeProgram (encodeProgram sampleProgram) == some sampleProgram

/-! ## 9. Balanced reductions and the folding constructors -/

theorem pairUp_foldr {α β : Type} (f : α -> α -> α) (h : α -> β) (g : β -> β -> β) (u : β)
    (hf : forall a b, h (f a b) = g (h a) (h b))
    (hassoc : forall x y z, g (g x y) z = g x (g y z)) (xs : List α) :
    ((pairUp f xs).map h).foldr g u = (xs.map h).foldr g u := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b rest ih _ =>
      simp only [pairUp, List.map_cons, List.foldr_cons, hf, hassoc] at ih ⊢
      rw [ih]

theorem reduceBalancedAux_hom {α β : Type} (e : α) (f : α -> α -> α) (h : α -> β)
    (g : β -> β -> β) (u : β)
    (hf : forall a b, h (f a b) = g (h a) (h b))
    (hassoc : forall x y z, g (g x y) z = g x (g y z)) (hu : forall x, g x u = x)
    (he : h e = u) : forall (n : Nat) (xs : List α), xs.length ≤ n + 1 ->
      h (reduceBalancedAux e f n xs) = (xs.map h).foldr g u := by
  intro n
  induction n with
  | zero =>
      intro xs hlen
      match xs, hlen with
      | [], _ => simp [reduceBalancedAux, he]
      | [x], _ => simp [reduceBalancedAux, hu]
      | _ :: _ :: _, hlen => simp at hlen
  | succ n ih =>
      intro xs hlen
      match xs, hlen with
      | [], _ => simp [reduceBalancedAux, he]
      | [x], _ => simp [reduceBalancedAux, hu]
      | a :: b :: rest, hlen =>
          rw [reduceBalancedAux, ih _ (by have := pairUp_length_lt f a b rest; omega),
            pairUp_foldr f h g u hf hassoc]

theorem reduceBalanced_hom {α β : Type} (e : α) (f : α -> α -> α) (h : α -> β)
    (g : β -> β -> β) (u : β)
    (hf : forall a b, h (f a b) = g (h a) (h b))
    (hassoc : forall x y z, g (g x y) z = g x (g y z)) (hu : forall x, g x u = x)
    (he : h e = u) (xs : List α) :
    h (reduceBalanced e f xs) = (xs.map h).foldr g u :=
  reduceBalancedAux_hom e f h g u hf hassoc hu he xs.length xs (Nat.le_succ _)

theorem pairUp_pred {α : Type} (P : α -> Prop) (f : α -> α -> α)
    (hf : forall a b, P a -> P b -> P (f a b)) :
    forall ys : List α, (forall y, y ∈ ys -> P y) -> forall z, z ∈ pairUp f ys -> P z := by
  intro ys
  induction ys using List.twoStepInduction with
  | nil => intro _ z hz; simp [pairUp] at hz
  | singleton c => intro hy z hz; simp only [pairUp] at hz; exact hy z hz
  | cons_cons c d rest' ih' _ =>
      intro hy z hz
      simp only [pairUp, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hf c d (hy c (by simp)) (hy d (by simp))
      · exact ih' (fun y hy' => hy y (by simp [hy'])) z hz

theorem reduceBalanced_pred {α : Type} (P : α -> Prop) (e : α) (f : α -> α -> α)
    (he : P e) (hf : forall a b, P a -> P b -> P (f a b)) (xs : List α)
    (hxs : forall x, x ∈ xs -> P x) : P (reduceBalanced e f xs) := by
  have key : forall (n : Nat) (ys : List α), (forall y, y ∈ ys -> P y) ->
      P (reduceBalancedAux e f n ys) := by
    intro n
    induction n with
    | zero =>
        intro ys hy
        match ys, hy with
        | [], _ => exact he
        | [x], hy => exact hy x (by simp)
        | _ :: _ :: _, _ => exact he
    | succ n ih =>
        intro ys hy
        match ys, hy with
        | [], _ => exact he
        | [x], hy => exact hy x (by simp)
        | a :: b :: rest, hy =>
            rw [reduceBalancedAux]
            exact ih _ (pairUp_pred P f hf _ hy)
  exact key _ xs hxs

theorem foldr_and_eq_all {α : Type} (p : α -> Bool) (xs : List α) :
    (xs.map p).foldr (· && ·) true = xs.all p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem foldr_or_eq_any {α : Type} (p : α -> Bool) (xs : List α) :
    (xs.map p).foldr (· || ·) false = xs.any p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem eval_constS (env : Nat -> Bool) (b : Bool) : Cert.eval env (constS b) = b := by
  cases b <;> rfl

theorem eval_mkNot (env : Nat -> Bool) (s : Source) :
    Cert.eval env (mkNot s) = !(Cert.eval env s) := by
  cases s <;> simp [mkNot, Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval]

theorem eval_mkAnd (env : Nat -> Bool) (l r : Source) :
    Cert.eval env (mkAnd l r) = (Cert.eval env l && Cert.eval env r) := by
  unfold mkAnd
  split <;> try (simp [Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval])
  split
  · next h => subst h; simp
  · rfl

theorem eval_mkOr (env : Nat -> Bool) (l r : Source) :
    Cert.eval env (mkOr l r) = (Cert.eval env l || Cert.eval env r) := by
  unfold mkOr
  split <;> try (simp [Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval])
  split
  · next h => subst h; simp
  · rfl

theorem eval_allS (env : Nat -> Bool) (xs : List Source) :
    Cert.eval env (allS xs) = xs.all (Cert.eval env) := by
  rw [allS, reduceBalanced_hom .top mkAnd (Cert.eval env) (· && ·) true (eval_mkAnd env)
    (fun x y z => Bool.and_assoc x y z) Bool.and_true rfl, foldr_and_eq_all]

theorem eval_anyS (env : Nat -> Bool) (xs : List Source) :
    Cert.eval env (anyS xs) = xs.any (Cert.eval env) := by
  rw [anyS, reduceBalanced_hom .bot mkOr (Cert.eval env) (· || ·) false (eval_mkOr env)
    (fun x y z => Bool.or_assoc x y z) Bool.or_false rfl, foldr_or_eq_any]

theorem atomsBelow_mkNot {n : Nat} {s : Source} (h : atomsBelow n s = true) :
    atomsBelow n (mkNot s) = true := by
  cases s <;> simp_all [mkNot, atomsBelow]

theorem atomsBelow_mkAnd {n : Nat} {l r : Source} (hl : atomsBelow n l = true)
    (hr : atomsBelow n r = true) : atomsBelow n (mkAnd l r) = true := by
  unfold mkAnd
  split <;> try simp_all [atomsBelow]
  split <;> simp_all [atomsBelow]

theorem atomsBelow_mkOr {n : Nat} {l r : Source} (hl : atomsBelow n l = true)
    (hr : atomsBelow n r = true) : atomsBelow n (mkOr l r) = true := by
  unfold mkOr
  split <;> try simp_all [atomsBelow]
  split <;> simp_all [atomsBelow]

theorem atomsBelow_allS {n : Nat} (xs : List Source)
    (h : forall x, x ∈ xs -> atomsBelow n x = true) : atomsBelow n (allS xs) = true :=
  reduceBalanced_pred (fun s => atomsBelow n s = true) .top mkAnd rfl
    (fun _ _ => atomsBelow_mkAnd) xs h

theorem atomsBelow_anyS {n : Nat} (xs : List Source)
    (h : forall x, x ∈ xs -> atomsBelow n x = true) : atomsBelow n (anyS xs) = true :=
  reduceBalanced_pred (fun s => atomsBelow n s = true) .bot mkOr rfl
    (fun _ _ => atomsBelow_mkOr) xs h

theorem eval_sumW (env : VmRowEnv) (xs : List WindowExpr) :
    (sumW xs).eval env = (xs.map (WindowExpr.eval env)).sum := by
  rw [sumW, reduceBalanced_hom (.const 0) .add (WindowExpr.eval env) (· + ·) 0
    (fun _ _ => rfl) (fun x y z => Int.add_assoc x y z) Int.add_zero rfl]
  rfl

/-! ## 10. Row-major indices -/

theorem horner_acc (acc : Nat) (l : List (Nat × Nat)) :
    horner acc l = acc * (l.map Prod.fst).prod + horner 0 l := by
  induction l generalizing acc with
  | nil => simp [horner]
  | cons x rest ih =>
      obtain ⟨c, v⟩ := x
      simp only [horner, List.map_cons, List.prod_cons]
      rw [ih (acc * c + v), ih (0 * c + v)]
      ring

theorem map_fst_zip {cs vs : List Nat} (h : List.Forall₂ (fun v c => v < c) vs cs) :
    (cs.zip vs).map Prod.fst = cs := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem horner_decode {cs vs : List Nat} (h : List.Forall₂ (fun v c => v < c) vs cs) :
    horner 0 (cs.zip vs) < cs.prod /\ decodeRowMajor cs (horner 0 (cs.zip vs)) = vs := by
  induction h with
  | nil => simp [horner, decodeRowMajor]
  | @cons v c vs cs hvc hrest ih =>
      have hsplit : horner 0 ((c :: cs).zip (v :: vs)) = v * cs.prod + horner 0 (cs.zip vs) := by
        simp only [List.zip_cons_cons, horner]
        rw [horner_acc, map_fst_zip hrest]
        ring
      have hpos : 0 < cs.prod := by omega
      rw [hsplit]
      refine ⟨?_, ?_⟩
      · simp only [List.prod_cons]
        calc v * cs.prod + horner 0 (cs.zip vs) < v * cs.prod + cs.prod := by omega
          _ = (v + 1) * cs.prod := by ring
          _ ≤ c * cs.prod := Nat.mul_le_mul_right _ hvc
      · simp only [decodeRowMajor]
        have hdiv : (v * cs.prod + horner 0 (cs.zip vs)) / cs.prod = v := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt ih.1, Nat.zero_add]
        have hmod : (v * cs.prod + horner 0 (cs.zip vs)) % cs.prod = horner 0 (cs.zip vs) := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ih.1]
        rw [hdiv, hmod, ih.2]

theorem decode_horner (cs : List Nat) (flat : Nat) (h : flat < cs.prod) :
    List.Forall₂ (fun v c => v < c) (decodeRowMajor cs flat) cs /\
      horner 0 (cs.zip (decodeRowMajor cs flat)) = flat := by
  induction cs generalizing flat with
  | nil => simp at h; subst h; simp [decodeRowMajor, horner]
  | cons c cs ih =>
      simp only [List.prod_cons] at h
      have hpos : 0 < cs.prod := by
        rcases Nat.eq_zero_or_pos cs.prod with h0 | h0
        · rw [h0] at h; simp at h
        · exact h0
      obtain ⟨hf, hh⟩ := ih (flat % cs.prod) (Nat.mod_lt _ hpos)
      refine ⟨List.Forall₂.cons ?_ hf, ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hpos).mpr h
      · simp only [decodeRowMajor, List.zip_cons_cons, horner]
        rw [horner_acc, map_fst_zip hf, hh]
        simp only [Nat.zero_mul, Nat.zero_add]
        rw [Nat.mul_comm]
        exact Nat.div_add_mod flat cs.prod

/-! ## 11. Layout and the atom environment -/

theorem getD_append_left' {α : Type} {l1 l2 : List α} {i : Nat} (h : i < l1.length) (a : α) :
    (l1 ++ l2).getD i a = l1.getD i a := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type} {l1 l2 : List α} {i : Nat} (h : l1.length ≤ i) (a : α) :
    (l1 ++ l2).getD i a = l2.getD (i - l1.length) a := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem inputBits_length (ty : LType) (v : Nat) : (inputBits ty v).length = ty.atomCount := by
  cases ty <;> simp [inputBits, LType.atomCount]

theorem layoutFrom_length (next : Nat) (ds : List InputDecl) :
    (layoutFrom next ds).length = ds.length := by
  induction ds generalizing next with
  | nil => rfl
  | cons d ds ih => simp [layoutFrom, ih]

theorem layoutFrom_getElem? (next : Nat) (ds : List InputDecl) (i : Nat) (hi : i < ds.length) :
    (layoutFrom next ds)[i]? = some (next + atomTotal (ds.take i), ds[i].ty.atomCount) := by
  induction ds generalizing next i with
  | nil => simp at hi
  | cons d ds ih =>
      cases i with
      | zero => simp [layoutFrom, atomTotal]
      | succ i =>
          simp only [layoutFrom, List.getElem?_cons_succ, List.take_succ_cons,
            List.getElem_cons_succ]
          rw [ih (next + d.ty.atomCount) i (by simpa using hi)]
          simp [atomTotal, Nat.add_assoc]

theorem atomTotal_cons (d : InputDecl) (ds : List InputDecl) :
    atomTotal (d :: ds) = d.ty.atomCount + atomTotal ds := by
  simp [atomTotal]

theorem atomTotal_take_add_le (ds : List InputDecl) (i : Nat) (hi : i < ds.length) :
    atomTotal (ds.take i) + ds[i].ty.atomCount ≤ atomTotal ds := by
  induction ds generalizing i with
  | nil => simp at hi
  | cons d ds ih =>
      cases i with
      | zero => simp [atomTotal]
      | succ i =>
          simp only [List.take_succ_cons, atomTotal_cons, List.getElem_cons_succ]
          have := ih i (by simpa using hi)
          omega

theorem encodeRow_getD (ds : List InputDecl) (vs : List Nat) (hlen : vs.length = ds.length)
    (i : Nat) (hi : i < ds.length) (k : Nat) (hk : k < ds[i].ty.atomCount) :
    (encodeRow ds vs).getD (atomTotal (ds.take i) + k) false =
      (inputBits ds[i].ty (vs.getD i 0)).getD k false := by
  induction ds generalizing vs i with
  | nil => simp at hi
  | cons d ds ih =>
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          cases i with
          | zero =>
              simp only [List.take_zero, encodeRow, List.getElem_cons_zero, List.getD_cons_zero]
              simp only [atomTotal, List.map_nil, List.sum_nil, Nat.zero_add]
              rw [getD_append_left' (by rw [inputBits_length]; exact hk)]
          | succ i =>
              simp only [List.take_succ_cons, atomTotal_cons, encodeRow, List.getElem_cons_succ,
                List.getD_cons_succ]
              simp only [List.getElem_cons_succ] at hk
              rw [Nat.add_assoc, getD_append_right' (by rw [inputBits_length]; omega)]
              rw [inputBits_length, Nat.add_sub_cancel_left]
              exact ih vs hlen i (by simpa using hi) hk

/-- The atom an input's `k`-th column holds is the `k`-th one-hot bit of its value. -/
theorem atomEnv_input (inputs : List InputDecl) (vals : List Nat)
    (hlen : vals.length = inputs.length) (i : Nat) (hi : i < inputs.length) (k : Nat)
    (hk : k < inputs[i].ty.atomCount) :
    atomEnv inputs vals (atomTotal (inputs.take i) + k) =
      (inputBits inputs[i].ty (vals.getD i 0)).getD k false :=
  encodeRow_getD inputs vals hlen i hi k hk

theorem layout_getElem? (inputs : List InputDecl) (i : Nat) (hi : i < inputs.length) :
    (layout inputs)[i]? = some (atomTotal (inputs.take i), inputs[i].ty.atomCount) := by
  rw [layout, layoutFrom_getElem? 0 inputs i hi, Nat.zero_add]

/-! ## 12. Terms -/

theorem termType_input {inputs : List InputDecl} {ctx : List LType} {i : Nat} {ty : LType}
    (h : termType inputs ctx (.input i) = .ok ty) :
    exists hi : i < inputs.length, inputs[i].ty = ty := by
  simp only [termType] at h
  split at h
  · next d hd =>
      cases h
      obtain ⟨hi, hdi⟩ := List.getElem?_eq_some_iff.mp hd
      exact ⟨hi, by rw [hdi]⟩
  · cases h

theorem termType_bound {inputs : List InputDecl} {ctx : List LType} {i : Nat} {ty : LType}
    (h : termType inputs ctx (.bound i) = .ok ty) :
    exists hi : i < ctx.length, ctx[i] = ty := by
  simp only [termType] at h
  split at h
  · next ty' hty =>
      cases h
      exact List.getElem?_eq_some_iff.mp hty
  · cases h

theorem termType_const {inputs : List InputDecl} {ctx : List LType} {ty' : LType} {v : Nat}
    {ty : LType} (h : termType inputs ctx (.const ty' v) = .ok ty) :
    ty = ty' /\ v < ty'.card /\ 0 < ty'.card := by
  simp only [termType, bind, Except.bind] at h
  split at h
  · cases h
  · next n hn =>
      obtain ⟨rfl, hpos⟩ := LType.checkCard_ok hn
      split at h
      · cases h; exact ⟨rfl, by assumption, hpos⟩
      · cases h

theorem termType_value {inputs : List InputDecl} {ctx : List LType} {vals bvals : List Nat}
    (hv : ValuesOk inputs vals) (hb : BvalsOk ctx bvals) {t : Term} {ty : LType}
    (h : termType inputs ctx t = .ok ty) : evalTerm vals bvals t < ty.card := by
  cases t with
  | input i =>
      obtain ⟨hi, rfl⟩ := termType_input h
      exact hv.2 i hi
  | bound i =>
      obtain ⟨hi, rfl⟩ := termType_bound h
      exact hb.2 i hi
  | const ty' v =>
      obtain ⟨rfl, hv', _⟩ := termType_const h
      exact hv'

theorem beq_eq_decide_symm (a b : Nat) : (a == b) = decide (b = a) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : ¬ b = a := fun e => h e.symm
    simp [h, h']

theorem getD_map_range {α : Type} (n : Nat) (f : Nat -> α) (k : Nat) (hk : k < n) (d : α) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hk]

/-- A well-typed term lowers to exactly `card` one-hot bits, bit `k` true iff its value is `k`. -/
theorem termBits_spec {inputs : List InputDecl} {ctx : List LType} {vals bvals : List Nat}
    (hv : ValuesOk inputs vals) (_hb : BvalsOk ctx bvals) {t : Term} {ty : LType}
    (h : termType inputs ctx t = .ok ty) :
    (termBits inputs bvals ctx t).length = ty.card /\
      forall k, k < ty.card ->
        Cert.eval (atomEnv inputs vals) ((termBits inputs bvals ctx t).getD k .bot) =
          decide (evalTerm vals bvals t = k) := by
  cases t with
  | input i =>
      obtain ⟨hi, hty⟩ := termType_input h
      have hval := hv.2 i hi
      have hdi : inputs[i]? = some inputs[i] := List.getElem?_eq_getElem hi
      have hlay := layout_getElem? inputs i hi
      have hbits := fun k hk => atomEnv_input inputs vals hv.1 i hi k hk
      subst hty
      simp only [termBits, hdi, hlay, evalTerm]
      generalize hT : inputs[i].ty = T at hval hbits
      cases T with
      | bool =>
          dsimp only
          refine ⟨rfl, ?_⟩
          intro k hk
          have h0 := hbits 0 (by simp [LType.atomCount])
          simp only [Nat.add_zero, inputBits, List.getD_cons_zero] at h0
          simp only [LType.card] at hk hval
          rcases (by omega : k = 0 \/ k = 1) with rfl | rfl
          · simp only [List.getD_cons_zero, eval_mkNot, Cert.eval,
              Dregg2.Logic.CompilationCertificateBundle.Source.eval, h0]
            rcases (by omega : vals.getD i 0 = 0 \/ vals.getD i 0 = 1) with hz | hz <;>
              (simp only [hz]) <;> decide
          · simp only [List.getD_cons_succ, List.getD_cons_zero, Cert.eval,
              Dregg2.Logic.CompilationCertificateBundle.Source.eval, h0]
            rcases (by omega : vals.getD i 0 = 0 \/ vals.getD i 0 = 1) with hz | hz <;>
              (simp only [hz]) <;> decide
      | finite n =>
          dsimp only
          refine ⟨by simp [LType.card], ?_⟩
          intro k hk
          simp only [LType.card] at hk
          rw [getD_map_range n _ k hk]
          simp only [Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval]
          rw [hbits k (by simpa [LType.atomCount] using hk)]
          simp only [inputBits]
          rw [getD_map_range n _ k hk]
          exact beq_eq_decide_symm _ _
      | unbounded =>
          simp [LType.card]
  | bound i =>
      obtain ⟨hi, hty⟩ := termType_bound h
      have hget : ctx.getD i .unbounded = ty := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hty]; rfl
      simp only [termBits, hget, evalTerm]
      refine ⟨by simp, ?_⟩
      intro k hk
      rw [getD_map_range _ _ k hk, eval_constS]
      exact beq_eq_decide_symm _ _
  | const ty' v =>
      obtain ⟨rfl, _, _⟩ := termType_const h
      simp only [termBits, evalTerm]
      refine ⟨by simp, ?_⟩
      intro k hk
      rw [getD_map_range _ _ k hk, eval_constS]
      exact beq_eq_decide_symm _ _

/-! ## 13. Formulae: the lowering computes the source meaning -/

theorem getD_eq_getElem' {α : Type} (l : List α) (i : Nat) (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_map_getElem {α : Type} (l : List α) (g : α -> Nat) (i : Nat) (h : i < l.length) :
    (l.map g).getD i 0 = g l[i] := by
  rw [getD_eq_getElem' _ i (by simpa using h), List.getElem_map]

theorem BvalsOk.cons {ctx : List LType} {bvals : List Nat} (hb : BvalsOk ctx bvals)
    (ty : LType) (v : Nat) (hv : v < ty.card) : BvalsOk (ty :: ctx) (v :: bvals) := by
  refine ⟨by simp [hb.1], ?_⟩
  intro i hi
  cases i with
  | zero => simpa using hv
  | succ i =>
      simp only [List.getD_cons_succ, List.getElem_cons_succ]
      exact hb.2 i (by simpa using hi)

/-- Equality of two one-hot vectors of values below `n`. -/
theorem any_zipWith_onehot (env : Nat -> Bool) (n : Nat) (bl br : List Source) (x y : Nat)
    (hl : bl.length = n) (hr : br.length = n) (hx : x < n) (hy : y < n)
    (hbl : forall k, k < n -> Cert.eval env (bl.getD k .bot) = decide (x = k))
    (hbr : forall k, k < n -> Cert.eval env (br.getD k .bot) = decide (y = k)) :
    (bl.zipWith mkAnd br).any (Cert.eval env) = (x == y) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨z, hz, hez⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hz
    rw [List.getElem_zipWith, eval_mkAnd] at hez
    have hk' : k < n := by simp [List.length_zipWith, hl, hr] at hk; omega
    have h1 := hbl k hk'
    have h2 := hbr k hk'
    rw [getD_eq_getElem' bl k (by omega)] at h1
    rw [getD_eq_getElem' br k (by omega)] at h2
    rw [h1, h2] at hez
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hez
    omega
  · intro hxy
    subst hxy
    have hlen : x < (bl.zipWith mkAnd br).length := by simp [List.length_zipWith, hl, hr, hx]
    refine ⟨_, List.getElem_mem hlen, ?_⟩
    rw [List.getElem_zipWith, eval_mkAnd]
    have h1 := hbl x hx
    have h2 := hbr x hx
    rw [getD_eq_getElem' bl x (by omega)] at h1
    rw [getD_eq_getElem' br x (by omega)] at h2
    rw [h1, h2]
    simp

theorem checkArgs_spec {inputs : List InputDecl} {ctx : List LType} :
    forall (tys : List LType) (args : List Term), tys.length = args.length ->
      checkArgs inputs ctx tys args = .ok () ->
      forall i (hi : i < tys.length), exists hj : i < args.length,
        termType inputs ctx args[i] = .ok tys[i] := by
  intro tys
  induction tys with
  | nil => intro _ _ _ i hi; simp at hi
  | cons ty tys ih =>
      intro args hlen h i hi
      cases args with
      | nil => simp at hlen
      | cons arg args =>
          simp only [checkArgs] at h
          cases hn : ty.checkCard with
          | error e => rw [hn] at h; cases h
          | ok n =>
              rw [hn] at h
              cases haty : termType inputs ctx arg with
              | error e => simp only [bind, Except.bind, haty] at h; cases h
              | ok aty =>
                  by_cases hsame : ty = aty
                  · subst hsame
                    simp only [bind, Except.bind, haty, requireSame, ite_true] at h
                    cases i with
                    | zero => exact ⟨by simp, by simpa using haty⟩
                    | succ i =>
                        obtain ⟨hj, hj'⟩ := ih args (by simpa using hlen) h i (by simpa using hi)
                        exact ⟨by simpa using hj, by simpa using hj'⟩
                  · simp [bind, Except.bind, haty, requireSame, hsame] at h

theorem any_filterMap_if {α β : Type} (xs : List α) (p : α -> Bool) (g : α -> β) (q : β -> Bool) :
    (xs.filterMap fun x => if p x then some (g x) else none).any q =
      xs.any (fun x => p x && q (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hp : p x <;> simp [hp, ih]

/-- One truth-table row: its conjunction holds exactly when the arguments' values are the
row's decoded tuple. -/
theorem eval_predRow (env : Nat -> Bool) (D argvals : List Nat) (argBits : List (List Source))
    (hlenD : D.length = argBits.length) (hlenA : argvals.length = argBits.length)
    (hbits : forall i (hi : i < D.length),
      Cert.eval env ((argBits.getD i []).getD D[i] .bot) = decide (argvals.getD i 0 = D[i])) :
    ((D.zipIdx.map fun (sel, i) => (argBits.getD i []).getD sel .bot).all (Cert.eval env)) =
      decide (D = argvals) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro hall
    apply List.ext_getElem (by omega)
    intro i h1 h2
    have hmem : (D[i], i) ∈ D.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]; simp [h1]
    have := hall _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
    rw [hbits i h1] at this
    have h := of_decide_eq_true this
    rw [getD_eq_getElem' argvals i h2] at h
    exact h.symm
  · intro hDA z hz
    obtain ⟨⟨sel, i⟩, hmem, rfl⟩ := List.mem_map.mp hz
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    simp only at hmem
    obtain ⟨hi, hsel⟩ := List.getElem?_eq_some_iff.mp hmem
    simp only
    rw [← hsel, hbits i hi]
    apply decide_eq_true
    subst hDA
    exact getD_eq_getElem' D i hi 0

theorem any_rows_eq_lookup (values : List Bool) (cs argvals : List Nat)
    (hlen : values.length = cs.prod) (hargs : List.Forall₂ (fun v c => v < c) argvals cs) :
    (List.range values.length).any
        (fun flat => values.getD flat false && decide (decodeRowMajor cs flat = argvals)) =
      values.getD (horner 0 (cs.zip argvals)) false := by
  rw [Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨flat, hflat, h⟩
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hv, hdec⟩ := h
    have hlt : flat < cs.prod := by rw [← hlen]; exact List.mem_range.mp hflat
    have := (decode_horner cs flat hlt).2
    rw [hdec] at this
    rw [this]; exact hv
  · intro hv
    obtain ⟨hlt, hdec⟩ := horner_decode hargs
    refine ⟨_, List.mem_range.mpr (by rw [hlen]; exact hlt), ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hv, hdec⟩

theorem forall2_of_index {vs cs : List Nat} (hlen : vs.length = cs.length)
    (h : forall i (hi : i < cs.length), vs.getD i 0 < cs[i]) :
    List.Forall₂ (fun v c => v < c) vs cs := by
  induction cs generalizing vs with
  | nil => cases vs with
    | nil => exact .nil
    | cons _ _ => simp at hlen
  | cons c cs ih =>
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          have h0 := h 0 (by simp)
          rw [List.getElem_cons_zero, List.getD_cons_zero] at h0
          refine .cons h0 (ih (by simpa using hlen) ?_)
          intro i hi
          have h1 := h (i + 1) (by simpa using hi)
          rw [List.getElem_cons_succ, List.getD_cons_succ] at h1
          exact h1

theorem forall2_length {vs cs : List Nat} (h : List.Forall₂ (fun v c => v < c) vs cs) :
    vs.length = cs.length := h.length_eq

theorem forall2_getElem {vs cs : List Nat} (h : List.Forall₂ (fun v c => v < c) vs cs)
    (i : Nat) (hi : i < vs.length) : vs[i] < cs[i]'(by rw [← h.length_eq]; exact hi) := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hvc _ ih =>
      cases i with
      | zero => simpa using hvc
      | succ i => simpa using ih i (by simpa using hi)

theorem all_congr_mem {α : Type} {xs : List α} {f g : α -> Bool}
    (h : forall x, x ∈ xs -> f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.all_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem any_congr_mem {α : Type} {xs : List α} {f g : α -> Bool}
    (h : forall x, x ∈ xs -> f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.any_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem lower_eval (limits : Limits) (inputs : List InputDecl) (vals : List Nat)
    (hv : ValuesOk inputs vals) :
    forall (f : Formula) (ctx : List LType) (bvals : List Nat), BvalsOk ctx bvals ->
      checkFormula limits inputs ctx f = .ok () ->
      Cert.eval (atomEnv inputs vals) (lower inputs bvals ctx f) = evalFormula vals bvals f := by
  intro f
  induction f with
  | top => intros; rfl
  | bot => intros; rfl
  | eq l r =>
      intro ctx bvals hb h
      simp only [checkFormula, bind, Except.bind] at h
      split at h
      · cases h
      · next lt hlt =>
          split at h
          · cases h
          · next rt hrt =>
              simp only [requireSame] at h
              split at h
              · next hsame =>
                  subst hsame
                  obtain ⟨hl1, hl2⟩ := termBits_spec hv hb hlt
                  obtain ⟨hr1, hr2⟩ := termBits_spec hv hb hrt
                  simp only [lower, evalFormula]
                  rw [eval_anyS]
                  exact any_zipWith_onehot _ lt.card _ _ _ _ hl1 hr1
                    (termType_value hv hb hlt) (termType_value hv hb hrt) hl2 hr2
              · cases h
  | pred table args =>
      intro ctx bvals hb h
      simp only [checkFormula, bind, Except.bind] at h
      split at h
      · cases h
      · next harity =>
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at harity
          split at h
          · cases h
          · next hargs =>
              split at h
              · cases h
              · next hentries =>
                  split at h
                  · cases h
                  · next hshape =>
                      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hshape
                      have hspec := checkArgs_spec table.argTypes args harity hargs
                      set cs := table.argTypes.map LType.card with hcs
                      set argvals := args.map (evalTerm vals bvals) with hav
                      have hlenA : argvals.length = cs.length := by
                        simp [hav, hcs, harity]
                      have hfa : List.Forall₂ (fun v c => v < c) argvals cs := by
                        apply forall2_of_index hlenA
                        intro i hi
                        have hi' : i < table.argTypes.length := by simpa [hcs] using hi
                        obtain ⟨hj, hty⟩ := hspec i hi'
                        have := termType_value hv hb hty
                        rw [hav, getD_map_getElem args _ i hj]
                        simpa [hcs] using this
                      simp only [lower, evalFormula]
                      rw [eval_anyS, any_filterMap_if]
                      rw [← any_rows_eq_lookup table.values cs argvals hshape hfa]
                      apply List.any_congr rfl
                      intro flat
                      by_cases hflat : flat < table.values.length
                      · congr 1
                        rw [eval_allS]
                        have hdec := (decode_horner cs flat (by rw [← hshape]; exact hflat)).1
                        apply eval_predRow
                        · rw [List.length_map, forall2_length hdec, hcs, List.length_map, harity]
                        · simp [hav]
                        · intro i hi
                          have hiA : i < table.argTypes.length := by
                            rw [forall2_length hdec] at hi; simpa [hcs] using hi
                          obtain ⟨hj, hty⟩ := hspec i hiA
                          obtain ⟨_, hb2⟩ := termBits_spec hv hb hty
                          have hsel := forall2_getElem hdec i hi
                          have hsel' : (decodeRowMajor cs flat)[i] < table.argTypes[i].card := by
                            simpa [hcs] using hsel
                          rw [getD_eq_getElem' _ i (by simpa using hj), List.getElem_map]
                          rw [hb2 _ hsel', hav, getD_map_getElem args _ i hj]
                      · have : table.values.getD flat false = false := by
                          rw [List.getD_eq_getElem?_getD,
                            List.getElem?_eq_none (Nat.le_of_not_lt hflat)]
                          rfl
                        rw [this, Bool.false_and, Bool.false_and]
  | not p ih =>
      intro ctx bvals hb h
      simp only [lower, evalFormula, eval_mkNot]
      rw [ih ctx bvals hb h]
  | and p q ihp ihq =>
      intro ctx bvals hb h
      simp only [checkFormula, bind, Except.bind] at h
      split at h
      · cases h
      · next hp =>
          simp only [lower, evalFormula, eval_mkAnd]
          rw [ihp ctx bvals hb hp, ihq ctx bvals hb h]
  | or p q ihp ihq =>
      intro ctx bvals hb h
      simp only [checkFormula, bind, Except.bind] at h
      split at h
      · cases h
      · next hp =>
          simp only [lower, evalFormula, eval_mkOr]
          rw [ihp ctx bvals hb hp, ihq ctx bvals hb h]
  | all ty body ih =>
      intro ctx bvals hb h
      simp only [checkFormula, bind, Except.bind] at h
      split at h
      · cases h
      · simp only [lower, evalFormula, eval_allS, List.all_map]
        apply all_congr_mem
        intro v hvl
        exact ih (ty :: ctx) (v :: bvals) (hb.cons ty v (List.mem_range.mp hvl)) h
  | ex ty body ih =>
      intro ctx bvals hb h
      simp only [checkFormula, bind, Except.bind] at h
      split at h
      · cases h
      · simp only [lower, evalFormula, eval_anyS, List.any_map]
        apply any_congr_mem
        intro v hvl
        exact ih (ty :: ctx) (v :: bvals) (hb.cons ty v (List.mem_range.mp hvl)) h

/-! ## 14. The lowering only reads atom columns -/

theorem getD_mem_or {α : Type} (l : List α) (k : Nat) (d : α) : l.getD k d = d \/ l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => left; rfl
  | some x => right; exact List.mem_of_getElem? h

theorem termBits_atoms (inputs : List InputDecl) (bvals : List Nat) (ctx : List LType) (t : Term) :
    forall s, s ∈ termBits inputs bvals ctx t -> atomsBelow (atomTotal inputs) s = true := by
  intro s hs
  cases t with
  | input i =>
      simp only [termBits] at hs
      split at hs
      · next d first cnt hd hl =>
          obtain ⟨hi, hdi⟩ := List.getElem?_eq_some_iff.mp hd
          have hlay := layout_getElem? inputs i hi
          rw [hl] at hlay
          simp only [Option.some.injEq, Prod.mk.injEq] at hlay
          obtain ⟨rfl, -⟩ := hlay
          have hle := atomTotal_take_add_le inputs i hi
          rw [hdi] at hle
          split at hs
          · next hty =>
              rw [hty] at hle
              simp only [LType.atomCount] at hle
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
              rcases hs with rfl | rfl
              · apply atomsBelow_mkNot; simp [atomsBelow]; omega
              · simp [atomsBelow]; omega
          · next n hty =>
              rw [hty] at hle
              simp only [LType.atomCount] at hle
              obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
              simp [atomsBelow]; have := List.mem_range.mp hk; omega
          · simp at hs
      · simp at hs
  | bound i =>
      simp only [termBits] at hs
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hs
      cases (v == bvals.getD i 0) <;> rfl
  | const ty v =>
      simp only [termBits] at hs
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hs
      cases (c == v) <;> rfl

theorem lower_atoms (inputs : List InputDecl) :
    forall (f : Formula) (bvals : List Nat) (ctx : List LType),
      atomsBelow (atomTotal inputs) (lower inputs bvals ctx f) = true := by
  intro f
  induction f with
  | top => intros; rfl
  | bot => intros; rfl
  | eq l r =>
      intro bvals ctx
      simp only [lower]
      apply atomsBelow_anyS
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [List.getElem_zipWith]
      exact atomsBelow_mkAnd (termBits_atoms _ _ _ _ _ (List.getElem_mem _))
        (termBits_atoms _ _ _ _ _ (List.getElem_mem _))
  | pred table args =>
      intro bvals ctx
      simp only [lower]
      apply atomsBelow_anyS
      intro x hx
      obtain ⟨flat, -, hfx⟩ := List.mem_filterMap.mp hx
      split at hfx
      · simp only [Option.some.injEq] at hfx
        subst hfx
        apply atomsBelow_allS
        intro y hy
        obtain ⟨⟨sel, i⟩, -, rfl⟩ := List.mem_map.mp hy
        rcases getD_mem_or ((args.map (termBits inputs bvals ctx)).getD i []) sel .bot with h | h
        · simp only; rw [h]; rfl
        · simp only
          rcases getD_mem_or (args.map (termBits inputs bvals ctx)) i [] with h' | h'
          · rw [h'] at h; simp at h
          · obtain ⟨t, -, ht⟩ := List.mem_map.mp h'
            rw [← ht] at h ⊢
            exact termBits_atoms _ _ _ _ _ h
      · cases hfx
  | not p ih => intro bvals ctx; exact atomsBelow_mkNot (ih bvals ctx)
  | and p q ihp ihq => intro bvals ctx; exact atomsBelow_mkAnd (ihp bvals ctx) (ihq bvals ctx)
  | or p q ihp ihq => intro bvals ctx; exact atomsBelow_mkOr (ihp bvals ctx) (ihq bvals ctx)
  | all ty body ih =>
      intro bvals ctx
      apply atomsBelow_allS
      intro x hx
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      exact ih _ _
  | ex ty body ih =>
      intro bvals ctx
      apply atomsBelow_anyS
      intro x hx
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      exact ih _ _

/-! ## 15. What a successful compilation guarantees -/

theorem inputAtoms_ok {ty : LType} {n : Nat} (h : inputAtoms ty = .ok n) :
    ty ≠ .unbounded /\ n = ty.atomCount := by
  cases ty with
  | bool => cases h; exact ⟨by simp, rfl⟩
  | finite m =>
      obtain ⟨rfl, _⟩ := LType.checkCard_ok h
      exact ⟨by simp, rfl⟩
  | unbounded => cases h

theorem checkInputs_spec (limits : Limits) :
    forall (ds : List InputDecl) (seen : List String) (next : Nat), next ≤ limits.atomMax ->
      checkInputs limits seen next ds = .ok () ->
      next + atomTotal ds ≤ limits.atomMax /\ forall d, d ∈ ds -> d.ty ≠ .unbounded := by
  intro ds
  induction ds with
  | nil => intro seen next hle _; simpa [atomTotal] using hle
  | cons d ds ih =>
      intro seen next hle h
      simp only [checkInputs] at h
      by_cases hdup : seen.contains d.name = true
      · have hmem : d.name ∈ seen := by simpa using hdup
        simp [hmem, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      · simp only [hdup, bind, Except.bind] at h
        cases hn : inputAtoms d.ty with
        | error e => simp [hn] at h
        | ok n =>
            simp only [hn] at h
            obtain ⟨hne, rfl⟩ := inputAtoms_ok hn
            by_cases hlim : limits.atomMax < next + d.ty.atomCount
            · simp [hlim, throw, throwThe, MonadExceptOf.throw] at h
            · simp only [hlim] at h
              obtain ⟨h1, h2⟩ := ih _ _ (by omega) h
              refine ⟨?_, ?_⟩
              · rw [atomTotal_cons]; omega
              · intro d' hd'
                rcases List.mem_cons.mp hd' with rfl | hd'
                · exact hne
                · exact h2 d' hd'

/-- Inversion of `compileProgram`: the artifact is exactly the descriptor of the lowered
formula, for admitted inputs and a type-correct formula. -/
theorem compileProgram_spec {limits : Limits} {name : String} {p : Program} {c : Compiled}
    (h : compileProgram limits name p = .ok c) :
    atomTotal p.inputs ≤ atomCeiling /\
    (forall d, d ∈ p.inputs -> d.ty ≠ .unbounded) /\
    checkFormula limits p.inputs [] p.formula = .ok () /\
    c = { descriptor := programDescriptor name p.inputs (lower p.inputs [] [] p.formula)
        , relation := lower p.inputs [] [] p.formula
        , layout := layout p.inputs
        , logicalAtoms := atomTotal p.inputs } := by
  simp only [compileProgram, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · next hin =>
        split at h
        · cases h
        · next hf =>
            split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · cases h
                · cases h
                  obtain ⟨h1, h2⟩ := checkInputs_spec limits p.inputs [] 0 (Nat.zero_le _) hin
                  refine ⟨?_, h2, hf, rfl⟩
                  have : limits.atomMax ≤ atomCeiling := Nat.min_le_right _ _
                  omega

/-! ## 16. One-hot gates -/

theorem oneHotGates_mem :
    forall (ds : List InputDecl) (next : Nat) (c : VmConstraint2),
      c ∈ oneHotGates (ds.zip (layoutFrom next ds)) ->
      exists j, exists hj : j < ds.length, exists n, ds[j].ty = .finite n /\
        c = .windowGate (oneHotConstraint (next + atomTotal (ds.take j)) n) := by
  intro ds
  induction ds with
  | nil => intro next c hc; simp [layoutFrom, oneHotGates] at hc
  | cons d ds ih =>
      intro next c hc
      simp only [layoutFrom, List.zip_cons_cons, oneHotGates] at hc
      have tail : c ∈ oneHotGates (ds.zip (layoutFrom (next + d.ty.atomCount) ds)) ->
          exists j, exists hj : j < (d :: ds).length, exists n, (d :: ds)[j].ty = .finite n /\
            c = .windowGate (oneHotConstraint (next + atomTotal ((d :: ds).take j)) n) := by
        intro hc'
        obtain ⟨j, hj, n, hty, rfl⟩ := ih _ c hc'
        refine ⟨j + 1, by simpa using hj, n, by simpa using hty, ?_⟩
        simp [atomTotal_cons, Nat.add_assoc]
      split at hc
      · next n hT =>
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ⟨0, by simp, n, by simpa using hT, by simp [atomTotal]⟩
          · exact tail hc
      · exact tail hc

theorem eval_oneHotBody (env : VmRowEnv) (first n : Nat) :
    (oneHotBody first n).eval env =
      ((List.range n).map fun k => env.loc (first + k)).sum + (-1) := by
  simp only [oneHotBody, WindowExpr.eval, eval_sumW, List.map_map]
  rfl

theorem sum_onehot_range (n v : Nat) (hv : v < n) :
    ((List.range n).map fun k => bitInt (k == v)).sum = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      by_cases hvn : v = n
      · subst hvn
        have hz : ((List.range v).map fun k => bitInt (k == v)).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
          have : k ≠ v := Nat.ne_of_lt (List.mem_range.mp hk)
          simp [bitInt, this]
        rw [hz]
        simp [bitInt]
      · rw [ih (by omega)]
        have hnv : n ≠ v := fun e => hvn e.symm
        simp [bitInt, hnv]

/-! ## 17. Completeness: every well-typed true input has a one-row witness -/

/-- `Satisfied2` of the compiled descriptor plus field-canonical main columns. -/
structure ProgramSatisfied2 (hash : List Int -> Int) (c : Compiled) (minit : Int -> Int)
    (mfin : Int -> Int × Nat) (maddrs : List Int) (t : VmTrace) : Prop
    extends Satisfied2 hash c.descriptor minit mfin maddrs t where
  canonicalAtoms : forall i, i < t.rows.length ->
    CanonicalAtoms c.descriptor.traceWidth (envAt t i).loc

/-- The canonical one-row witness of source values. -/
def witnessTrace (inputs : List InputDecl) (vals : List Nat) : VmTrace :=
  traceOf (atomEnv inputs vals)

theorem programConstraints_window (inputs : List InputDecl) (rel : Source) :
    forall c, c ∈ programConstraints inputs rel -> exists w, c = .windowGate w := by
  intro c hc
  simp only [programConstraints, List.mem_append, List.mem_map, List.mem_singleton] at hc
  rcases hc with (⟨_, _, rfl⟩ | hc) | rfl
  · exact ⟨_, rfl⟩
  · obtain ⟨_, _, _, _, rfl⟩ := oneHotGates_mem inputs 0 c (by simpa [layout] using hc)
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem memOpsOf_programDescriptor (name : String) (inputs : List InputDecl) (rel : Source) :
    memOpsOf (programDescriptor name inputs rel) = [] := by
  unfold memOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  obtain ⟨w, rfl⟩ := programConstraints_window inputs rel c hc
  rfl

theorem mapOpsOf_programDescriptor (name : String) (inputs : List InputDecl) (rel : Source) :
    mapOpsOf (programDescriptor name inputs rel) = [] := by
  unfold mapOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  obtain ⟨w, rfl⟩ := programConstraints_window inputs rel c hc
  rfl

theorem memLog_programDescriptor (name : String) (inputs : List InputDecl) (rel : Source)
    (t : VmTrace) : memLog (programDescriptor name inputs rel) t = [] := by
  simp [memLog, memOpsOf_programDescriptor]

theorem mapLog_programDescriptor (name : String) (inputs : List InputDecl) (rel : Source)
    (t : VmTrace) : mapLog (programDescriptor name inputs rel) t = [] := by
  simp [mapLog, mapOpsOf_programDescriptor]

theorem witnessTrace_loc (inputs : List InputDecl) (vals : List Nat) (a : Nat) :
    (envAt (witnessTrace inputs vals) 0).loc a = bitInt (atomEnv inputs vals a) := by
  simp [witnessTrace, envAt, traceOf, rowOf]

theorem bvalsOk_nil : BvalsOk [] [] := ⟨rfl, fun i hi => by simp at hi⟩

/-- **Completeness.**  Every well-typed source input making the program true yields a canonical
one-row trace satisfying the emitted descriptor: booleanity, one-hot and acceptance gates. -/
theorem program_complete (hash : List Int -> Int) {limits : Limits} {name : String}
    {p : Program} {c : Compiled} (hc : compileProgram limits name p = .ok c)
    (vals : List Nat) (hok : ValuesOk p.inputs vals) (htrue : evalProgram p vals = true) :
    ProgramSatisfied2 hash c (fun _ => 0) (fun _ => ((0 : Int), 0)) []
      (witnessTrace p.inputs vals) := by
  obtain ⟨_, _, hf, rfl⟩ := compileProgram_spec hc
  have hbound := lower_atoms p.inputs p.formula [] []
  have heval : Cert.eval (atomEnv p.inputs vals) (lower p.inputs [] [] p.formula) = true := by
    rw [lower_eval limits p.inputs vals hok p.formula [] [] bvalsOk_nil hf]; exact htrue
  have hpoly := sourcePoly_eval_rowOf (atomTotal p.inputs) _ (atomEnv p.inputs vals) hbound
  refine ⟨⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi cst hcst
    have hi0 : i = 0 := by simp [witnessTrace, traceOf] at hi; omega
    subst i
    simp only [programDescriptor, programConstraints, List.mem_append, List.mem_map,
      List.mem_singleton] at hcst
    rcases hcst with (⟨col, _, rfl⟩ | hcst) | rfl
    · simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, binaryConstraint]
      change (binaryBody col).eval (envAt (witnessTrace p.inputs vals) 0) ≡ 0 [ZMOD 2013265921]
      rw [binaryBody_eq]
      simp only [WindowExpr.eval, witnessTrace_loc]
      cases atomEnv p.inputs vals col <;> simp [bitInt]
    · obtain ⟨j, hj, n, hT, rfl⟩ := oneHotGates_mem p.inputs 0 cst (by simpa [layout] using hcst)
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, oneHotConstraint]
      rw [eval_oneHotBody]
      have hval : vals.getD j 0 < n := by
        have := hok.2 j hj; rwa [hT] at this
      have hcols : (List.range n).map
            (fun k => (envAt (witnessTrace p.inputs vals) 0).loc (0 + atomTotal (p.inputs.take j) + k)) =
          (List.range n).map (fun k => bitInt (k == vals.getD j 0)) := by
        apply List.map_congr_left
        intro k hk
        have hk' := List.mem_range.mp hk
        rw [witnessTrace_loc, Nat.zero_add,
          atomEnv_input p.inputs vals hok.1 j hj k (by rw [hT]; exact hk'), hT]
        simp only [inputBits]
        rw [getD_map_range n _ k hk']
      rw [hcols, sum_onehot_range n _ hval]
      exact Int.ModEq.refl 0
    · simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, acceptConstraint, acceptBody,
        WindowExpr.eval]
      have hp : (sourcePoly (lower p.inputs [] [] p.formula)).eval
          (envAt (witnessTrace p.inputs vals) 0) = 1 := by
        simpa [witnessTrace, heval, bitInt] using hpoly
      rw [hp]
      exact Int.ModEq.refl 0
  · intro i hi
    trivial
  · intro i hi r hr
    simp [programDescriptor] at hr
  · intro op hop
    rw [memLog_programDescriptor] at hop
    cases hop
  · rw [memLog_programDescriptor]
    trivial
  · rw [memLog_programDescriptor]
    exact memCheck_nil _ _
  · rw [memLog_programDescriptor]
    rfl
  · rw [mapLog_programDescriptor]
    rfl
  · intro i hi
    have hi0 : i = 0 := by simp [witnessTrace, traceOf] at hi; omega
    subst i
    simp only [witnessTrace, traceOf_loc]
    exact canonicalAtoms_rowOf _ _

/-! ## 18. Soundness: every satisfying row decodes to a true, well-typed source input -/

/-- Read source values back off a row: a Boolean column's integer, an enumeration's set index. -/
def decodeValue (row : Assignment) (first : Nat) : LType -> Nat
  | .bool => (row first).toNat
  | .finite n => ((List.range n).find? (fun k => row (first + k) == 1)).getD 0
  | .unbounded => 0

def decodeValsFrom (row : Assignment) (next : Nat) : List InputDecl -> List Nat
  | [] => []
  | d :: ds => decodeValue row next d.ty :: decodeValsFrom row (next + d.ty.atomCount) ds

def decodeVals (row : Assignment) (inputs : List InputDecl) : List Nat :=
  decodeValsFrom row 0 inputs

theorem decodeValsFrom_length (row : Assignment) (next : Nat) (ds : List InputDecl) :
    (decodeValsFrom row next ds).length = ds.length := by
  induction ds generalizing next with
  | nil => rfl
  | cons d ds ih => simp [decodeValsFrom, ih]

theorem sum_bits_bounds (n : Nat) (b : Nat -> Int) (hb : forall k, k < n -> b k = 0 \/ b k = 1) :
    0 ≤ ((List.range n).map b).sum /\ ((List.range n).map b).sum ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      have h1 := ih (fun k hk => hb k (by omega))
      rcases hb n (by omega) with h | h <;> simp [h] <;> omega

theorem onehot_unique (n : Nat) (b : Nat -> Int) (hb : forall k, k < n -> b k = 0 \/ b k = 1)
    (hsum : ((List.range n).map b).sum = 1) :
    exists k0, k0 < n /\ forall k, k < n -> b k = if k = k0 then 1 else 0 := by
  induction n with
  | zero => simp at hsum
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append] at hsum
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
      have hbounds := sum_bits_bounds n b (fun k hk => hb k (by omega))
      rcases hb n (by omega) with hn | hn
      · rw [hn, add_zero] at hsum
        obtain ⟨k0, hk0, hall⟩ := ih (fun k hk => hb k (by omega)) hsum
        refine ⟨k0, by omega, ?_⟩
        intro k hk
        by_cases hkn : k = n
        · subst hkn; rw [hn]; simp; omega
        · exact hall k (by omega)
      · rw [hn] at hsum
        have hz : ((List.range n).map b).sum = 0 := by omega
        refine ⟨n, by omega, ?_⟩
        intro k hk
        by_cases hkn : k = n
        · subst hkn; simp [hn]
        · have hk' : k < n := by omega
          have hzero : b k = 0 := by
            rcases hb k (by omega) with h | h
            · exact h
            · exfalso
              have := List.single_le_sum (fun x hx => by
                obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
                rcases hb j (by have := List.mem_range.mp hj; omega) with h' | h' <;> omega)
                (b k) (List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩)
              omega
          simp [hzero, hkn]

theorem find_onehot (n k0 : Nat) (b : Nat -> Int) (hk0 : k0 < n)
    (hb : forall k, k < n -> b k = if k = k0 then 1 else 0) :
    (List.range n).find? (fun k => b k == 1) = some k0 := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.find?_append]
      by_cases hkn : k0 = n
      · subst hkn
        have hnone : (List.range k0).find? (fun k => b k == 1) = none := by
          rw [List.find?_eq_none]
          intro k hk
          have hk' := List.mem_range.mp hk
          rw [hb k (by omega)]
          simp [Nat.ne_of_lt hk']
        rw [hnone]
        simp [hb k0 (by omega)]
      · rw [ih (by omega) (fun k hk => hb k (by omega))]
        rfl

/-- One input's columns decode to a value whose encoding is exactly those columns. -/
theorem decodeValue_spec (row : Assignment) (first : Nat) (ty : LType) (hne : ty ≠ .unbounded)
    (hbits : forall k, k < ty.atomCount -> row (first + k) = 0 \/ row (first + k) = 1)
    (honehot : forall n, ty = .finite n -> ((List.range n).map fun k => row (first + k)).sum = 1) :
    decodeValue row first ty < ty.card /\
      forall k, k < ty.atomCount ->
        row (first + k) = bitInt ((inputBits ty (decodeValue row first ty)).getD k false) := by
  cases ty with
  | bool =>
      have h0 := hbits 0 (by simp [LType.atomCount])
      simp only [Nat.add_zero] at h0
      refine ⟨?_, ?_⟩
      · simp only [decodeValue, LType.card]; omega
      · intro k hk
        simp only [LType.atomCount] at hk
        have : k = 0 := by omega
        subst this
        simp only [Nat.add_zero, decodeValue, inputBits, List.getD_cons_zero]
        rcases h0 with h | h <;> rw [h] <;> rfl
  | finite n =>
      obtain ⟨k0, hk0, hall⟩ := onehot_unique n (fun k => row (first + k))
        (fun k hk => hbits k (by simpa [LType.atomCount] using hk)) (honehot n rfl)
      have hfind := find_onehot n k0 (fun k => row (first + k)) hk0 hall
      have hdec : decodeValue row first (.finite n) = k0 := by
        simp only [decodeValue]; rw [hfind]; rfl
      rw [hdec]
      refine ⟨hk0, ?_⟩
      intro k hk
      simp only [LType.atomCount] at hk
      simp only [inputBits]
      rw [getD_map_range n _ k hk, hall k hk]
      by_cases h : k = k0 <;> simp [h, bitInt]
  | unbounded => exact absurd rfl hne

theorem decodeValsFrom_spec (row : Assignment) :
    forall (ds : List InputDecl) (next : Nat), (forall d, d ∈ ds -> d.ty ≠ .unbounded) ->
      (forall a, a < atomTotal ds -> row (next + a) = 0 \/ row (next + a) = 1) ->
      (forall j (hj : j < ds.length) n, ds[j].ty = .finite n ->
        ((List.range n).map fun k => row (next + atomTotal (ds.take j) + k)).sum = 1) ->
      ValuesOk ds (decodeValsFrom row next ds) /\
        forall a, a < atomTotal ds ->
          row (next + a) = bitInt ((encodeRow ds (decodeValsFrom row next ds)).getD a false) := by
  intro ds
  induction ds with
  | nil => intro next _ _ _; exact ⟨⟨rfl, fun i hi => by simp at hi⟩, fun a ha => by simp [atomTotal] at ha⟩
  | cons d ds ih =>
      intro next hne hbits honehot
      have hd := decodeValue_spec row next d.ty (hne d (by simp))
        (fun k hk => hbits k (by rw [atomTotal_cons]; omega))
        (fun n hn => by simpa [atomTotal] using honehot 0 (by simp) n (by simpa using hn))
      obtain ⟨hok, henc⟩ := ih (next + d.ty.atomCount) (fun d' hd' => hne d' (by simp [hd']))
        (fun a ha => by
          have := hbits (d.ty.atomCount + a) (by rw [atomTotal_cons]; omega)
          rwa [Nat.add_assoc])
        (fun j hj n hn => by
          have := honehot (j + 1) (by simpa using hj) n (by simpa using hn)
          simpa [atomTotal_cons, Nat.add_assoc] using this)
      refine ⟨⟨by simp [decodeValsFrom, decodeValsFrom_length], ?_⟩, ?_⟩
      · intro i hi
        cases i with
        | zero => simpa [decodeValsFrom] using hd.1
        | succ i => simpa [decodeValsFrom] using hok.2 i (by simpa using hi)
      · intro a ha
        simp only [decodeValsFrom, encodeRow]
        by_cases hlt : a < d.ty.atomCount
        · rw [getD_append_left' (by rw [inputBits_length]; exact hlt)]
          exact hd.2 a hlt
        · rw [getD_append_right' (by rw [inputBits_length]; omega), inputBits_length]
          have := henc (a - d.ty.atomCount) (by rw [atomTotal_cons] at ha; omega)
          rwa [Nat.add_assoc, Nat.add_sub_cancel' (by omega)] at this

theorem oneHotGates_complete :
    forall (ds : List InputDecl) (next j : Nat) (hj : j < ds.length) (n : Nat),
      ds[j].ty = .finite n ->
      .windowGate (oneHotConstraint (next + atomTotal (ds.take j)) n) ∈
        oneHotGates (ds.zip (layoutFrom next ds)) := by
  intro ds
  induction ds with
  | nil => intro next j hj; simp at hj
  | cons d ds ih =>
      intro next j hj n hT
      simp only [layoutFrom, List.zip_cons_cons, oneHotGates]
      cases j with
      | zero =>
          simp only [List.getElem_cons_zero] at hT
          simp [hT, atomTotal]
      | succ j =>
          have hmem := ih (next + d.ty.atomCount) j (by simpa using hj) n (by simpa using hT)
          have heq : next + d.ty.atomCount + atomTotal (ds.take j) =
              next + atomTotal ((d :: ds).take (j + 1)) := by
            simp [atomTotal_cons, Nat.add_assoc]
          rw [heq] at hmem
          split
          · exact List.mem_cons_of_mem _ hmem
          · exact hmem

theorem eval_congr_atoms {n : Nat} (s : Source) (hs : atomsBelow n s = true) {l r : Nat -> Bool}
    (h : forall a, a < n -> l a = r a) : Cert.eval l s = Cert.eval r s := by
  induction s with
  | atom a =>
      simp only [atomsBelow, decide_eq_true_eq] at hs
      exact h a hs
  | top => rfl
  | bot => rfl
  | not p ih =>
      simp only [atomsBelow] at hs
      simp [Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval] at ih ⊢
      rw [ih hs]
  | and p q ihp ihq =>
      simp only [atomsBelow, Bool.and_eq_true] at hs
      simp [Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval] at ihp ihq ⊢
      rw [ihp hs.1, ihq hs.2]
  | or p q ihp ihq =>
      simp only [atomsBelow, Bool.and_eq_true] at hs
      simp [Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval] at ihp ihq ⊢
      rw [ihp hs.1, ihq hs.2]

/-- **Soundness.**  On every row of a canonical satisfying trace, the atom columns are exactly the
canonical encoding of well-typed source values, and those values make the program true. -/
theorem program_sound {hash : List Int -> Int} {limits : Limits} {name : String} {p : Program}
    {c : Compiled} {minit : Int -> Int} {mfin : Int -> Int × Nat} {maddrs : List Int}
    {t : VmTrace} (hc : compileProgram limits name p = .ok c)
    (hsat : ProgramSatisfied2 hash c minit mfin maddrs t) :
    forall i, i < t.rows.length -> exists vals, ValuesOk p.inputs vals /\
      (forall a, a < atomTotal p.inputs -> (envAt t i).loc a = bitInt (atomEnv p.inputs vals a)) /\
      evalProgram p vals = true := by
  obtain ⟨hceil, hne, hf, rfl⟩ := compileProgram_spec hc
  intro i hi
  set env := envAt t i
  set rel := lower p.inputs [] [] p.formula
  have hgate := hsat.toSatisfied2.rowConstraints i hi
  have hcanon := hsat.canonicalAtoms i hi
  have hwidth : atomTotal p.inputs ≤ traceWidthOf p.inputs := Nat.le_max_right _ _
  have hbits : forall a, a < traceWidthOf p.inputs -> env.loc a = 0 \/ env.loc a = 1 := by
    intro a ha
    have hmem : VmConstraint2.windowGate (binaryConstraint a) ∈
        (programDescriptor name p.inputs rel).constraints := by
      simp only [programDescriptor, programConstraints, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨a, List.mem_range.mpr ha, rfl⟩)
    have h := hgate _ hmem
    have hmod : (binaryBody a).eval env ≡ 0 [ZMOD 2013265921] := by
      simpa [VmConstraint2.holdsAt, WindowConstraint.holdsAt, binaryConstraint] using h
    exact binary_of_modular_gate hcanon ha hmod
  have honehot : forall j (hj : j < p.inputs.length) n, p.inputs[j].ty = .finite n ->
      ((List.range n).map fun k => env.loc (0 + atomTotal (p.inputs.take j) + k)).sum = 1 := by
    intro j hj n hT
    suffices H : ((List.range n).map fun k => env.loc (atomTotal (p.inputs.take j) + k)).sum = 1 by
      simpa using H
    have hmem : VmConstraint2.windowGate (oneHotConstraint (atomTotal (p.inputs.take j)) n) ∈
        (programDescriptor name p.inputs rel).constraints := by
      simp only [programDescriptor, programConstraints, List.mem_append]
      exact Or.inl (Or.inr (by simpa [layout] using oneHotGates_complete p.inputs 0 j hj n hT))
    have h := hgate _ hmem
    simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, oneHotConstraint] at h
    rw [eval_oneHotBody, Int.modEq_zero_iff_dvd] at h
    have hle := atomTotal_take_add_le p.inputs j hj
    rw [hT] at hle
    simp only [LType.atomCount] at hle
    have hb := sum_bits_bounds n (fun k => env.loc (atomTotal (p.inputs.take j) + k))
      (fun k hk => hbits _ (by omega))
    obtain ⟨m, hm⟩ := h
    have hn : (n : Int) < 2013265921 := by
      have : n ≤ atomCeiling := by omega
      simp only [atomCeiling] at this; omega
    generalize ((List.range n).map fun k => env.loc (atomTotal (p.inputs.take j) + k)).sum = S
      at hm hb ⊢
    omega
  obtain ⟨hok, henc⟩ := decodeValsFrom_spec env.loc p.inputs 0 hne
    (fun a ha => by rw [Nat.zero_add]; exact hbits a (by omega)) honehot
  refine ⟨decodeVals env.loc p.inputs, hok, ?_, ?_⟩
  · intro a ha
    have := henc a ha
    rwa [Nat.zero_add] at this
  · have hbound := lower_atoms p.inputs p.formula [] []
    have hpoly := sourcePoly_eval env (atomTotal p.inputs) rel hbound
      (fun a ha => hbits a (by omega))
    have hacc : VmConstraint2.windowGate (acceptConstraint rel) ∈
        (programDescriptor name p.inputs rel).constraints := by
      simp [programDescriptor, programConstraints]
    have hmod : (acceptBody rel).eval env ≡ 0 [ZMOD 2013265921] := by
      simpa [VmConstraint2.holdsAt, WindowConstraint.holdsAt, acceptConstraint] using hgate _ hacc
    have htrue : Cert.eval (rowEnv env.loc) rel = true := by
      cases heval : Cert.eval (rowEnv env.loc) rel with
      | false =>
          have hp0 : (sourcePoly rel).eval env = 0 := by simpa [heval, bitInt] using hpoly
          simp only [acceptBody, WindowExpr.eval, hp0, zero_add] at hmod
          rw [Int.modEq_zero_iff_dvd] at hmod
          norm_num at hmod
      | true => rfl
    have hagree : forall a, a < atomTotal p.inputs ->
        rowEnv env.loc a = atomEnv p.inputs (decodeVals env.loc p.inputs) a := by
      intro a ha
      have := henc a ha
      rw [Nat.zero_add] at this
      simp only [rowEnv, this, atomEnv, decodeVals]
      cases (encodeRow p.inputs (decodeValsFrom env.loc 0 p.inputs)).getD a false <;> simp [bitInt]
    rw [eval_congr_atoms rel hbound hagree] at htrue
    exact (lower_eval limits p.inputs (decodeVals env.loc p.inputs) hok p.formula [] []
      bvalsOk_nil hf).symm.trans htrue

/-! ## 19. Source-hash identity: the reply binds the exact decoded bytes -/

theorem decodeProgram_canonical {bytes : List UInt8} {p : Program}
    (h : decodeProgram bytes = some p) : encodeProgram p = bytes := by
  unfold decodeProgram at h
  split at h
  · split at h
    · next he => cases h; exact he
    · cases h
  · cases h

/-- What an accepted compile request is: the program whose canonical encoding is exactly the
request bytes, compiled under the name `dregg-direct-logic-v1-<BLAKE3 of those bytes>`. -/
theorem compileBytes_spec {limits : Limits} {bytes : List UInt8} {p : Program} {c : Compiled}
    (h : compileBytes limits bytes = .ok (p, c)) :
    encodeProgram p = bytes /\ compileProgram limits (descriptorNameOf bytes) p = .ok c /\
      c.descriptor.name = descriptorNameOf bytes := by
  unfold compileBytes at h
  split at h
  · cases h
  · next p' hp =>
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · next c' hc =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨decodeProgram_canonical hp, hc, ?_⟩
          rw [(compileProgram_spec hc).2.2.2]
          rfl

/-- Two accepted requests over the same source bytes compile the same program to the same
artifact; distinct bytes give distinct names unless BLAKE3 collides on them.  The name is a
function of the bytes alone, and the bytes of the program (`decodeProgram_canonical`). -/
theorem compileBytes_source_identity {limits : Limits} {b1 b2 : List UInt8} {p1 p2 : Program}
    {c1 c2 : Compiled} (h1 : compileBytes limits b1 = .ok (p1, c1))
    (h2 : compileBytes limits b2 = .ok (p2, c2)) (hsrc : encodeProgram p1 = encodeProgram p2) :
    p1 = p2 /\ c1 = c2 := by
  have e1 := (compileBytes_spec h1).1
  have e2 := (compileBytes_spec h2).1
  have hb : b1 = b2 := by rw [← e1, ← e2, hsrc]
  subst hb
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

/-- **The served statement.**  An accepted request's descriptor, satisfied canonically, means:
every row is the encoding of well-typed values of the program the request bytes encode, and the
program holds on them. -/
theorem compileBytes_sound {hash : List Int -> Int} {limits : Limits} {bytes : List UInt8}
    {p : Program} {c : Compiled} {minit : Int -> Int} {mfin : Int -> Int × Nat}
    {maddrs : List Int} {t : VmTrace} (h : compileBytes limits bytes = .ok (p, c))
    (hsat : ProgramSatisfied2 hash c minit mfin maddrs t) :
    encodeProgram p = bytes /\
      forall i, i < t.rows.length -> exists vals, ValuesOk p.inputs vals /\
        (forall a, a < atomTotal p.inputs ->
          (envAt t i).loc a = bitInt (atomEnv p.inputs vals a)) /\
        evalProgram p vals = true :=
  ⟨(compileBytes_spec h).1, program_sound (compileBytes_spec h).2.1 hsat⟩

theorem respond_eq {line : String} {limits : Limits} {bytes : List UInt8}
    (h : parseRequest line = .ok (limits, bytes)) :
    respond line = reply (compileBytes limits bytes) bytes := by
  simp [respond, h]

/-! ## 20. Honest witness and the Boolean-only control -/

def sampleName : String := "dregg-direct-logic-sample"

def sampleCompiled : Except Error Compiled := compileProgram Limits.default sampleName sampleProgram

theorem sample_compiles : exists c, sampleCompiled = .ok c := by
  cases h : sampleCompiled with
  | ok c => exact ⟨c, rfl⟩
  | error e =>
      have : sampleCompiled.isOk = true := by decide
      rw [h] at this
      cases this

/-- `flag = false`, `color = 0`: allowed, so the program holds. -/
def sampleVals : List Nat := [0, 0]

theorem sampleVals_ok : ValuesOk sampleProgram.inputs sampleVals := by
  refine ⟨rfl, ?_⟩
  intro i hi
  have : i < 2 := by simpa [sampleProgram] using hi
  rcases (by omega : i = 0 \/ i = 1) with rfl | rfl <;> simp [sampleVals, sampleProgram, LType.card]

theorem sampleVals_true : evalProgram sampleProgram sampleVals = true := by decide

/-- The compiled sample has a canonical satisfying trace: the hypotheses of `program_sound` are
jointly inhabited. -/
theorem sample_satisfied (hash : List Int -> Int) :
    exists c, sampleCompiled = .ok c /\
      ProgramSatisfied2 hash c (fun _ => 0) (fun _ => ((0 : Int), 0)) []
        (witnessTrace sampleProgram.inputs sampleVals) := by
  obtain ⟨c, hc⟩ := sample_compiles
  exact ⟨c, hc, program_complete hash hc sampleVals sampleVals_ok sampleVals_true⟩

/-- A TWO-HOT row: `flag = false` and color columns `0` and `1` both set.  It encodes no source
value. -/
def twoHotEnv : Nat -> Bool
  | 1 => true
  | 2 => true
  | _ => false

/-- The lowered sample relation (the formula polynomial alone) accepts the two-hot row. -/
theorem twoHot_relation_true (c : Compiled) (hc : sampleCompiled = .ok c) :
    Cert.eval twoHotEnv c.relation = true := by
  rw [(compileProgram_spec hc).2.2.2]
  decide

/-- **Control: replacing only the Boolean polynomial is weaker.**  The Boolean-only descriptor
(`FiniteLogicDescriptorIR2.compileDescriptor` of the same lowered relation, without one-hot gates)
accepts the two-hot row canonically ... -/
theorem booleanOnly_accepts_twoHot (hash : List Int -> Int) (c : Compiled)
    (hc : sampleCompiled = .ok c) :
    CanonicalLogicSatisfied2 hash 4 c.relation (fun _ => 0) (fun _ => ((0 : Int), 0)) []
      (traceOf twoHotEnv) := by
  have hrel := (compileProgram_spec hc).2.2.2
  have hb : atomsBelow 4 c.relation = true := by
    rw [hrel]; exact lower_atoms sampleProgram.inputs sampleProgram.formula [] []
  exact source_complete hash 4 c.relation twoHotEnv hb (twoHot_relation_true c hc)

/-- ... while the compiled descriptor refuses every trace containing it: the color one-hot gate
evaluates to `1 + 1 + 0 - 1 = 1`. -/
theorem program_refuses_twoHot (hash : List Int -> Int) (c : Compiled)
    (hc : sampleCompiled = .ok c) (minit : Int -> Int) (mfin : Int -> Int × Nat)
    (maddrs : List Int) :
    ¬ ProgramSatisfied2 hash c minit mfin maddrs (traceOf twoHotEnv) := by
  intro hsat
  have hdesc := (compileProgram_spec hc).2.2.2
  have hmem : VmConstraint2.windowGate (oneHotConstraint 1 3) ∈ c.descriptor.constraints := by
    have hg := oneHotGates_complete sampleProgram.inputs 0 1 (by simp [sampleProgram]) 3 rfl
    have h1 : 0 + atomTotal (sampleProgram.inputs.take 1) = 1 := by
      simp [sampleProgram, atomTotal, LType.atomCount]
    rw [h1] at hg
    rw [hdesc]
    simp only [programDescriptor, programConstraints, List.mem_append]
    exact Or.inl (Or.inr hg)
  have h := hsat.toSatisfied2.rowConstraints 0 (by simp [traceOf]) _ hmem
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, oneHotConstraint] at h
  rw [eval_oneHotBody] at h
  have hv : ((List.range 3).map fun k => (envAt (traceOf twoHotEnv) 0).loc (1 + k)).sum + -1 = 1 := by
    simp [traceOf_loc, rowOf, twoHotEnv, bitInt, List.range_succ]
  rw [hv, Int.modEq_zero_iff_dvd] at h
  norm_num at h

/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.lower_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower_eval
/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.program_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms program_complete
/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.program_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms program_sound
/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.compileBytes_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compileBytes_spec
/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.compileBytes_source_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms compileBytes_source_identity
/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.compileBytes_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compileBytes_sound
/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.sample_satisfied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sample_satisfied
/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.booleanOnly_accepts_twoHot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms booleanOnly_accepts_twoHot
/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.program_refuses_twoHot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms program_refuses_twoHot
/-- info: 'Dregg2.Logic.DirectLogicProgramIR2.decodeProgram_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeProgram_canonical

end Dregg2.Logic.DirectLogicProgramIR2
