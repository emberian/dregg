/-
# Dregg2.Tree.Schema: the regular core of JSON Schema, its top-down semantics, and its compilation
to a bottom-up tree automaton (`compile_correct`)

A `Schema` is a list of definitions referred to by index (JSON Schema's `$defs`, flattened, with
every subschema named), a list of byte tables for `pattern`, and a root index. A definition carries
the keywords of the regular core (`GROUNDING.md` §3.2):

    type, enum (strings), pattern (a byte table deciding the WHOLE string), minimum, maximum,
    properties, required, additionalProperties (true / false / a definition), items,
    minItems, maxItems, allOf, anyOf

`allOf`/`anyOf` refer to definitions applied to the SAME node; they must point to lower indices
(`Schema.Ok`, checked), which keeps same-node references acyclic. References through `properties`,
`additionalProperties` and `items` go to children and may be recursive in any direction.

`valid S v d` is the semantics, written top-down the way JSON Schema specifies validation. The
automaton `compile S` is bottom-up: its state at a node is the bit vector of every definition the
node satisfies; an object's horizontal state per definition is `(count, ok, required keys still
missing)`, an array's is `(min (count, cap), ok, -)`, where `cap = minItems + maxItems + 1`, so
the horizontal state space is finite. ⚑ `compile_correct`: on every value, the automaton's state
is exactly `[valid S v 0, …, valid S v (m-1)]`.
-/
import Dregg2.Tree.Automaton

namespace Dregg2.Tree

/-- A byte table in the `dfa` crate's shape (`transitions[s * 256 + b]`, out of range → state 0).
Field for field and step for step the same object as `Dregg2.Automata.TableRun.FlatTable`;
`Spec.tableAccepts_eq` proves `tableAccepts` is `TableRun.acceptsBytes` on the converted table, so
`TableRunSpec`'s chain to `Dfa.lean`'s `DfaAccepts` applies. Kept separate so the `tree-check`
executable does not link a module other lanes rebuild. -/
structure FlatTable where
  numStates : Nat
  transitions : Array Nat
  start : Nat
  accepting : List Nat
  deriving Repr

namespace FlatTable
def step (t : FlatTable) (s : Nat) (b : UInt8) : Nat := t.transitions.getD (s * 256 + b.toNat) 0
def isAccepting (t : FlatTable) (s : Nat) : Bool := t.accepting.contains s
def wellFormed (t : FlatTable) : Bool :=
  t.transitions.size == t.numStates * 256 && t.transitions.all (· < t.numStates)
    && t.start < t.numStates
end FlatTable

def runFrom (t : FlatTable) (q : Nat) (w : List UInt8) : Nat := w.foldl t.step q

/-- JSON Schema `type` values. `num` admits integers as well. -/
inductive Ty where
  | null | bool | int | num | str | arr | obj
  deriving Repr, DecidableEq

/-- `additionalProperties`. -/
inductive Addl where
  | any
  | forbid
  | sch (j : Nat)
  deriving Repr, DecidableEq

/-- One definition of the regular core. -/
structure Def where
  types : List Ty := []
  enumStr : Option (List (List UInt8)) := none
  pattern : Option Nat := none
  minimum : Option Int := none
  maximum : Option Int := none
  props : List (List UInt8 × Nat) := []
  required : List (List UInt8) := []
  additional : Addl := .any
  items : Option Nat := none
  minItems : Nat := 0
  maxItems : Option Nat := none
  allOf : List Nat := []
  anyOf : List Nat := []
  deriving Repr

structure Schema where
  defs : List Def
  tables : List FlatTable
  root : Nat

namespace Schema

variable (S : Schema)

/-- Same-node references point to lower indices; table indices exist; the root exists. -/
def ok : Bool :=
  S.root < S.defs.length &&
  (List.range S.defs.length).all fun d =>
    let D := S.defs.getD d {}
    D.allOf.all (· < d) && D.anyOf.all (· < d) &&
      (match D.pattern with | some p => p < S.tables.length | none => true)

end Schema

/-! ## Local (single-node) checks -/

def tyOf : JVal → Ty
  | .null => .null
  | .bool _ => .bool
  | .int _ => .int
  | .dec _ _ => .num
  | .str _ => .str
  | .arr _ => .arr
  | .obj _ => .obj

def typeOk (D : Def) (v : JVal) : Bool :=
  D.types.isEmpty || D.types.contains (tyOf v) || (tyOf v == .int && D.types.contains .num)

/-- `m · 10^e ≥ b` for `e < 0`. -/
def decGe (m e b : Int) : Bool := m ≥ b * 10 ^ (-e).toNat
/-- `m · 10^e ≤ b` for `e < 0`. -/
def decLe (m e b : Int) : Bool := m ≤ b * 10 ^ (-e).toNat

def tableAccepts (t : FlatTable) (s : List UInt8) : Bool := t.isAccepting (runFrom t t.start s)

/-- The scalar keywords on a node (true on containers). -/
def scalarOk (S : Schema) (D : Def) : JVal → Bool
  | .str s =>
    (match D.enumStr with | some l => l.contains s | none => true) &&
    (match D.pattern with
     | some p => match S.tables[p]? with
       | some t => tableAccepts t s
       | none => false
     | none => true)
  | .int n =>
    (match D.minimum with | some b => b ≤ n | none => true) &&
    (match D.maximum with | some b => n ≤ b | none => true)
  | .dec m e =>
    (match D.minimum with | some b => decGe m e b | none => true) &&
    (match D.maximum with | some b => decLe m e b | none => true)
  | _ => true

def getBit (bits : List Bool) (j : Nat) : Bool := bits.getD j false

def itemOk (D : Def) (f : Nat → Bool) : Bool :=
  match D.items with
  | some j => f j
  | none => true

def lookupProp (k : List UInt8) : List (List UInt8 × Nat) → Option Nat
  | [] => none
  | (k', j) :: r => if k' = k then some j else lookupProp k r

def entryOk (D : Def) (k : List UInt8) (f : Nat → Bool) : Bool :=
  match lookupProp k D.props with
  | some j => f j
  | none => match D.additional with
    | .any => true
    | .forbid => false
    | .sch j => f j

def maxOk (D : Def) (n : Nat) : Bool :=
  match D.maxItems with
  | some m => n ≤ m
  | none => true

/-! ## The semantics (top-down) -/

/-- ⚑ **`valid S v d`**: `v` validates against definition `d`. -/
def valid (S : Schema) (v : JVal) (d : Nat) : Bool :=
  match S.defs[d]? with
  | none => false
  | some D =>
    typeOk D v && scalarOk S D v &&
    (match v with
     | .arr xs =>
       (xs.attach.all fun ⟨c, _⟩ => itemOk D (fun j => valid S c j)) &&
         D.minItems ≤ xs.length && maxOk D xs.length
     | .obj kvs =>
       (kvs.attach.all fun ⟨e, _⟩ => entryOk D e.1 (fun j => valid S e.2 j)) &&
         D.required.all (fun r => kvs.any (·.1 == r))
     | _ => true) &&
    (D.allOf.attach.all fun ⟨j, _⟩ => if j < d then valid S v j else false) &&
    (D.anyOf.isEmpty || D.anyOf.attach.any fun ⟨j, _⟩ => if j < d then valid S v j else false)
termination_by (sizeOf v, d)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; assumption)
    | (apply Prod.Lex.left
       have := List.sizeOf_lt_of_mem ‹_ ∈ _›
       simp_all only [JVal.arr.sizeOf_spec, JVal.obj.sizeOf_spec]
       first
         | omega
         | (have : sizeOf e.2 < sizeOf e := by
              obtain ⟨a, b⟩ := e; simp only [Prod.mk.sizeOf_spec]; omega
            omega))

theorem all_attach' {α : Type} (l : List α) (f : α → Bool) :
    (l.attach.all fun x => f x.1) = l.all f := by
  apply Bool.eq_iff_iff.mpr; simp [List.all_eq_true]
theorem any_attach' {α : Type} (l : List α) (f : α → Bool) :
    (l.attach.any fun x => f x.1) = l.any f := by
  apply Bool.eq_iff_iff.mpr; simp [List.any_eq_true]
theorem filter_true' {α : Type} (l : List α) : l.filter (fun _ => true) = l := by
  induction l <;> simp_all

/-! ## The compiled automaton (bottom-up) -/

/-- Per-definition horizontal state. -/
structure HS where
  count : Nat
  ok : Bool
  rem : List (List UInt8)

/-- The array-length counter saturates at `cap`, which exceeds both bounds. -/
def cap (D : Def) : Nat := D.minItems + D.maxItems.getD 0 + 1

def stepD (D : Def) (key : Option (List UInt8)) (q : List Bool) (h : HS) : HS :=
  match key with
  | none => ⟨min (h.count + 1) (cap D), h.ok && itemOk D (getBit q), h.rem⟩
  | some k => ⟨h.count, h.ok && entryOk D k (getBit q), h.rem.filter (· != k)⟩

/-- Same-node combinators, applied in index order to the base bits. -/
def closeStep (S : Schema) (base acc : List Bool) (d : Nat) : Bool :=
  let D := S.defs.getD d {}
  base.getD d false && D.allOf.all (fun j => decide (j < d) && getBit acc j) &&
    (D.anyOf.isEmpty || D.anyOf.any (fun j => decide (j < d) && getBit acc j))

def close (S : Schema) (base : List Bool) : List Bool :=
  (List.range S.defs.length).foldl (fun acc d => acc ++ [closeStep S base acc d]) []

def defAt (S : Schema) (d : Nat) : Def := S.defs.getD d {}

/-- ⚑ **The compiled automaton.** States: the bit vector of satisfied definitions. -/
def compile (S : Schema) : TreeAut (List Bool) (Nat → HS) where
  leaf v := some (close S ((List.range S.defs.length).map fun d =>
    typeOk (defAt S d) v && scalarOk S (defAt S d) v))
  hstart k := fun d => ⟨0, true, match k with | .obj => (defAt S d).required | .arr => []⟩
  hstep h key q := some fun d => stepD (defAt S d) key q (h d)
  hfinal k h := some (close S ((List.range S.defs.length).map fun d =>
    let D := defAt S d
    match k with
    | .arr => typeOk D (.arr []) && (h d).ok && decide (D.minItems ≤ (h d).count) && maxOk D (h d).count
    | .obj => typeOk D (.obj []) && (h d).ok && (h d).rem.isEmpty))

/-! ## `compile_correct` -/

section
variable (S : Schema)

/-- The bit vector the semantics assigns. -/
def bitsOf (v : JVal) : List Bool := (List.range S.defs.length).map (valid S v)

theorem valid_out {v : JVal} {d : Nat} (h : S.defs.length ≤ d) : valid S v d = false := by
  unfold valid
  rw [List.getElem?_eq_none h]

theorem getBit_bitsOf (v : JVal) (j : Nat) : getBit (bitsOf S v) j = valid S v j := by
  unfold getBit bitsOf
  by_cases h : j < S.defs.length
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, show S.defs.length ≤ j by omega, valid_out S (v := v)
      (show S.defs.length ≤ j by omega)]

theorem getBit_bitsOf_fun (v : JVal) : getBit (bitsOf S v) = valid S v :=
  funext (getBit_bitsOf S v)

theorem defAt_eq {d : Nat} (h : d < S.defs.length) : S.defs[d]? = some (defAt S d) := by
  simp [defAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem typeOk_tyOf (D : Def) {v w : JVal} (h : tyOf v = tyOf w) : typeOk D v = typeOk D w := by
  simp [typeOk, h]

theorem foldl_count (D : Def) (f : JVal → List Bool) :
    ∀ (xs : List JVal) (h : HS), h.count ≤ cap D →
      (xs.foldl (fun hs c => stepD D none (f c) hs) h).count = min (h.count + xs.length) (cap D)
  | [], h, hc => by simp; omega
  | x :: xs, h, hc => by
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl_count D f xs _ (by simp [stepD]; omega)]
    simp only [stepD]; omega

theorem foldl_ok_arr (D : Def) (f : JVal → List Bool) :
    ∀ (xs : List JVal) (h : HS),
      (xs.foldl (fun hs c => stepD D none (f c) hs) h).ok =
        (h.ok && xs.all fun c => itemOk D (getBit (f c)))
  | [], h => by simp
  | x :: xs, h => by
    simp only [List.foldl_cons, List.all_cons]
    rw [foldl_ok_arr D f xs]
    simp [stepD, Bool.and_assoc]

theorem foldl_ok_obj (D : Def) (f : JVal → List Bool) :
    ∀ (kvs : List (List UInt8 × JVal)) (h : HS),
      (kvs.foldl (fun hs e => stepD D (some e.1) (f e.2) hs) h).ok =
        (h.ok && kvs.all fun e => entryOk D e.1 (getBit (f e.2)))
  | [], h => by simp
  | e :: kvs, h => by
    simp only [List.foldl_cons, List.all_cons]
    rw [foldl_ok_obj D f kvs]
    simp [stepD, Bool.and_assoc]

theorem foldl_rem_obj (D : Def) (f : JVal → List Bool) :
    ∀ (kvs : List (List UInt8 × JVal)) (h : HS),
      (kvs.foldl (fun hs e => stepD D (some e.1) (f e.2) hs) h).rem =
        h.rem.filter (fun r => !(kvs.any (·.1 == r)))
  | [], h => by simp only [List.foldl_nil, List.any_nil, Bool.not_false, filter_true']
  | e :: kvs, h => by
    simp only [List.foldl_cons]
    rw [foldl_rem_obj D f kvs]
    simp only [stepD, List.filter_filter, List.any_cons]
    congr 1
    funext r
    by_cases hr : e.1 = r
    · simp [hr]
    · have hr' : r ≠ e.1 := fun h => hr h.symm
      have h1 : (r != e.1) = true := by simp [hr']
      have h2 : (e.1 == r) = false := by simp [hr]
      rw [h1, h2]; simp [Bool.and_comm]

theorem compile_hstep (h : Nat → HS) (k : Option (List UInt8)) (q : List Bool) :
    (compile S).hstep h k q = some (fun d => stepD (defAt S d) k q (h d)) := rfl

theorem evalArr_spec (xs : List JVal) (ih : ∀ c ∈ xs, (compile S).eval c = some (bitsOf S c)) :
    ∀ (h : Nat → HS), (compile S).evalArr xs h =
      some (fun d => xs.foldl (fun hs c => stepD (defAt S d) none (bitsOf S c) hs) (h d)) := by
  induction xs with
  | nil => intro h; rfl
  | cons x xs ihx =>
    intro h
    simp only [TreeAut.evalArr, ih x (by simp), compile_hstep]
    rw [ihx (fun c hc => ih c (by simp [hc]))]
    rfl

theorem evalObj_spec (kvs : List (List UInt8 × JVal))
    (ih : ∀ e ∈ kvs, (compile S).eval e.2 = some (bitsOf S e.2)) :
    ∀ (h : Nat → HS), (compile S).evalObj kvs h =
      some (fun d => kvs.foldl (fun hs e => stepD (defAt S d) (some e.1) (bitsOf S e.2) hs) (h d)) := by
  induction kvs with
  | nil => intro h; rfl
  | cons e kvs ihx =>
    intro h
    obtain ⟨k, x⟩ := e
    simp only [TreeAut.evalObj, ih (k, x) (by simp), compile_hstep]
    rw [ihx (fun c hc => ih c (by simp [hc]))]
    rfl

/-- The local part of `valid` (everything but the same-node combinators). -/
def localOk (v : JVal) (d : Nat) : Bool :=
  let D := defAt S d
  typeOk D v && scalarOk S D v &&
    (match v with
     | .arr xs => (xs.all fun c => itemOk D (valid S c)) &&
         decide (D.minItems ≤ xs.length) && maxOk D xs.length
     | .obj kvs => (kvs.all fun e => entryOk D e.1 (valid S e.2)) &&
         D.required.all (fun r => kvs.any (·.1 == r))
     | _ => true)

theorem valid_eq (v : JVal) {d : Nat} (hd : d < S.defs.length) :
    valid S v d = (localOk S v d &&
      (defAt S d).allOf.all (fun j => decide (j < d) && valid S v j) &&
      ((defAt S d).anyOf.isEmpty || (defAt S d).anyOf.any (fun j => decide (j < d) && valid S v j))) := by
  rw [valid, defAt_eq S hd]
  simp only [localOk]
  have h1 : ∀ (l : List Nat), (l.attach.all fun x => if x.1 < d then valid S v x.1 else false) =
      l.all (fun j => decide (j < d) && valid S v j) := by
    intro l; rw [← all_attach' l (fun j => decide (j < d) && valid S v j)]
    apply congrArg (List.all l.attach); funext x; by_cases hx : x.1 < d <;> simp [hx]
  have h2 : ∀ (l : List Nat), (l.attach.any fun x => if x.1 < d then valid S v x.1 else false) =
      l.any (fun j => decide (j < d) && valid S v j) := by
    intro l; rw [← any_attach' l (fun j => decide (j < d) && valid S v j)]
    apply congrArg (List.any l.attach); funext x; by_cases hx : x.1 < d <;> simp [hx]
  cases v with
  | arr xs =>
    have h3 : (xs.attach.all fun x => itemOk (defAt S d) (fun j => valid S x.1 j)) =
        xs.all (fun c => itemOk (defAt S d) (valid S c)) := by
      rw [← all_attach' xs (fun c => itemOk (defAt S d) (valid S c))]
    simp only [h1, h2, h3]
  | obj kvs =>
    have h3 : (kvs.attach.all fun x => entryOk (defAt S d) x.1.1 (fun j => valid S x.1.2 j)) =
        kvs.all (fun e => entryOk (defAt S d) e.1 (valid S e.2)) := by
      rw [← all_attach' kvs (fun e => entryOk (defAt S d) e.1 (valid S e.2))]
    simp only [h1, h2, h3]
  | _ => simp only [h1, h2]

/-- `close` turns the local bits into the full bits, given `Schema.ok`'s ordering. -/
theorem close_spec (v : JVal) (base : List Bool)
    (hb : ∀ d, d < S.defs.length → base.getD d false = localOk S v d) :
    close S base = bitsOf S v := by
  unfold close bitsOf
  suffices ∀ n, n ≤ S.defs.length →
      (List.range n).foldl (fun acc d => acc ++ [closeStep S base acc d]) [] =
        (List.range n).map (valid S v) from this _ (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro; rfl
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldl_append, ih (by omega), List.map_append]
    simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.append_cancel_left_eq,
      List.cons.injEq, and_true]
    rw [valid_eq S v (by omega), closeStep, hb n (by omega)]
    have hg : ∀ j, j < n → getBit ((List.range n).map (valid S v)) j = valid S v j := by
      intro j hj; simp [getBit, List.getD_eq_getElem?_getD, hj]
    have e1 : ((defAt S n).allOf.all fun j => decide (j < n) && getBit ((List.range n).map (valid S v)) j) =
        (defAt S n).allOf.all (fun j => decide (j < n) && valid S v j) := by
      congr 1; funext j; by_cases hj : j < n <;> simp [hj, hg]
    have e2 : ((defAt S n).anyOf.any fun j => decide (j < n) && getBit ((List.range n).map (valid S v)) j) =
        (defAt S n).anyOf.any (fun j => decide (j < n) && valid S v j) := by
      congr 1; funext j; by_cases hj : j < n <;> simp [hj, hg]
    simp only [defAt] at e1 e2 ⊢
    rw [e1, e2]

mutual
/-- ⚑ **`compile_correct`** — the compiled bottom-up automaton computes, at every node, exactly
the set of definitions the top-down semantics says the node satisfies. -/
theorem compile_correct : ∀ v : JVal, (compile S).eval v = some (bitsOf S v)
  | .arr xs => by
    simp only [TreeAut.eval]
    rw [evalArr_spec S xs (fun c _ => compile_correct c)]
    simp only [Option.bind_some, compile, Option.some.injEq]
    apply close_spec
    intro d hd
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd, Option.map_some,
      Option.getD_some, localOk, scalarOk, Bool.and_true]
    rw [foldl_ok_arr, foldl_count _ _ _ _ (by simp [cap])]
    simp only [getBit_bitsOf_fun]
    have hty : typeOk (defAt S d) (.arr []) = typeOk (defAt S d) (.arr xs) := typeOk_tyOf _ rfl
    rw [hty]
    simp only [Nat.zero_add, Bool.true_and]
    have hm : decide ((defAt S d).minItems ≤ min xs.length (cap (defAt S d))) =
        decide ((defAt S d).minItems ≤ xs.length) := by
      simp only [cap, decide_eq_decide]; omega
    have hx : maxOk (defAt S d) (min xs.length (cap (defAt S d))) = maxOk (defAt S d) xs.length := by
      unfold maxOk cap; cases hmx : (defAt S d).maxItems <;> simp <;> omega
    rw [hm, hx]
    simp [Bool.and_assoc]
  | .obj kvs => by
    simp only [TreeAut.eval]
    rw [evalObj_spec S kvs (fun e _ => compile_correct e.2)]
    simp only [Option.bind_some, compile, Option.some.injEq]
    apply close_spec
    intro d hd
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd, Option.map_some,
      Option.getD_some, localOk, scalarOk, Bool.and_true]
    rw [foldl_ok_obj, foldl_rem_obj]
    simp only [getBit_bitsOf_fun]
    have hty : typeOk (defAt S d) (.obj []) = typeOk (defAt S d) (.obj kvs) := typeOk_tyOf _ rfl
    rw [hty]
    have hr : ((defAt S d).required.filter fun r => !(kvs.any (·.1 == r))).isEmpty =
        (defAt S d).required.all (fun r => kvs.any (·.1 == r)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.isEmpty_iff, List.filter_eq_nil_iff, List.all_eq_true]
      simp
    simp only [Bool.true_and, hr, Bool.and_assoc]
  | .null => by simp only [TreeAut.eval, compile]; congr 1; apply close_spec; intro d hd; simp [localOk, hd]
  | .bool _ => by simp only [TreeAut.eval, compile]; congr 1; apply close_spec; intro d hd; simp [localOk, hd]
  | .int _ => by simp only [TreeAut.eval, compile]; congr 1; apply close_spec; intro d hd; simp [localOk, hd]
  | .dec _ _ => by simp only [TreeAut.eval, compile]; congr 1; apply close_spec; intro d hd; simp [localOk, hd]
  | .str _ => by simp only [TreeAut.eval, compile]; congr 1; apply close_spec; intro d hd; simp [localOk, hd]
termination_by v => sizeOf v
decreasing_by
  all_goals
    have := List.sizeOf_lt_of_mem ‹_ ∈ _›
    simp_all only [JVal.arr.sizeOf_spec, JVal.obj.sizeOf_spec]
    first
      | omega
      | (have : sizeOf e.2 < sizeOf e := by
           obtain ⟨a, b⟩ := e; simp only [Prod.mk.sizeOf_spec]; omega
         omega)
end

end

/-- info: 'Dregg2.Tree.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compile_correct

end Dregg2.Tree
