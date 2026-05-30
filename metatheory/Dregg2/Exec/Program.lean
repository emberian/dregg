/-
# Dregg2.Exec.Program — the RecordProgram as the coalgebra structure-map (over records).

`dregg2 §1.5` / CLAUDETHOUGHT: **the `RecordProgram` IS the coalgebra structure-map** — the
`AdmissibleTurn ⇒ Cell` arrow. dregg1 realizes it as `RecordProgram = None | Predicate([…]) |
Cases([…]) | Circuit{hash}` over a ~21-variant `StateConstraint` catalog (`cell/src/program.rs`),
with **default-deny on no matching case** (the partial, fail-closed arrow). This module is the
faithful Lean transcription of that catalog and evaluator — but **name-keyed over the Preserves
`Value`/`Schema`** of `Exec/Value.lean`, not bit-positioned over 8 fixed slots.

The evaluator `RecordProgram.admits : RecordProgram → method → (old new : Value) → Bool` is the
admissibility filter: the *domain* of the structure-map (`{(method, new) | admits …}`). It is
decidable and computable (it is the executable golden oracle). Crucially, **every constraint
reads specific NAMED fields** (`Value.scalar`) — so under `flatten` each constraint is a Boolean
function of a known set of *wires*, which is exactly what the Build-3 circuit compiler
(`RecordCircuit`) places onto `fieldOffset` columns. That correspondence (`admits ↔ circuit`) is
the prize; this module is its spec side.

The Heyting fragment (`anyOf` ⊔ / `not` ¬) realizes `Laws.predicate_heyting` in the slot-caveat
vocabulary (`dregg2 §1.5`). Witnessed / sender / cross-cell (`boundDelta`) constraints — which
need the verify/find seam (`Laws.Verifiable`/`CryptoKernel`) or a peer cell — are *declared*
here and routed to their seam in later builds, exactly as dregg1's scalar evaluator defers
`BoundDelta`/`Witnessed` to dedicated passes.

Pure, computable, `#eval`-able; imports only `Exec.Value` (Lean-core), so it checks fast.
-/
import Dregg2.Exec.Value

namespace Dregg2.Exec

/-! ## Field access into a record `Value`. -/

/-- Look up a named field's value in a record (`none` if not a record / field absent). -/
def Value.field : Value → FieldName → Option Value
  | .record fs, f => (fs.find? (fun p => p.1 == f)).map (·.2)
  | _,          _ => none

/-- Read a named field as a scalar `Int` (`none` if absent or not an `int`). Constraints that
need a missing/ill-typed field **fail closed** (the `none` propagates to `false`). -/
def Value.scalar (v : Value) (f : FieldName) : Option Int :=
  match v.field f with
  | some (.int i) => some i
  | _             => none

/-- Sum the scalar values of named fields; `none` if any is absent/ill-typed (fail-closed). -/
def sumScalars (v : Value) (fields : List FieldName) : Option Int :=
  fields.foldr
    (fun f acc => match acc, v.scalar f with
                  | some s, some x => some (s + x)
                  | _,      _      => none)
    (some 0)

/-! ## The constraint catalog (name-keyed; the structural subset of dregg1's 21). -/

/-- **Simple (non-witnessed, non-recursive-except-`not`) constraints** — the fragment
admissible inside `anyOf` and under `not` (mirrors dregg1's `SimpleStateConstraint`, the
Heyting-liftable subset). -/
inductive SimpleConstraint where
  /-- `new[field] = value`. -/
  | fieldEquals (field : FieldName) (value : Int)
  /-- `new[field] ≥ value`. -/
  | fieldGe     (field : FieldName) (value : Int)
  /-- `new[field] ≤ value`. -/
  | fieldLe     (field : FieldName) (value : Int)
  /-- `new[field] = old[field]` (read-only after init; absent-old ⇒ first write allowed). -/
  | immutable   (field : FieldName)
  /-- `old[field] = 0/absent ⇒ any; else new[field] = old[field]` (register-once). -/
  | writeOnce   (field : FieldName)
  /-- `new[field] ≥ old[field]` (append-only / monotone counter). -/
  | monotonic   (field : FieldName)
  /-- `new[field] > old[field]` (strictly increasing — bids, sequence numbers). -/
  | strictMono  (field : FieldName)
  /-- `new[field] = old[field] + delta`. -/
  | fieldDelta  (field : FieldName) (delta : Int)
  /-- **Negation** (the Heyting `¬`) — accept iff `inner` rejects. Unboxed inner ⇒ no
  unbounded nesting (`dregg2 §1.5` Heyting fragment). -/
  | not         : SimpleConstraint → SimpleConstraint
  deriving Repr

/-- **The full state-constraint catalog** — simple constraints plus the cross-slot,
conservation, state-machine, disjunction, and (declared-but-deferred) cross-cell variants. -/
inductive StateConstraint where
  /-- Lift a simple constraint. -/
  | simple        : SimpleConstraint → StateConstraint
  /-- `new[left] ≤ new[right]` (queue tail ≤ head). -/
  | fieldLeField  (left right : FieldName)
  /-- `Σ new[fields] = value` (intra-cell post-state sum). -/
  | sumEquals     (fields : List FieldName) (value : Int)
  /-- `Σ new[inputs] = Σ old[inputs] + Σ new[outputs]` (intra-cell conservation across the
  transition — dregg1 `SumEqualsAcross`). -/
  | sumEqualsAcross (inputs outputs : List FieldName)
  /-- `new[field] ∈ [old[field] + lo, old[field] + hi]` (bounded growth). -/
  | fieldDeltaInRange (field : FieldName) (lo hi : Int)
  /-- `(old[field], new[field]) ∈ allowed` (a bounded state machine). -/
  | allowedTransitions (field : FieldName) (allowed : List (Int × Int))
  /-- **Single-level disjunction** (the Heyting `⊔`) over simple constraints. -/
  | anyOf         (variants : List SimpleConstraint)
  /-- **Cross-cell binding (γ.2)** — `this[localField]` delta vs `peer[peerField]` delta.
  DECLARED here; the single-cell evaluator defers it (returns `true`), exactly like dregg1's
  scalar evaluator — it is discharged by the JointTurn aggregate (Build 4). `eqOpp = true` is
  `EqualAndOpposite` (bilateral conservation), `false` is `Equal`. -/
  | boundDelta    (localField : FieldName) (peer : Nat) (peerField : FieldName) (eqOpp : Bool)
  deriving Repr

/-! ## Evaluation — the executable admissibility check. -/

/-- A decidable `Int` comparison as a `Bool`. -/
private def intLe (a b : Int) : Bool := decide (a ≤ b)
private def intLt (a b : Int) : Bool := decide (a < b)

/-- **Evaluate a simple constraint** against `(old, new)`. Fail-closed on absent/ill-typed
fields (`none ⇒ false`). Recurses only through `not`. -/
def evalSimple : SimpleConstraint → Value → Value → Bool
  | .fieldEquals f val, _,   new => new.scalar f == some val
  | .fieldGe f val,     _,   new => match new.scalar f with | some x => intLe val x | none => false
  | .fieldLe f val,     _,   new => match new.scalar f with | some x => intLe x val | none => false
  | .immutable f,       old, new => match old.scalar f with
                                    | none   => true                        -- init: first write allowed
                                    | some a => new.scalar f == some a
  | .writeOnce f,       old, new => match old.scalar f with
                                    | none      => true
                                    | some 0    => true                     -- unwritten ⇒ any
                                    | some a    => new.scalar f == some a
  | .monotonic f,       old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => intLe a b | _, _ => false
  | .strictMono f,      old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => intLt a b | _, _ => false
  | .fieldDelta f d,    old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => b == a + d | _, _ => false
  | .not c,             old, new => !(evalSimple c old new)

/-- **Evaluate a full state constraint** against `(old, new)`. -/
def evalConstraint : StateConstraint → Value → Value → Bool
  | .simple c,              old, new => evalSimple c old new
  | .fieldLeField l r,      _,   new => match new.scalar l, new.scalar r with
                                        | some a, some b => intLe a b | _, _ => false
  | .sumEquals fs val,      _,   new => sumScalars new fs == some val
  | .sumEqualsAcross ins outs, old, new =>
      match sumScalars new ins, sumScalars old ins, sumScalars new outs with
      | some ni, some oi, some no => ni == oi + no
      | _, _, _ => false
  | .fieldDeltaInRange f lo hi, old, new =>
      match old.scalar f, new.scalar f with
      | some a, some b => intLe (a + lo) b && intLe b (a + hi)
      | _, _ => false
  | .allowedTransitions f allowed, old, new =>
      match old.scalar f, new.scalar f with
      | some a, some b => allowed.any (fun p => p.1 == a && p.2 == b)
      | _, _ => false
  | .anyOf variants,        old, new => variants.any (fun c => evalSimple c old new)
  | .boundDelta _ _ _ _,    _,   _   => true     -- deferred to the JointTurn aggregate (Build 4)

/-! ## RecordProgram + TransitionGuard dispatch + default-deny. -/

/-- Guard naming which transitions a `Cases` arm applies to (`cell/src/program.rs`). -/
inductive TransitionGuard where
  | always
  | methodIs    (method : Nat)
  | slotChanged (field : FieldName)
  | anyOf       (children : List TransitionGuard)
  | allOf       (children : List TransitionGuard)
  deriving Repr

mutual
/-- Does a guard dispatch on the action's *method/effect* (vs being a pure state guard)?
Used for default-deny: a `Cases` value with a method-dispatching arm denies unknown methods. -/
def TransitionGuard.isMethodDispatching : TransitionGuard → Bool
  | .always         => false
  | .methodIs _     => true
  | .slotChanged _  => false
  | .anyOf cs       => anyDispatching cs
  | .allOf cs       => anyDispatching cs
def anyDispatching : List TransitionGuard → Bool
  | []        => false
  | g :: rest => g.isMethodDispatching || anyDispatching rest
end

mutual
/-- Evaluate a guard against `(method, old, new)`. -/
def TransitionGuard.matches : TransitionGuard → Nat → Value → Value → Bool
  | .always,        _,      _,   _   => true
  | .methodIs m,    method, _,   _   => m == method
  | .slotChanged f, _,      old, new => !(old.scalar f == new.scalar f)
  | .anyOf cs,      method, old, new => anyMatch cs method old new
  | .allOf cs,      method, old, new => allMatch cs method old new
def anyMatch : List TransitionGuard → Nat → Value → Value → Bool
  | [],        _,      _,   _   => false
  | g :: rest, method, old, new => g.matches method old new || anyMatch rest method old new
def allMatch : List TransitionGuard → Nat → Value → Value → Bool
  | [],        _,      _,   _   => true
  | g :: rest, method, old, new => g.matches method old new && allMatch rest method old new
end

/-- One operation-scoped case: a guard + the constraints that bind when it matches. -/
structure TransitionCase where
  guard       : TransitionGuard
  constraints : List StateConstraint
  deriving Repr

/-- **The RecordProgram** — the developer-authored coalgebra structure-map. -/
inductive RecordProgram where
  /-- Terminal program: every (authorized) transition admissible. -/
  | none
  /-- A conjunction of constraints (the legacy `Always`-case shape). -/
  | predicate (constraints : List StateConstraint)
  /-- Operation-scoped cases; **no matching case ⇒ default-deny**. -/
  | cases     (cases : List TransitionCase)
  /-- An opaque AIR; admissibility = "carries a proof the circuit accepts" (Build 3). -/
  | circuit   (hash : Nat)
  deriving Repr

/-- **`admits` — the admissibility filter (the structure-map's domain).** Decidable, computable,
fail-closed. `none` admits all; `predicate` ANDs its constraints; `cases` ANDs every *matching*
arm's constraints and **denies when no arm matches** (the partial, default-deny arrow); `circuit`
denies in the pure evaluator (it needs the proof — discharged in `RecordCircuit`, Build 3). -/
def RecordProgram.admits : RecordProgram → Nat → Value → Value → Bool
  | .none,           _,      _,   _   => true
  | .predicate cs,   _,      old, new => cs.all (fun c => evalConstraint c old new)
  | .cases tcs,      method, old, new =>
      match tcs.filter (fun tc => tc.guard.matches method old new) with
      | []      => false                                              -- default-deny on no match
      | m :: ms => (m :: ms).all (fun tc => tc.constraints.all (fun c => evalConstraint c old new))
  | .circuit _,      _,      _,   _   => false

/-! ## Basic laws (the structure-map is a genuine, Heyting-respecting, fail-closed filter). -/

/-- The terminal program admits every transition — PROVED. -/
theorem admits_none (m : Nat) (o n : Value) : RecordProgram.admits .none m o n = true := rfl

/-- A `predicate` program is exactly the conjunction of its constraints — PROVED (definitional). -/
theorem admits_predicate (cs : List StateConstraint) (m : Nat) (o n : Value) :
    RecordProgram.admits (.predicate cs) m o n = cs.all (fun c => evalConstraint c o n) := rfl

/-- **Default-deny — PROVED.** An empty `Cases` (and any `Cases` with no matching arm) denies. -/
theorem admits_cases_nil (m : Nat) (o n : Value) :
    RecordProgram.admits (.cases []) m o n = false := rfl

/-- A `Circuit` program is never admitted by the *pure* evaluator (it needs its proof) — PROVED. -/
theorem admits_circuit (h : Nat) (m : Nat) (o n : Value) :
    RecordProgram.admits (.circuit h) m o n = false := rfl

/-- **Negation is the Boolean complement — PROVED** (the Heyting `¬` on the predicate algebra). -/
theorem evalSimple_not (c : SimpleConstraint) (o n : Value) :
    evalSimple (.not c) o n = !(evalSimple c o n) := rfl

/-- **Double negation collapses — PROVED** (`¬¬c = c` on the decidable predicate algebra). -/
theorem evalSimple_not_not (c : SimpleConstraint) (o n : Value) :
    evalSimple (.not (.not c)) o n = evalSimple c o n := by
  simp [evalSimple]

/-- **Disjunction is `∃`/`any` — PROVED** (the Heyting `⊔`). -/
theorem evalConstraint_anyOf (vs : List SimpleConstraint) (o n : Value) :
    evalConstraint (.anyOf vs) o n = vs.any (fun c => evalSimple c o n) := rfl

/-! ## It runs (`#eval`) — real programs admitting / denying real record transitions. -/

/-- A counter cell: one scalar field `count`, program = "count only ever increases". -/
def counterProgram : RecordProgram := .predicate [.simple (.monotonic "count")]

def counterOld : Value := .record [("count", .int 5)]
def counterUp  : Value := .record [("count", .int 7)]   -- 7 ≥ 5  → admitted
def counterDn  : Value := .record [("count", .int 3)]   -- 3 ≥ 5? → denied

#eval counterProgram.admits 0 counterOld counterUp     -- true
#eval counterProgram.admits 0 counterOld counterDn     -- false

/-- A bounded state machine on `status`: only Open(0)→Claimed(1)→Paid(2). -/
def smProgram : RecordProgram :=
  .predicate [.allowedTransitions "status" [(0, 1), (1, 2)]]

#eval smProgram.admits 0 (.record [("status", .int 0)]) (.record [("status", .int 1)])  -- true  (Open→Claimed)
#eval smProgram.admits 0 (.record [("status", .int 0)]) (.record [("status", .int 2)])  -- false (Open↛Paid)

/-- A `Cases` program: on method `1` (a "deposit"), balance must strictly increase; any other
method has no matching arm and is **default-denied**. -/
def depositOnly : RecordProgram :=
  .cases [⟨.methodIs 1, [.simple (.strictMono "balance")]⟩]

def balLo : Value := .record [("balance", .int 100)]
def balHi : Value := .record [("balance", .int 150)]

#eval depositOnly.admits 1 balLo balHi    -- true  (method 1, balance ↑)
#eval depositOnly.admits 1 balHi balLo    -- false (method 1, balance ↓)
#eval depositOnly.admits 2 balLo balHi    -- false (method 2: no matching case → default-deny)

/-- Intra-cell conservation: `Σ new[ins] = Σ old[ins] + Σ new[outs]` (a split). -/
def splitProgram : RecordProgram := .predicate [.sumEqualsAcross ["a"] ["b"]]
-- old a=10; new a=4, b=6  ⇒  4 = 10 + 6? no.  new a=16, b=6 ⇒ 16 = 10 + 6 ✓
#eval splitProgram.admits 0 (.record [("a", .int 10)]) (.record [("a", .int 16), ("b", .int 6)])  -- true

end Dregg2.Exec
