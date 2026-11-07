/-
# Dregg2.Exec.PredAlgebra — the clean Boolean predicate ALGEBRA over the policy-combinator atoms.

The forked predicate surfaces (`SimpleConstraint`/`StateConstraint` in `Exec/Program.lean`, the
per-slot `SlotCaveat` in `Exec/RecordKernel.lean`) are ad-hoc 2-level grammars: `anyOf` is
single-level over simples only, `not` lives only at `SimpleConstraint`, and there is no `allOf`. The
`_POLICY-LANGUAGES-REFRESH.md` §B.1 target is **a small core of orthogonal, introspectable
combinators** under a uniform Boolean layer, into which the OLD corpora embed as a NO-OP extension so
existing proofs LIFT.

This module is that uniform layer. It is built ON TOP of `Exec/Program.lean`'s extended atom set
(`memberOf`/`prefixOf`/`inRangeTwoSided`/`deltaBounded`/`affineLe`/`affineEq`/`reachable` plus
`clearanceGe` and every legacy constructor) — it does NOT re-fork them. The old corpora embed via
`Pred.ofSimple`/`Pred.ofConstraint` (proved semantics-preserving, the no-op extension), so a `Pred`
is a strict GENERALIZATION of the legacy `StateConstraint`: every old program is a `Pred` with the
SAME truth value (`Pred.ofConstraint_eval`).

It then provides the **executor adapter** (`§ Adapter`): a `PredCaveat` evaluating a `Pred` over the
live `(actor, old, new)` scalar transition, and `predStateStepGuarded` which gates the verified
`stateStep` field-write by a `Pred` — committing EXACTLY `stateStep`'s post-state (a domain
restrictor, never a mutator), so every `stateStep` keystone (conservation/authority/forward-sim)
LIFTS verbatim (`predStateStepGuarded_eq`, the mirror of `stateStepGuarded_eq`). This is what makes
the new policy atoms enforced on the LIVE `setFieldA` leg, exactly like `clearanceGe`.

Imports `Exec/EffectsState` (hence `Program`, `RecordKernel`, `Value`) READ-ONLY. Pure, computable,
`#guard`-able; `#assert_axioms`-clean (subset {propext, Classical.choice, Quot.sound}).
-/
import Dregg2.Exec.EffectsState

namespace Dregg2.Exec.PredAlgebra

/- v4.35: core's `Std.LinearOrderPackage Int` supplies a choice-built `BEq`; keep `==` on `Int`
on its decidable equality so `Pred.eval` (and every pin downstream of it) stays choice-free, as
under 4.30 (see Tree/Value.lean). Narrowed to `Int` so `Option`/`List` BEq instances still
resolve as before. -/
local instance (priority := high) intBEqOfDecEq : BEq Int := instBEqOfDecidableEq

open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf stateStep)
open Dregg2.Authority.ClearanceGraph (ClearanceGraph Label)

/-! ## Typed field readers for the NON-scalar leaves (`Value.sym` / `Value.dig`).

The numeric atom catalog (`StateConstraint`) reads `Value.scalar` (the `.int` leaf) ONLY: every
identity/enum/ownership policy went through a lossy `Int`-coercion ("read the owner digest's low
word as a number"). These two readers close that gap — they read a field BY PROPER TYPE, the
data-model twins of `Value.scalar` for the `Value.sym` (interned identity / enum case) and
`Value.dig` (digest / cell-reference) leaves. Both FAIL CLOSED: an absent field, or a field present
at the WRONG leaf (a `.dig` where a `.sym` is wanted, or an `.int`/`.record`), reads `none`, so a
typed atom over a mistyped field REJECTS — never silently coerces. They generalize `Collections.elemSym`
(which reads a `.sym` element field) to the top-level transition record. -/

/-- **`Value.symField v f`** — read named field `f` of `v` as an interned identity (`Value.sym`, a
`Nat`). `none` if absent or NOT a symbol (an `.int`/`.dig`/`.record` at `f` fails closed — a digest
is NOT a symbol, so an ownership-by-symbol policy cannot be fooled by a coincident digest word). The
typed twin of `Value.scalar` for the identity/enum leaf. -/
def _root_.Dregg2.Exec.Value.symField (v : Value) (f : FieldName) : Option Nat :=
  match v.field f with
  | some (.sym s) => some s
  | _             => none

/-- **`Value.digField v f`** — read named field `f` of `v` as a digest / cell-reference
(`Value.dig`, a `Nat`). `none` if absent or NOT a digest (an `.int`/`.sym`/`.record` fails closed —
a symbol is NOT a digest). The typed twin of `Value.scalar` for the cell-reference leaf; the reader
behind owner-match / no-self-transfer. -/
def _root_.Dregg2.Exec.Value.digField (v : Value) (f : FieldName) : Option Nat :=
  match v.field f with
  | some (.dig d) => some d
  | _             => none

/-! ## Structural `Value` equality (the decidable leaf-equality behind `fieldEqField`).

`Value` derives `Repr` only — no `DecidableEq`/`BEq` (it lives in `Exec/Value.lean`, untouched). The
general cross-field-equality atom `fieldEqField` needs to decide `new[f] = new[g]` as VALUES, across
ANY leaf. We provide a self-contained structural decision `Value.beq` (computable, `decide`-reducible,
no global instance) and its soundness `Value.beq_iff` — the type-agnostic equality respects the
STRUCTURE (`.sym 5 ≠ .dig 5`, never a coerced word). -/

mutual
/-- Structural Boolean equality on `Value` (computable; the `decEq` behind `fieldEqField`). -/
def Value.beq : Value → Value → Bool
  | .int a,    .int b    => a == b
  | .dig a,    .dig b    => a == b
  | .sym a,    .sym b    => a == b
  | .record a, .record b => Value.beqFields a b
  | _,         _         => false
/-- Field-list structural equality (ordered key+value match). -/
def Value.beqFields : List (FieldName × Value) → List (FieldName × Value) → Bool
  | [],            []            => true
  | (k, v) :: a,   (k', v') :: b => (k == k') && Value.beq v v' && Value.beqFields a b
  | _,             _             => false
end

mutual
/-- **`Value.beq_iff`** — the structural equality is sound and complete (`beq = true ↔ propositional
equality`). So `fieldEqField` decides genuine `Value` equality. -/
theorem Value.beq_iff : ∀ (a b : Value), Value.beq a b = true ↔ a = b
  | .int a,    .int b    => by simp [Value.beq]
  | .dig a,    .dig b    => by simp [Value.beq]
  | .sym a,    .sym b    => by simp [Value.beq]
  | .record a, .record b => by
      simp only [Value.beq, Value.record.injEq]; exact Value.beqFields_iff a b
  -- the cross-leaf cases: `beq = false`, and the values are unequal by constructor.
  | .int _,    .dig _    => by simp [Value.beq]
  | .int _,    .sym _    => by simp [Value.beq]
  | .int _,    .record _ => by simp [Value.beq]
  | .dig _,    .int _    => by simp [Value.beq]
  | .dig _,    .sym _    => by simp [Value.beq]
  | .dig _,    .record _ => by simp [Value.beq]
  | .sym _,    .int _    => by simp [Value.beq]
  | .sym _,    .dig _    => by simp [Value.beq]
  | .sym _,    .record _ => by simp [Value.beq]
  | .record _, .int _    => by simp [Value.beq]
  | .record _, .dig _    => by simp [Value.beq]
  | .record _, .sym _    => by simp [Value.beq]
theorem Value.beqFields_iff : ∀ (a b : List (FieldName × Value)),
    Value.beqFields a b = true ↔ a = b
  | [],          []          => by simp [Value.beqFields]
  | [],          _ :: _      => by simp [Value.beqFields]
  | _ :: _,      []          => by simp [Value.beqFields]
  | (k, v) :: a, (k', v') :: b => by
      simp only [Value.beqFields, Bool.and_eq_true, List.cons.injEq, Prod.mk.injEq,
        beq_iff_eq, Value.beq_iff v v', Value.beqFields_iff a b]
end

/-! ## The uniform Boolean predicate algebra. -/

/-- **`Pred`** — a clean Boolean algebra over the `Exec` policy-combinator atoms (the
`StateConstraint` catalog, which already carries every atom: `memberOf`/`prefixOf`/`inRangeTwoSided`/
`deltaBounded`/`affineLe`/`affineEq`/`reachable`/`clearanceGe` + the legacy shapes). Orthogonal to the
atoms: `and`/`or`/`not` at EVERY level, plus n-ary `allOf`/`anyOf`. This is the Heyting algebra done
properly — the §B.1(ii) layer the forked 2-level `anyOf`/`SimpleConstraint`-only-`not` could not give. -/
inductive Pred where
  /-- An atom: any `Exec.StateConstraint` (so every legacy + new atom embeds verbatim). -/
  | atom  (c : StateConstraint)
  /-- Top (admits everything). -/
  | tt
  /-- Bottom (admits nothing). -/
  | ff
  /-- Conjunction. -/
  | and   (l r : Pred)
  /-- Disjunction. -/
  | or    (l r : Pred)
  /-- Negation — at EVERY level (not just `SimpleConstraint`). -/
  | not   (p : Pred)
  /-- n-ary conjunction. -/
  | allOf (ps : List Pred)
  /-- n-ary disjunction (replaces the single-level `anyOf`). -/
  | anyOf (ps : List Pred)
  -- ─── TYPED dig/sym FIELD ATOMS (the identity/ownership/enum gap the scalar-only catalog
  --     could not express by PROPER TYPE — `StateConstraint` reads `Value.scalar` (`.int`) only,
  --     so `owner = a digest` / `status ∈ {Draft,Active,Frozen}` went through lossy Int-coercion).
  --     These read `Value.sym`/`Value.dig` by type via `Value.symField`/`Value.digField`; each
  --     FAILS CLOSED on an absent or mistyped field (a digest is not a symbol, a symbol is not a
  --     digest), so an identity policy cannot be fooled by a coincident scalar word. Leaf atoms
  --     (no recursion), so they extend `Pred.eval` with plain match arms — NOT the mutual list arms. ───
  /-- **`symEq f s`** — field `f`'s `Value.sym` identity equals `s`. The typed identity-equality the
  numeric `fieldEquals` could only fake by reading a symbol's word as an `Int`. -/
  | symEq (f : FieldName) (s : Nat)
  /-- **`symMemberOf f set`** — field `f`'s `Value.sym` is one of `set`: enum membership BY PROPER
  TYPE ("`status ∈ {Draft, Active, Frozen}`"). The typed twin of the scalar `memberOf`. -/
  | symMemberOf (f : FieldName) (set : List Nat)
  /-- **`digEq f d`** — field `f`'s `Value.dig` digest equals `d`. Pin a cell-reference / commitment
  to a known digest by type (a coincident `.int`/`.sym` of the same word fails closed). -/
  | digEq (f : FieldName) (d : Nat)
  /-- **`digFieldEq f g`** — two DIGEST fields `f`, `g` are both present as `Value.dig` AND equal.
  THE owner-match tooth (`digFieldEq sender owner`: only the owner may act); its NEGATION
  (`not (digFieldEq from to)`) is the no-self-transfer "from ≠ to". Typed: a non-digest on either
  side fails closed (you cannot owner-match a scalar against a digest). -/
  | digFieldEq (f g : FieldName)
  /-- **`fieldEqField f g`** — GENERAL cross-field equality on the full `Value` leaf (any of
  `.int`/`.sym`/`.dig`/`.record`): `new[f] = new[g]` as values. The type-agnostic generalization of
  `digFieldEq`; fail-closed if EITHER field is absent. -/
  | fieldEqField (f g : FieldName)
  /-- **`symUnchanged f`** — field `f`'s `Value.sym` identity is the SAME in old and new (the typed
  reactive `immutable` for the identity leaf: "the controller symbol must NOT change"). First write
  (absent old) is permitted, mirroring the numeric `immutable`. -/
  | symUnchanged (f : FieldName)
  /-- **`symChanged f`** — field `f`'s `Value.sym` identity DIFFERS between old and new (both present
  as symbols). The reactive complement of `symUnchanged` — a status/role symbol that MUST flip. -/
  | symChanged (f : FieldName)
  /-- **`digUnchanged f`** — field `f`'s `Value.dig` digest is the SAME in old and new (the typed
  reactive `immutable` for the cell-reference leaf: "the OWNER DIGEST must NOT change"). First write
  (absent old) is permitted. THE keystone non-numeric reactive atom. -/
  | digUnchanged (f : FieldName)
  /-- **`digChanged f`** — field `f`'s `Value.dig` digest DIFFERS between old and new (both present
  as digests). The reactive complement — an ownership-handoff slot that MUST move to a new digest. -/
  | digChanged (f : FieldName)
  deriving Repr

/-! **`Pred.eval`** — the structural fold to a `Bool` over `(old, new)`. Decidable, computable,
fail-closed (an atom that cannot read its fields rejects; `ff`/`anyOf []` reject). The `allOf`/`anyOf`
list arms recur through explicit `evalAll`/`evalAny` helpers (so termination is structural — the
`TransitionGuard.anyMatch`/`allMatch` pattern of `Program.lean`). -/
mutual
def Pred.eval : Pred → Value → Value → Bool
  | .atom c,    o, n => evalConstraint c o n
  | .tt,        _, _ => true
  | .ff,        _, _ => false
  | .and l r,   o, n => l.eval o n && r.eval o n
  | .or l r,    o, n => l.eval o n || r.eval o n
  | .not p,     o, n => !(p.eval o n)
  | .allOf ps,  o, n => Pred.evalAll ps o n
  | .anyOf ps,  o, n => Pred.evalAny ps o n
  -- Typed dig/sym leaf atoms (fail-closed via the `Value.symField`/`Value.digField` readers):
  | .symEq f s,        _, n => n.symField f == some s
  | .symMemberOf f set, _, n => match n.symField f with
                                | some x => set.contains x | none => false
  | .digEq f d,        _, n => n.digField f == some d
  | .digFieldEq f g,   _, n => match n.digField f, n.digField g with
                               | some a, some b => a == b | _, _ => false
  | .fieldEqField f g, _, n => match n.field f, n.field g with
                               | some a, some b => Value.beq a b | _, _ => false
  | .symUnchanged f,   o, n => match o.symField f with
                               | none   => true                         -- first write allowed
                               | some a => n.symField f == some a
  | .symChanged f,     o, n => match o.symField f, n.symField f with
                               | some a, some b => !(a == b) | _, _ => false
  | .digUnchanged f,   o, n => match o.digField f with
                               | none   => true                         -- first write allowed
                               | some a => n.digField f == some a
  | .digChanged f,     o, n => match o.digField f, n.digField f with
                               | some a, some b => !(a == b) | _, _ => false
def Pred.evalAll : List Pred → Value → Value → Bool
  | [],      _, _ => true
  | p :: ps, o, n => p.eval o n && Pred.evalAll ps o n
def Pred.evalAny : List Pred → Value → Value → Bool
  | [],      _, _ => false
  | p :: ps, o, n => p.eval o n || Pred.evalAny ps o n
end

/-! ## The no-op embeddings — old corpora LIFT into `Pred` with the SAME truth value. -/

/-- Embed a legacy/new `SimpleConstraint` as a `Pred` (via the `simple` lift to `StateConstraint`). -/
def Pred.ofSimple (c : SimpleConstraint) : Pred := .atom (.simple c)

/-- Embed any `StateConstraint` (legacy or new atom) as a `Pred`. -/
def Pred.ofConstraint (c : StateConstraint) : Pred := .atom c

/-- A legacy `predicate` program (a conjunction of `StateConstraint`s) embeds as `allOf` of atoms. -/
def Pred.ofProgram (cs : List StateConstraint) : Pred := .allOf (cs.map Pred.ofConstraint)

/-- **`ofSimple_eval` (no-op embedding).** A `SimpleConstraint` embedded into `Pred`
evaluates IDENTICALLY to `evalSimple`. The legacy simple layer is a strict sub-algebra. -/
theorem Pred.ofSimple_eval (c : SimpleConstraint) (o n : Value) :
    (Pred.ofSimple c).eval o n = evalSimple c o n := rfl

/-- **`ofConstraint_eval` (no-op embedding).** A `StateConstraint` embedded into `Pred`
evaluates IDENTICALLY to `evalConstraint`. EVERY existing program is a `Pred` with the SAME truth
value — so every proof phrased over `evalConstraint` lifts to the algebra unchanged. -/
theorem Pred.ofConstraint_eval (c : StateConstraint) (o n : Value) :
    (Pred.ofConstraint c).eval o n = evalConstraint c o n := rfl

/-- **`ofProgram_eval`.** A legacy conjunctive `predicate` program embeds as `allOf` and
evaluates to the SAME `cs.all evalConstraint` that `RecordProgram.admits (.predicate cs)` uses. The
forked `predicate`/`anyOf` grammar is exactly the `allOf`/`anyOf` fragment of the clean algebra. -/
theorem Pred.ofProgram_eval (cs : List StateConstraint) (o n : Value) :
    (Pred.ofProgram cs).eval o n = cs.all (fun c => evalConstraint c o n) := by
  unfold Pred.ofProgram
  show Pred.evalAll (cs.map Pred.ofConstraint) o n = cs.all (fun c => evalConstraint c o n)
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.all_cons, Pred.evalAll, Pred.ofConstraint_eval, ih]

/-! ## Heyting / Boolean laws (the algebra is a genuine Boolean algebra, not an ad-hoc grammar). -/

/-- **`eval_not`.** Negation is the Boolean complement at EVERY level (the §B.1 fix: `not`
is not `SimpleConstraint`-only). -/
theorem Pred.eval_not (p : Pred) (o n : Value) : (Pred.not p).eval o n = !(p.eval o n) := rfl

/-- **`eval_not_not`.** Double negation collapses on the decidable algebra. -/
theorem Pred.eval_not_not (p : Pred) (o n : Value) :
    (Pred.not (Pred.not p)).eval o n = p.eval o n := by
  simp only [Pred.eval, Bool.not_not]

/-- **`eval_and`.** Conjunction is `&&`. -/
theorem Pred.eval_and (l r : Pred) (o n : Value) :
    (Pred.and l r).eval o n = (l.eval o n && r.eval o n) := rfl

/-- **`eval_or`.** Disjunction is `||`. -/
theorem Pred.eval_or (l r : Pred) (o n : Value) :
    (Pred.or l r).eval o n = (l.eval o n || r.eval o n) := rfl

/-- **De Morgan.** `¬(l ∧ r) = ¬l ∨ ¬r` on the algebra. -/
theorem Pred.deMorgan_and (l r : Pred) (o n : Value) :
    (Pred.not (Pred.and l r)).eval o n = (Pred.or (Pred.not l) (Pred.not r)).eval o n := by
  simp only [Pred.eval, Bool.not_and]

/-- **De Morgan.** `¬(l ∨ r) = ¬l ∧ ¬r`. -/
theorem Pred.deMorgan_or (l r : Pred) (o n : Value) :
    (Pred.not (Pred.or l r)).eval o n = (Pred.and (Pred.not l) (Pred.not r)).eval o n := by
  simp only [Pred.eval, Bool.not_or]

/-- **`allOf_cons`.** n-ary conjunction unfolds: the head AND the rest. -/
theorem Pred.allOf_cons (p : Pred) (ps : List Pred) (o n : Value) :
    (Pred.allOf (p :: ps)).eval o n = (p.eval o n && (Pred.allOf ps).eval o n) := rfl

/-- **`anyOf_cons`.** n-ary disjunction unfolds: the head OR the rest. -/
theorem Pred.anyOf_cons (p : Pred) (ps : List Pred) (o n : Value) :
    (Pred.anyOf (p :: ps)).eval o n = (p.eval o n || (Pred.anyOf ps).eval o n) := rfl

/-- **`allOf_nil_admits` / `anyOf_nil_rejects` (the unit laws).** Empty `allOf` is `tt`
(vacuous conjunction admits); empty `anyOf` is `ff` (empty disjunction rejects, fail-closed). -/
theorem Pred.allOf_nil_admits (o n : Value) : (Pred.allOf []).eval o n = true := rfl
theorem Pred.anyOf_nil_rejects (o n : Value) : (Pred.anyOf []).eval o n = false := rfl

/-! ## TYPED dig/sym atom admit-characterizations (each PROVED — the identity/ownership/enum teeth).

Each typed atom is decidable and computable (`Pred.eval` is a `Bool`); these `iff`s pin its admit
semantics over the typed `Value.symField`/`Value.digField` readers, mirroring the
`evalConstraint_*_iff` family for the scalar atoms. Each is fail-closed: an absent or MISTYPED field
makes the `Option` reader return `none` and the atom REJECT. -/

/-- **`symEq` admit-char.** Admits IFF field `f` reads as a `Value.sym` whose identity is `s`. A
non-symbol (a `.dig`/`.int`/`.record`) at `f`, or an absent field, fails closed. -/
theorem Pred.symEq_iff (f : FieldName) (s : Nat) (o n : Value) :
    (Pred.symEq f s).eval o n = true ↔ n.symField f = some s := by
  simp only [Pred.eval, beq_iff_eq]

/-- **`symMemberOf` admit-char (enum-by-type).** Admits IFF field `f` reads as a `Value.sym` whose
identity is in `set`. The typed enum membership "`status ∈ {Draft, Active, Frozen}`". -/
theorem Pred.symMemberOf_iff (f : FieldName) (set : List Nat) (o n : Value) :
    (Pred.symMemberOf f set).eval o n = true ↔
      ∃ x, n.symField f = some x ∧ set.contains x = true := by
  simp only [Pred.eval]
  cases h : n.symField f with
  | none   => simp
  | some x => simp

/-- **`digEq` admit-char.** Admits IFF field `f` reads as a `Value.dig` whose digest is `d`. -/
theorem Pred.digEq_iff (f : FieldName) (d : Nat) (o n : Value) :
    (Pred.digEq f d).eval o n = true ↔ n.digField f = some d := by
  simp only [Pred.eval, beq_iff_eq]

/-- **`digFieldEq` admit-char (the owner-match keystone).** Admits IFF BOTH fields read as
`Value.dig` digests AND they are equal. `digFieldEq sender owner` is "only the owner may act"; its
negation is "from ≠ to". A non-digest on either side fails closed. -/
theorem Pred.digFieldEq_iff (f g : FieldName) (o n : Value) :
    (Pred.digFieldEq f g).eval o n = true ↔
      ∃ a b, n.digField f = some a ∧ n.digField g = some b ∧ a = b := by
  simp only [Pred.eval]
  cases hf : n.digField f with
  | none   => simp
  | some a =>
    cases hg : n.digField g with
    | none   => simp
    | some b =>
      simp only [beq_iff_eq, Option.some.injEq]
      exact ⟨fun h => ⟨a, b, rfl, rfl, h⟩, fun ⟨_, _, ha, hb, hab⟩ => ha ▸ hb ▸ hab⟩

/-- **`fieldEqField` admit-char (general cross-field equality).** Admits IFF both fields are present
(any leaf) AND equal as `Value`s. The type-agnostic generalization of `digFieldEq`. -/
theorem Pred.fieldEqField_iff (f g : FieldName) (o n : Value) :
    (Pred.fieldEqField f g).eval o n = true ↔
      ∃ a b, n.field f = some a ∧ n.field g = some b ∧ a = b := by
  simp only [Pred.eval]
  cases hf : n.field f with
  | none   => simp
  | some a =>
    cases hg : n.field g with
    | none   => simp
    | some b =>
      simp only [Value.beq_iff, Option.some.injEq]
      exact ⟨fun h => ⟨a, b, rfl, rfl, h⟩, fun ⟨_, _, ha, hb, hab⟩ => ha ▸ hb ▸ hab⟩

/-- **`symUnchanged` admit-char (typed reactive `immutable`, the identity leaf).** With an old symbol
present, admits IFF the new symbol equals it; an ABSENT old symbol admits (first write). "The
controller symbol must not change." -/
theorem Pred.symUnchanged_iff (f : FieldName) (o n : Value) :
    (Pred.symUnchanged f).eval o n = true ↔
      (∀ a, o.symField f = some a → n.symField f = some a) := by
  simp only [Pred.eval]
  cases ho : o.symField f with
  | none   => simp
  | some a => simp [beq_iff_eq]

/-- **`symChanged` admit-char.** Admits IFF both old and new read as symbols AND they differ. -/
theorem Pred.symChanged_iff (f : FieldName) (o n : Value) :
    (Pred.symChanged f).eval o n = true ↔
      ∃ a b, o.symField f = some a ∧ n.symField f = some b ∧ a ≠ b := by
  simp only [Pred.eval]
  cases ho : o.symField f with
  | none   => simp
  | some a =>
    cases hn : n.symField f with
    | none   => simp
    | some b => simp

/-- **`digUnchanged` admit-char (THE owner-digest reactive — typed `immutable` for the cell-reference
leaf).** With an old digest present, admits IFF the new digest equals it; an ABSENT old digest admits
(first write). "The owner digest must NOT change." -/
theorem Pred.digUnchanged_iff (f : FieldName) (o n : Value) :
    (Pred.digUnchanged f).eval o n = true ↔
      (∀ a, o.digField f = some a → n.digField f = some a) := by
  simp only [Pred.eval]
  cases ho : o.digField f with
  | none   => simp
  | some a => simp [beq_iff_eq]

/-- **`digChanged` admit-char.** Admits IFF both old and new read as digests AND they differ (an
ownership-handoff slot that must move). -/
theorem Pred.digChanged_iff (f : FieldName) (o n : Value) :
    (Pred.digChanged f).eval o n = true ↔
      ∃ a b, o.digField f = some a ∧ n.digField f = some b ∧ a ≠ b := by
  simp only [Pred.eval]
  cases ho : o.digField f with
  | none   => simp
  | some a =>
    cases hn : n.digField f with
    | none   => simp
    | some b => simp

/-! ### TYPED-ATOM NON-VACUITY (`#guard` + `by decide`) — each atom BOTH admits and rejects, and the
THREE motivating teeth: "only owner may act" · "status ∈ enum" · "no self-transfer". No `:= true`. -/

-- The cells: a transfer turn carries `sender`/`owner`/`from`/`to` DIGEST fields and a `status` SYMBOL.
-- Symbol identities for an enum: Draft = 0, Active = 1, Frozen = 2. (Interned ids, by type.)
def transferOwnerOk  : Value := .record [("sender", .dig 7), ("owner", .dig 7)]   -- sender = owner
def transferOwnerBad : Value := .record [("sender", .dig 9), ("owner", .dig 7)]   -- sender ≠ owner
def selfTransfer     : Value := .record [("from", .dig 7), ("to", .dig 7)]        -- from = to (forbidden)
def realTransfer     : Value := .record [("from", .dig 7), ("to", .dig 9)]        -- from ≠ to (ok)

/-- **OWNER-MATCH (`digFieldEq sender owner`) — "only the owner may act".** -/
def ownerMayAct : Pred := .digFieldEq "sender" "owner"
#guard (ownerMayAct.eval (.record []) transferOwnerOk)            -- true  (sender digest = owner digest)
#guard (ownerMayAct.eval (.record []) transferOwnerBad) == false  -- false (a non-owner sender is REFUSED)
example : ownerMayAct.eval (.record []) transferOwnerOk  = true  := by decide
example : ownerMayAct.eval (.record []) transferOwnerBad = false := by decide
-- TYPED: a scalar `sender` of the SAME word does NOT owner-match a digest owner (fail-closed by type).
#guard (ownerMayAct.eval (.record []) (.record [("sender", .int 7), ("owner", .dig 7)])) == false

/-- **NO-SELF-TRANSFER (`not (digFieldEq from to)`) — from ≠ to.** -/
def noSelfTransfer : Pred := .not (.digFieldEq "from" "to")
#guard (noSelfTransfer.eval (.record []) realTransfer)            -- true  (from ≠ to: permitted)
#guard (noSelfTransfer.eval (.record []) selfTransfer) == false   -- false (from = to: REFUSED)
example : noSelfTransfer.eval (.record []) realTransfer = true  := by decide
example : noSelfTransfer.eval (.record []) selfTransfer = false := by decide

/-- **ENUM-BY-TYPE (`symMemberOf status {Draft, Active, Frozen}`).** -/
def statusInEnum : Pred := .symMemberOf "status" [0, 1, 2]   -- {Draft, Active, Frozen}
#guard (statusInEnum.eval (.record []) (.record [("status", .sym 1)]))            -- true  (Active ∈ enum)
#guard (statusInEnum.eval (.record []) (.record [("status", .sym 5)])) == false   -- false (5 ∉ enum)
example : statusInEnum.eval (.record []) (.record [("status", .sym 2)]) = true  := by decide
example : statusInEnum.eval (.record []) (.record [("status", .sym 5)]) = false := by decide
-- TYPED: a SCALAR `status` of the same word is NOT a symbol-enum member (fail-closed by type — the
-- whole point: an enum is over interned symbols, not coercible integers).
#guard (statusInEnum.eval (.record []) (.record [("status", .int 1)])) == false

-- symEq: pin an identity symbol.
#guard ((Pred.symEq "role" 3).eval (.record []) (.record [("role", .sym 3)]))            -- true
#guard ((Pred.symEq "role" 3).eval (.record []) (.record [("role", .sym 4)])) == false   -- false
#guard ((Pred.symEq "role" 3).eval (.record []) (.record [("role", .dig 3)])) == false   -- false (a digest is not the symbol)
example : (Pred.symEq "role" 3).eval (.record []) (.record [("role", .sym 3)]) = true  := by decide
example : (Pred.symEq "role" 3).eval (.record []) (.record [("role", .int 3)]) = false := by decide

-- digEq: pin a cell-reference digest.
#guard ((Pred.digEq "ref" 42).eval (.record []) (.record [("ref", .dig 42)]))            -- true
#guard ((Pred.digEq "ref" 42).eval (.record []) (.record [("ref", .dig 43)])) == false   -- false
#guard ((Pred.digEq "ref" 42).eval (.record []) (.record [("ref", .sym 42)])) == false   -- false (a symbol is not the digest)
example : (Pred.digEq "ref" 42).eval (.record []) (.record [("ref", .dig 42)]) = true  := by decide

-- digUnchanged (THE owner-digest reactive): the owner digest must NOT change across the turn.
def ownerPinned : Pred := .digUnchanged "owner"
#guard (ownerPinned.eval (.record [("owner", .dig 7)]) (.record [("owner", .dig 7)]))            -- true  (unchanged)
#guard (ownerPinned.eval (.record [("owner", .dig 7)]) (.record [("owner", .dig 8)])) == false   -- false (owner moved — REFUSED)
#guard (ownerPinned.eval (.record []) (.record [("owner", .dig 8)]))                             -- true  (first write: absent old admits)
example : ownerPinned.eval (.record [("owner", .dig 7)]) (.record [("owner", .dig 7)]) = true  := by decide
example : ownerPinned.eval (.record [("owner", .dig 7)]) (.record [("owner", .dig 8)]) = false := by decide

-- digChanged (the ownership-handoff dual): the owner digest MUST move.
def ownerHandoff : Pred := .digChanged "owner"
#guard (ownerHandoff.eval (.record [("owner", .dig 7)]) (.record [("owner", .dig 8)]))           -- true  (moved)
#guard (ownerHandoff.eval (.record [("owner", .dig 7)]) (.record [("owner", .dig 7)])) == false  -- false (no move)
example : ownerHandoff.eval (.record [("owner", .dig 7)]) (.record [("owner", .dig 8)]) = true  := by decide

-- symUnchanged / symChanged (the identity-leaf reactive pair).
#guard ((Pred.symUnchanged "ctl").eval (.record [("ctl", .sym 1)]) (.record [("ctl", .sym 1)]))            -- true
#guard ((Pred.symUnchanged "ctl").eval (.record [("ctl", .sym 1)]) (.record [("ctl", .sym 2)])) == false   -- false (controller flipped)
#guard ((Pred.symChanged "ctl").eval (.record [("ctl", .sym 1)]) (.record [("ctl", .sym 2)]))             -- true
#guard ((Pred.symChanged "ctl").eval (.record [("ctl", .sym 1)]) (.record [("ctl", .sym 1)])) == false    -- false (no flip)
example : (Pred.symUnchanged "ctl").eval (.record [("ctl", .sym 1)]) (.record [("ctl", .sym 2)]) = false := by decide
example : (Pred.symChanged "ctl").eval (.record [("ctl", .sym 1)]) (.record [("ctl", .sym 2)]) = true   := by decide

-- fieldEqField (general cross-field equality, type-agnostic): matches across ANY leaf, including syms.
#guard ((Pred.fieldEqField "a" "b").eval (.record []) (.record [("a", .sym 5), ("b", .sym 5)]))            -- true
#guard ((Pred.fieldEqField "a" "b").eval (.record []) (.record [("a", .sym 5), ("b", .sym 6)])) == false   -- false
-- Type-agnostic: it matches when both leaves are the SAME leaf+value, and refuses across leaves
-- (`.sym 5` ≠ `.dig 5` as `Value`s — the structural `Value` equality, not a coerced word).
#guard ((Pred.fieldEqField "a" "b").eval (.record []) (.record [("a", .sym 5), ("b", .dig 5)])) == false
example : (Pred.fieldEqField "a" "b").eval (.record []) (.record [("a", .sym 5), ("b", .sym 5)]) = true := by decide

/-- **`typed_atoms_discriminate` (non-vacuity, theorem layer).** The three motivating teeth each
ADMIT one transition and REFUSE another — genuine discriminators, both polarities, no laundered
vacuity: owner-may-act, no-self-transfer, status∈enum. -/
theorem typed_atoms_discriminate :
    ownerMayAct.eval (.record []) transferOwnerOk = true ∧
    ownerMayAct.eval (.record []) transferOwnerBad = false ∧
    noSelfTransfer.eval (.record []) realTransfer = true ∧
    noSelfTransfer.eval (.record []) selfTransfer = false ∧
    statusInEnum.eval (.record []) (.record [("status", .sym 1)]) = true ∧
    statusInEnum.eval (.record []) (.record [("status", .sym 5)]) = false :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **`typed_atoms_fail_closed_on_type` (the typing is LOAD-BEARING).** Each typed atom REFUSES a
field present at the WRONG leaf with the SAME numeric word — the precise statement that identity/
ownership/enum policies are decided BY TYPE, not by a coercible scalar word (the toy-gap closure):
a scalar sender does not owner-match a digest owner; a scalar status is not in a symbol enum; a
digest is not the symbol; a symbol is not the digest. -/
theorem typed_atoms_fail_closed_on_type :
    ownerMayAct.eval (.record []) (.record [("sender", .int 7), ("owner", .dig 7)]) = false ∧
    statusInEnum.eval (.record []) (.record [("status", .int 1)]) = false ∧
    (Pred.symEq "role" 3).eval (.record []) (.record [("role", .dig 3)]) = false ∧
    (Pred.digEq "ref" 42).eval (.record []) (.record [("ref", .sym 42)]) = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### The typed atoms enforce on the LIVE leg too — a `PredCaveat` carrying a typed atom REJECTS a
typed violation through `predCaveatsAdmit`, exactly like the scalar atoms (the executor teeth). Note
the `PredCaveat` scalar-write adapter lifts `(old,new) : Int` to single-field `.int` records, so the
record-shaped non-vacuity above is the natural home for the typed atoms; here we show a typed atom
composed with the scalar adapter still DISCRIMINATES on a record transition via `Pred.eval` directly,
which is precisely what `predStateStepGuarded` evaluates (it gates on `Pred.eval` over the records). -/

-- A composite REAL policy: a transfer is admissible iff the SENDER owns the cell (typed owner-match)
-- AND it is not a self-transfer (typed) AND the status is a live enum case — authored in the clean
-- Boolean algebra over the TYPED atoms, the thing the scalar-only catalog could not say by type.
def transferPolicy : Pred :=
  .allOf [ .digFieldEq "sender" "owner"
         , .not (.digFieldEq "from" "to")
         , .symMemberOf "status" [0, 1] ]   -- status ∈ {Draft, Active} (not Frozen)

def goodTransfer : Value :=
  .record [("sender", .dig 7), ("owner", .dig 7), ("from", .dig 7), ("to", .dig 9), ("status", .sym 1)]
def frozenTransfer : Value :=   -- owner matches, not self, but status = Frozen (2) ∉ {0,1}
  .record [("sender", .dig 7), ("owner", .dig 7), ("from", .dig 7), ("to", .dig 9), ("status", .sym 2)]
def nonOwnerTransfer : Value := -- status fine, not self, but sender ≠ owner
  .record [("sender", .dig 9), ("owner", .dig 7), ("from", .dig 7), ("to", .dig 9), ("status", .sym 1)]

#guard (transferPolicy.eval (.record []) goodTransfer)              -- true  (all three typed teeth pass)
#guard (transferPolicy.eval (.record []) frozenTransfer) == false   -- false (Frozen status REFUSED)
#guard (transferPolicy.eval (.record []) nonOwnerTransfer) == false -- false (non-owner sender REFUSED)
example : transferPolicy.eval (.record []) goodTransfer = true := by decide

/-- **`transferPolicy_discriminates` (the composite end-to-end, both polarities).** The clean Boolean
algebra over the TYPED atoms admits the well-formed owner-driven transfer and refuses BOTH a frozen
status and a non-owner sender — a genuine multi-tooth discriminator authored by proper type. -/
theorem transferPolicy_discriminates :
    transferPolicy.eval (.record []) goodTransfer = true ∧
    transferPolicy.eval (.record []) frozenTransfer = false ∧
    transferPolicy.eval (.record []) nonOwnerTransfer = false :=
  ⟨by decide, by decide, by decide⟩

/-! ## § Adapter — the LIVE-leg executor enforcement (mirrors `clearanceGe` / `stateStepGuarded`).

A `Pred` is enforced on the LIVE `setFieldA` field-write leg by gating the verified `stateStep`:
`predStateStepGuarded` commits EXACTLY `stateStep`'s post-state ONLY when the `Pred` admits the
`(old-scalar, new-scalar)` transition (the same scalar reads the kernel's per-slot caveats use,
`caveatsAdmit`). The `Pred` only DECIDES; it never mutates — so it is a pure domain restrictor, and
`predStateStepGuarded_eq` lifts every `stateStep` keystone verbatim, exactly like `stateStepGuarded`. -/

/-- **`PredCaveat`** — a `Pred` bound to a slot `field`, enforced on writes to that slot. The
introspectable, algebra-valued generalization of the 7-arm `RecordKernel.SlotCaveat`. -/
structure PredCaveat where
  field : FieldName
  pred  : Pred
  deriving Repr

/-- Evaluate a `PredCaveat` on a scalar write of `new` to its slot whose committed value is `old`.
The `(old, new)` scalars are lifted to single-field records keyed by the caveat's slot, so the full
`Pred`/`evalConstraint` machinery applies on the live leg (the slot-local transition view). -/
def PredCaveat.eval (pc : PredCaveat) (old new : Int) : Bool :=
  pc.pred.eval (.record [(pc.field, .int old)]) (.record [(pc.field, .int new)])

/-- **`predCaveatsAdmit`** — do ALL `Pred`-caveats bound to slot `f` admit the scalar write `new` by
`actor` to `target` (against the committed `fieldOf f (k.cell target)`, defaulting absent to `0` —
dregg1's `FIELD_ZERO`)? The `Pred` analog of `caveatsAdmit`. Computable, fail-closed. -/
def predCaveatsAdmit (caveats : List PredCaveat) (k : RecordKernelState) (f : FieldName)
    (target : CellId) (new : Int) : Bool :=
  (caveats.filter (fun pc => pc.field == f)).all
    (fun pc => pc.eval (fieldOf f (k.cell target)) new)

/-- **`predStateStepGuarded` — the `Pred`-gated field write (computable).** First the
authority gate (`stateStep`), then the `Pred`-caveat gate (`predCaveatsAdmit`): a write commits iff
the actor holds authority AND every `Pred`-caveat bound to the written slot admits the
`(actor, old, new)` transition. Fail-closed on EITHER gate. The post-state is EXACTLY `stateStep`'s —
the `Pred` gate only DECIDES, never mutates. The live-leg executor enforcement of the algebra. -/
def predStateStepGuarded (caveats : List PredCaveat) (s : RecChainedState) (f : FieldName)
    (actor target : CellId) (n : Int) : Option RecChainedState :=
  if predCaveatsAdmit caveats s.kernel f target n = true then
    stateStep s f actor target (.int n)
  else
    none

/-- **`predStateStepGuarded_eq` (the safety net).** A committed `Pred`-gated write is
EXACTLY the underlying `stateStep` write (the algebra gate only restricts the domain — it never
changes the post-state). The bridge that lifts EVERY `stateStep` keystone (conservation, authority,
forward-sim) to the `Pred`-guarded write verbatim — the mirror of `stateStepGuarded_eq`. -/
theorem predStateStepGuarded_eq {caveats : List PredCaveat} {s s' : RecChainedState}
    {f : FieldName} {actor target : CellId} {n : Int}
    (h : predStateStepGuarded caveats s f actor target n = some s') :
    stateStep s f actor target (.int n) = some s' := by
  unfold predStateStepGuarded at h
  by_cases hg : predCaveatsAdmit caveats s.kernel f target n = true
  · rw [if_pos hg] at h; exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`predStateStepGuarded_admits`.** A committed `Pred`-gated write means every
`Pred`-caveat bound to the written slot ADMITTED the transition. The witness that the algebra was
enforced on the live leg. -/
theorem predStateStepGuarded_admits {caveats : List PredCaveat} {s s' : RecChainedState}
    {f : FieldName} {actor target : CellId} {n : Int}
    (h : predStateStepGuarded caveats s f actor target n = some s') :
    predCaveatsAdmit caveats s.kernel f target n = true := by
  unfold predStateStepGuarded at h
  by_cases hg : predCaveatsAdmit caveats s.kernel f target n = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`predStateStepGuarded_violation_fails` (FAIL-CLOSED).** If ANY `Pred`-caveat bound to
the written slot rejects the transition (`predCaveatsAdmit = false`), the write does NOT commit. The
executor-level teeth of the algebra: a violated policy `Pred` rejects the write, BY THE EXECUTOR. -/
theorem predStateStepGuarded_violation_fails (caveats : List PredCaveat) (s : RecChainedState)
    (f : FieldName) (actor target : CellId) (n : Int)
    (h : predCaveatsAdmit caveats s.kernel f target n = false) :
    predStateStepGuarded caveats s f actor target n = none := by
  unfold predStateStepGuarded; rw [if_neg (by rw [h]; simp)]

/-! ## It runs (`#guard`) — the algebra admitting / rejecting real programs, with non-vacuity pairs. -/

/-- A role-cell policy combining a value allowlist with a two-sided band, via the clean Boolean
layer: `role ∈ {1,2,3}  AND  (NOT price > 200)`, authored with `and`/`not` at the `Pred` level. -/
def rolePolicy : Pred :=
  .and (.ofSimple (.memberOf "role" [1, 2, 3]))
       (.not (.ofConstraint (.simple (.fieldGe "price" 201))))

def roleNew_ok  : Value := .record [("role", .int 2), ("price", .int 150)]   -- role∈set ∧ price≤200
def roleNew_bad : Value := .record [("role", .int 2), ("price", .int 250)]   -- price>200 ⇒ reject

#guard (rolePolicy.eval (.record []) roleNew_ok)            -- true
#guard (rolePolicy.eval (.record []) roleNew_bad) == false  -- false

-- The algebra non-vacuity at the `by decide` layer (ADMIT and REJECT witnesses):
example : rolePolicy.eval (.record []) roleNew_ok = true := by decide
example : rolePolicy.eval (.record []) roleNew_bad = false := by decide

/-- An n-ary `anyOf` (multi-branch disjunction the legacy single-level `anyOf` could express only
over simples — here over arbitrary `Pred`s, including the new affine atom): a price band is OK if it
is within `[100,200]` OR satisfies the affine relation `2·bid ≤ 250`. -/
def bandPolicy : Pred :=
  .anyOf [ .ofSimple (.inRangeTwoSided "price" 100 200)
         , .ofConstraint (.affineLe [(2, "bid")] 250) ]

#guard (bandPolicy.eval (.record []) (.record [("price", .int 150), ("bid", .int 999)]))          -- true  (in band)
#guard (bandPolicy.eval (.record []) (.record [("price", .int 999), ("bid", .int 100)]))          -- true  (affine ok: 200 ≤ 250)
#guard (bandPolicy.eval (.record []) (.record [("price", .int 999), ("bid", .int 200)])) == false  -- false (neither)
example : bandPolicy.eval (.record []) (.record [("price", .int 999), ("bid", .int 200)]) = false := by decide

/-! ### Live-leg adapter non-vacuity: a `PredCaveat` admitting one write and rejecting another,
demonstrating the executor-level fail-closed teeth at the SCALAR transition (the `caveatsAdmit` view). -/

-- A monotone-bounded slot policy: the new value must be in `[old? we test absolute]` `[0,100]` AND
-- a member of {10,20,30,40,50,60,70,80,90,100}. Authored as the clean Boolean `and`.
def slotPolicy : Pred :=
  .and (.ofSimple (.inRangeTwoSided "v" 0 100))
       (.ofSimple (.memberOf "v" [10,20,30,40,50,60,70,80,90,100]))

def vCaveat : PredCaveat := { field := "v", pred := slotPolicy }

-- ADMIT: 50 is in [0,100] and ∈ the allowlist.
#guard (vCaveat.eval 0 50)            -- true
-- REJECT: 55 is in range but NOT in the allowlist (the `and` fails closed).
#guard (vCaveat.eval 0 55) == false   -- false
-- REJECT: 110 is in the (extended) allowlist? no — and out of [0,100]; rejected.
#guard (vCaveat.eval 0 110) == false  -- false
example : vCaveat.eval 0 50 = true  := by decide
example : vCaveat.eval 0 55 = false := by decide

-- A bare kernel with all-zero cells (slot "v" reads committed 0 via `fieldOf`):
def kbare : RecordKernelState :=
  { accounts := ∅, cell := fun _ => .record [("v", .int 0)], caps := fun _ => [] }

-- `predCaveatsAdmit` filters to the touched slot: a caveat on slot "v" is irrelevant to a write on "w".
#guard (predCaveatsAdmit [vCaveat] kbare "v" 0 50)            -- true
#guard (predCaveatsAdmit [vCaveat] kbare "v" 0 55) == false   -- false
#guard (predCaveatsAdmit [vCaveat] kbare "w" 0 55)            -- true (irrelevant slot — filtered out)

#assert_axioms Pred.ofSimple_eval
#assert_axioms Pred.ofConstraint_eval
#assert_axioms Pred.ofProgram_eval
#assert_axioms Pred.eval_not_not
#assert_axioms Pred.deMorgan_and
#assert_axioms Pred.deMorgan_or
#assert_axioms Pred.allOf_cons
#assert_axioms Pred.anyOf_cons
#assert_axioms predStateStepGuarded_eq
#assert_axioms predStateStepGuarded_admits
#assert_axioms predStateStepGuarded_violation_fails

-- TYPED dig/sym atom keystones — every admit-char + the non-vacuity teeth, pinned kernel-clean.
#assert_all_clean [
  Pred.symEq_iff,
  Pred.symMemberOf_iff,
  Pred.digEq_iff,
  Pred.digFieldEq_iff,
  Pred.fieldEqField_iff,
  Pred.symUnchanged_iff,
  Pred.symChanged_iff,
  Pred.digUnchanged_iff,
  Pred.digChanged_iff,
  typed_atoms_discriminate,
  typed_atoms_fail_closed_on_type,
  transferPolicy_discriminates
]

end Dregg2.Exec.PredAlgebra
