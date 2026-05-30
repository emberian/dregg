/-
# Dregg2.DSL — the `dregg_program { … }` cell-program eDSL (PHASE-EDSL DSL-A).

This is **DSL-A** of `docs/rebuild/PHASE-EDSL.md`, restricted to the first-party / decidable
fragment of the catalog (PHASE-EDSL §"Recommended minimal first DSL"): a term-level eDSL that
elaborates a readable block of named-field constraints **directly to a verified
`RecordProgram`** (`Exec/Program.lean`).

It is the dregg2 migration of dregg1's external `#[dregg_caveat]`/`#[dregg_effect]` proc-macros
(`dregg-dsl/src/lib.rs`, lowering to a flat `RequirementKind` IR fanned to 8 codegen backends).
In dregg2 there is NO separate IR and NO codegen gap: a `dregg_program { … }` term *is* a
`RecordProgram` — a value in the verified theory — so `recReplay_preserves_sumEquals` /
`recCexec_attests` (`Exec/RecordCellLive.lean`) apply to *this exact term*.

## The rail (PHASE-EDSL §3, REORIENT §6)
The eDSL is a **parser onto already-proved smart constructors** — `declare_syntax_cat` +
`macro_rules` translating each atom to the EXACT `SimpleConstraint`/`StateConstraint`/
`RecordProgram` constructor names of `Exec/Program.lean`. There is **no new metatheory** and
**no `sorry`**: the elaborated term's behaviour is characterized by the existing `@[simp]
admits_*` / `evalSimple_*` / `evalConstraint_*` lemmas, and is checked here by `rfl`/`decide`.

## Covered (first-party / decidable) vs deferred
COVERED atoms (each → its catalog constructor, see the `macro_rules` below):
  `f >= v` / `f <= v` / `f = v`          → `.simple (.fieldGe/.fieldLe/.fieldEquals …)`
  `monotonic f` / `strictMono f`         → `.simple (.monotonic/.strictMono …)`
  `immutable f` / `writeOnce f`          → `.simple (.immutable/.writeOnce …)`
  `f := old + d`                         → `.simple (.fieldDelta …)`
  `not c`                                → `.simple (.not …)`
  `f <= g` (field ≤ field)               → `.fieldLeField …`
  `sum [fs] = v`                         → `.sumEquals …`
  `conserve [ins] => [outs]`             → `.sumEqualsAcross …`
  `f in old + [lo, hi]`                  → `.fieldDeltaInRange …`
  `f : a => b`                           → `.allowedTransitions …`
  `any { c , … }`                        → `.anyOf …`
  `on m { … }`                           → a `.cases` arm (`⟨.methodIs m, …⟩`)
  `invariant { … }`                      → a `.predicate` block

DEFERRED (need the verify/find seam / proof-carrying elaboration — PHASE-EDSL §3, out of scope
for DSL-A): `witnessed s`, `circuit h`, `boundDelta …`. Also deferred: DSL-B (`dregg_choreo`)
and DSL-C (`dregg_effect`).

Pure metaprogramming over `Exec.Program`; no `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.Exec.Program
import Dregg2.Tactics      -- for the `#assert_axioms` honesty pin

namespace Dregg2.DSL

open Dregg2.Exec

/-! ## §1 — The syntax categories.

Three fresh categories isolate the DSL grammar from Lean's term grammar inside the braces:
  * `dregg_simple`     — atoms that elaborate to `SimpleConstraint` (the `not`/`any`-liftable
                         fragment);
  * `dregg_constraint` — atoms that elaborate to `StateConstraint` (a simple, or a cross-slot /
                         sum / state-machine / disjunction atom);
  * `dregg_case`       — an `on m { … }` arm, elaborating to a `TransitionCase`.

Field names are written as plain identifiers and become `String` literals (the name-keyed
`Value` discipline of `Exec/Value.lean`). -/

declare_syntax_cat dregg_simple
declare_syntax_cat dregg_constraint
declare_syntax_cat dregg_case

/-! ### Simple atoms (`SimpleConstraint`).

NB on tokenization: a string atom must be a *single* token, so the multi-word surface forms of
PHASE-EDSL (`:= old +`, `in old + [...]`) are spelled here as sequences of single-token atoms
(`":=" "old" "+"`). Constraint-list separators are `,` (a comma splices cleanly as `$xs,*`). -/

syntax ident " >= " term       : dregg_simple   -- fieldGe
syntax ident " <= " term       : dregg_simple   -- fieldLe  (NB: field-≤-field uses `fieldLe`, below)
syntax ident " = " term        : dregg_simple   -- fieldEquals
syntax "monotonic " ident      : dregg_simple   -- monotonic
syntax "strictMono " ident     : dregg_simple   -- strictMono
syntax "immutable " ident      : dregg_simple   -- immutable
syntax "writeOnce " ident      : dregg_simple   -- writeOnce
syntax ident " := " "old" " + " term : dregg_simple   -- fieldDelta  (`f := old + d`)
syntax "not " dregg_simple     : dregg_simple   -- the Heyting ¬

/-! ### Constraint atoms (`StateConstraint`). -/

-- every simple atom is also a constraint (lifted via `.simple`)
syntax dregg_simple : dregg_constraint
-- field-≤-field (queue tail ≤ head): `fieldLe tail head`
syntax "fieldLe " ident ppSpace ident : dregg_constraint     -- fieldLeField
-- intra-cell post-state sum: `sum [a, b, …] = v`
syntax "sum " "[" ident,* "] " "= " term : dregg_constraint   -- sumEquals
-- intra-cell conservation across the transition: `conserve [ins] => [outs]`
syntax "conserve " "[" ident,* "] " "=> " "[" ident,* "]" : dregg_constraint   -- sumEqualsAcross
-- bounded growth: `f in old + [lo, hi]`
syntax ident " in " "old" " + " "[" term ", " term "]" : dregg_constraint   -- fieldDeltaInRange
-- bounded state machine (single edge): `f : a => b`
syntax ident " : " term " => " term : dregg_constraint        -- allowedTransitions
-- single-level disjunction over simple atoms: `any { c , c , … }`
syntax "any " "{" dregg_simple,* "}" : dregg_constraint   -- anyOf

/-! ## §2 — Field names → `String` literals.

A helper `macro` turning a parsed identifier into its `String`-literal `FieldName`. We keep it
as its own production so every atom that names a field reuses the one rule (and the name-keyed
discipline is in exactly one place). -/

/-- `dregg_field` wraps an identifier; it elaborates to the field's `String` name. -/
syntax (name := dreggField) "dreggField% " ident : term
macro_rules
  | `(dreggField% $f:ident) => pure (Lean.Syntax.mkStrLit (toString f.getId))

/-! ## §3 — Elaboration (`macro_rules`) — the parser onto the smart constructors.

Each rule translates one atom to the EXACT constructor from `Exec/Program.lean`. The
translation is purely syntactic (a `macro`), so no `elab`/elaboration-context is needed for the
first-party fragment — `on m { … }` resolves its method to a `term` (a `Nat`), not a symbol
table, keeping it inside the syntactic-macro regime. -/

/-- Elaborate a `dregg_simple` atom to a `SimpleConstraint` term. -/
syntax (name := dreggSimpleElab) "dregg_simple% " dregg_simple : term
macro_rules
  | `(dregg_simple% $f:ident >= $v:term)        => `(SimpleConstraint.fieldGe     (dreggField% $f) $v)
  | `(dregg_simple% $f:ident <= $v:term)        => `(SimpleConstraint.fieldLe     (dreggField% $f) $v)
  | `(dregg_simple% $f:ident = $v:term)         => `(SimpleConstraint.fieldEquals (dreggField% $f) $v)
  | `(dregg_simple% monotonic $f:ident)         => `(SimpleConstraint.monotonic   (dreggField% $f))
  | `(dregg_simple% strictMono $f:ident)        => `(SimpleConstraint.strictMono  (dreggField% $f))
  | `(dregg_simple% immutable $f:ident)         => `(SimpleConstraint.immutable   (dreggField% $f))
  | `(dregg_simple% writeOnce $f:ident)         => `(SimpleConstraint.writeOnce   (dreggField% $f))
  | `(dregg_simple% $f:ident := old + $d:term)  => `(SimpleConstraint.fieldDelta  (dreggField% $f) $d)
  | `(dregg_simple% not $c:dregg_simple)        => `(SimpleConstraint.not (dregg_simple% $c))

/-- Elaborate a `dregg_constraint` atom to a `StateConstraint` term. -/
syntax (name := dreggConstraintElab) "dregg_constraint% " dregg_constraint : term
macro_rules
  | `(dregg_constraint% $c:dregg_simple) => `(StateConstraint.simple (dregg_simple% $c))
  | `(dregg_constraint% fieldLe $l:ident $r:ident) =>
      `(StateConstraint.fieldLeField (dreggField% $l) (dreggField% $r))
  | `(dregg_constraint% sum [ $fs,* ] = $v:term) =>
      `(StateConstraint.sumEquals [ $[(dreggField% $fs)],* ] $v)
  | `(dregg_constraint% conserve [ $ins,* ] => [ $outs,* ]) =>
      `(StateConstraint.sumEqualsAcross [ $[(dreggField% $ins)],* ] [ $[(dreggField% $outs)],* ])
  | `(dregg_constraint% $f:ident in old + [ $lo:term, $hi:term ]) =>
      `(StateConstraint.fieldDeltaInRange (dreggField% $f) $lo $hi)
  | `(dregg_constraint% $f:ident : $a:term => $b:term) =>
      `(StateConstraint.allowedTransitions (dreggField% $f) [($a, $b)])
  | `(dregg_constraint% any { $cs,* }) =>
      `(StateConstraint.anyOf [ $[(dregg_simple% $cs)],* ])

/-! ### `on m { … }` arms (`TransitionCase`). -/

/-- `on m { c , … }` — a method-dispatching `Cases` arm; `m` is an **identifier** naming the
method id (the symbol table). Resolving the symbol (`deposit`) to a `Nat` is left to the caller
(define `def deposit : Nat := …`): the `on`-rule emits `TransitionGuard.methodIs deposit`, so
the identifier is elaborated as an ordinary term reference to that `def`. Using `ident` (not
`term`) avoids the `term`-grabs-the-`{…}`-block ambiguity, keeping this a pure `macro`
(PHASE-EDSL §3 — the one place §3 anticipated possibly needing an `elab` is sidestepped). -/
syntax (name := dreggCaseSyn) "on " ident " { " dregg_constraint,* " }" : dregg_case

syntax (name := dreggCaseElab) "dregg_case% " dregg_case : term
macro_rules
  | `(dregg_case% on $m:ident { $cs,* }) =>
      `(TransitionCase.mk (TransitionGuard.methodIs $m) [ $[(dregg_constraint% $cs)],* ])

/-! ## §4 — The top-level `dregg_program { … }` block.

A `dregg_program` block is a sequence of items, each either an `on m { … }` case or an
`invariant { … }` predicate block. To stay decidable and structurally simple we support the two
shapes PHASE-EDSL §4 uses:

  * **all-`invariant`** (the counter): `dregg_program { invariant { c , … } }` → `.predicate […]`.
    (Constraints *within* a block are `,`-separated — a single-token separator that splices
    cleanly; program ITEMS are `;`-separated.)
    Multiple `invariant` blocks concatenate their constraints into one `.predicate`.
  * **`on`-arms + a trailing `invariant`** (the escrow): each `on m { … }` becomes a method
    arm; a trailing `invariant { … }` becomes an `always`-guarded arm (so its constraints bind
    on every matching transition). Mixing `on`-arms with an `invariant` ⇒ a `.cases` program.

(If ONLY `invariant`s appear, we emit the leaner `.predicate` form so the counter elaborates to
*exactly* `counterProgram`.) -/

declare_syntax_cat dregg_item
syntax dregg_case                              : dregg_item   -- an `on m { … }` arm
syntax "invariant " "{ " dregg_constraint,* " }" : dregg_item   -- a predicate block

/-- `dregg_program { item ; … }` → a `RecordProgram`. The block is a `;`-separated list of
items. We dispatch on whether any `on`-arm is present:
  * no `on`-arm ⇒ `.predicate` of all the (`invariant`) constraints;
  * some `on`-arm ⇒ `.cases`, with each `on` an arm and each `invariant` an `always` arm. -/
syntax (name := dreggProgram) "dregg_program " "{ " sepBy(dregg_item, ";", "; ", allowTrailingSep) " }" : term

open Lean in
macro_rules
  | `(dregg_program { $items;* }) => do
      -- Partition items into `on`-cases and `invariant`-blocks, preserving order.
      let mut caseStxs : Array (TSyntax `term) := #[]      -- elaborated `TransitionCase`s
      let mut invStxs  : Array (TSyntax `term) := #[]      -- elaborated `StateConstraint`s (flattened)
      let mut sawCase := false
      for item in items.getElems do
        match item with
        | `(dregg_item| $c:dregg_case) =>
            sawCase := true
            caseStxs := caseStxs.push (← `(dregg_case% $c))
        | `(dregg_item| invariant { $cs,* }) =>
            for c in cs.getElems do
              invStxs := invStxs.push (← `(dregg_constraint% $c))
        | _ => Macro.throwUnsupported
      if sawCase then
        -- a `.cases` program: the `on`-arms, then (if any) a single trailing `always` arm
        -- carrying all the `invariant` constraints.
        let invArm? : Array (TSyntax `term) ←
          if invStxs.isEmpty then pure #[]
          else do pure #[← `(TransitionCase.mk TransitionGuard.always [ $invStxs,* ])]
        let allArms := caseStxs ++ invArm?
        `(RecordProgram.cases [ $allArms,* ])
      else
        -- a pure `.predicate` program (the counter shape).
        `(RecordProgram.predicate [ $invStxs,* ])

/-! ## §5 — Worked example: the monotonic counter (PHASE-EDSL §4).

`dregg_program { invariant { monotonic count } }` must elaborate to **exactly** the existing
`counterProgram` (`Exec/Program.lean`): `.predicate [.simple (.monotonic "count")]`. Proved by
`rfl`. -/

/-- The counter, written in the eDSL. -/
def counter : RecordProgram := dregg_program {
  invariant { monotonic count }
}

/-- **The eDSL counter IS exactly the hand-written `counterProgram` — PROVED by `rfl`.** This is
the headline of DSL-A: ~3 readable lines elaborate to the precise verified catalog term, so the
already-proved `recReplay_preserves_sumEquals` / `recCexec_attests` apply to *this* term. -/
theorem counter_eq_counterProgram : counter = counterProgram := rfl

#assert_axioms counter_eq_counterProgram

/-- And the admit/reject behaviour is the catalog's: 7 ≥ 5 admitted, 3 ≥ 5 rejected. The
`@[simp] admits_predicate` + `evalSimple` lemmas characterize it; `decide` checks it. -/
example : counter.admits 0 counterOld counterUp = true := by decide
example : counter.admits 0 counterOld counterDn = false := by decide

#eval counter.admits 0 counterOld counterUp     -- true
#eval counter.admits 0 counterOld counterDn     -- false

/-! ## §6 — Worked example: the escrow (PHASE-EDSL §4).

`deposit`/`release` are method ids (plain `Nat` defs — the caller-supplies-the-symbol-table
discipline of §3). The escrow:

  * `on deposit  { strictMono balance }`
  * `on release  { status : 1 => 2 , immutable amount }`
  * `invariant   { conserve [locked] => [paid] }`

elaborates to the `.cases` program of PHASE-EDSL §4: two method arms + one `always` conservation
arm; an unknown method is default-denied. -/

/-- Method ids (the symbol table the eDSL `on` resolves against). -/
def deposit : Nat := 1
def release : Nat := 2

/-- The escrow, written in the eDSL. -/
def escrow : RecordProgram := dregg_program {
  on deposit  { strictMono balance };
  on release  { status : 1 => 2 , immutable amount };
  invariant   { conserve [locked] => [paid] }
}

/-- **The escrow elaborates to exactly the §4 `.cases` term — PROVED by `rfl`.** Two
method-dispatching arms (`deposit`/`release`) + one `always` conservation arm. -/
theorem escrow_eq_expected :
    escrow = RecordProgram.cases
      [ ⟨.methodIs 1, [.simple (.strictMono "balance")]⟩,
        ⟨.methodIs 2, [.allowedTransitions "status" [(1, 2)], .simple (.immutable "amount")]⟩,
        ⟨.always,     [.sumEqualsAcross ["locked"] ["paid"]]⟩ ] := rfl

#assert_axioms escrow_eq_expected

/-! ### Admit/reject checks (the catalog `admits` golden oracle on the elaborated term). -/

-- a deposit that strictly increases `balance` AND conserves `locked`/`paid` is admitted.
example :
    escrow.admits deposit
      (.record [("balance", .int 100), ("locked", .int 50), ("paid", .int 0)])
      (.record [("balance", .int 150), ("locked", .int 50), ("paid", .int 0)]) = true := by decide

-- a deposit that DECREASES balance is rejected (strictMono fails).
example :
    escrow.admits deposit
      (.record [("balance", .int 100), ("locked", .int 50), ("paid", .int 0)])
      (.record [("balance",  .int 90), ("locked", .int 50), ("paid", .int 0)]) = false := by decide

-- a `release` taking `status` 1→2 with `amount` unchanged AND conserving (`new[locked] =
-- old[locked] + new[paid]`: 70 = 50 + 20) is admitted.
example :
    escrow.admits release
      (.record [("status", .int 1), ("amount", .int 7), ("locked", .int 50), ("paid", .int 0)])
      (.record [("status", .int 2), ("amount", .int 7), ("locked", .int 70), ("paid", .int 20)]) = true := by decide

-- a `release` that MUTATES `amount` is rejected (immutable fails), conservation notwithstanding.
example :
    escrow.admits release
      (.record [("status", .int 1), ("amount", .int 7), ("locked", .int 50), ("paid", .int 0)])
      (.record [("status", .int 2), ("amount", .int 9), ("locked", .int 70), ("paid", .int 20)]) = false := by decide

-- HONEST SEMANTICS NOTE (corrects PHASE-EDSL §4 VC 1): because the escrow carries a trailing
-- `invariant` (an `always`-guarded arm), the `always` arm matches EVERY method — so an unknown
-- method is NOT default-denied; it is governed by the conservation invariant alone. (Pure
-- default-deny on unknown methods holds only for an `on`-arms-ONLY program with no `invariant`,
-- e.g. `Exec.depositOnly`.) An unknown method that VIOLATES conservation IS denied:
example :
    escrow.admits 3
      (.record [("locked", .int 50), ("paid", .int 0)])
      (.record [("locked", .int 99), ("paid", .int 0)]) = false := by decide   -- 99 ≠ 50 + 0

-- …and an `on`-arms-only program (no `invariant`) DOES default-deny unknown methods — the
-- existing `Exec.depositOnly` (method 2 has no matching arm):
example : depositOnly.admits 2 balLo balHi = false := by decide

#eval escrow.admits deposit
  (.record [("balance", .int 100), ("locked", .int 50), ("paid", .int 0)])
  (.record [("balance", .int 150), ("locked", .int 50), ("paid", .int 0)])     -- true
#eval escrow.admits 3
  (.record [("locked", .int 50), ("paid", .int 0)])
  (.record [("locked", .int 99), ("paid", .int 0)])                            -- false (violates conservation)

/-! ## §7 — A few more atom smoke-tests (each atom elaborates to its catalog constructor).

These pin the remaining first-party atoms to their exact constructors by `rfl`, documenting the
1:1 surface→catalog map and guarding it against drift. -/

example : (dregg_program { invariant { balance >= 0 } } : RecordProgram)
        = .predicate [.simple (.fieldGe "balance" 0)] := rfl
example : (dregg_program { invariant { count <= 100 } } : RecordProgram)
        = .predicate [.simple (.fieldLe "count" 100)] := rfl
example : (dregg_program { invariant { status = 2 } } : RecordProgram)
        = .predicate [.simple (.fieldEquals "status" 2)] := rfl
example : (dregg_program { invariant { writeOnce owner } } : RecordProgram)
        = .predicate [.simple (.writeOnce "owner")] := rfl
example : (dregg_program { invariant { balance := old + 5 } } : RecordProgram)
        = .predicate [.simple (.fieldDelta "balance" 5)] := rfl
example : (dregg_program { invariant { not monotonic count } } : RecordProgram)
        = .predicate [.simple (.not (.monotonic "count"))] := rfl
example : (dregg_program { invariant { fieldLe tail head } } : RecordProgram)
        = .predicate [.fieldLeField "tail" "head"] := rfl
example : (dregg_program { invariant { sum [locked, free] = 100 } } : RecordProgram)
        = .predicate [.sumEquals ["locked", "free"] 100] := rfl
example : (dregg_program { invariant { count in old + [0, 10] } } : RecordProgram)
        = .predicate [.fieldDeltaInRange "count" 0 10] := rfl
example : (dregg_program { invariant { status : 0 => 1 } } : RecordProgram)
        = .predicate [.allowedTransitions "status" [(0, 1)]] := rfl
example : (dregg_program { invariant { any { balance >= 0 , status = 1 } } } : RecordProgram)
        = .predicate [.anyOf [.fieldGe "balance" 0, .fieldEquals "status" 1]] := rfl

end Dregg2.DSL
