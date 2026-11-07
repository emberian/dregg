/-
# `Dregg2.Circuit.GateExpr` — ⚑ THE ONE GATE AST, AND THE FIVE THAT ARE ITS VIEWS.

## The measured finding this answers

A structural census (2026-08-06) found **five gate ASTs** in this tree and concluded that the split
*"is what physically blocks reuse, not laziness."* Read at source, here is what each one is:

| AST | defined at | leaves | `const` / `add` / `mul` |
|---|---|---|---|
| `Circuit.Expr`   | `Dregg2/Circuit.lean:72`                 | `var c`                                | identical |
| `EmittedExpr`    | `Dregg2/Exec/CircuitEmit.lean:64`        | `var c`                                | identical |
| `WindowExpr`     | `Dregg2/Circuit/DescriptorIR2.lean:598`  | `loc c` · `nxt c`                      | identical |
| `ChalExpr`       | `Dregg2/Circuit/DescriptorIR2.lean:742`  | `loc c` · `nxt c` · `chal i`           | identical |
| `TExpr`          | `Dregg2/Circuit/TableAirIR.lean:177`     | `loc c` · `nxt c` · `shr i` · `prep c` | identical |

⚑ **THE ANSWER TO "EXPRESSIVE POWER OR VOCABULARY" IS: VOCABULARY, AND NOTHING ELSE.** The
arithmetic skeleton — `const : ℤ`, binary `add`, binary `mul`, no other former — is
character-for-character the same in all five. Every difference is a difference in the LEAF ALPHABET.
Three of the five say so in their own docblocks:

* `CircuitEmit.lean:57` — *"`EmittedExpr` is `Expr` re-spelled as a tagged wire form"*. The two are
  the **same inductive up to nothing at all**: `var`/`const`/`add`/`mul` against `var`/`const`/`add`/
  `mul`, and `emitExpr`/`decodeExpr` are the structural identity.
* `DescriptorIR2.lean:596` — *"It is a strict generalization — `EmittedExpr.var c` is
  `WindowExpr.loc c`."*
* `TableAirIR.lean:160` — *"`TExpr` is `WindowExpr`'s five leaves plus `shr` and `prep`. The wire
  tags of the shared five are IDENTICAL."*

and `ChalExpr` already SHIPS its derived view: `ChalExpr.ofWindow` with `ofWindow_eval`
(`DescriptorIR2.lean`). One of the collapses was already done, once, by hand, for one pair —
`chal_ofWindow_is_alphabet_extension` below recovers it as an instance of the general fact.

## ⚑ THE SIXTH AND SEVENTH COPIES, WHICH ARE THE PROOF THAT THE LEAF ALPHABET IS THE WHOLE STORY

`Head` (`Emit/AirBuilder.lean:54`) is not an AST — it is the **sum-of-products normal form** the
corpus renders into. And `AirNormalForm.lean` §3 carries `WHead`, the *same* normal form again, for
the *same* reason, and says it outright:

> *"`AirBuilder.Head` is `Σ coeff · ∏ COLUMNS + const`: its leaves are current-row columns, so it
> has no name for the next-row leaf a `.transition` continuity gate reads. That is why window and
> boundary bodies had no canonical renderer at all … `WHead` closes that: same shape, same rendering
> rules, **leaves widened to `loc`/`nxt`**."*

The cost, counted inside that ONE file: `isVarProd`/`isVarProdW`, `isTermAtom`/`isTermAtomW`,
`isNormal`/`isNormalW`, `Head`/`WHead` and their builder methods each, `varsProd`/`wVarsProd`,
`termToExpr`/`wTermToExpr`, `headExprs`/`wHeadExprs`, `foldExprs`/`wFoldExprs`,
`headToExpr`/`wHeadToWindow`, and the supporting `isNormal…` proofs twice over. **A leaf alphabet
was `Nat` instead of `WLeaf`, and it cost ~20 definitions and ~8 proofs in a single file.**

`WLeaf` is already the right idea. This module is `WLeaf` taken seriously: the alphabet becomes a
PARAMETER, and every one of those pairs becomes one definition applied twice.

## ⚑ AND `Head` ITSELF SHIPS THREE TIMES, IN TWO INCOMPATIBLE RENDERINGS

`Head` + `headToExpr` are written out at `Emit/AirBuilder.lean:54`, `Emit/AutomataflStepEmit.lean:162`
and `Emit/AutomataflResolveEmit.lean:656`. `AirBuilder`'s docblock names the migration as debt
(*"`AutomataflStepEmit`/`AutomataflResolveEmit` still carry their own `Head` copies … NOT done here"*,
*"a mechanical, separately-verifiable change"*) — but read the three `termToExpr`s and the debt turns
out to be **not mechanical at all**, which is very probably why it was never paid:

    AirBuilder.termToExpr (coeff, cols)  =  .mul (.const coeff) (varsProd cols)
    Automatafl*.termToExpr (coeff, cols) =  if coeff == 1 then varsProd cols else .mul …

and `AirBuilder.headExprs` keeps zero-coefficient terms where the automatafl copies `filter` them
out. **The "shared" vocabulary emits different bytes from the two files it was hoisted from.** So
adopting it was never a rename; it was always a re-emit, and nobody priced it as one.

⚑ That divergence is not cosmetic: the surviving `AirBuilder` shape is the one
`AirNormalForm.isNormal` accepts (*"a UNIT COEFFICIENT IS RENDERED `mul(const 1, x)`, NEVER BARE
`x`"*), so the automatafl renderer emits bodies **outside the corpus normal form by construction** —
`elide_is_not_normal` below, on the most ordinary head there is.

## What this module IS

**One AST, one head, one normal form, one gadget library — with the leaf alphabet as a parameter**,
and every existing object pinned to its instantiation:

* `GExpr L` — the gate AST. `L` is the leaf alphabet.
* `ExprOps L E` — a **derived view**: the four constructors of a target AST. `render` is the fold.
* `GHead L` — the sum-of-products head. `Head` is `GHead VLeaf`, `WHead` is `GHead WLeaf`.
* `gIsNormal` — the normal-form predicate, once, over any alphabet.
* §7 — the gadgets the census ranked: the alphabet/booleanity gate, the mux, the thread.

⚑ **NOTHING EMITTED MOVES, AND THAT IS PROVED THE WAY THIS CONE ALWAYS PROVES IT.** Every byte pin
below is a GENERAL theorem — over every head, every column, every alphabet — closed `by rfl`, the
`PastaMsmBucketed.rowGatesWith_pallas` shape (*"the parameterised row and the inherited one are the
SAME emitted list and no gate moved"*). Nothing here is a spot check on a fixture.

## ⚑ WHAT A COLLAPSED AST BUYS THE CERTIFIED LOWERING

`EffectLowerCertified.AirLeg.forces` has one arm per leg kind, and three of them — `.gate`,
`.window`, `.chal` — say the SAME thing (*"the body vanishes, under the scope the `RowSel` names"*)
in three different ASTs' `eval`, because the source language has three body types. With one AST at
one alphabet, `.gate` is `.window` at `RowSel.transition` over the `loc`-only sub-alphabet and
`.chal` is `.window` over the challenge-extended one, so those three arms — and the three refinement
lemmas that discharge them — become one. That is the strongest single argument for the collapse and
it is stated here rather than assumed: §4b proves the three `eval`s ARE `evalG` at three leaf
environments, which is exactly the hypothesis such a merge needs.

## ⚠ THE LINE THIS MODULE DOES NOT CROSS — the bespoke gates, named

A gate is BESPOKE when the **mathematics** is bespoke, and those are left alone on purpose:

* **Poseidon round gates** (`Poseidon2RoundGates`, `TableAirIR`'s chip arms) — the S-box degree, the
  round constants and the MDS layer are the primitive's definition. There is no shorter true form,
  and `TableAirIR`'s own `defs` sharing (140,850 nodes against 3,194, measured on the chip) is the
  right abstraction for it, not a gadget helper.
* **Complete-addition formulae** (`swCompleteAddGadget`, `pallasCompleteAdd`, `vestaCompleteAdd`) —
  the exceptional-case algebra IS the gadget. `PastaMsmBucketed` already parameterised the one thing
  that genuinely repeats there (the curve) and pinned it by `rfl`; the formula itself does not repeat.
* **Limb / carry arithmetic** (`LimbTally`, the RCB carry chains, `EmitSameOpeningGadget.carryBody`) —
  a radix-`2^16` carry gate names a different polynomial from a thread gate. ⚠ `EmitSameOpeningGadget.
  carryBody` matches the thread census BY NAME and is NOT a thread; it stays where it is.
* **Domain and arity tags** — `FOLD_TAG`, `CHIP_ADMITTED_ARITIES`. A constant that separates two hash
  domains is content, not boilerplate.

Collapsing any of those would be inventing a generality the mathematics does not have. The three
families §7 factors are the opposite case: identical polynomials, written out repeatedly, in
renderings that disagree with each other.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. NEW file; imports read-only; ADDITIVE — every existing
definition is untouched and pinned equal to its instantiation.
-/
import Dregg2.Circuit.TableAirIR
import Dregg2.Circuit.Emit.AirBuilder

namespace Dregg2.Circuit.GateExpr

open Dregg2.Circuit (Assignment Expr)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (WindowExpr ChalExpr)
open Dregg2.Circuit.TableAirIR (TExpr TRowEnv)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false

/-! ## §1 — ⚑ THE ONE GATE AST.

Compare, constructor for constructor, with the five in the table above. The only thing that ever
differed is `leaf`. -/

/-- ⚑ **THE GATE AST.** A field constant, addition, multiplication, and a leaf drawn from the
alphabet `L`. Every gate AST in this tree is this inductive at some `L`. -/
inductive GExpr (L : Type) where
  /-- A leaf of the alphabet — the ONLY place the five ASTs ever differed. -/
  | leaf  : L → GExpr L
  /-- A field constant. -/
  | const : ℤ → GExpr L
  | add   : GExpr L → GExpr L → GExpr L
  | mul   : GExpr L → GExpr L → GExpr L
  deriving Repr, DecidableEq

/-- Re-alphabet an expression — the map that makes "a strict generalization of" a fact rather than a
docblock sentence. -/
def GExpr.map {L M : Type} (f : L → M) : GExpr L → GExpr M
  | .leaf l  => .leaf (f l)
  | .const k => .const k
  | .add a b => .add (GExpr.map f a) (GExpr.map f b)
  | .mul a b => .mul (GExpr.map f a) (GExpr.map f b)

/-! ## §2 — the leaf alphabets, as the extension chain the ASTs actually form.

`WLeaf` (`loc`/`nxt`) already exists in `AirNormalForm`; it is reused rather than re-declared, so
this module adds no third spelling of a row tag. The other two alphabets are stated as EXTENSIONS of
it, which is exactly the relationship the two docblocks assert in prose. -/

/-- The one-row alphabet: a column index. `Circuit.Expr` and `EmittedExpr` are `GExpr VLeaf`. -/
abbrev VLeaf := Nat

/-- The TWO-ROW alphabet: a current-row or next-row column. `WindowExpr` is `GExpr WLeaf`.

⚑ **MOVED HERE FROM `AirNormalForm` (2026-08-06).** It was declared there because that file needed a
leaf type to state `WHead` with, and `WHead` existed because `AirBuilder.Head`'s leaves were `Nat`.
`WLeaf` was always the right idea in the wrong place: it is the parameter, not a local. -/
inductive WLeaf where
  | loc (c : Nat)
  | nxt (c : Nat)
  deriving Repr, DecidableEq

def WLeaf.expr : WLeaf → WindowExpr
  | .loc c => .loc c
  | .nxt c => .nxt c

/-- The CHALLENGE alphabet — `WLeaf` plus the verifier's Fiat–Shamir leaf. `ChalExpr` is
`GExpr CLeaf`, and the `win` injection IS `ChalExpr.ofWindow`. -/
inductive CLeaf where
  | win  (l : WLeaf)
  | chal (i : Nat)
  deriving Repr, DecidableEq

/-- The TABLE alphabet — `WLeaf` plus the sharing leaf and the preprocessed leaf. `TExpr` is
`GExpr TLeaf`. -/
inductive TLeaf where
  | win  (l : WLeaf)
  | shr  (i : Nat)
  | prep (c : Nat)
  deriving Repr, DecidableEq

/-! ## §3 — ⚑ THE DERIVED VIEW.

`ExprOps L E` is the four constructors of a target AST. `render` folds a `GExpr L` through them.
That is what "the others are derived views" means concretely: each existing AST is `render` at its
own ops record, and §3b proves the view is faithful — the roundtrip is the identity **on every
expression**, not on a fixture. -/

/-- The four constructors of a target gate AST — a derived view of `GExpr L`. -/
structure ExprOps (L : Type) (E : Type) where
  leaf  : L → E
  const : ℤ → E
  add   : E → E → E
  mul   : E → E → E

/-- ⚑ **THE VIEW.** The structural fold that lowers the one AST into any target. -/
def render {L E : Type} (O : ExprOps L E) : GExpr L → E
  | .leaf l  => O.leaf l
  | .const k => O.const k
  | .add a b => O.add (render O a) (render O b)
  | .mul a b => O.mul (render O a) (render O b)

/-- The view onto `GExpr L` itself — the alphabet's own AST, used to state the alphabet-generic
facts (`gHeadToExpr_gIsNormal`) once. -/
abbrev idOps {L : Type} : ExprOps L (GExpr L) := ⟨.leaf, .const, .add, .mul⟩

theorem render_idOps {L : Type} (e : GExpr L) : render idOps e = e := by
  induction e with
  | leaf l => rfl
  | const k => rfl
  | add a b iha ihb => simp only [render, iha, ihb]
  | mul a b iha ihb => simp only [render, iha, ihb]

/-- The challenge leaf's target constructor. -/
def CLeaf.expr : CLeaf → ChalExpr
  | .win (.loc c) => .loc c
  | .win (.nxt c) => .nxt c
  | .chal i       => .chal i

/-- The table leaf's target constructor. -/
def TLeaf.expr : TLeaf → TExpr
  | .win (.loc c) => .loc c
  | .win (.nxt c) => .nxt c
  | .shr i        => .shr i
  | .prep c       => .prep c

/-- The view onto the SOURCE IR (`Circuit.Expr`). -/
abbrev toSource : ExprOps VLeaf Expr := ⟨.var, .const, .add, .mul⟩
/-- The view onto the WIRE form (`EmittedExpr`). ⚑ Identical to `toSource` field for field — the
two ASTs are the same inductive, and this record is where that stops being prose. -/
abbrev toEmitted : ExprOps VLeaf EmittedExpr := ⟨.var, .const, .add, .mul⟩
/-- The view onto the two-row form (`WindowExpr`). -/
abbrev toWindow : ExprOps WLeaf WindowExpr := ⟨WLeaf.expr, .const, .add, .mul⟩
/-- The view onto the challenge form (`ChalExpr`). -/
abbrev toChal : ExprOps CLeaf ChalExpr := ⟨CLeaf.expr, .const, .add, .mul⟩
/-- The view onto the table form (`TExpr`). -/
abbrev toTable : ExprOps TLeaf TExpr := ⟨TLeaf.expr, .const, .add, .mul⟩

/-! ### §3b — the views are FAITHFUL: each existing AST embeds and comes back unchanged.

Each `of*` is the embedding, each theorem is the roundtrip **over every expression of that AST**. A
view that lost information would fail here, and a view that were secretly a different grammar could
not be stated at all. -/

/-- Embed a `Circuit.Expr`. -/
def ofSource : Expr → GExpr VLeaf
  | .var v   => .leaf v
  | .const k => .const k
  | .add a b => .add (ofSource a) (ofSource b)
  | .mul a b => .mul (ofSource a) (ofSource b)

/-- Embed an `EmittedExpr`. -/
def ofEmitted : EmittedExpr → GExpr VLeaf
  | .var v   => .leaf v
  | .const k => .const k
  | .add a b => .add (ofEmitted a) (ofEmitted b)
  | .mul a b => .mul (ofEmitted a) (ofEmitted b)

/-- Embed a `WindowExpr`. -/
def ofWindow : WindowExpr → GExpr WLeaf
  | .loc c   => .leaf (.loc c)
  | .nxt c   => .leaf (.nxt c)
  | .const k => .const k
  | .add a b => .add (ofWindow a) (ofWindow b)
  | .mul a b => .mul (ofWindow a) (ofWindow b)

/-- Embed a `ChalExpr`. -/
def ofChal : ChalExpr → GExpr CLeaf
  | .loc c   => .leaf (.win (.loc c))
  | .nxt c   => .leaf (.win (.nxt c))
  | .chal i  => .leaf (.chal i)
  | .const k => .const k
  | .add a b => .add (ofChal a) (ofChal b)
  | .mul a b => .mul (ofChal a) (ofChal b)

/-- Embed a `TExpr`. -/
def ofTable : TExpr → GExpr TLeaf
  | .loc c   => .leaf (.win (.loc c))
  | .nxt c   => .leaf (.win (.nxt c))
  | .shr i   => .leaf (.shr i)
  | .prep c  => .leaf (.prep c)
  | .const k => .const k
  | .add a b => .add (ofTable a) (ofTable b)
  | .mul a b => .mul (ofTable a) (ofTable b)

/-- ⚑ `Circuit.Expr` is a view of `GExpr VLeaf` — for EVERY expression. -/
theorem render_ofSource (e : Expr) : render toSource (ofSource e) = e := by
  induction e with
  | var v => rfl
  | const k => rfl
  | add a b iha ihb => simp only [ofSource, render, iha, ihb]
  | mul a b iha ihb => simp only [ofSource, render, iha, ihb]

/-- ⚑ `EmittedExpr` is a view of `GExpr VLeaf` — for EVERY expression. -/
theorem render_ofEmitted (e : EmittedExpr) : render toEmitted (ofEmitted e) = e := by
  induction e with
  | var v => rfl
  | const k => rfl
  | add a b iha ihb => simp only [ofEmitted, render, iha, ihb]
  | mul a b iha ihb => simp only [ofEmitted, render, iha, ihb]

/-- ⚑ `WindowExpr` is a view of `GExpr WLeaf` — for EVERY expression. -/
theorem render_ofWindow (e : WindowExpr) : render toWindow (ofWindow e) = e := by
  induction e with
  | loc c => rfl
  | nxt c => rfl
  | const k => rfl
  | add a b iha ihb => simp only [ofWindow, render, iha, ihb]
  | mul a b iha ihb => simp only [ofWindow, render, iha, ihb]

/-- ⚑ `ChalExpr` is a view of `GExpr CLeaf` — for EVERY expression. -/
theorem render_ofChal (e : ChalExpr) : render toChal (ofChal e) = e := by
  induction e with
  | loc c => rfl
  | nxt c => rfl
  | const k => rfl
  | chal i => rfl
  | add a b iha ihb => simp only [ofChal, render, iha, ihb]
  | mul a b iha ihb => simp only [ofChal, render, iha, ihb]

/-- ⚑ `TExpr` is a view of `GExpr TLeaf` — for EVERY expression. -/
theorem render_ofTable (e : TExpr) : render toTable (ofTable e) = e := by
  induction e with
  | loc c => rfl
  | nxt c => rfl
  | const k => rfl
  | shr i => rfl
  | prep c => rfl
  | add a b iha ihb => simp only [ofTable, render, iha, ihb]
  | mul a b iha ihb => simp only [ofTable, render, iha, ihb]

/-- ⚑ **THE `emitExpr` STEP IS THE IDENTITY, AND NOW IT IS SAID ONCE.** `CircuitEmit`'s docblock
justifies keeping `EmittedExpr` a separate inductive so *"the emitter is an explicit serialization
step with its own faithfulness obligation"*. Read at the two ops records, the obligation is that
`toSource` and `toEmitted` are the same four constructors; the serialization that actually happens
is `toJson`, one level further down, and it is not this. -/
theorem source_view_is_emitted_view (e : GExpr VLeaf) :
    Dregg2.Exec.CircuitEmit.emitExpr (render toSource e) = render toEmitted e := by
  induction e with
  | leaf l => rfl
  | const k => rfl
  | add a b iha ihb =>
    simp only [render, Dregg2.Exec.CircuitEmit.emitExpr, iha, ihb]
  | mul a b iha ihb =>
    simp only [render, Dregg2.Exec.CircuitEmit.emitExpr, iha, ihb]

/-- ⚑ **THE ONE COLLAPSE THAT WAS ALREADY DONE BY HAND, RECOVERED AS AN INSTANCE.**
`ChalExpr.ofWindow` — the tree's existing, hand-written derived view — is `render toChal` after the
alphabet injection `CLeaf.win`. So `WindowExpr ⊂ ChalExpr` was never a special fact about
challenges; it is the leaf alphabet extending, which is the only thing that ever happens here. -/
theorem chal_ofWindow_is_alphabet_extension (e : GExpr WLeaf) :
    ChalExpr.ofWindow (render toWindow e) = render toChal (GExpr.map CLeaf.win e) := by
  induction e with
  | leaf l => cases l <;> rfl
  | const k => rfl
  | add a b iha ihb =>
    simp only [render, GExpr.map, ChalExpr.ofWindow, iha, ihb]
  | mul a b iha ihb =>
    simp only [render, GExpr.map, ChalExpr.ofWindow, iha, ihb]

/-! ## §4 — ⚑ THE DENOTATION, ONCE.

Five ASTs carried five `eval`s that agreed line for line (`Expr.eval`, `EmittedExpr.eval`,
`WindowExpr.eval`, `ChalExpr.eval`, `TExpr.evalWith`) and differed only in how a leaf is looked up.
`evalG` takes the lookup as its parameter, and §4b proves each existing `eval` is this one at its own
leaf environment — **for every expression**. -/

/-- ⚑ **THE DENOTATION.** The leaf environment `ρ` is the only per-AST content. -/
def evalG {L : Type} (ρ : L → ℤ) : GExpr L → ℤ
  | .leaf l  => ρ l
  | .const k => k
  | .add a b => evalG ρ a + evalG ρ b
  | .mul a b => evalG ρ a * evalG ρ b

/-- The one-row leaf environment. -/
def vEnv (a : Assignment) : VLeaf → ℤ := a
/-- The two-row leaf environment. -/
def wEnv (env : VmRowEnv) : WLeaf → ℤ
  | .loc c => env.loc c
  | .nxt c => env.nxt c
/-- The challenge leaf environment. -/
def cEnv (env : VmRowEnv) : CLeaf → ℤ
  | .win l  => wEnv env l
  | .chal i => env.chal i
/-- The table leaf environment — `sv` is the already-resolved definition vector. -/
def tEnv (sv : Array ℤ) (env : TRowEnv) : TLeaf → ℤ
  | .win (.loc c) => env.loc c
  | .win (.nxt c) => env.nxt c
  | .shr i        => sv.getD i 0
  | .prep c       => env.prep c

/-! ### §4b — ⚑ every existing `eval` IS `evalG`.

Five denotations, one denotation and four leaf environments. This is the hypothesis the
`EffectLowerCertified.forces` merge described in the header needs. -/

theorem eval_render_toSource (a : Assignment) (e : GExpr VLeaf) :
    (render toSource e).eval a = evalG (vEnv a) e := by
  induction e with
  | leaf l => rfl
  | const k => rfl
  | add x y ihx ihy => simp only [render, Expr.eval, evalG, ihx, ihy]
  | mul x y ihx ihy => simp only [render, Expr.eval, evalG, ihx, ihy]

theorem eval_render_toEmitted (a : Assignment) (e : GExpr VLeaf) :
    (render toEmitted e).eval a = evalG (vEnv a) e := by
  induction e with
  | leaf l => rfl
  | const k => rfl
  | add x y ihx ihy =>
    simp only [render, Dregg2.Exec.CircuitEmit.EmittedExpr.eval, evalG, ihx, ihy]
  | mul x y ihx ihy =>
    simp only [render, Dregg2.Exec.CircuitEmit.EmittedExpr.eval, evalG, ihx, ihy]

theorem eval_render_toWindow (env : VmRowEnv) (e : GExpr WLeaf) :
    (render toWindow e).eval env = evalG (wEnv env) e := by
  induction e with
  | leaf l => cases l <;> rfl
  | const k => rfl
  | add x y ihx ihy => simp only [render, WindowExpr.eval, evalG, ihx, ihy]
  | mul x y ihx ihy => simp only [render, WindowExpr.eval, evalG, ihx, ihy]

theorem eval_render_toChal (env : VmRowEnv) (e : GExpr CLeaf) :
    (render toChal e).eval env = evalG (cEnv env) e := by
  induction e with
  | leaf l => cases l with
    | win w => cases w <;> rfl
    | chal i => rfl
  | const k => rfl
  | add x y ihx ihy => simp only [render, ChalExpr.eval, evalG, ihx, ihy]
  | mul x y ihx ihy => simp only [render, ChalExpr.eval, evalG, ihx, ihy]

theorem eval_render_toTable (sv : Array ℤ) (env : TRowEnv) (e : GExpr TLeaf) :
    (render toTable e).evalWith sv env = evalG (tEnv sv env) e := by
  induction e with
  | leaf l => cases l with
    | win w => cases w <;> rfl
    | shr i => rfl
    | prep c => rfl
  | const k => rfl
  | add x y ihx ihy => simp only [render, TExpr.evalWith, evalG, ihx, ihy]
  | mul x y ihx ihy => simp only [render, TExpr.evalWith, evalG, ihx, ihy]

/-! ## §5 — ⚑ THE HEAD, ONCE — and `Head` / `WHead` pinned to it BY `rfl`.

`AirBuilder.Head` is `GHead VLeaf`. `AirNormalForm.WHead` is `GHead WLeaf`. The ~20 definitions
`AirNormalForm` §3 spends re-deriving the second from the first are one definition here, applied
twice. -/

/-- ⚑ **THE SUM-OF-PRODUCTS HEAD**: `Σ coeff · ∏ leaves + const`. -/
structure GHead (L : Type) where
  terms : List (ℤ × List L)
  const : ℤ
  deriving Repr

namespace GHead
variable {L : Type}

/-- The identically-zero head. -/
def zero : GHead L := ⟨[], 0⟩
/-- A pure constant head. -/
def c (k : ℤ) : GHead L := ⟨[], k⟩
/-- `coeff · leaf`. -/
def lin (coeff : ℤ) (l : L) : GHead L := ⟨[(coeff, [l])], 0⟩
/-- Append a linear term. -/
def addLin (h : GHead L) (coeff : ℤ) (l : L) : GHead L := ⟨h.terms ++ [(coeff, [l])], h.const⟩
/-- Append a product term. -/
def addProd (h : GHead L) (coeff : ℤ) (ls : List L) : GHead L := ⟨h.terms ++ [(coeff, ls)], h.const⟩
/-- Shift the constant. -/
def addConst (h : GHead L) (k : ℤ) : GHead L := ⟨h.terms, h.const + k⟩
/-- Scale the whole head. -/
def scale (h : GHead L) (k : ℤ) : GHead L := ⟨h.terms.map (fun t => (t.1 * k, t.2)), h.const * k⟩
/-- Sum two heads. -/
def append (h o : GHead L) : GHead L := ⟨h.terms ++ o.terms, h.const + o.const⟩

end GHead

/-- ⚑ The zero head is the default, at EVERY alphabet — declared once here rather than as a local
`instance : Inhabited Head` per rail (`AutomataflStepEmit` and `AutomataflResolveEmit` each carried
one for what is now the same type). -/
instance {L : Type} : Inhabited (GHead L) := ⟨GHead.zero⟩

/-- `AirBuilder.Head` as a `GHead`. -/
def ofHead (h : Dregg2.Circuit.Emit.AirBuilder.Head) : GHead VLeaf := ⟨h.terms, h.const⟩

/-- ⚑ `AirNormalForm.WHead` no longer exists as its own structure: it IS `GHead WLeaf`, aliased
there. That alias is the deletion this module exists to make possible. -/
abbrev WHead := GHead WLeaf

/-! ### §5a — the CANONICAL renderer, once.

This is `AirBuilder.headToExpr` / `AirNormalForm.wHeadToWindow` with the alphabet as a parameter:
every term carries its coefficient, a zero head-constant is elided, the spine is left-nested. -/

/-- The leaf product, left-nested. Empty renders `const 1` (unreachable from `gTermToExpr`). -/
def gVarsProd {L E : Type} (O : ExprOps L E) : List L → E
  | []        => O.const 1
  | l :: rest => rest.foldl (fun acc v => O.mul acc (O.leaf v)) (O.leaf l)

/-- One term. ⚑ The coefficient is ALWAYS written — the corpus normal form's load-bearing rule. -/
def gTermToExpr {L E : Type} (O : ExprOps L E) : ℤ × List L → E
  | (coeff, [])  => O.const coeff
  | (coeff, ls)  => O.mul (O.const coeff) (gVarsProd O ls)

/-- The summand list; a zero head-constant is elided, a zero-coefficient TERM is not. -/
def gHeadExprs {L E : Type} (O : ExprOps L E) (h : GHead L) : List E :=
  h.terms.map (gTermToExpr O) ++ (if h.const = 0 then [] else [O.const h.const])

/-- The left-nested sum; `[]` renders `const 0`. -/
def gFoldExprs {L E : Type} (O : ExprOps L E) : List E → E
  | []        => O.const 0
  | e :: rest => rest.foldl (fun acc x => O.add acc x) e

/-- ⚑ **THE CANONICAL RENDERER**, over any alphabet, into any view. -/
def gHeadToExpr {L E : Type} (O : ExprOps L E) (h : GHead L) : E :=
  gFoldExprs O (gHeadExprs O h)

/-! ### §5b — ⚑ THE PINS. Both existing renderers ARE this one, `by rfl`, over EVERY head.

This is the `rowGatesWith_pallas` obligation discharged for the collapse: the parameterised renderer
and each inherited one are the SAME emitted object, for every input, with no fixture anywhere. -/

/-! ### §5b — ⚑ THE HEAD'S DENOTATION, ONCE.

`AirBuilder.headToExpr_eval` and `AirNormalForm.wHeadToWindow_eval` are the same theorem twice — the
canonical rendering evaluates to the head's value. Here it is once, for every alphabet, with the
seven supporting fold lemmas each written once instead of twice. -/

/-- One term's value: `coeff · ∏ leaves`. -/
def gEvalTerm {L : Type} (ρ : L → ℤ) (t : ℤ × List L) : ℤ := t.1 * ((t.2.map ρ).prod)

/-- A head's value under a leaf environment. -/
def gEvalH {L : Type} (h : GHead L) (ρ : L → ℤ) : ℤ := (h.terms.map (gEvalTerm ρ)).sum + h.const

theorem gVarsProd_foldl {L : Type} (ρ : L → ℤ) (rest : List L) (e : GExpr L) :
    evalG ρ (rest.foldl (fun acc v => GExpr.mul acc (GExpr.leaf v)) e)
      = evalG ρ e * ((rest.map ρ).prod) := by
  induction rest generalizing e with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, evalG]; ring

theorem gVarsProd_eval {L : Type} (ρ : L → ℤ) (ls : List L) :
    evalG ρ (gVarsProd idOps ls) = ((ls.map ρ).prod) := by
  cases ls with
  | nil => simp [gVarsProd, evalG]
  | cons l rest =>
    show evalG ρ (rest.foldl (fun acc v => GExpr.mul acc (GExpr.leaf v)) (GExpr.leaf l)) = _
    rw [gVarsProd_foldl]; simp [evalG]

theorem gTermToExpr_eval {L : Type} (ρ : L → ℤ) (t : ℤ × List L) :
    evalG ρ (gTermToExpr idOps t) = gEvalTerm ρ t := by
  obtain ⟨k, ls⟩ := t
  cases ls with
  | nil => simp [gTermToExpr, gEvalTerm, evalG]
  | cons l rest => simp [gTermToExpr, gEvalTerm, evalG, gVarsProd_eval]

theorem gFoldExprs_foldl {L : Type} (ρ : L → ℤ) (rest : List (GExpr L)) (e : GExpr L) :
    evalG ρ (rest.foldl (fun acc x => GExpr.add acc x) e)
      = evalG ρ e + (rest.map (evalG ρ)).sum := by
  induction rest generalizing e with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, evalG]; ring

theorem gFoldExprs_eval {L : Type} (ρ : L → ℤ) (es : List (GExpr L)) :
    evalG ρ (gFoldExprs idOps es) = (es.map (evalG ρ)).sum := by
  cases es with
  | nil => simp [gFoldExprs, evalG]
  | cons e rest =>
    show evalG ρ (rest.foldl (fun acc x => GExpr.add acc x) e) = _
    rw [gFoldExprs_foldl]; simp

/-- ⚑ **THE HEAD BRIDGE, ONCE.** The canonical rendering evaluates to exactly the head's value — so
re-rendering any body into normal form cannot change what the constraint says, on any rail. -/
theorem gHeadToExpr_eval {L : Type} (ρ : L → ℤ) (h : GHead L) :
    evalG ρ (gHeadToExpr idOps h) = gEvalH h ρ := by
  simp only [gHeadToExpr, gFoldExprs_eval, gHeadExprs, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, gEvalH]
  by_cases hc : h.const = 0
  · simp [hc, gTermToExpr_eval]
  · simp [hc, gTermToExpr_eval, evalG]

/-! ### §5b — ⚑ THE PINS on the `EmittedExpr` rail. `AirBuilder`'s renderer IS this one.

`AirNormalForm`'s window rail is pinned in that file, where it is now the instantiation rather than
a twin. -/

theorem gVarsProd_emitted (cols : List VLeaf) :
    gVarsProd toEmitted cols = Dregg2.Circuit.Emit.AirBuilder.varsProd cols := by
  cases cols <;> rfl

/-- The per-term rendering agrees AS A FUNCTION — what the `List.map` inside `gHeadExprs` needs.
⚠ This is the one step that is not `rfl`: `Eq.refl` cannot see through `List.map f` when the term
list is a variable, because that needs `f` and `g` definitionally equal *as functions* and the two
compiled matchers are distinct constants. A Lean elaboration limit, not a gap in the collapse —
every ARM is `rfl`, and every pin over a CLOSED emitted object is `rfl`. -/
theorem gTermToExpr_emitted :
    gTermToExpr toEmitted = Dregg2.Circuit.Emit.AirBuilder.termToExpr := by
  funext t; obtain ⟨k, ls⟩ := t; cases ls <;> rfl

theorem gFoldExprs_emitted (es : List EmittedExpr) :
    gFoldExprs toEmitted es = Dregg2.Circuit.Emit.AirBuilder.foldExprs es := by
  cases es <;> rfl

theorem gHeadExprs_emitted (h : Dregg2.Circuit.Emit.AirBuilder.Head) :
    gHeadExprs toEmitted (ofHead h) = Dregg2.Circuit.Emit.AirBuilder.headExprs h := by
  simp only [gHeadExprs, Dregg2.Circuit.Emit.AirBuilder.headExprs, ofHead, gTermToExpr_emitted]
  congr

/-- ⚑ **`AirBuilder.headToExpr` IS `gHeadToExpr toEmitted`** — for EVERY head, no fixture. -/
theorem gHeadToExpr_emitted (h : Dregg2.Circuit.Emit.AirBuilder.Head) :
    gHeadToExpr toEmitted (ofHead h) = Dregg2.Circuit.Emit.AirBuilder.headToExpr h := by
  show gFoldExprs toEmitted (gHeadExprs toEmitted (ofHead h))
    = Dregg2.Circuit.Emit.AirBuilder.foldExprs (Dregg2.Circuit.Emit.AirBuilder.headExprs h)
  rw [gHeadExprs_emitted, gFoldExprs_emitted]

/-- ⚑ **`AirBuilder.gBin` is the alphabet gate at `[0,1]`** — every column, `rfl`. -/
theorem gBin_is_gBool (co : Nat) :
    Dregg2.Circuit.Emit.AirBuilder.gBin co
      = render toEmitted (GExpr.mul (.leaf co) (.add (.leaf co) (.const (-1)))) := rfl

/-! ### §5b‴ — ⚑ THE TACTIC THAT REPLACED `rfl` AT THE PINNED CALL SITES.

Every consumer that pinned a CLOSED head's rendering (`(headToExpr H).eval a = <polynomial>`) did it
`by rfl`, and `rfl` worked only because the ELIDED renderer wrote a unit-coefficient term bare: the
canonical renderer writes `mul(const 1, x)`, whose `eval` is `1 * a x`, and `1 * x` is NOT
definitionally `x` for a symbolic `x`. So the flag day of 2026-08-06 broke ~250 `rfl`s that were
never about the arithmetic — they were about the RENDERING.

`canon_head_eval` re-proves them SEMANTICALLY: `simp +ground` evaluates the closed rendering (the
head, its column indices and the whole `EmittedExpr` tree are ground), and `ring` closes the
resulting polynomial identity. That is strictly better than what it replaced — a site proved this way
does not care which of the two renderings is in force, so the next rendering change moves bytes
without touching a proof. -/

/-- ⚑ Discharge `(r H).eval a = <polynomial>` for the rail's own renderer `r` (`headToExpr`).
`+ground` EVALUATES the ground subterms, which is what a head built by a `List.foldl` over a
`List.range n` needs before its term list is visible at all. -/
macro "canon_head_eval" "[" rs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp +ground (maxSteps := 40000000) [$rs,*, Dregg2.Circuit.GateExpr.gHeadToExpr, Dregg2.Circuit.GateExpr.gHeadExprs,
      Dregg2.Circuit.GateExpr.gFoldExprs, Dregg2.Circuit.GateExpr.gTermToExpr,
      Dregg2.Circuit.GateExpr.gVarsProd, Dregg2.Circuit.GateExpr.GHead.zero,
      Dregg2.Circuit.GateExpr.GHead.c, Dregg2.Circuit.GateExpr.GHead.lin,
      Dregg2.Circuit.GateExpr.GHead.addLin, Dregg2.Circuit.GateExpr.GHead.addProd,
      Dregg2.Circuit.GateExpr.GHead.addConst, Dregg2.Circuit.GateExpr.GHead.scale,
      Dregg2.Circuit.GateExpr.GHead.append,
      Dregg2.Exec.CircuitEmit.EmittedExpr.eval] <;> ring)

/-- ⚑ The SAME reduction without ground evaluation — for the rails whose column functions are
defined through a thirty-deep offset chain (`AutomataflResolveEmit`'s `cFork`, `cEqBit`, …). Ground-
evaluating those blows simp's step budget, and it is not needed: the head is a chain of
`Head.lin`/`addLin`/`addProd`, so the builder unfoldings alone expose its term list. -/
macro "canon_head_eval_plain" "[" rs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (maxSteps := 4000000) [$rs,*, Dregg2.Circuit.GateExpr.gHeadToExpr, Dregg2.Circuit.GateExpr.gHeadExprs,
      Dregg2.Circuit.GateExpr.gFoldExprs, Dregg2.Circuit.GateExpr.gTermToExpr,
      Dregg2.Circuit.GateExpr.gVarsProd, Dregg2.Circuit.GateExpr.GHead.zero,
      Dregg2.Circuit.GateExpr.GHead.c, Dregg2.Circuit.GateExpr.GHead.lin,
      Dregg2.Circuit.GateExpr.GHead.addLin, Dregg2.Circuit.GateExpr.GHead.addProd,
      Dregg2.Circuit.GateExpr.GHead.addConst, Dregg2.Circuit.GateExpr.GHead.scale,
      Dregg2.Circuit.GateExpr.GHead.append,
      Dregg2.Exec.CircuitEmit.EmittedExpr.eval] <;> ring)

/-- ⚑ The FULLY CLOSED variant: `+ground` alone reduces the rendering, and `only` — with the head
BUILDERS deliberately absent from the set — keeps `simp` off the emitted polynomial. That matters at
exactly two sites: the 20-bit score-comparison heads diverge past forty million rewrite steps under
either of the other two forms, and close in seconds under this one. -/
macro "canon_head_eval_closed" "[" rs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp +ground (maxSteps := 8000000) only [$rs,*,
      Dregg2.Circuit.GateExpr.gHeadToExpr, Dregg2.Circuit.GateExpr.gHeadExprs,
      Dregg2.Circuit.GateExpr.gFoldExprs, Dregg2.Circuit.GateExpr.gTermToExpr,
      Dregg2.Circuit.GateExpr.gVarsProd,
      Dregg2.Exec.CircuitEmit.EmittedExpr.eval] <;> ring)

/-- ⚑ The reduction AT A HYPOTHESIS — for the extraction sites that read a gate's satisfaction out of
a membership proof rather than pinning the emitted body as a literal. -/
macro "canon_head_at" h:ident "[" rs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp +ground (maxSteps := 40000000) [$rs,*, Dregg2.Circuit.GateExpr.gHeadToExpr, Dregg2.Circuit.GateExpr.gHeadExprs,
      Dregg2.Circuit.GateExpr.gFoldExprs, Dregg2.Circuit.GateExpr.gTermToExpr,
      Dregg2.Circuit.GateExpr.gVarsProd, Dregg2.Circuit.GateExpr.GHead.zero,
      Dregg2.Circuit.GateExpr.GHead.c, Dregg2.Circuit.GateExpr.GHead.lin,
      Dregg2.Circuit.GateExpr.GHead.addLin, Dregg2.Circuit.GateExpr.GHead.addProd,
      Dregg2.Circuit.GateExpr.GHead.addConst, Dregg2.Circuit.GateExpr.GHead.scale,
      Dregg2.Circuit.GateExpr.GHead.append,
      Dregg2.Exec.CircuitEmit.EmittedExpr.eval] at $h:ident)

/-! ### §5b′ — ⚑ THE FUSION LAW: rendering the head is rendering the rendered head.

This is what lets a target rail be a one-line `def` instead of a re-derivation: everything proved
about `gHeadToExpr idOps` (normality, denotation) transfers to EVERY view for free. -/

theorem render_gVarsProd {L E : Type} (O : ExprOps L E) (ls : List L) :
    render O (gVarsProd idOps ls) = gVarsProd O ls := by
  cases ls with
  | nil => rfl
  | cons l rest =>
    show render O (rest.foldl (fun acc v => GExpr.mul acc (GExpr.leaf v)) (GExpr.leaf l))
      = rest.foldl (fun acc v => O.mul acc (O.leaf v)) (O.leaf l)
    suffices h : ∀ (rs : List L) (e : GExpr L),
        render O (rs.foldl (fun acc v => GExpr.mul acc (GExpr.leaf v)) e)
          = rs.foldl (fun acc v => O.mul acc (O.leaf v)) (render O e) by
      exact h rest (.leaf l)
    intro rs
    induction rs with
    | nil => intro e; rfl
    | cons x xs ih => intro e; simpa [render] using ih (GExpr.mul e (GExpr.leaf x))

theorem render_gTermToExpr {L E : Type} (O : ExprOps L E) (t : ℤ × List L) :
    render O (gTermToExpr idOps t) = gTermToExpr O t := by
  obtain ⟨k, ls⟩ := t
  cases ls with
  | nil => rfl
  | cons l rest =>
    show O.mul (O.const k) (render O (gVarsProd idOps (l :: rest)))
      = O.mul (O.const k) (gVarsProd O (l :: rest))
    rw [render_gVarsProd]

theorem render_gHeadExprs {L E : Type} (O : ExprOps L E) (h : GHead L) :
    (gHeadExprs idOps h).map (render O) = gHeadExprs O h := by
  simp only [gHeadExprs, List.map_append, List.map_map, Function.comp_def, render_gTermToExpr]
  by_cases hc : h.const = 0 <;> simp [hc, render]

theorem render_gFoldExprs {L E : Type} (O : ExprOps L E) (es : List (GExpr L)) :
    render O (gFoldExprs idOps es) = gFoldExprs O (es.map (render O)) := by
  cases es with
  | nil => rfl
  | cons e rest =>
    show render O (rest.foldl (fun acc x => GExpr.add acc x) e)
      = (rest.map (render O)).foldl (fun acc x => O.add acc x) (render O e)
    suffices h : ∀ (rs : List (GExpr L)) (a : GExpr L),
        render O (rs.foldl (fun acc x => GExpr.add acc x) a)
          = (rs.map (render O)).foldl (fun acc x => O.add acc x) (render O a) by
      exact h rest e
    intro rs
    induction rs with
    | nil => intro a; rfl
    | cons x xs ih => intro a; simpa [render] using ih (GExpr.add a x)

/-- ⚑ **THE FUSION LAW.** Rendering a head directly into a view is rendering it into the one AST and
then viewing — so every rail's canonical renderer is `gHeadToExpr` and inherits its proofs. -/
theorem render_gHeadToExpr {L E : Type} (O : ExprOps L E) (h : GHead L) :
    render O (gHeadToExpr idOps h) = gHeadToExpr O h := by
  simp only [gHeadToExpr, render_gFoldExprs, render_gHeadExprs]

/-! ### §5b″ — the reverse roundtrips, so a view's PREDICATE is the one AST's predicate. -/

theorem ofEmitted_render (e : GExpr VLeaf) : ofEmitted (render toEmitted e) = e := by
  induction e with
  | leaf l => rfl
  | const k => rfl
  | add a b iha ihb => simp only [render, ofEmitted, iha, ihb]
  | mul a b iha ihb => simp only [render, ofEmitted, iha, ihb]

theorem ofWindow_render (e : GExpr WLeaf) : ofWindow (render toWindow e) = e := by
  induction e with
  | leaf l => cases l <;> rfl
  | const k => rfl
  | add a b iha ihb => simp only [render, ofWindow, iha, ihb]
  | mul a b iha ihb => simp only [render, ofWindow, iha, ihb]

theorem ofChal_render (e : GExpr CLeaf) : ofChal (render toChal e) = e := by
  induction e with
  | leaf l => cases l with
    | win w => cases w <;> rfl
    | chal i => rfl
  | const k => rfl
  | add a b iha ihb => simp only [render, ofChal, iha, ihb]
  | mul a b iha ihb => simp only [render, ofChal, iha, ihb]

theorem ofTable_render (e : GExpr TLeaf) : ofTable (render toTable e) = e := by
  induction e with
  | leaf l => cases l with
    | win w => cases w <;> rfl
    | shr i => rfl
    | prep c => rfl
  | const k => rfl
  | add a b iha ihb => simp only [render, ofTable, iha, ihb]
  | mul a b iha ihb => simp only [render, ofTable, iha, ihb]

/-! ### §5c — ⚑ THE LEGACY RENDERER, AND WHY THE HOISTED VOCABULARY WAS NEVER ADOPTED.

`AutomataflStepEmit.headToExpr` and `AutomataflResolveEmit.headToExpr` elide a unit coefficient and
drop zero-coefficient terms. That is a DIFFERENT function, not a different spelling, and it is named
here so the divergence is a fact rather than a footnote in a docblock. -/

/-- One term with the coefficient `1` ELIDED — the automatafl rendering. -/
def gTermToExprElide {L E : Type} (O : ExprOps L E) : ℤ × List L → E
  | (coeff, [])  => O.const coeff
  | (coeff, ls)  => if coeff == 1 then gVarsProd O ls else O.mul (O.const coeff) (gVarsProd O ls)

/-- ⚑ **THE LEGACY RENDERER** — unit coefficients elided, zero-coefficient terms dropped. -/
def gHeadToExprElide {L E : Type} (O : ExprOps L E) (h : GHead L) : E :=
  let ts := (h.terms.filter (fun t => t.1 != 0)).map (gTermToExprElide O)
  let ts := if h.const == 0 then ts else ts ++ [O.const h.const]
  match ts with
  | []        => O.const 0
  | e :: rest => rest.foldl (fun acc x => O.add acc x) e

/-- The head both renderers are read on: the single term `1 · x₀`. -/
def unitHead : GHead VLeaf := ⟨[(1, [0])], 0⟩

/-- ⚑ **THE TWO RENDERERS DISAGREE ON THE BYTES.** `AirBuilder` writes `mul(const 1, var 0)`; the
automatafl copies write bare `var 0`. Adopting the hoisted vocabulary in those two files is therefore
a RE-EMIT, which is what the `AirBuilder` docblock's "mechanical, separately-verifiable change"
framing missed — and very probably why the migration never happened. -/
theorem canonical_ne_elide :
    gHeadToExpr toEmitted unitHead ≠ gHeadToExprElide toEmitted unitHead := by decide

/-! ## §6 — ⚑ THE NORMAL FORM, ONCE.

`isNormal`/`isVarProd`/`isTermAtom` and `isNormalW`/`isVarProdW`/`isTermAtomW` are one predicate at
two alphabets. Deciding a leaf is the only per-AST content, so it is the parameter. -/

/-- A LEAF PRODUCT: a left-nested `mul` chain of leaves. -/
def gIsVarProd {L : Type} : GExpr L → Bool
  | .leaf _  => true
  | .mul a b => gIsVarProd a && (match b with | .leaf _ => true | _ => false)
  | _        => false

/-- A TERM ATOM: `mul(const c, prod)` — ⚑ including `c = 1` — or a bare constant. -/
def gIsTermAtom {L : Type} : GExpr L → Bool
  | .const _ => true
  | .mul a b => (match a with | .const _ => true | _ => false) && gIsVarProd b
  | _        => false

/-- ⚑ **THE NORMAL FORM**: a left-nested `add` spine of term atoms. -/
def gIsNormal {L : Type} : GExpr L → Bool
  | .add l r => gIsNormal l && gIsTermAtom r
  | e        => gIsTermAtom e

/-- ⚑ **THE DIVERGENCE HAS A DIRECTION.** The canonical rendering is the one the corpus normal form
accepts; the legacy automatafl rendering is outside it BY CONSTRUCTION, on the most ordinary head
there is. Every descriptor rendered through those two copies is in the non-canonical 88 of 111. -/
theorem canonical_is_normal : gIsNormal (gHeadToExpr idOps unitHead) = true := by decide

theorem elide_is_not_normal : gIsNormal (gHeadToExprElide idOps unitHead) = false := by decide

/-! ### §6b — the canonical renderer is normal BY CONSTRUCTION, once, for every alphabet.

`headToExpr_isNormal` and `wHeadToWindow_isNormalW` are two proofs of this one statement. -/

theorem gIsVarProd_gVarsProd {L : Type} (l : L) (rest : List L) :
    gIsVarProd (gVarsProd (idOps (L := L)) (l :: rest)) = true := by
  show gIsVarProd (rest.foldl (fun acc v => GExpr.mul acc (GExpr.leaf v)) (GExpr.leaf l)) = true
  suffices h : ∀ (rs : List L) (e : GExpr L), gIsVarProd e = true →
      gIsVarProd (rs.foldl (fun acc v => GExpr.mul acc (GExpr.leaf v)) e) = true by
    exact h rest (.leaf l) rfl
  intro rs
  induction rs with
  | nil => intro e he; simpa using he
  | cons x xs ih => intro e he; exact ih _ (by simp [gIsVarProd, he])

theorem gIsTermAtom_gTermToExpr {L : Type} (t : ℤ × List L) :
    gIsTermAtom (gTermToExpr (idOps (L := L)) t) = true := by
  obtain ⟨k, ls⟩ := t
  cases ls with
  | nil => rfl
  | cons x xs => simpa [gTermToExpr, gIsTermAtom, idOps] using gIsVarProd_gVarsProd x xs

theorem gIsNormal_gFoldExprs {L : Type} (es : List (GExpr L))
    (h : ∀ e ∈ es, gIsTermAtom e = true) :
    gIsNormal (gFoldExprs (idOps (L := L)) es) = true := by
  cases es with
  | nil => rfl
  | cons e rest =>
    have hbase : gIsNormal e = true := by
      have := h e List.mem_cons_self
      cases e <;> simp_all [gIsNormal, gIsTermAtom]
    show gIsNormal (rest.foldl (fun acc x => GExpr.add acc x) e) = true
    suffices hh : ∀ (xs : List (GExpr L)), (∀ x ∈ xs, gIsTermAtom x = true) →
        ∀ acc, gIsNormal acc = true →
          gIsNormal (xs.foldl (fun a x => GExpr.add a x) acc) = true by
      exact hh rest (fun x hx => h x (List.mem_cons_of_mem _ hx)) e hbase
    intro xs
    induction xs with
    | nil => intro _ acc hacc; simpa using hacc
    | cons y ys ih =>
      intro hys acc hacc
      exact ih (fun x hx => hys x (List.mem_cons_of_mem _ hx)) _
        (by simp [gIsNormal, hacc, hys y List.mem_cons_self])

/-- ⚑ **THE CANONICAL RENDERER IS NORMAL — every head, every alphabet, ONE proof.** -/
theorem gHeadToExpr_gIsNormal {L : Type} (h : GHead L) :
    gIsNormal (gHeadToExpr (idOps (L := L)) h) = true := by
  refine gIsNormal_gFoldExprs _ (fun e he => ?_)
  simp only [gHeadExprs, List.mem_append, List.mem_map] at he
  rcases he with ⟨t, _, ht⟩ | he
  · exact ht ▸ gIsTermAtom_gTermToExpr t
  · by_cases hc : h.const = 0 <;> simp [hc] at he
    · exact he ▸ rfl

/-! ### §6c — ⚑ THE NORMALIZER: an ARBITRARY body INTO the normal form, at every alphabet.

§6b says the canonical renderer's OUTPUT is normal. That is a fact about bodies the compiler BUILT
from a head, and it says nothing about a body that was hand-shaped before there was a compiler —
which is most of the corpus. `scripts/measure-descriptor-normal-form.py` reads **23 of 113**
checked-in descriptors in the normal form, 18,290 of 41,264 arithmetic bodies outside it.

What closes that is not a per-descriptor re-authoring. It is the renderer's INVERSE: read any body
back into a head, then render that head canonically. `EffectLower.exprToHead` has been exactly this
function at the `VLeaf` alphabet since the first rail fusion — used only on the SOURCE side, where
the input was already a compiler input. Here it is at EVERY alphabet, which is what lets the WINDOW
rail (whose bodies had no reader at all, only a builder) be canonicalized too.

## ⚑ ONE PASS — but the two EFFECTS are separable, and an earlier draft of this docblock said
they were not. The correction is the useful part.

`gCanon` does both jobs in one traversal, and that much is structural: a head is
`Σ coeff · ∏ leaves + const`, `gMulHead` multiplies two heads, and a product of two literal
constants is a head with an EMPTY term list — so the 5,075 `mul(const, const)` subtrees the corpus
ships (4,284 of them the `mul(const -1, const 1)` a subtraction of one lowers to) cannot survive
`gExprToHead`, because the head vocabulary cannot represent them.

⚠ **That is a fact about THIS pass's vocabulary, not about what is possible, and the first draft
here read it as the latter** ("there is no deletion step to schedule"). Measured at HEAD
2026-08-06, the two effects are ORTHOGONAL axes:

```text
                              nodes    descriptors moving    bodies normal
  a 4-case structural fold   −10,460         26 / 113      22,829 → 22,829  (+0)
  gCanon (this pass)        +179,476         90 / 113      22,829 → 41,264
```

A fold that does not round-trip through a head deletes every dead subtree, SHRINKS the corpus, and
buys **exactly zero** normality; `gCanon` buys all the normality and pays for it. Neither is the
other's phase. Anyone choosing between them should see both columns — which is why they are
written here rather than argued about.

## ⚠ What it costs, measured rather than estimated

Rendering every term with its coefficient is more bytes than eliding the unit ones. Over the 113
checked-in descriptors the whole pass is **1,954,732 → 2,142,886 AST nodes, +188,154 (+9.63%)**,
and it is bytes only: `gCanon_eval` says the polynomial is untouched, and the Rust interpreter's
`LeanExpr::degree` sends `mul(const 1, x)` to degree 1 exactly as bare `x`, so no FRI or VK
geometry moves. `AirNormalForm`'s header argues why that trade is the right one.

## ⚠ …and the one thing it DOES remove from a body

`gExprToHead` never emits a zero-coefficient term (`gExprToHead_coeff_ne_zero`), so a source
`0 · x` does not come back. `AirNormalForm` rule 3 forbids the RENDERER from eliding a
zero-coefficient term the head carries, and `gHeadExprs` still does not — but the normalizer
declines to build one, which is the same guard `mulHead` has carried since the Phase-3 re-emission
and is why `gCanon` is idempotent at all. -/

/-- Multiply two heads: distribute term × term, then each side's terms against the other's
constant, then the constant product. ⚑ `EffectLower.mulHead` at every alphabet, guards and all —
the constant cross-products are dropped when that constant is `0`. `gEvalH_gMulHead` is
UNCONDITIONAL: the dropped branches are exactly the ones whose value is `0`. -/
def gMulHead {L : Type} (h o : GHead L) : GHead L :=
  { terms := (h.terms.flatMap fun t => o.terms.map fun u => ((t.1 * u.1, t.2 ++ u.2) : ℤ × List L))
             ++ (if o.const = 0 then []
                 else h.terms.map fun t => ((t.1 * o.const, t.2) : ℤ × List L))
             ++ (if h.const = 0 then []
                 else o.terms.map fun u => ((h.const * u.1, u.2) : ℤ × List L))
  , const := h.const * o.const }

/-- ⚑ **THE NORMALIZER** — any gate AST into the sum-of-products head, at any alphabet. -/
def gExprToHead {L : Type} : GExpr L → GHead L
  | .leaf l  => GHead.lin 1 l
  | .const k => GHead.c k
  | .add a b => (gExprToHead a).append (gExprToHead b)
  | .mul a b => gMulHead (gExprToHead a) (gExprToHead b)

private theorem gsum_scaleR {L : Type} (ρ : L → ℤ) (k : ℤ) (ts : List (ℤ × List L)) :
    ((ts.map fun t => ((t.1 * k, t.2) : ℤ × List L)).map (gEvalTerm ρ)).sum
      = (ts.map (gEvalTerm ρ)).sum * k := by
  induction ts with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, gEvalTerm]; ring

private theorem gsum_scaleL {L : Type} (ρ : L → ℤ) (k : ℤ) (ts : List (ℤ × List L)) :
    ((ts.map fun t => ((k * t.1, t.2) : ℤ × List L)).map (gEvalTerm ρ)).sum
      = k * (ts.map (gEvalTerm ρ)).sum := by
  induction ts with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, gEvalTerm]; ring

private theorem gsum_crossOne {L : Type} (ρ : L → ℤ) (x : ℤ × List L) (us : List (ℤ × List L)) :
    ((us.map fun u => ((x.1 * u.1, x.2 ++ u.2) : ℤ × List L)).map (gEvalTerm ρ)).sum
      = gEvalTerm ρ x * (us.map (gEvalTerm ρ)).sum := by
  induction us with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, ih, gEvalTerm, List.map_append, List.prod_append]
    ring

private theorem gsum_cross {L : Type} (ρ : L → ℤ) (ts us : List (ℤ × List L)) :
    ((ts.flatMap fun t =>
        us.map fun u => ((t.1 * u.1, t.2 ++ u.2) : ℤ × List L)).map (gEvalTerm ρ)).sum
      = (ts.map (gEvalTerm ρ)).sum * (us.map (gEvalTerm ρ)).sum := by
  induction ts with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, gsum_crossOne,
      List.map_cons, List.sum_cons]
    ring

private theorem gsum_scaleR_guard {L : Type} (ρ : L → ℤ) (k : ℤ) (ts : List (ℤ × List L)) :
    (((if k = 0 then ([] : List (ℤ × List L))
        else ts.map fun t => ((t.1 * k, t.2) : ℤ × List L))).map (gEvalTerm ρ)).sum
      = (ts.map (gEvalTerm ρ)).sum * k := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk, gsum_scaleR]

private theorem gsum_scaleL_guard {L : Type} (ρ : L → ℤ) (k : ℤ) (ts : List (ℤ × List L)) :
    (((if k = 0 then ([] : List (ℤ × List L))
        else ts.map fun u => ((k * u.1, u.2) : ℤ × List L))).map (gEvalTerm ρ)).sum
      = k * (ts.map (gEvalTerm ρ)).sum := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk, gsum_scaleL]

/-- The multiplication bridge, at every alphabet. UNCONDITIONAL. -/
theorem gEvalH_gMulHead {L : Type} (ρ : L → ℤ) (h o : GHead L) :
    gEvalH (gMulHead h o) ρ = gEvalH h ρ * gEvalH o ρ := by
  simp only [gEvalH, gMulHead, List.map_append, List.sum_append, gsum_cross,
    gsum_scaleR_guard, gsum_scaleL_guard]
  ring

theorem gEvalH_append {L : Type} (ρ : L → ℤ) (h o : GHead L) :
    gEvalH (h.append o) ρ = gEvalH h ρ + gEvalH o ρ := by
  simp only [gEvalH, GHead.append, List.map_append, List.sum_append]; ring

/-- ⚑ **THE NORMALIZER IS MEANING-PRESERVING**, at every alphabet — so reading a hand-shaped body
back into a head cannot change what the gate says. -/
theorem gEvalH_gExprToHead {L : Type} (ρ : L → ℤ) (e : GExpr L) :
    gEvalH (gExprToHead e) ρ = evalG ρ e := by
  induction e with
  | leaf l => simp [gExprToHead, GHead.lin, gEvalH, gEvalTerm, evalG]
  | const k => simp [gExprToHead, GHead.c, gEvalH, evalG]
  | add a b iha ihb => simp [gExprToHead, evalG, gEvalH_append, iha, ihb]
  | mul a b iha ihb => simp [gExprToHead, evalG, gEvalH_gMulHead, iha, ihb]

/-- ⚑ **THE CANONICALIZER.** Read the body into a head, render the head canonically. This is the
whole pass, and both of its halves already existed — what did not exist was their composition at an
alphabet the window rail could use. -/
def gCanon {L : Type} (e : GExpr L) : GExpr L := gHeadToExpr idOps (gExprToHead e)

/-- ⚑ **THE END STATE, AS A THEOREM RATHER THAN A COUNT.** Every body, on every rail, is in the
canonical normal form after one pass — not 113 of 113 descriptors measured, but every expression
there is. -/
theorem gCanon_gIsNormal {L : Type} (e : GExpr L) : gIsNormal (gCanon e) = true :=
  gHeadToExpr_gIsNormal _

/-- ⚑ **AND IT SAYS THE SAME THING.** The canonicalized body evaluates to exactly what the original
did, under every leaf environment — so the flag day moves bytes and nothing else. -/
theorem gCanon_eval {L : Type} (ρ : L → ℤ) (e : GExpr L) : evalG ρ (gCanon e) = evalG ρ e := by
  rw [gCanon, gHeadToExpr_eval, gEvalH_gExprToHead]

/-- ⚑ **THE NORMALIZER NEVER BUILDS A ZERO-COEFFICIENT TERM.** This is the structural reason
`gCanon` cannot silently drop a column reference on a SECOND pass: there is no `mul(const 0, …)` in
its output for a second pass to guard away. Note where the zero cases go instead — a zero constant
sends the whole product to the EMPTY head, which is the folding above, not an elision. -/
theorem gExprToHead_coeff_ne_zero {L : Type} (e : GExpr L) :
    ∀ t ∈ (gExprToHead e).terms, t.1 ≠ 0 := by
  induction e with
  | leaf l => intro t ht; simp [gExprToHead, GHead.lin] at ht; simp [ht]
  | const k => intro t ht; simp [gExprToHead, GHead.c] at ht
  | add a b iha ihb =>
    intro t ht
    simp only [gExprToHead, GHead.append, List.mem_append] at ht
    rcases ht with h | h
    · exact iha t h
    · exact ihb t h
  | mul a b iha ihb =>
    intro t ht
    simp only [gExprToHead, gMulHead, List.mem_append, List.mem_flatMap, List.mem_map] at ht
    -- ⚠ `++` is `infixl`, so the three-way union is LEFT-nested: `(cross ++ right) ++ left`.
    rcases ht with (⟨u, hu, v, hv, huv⟩ | h) | h
    · exact huv ▸ mul_ne_zero (iha u hu) (ihb v hv)
    · split at h
      · exact absurd h (by simp)
      · rename_i hc
        obtain ⟨u, hu, hut⟩ := List.mem_map.mp h
        exact hut ▸ mul_ne_zero (iha u hu) hc
    · split at h
      · exact absurd h (by simp)
      · rename_i hc
        obtain ⟨u, hu, hut⟩ := List.mem_map.mp h
        exact hut ▸ mul_ne_zero hc (ihb u hu)

/-! ### §6c′ — ⚑ THE FOLD: the OTHER axis of §6c's table, as a pass.

§6c prices two passes and says they are orthogonal. `gCanon` is one of them and has been on disk
since the rail fusion. This is the other one, and until now it existed only as a row in a table.

`gFold` deletes the dead subtrees and buys **exactly zero** normality. That is not a hedge, it is
the measurement: at git HEAD `db577c93dc71d40dbab5326aec5876885dba3404`, over the 122 checked-in
`by-name` descriptors, the pass takes **1,958,542 → 1,948,364 AST nodes (−10,178)** across **26 of
122** descriptors, and the normality reading does not move at all — **22,976 → 22,976** normal
bodies, **23 / 122 → 23 / 122** normal descriptors. Anyone who reads this pass as a step toward
`isNormal` is reading the wrong column of §6c's table.

⚠ **Quote those figures with that revision.** §6c's own header records the same total read three
different ways in four hours because sibling lanes re-emit continuously; this reading is pinned to
one commit and `scripts/measure-descriptor-normal-form.py --fold` re-derives it.

## ⚑ What it is FOR, since it is not normality

Two things, and they are the two the corpus actually wanted.

1. **It makes the artifact SMALLER.** All 26 moving descriptors SHRINK — there is no sign question
   here, unlike `gCanon`, where 76 grow and 14 shrink. `gFold_nodeCount_le` (§7.1d) is that as a
   theorem over every expression rather than a count over these ones.
2. **It ships zero dead subtrees**, which `gFold_no_dead` states for every expression at every
   alphabet. The corpus ships 5,075 `mul(const, const)` subtrees in `by-name`, 4,284 of them the
   `mul(const -1, const 1)` a subtraction of one lowers to — a literal times a literal, carried all
   the way into a signed artifact and re-multiplied by the verifier on every row.

## ⚑ And what it does NOT disturb

`gFold` does not go through a head. It never touches `gExprToHead`, `gHeadToExpr` or `gCanon`, so
no preservation theorem in §5 or §6 is restated, weakened or re-proved on its account. `gCanon`
remains exactly as it was — the byte-reachability option, for whenever the 90 rotations are worth
paying. These two passes compose in either order and neither is the other's phase. -/

/-- The `add` node's fold: a sum of two literals IS a literal. Split out from `gFold` so the
bridge below is a 4×4 case analysis closed by `rfl` rather than a match inside an induction. -/
def gFoldAdd {L : Type} : GExpr L → GExpr L → GExpr L
  | .const x, .const y => .const (x + y)
  | a, b => .add a b

/-- The `mul` node's fold — the one that deletes `mul(const -1, const 1)`. -/
def gFoldMul {L : Type} : GExpr L → GExpr L → GExpr L
  | .const x, .const y => .const (x * y)
  | a, b => .mul a b

theorem gFoldAdd_eval {L : Type} (ρ : L → ℤ) (a b : GExpr L) :
    evalG ρ (gFoldAdd a b) = evalG ρ a + evalG ρ b := by
  cases a <;> cases b <;> rfl

theorem gFoldMul_eval {L : Type} (ρ : L → ℤ) (a b : GExpr L) :
    evalG ρ (gFoldMul a b) = evalG ρ a * evalG ρ b := by
  cases a <;> cases b <;> rfl

/-- ⚑ **THE CONSTANT FOLD** — four cases, no head, every alphabet. A leaf and a literal are fixed
points; a sum or product whose folded operands are both literals becomes the literal. -/
def gFold {L : Type} : GExpr L → GExpr L
  | .leaf l  => .leaf l
  | .const k => .const k
  | .add a b => gFoldAdd (gFold a) (gFold b)
  | .mul a b => gFoldMul (gFold a) (gFold b)

/-- ⚑ **THE FOLD SAYS THE SAME THING** — under every leaf environment, at every alphabet. This is
the whole licence for the re-emission: the polynomial each gate asserts is untouched, so the bytes
move and nothing else does. -/
theorem gFold_eval {L : Type} (ρ : L → ℤ) (e : GExpr L) : evalG ρ (gFold e) = evalG ρ e := by
  induction e with
  | leaf l => rfl
  | const k => rfl
  | add a b iha ihb => simp only [gFold, gFoldAdd_eval, iha, ihb, evalG]
  | mul a b iha ihb => simp only [gFold, gFoldMul_eval, iha, ihb, evalG]

/-- A `mul` whose BOTH operands are literals — the dead subtree, as a decidable predicate on one
node. -/
def gIsDeadProduct {L : Type} : GExpr L → Bool
  | .mul (.const _) (.const _) => true
  | _ => false

/-- Does any subtree multiply two literals? This is the thing the corpus ships 5,075 times. -/
def gHasDead {L : Type} : GExpr L → Bool
  | .leaf _  => false
  | .const _ => false
  | .add a b => gHasDead a || gHasDead b
  | .mul a b => gIsDeadProduct (GExpr.mul a b) || gHasDead a || gHasDead b

theorem gFoldAdd_no_dead {L : Type} (a b : GExpr L)
    (ha : gHasDead a = false) (hb : gHasDead b = false) : gHasDead (gFoldAdd a b) = false := by
  cases a <;> cases b <;> simp_all [gFoldAdd, gHasDead, gIsDeadProduct]

theorem gFoldMul_no_dead {L : Type} (a b : GExpr L)
    (ha : gHasDead a = false) (hb : gHasDead b = false) : gHasDead (gFoldMul a b) = false := by
  cases a <;> cases b <;> simp_all [gFoldMul, gHasDead, gIsDeadProduct]

/-- ⚑ **ZERO DEAD SUBTREES SHIP** — for EVERY expression at every alphabet, not 5,075 counted in
one corpus at one revision. This is the pass's actual product, stated where it cannot go stale. -/
theorem gFold_no_dead {L : Type} (e : GExpr L) : gHasDead (gFold e) = false := by
  induction e with
  | leaf l => rfl
  | const k => rfl
  | add a b iha ihb => exact gFoldAdd_no_dead _ _ iha ihb
  | mul a b iha ihb => exact gFoldMul_no_dead _ _ iha ihb

theorem gFold_gFoldAdd {L : Type} (a b : GExpr L) (ha : gFold a = a) (hb : gFold b = b) :
    gFold (gFoldAdd a b) = gFoldAdd a b := by
  cases a <;> cases b <;> simp_all [gFoldAdd, gFold]

theorem gFold_gFoldMul {L : Type} (a b : GExpr L) (ha : gFold a = a) (hb : gFold b = b) :
    gFold (gFoldMul a b) = gFoldMul a b := by
  cases a <;> cases b <;> simp_all [gFoldMul, gFold]

/-- ⚑ **A SECOND EMIT RUN MOVES ZERO BYTES** — as a theorem rather than as a re-run that happened
to agree. `gFold` is idempotent at every alphabet, so the artifact the re-emission installs is a
fixed point of the pass that produced it. -/
theorem gFold_idem {L : Type} (e : GExpr L) : gFold (gFold e) = gFold e := by
  induction e with
  | leaf l => rfl
  | const k => rfl
  | add a b iha ihb => exact gFold_gFoldAdd _ _ iha ihb
  | mul a b iha ihb => exact gFold_gFoldMul _ _ iha ihb

/-! ### §6c″ — ⚑ the RED pole. A fold that cannot be seen to act is decoration.

`gFold_no_dead` is universally quantified and therefore says nothing about whether the pass ever
FIRES. These three do: the exact shape the corpus ships 4,284 times, the cascade that makes the
total 28 nodes larger than 2 × 5,075, and a body the pass must leave alone. -/

/-- The corpus's own dead subtree — `mul(const -1, const 1)`, what a subtraction of one lowers to —
folded to the literal. Three nodes become one. -/
theorem gFold_kills_dead_product :
    gFold (L := VLeaf) (.mul (.const (-1)) (.const 1)) = .const (-1) := by decide

/-- ⚑ THE CASCADE, which is why the corpus total is not simply `2 × (dead subtree count)`: folding
an inner product exposes an outer one. `private-book-bfv-threshold-terminal-q0-b80` is where this
shows up — 66 dead subtrees, but 160 nodes deleted rather than 132. -/
theorem gFold_cascades :
    gFold (L := VLeaf) (.mul (.mul (.const 2) (.const 3)) (.const 5)) = .const 30 := by decide

/-- ⚠ **AND IT LEAVES A LIVE GATE ALONE.** The pass must not touch a product that reaches a column;
`mul(const 1, var 3)` is the unit coefficient the canonical renderer deliberately writes and the
fold has no opinion about it. This is the conjunct that fails if `gFold` is ever "improved" into an
identity-eliminator — which would DESTROY normality rather than preserve it. -/
theorem gFold_spares_live_product :
    gFold (L := VLeaf) (.add (.mul (.const 1) (.leaf 3)) (.mul (.const (-1)) (.const 1)))
      = .add (.mul (.const 1) (.leaf 3)) (.const (-1)) := by decide

/-! ### §6d — ⚑ the canonicalizer AT A VIEW, and the fusion law that makes it free.

A rail canonicalizes by embedding, canonicalizing, and rendering back. `gCanonAt` is that, and it
inherits BOTH theorems from `gCanon` through `render_gHeadToExpr` — so the `EmittedExpr` rail and
the `WindowExpr` rail are one definition applied twice, exactly as the renderer is. -/

/-- Canonicalize a body of the target AST `E`, given its embedding and its view. -/
def gCanonAt {L E : Type} (O : ExprOps L E) (of : E → GExpr L) (e : E) : E :=
  gHeadToExpr O (gExprToHead (of e))

/-- The view's canonicalization IS the one AST's, rendered. -/
theorem gCanonAt_render {L E : Type} (O : ExprOps L E) (of : E → GExpr L) (e : E) :
    gCanonAt O of e = render O (gCanon (of e)) := by
  rw [gCanonAt, gCanon, render_gHeadToExpr]

/-- ⚑ **THE FOLD AT A VIEW.** `gFold` is already `GExpr L → GExpr L`, so no fusion law is needed:
embed, fold, render back. Both deployed rails are this one definition applied twice, exactly as
`gCanonAt` is. -/
def gFoldAt {L E : Type} (O : ExprOps L E) (of : E → GExpr L) (e : E) : E :=
  render O (gFold (of e))

/-! ## §7 — ⚑ THE GADGET LIBRARY, AUTHORED ONCE.

The three families the census ranked. Each is written at `GExpr L` — leaf-generic, so it is
consumable from every one of the five ASTs, which is precisely what the type split prevented. -/

/-! ### §7.1 — the ALPHABET gate, which subsumes booleanity.

The census found **62 named booleanity defs across 51 files plus 5 inline**, and separately found
**four hits that were not duplicates but GENERALIZATIONS** — degree-3/4 gates `∏(x−k)` over a larger
alphabet — with `stateGridGate` shipping under ONE NAME at TWO DEGREES in two files. Those are the
same gadget at different alphabets, and this is the parameterised form both are instances of: *"the
parameterized `gGrid` nobody wrote."* -/

/-- `x − k`, with the additive unit ELIDED: `k = 0` renders bare `x`. ⚑ This is what makes the
degree-2 instance byte-identical to the deployed `gBin` (`x·(x−1)`, **not** `(x−0)·(x−1)`), and it is
the reason a naive `∏(x−k)` generalization would have moved bytes. -/
def gSub {L : Type} (x : GExpr L) (k : ℤ) : GExpr L :=
  if k = 0 then x else .add x (.const (-k))

/-- ⚑ **THE ALPHABET GATE** `∏_{k ∈ ks} (x − k)`, left-nested. Vanishes exactly on `ks`. -/
def gAlphabet {L : Type} (x : GExpr L) : List ℤ → GExpr L
  | []      => .const 1
  | k :: ks => ks.foldl (fun acc t => .mul acc (gSub x t)) (gSub x k)

/-- ⚑ **BOOLEANITY IS THE ALPHABET GATE AT `[0,1]`** — a definition, not a coincidence. -/
abbrev gBool {L : Type} (x : GExpr L) : GExpr L := gAlphabet x [0, 1]

/-- ⚑ **AND IT IS THE DEPLOYED BYTE.** `AirBuilder.gBin` is this instantiation, for EVERY column,
`by rfl`. -/
theorem gBool_is_gBin (co : Nat) :
    render toEmitted (gBool (.leaf co)) = Dregg2.Circuit.Emit.AirBuilder.gBin co := rfl

/-- The window-rail booleanity is the SAME gadget — the thing the type split made impossible. -/
theorem gBool_window (co : Nat) :
    render toWindow (gBool (.leaf (.loc co)))
      = WindowExpr.mul (.loc co) (.add (.loc co) (.const (-1))) := rfl

/-- The degree-3 alphabet gate — `stateGridGate`'s wider instance, from the same def. -/
theorem gAlphabet_deg3 (co : Nat) :
    render toEmitted (gAlphabet (.leaf co) [0, 1, 2])
      = .mul (.mul (.var co) (.add (.var co) (.const (-1)))) (.add (.var co) (.const (-2))) := rfl

/-- ⚑ **THE GADGET IS RIGHT, NOT JUST SHAPED RIGHT**: the alphabet gate vanishes at a value exactly
when the value is in the alphabet. Stated on the ONE AST, so it holds through every view — 62 defs
had this fact re-proved, restated, or (mostly) not stated at all. -/
theorem gAlphabet_eval_zero_iff {L : Type} (ρ : L → ℤ) (x : GExpr L) (ks : List ℤ) (hne : ks ≠ []) :
    evalG ρ (gAlphabet x ks) = 0 ↔ evalG ρ x ∈ ks := by
  have hsub : ∀ t : ℤ, evalG ρ (gSub x t) = evalG ρ x - t := by
    intro t; by_cases ht : t = 0 <;> (simp [gSub, ht, evalG]; try ring)
  have key : ∀ (rest : List ℤ) (acc : GExpr L),
      evalG ρ (rest.foldl (fun a t => GExpr.mul a (gSub x t)) acc)
        = evalG ρ acc * (rest.map (fun t => evalG ρ x - t)).prod := by
    intro rest
    induction rest with
    | nil => intro acc; simp
    | cons t ts ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.map_cons, List.prod_cons, evalG, hsub]
      ring
  cases ks with
  | nil => exact absurd rfl hne
  | cons k rest =>
    simp only [gAlphabet, key, hsub]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h0 | h0
      · exact List.mem_cons.2 (Or.inl (by omega))
      · obtain ⟨t, ht, hte⟩ := List.mem_map.1 (List.prod_eq_zero_iff.1 h0)
        exact List.mem_cons.2 (Or.inr ((by omega : evalG ρ x = t) ▸ ht))
    · intro h
      rcases List.mem_cons.1 h with h0 | h0
      · rw [h0]; simp
      · exact mul_eq_zero.2 (Or.inr (List.prod_eq_zero_iff.2
          (List.mem_map.2 ⟨evalG ρ x, h0, by omega⟩)))

/-! #### The THREE encodings that actually ship, and what normalizing them costs.

⚠ **THIS CORRECTS THE CENSUS IN THE DIRECTION THAT MATTERS.** The census reported two encodings and
concluded that normalizing would stop 4,401 redundant nodes shipping. Measured on the 111 checked-in
descriptors (`circuit/descriptors/by-name/*.json`, 1,794,644 arithmetic nodes):

* **encoding 1** — `mul(x, add(x, const −1))`, **5 nodes** — **3,665** deployed sites.
* **encoding 2** — `mul(x, add(x, mul(const −1, const 1)))`, **7 nodes** — **4,058** deployed sites.
  The `mul(const −1, const 1)` subtree is dead weight and there is no constant folder anywhere in the
  tree; it occurs **4,401** times, i.e. **8,802 wasted nodes** (869 in `private-book-bfv-slice`, 812
  in `dark-bazaar-private-poa-settlement` — the census's two named descriptors, confirmed).
* **encoding 3** — `add(mul(x, x), mul(const −1, x))`, **7 nodes** — `BlindedMembershipEmit.
  bitBinaryBody` and `AdjacencyMembershipEmit.dirBinaryBody`, re-exported into five further files.
  The census did not have this one.

⚑ **AND THE COROLLARY THE CENSUS GOT BACKWARDS:** the corpus normal form is not the cheap target.
`AirNormalForm.isNormal` rejects ALL THREE (each has `mul` at the root with a non-`const` left
child), and the canonical rendering of `x·(x−1)` from its head is `add(mul(const 1, mul(x, x)),
mul(const −1, x))` — **9 nodes**, larger than every shipping encoding. So there are TWO different
jobs here and they pull opposite ways:

  1. **Converge the three encodings onto encoding 1** — strictly removes 8,802 nodes, and `gAlphabet`
     produces exactly that shape (`gBool_is_gBin`, `rfl`). This is the win.
  2. **Reach `isNormal` compliance** — a separate, larger flag day that makes descriptors *bigger*.
     Worth doing for the decidability it buys, but it is not a node-count improvement and saying so
     would be quoting the flattering half of a pair. -/

/-- Encoding 2, generically: the redundant-`(−1)·1` shape, so the waste is an object. -/
def gBoolEnc2 {L : Type} (x : GExpr L) : GExpr L :=
  .mul x (.add x (.mul (.const (-1)) (.const 1)))

/-- Encoding 3, generically: the expanded `x² − x` shape. -/
def gBoolEnc3 {L : Type} (x : GExpr L) : GExpr L :=
  .add (.mul x x) (.mul (.const (-1)) x)

/-- Count every node of a body. -/
def nodeCount {L : Type} : GExpr L → Nat
  | .leaf _  => 1
  | .const _ => 1
  | .add a b => 1 + nodeCount a + nodeCount b
  | .mul a b => 1 + nodeCount a + nodeCount b

/-! ### §7.1d — ⚑ THE FOLD NEVER GROWS A BODY.

§6c′ reports the fold shrinking all 26 moving descriptors, and a per-descriptor table is evidence
about those 26 at one revision. This is the general fact, and it is the one that makes "fold-only
makes the artifact SMALLER" a property of the pass rather than a property of today's corpus:
`gCanon` has no such theorem and cannot — it grows 76 of the 90 descriptors it moves. -/

theorem gFoldAdd_nodeCount_le {L : Type} (a b : GExpr L) :
    nodeCount (gFoldAdd a b) ≤ nodeCount (GExpr.add a b) := by
  cases a <;> cases b <;> simp [gFoldAdd, nodeCount]

theorem gFoldMul_nodeCount_le {L : Type} (a b : GExpr L) :
    nodeCount (gFoldMul a b) ≤ nodeCount (GExpr.mul a b) := by
  cases a <;> cases b <;> simp [gFoldMul, nodeCount]

/-- ⚑ **THE FOLD NEVER GROWS AN EXPRESSION**, at any alphabet. -/
theorem gFold_nodeCount_le {L : Type} (e : GExpr L) : nodeCount (gFold e) ≤ nodeCount e := by
  induction e with
  | leaf l => exact Nat.le_refl _
  | const k => exact Nat.le_refl _
  | add a b iha ihb =>
    refine le_trans (gFoldAdd_nodeCount_le _ _) ?_
    simp only [nodeCount]; omega
  | mul a b iha ihb =>
    refine le_trans (gFoldMul_nodeCount_le _ _) ?_
    simp only [nodeCount]; omega

/-- ⚠ …and it is not vacuously true by never firing: on the corpus's own dead subtree it is a
STRICT decrease, 3 nodes to 1. -/
theorem gFold_nodeCount_strict :
    nodeCount (gFold (L := VLeaf) (.mul (.const (-1)) (.const 1)))
      < nodeCount (L := VLeaf) (.mul (.const (-1)) (.const 1)) := by decide

/-- ⚑ **THE NODE COUNTS, MEASURED IN THE AUTHORING LANGUAGE** — 5 · 7 · 7, for every column. -/
theorem gBool_nodeCount (co : Nat) : nodeCount (gBool (L := VLeaf) (.leaf co)) = 5 := rfl
theorem gBoolEnc2_nodeCount (co : Nat) : nodeCount (gBoolEnc2 (L := VLeaf) (.leaf co)) = 7 := rfl
theorem gBoolEnc3_nodeCount (co : Nat) : nodeCount (gBoolEnc3 (L := VLeaf) (.leaf co)) = 7 := rfl

/-- ⚑ …and all three are the SAME POLYNOMIAL, so the two larger ones are pure waste. -/
theorem gBoolEnc2_eval {L : Type} (ρ : L → ℤ) (x : GExpr L) :
    evalG ρ (gBoolEnc2 x) = evalG ρ (gBool x) := by
  show evalG ρ (GExpr.mul x (GExpr.add x (GExpr.mul (.const (-1)) (.const 1))))
     = evalG ρ (GExpr.mul x (GExpr.add x (GExpr.const (-1))))
  simp only [evalG]; ring

theorem gBoolEnc3_eval {L : Type} (ρ : L → ℤ) (x : GExpr L) :
    evalG ρ (gBoolEnc3 x) = evalG ρ (gBool x) := by
  show evalG ρ (GExpr.add (GExpr.mul x x) (GExpr.mul (.const (-1)) x))
     = evalG ρ (GExpr.mul x (GExpr.add x (GExpr.const (-1))))
  simp only [evalG]; ring

/-! #### ⚠ And the "fully general form" already in the tree is NOT a drop-in.

`memberExpr` — `∏(col − s)`, byte-identical in THREE files (`AutomataflStepEmit`,
`AutomataflResolveEmit`, `AutomataflCommit`) — looks like the natural target for the whole census. It
is not: it has **no zero-elision**, so its `k = 0` factor renders `add(var c, const 0)` and the
degree-2 instance comes out **7 nodes against `gBin`'s 5** — a different emitted object. Adopting it
would have moved bytes at all 3,665 deployed encoding-1 sites. `gSub` is the one line that fixes it;
`gBool_is_gBin` is the evidence that it did. -/

/-- `∏(x − k)` WITHOUT the zero-elision — the shape the three `memberExpr` copies produce. -/
def gAlphabetNoElide {L : Type} (x : GExpr L) : List ℤ → GExpr L
  | []      => .const 1
  | k :: ks => ks.foldl (fun acc t => .mul acc (.add x (.const (-t)))) (.add x (.const (-k)))

theorem gAlphabetNoElide_nodeCount (co : Nat) :
    nodeCount (gAlphabetNoElide (L := VLeaf) (.leaf co) [0, 1]) = 7 := rfl

/-- ⚑ …and it is a DIFFERENT emitted object from the deployed booleanity pin. -/
theorem memberExpr_shape_is_not_gBin :
    render toEmitted (gAlphabetNoElide (L := VLeaf) (.leaf 0) [0, 1])
      ≠ Dregg2.Circuit.Emit.AirBuilder.gBin 0 := by decide

/-- ⚑ …and the SAME comparison on the one AST, so it is a fact about the gadget rather than about
one view of it. -/
theorem gAlphabetNoElide_ne_gBool :
    gAlphabetNoElide (L := VLeaf) (.leaf 0) [0, 1] ≠ gBool (L := VLeaf) (.leaf 0) := by decide

/-- …while the elided form is the same polynomial, so the choice is purely a rendering one. -/
theorem gAlphabetNoElide_eval {L : Type} (ρ : L → ℤ) (x : GExpr L) :
    evalG ρ (gAlphabetNoElide x [0, 1]) = evalG ρ (gBool x) := by
  show evalG ρ (GExpr.mul (GExpr.add x (GExpr.const 0)) (GExpr.add x (GExpr.const (-1))))
     = evalG ρ (GExpr.mul x (GExpr.add x (GExpr.const (-1))))
  simp only [evalG]; ring

/-! ### §7.1c — ⚑ THE CANONICAL RENDERING, ONCE THE OPERATOR LIFTED "BYTES MAY NOT MOVE".

Converging the three shipping encodings onto `gBool` (5 nodes) and reaching `AirNormalForm.isNormal`
(9 nodes) were priced as two DIFFERENT jobs above (§7.1 header) under a brief that froze bytes. That
freeze is lifted: this project's standing doctrine is that a flag day here is a rebuild, not a
migration, and a cost estimate ("9 > 5, so canonicalizing is a second job") is not a reason to stop at
the cheaper non-canonical form. So booleanity has ONE more step: not just "the same helper everywhere"
but "the NORMAL FORM everywhere" — the property `AirNormalForm.isNormal` exists to buy, that two gates
meaning the same thing render the same, made real for the family this module collapsed. -/

/-- ⚑ **THE CANONICAL BOOLEANITY HEAD** — `x² − x` as a `GHead`: one squared-product term, one linear
term, no constant. -/
def gBoolHead {L : Type} (x : L) : GHead L :=
  ((GHead.zero (L := L)).addProd 1 [x, x]).addLin (-1) x

/-- ⚑ **THE CANONICAL BOOLEANITY GATE.** `gHeadToExpr` of `gBoolHead` — `mul(const 1, mul(x,x))` added
to `mul(const −1, x)`, 9 nodes, the corpus normal form's own rendering of `x·(x−1)`. This is the target
every migrated call site now points at, not `gBool`: `gBool` remains the closed-form 5-node witness the
byte-count claims are measured against (`gBool_nodeCount` etc.), `gBoolCanon` is what ships. -/
def gBoolCanon {L : Type} (x : L) : GExpr L := gHeadToExpr idOps (gBoolHead x)

/-- ⚑ Node count, measured: 9, for every leaf. -/
theorem gBoolCanon_nodeCount (co : VLeaf) : nodeCount (gBoolCanon co) = 9 := rfl

/-- ⚑ **THE CANONICAL FORM IS NORMAL BY CONSTRUCTION** — an instance of the ONE proof every
`gHeadToExpr` rendering gets for free (`gHeadToExpr_gIsNormal`), not a new argument. -/
theorem gBoolCanon_isNormal {L : Type} (x : L) : gIsNormal (gBoolCanon x) = true :=
  gHeadToExpr_gIsNormal _

/-- `gBool`'s value, stated plainly (the general `gAlphabet` machinery proves membership-in-roots;
this is the value itself). -/
theorem gBool_eval {L : Type} (ρ : L → ℤ) (x : GExpr L) :
    evalG ρ (gBool x) = evalG ρ x * (evalG ρ x - 1) := by
  show evalG ρ (GExpr.mul x (GExpr.add x (GExpr.const (-1)))) = evalG ρ x * (evalG ρ x - 1)
  simp only [evalG]; ring

/-- `gBoolCanon`'s value, stated plainly. -/
theorem gBoolCanon_eval' {L : Type} (ρ : L → ℤ) (x : L) :
    evalG ρ (gBoolCanon x) = ρ x * (ρ x - 1) := by
  show evalG ρ (gHeadToExpr idOps (gBoolHead x)) = ρ x * (ρ x - 1)
  rw [gHeadToExpr_eval]
  simp [gBoolHead, GHead.zero, GHead.addProd, GHead.addLin, gEvalH, gEvalTerm]
  ring

/-- ⚑ **THE CANONICAL FORM IS THE SAME POLYNOMIAL AS `gBool`** — every alphabet, every leaf
environment. This is the fact that makes swapping the render target a re-emission and NOT a semantic
edit: node count changes, the value a satisfying assignment must hit does not. -/
theorem gBoolCanon_eval {L : Type} (ρ : L → ℤ) (x : L) :
    evalG ρ (gBoolCanon x) = evalG ρ (gBool (.leaf x)) := by
  rw [gBoolCanon_eval', gBool_eval]; rfl

/-- ⚑ **THE DEPLOYED BYTE, CANONICAL, `EmittedExpr`.** For every column, `rfl`: this is exactly what
`scripts/emit-descriptors.sh` now writes for a migrated booleanity site. -/
theorem gBoolCanon_emitted (co : VLeaf) :
    render toEmitted (gBoolCanon co)
      = .add (.mul (.const 1) (.mul (.var co) (.var co))) (.mul (.const (-1)) (.var co)) := rfl

/-- ⚑ …and the window rail, the same object. -/
theorem gBoolCanon_window (co : Nat) :
    render toWindow (gBoolCanon (WLeaf.loc co))
      = .add (.mul (.const 1) (.mul (.loc co) (.loc co))) (.mul (.const (-1)) (.loc co)) := rfl

/-! ### §7.1b — ⚑ THE CHIP ABSORB TUPLE, and the arity check the type split DROPPED.

`LightClientSolanaAir.chipTuple16` exists *because* the chip helpers are `EmittedExpr` and that file
works in `Circuit.Expr` — and the re-typing dropped the arity gate. `chipLookupTupleN` takes
`hAdm : ChipArityAdmitted ins.length` as an `autoParam` (a site at arity 8, 9 or 14 **fails to
elaborate**) and pads through `padToE`; `chipTuple16` took neither, and wrote the arity tag as the
LITERAL `16` rather than `ins.length`, so its tag was decoupled from its own input list. This is the
generic constructor both are instances of. -/

/-- The expression-tuple pad, over any view. `AirNormalForm`'s obligation discipline is preserved:
`hFits` is an `autoParam` on the PRE-pad length, so an over-long block fails to elaborate rather than
being silently truncated or saturated. -/
def gPadTo {L E : Type} (O : ExprOps L E) (n : Nat) (es : List E)
    (hFits : es.length ≤ n := by pad_fits) : List E :=
  let _ := hFits
  es ++ List.replicate (n - es.length) (O.const 0)

/-- ⚑ **THE CHIP ABSORB TUPLE**: `(arity, inputs padded to `CHIP_RATE`, output columns)`. The arity
tag is `ins.length` — never a literal — and `hAdm` is the same `autoParam` gate the three
`EmittedExpr` rails carry. -/
def gChipTuple {L E : Type} (O : ExprOps L E) (ins : List E) (outCols : List L)
    (hAdm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted ins.length := by chip_arity_admitted) :
    List E :=
  O.const (ins.length : ℤ)
    :: gPadTo O Dregg2.Circuit.DescriptorIR2.CHIP_RATE ins
         (Dregg2.Circuit.DescriptorIR2.chipArity_le_rate hAdm)
    ++ outCols.map O.leaf

/-- The pad IS `padToE`, for every tuple. -/
theorem gPadTo_emitted (n : Nat) (es : List EmittedExpr) (h : es.length ≤ n) :
    gPadTo toEmitted n es h = Dregg2.Circuit.DescriptorIR2.padToE n es h := rfl

/-- ⚑ **`chipLookupTupleN` IS `gChipTuple toEmitted`** — every input list, every digest column list,
`rfl`. So restoring the check on the `Circuit.Expr` rail is an instantiation, not a fourth copy. -/
theorem gChipTuple_emitted (ins : List EmittedExpr) (cols : List VLeaf)
    (hAdm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted ins.length) :
    gChipTuple toEmitted ins cols hAdm
      = Dregg2.Circuit.DescriptorIR2.chipLookupTupleN ins cols hAdm := rfl

/-! ### §7.2 — the MUX, in the form that costs ONE multiplication.

The census found **26 mux sites, 22 named defs, 12 files, zero shared helper**, with the Merkle
sibling-swap written **seven times in two algebraically distinct forms** (verified at source: 3 form
A, 4 form B). Both forms are named here, proved equal as polynomials, and the cost difference is a
theorem rather than a claim — one that CORRECTS the census's figure; see `gMux_cheaper`.

⚠ Two shared mux helpers already exist on OTHER rails — `R1csFr.Wire.select` (gnark `Wire`, with
`eval_select_of_bool`) and `KimchiGadgets.selectHalves` (the Kimchi `Half` rail, with
`selectHalves_sound`). Both are form B. There was none for `EmittedExpr`, `WindowExpr` or `ChalExpr`,
which is exactly the set this AST covers. -/

/-- ⚑ **THE MUX, FORM B** — `l + b·(r − l)`. -/
def gMux {L : Type} (b l r : GExpr L) : GExpr L :=
  .add l (.mul b (.add r (.mul (.const (-1)) l)))

/-- **FORM A** — `b·r + (1 − b)·l`. Same polynomial, more multiplications. Named so the census's
"two algebraically distinct forms" is a comparison rather than an assertion. -/
def gMuxA {L : Type} (b l r : GExpr L) : GExpr L :=
  .add (.mul b r) (.mul (.add (.const 1) (.mul (.const (-1)) b)) l)

/-- ⚑ **THE TWO FORMS ARE THE SAME POLYNOMIAL** — every assignment, every alphabet. This is what
makes the expensive sites strictly wasteful rather than differently-specified. -/
theorem gMux_eval_eq {L : Type} (ρ : L → ℤ) (b l r : GExpr L) :
    evalG ρ (gMux b l r) = evalG ρ (gMuxA b l r) := by
  simp only [gMux, gMuxA, evalG]; ring

/-- ⚑ …and the mux SELECTS, which the 22 defs left unstated: at `b = 0` it is `l`, at `b = 1` it is
`r`. -/
theorem gMux_eval_select {L : Type} (ρ : L → ℤ) (b l r : GExpr L) :
    (evalG ρ b = 0 → evalG ρ (gMux b l r) = evalG ρ l) ∧
    (evalG ρ b = 1 → evalG ρ (gMux b l r) = evalG ρ r) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [gMux, evalG, h] <;> ring

/-- Count the multiplications a body carries. -/
def mulCount {L : Type} : GExpr L → Nat
  | .leaf _  => 0
  | .const _ => 0
  | .add a b => mulCount a + mulCount b
  | .mul a b => 1 + mulCount a + mulCount b

/-- ⚑ **THE COST GAP, MEASURED — and it is ONE multiplication, not two.**

⚠ This CORRECTS the census figure it implements. The census reported *"form A costs two
multiplications where form B costs one, so 14 sites are strictly more expensive"*. Counted on the
emitted nodes: form B carries **2** multiplications (the selector multiply and the `(−1)·l`
negation), form A carries **3** (`b·r`, `(−1)·b`, and the `(1−b)·l`). The gap is **one multiplication
per expression**, and a structural sweep found **6** form-A swap expressions (three sites, two
expressions each — `DeployedCapOpen.leftExpr`/`rightExpr`, `TableAirIR.node8Tuple`'s L8/R8,
`AdjacencyMembershipEmit.leftOrderBody`/`rightOrderBody`), not 14. The 14 is reached only by counting
the 4-ary child-arrangement copies as sibling swaps, and those are 4-way Lagrange selects with a
different cost model.

What DOES hold at the census's strength is the SELECTOR count, which is what the quotient degree
sees: form B multiplies by the bit ONCE, form A twice. -/
theorem gMux_cheaper (b l r : Nat) :
    mulCount (gMux (L := VLeaf) (.leaf b) (.leaf l) (.leaf r)) + 1
      = mulCount (gMuxA (L := VLeaf) (.leaf b) (.leaf l) (.leaf r)) := rfl

theorem gMux_mulCount (b l r : Nat) :
    mulCount (gMux (L := VLeaf) (.leaf b) (.leaf l) (.leaf r)) = 2 := rfl

theorem gMuxA_mulCount (b l r : Nat) :
    mulCount (gMuxA (L := VLeaf) (.leaf b) (.leaf l) (.leaf r)) = 3 := rfl

/-- **The Merkle sibling-swap**, the seven-times-written instance: the LEFT input of the parent
hash, given the swap bit and the two children. -/
def gSwapLeft {L : Type} (bit cur sib : GExpr L) : GExpr L := gMux bit cur sib
/-- …and the RIGHT input. -/
def gSwapRight {L : Type} (bit cur sib : GExpr L) : GExpr L := gMux bit sib cur

/-- ⚑ **`TableAirIR.node8Tuple`'s `L8`/`R8` lanes ARE `gSwapLeft`/`gSwapRight`, `rfl`.** Stated here
rather than migrated in `TableAirIR.lean` itself: `GateExpr` imports `TableAirIR`, so the reverse
import is a cycle (the same constraint `gCols`/`gVars`/`gOneMinus_table` name). `node8Tuple`'s body
was rewritten BY HAND to this shape; this pin is the check that the rewrite is exactly `gMux`. -/
theorem node8Tuple_is_gMux (cur sib dir : Nat) :
    render toTable (gSwapLeft (.leaf (TLeaf.win (WLeaf.loc dir)))
        (.leaf (TLeaf.win (WLeaf.loc cur))) (.leaf (TLeaf.win (WLeaf.loc sib))))
      = .add (Dregg2.Circuit.TableAirIR.v cur) (.mul (Dregg2.Circuit.TableAirIR.v dir)
          (Dregg2.Circuit.TableAirIR.eSub (Dregg2.Circuit.TableAirIR.v sib) (Dregg2.Circuit.TableAirIR.v cur))) :=
  rfl

theorem node8Tuple_R_is_gMux (cur sib dir : Nat) :
    render toTable (gSwapRight (.leaf (TLeaf.win (WLeaf.loc dir)))
        (.leaf (TLeaf.win (WLeaf.loc cur))) (.leaf (TLeaf.win (WLeaf.loc sib))))
      = .add (Dregg2.Circuit.TableAirIR.v sib) (.mul (Dregg2.Circuit.TableAirIR.v dir)
          (Dregg2.Circuit.TableAirIR.eSub (Dregg2.Circuit.TableAirIR.v cur) (Dregg2.Circuit.TableAirIR.v sib))) :=
  rfl

/-- ⚑ **THE SWAP IS A SWAP** — at `bit = 1` the pair is exchanged, at `bit = 0` it is not. Stated
once, for every alphabet; no site stated it at all. -/
theorem gSwap_exchanges {L : Type} (ρ : L → ℤ) (bit cur sib : GExpr L) :
    (evalG ρ bit = 0 →
      evalG ρ (gSwapLeft bit cur sib) = evalG ρ cur ∧
      evalG ρ (gSwapRight bit cur sib) = evalG ρ sib) ∧
    (evalG ρ bit = 1 →
      evalG ρ (gSwapLeft bit cur sib) = evalG ρ sib ∧
      evalG ρ (gSwapRight bit cur sib) = evalG ρ cur) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩ <;>
    simp only [gSwapLeft, gSwapRight, gMux, evalG, h] <;> ring

/-! ### §7.3 — the TRANSITION THREAD.

The census named four defs — `constBody` · `contBody` · `contWindowBody` · `carryBody` — as "four
names, four files, the same eight tokens". A structural sweep of the tree found **~40**: three
byte-identical `wThread`s (`DyckStackEmit`, `DyckStackRefine`, `RowLibraryExperiment`), three
byte-identical `contWindowBody`s in the Dfa cone, byte-identical `wContWindow` pairs in the
wide-membership cone, byte-identical `carryLeg`s in `PastaLadderThread`/`MinaWrapConjunctionAir`,
plus ~20 anonymous inline copies. All of them are this: -/

/-- ⚑ **THE THREAD BODY** `nxt(dst) − loc(src)`, in the deployed rendering
`add(nxt dst, mul(const −1, loc src))`. -/
def gThread (dst src : Nat) : GExpr WLeaf :=
  .add (.leaf (.nxt dst)) (.mul (.const (-1)) (.leaf (.loc src)))

/-- The same-column case — `constBody`, `carryBody`, `attRootBody`, `rootCarryWindow`, … -/
abbrev gCarry (c : Nat) : GExpr WLeaf := gThread c c

/-- ⚑ **THE DEPLOYED BYTE, FOR EVERY COLUMN PAIR, `by rfl`.** This is literally the body of
`AccumulatorNonRevocationEmit.constBody`,
`EffectActionBindingEmit.contWindowBody`, `ExactNullifierAafiRotatedStateWeld.carryBody` and
`DyckStackEmit.wThread` — one object under five names, now one object under one name. -/
theorem gThread_window (dst src : Nat) :
    render toWindow (gThread dst src)
      = WindowExpr.add (.nxt dst) (.mul (.const (-1)) (.loc src)) := rfl

/-- ⚑ **AND IT THREADS**: the body vanishes exactly when the next row's `dst` equals this row's
`src`. Sixteen call sites re-proved this per-column; it is one theorem. -/
theorem gThread_eval_zero_iff (env : VmRowEnv) (dst src : Nat) :
    evalG (wEnv env) (gThread dst src) = 0 ↔ env.nxt dst = env.loc src := by
  simp only [gThread, evalG, wEnv]; omega

/-- ⚠ The hand-written thread body is NOT in the corpus normal form — its `nxt` leaf rides bare where
the canonical rendering writes `mul(const 1, nxt)`. That is exactly the byte the re-emission moves,
and part of why 88 of 111 descriptors are currently non-canonical. -/
theorem gThread_not_normal (dst src : Nat) : gIsNormal (gThread dst src) = false := rfl

/-- The canonical rendering of the same polynomial, from the head. -/
def gThreadHead (dst src : Nat) : GHead WLeaf :=
  ((GHead.zero (L := WLeaf)).addLin 1 (.nxt dst)).addLin (-1) (.loc src)

/-- ⚑ **THE NORMALIZED THREAD.** `mul(const 1, nxt dst)` where the hand-written form wrote
`nxt dst` — two nodes added per thread gate. This is the re-emission stated as an object rather than
as a plan. -/
theorem gThreadHead_normal (dst src : Nat) :
    gIsNormal (gHeadToExpr (idOps (L := WLeaf)) (gThreadHead dst src)) = true :=
  gHeadToExpr_gIsNormal _

/-- …and it is the SAME POLYNOMIAL as the hand-written body — the normalization is a rendering change
and nothing else, which is what makes it a re-emit rather than a semantic edit. -/
theorem gThreadHead_eval (env : VmRowEnv) (dst src : Nat) :
    evalG (wEnv env) (gHeadToExpr (idOps (L := WLeaf)) (gThreadHead dst src))
      = evalG (wEnv env) (gThread dst src) := by
  show evalG (wEnv env)
      (GExpr.add (GExpr.mul (.const 1) (.leaf (WLeaf.nxt dst)))
                 (GExpr.mul (.const (-1)) (.leaf (WLeaf.loc src))))
    = evalG (wEnv env) (gThread dst src)
  simp only [gThread, evalG, wEnv]
  ring

/-! ### §7.4 — the COLUMN-READER family, once.

A structural census found the SAME THREE-DEFINITION IDIOM — `cols` (a run of column indices from a
base), `vars` (those columns read as leaf expressions) and `stateCols` (a sponge-state-width block at
a step) — byte-identical in THREE files (`Emit/ExactFieldsRefusalEmit.lean`,
`Emit/FaithfulNoteSpendDescriptorPlan.lean`, `Games/DescentCensusDescriptor.lean`), plus narrower
base-0 instances of the same `vars` shape (`ChipArityBite.ins`). `cols` never touches a leaf, so it
needed no alphabet parameter at all; `vars` is `gVars` below at `toEmitted`.

⚠ `DescriptorIR2.lean`'s three `factColsFour`/`factColsNine`/`factColsFourteen` are the SAME shape
again but are NOT migrated here: `GateExpr` imports `TableAirIR`, which imports `DescriptorIR2` — a
`DescriptorIR2` → `GateExpr` import would be a cycle. Named as a residual, not silently dropped. -/

/-- A run of `count` column indices starting at `base` — alphabet-free, so it is the SAME `List Nat`
whichever AST reads it. -/
def gCols (base count : Nat) : List Nat := (List.range count).map (base + ·)

/-- The run, read as leaf expressions in ANY view — `vars`/`ins`'s shared body. -/
def gVars {E : Type} (O : ExprOps VLeaf E) (base count : Nat) : List E :=
  (gCols base count).map O.leaf

/-- ⚑ **`vars`/`ins` ARE THIS, on `EmittedExpr`, `rfl`.** -/
theorem gVars_emitted (base count : Nat) :
    gVars toEmitted base count = (gCols base count).map .var := rfl

/-! ### §7.5 — the ESUB / "1 − e" family, once.

A structural census found the generic two-argument idiom `esub`/`eSub a b := add a (mul (const -1)
b)` reinvented as its own named local def in well over a dozen files, across EVERY one of the five
concrete ASTs, and its one-argument specialization `1 − e` under at least a dozen more distinct
names (`eOneMinus`, `oneMinus`, `oneMinusW`, `eoneMinus`, `notDbl`, `notPadding`, `unlessFire`,
`whenHold`, `eneg1`, `atLeastOneFactor`, `wInvGate`, `eCreditSel`) — the SAME shape `gMuxA`'s own
`(1 − b)` sub-term already carries (`gMuxA_has_gOneMinus` below), never itself exposed as a reusable
combinator, which is very probably why nothing reused it. Both are one definition, generic over the
view, applied everywhere.

⚠ The named-def population above is what is migrated below. A further ~35 INLINE (unnamed)
occurrences of the same shape, embedded directly in unrelated larger definitions across ~20 further
files, were also found by the census and are NOT migrated in this pass — the volume and the breadth
of unrelated subsystems they sit in (Pasta, Automatafl, Fold, DyckStack, EffectVM, …) make a safe
single-pass edit of all of them irresponsible; they are a named residual for a follow-up, not a hole
silently left out of the count. -/

/-- `−e`, the standard encoding: `mul (const -1) e`. -/
def gNeg {L E : Type} (O : ExprOps L E) (e : E) : E := O.mul (O.const (-1)) e

/-- `a − b` — the generic two-argument subtraction every `esub`/`eSub`/`subE`/`sub`/`subW` copy
reinvents. -/
def gEsub {L E : Type} (O : ExprOps L E) (a b : E) : E := O.add a (gNeg O b)

/-- `1 − e` — the specialization `eOneMinus`/`oneMinus`/`oneMinusW`/`notDbl`/… all name separately. -/
def gOneMinus {L E : Type} (O : ExprOps L E) (e : E) : E := gEsub O (O.const 1) e

/-- ⚑ **THE MUX'S OWN `(1 − b)` FACTOR IS THIS.** `gMuxA`'s second term never exposed its own
complement as a combinator; this is the fact that it could have. -/
theorem gMuxA_has_gOneMinus {L : Type} (b l r : GExpr L) :
    gMuxA b l r = .add (.mul b r) (.mul (gOneMinus idOps b) l) := rfl

theorem gEsub_eval {L : Type} (ρ : L → ℤ) (a b : GExpr L) :
    evalG ρ (gEsub idOps a b) = evalG ρ a - evalG ρ b := by
  simp only [gEsub, gNeg, evalG]; ring

theorem gOneMinus_eval {L : Type} (ρ : L → ℤ) (e : GExpr L) :
    evalG ρ (gOneMinus idOps e) = 1 - evalG ρ e := by
  simp only [gOneMinus, gEsub, gNeg, evalG]; ring

/-- ⚑ **THE FUSION LAW**, once: rendering `gEsub`/`gOneMinus` into any view IS `gEsub`/`gOneMinus`
of the rendered pieces — so a target rail's `esub`/`oneMinus` becomes a one-line `def` that inherits
these facts for free, the same shape as `render_gHeadToExpr` above. -/
theorem render_gEsub {L E : Type} (O : ExprOps L E) (a b : GExpr L) :
    render O (gEsub idOps a b) = gEsub O (render O a) (render O b) := by
  simp only [gEsub, gNeg, render]

theorem render_gOneMinus {L E : Type} (O : ExprOps L E) (e : GExpr L) :
    render O (gOneMinus idOps e) = gOneMinus O (render O e) := by
  simp only [gOneMinus, gEsub, gNeg, render]

/-! #### The pins — named local copies ARE this, `rfl`, at their own view. -/

/-- ⚑ **`LexCompare8Emit.eOneMinus` IS THIS, on `EmittedExpr`, `rfl`.** -/
theorem gOneMinus_emitted (e : EmittedExpr) : gOneMinus toEmitted e = .add (.const 1) (.mul (.const (-1)) e) := rfl

/-- ⚑ **`PastaMsmBound.notDbl`'s shape IS THIS**, applied to the `DBL` column, `rfl`. -/
theorem gOneMinus_var_emitted (c : Nat) :
    gOneMinus toEmitted (.var c) = .add (.const 1) (.mul (.const (-1)) (.var c)) := rfl

/-- ⚑ **The `WindowExpr` rail's `1 − loc c` shape** (`FiniteLogicDescriptorIR2.oneMinusW`,
`TurnChainAirSource`/`EffectVmEmitTurnChainBinding`/`LightClientMinaLinkAir`'s triplicated
`realMonotone`) IS THIS, `rfl`. -/
theorem gOneMinus_loc_window (c : Nat) :
    gOneMinus toWindow (.loc c) = .add (.const 1) (.mul (.const (-1)) (.loc c)) := rfl

/-- ⚑ **`TableAirIR.eOneMinus`'s SHAPE is this**, on `TExpr`, `rfl` — named as a pin rather than a
migration: `GateExpr` imports `TableAirIR`, so `TableAirIR` cannot import `GateExpr` back (a cycle),
the same constraint `gCols`/`gVars` hit against `DescriptorIR2` above. -/
theorem gOneMinus_table (e : TExpr) : gOneMinus toTable e = .add (.const 1) (.mul (.const (-1)) e) := rfl

end Dregg2.Circuit.GateExpr
