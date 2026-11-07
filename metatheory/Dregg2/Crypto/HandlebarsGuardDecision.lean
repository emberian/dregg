/-
# Dregg2.Crypto.HandlebarsGuardDecision — the DEPLOYED templater guard, run through the committed
decidable-predicate tower.

`Crypto/HandlebarsGuarded.lean` demoted the templater's hardcoded brace-ban to ONE guard among many:
a hole carries a `PredRE` over `Dregg2.Exec.Value`, and `noDoubleBraceRE = neg (any* ⬝ {{ ⬝ any*)` is
the particular guard the committed `Handlebars` family uses at EVERY hole
(`noDoubleBraceRE_iff` / `guardedSafe_noDoubleBrace_iff`). `guardedToGrammar` composes those guards
as REGULAR leaves — not a finite `ContextFreeGrammar` — precisely because the `Value` alphabet is
infinite.

A regular leaf over `Value` with pin-shaped `Pred` atoms is EXACTLY the object
`Crypto/Deriv/{SymbolicFixpoint,EquivalenceFixpoint}.lean` decide. This module points that decision
at the templater and asks the two questions a template author actually has:

1. **Can this guard ever be satisfied?** (a contradictory guard means the slot can NEVER be filled —
   the template is a brick.) — `emptyFix`, the runnable `≅`-fixpoint emptiness verdict.
2. **Did my template edit change what the slot accepts?** — `emptyFix` on `symDiff g g'`, the
   runnable language-equivalence decision, over words of EVERY length across the infinite alphabet.

## ═══ THE VERDICTS ═══

### Fragment (§1) — IN, at the CHEAPEST cover
`noDoubleBraceRE`'s leaves are `tt` (from `any`) and `braceP = symEq "t" 0`. Both are PIN atoms, so:

| fragment predicate | verdict | why |
|--------------------|---------|-----|
| `IsSymbolic` (pin/minterm cover, `SymbolicMinterms`) | **true** | `atomsOfLeaves? = some [("t", sym 0), ("t", sym 0)]` |
| `rigidRE` / `RigidFull` (`≅`-dedup side condition)   | **true** | free, via `rigidRE_of_isSymbolic` |
| `scalarRE` (threshold/interval cover, `SymbolicIntervals`) | **false** | `predIntervalAtoms?` covers `atom (.simple …)` comparisons; `symEq` is a SYMBOL pin, not a scalar threshold — no `Int` to compare |
| `differenceRE` (DBM cover, `SymbolicDifference`)     | **false** | `predDifference?` covers `atom`/`fieldEqField`; `symEq` is again outside — it names no difference coordinate |

So the blocking-atom question has a clean answer in the POSITIVE direction: the deployed guard needs
NONE of the later covers — the base pin cover (the cheapest committed one) reaches it exactly. The
`false`s above are not a wall; they are the statement that interval/DBM machinery is the wrong tool
for a symbol-tag guard.

⚑ This CORRECTS the scope of `Deriv/RealGuardAudit2.lean` row #9 ("templater string-span guards" =
RESIDUAL). That row is right about the **Rust** templater's byte/span guards, which are not authored
as a state `Pred` at all. It is NOT right about the **Lean** guarded templater: `noDoubleBraceRE` is
a `PredRE` over `Value` with a pin leaf, squarely IN the base fragment — and this file decides it.

### Emptiness / satisfiability (§2)
* `emptyFix (fixCands noDoubleBraceRE) 64 noDoubleBraceRE = some false` — **SATISFIABLE**. The
  deployed brace-ban is not a brick; the frontier saturates in **11** `≅`-classes over 3 candidate
  frames. (A `some true` here would have meant the templater could never render.)
* satisfiable by a NON-EMPTY slot too (`noDoubleBraceRE ⋒ any ⬝ any*` — `some false`), so the
  `some false` above is not riding the trivial `[]` witness.
* the CONTRADICTORY guard `noDoubleBraceRE ⋒ BB` ("ban `{{` and require `{{`") decides
  **`some true` = EMPTY at all word lengths** — the decision can say "brick", and §4 turns that into
  a theorem: no hole data whatsoever satisfies such a template.

### Equivalence of guard spellings (§3) — the killer app
Each row is `emptyFix` on the symmetric difference, `some true` = the two spellings accept EXACTLY
the same words (every length, infinite alphabet), `some false` = a separating word exists. Every
row is ALSO a `Prop`: the last column is the theorem that carries it.

| edit to the deployed guard | spelling | verdict | `Prop` |
|----------------------------|----------|---------|--------|
| re-associate the `cat` chain | `neg ((any* ⬝ {) ⬝ ({ ⬝ any*))` | **EQUIVALENT** | `assoc_langEq` (hand) |
| conjoin a total guard        | `noDoubleBraceRE ⋒ any*`        | **EQUIVALENT** | `redundant_langEq` (hand) |
| rewrite POSITIVELY (no complement) | `(¬{ ⋓ ({ ⬝ ¬{))* ⬝ (ε ⋓ {)` | **EQUIVALENT** | `pos_langEq` (DECISION) |
| drop the trailing `any*`     | `neg (any* ⬝ { ⬝ {)`            | **NOT EQUIVALENT** | `noTail_not_langEq` (DECISION) |
| "just check it isn't literally `{{`" | `neg ({ ⬝ {)`           | **NOT EQUIVALENT** | `exactly_not_langEq` (hand) + `exactly_not_langEq_fix` (DECISION) |

The two NOT-EQUIVALENT rows are REAL refactor bugs, and §3 exhibits the separating words the
decision predicted: `[data, {, {]` and `[{, {, data]` are REJECTED by the deployed guard and
ACCEPTED by the weakened spellings. §4 turns the second one into a theorem: a concrete hole
assignment that the refactored template calls safe and the deployed template calls unsafe, and
(`pos_edit_preserves`) the positive rewrite into a template-level safety-preservation theorem.

## Resource discipline — MEASURED, not assumed
The Bool route is the default: raw `emptyFix` over the SAME candidate covers the proven decisions
compute (`fixCands`, the `coverOfSymbolic` arm), fired by `#guard` (compiled evaluation). Fuels are
64–256; every frontier saturates in ≤ 20 `≅`-classes.

Where a verdict is worth a `Prop`, it is CROSSED — and the crossing was measured, not feared. The
three decision-carried rows above run `predRE_equivalence_decidable_fix` (EquivalenceFixpoint) at
fuel 256 through `of_decide_eq_{true,false}`, i.e. a real KERNEL reduction of the `≅`-fixpoint on
the symmetric difference. Cost of all three together, `/usr/bin/time -l` over `lake env lean` on
this file (3 runs, warm): **+2.1 s CPU and +0.16 GB peak RSS** — whole file 3.5 s → 5.6 s user,
1.81 GB → 1.97 GB peak, against a bare-import baseline of 1.5 s / 1.78 GB (i.e. nearly all of the
absolute memory is loading mathlib oleans, not the fixpoint). Wall clock is I/O-noise-dominated at
this size (5–9 s either way), so CPU is the honest figure. That is nowhere near the 64GB/20min
hazard an earlier revision of this header ASSERTED it would be — wrong by ~2.5 orders of magnitude
in time and ~2.5 in memory — and the assertion is retracted. The reason it is cheap is structural:
the adaptive worklist saturates in a HANDFUL of `≅`-classes — 13 classes over 13 candidate frames
for the positive spelling (least saturating fuel 171), 17 over 9 frames for refactor #2 (fuel 155),
11 over 9 for refactor #1 (fuel 101) — so the kernel never touches the `emptinessBound` powerset.
Fuel above the saturation point is FREE (the worklist returns as soon as `pending` empties), which
is why 256 is safe to carry.

Still NO `native_decide` anywhere. The two hand proofs (`assoc_langEq`, `redundant_langEq`) remain
independent CONFIRMATIONS of the machine's verdict on their pairs, and `exactly_not_langEq` is
hand-proven with `exactly_not_langEq_fix` agreeing — decision and theorem agree wherever both
exist.

## Semantic resolution
Verdicts are over `Value` words at the `symEq "t"`-pin resolution — the alphabet `HandlebarsGuarded`
itself uses (`braceVal`/`dataVal` are its `Tok` embedding, `tokVal`). They are IN-SLOT statements
about ONE hole's guard, exactly like `guardedSafe`; the cross-junction residual named in
`HandlebarsGuarded` §7 is untouched here.

`#assert_all_clean`, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.SymbolicDifference
import Dregg2.Crypto.HandlebarsGuardedWitness
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsGuardDecision

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.HandlebarsGuarded
open Dregg2.Crypto.Deriv.PredRE
  (derives rigidRE RigidFull derives_cat derives_neg derives_inter derives_sym)

/-! ## §1 IS THE DEPLOYED GUARD IN THE DECIDABLE FRAGMENT? — yes, at the base pin cover.

`noDoubleBraceRE = neg (any* ⬝ braceP ⬝ braceP ⬝ any*)`; its leaves are `tt` (from `PredRE.any`) and
`braceP = symEq "t" 0`. `predAtoms?` accepts both, so the pin/minterm cover applies; the later
interval and DBM covers do NOT (and need not). -/

section Fragment

-- The computed pin set of the deployed guard: ONE field, ONE symbol, mentioned twice.
#guard atomsOfLeaves? (leavesOf noDoubleBraceRE)
         = some [("t", AtomVal.sym 0), ("t", AtomVal.sym 0)]

-- IN the base decidable-leaf fragment, and (for free) `RigidFull`, so the `≅`-dedup applies.
#guard (atomsOfLeaves? (leavesOf noDoubleBraceRE)).isSome
#guard rigidRE noDoubleBraceRE = true

-- OUT of the interval and DBM covers — and this is the RIGHT answer, not a wall: the blocking
-- atom is `symEq "t" 0`, a SYMBOL pin. `predIntervalAtoms?` wants a scalar threshold
-- (`fieldGe`/`fieldLe`/…); `predDifference?` wants a difference coordinate. A symbol tag is
-- neither — it is a pin, which is exactly what the BASE cover enumerates.
#guard scalarRE noDoubleBraceRE = false
#guard differenceRE noDoubleBraceRE = false

/-- The deployed guard, bundled into the decidable-leaf fragment. (`SymbolicMinterms.lean` already
names this bundle as `noDoubleBraceSymbolic`; restated here as this module's entry point.) -/
def nodbSym : SymbolicRE := ⟨noDoubleBraceRE, by rw [IsSymbolic]; rfl⟩

/-- ...and its `RigidFull` side condition, discharged by the fragment collapse
(`rigidRE_of_isSymbolic`) rather than by hand. -/
theorem nodb_rigid : RigidFull noDoubleBraceRE := rigidRE_of_isSymbolic nodbSym.property

/-- The deployed guard as a `RigidSymbolicRE` — the type the RUNNABLE equivalence decision
(`predRE_equivalence_decidable_fix`) consumes. Membership is the whole content of §1, and §3's
three decision-carried equivalence theorems are exactly its consumption: every one of them is
`predRE_equivalence_decidable_fix 256 nodbR _`. -/
def nodbR : RigidSymbolicRE := ⟨nodbSym, nodb_rigid⟩

-- The cover the decision computes for it: 3 candidate frames (no-`t`, and the pin twice over).
#guard (fixCands noDoubleBraceRE).length = 3

end Fragment

/-! ## §2 DECIDING THE DEPLOYED GUARD — is the brace-ban satisfiable?

`emptyFix cands fuel R`: `some false` = the language is NONEMPTY (a real accepting word exists, of
some length), `some true` = EMPTY at ALL lengths, `none` = the worklist did not saturate. -/

section Emptiness

/-- "the slot is non-empty AND obeys the brace-ban" — so the satisfiability verdict below cannot be
riding the trivial empty-word witness. -/
def nodbNonEmpty : PredRE := .inter noDoubleBraceRE (.cat PredRE.any (.star PredRE.any))

/-- The CONTRADICTORY template guard: ban `{{` and require `{{`. A template carrying this at a hole
can never be rendered — §4 proves exactly that. -/
def nodbContra : PredRE := .inter noDoubleBraceRE BB

#guard rigidRE nodbNonEmpty && rigidRE nodbContra
#guard (atomsOfLeaves? (leavesOf nodbNonEmpty)).isSome
         && (atomsOfLeaves? (leavesOf nodbContra)).isSome

-- SATISFIABLE: the deployed brace-ban CAN be met (the templater is not bricked)...
#guard emptyFix (fixCands noDoubleBraceRE) 64 noDoubleBraceRE = some false
-- ...and the fixpoint SATURATES in a handful of `≅`-classes (the whole point of the adaptive
-- worklist — `emptinessBound` on a `neg`-headed machine is astronomical):
#guard ((reachFix (fixCands noDoubleBraceRE) 64 noDoubleBraceRE).map List.length).getD 1000 ≤ 20

-- ...satisfiable by a NON-EMPTY slot as well:
#guard emptyFix (fixCands nodbNonEmpty) 128 nodbNonEmpty = some false

-- ...and the decision can say BRICK: the contradictory guard is EMPTY at every word length.
#guard emptyFix (fixCands nodbContra) 128 nodbContra = some true
#guard ((reachFix (fixCands nodbContra) 128 nodbContra).map List.length).getD 1000 ≤ 20

/-- The `some true` verdict above, INDEPENDENTLY proven (no kernel reduction): `neg BB ⋒ BB` accepts
nothing by pure Boolean algebra of `derives`. Machine verdict and theorem agree — the cross-check
that keeps §2 from being a `#guard` we merely believe. -/
theorem nodbContra_empty : ¬ ∃ w, derives w nodbContra = true := by
  rintro ⟨w, hw⟩
  rw [nodbContra, noDoubleBraceRE, derives_inter, derives_neg] at hw
  cases h : derives w BB with
  | true  => rw [h] at hw; exact Bool.noConfusion hw
  | false => rw [h] at hw; exact Bool.noConfusion hw

end Emptiness

/-! ## §3 THE KILLER APP — did my template edit change what the slot accepts?

Five plausible rewrites of the deployed guard. `emptyFix` on `symDiff` decides each. Three are
faithful; two are silent weakenings, and the separating words are exhibited. -/

section Spellings

/-- Re-associated `cat` chain — the shape a mechanical rewrite produces. -/
def nodbAssoc : PredRE :=
  .neg (.cat (.cat (.star PredRE.any) (.sym braceP)) (.cat (.sym braceP) (.star PredRE.any)))

/-- The deployed guard conjoined with a TOTAL guard (`any*` accepts everything) — the shape a
"defensive" edit produces. -/
def nodbRedundant : PredRE := .inter noDoubleBraceRE (.star PredRE.any)

/-- "not a brace". -/
def nonBraceP : Pred := .not braceP

/-- The POSITIVE spelling of "no `{{`", with NO complement at the regex level: a run of blocks, each
either a non-brace or a brace-followed-by-non-brace, optionally ending in a single brace. A
genuinely different machine for the same language — the hardest of the three faithful rewrites. -/
def nodbPos : PredRE :=
  .cat (.star (.alt (.sym nonBraceP) (.cat (.sym braceP) (.sym nonBraceP))))
       (.alt PredRE.ε (.sym braceP))

/-- REFACTOR BUG #1: the trailing `any*` dropped. Bans a double brace only at the END of the slot. -/
def nodbNoTail : PredRE := .neg (.cat (.star PredRE.any) (.cat (.sym braceP) (.sym braceP)))

/-- REFACTOR BUG #2: "just check the datum isn't literally `{{`". Bans only the two-frame word. -/
def nodbExactly : PredRE := .neg (.cat (.sym braceP) (.sym braceP))

-- All five spellings are in the runnable fragment, so the decision applies to every pair:
#guard rigidRE nodbAssoc && rigidRE nodbRedundant && rigidRE nodbPos
         && rigidRE nodbNoTail && rigidRE nodbExactly
#guard (atomsOfLeaves? (leavesOf nodbAssoc)).isSome
         && (atomsOfLeaves? (leavesOf nodbRedundant)).isSome
         && (atomsOfLeaves? (leavesOf nodbPos)).isSome
         && (atomsOfLeaves? (leavesOf nodbNoTail)).isSome
         && (atomsOfLeaves? (leavesOf nodbExactly)).isSome

/-- The pair's symmetric difference, on the cover the decision itself computes. -/
def diffCands (R S : PredRE) : List Value := fixCands (symDiff R S)

-- ── EQUIVALENT (`some true` = the symmetric difference is EMPTY at every word length) ──
#guard emptyFix (diffCands noDoubleBraceRE nodbAssoc) 256
         (symDiff noDoubleBraceRE nodbAssoc) = some true
#guard emptyFix (diffCands noDoubleBraceRE nodbRedundant) 256
         (symDiff noDoubleBraceRE nodbRedundant) = some true
#guard emptyFix (diffCands noDoubleBraceRE nodbPos) 512
         (symDiff noDoubleBraceRE nodbPos) = some true

-- ── NOT EQUIVALENT (`some false` = a separating word exists) ──
#guard emptyFix (diffCands noDoubleBraceRE nodbNoTail) 256
         (symDiff noDoubleBraceRE nodbNoTail) = some false
#guard emptyFix (diffCands noDoubleBraceRE nodbExactly) 256
         (symDiff noDoubleBraceRE nodbExactly) = some false

-- Every one of those symmetric differences SATURATES in ≤ 20 `≅`-classes (the tractability claim):
#guard ((reachFix (diffCands noDoubleBraceRE nodbPos) 512
          (symDiff noDoubleBraceRE nodbPos)).map List.length).getD 1000 ≤ 20
#guard ((reachFix (diffCands noDoubleBraceRE nodbExactly) 256
          (symDiff noDoubleBraceRE nodbExactly)).map List.length).getD 1000 ≤ 20

/-! ### The separating words the `some false` verdicts predicted, exhibited.

`[data, {, {]` and `[{, {, data]` both contain a `{{`, so the DEPLOYED guard rejects them; each
weakened spelling ACCEPTS one of them. These are the concrete injections the refactor would let
through. (`#guard` on the executable matcher — a `Prop`-level version of the second is `bad_edit`
in §4.) -/

#guard derives [dataVal, braceVal, braceVal] noDoubleBraceRE = false  -- deployed: rejected
#guard derives [dataVal, braceVal, braceVal] nodbExactly     = true   -- refactor #2: ADMITTED
#guard derives [braceVal, braceVal, dataVal] noDoubleBraceRE = false  -- deployed: rejected
#guard derives [braceVal, braceVal, dataVal] nodbNoTail      = true   -- refactor #1: ADMITTED

-- ...and the weakened guards are not vacuous — each still rejects the word it was written for:
#guard derives [braceVal, braceVal] nodbExactly = false
#guard derives [braceVal, braceVal] nodbNoTail  = false

/-! ### Two of the EQUIVALENT verdicts, re-derived by hand.

A `#guard` proves no `Prop`. For the two rewrites whose identity is elementary, the equivalence is
PROVEN — and it agrees with the machine. (`nodbPos ≡ noDoubleBraceRE` is the one that genuinely
needs the decision procedure: it is a different machine, not an algebraic identity.) -/

/-- `cat` is associative for `derives` — the content of the re-association rewrite. -/
theorem derives_cat_assoc (w : List Value) (a b c : PredRE) :
    derives w (.cat (.cat a b) c) = derives w (.cat a (.cat b c)) := by
  have h : derives w (.cat (.cat a b) c) = true ↔ derives w (.cat a (.cat b c)) = true := by
    rw [derives_cat, derives_cat]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      rw [derives_cat] at hu
      obtain ⟨x, y, hxy, hx, hy⟩ := hu
      exact ⟨x, y ++ v, by rw [← List.append_assoc, hxy, huv], hx,
        by rw [derives_cat]; exact ⟨y, v, rfl, hy, hv⟩⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      rw [derives_cat] at hv
      obtain ⟨x, y, hxy, hx, hy⟩ := hv
      exact ⟨u ++ x, y, by rw [List.append_assoc, hxy, huv],
        by rw [derives_cat]; exact ⟨u, x, rfl, hu, hx⟩, hy⟩
  exact Bool.eq_iff_iff.mpr h

/-- **The re-association is FAITHFUL** — proven, matching the `some true` verdict above. -/
theorem assoc_langEq (w : List Value) : derives w nodbAssoc = derives w noDoubleBraceRE := by
  rw [nodbAssoc, noDoubleBraceRE, BB, derives_neg, derives_neg,
    derives_cat_assoc w (PredRE.star PredRE.any) (.sym braceP)
      (.cat (.sym braceP) (.star PredRE.any))]

/-- **Conjoining the total guard is FAITHFUL** — proven, matching the `some true` verdict above.
(`derives_star_any` is `HandlebarsGuarded`'s own: `any*` accepts every word.) -/
theorem redundant_langEq (w : List Value) :
    derives w nodbRedundant = derives w noDoubleBraceRE := by
  rw [nodbRedundant, derives_inter, derives_star_any, Bool.and_true]

/-! ### And the `some false` verdict on refactor #2, re-derived by hand. -/

/-- The deployed guard REJECTS `[data, {, {]` (it contains adjacent braces), through the
already-proven matcher characterization `noDoubleBraceRE_via_matcher`. -/
theorem deployed_rejects_sep : derives [dataVal, braceVal, braceVal] noDoubleBraceRE = false := by
  have hadj : ¬ ¬ hasAdjB [dataVal, braceVal, braceVal] := fun hn =>
    hn ⟨[dataVal], braceVal, braceVal, [], rfl, leaf_braceP_brace, leaf_braceP_brace⟩
  cases hd : derives [dataVal, braceVal, braceVal] noDoubleBraceRE with
  | true  => exact absurd ((noDoubleBraceRE_via_matcher _).mp hd) hadj
  | false => rfl

/-- The refactored guard ACCEPTS the same word: `cat (sym braceP) (sym braceP)` matches only
two-frame words, and this one has three. A pure length argument. -/
theorem refactor_admits_sep : derives [dataVal, braceVal, braceVal] nodbExactly = true := by
  rw [nodbExactly, derives_neg, Bool.not_eq_true']
  cases hc : derives [dataVal, braceVal, braceVal] (PredRE.cat (.sym braceP) (.sym braceP)) with
  | false => rfl
  | true =>
      obtain ⟨u, v, huv, hu, hv⟩ := (derives_cat _ _ _).mp hc
      rw [derives_sym] at hu hv
      obtain ⟨x, rfl, _⟩ := hu
      obtain ⟨y, rfl, _⟩ := hv
      exact absurd (congrArg List.length huv) (by simp)

/-- **The refactor is a REAL weakening** — proven, matching the `some false` verdict above: the two
spellings disagree on `[data, {, {]`. -/
theorem exactly_not_langEq : ¬ ∀ w, derives w noDoubleBraceRE = derives w nodbExactly := by
  intro h
  have hw := h [dataVal, braceVal, braceVal]
  rw [deployed_rejects_sep, refactor_admits_sep] at hw
  exact Bool.noConfusion hw

/-! ### The remaining verdicts, CROSSED from `#guard` to `Prop` by the running decision.

The positive spelling is the one with no algebraic identity to hand-prove — it is a genuinely
different machine — and dropping the trailing `any*` likewise had only a `#guard`. Both are lifted
here by RUNNING `predRE_equivalence_decidable_fix` (EquivalenceFixpoint §2) in the kernel: it is
`emptyFix` on the symmetric difference (the very `#guard`s above) composed with the proven
`emptyFix_some_iff` and `langEq_iff_symDiff_empty`, so `of_decide_eq_{true,false}` yields the
`∀ w`-statement itself. MEASURED cost, all three: +2.1–2.4 s CPU / +0.16–0.19 GB (an independent verify's 3 warm runs averaged 5.81 s / 1.99 GB whole-file vs the 5.62 s / 1.97 GB recorded here — same order, ~12% above; treat these as a range, not a point) peak RSS — see the header's
resource note, which used to assert the opposite without measuring. -/

/-- The positive (complement-free) spelling, bundled into the runnable-equivalence fragment. -/
def nodbPosR : RigidSymbolicRE :=
  ⟨⟨nodbPos, by rw [IsSymbolic]; rfl⟩, show rigidRE nodbPos = true from rfl⟩

/-- REFACTOR BUG #1, bundled. -/
def nodbNoTailR : RigidSymbolicRE :=
  ⟨⟨nodbNoTail, by rw [IsSymbolic]; rfl⟩, show rigidRE nodbNoTail = true from rfl⟩

/-- REFACTOR BUG #2, bundled. -/
def nodbExactlyR : RigidSymbolicRE :=
  ⟨⟨nodbExactly, by rw [IsSymbolic]; rfl⟩, show rigidRE nodbExactly = true from rfl⟩

set_option maxRecDepth 65536 in
/-- **The POSITIVE rewrite is FAITHFUL — as a `Prop`.** The deployed brace-ban and its
complement-free spelling accept EXACTLY the same `Value` words, at EVERY length, over the infinite
alphabet. No hand proof relates these two machines; the fixpoint decision does, in 13 `≅`-classes.
This is the verdict this file previously left at `#guard` resolution. -/
theorem pos_langEq : ∀ w, derives w noDoubleBraceRE = derives w nodbPos :=
  @of_decide_eq_true _ (predRE_equivalence_decidable_fix 256 nodbR nodbPosR) (by rfl)

/-- **Dropping the trailing `any*` is a REAL weakening — as a `Prop`.** Some word separates the
deployed guard from refactor #1 (the `#guard`s exhibit `[{, {, data]`). -/
theorem noTail_not_langEq : ¬ ∀ w, derives w noDoubleBraceRE = derives w nodbNoTail :=
  @of_decide_eq_false _ (predRE_equivalence_decidable_fix 256 nodbR nodbNoTailR) (by rfl)

set_option maxRecDepth 65536 in
/-- Refactor #2's separation, re-derived by the DECISION — the same statement
`exactly_not_langEq` proves by hand from the exhibited word. Machine and theorem agree, in both
directions this time (the hand proof exhibits a witness; the decision quantifies over all
words). -/
theorem exactly_not_langEq_fix : ¬ ∀ w, derives w noDoubleBraceRE = derives w nodbExactly :=
  @of_decide_eq_false _ (predRE_equivalence_decidable_fix 256 nodbR nodbExactlyR) (by rfl)

end Spellings

/-! ## §4 THE TEMPLATER PAYOFF — what the two decisions MEAN for a template.

The decisions above are about `PredRE` languages. These two theorems are the bridge to
`HandlebarsGuarded`'s `guardedSafe` / `guardedToGrammar`: what a satisfiability verdict and an
equivalence verdict say about the TEMPLATE. -/

section Templates

/-- **`no_data_for_empty_guard`** — an EMPTY hole guard bricks the template: if some hole of `T`
carries a guard whose language is empty, then NO data assignment whatsoever is `guardedSafe`, hence
`guarded_render_mem_language` is never applicable to `T`. This is the `Prop` behind §2's `some true`
pole: the emptiness decision is a BRICK DETECTOR for templates. -/
theorem no_data_for_empty_guard (T : GuardedTemplate) (id : Nat) (g : PredRE)
    (hmem : GSeg.hole id g ∈ T.segments) (hempty : ¬ ∃ w, derives w g = true) :
    ∀ d : Nat → List Value, ¬ guardedSafe T d :=
  fun d hsafe => hempty ⟨d id, hsafe id g hmem⟩

/-- **`guardedSafe_swap`** — an EQUIVALENCE verdict licenses the template edit: if `g` and `g'`
accept the same words, then every template `T'` whose holes are `T`'s holes with (some) `g`
rewritten to `g'` accepts exactly the data assignments `T` did. This is the `Prop` behind §3's
`some true` pole — "did my edit change what it accepts?", answered. -/
theorem guardedSafe_swap {T T' : GuardedTemplate} {g g' : PredRE}
    (heq : ∀ w, derives w g = derives w g')
    (hstruct : ∀ id h, GSeg.hole id h ∈ T'.segments →
      GSeg.hole id h ∈ T.segments ∨ (h = g' ∧ GSeg.hole id g ∈ T.segments))
    {d : Nat → List Value} (hsafe : guardedSafe T d) : guardedSafe T' d := by
  intro id h hmem
  rcases hstruct id h hmem with hm | ⟨rfl, hm⟩
  · exact hsafe id h hm
  · rw [← heq]; exact hsafe id g hm

/-! ### The three templates: deployed, faithfully edited, badly edited. -/

/-- The deployed shape: a literal, then a hole under the brace-ban. -/
def strictT : GuardedTemplate := ⟨[GSeg.lit [dataVal], GSeg.hole 0 noDoubleBraceRE]⟩

/-- The SAME template after the faithful re-association edit (§3, `some true`). -/
def assocT : GuardedTemplate := ⟨[GSeg.lit [dataVal], GSeg.hole 0 nodbAssoc]⟩

/-- The same template after the BAD edit (§3, `some false`). -/
def exactlyT : GuardedTemplate := ⟨[GSeg.lit [dataVal], GSeg.hole 0 nodbExactly]⟩

/-- A template that can NEVER be rendered: its hole carries the contradictory guard of §2. -/
def brickT : GuardedTemplate := ⟨[GSeg.lit [dataVal], GSeg.hole 0 nodbContra]⟩

/-- **The faithful edit is safe, at the TEMPLATE level**: every data assignment the deployed
template accepted, the re-associated template still accepts — and the rendered output is
unchanged (`render` reads the hole's `id`, not its guard). The equivalence verdict, cashed. -/
theorem assoc_edit_preserves (d : Nat → List Value) (hsafe : guardedSafe strictT d) :
    guardedSafe assocT d ∧ render assocT d = render strictT d := by
  refine ⟨guardedSafe_swap (g := noDoubleBraceRE) (g' := nodbAssoc)
    (fun w => (assoc_langEq w).symm) ?_ hsafe, rfl⟩
  intro id h hmem
  simp only [assocT, List.mem_cons, List.not_mem_nil, or_false, GSeg.hole.injEq,
             reduceCtorEq, false_or] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  exact Or.inr ⟨rfl, by simp [strictT]⟩

/-- The same template after the POSITIVE (complement-free) rewrite — the edit whose faithfulness
only the fixpoint decision establishes (§3, `pos_langEq`). -/
def posT : GuardedTemplate := ⟨[GSeg.lit [dataVal], GSeg.hole 0 nodbPos]⟩

/-- **The killer app, CASHED at the template level**: rewriting the deployed guard into its
complement-free spelling preserves every safe data assignment and every rendered output. Unlike
`assoc_edit_preserves`, no algebraic identity backs this — it rides `pos_langEq`, i.e. the
`≅`-fixpoint equivalence decision run in the kernel. This is what a template author actually asked
for: "did my edit change what the slot accepts?", answered as a theorem. -/
theorem pos_edit_preserves (d : Nat → List Value) (hsafe : guardedSafe strictT d) :
    guardedSafe posT d ∧ render posT d = render strictT d := by
  refine ⟨guardedSafe_swap (g := noDoubleBraceRE) (g' := nodbPos) pos_langEq ?_ hsafe, rfl⟩
  intro id h hmem
  simp only [posT, List.mem_cons, List.not_mem_nil, or_false, GSeg.hole.injEq,
             reduceCtorEq, false_or] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  exact Or.inr ⟨rfl, by simp [strictT]⟩

/-- The hole datum that separates the two spellings: a `{{`-bearing slot. -/
def sepD : Nat → List Value := fun _ => [dataVal, braceVal, braceVal]

/-- **The bad edit ADMITS AN INJECTION** — the `some false` verdict, cashed at the template level:
`sepD` fills the hole with a `{{`-bearing datum that the REFACTORED template calls safe and the
DEPLOYED template rejects. The equivalence decision flagged this pair; here is the witness. -/
theorem bad_edit_admits_injection :
    guardedSafe exactlyT sepD ∧ ¬ guardedSafe strictT sepD := by
  constructor
  · intro id h hmem
    simp only [exactlyT, List.mem_cons, List.not_mem_nil, or_false, GSeg.hole.injEq,
               reduceCtorEq, false_or] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact refactor_admits_sep
  · intro hsafe
    have := hsafe 0 noDoubleBraceRE (by simp [strictT])
    rw [show derives (sepD 0) noDoubleBraceRE = false from deployed_rejects_sep] at this
    exact Bool.noConfusion this

/-- **The brick, at the template level**: `brickT` has NO safe data assignment at all — so
`guarded_render_mem_language` can never fire for it, and (through `guardedVerify_iff`) no
certificate for it can ever be accepted. The emptiness decision's `some true` pole, cashed. -/
theorem brickT_unrenderable : ∀ d : Nat → List Value, ¬ guardedSafe brickT d :=
  no_data_for_empty_guard brickT 0 nodbContra (by simp [brickT]) nodbContra_empty

/-- ...and therefore no per-hole certificate for `brickT` is ever accepted by the verifier of
`HandlebarsGuardedWitness` — the guard-acceptance replay cannot pass on an unsatisfiable guard. -/
theorem brickT_no_accepting_certificate (d : Nat → List Value) :
    HandlebarsGuardedWitness.guardedVerify brickT
      (HandlebarsGuardedWitness.guardedWitness brickT d) = false := by
  cases h : HandlebarsGuardedWitness.guardedVerify brickT
      (HandlebarsGuardedWitness.guardedWitness brickT d) with
  | false => rfl
  | true =>
      exact absurd ((HandlebarsGuardedWitness.guardedVerify_iff brickT d).mp h)
        (brickT_unrenderable d)

end Templates

/-! ## §5 Axiom hygiene. -/

#assert_all_clean [
  nodb_rigid,
  nodbContra_empty,
  derives_cat_assoc, assoc_langEq, redundant_langEq,
  deployed_rejects_sep, refactor_admits_sep, exactly_not_langEq,
  pos_langEq, noTail_not_langEq, exactly_not_langEq_fix,
  no_data_for_empty_guard, guardedSafe_swap,
  assoc_edit_preserves, pos_edit_preserves, bad_edit_admits_injection,
  brickT_unrenderable, brickT_no_accepting_certificate
]

/-! ## §6 RESIDUALS — named precisely, not `sorry`-ed.

* **(machine-verdict → `Prop`: CROSSED, and the old cost claim RETRACTED)** An earlier revision of
  this section said the kernel reduction needed for the crossing "is exactly the 64GB/20min hazard"
  and refused to run it, leaving `nodbPos ≡ noDoubleBraceRE` at `#guard` resolution. That was an
  ASSERTED cost, never measured, and it was wrong. Measured (`/usr/bin/time -l`, this file, 3 warm
  runs): crossing ALL THREE remaining verdicts costs **+2.1–2.4 s CPU / +0.16–0.19 GB (an independent verify's 3 warm runs averaged 5.81 s / 1.99 GB whole-file vs the 5.62 s / 1.97 GB recorded here — same order, ~12% above; treat these as a range, not a point) peak RSS** — whole
  file 3.5 s → 5.6 s user and 1.81 GB → 1.97 GB, against a 1.5 s / 1.78 GB bare-import baseline, so
  the memory is mathlib oleans either way. ~2.5 orders of magnitude below the claimed hazard on
  both axes (20 min → 2.1 s; 64 GB → 0.16 GB incremental) — and a deliberately FALSE variant of the
  same reduction (claiming `nodbNoTail` equivalent) is REJECTED by `rfl`, so the crossing is doing
  real discriminating work, not reducing to a tautology. So §3 now
  crosses them: `pos_langEq`, `noTail_not_langEq`, `exactly_not_langEq_fix` are `Prop`s produced by
  `predRE_equivalence_decidable_fix 256 nodbR _` (i.e. `emptyFix_some_iff` ∘
  `langEq_iff_symDiff_empty`, kernel-reduced), and `pos_edit_preserves` cashes the positive rewrite
  at the template level. The residual that REMAINS is narrow and structural: cheapness here is a
  property of THESE machines (13 `≅`-classes, 13 candidate frames, saturating fuel ≤ 171), not a
  general bound — the missing counting step in `SymbolicFixpoint`'s termination note (fuel
  `(emptinessBound R + 1) * (|V| + 1) + 1` suffices) is still unproven, so a bigger guard's
  crossing must be MEASURED again rather than assumed cheap. Measure, do not assert, in either
  direction.

* **(cover fidelity)** `fixCands` mirrors the `coverOfSymbolic` arm of the decision instances, so the
  raw `emptyFix` guards exercise the SAME search the instances would. It contains duplicate
  candidates (the pin `("t", sym 0)` is mentioned twice, so `atomCands` emits it twice); that costs
  branching factor, never correctness — the cover only has to CONTAIN a witness per minterm.

* **(in-slot, as always)** Every verdict is about ONE hole's guard language. The cross-junction
  breakout named in `HandlebarsGuarded` §7 (a guard-conforming slot abutting a literal can still
  form a delimiter across the junction) is a property of the CONCATENATION, not of any single guard,
  and no per-guard decision can see it.

* **(`RealGuardAudit2` row #9, re-scoped)** That row's RESIDUAL verdict is correct for the Rust
  templater's byte/span guards and for `RoleCapMap::holds`, neither of which is a state `Pred`. It
  over-reached in listing "`Dregg2/Crypto/HandlebarsGuarded*.lean`" as residual: the Lean guarded
  templater's guards ARE `PredRE` over `Value` with pin leaves, and this file decides the deployed
  one. The honest residual there is the RUST side.
-/

end Dregg2.Crypto.HandlebarsGuardDecision
