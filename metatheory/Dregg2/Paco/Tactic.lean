import Dregg2.Paco.Basic
import Dregg2.Paco.GPaco
import Dregg2.Paco.UpTo.GPacoClo
import Dregg2.Paco.Companion

/-!
# Paco Tactics

This module provides tactics for working with parametrized coinduction (paco).

## Quick Reference

| Tactic | Goal/Hyp | Effect |
|--------|----------|--------|
| `pcofix ih` | `⊢ paco F r x y` | Start coinduction, get hypothesis `ih` |
| `pfold` | `⊢ paco F r x y` | Convert to `⊢ F (upaco F r) x y` |
| `pfold_reverse` | `⊢ F (upaco F r) x y` | Convert to `⊢ paco F r x y` |
| `punfold h` | `h : paco F r x y` | Convert to `h : F (upaco F r) x y` |
| `punfold_reverse h` | `h : F (upaco F r) x y` | Convert to `h : paco F r x y` |
| `pstep` | `⊢ upaco F r x y` | Go left (paco side), then fold |
| `pbase` | `⊢ upaco F r x y` | Go right (use accumulator `r`) |
| `pclearbot` | anywhere | Simplify `upaco F ⊥` to `paco F ⊥` |
| `pdestruct h` | `h : paco F r x y` | Unfold, destruct, clear bot |
| `pinversion h` | `h : paco F r x y` | Like pdestruct, preserves original |
| `pmonauto` | `⊢ Monotone2 F` | Auto-prove monotonicity |
| `gcofix ih` | `⊢ gpaco_clo F clo r rg x y` | Start gpaco_clo coinduction |

## Typical Proof Structure

```lean
theorem my_bisim : paco Bisim ⊥ p q := by
  pcofix ih           -- Start coinduction
  · trivial           -- Prove witness: R p q
  · pfold             -- Prove F-step
    constructor       -- Destruct F structure
    · pstep; ...      -- Recursive case: use coinduction
    · pbase; ...      -- Base case: use accumulator
```

## See Also

- `ginit`, `gstep`, `gbase`, `gfinal` for up-to reasoning with closures
- `paco_acc` for accumulation (absorbing nested paco)

## References

- [Coq paco tactics](https://github.com/snu-sf/paco/blob/master/src/pacotac.v)
- [Paco paper (POPL 2013)](https://plv.mpi-sws.org/paco/)
-/

namespace Paco

/-!
## Simp Lemmas
-/

/-- Simplifies `paco F ⊥` to the ordinary greatest fixed point. -/
@[simp] theorem paco_sup_bot_eq {α : Type*} (F : MonoRel α) : paco F ⊥ = F.toOrderHom.gfp := paco_bot F

/-!
## Core Tactics: Folding and Unfolding

These tactics convert between `paco F r` and `F (upaco F r)`.
-/

/-- Unfold a paco hypothesis to expose the F-structure.

## Signature
`punfold h` where `h : paco F r x y`

## Effect
Replaces `h` with `h : F (upaco F r) x y`

## Example
```lean
example (h : paco Bisim r p q) : Bisim (upaco Bisim r) p q := by
  punfold h
  exact h
```

## See Also
- `pfold`: the reverse operation (for goals)
- `pdestruct`: unfold + destruct in one step
-/
macro "punfold" h:ident : tactic =>
  `(tactic| first
    | (have $h := Paco.paco_unfold _ _ _ _ $h)
    | fail "punfold: hypothesis must have type `paco F r x y`")

/-- Reverse of punfold: fold F-structure hypothesis back to paco.

## Signature
`punfold_reverse h` where `h : F (upaco F r) x y`

## Effect
Replaces `h` with `h : paco F r x y`

## When to Use
When you have an unfolded hypothesis and want to fold it back to paco form
(e.g., to pass to a lemma expecting `paco`).

## Example
```lean
example (h : F (upaco F r) x y) : paco F r x y := by
  punfold_reverse h
  exact h  -- h is now `paco F r x y`
```

## See Also
- `punfold`: the reverse operation
- `pfold_reverse`: the goal version
-/
macro "punfold_reverse" h:ident : tactic =>
  `(tactic| first
    | (have $h := Paco.paco_fold _ _ _ _ $h)
    | fail "punfold_reverse: hypothesis must have type `F (upaco F r) x y`")

/-- Fold F-structure into a paco goal.

## Signature
`pfold` when goal is `⊢ paco F r x y`

## Effect
Converts goal to `⊢ F (upaco F r) x y`

## Example
```lean
example : paco Bisim r p q := by
  pfold
  -- Goal is now: Bisim (upaco Bisim r) p q
  constructor <;> pstep <;> ...
```

## See Also
- `punfold`: the reverse operation (for hypotheses)
- `pfold_reverse`: the inverse (F-structure → paco goal)
- `pstep`: when goal is `upaco` instead of `paco`
-/
macro "pfold" : tactic =>
  `(tactic| apply Paco.paco_fold)

/-- Reverse of pfold: convert F-structure goal to paco goal.

## Signature
`pfold_reverse` when goal is `⊢ F (upaco F r) x y`

## Effect
Converts goal to `⊢ paco F r x y`

## When to Use
When you have an F-structure goal but want to prove it via paco reasoning
(e.g., to use `pcofix`).

## Example
```lean
example : F (upaco F r) x y := by
  pfold_reverse
  -- Goal is now: paco F r x y
  pcofix ih
  ...
```

## See Also
- `pfold`: the reverse operation
- `punfold_reverse`: the hypothesis version
-/
macro "pfold_reverse" : tactic =>
  `(tactic| apply Paco.paco_unfold)

/-- Unfold a gpaco hypothesis to expose structure.

## Signature
`gpunfold h` where `h : gpaco F r g x y`

## Effect
Replaces `h` with `h : F (gupaco F r g) x y ∨ r x y`

## See Also
- `gpfold`: the reverse operation (for goals)
-/
macro "gpunfold" h:ident : tactic =>
  `(tactic| first
    | (have $h := Paco.gpaco_unfold _ _ _ _ _ $h)
    | fail "gpunfold: expected hypothesis of type `gpaco F r g x y`")

/-- Fold F-structure into a gpaco goal.

## Signature
`gpfold` when goal is `⊢ gpaco F r g x y`

## Effect
Converts goal to `⊢ F (gupaco F r g) x y`
-/
macro "gpfold" : tactic =>
  `(tactic| apply Paco.gpaco_fold)

/-!
## Progress Tactics

Use these when your goal is `upaco F r x y` (a disjunction `paco F r x y ∨ r x y`).
-/

/-- Take a coinductive step (go into the paco side of upaco).

## Signature
`pstep` when goal is `⊢ upaco F r x y`

## Effect
1. Chooses left side of `paco F r x y ∨ r x y`
2. Folds to `⊢ F (upaco F r) x y`

## When to Use
Use `pstep` for the **recursive case** where you need to apply the generating
function F and may use the coinductive hypothesis.

## Example
```lean
example : upaco Bisim r p q := by
  pstep
  -- Goal: Bisim (upaco Bisim r) p q
  constructor
  · ...  -- prove left component
  · ...  -- prove right component
```

## See Also
- `pbase`: for using the accumulator instead
- `pfold`: when goal is `paco` not `upaco`
-/
macro "pstep" : tactic =>
  `(tactic| first
    | (left; apply Paco.paco_fold)
    | fail "pstep: expected goal `upaco F r x y` (i.e., `paco F r x y ∨ r x y`). If goal is `paco F r x y`, use `pfold` instead.")

/-- Use the accumulator relation (go into the r side of upaco).

## Signature
`pbase` when goal is `⊢ upaco F r x y`

## Effect
Chooses right side, converting goal to `⊢ r x y`

## When to Use
Use `pbase` for the **base case** where you already have `r x y` in context
(typically from a previous proof or the coinductive hypothesis).

## Example
```lean
example (hr : r p q) : upaco Bisim r p q := by
  pbase
  exact hr
```

## See Also
- `pstep`: for the recursive case
-/
macro "pbase" : tactic =>
  `(tactic| first
    | right
    | fail "pbase: expected goal `upaco F r x y` (i.e., `paco F r x y ∨ r x y`)")

/-- Simplify `upaco F ⊥` to `paco F ⊥` everywhere.

## Signature
`pclearbot` (applies to goal and all hypotheses)

## Effect
Since `⊥` (the empty relation) contributes nothing to the disjunction,
`upaco F ⊥ = paco F ⊥ ∨ ⊥ = paco F ⊥`.

## When to Use
After `pcofix ih` when proving `paco F ⊥ x y`, the coinductive hypothesis
gives you `upaco F ⊥`. Use `pclearbot` to simplify.

## Example
```lean
example (h : upaco Bisim ⊥ p q) : paco Bisim ⊥ p q := by
  pclearbot
  exact h  -- h is now `paco Bisim ⊥ p q`
```
-/
macro "pclearbot" : tactic =>
  `(tactic| simp only [Paco.upaco_bot])

/-- Simplify `upaco F ⊥` to `paco F ⊥` in a specific hypothesis.

## Signature
`pclearbot_hyp h`

## See Also
- `pclearbot`: applies to everything
-/
macro "pclearbot_hyp" h:ident : tactic =>
  `(tactic| simp only [Paco.upaco_bot] at $h:ident)

/-!
## Coinduction Tactics

These tactics initiate a coinductive proof by applying the coinduction principle.
-/

/-- Start a coinduction proof.

## Signature
`pcofix ih` when goal is `⊢ paco F r x y`

## Effect
Applies the coinduction principle, creating:
1. **Witness goal**: Prove `R x y` for some witness relation R
2. **Step goal**: Prove `F (R ⊔ r) a b` given `ih : R a b`

The name `ih` is bound to the coinductive hypothesis in the step goal.

## Example
```lean
theorem stream_eq : paco StreamEq ⊥ s t := by
  pcofix ih
  · -- Goal 1: R s t (witness that s, t are in R)
    trivial  -- or construct the witness
  · -- Goal 2: StreamEq (R ⊔ ⊥) a b, given ih : R a b
    constructor
    · exact head_eq  -- prove heads equal
    · pstep          -- recursive case for tails
      exact ih_tail
```

## Understanding the Coinduction Principle
The coinduction principle says: to prove `paco F r x y`, find a relation R such that:
1. `R x y` holds (witness)
2. `R` is a post-fixpoint: `R ≤ F (R ⊔ r)` (step)

Then by Knaster-Tarski, `R ≤ gfp (λ X. F (X ⊔ r)) = paco F r`.

## See Also
- `pfold`: after `pcofix`, use `pfold` to work on the F-step
- `pstep`/`pbase`: for recursive vs base cases in the step
-/
macro "pcofix" ih:ident : tactic =>
  `(tactic| (apply Paco.paco_coind _ ?R _; intro _ _ $ih))

/-- Low-level coinduction with explicit control over naming.

## Signature
`pcofix' ih`

## Effect
Like `pcofix` but uses `refine` for more control. The witness relation
becomes a metavariable `?R` that you can instantiate explicitly.

## See Also
- `pcofix`: the standard version
-/
macro "pcofix'" ih:ident : tactic =>
  `(tactic| (
    refine Paco.paco_coind _ ?_ _ ?_ ?_
    intro _ _ $ih
  ))

/-- Start a generalized paco coinduction proof.

## Signature
`gpcofix ih` when goal is `⊢ gpaco F r g x y`

## Effect
Like `pcofix` but for generalized paco with guard parameter `g`.

## See Also
- `pcofix`: for standard paco
- `gpfold`, `gpunfold`: for working with gpaco hypotheses
-/
macro "gpcofix" ih:ident : tactic =>
  `(tactic| (apply Paco.gpaco_coind _ ?R _ _ _ _; intro _ _ $ih))

/-!
## Accumulation Tactics

These tactics handle "nested" paco, absorbing inner paco into the parameter.
This is key for compositional proofs where lemmas return paco results.
-/

/-- Absorb nested paco into the parameter.

## Signature
`paco_acc` when goal is `⊢ paco F (paco F r) x y`

## Effect
Converts goal to `⊢ paco F r x y`

## When to Use
When composing lemmas that each return `paco F r`, the composition gives
`paco F (paco F r)`. Use `paco_acc` to flatten this.

## Example
```lean
-- Given: lemma1 : paco F r a b
--        lemma2 : paco F (paco F r) b c  (uses lemma1 in parameter)
-- Goal:  paco F r a c

example : paco F r a c := by
  paco_acc  -- flatten nested paco
  exact lemma2
```

## Alias
Also known as `pmult` in Coq paco.
-/
macro "paco_acc" : tactic =>
  `(tactic| first
    | apply Paco.paco_acc
    | fail "paco_acc: expected goal `paco F (paco F r) x y`")

/-- Absorb nested upaco into the parameter (stronger version).

## Signature
`paco_acc_upaco` when goal is `⊢ paco F (upaco F r) x y`

## Effect
Converts goal to `⊢ paco F r x y`
-/
macro "paco_acc_upaco" : tactic =>
  `(tactic| first
    | apply Paco.paco_acc_upaco
    | fail "paco_acc_upaco: expected goal `paco F (upaco F r) x y`")

/-- Alias for `paco_acc` (Coq naming convention). -/
macro "pmult" : tactic => `(tactic| paco_acc)

/-!
## Monotonicity Tactics

Apply monotonicity to weaken/strengthen the accumulator parameter.
-/

/-- Apply monotonicity of paco in the accumulator.

## Signature
`paco_mon h` where `h : r ≤ s`

## Effect
When goal is `⊢ paco F s x y` and you have `h : r ≤ s`,
converts goal to `⊢ paco F r x y`.

## Example
```lean
example (h : r ≤ s) (hp : paco F r x y) : paco F s x y := by
  paco_mon h
  exact hp
```
-/
macro "paco_mon" h:term : tactic =>
  `(tactic| apply Paco.paco_mon _ $h)

/-- Apply monotonicity of upaco in the accumulator.

## Signature
`upaco_mon h` where `h : r ≤ s`

## Effect
When goal is `⊢ upaco F s x y` and you have `h : r ≤ s`,
converts goal to `⊢ upaco F r x y`.
-/
macro "upaco_mon" h:term : tactic =>
  `(tactic| apply Paco.upaco_mon _ $h)

/-!
## GPaco with Closures Tactics

These tactics work with `gpaco_clo` and `gupaco_clo` for **up-to reasoning**.
Up-to techniques allow more aggressive use of the coinductive hypothesis
by reasoning "up to" some closure operator (e.g., reflexivity, transitivity).

### Typical Up-To Proof Structure

```lean
theorem bisim_upto : paco Bisim ⊥ p q := by
  ginit                    -- enter gpaco_clo with companion
  gstep                    -- take F-step
  constructor
  · gclo                   -- apply closure (e.g., transitivity)
    exact intermediate_step
  · gbase                  -- use base relation
    exact base_case
```
-/

/-- Initialize an up-to proof using the companion closure.

## Signature
`ginit` when goal is `⊢ paco F r x y`

## Effect
Converts goal to `⊢ gupaco_clo F (companion F) r x y`

## When to Use
Use `ginit` to enter "up-to mode" where you can apply closure operators
during coinduction. The companion is the greatest compatible closure,
so it subsumes all sound up-to techniques.

## Example
```lean
example : paco Bisim ⊥ p q := by
  ginit  -- now in up-to mode
  gstep  -- take a step
  ...
```

## See Also
- `gstep`: take an F-step in up-to mode
- `gclo`: apply the closure operator
-/
macro "ginit" : tactic =>
  `(tactic| first
    | apply Paco.paco_le_gpaco_clo
    | fail "ginit: expected goal `paco F r x y`")

/-- Take one F-step in an up-to proof.

## Signature
`gstep` when goal is `⊢ gpaco_clo F clo r rg x y`

## Effect
Converts goal to `⊢ F (gupaco_clo F clo r) x y`

## When to Use
After `ginit`, use `gstep` to make progress by providing the F-structure.
The recursive positions get `gupaco_clo` which allows closure applications.

## See Also
- `gbase`: use the base relation instead of stepping
- `gclo`: apply the closure operator
-/
macro "gstep" : tactic =>
  `(tactic| first
    | (apply Paco.rclo.base; left; apply Paco.paco_fold)
    | fail "gstep: expected goal `gpaco_clo F clo r rg x y`")

/-- Use the base relation in an up-to proof.

## Signature
`gbase` when goal is `⊢ gpaco_clo F clo r rg x y`

## Effect
Converts goal to `⊢ r x y`

## When to Use
For base cases where you have `r x y` directly.
-/
macro "gbase" : tactic =>
  `(tactic| first
    | apply Paco.r_le_gpaco_clo
    | fail "gbase: expected goal `gpaco_clo F clo r rg x y`")

/-- Conclude an up-to proof by reducing to standard paco.

## Signature
`gfinal` when goal is `⊢ gpaco_clo F clo r rg x y`

## Effect
Applies `gpaco_clo_final`, requiring the closure to be compatible with F.

## When to Use
When you have a standard `paco F (r ⊔ rg) x y` and want to embed it
into `gpaco_clo`.
-/
macro "gfinal" : tactic =>
  `(tactic| first
    | apply Paco.gpaco_clo_final
    | fail "gfinal: expected goal `gpaco_clo F clo r rg x y`. Make sure the closure is compatible.")

/-- Apply the closure operator in an up-to proof.

## Signature
`gclo` when goal involves `rclo clo`

## Effect
Introduces a closure application, allowing you to use up-to reasoning.

## Example
```lean
-- Using up-to transitivity
example : gpaco_clo F transClo r rg x z := by
  gclo  -- apply transitive closure
  · exact step1  -- x to y
  · exact step2  -- y to z
```

## See Also
- `ginit`: enter up-to mode
- `gstep`: take an F-step
-/
macro "gclo" : tactic =>
  `(tactic| apply Paco.rclo.clo)

/-!
## GPaco_clo Coinduction Tactics
-/

/-- Start a gpaco_clo coinduction proof with closure accumulation.

## Signature
`gcofix ih` when goal is `⊢ gpaco_clo F clo r rg x y`

## Effect
Applies the full coinduction principle for gpaco_clo (`gpaco_clo_coind`),
creating goals:
1. **INC goal**: `⊢ rg ≤ rr` (the guard is contained in the extension)
2. **CIH goal**: `⊢ R ≤ rr` (the witness is contained in the extension)
3. **Step goal**: `⊢ R x y → gpaco_clo F clo r rr x y` with `ih : R a b`
4. **Witness goal**: `⊢ R x y` (show the witness contains the target)

The name `ih` is bound to the coinductive hypothesis in the step goal.

## Understanding the Principle
To prove `l ≤ gpaco_clo F clo r rg`, we find a witness `R` such that
for any `rr` extending both `rg` (INC) and `R` (CIH), we have `R ≤ gpaco_clo F clo r rr`.

## Example
```lean
theorem upTo_bisim : gpaco_clo Bisim transClo ⊥ ⊥ p q := by
  gcofix ih
  · -- Goal: R p q (witness membership)
    trivial
  · -- Goal: R a b → gpaco_clo Bisim transClo ⊥ rr a b
    intro hR
    gstep  -- take F-step
    constructor
    · gclo  -- apply closure
      ...
    · ...
```

## See Also
- `gpcofix`: for simpler gpaco without closure
- `pcofix`: for basic paco
- `ginit`, `gstep`, `gclo`: for working with gpaco_clo
-/
macro "gcofix" ih:ident : tactic =>
  `(tactic| (apply Paco.gpaco_clo_coind' _ _ _ _ ?R; intro _rr _INC _CIH _ _ $ih))

/-- Low-level gpaco_clo coinduction using the simpler cofix principle.

## Signature
`gcofix' ih` when goal is `⊢ gpaco_clo F clo r rg x y`

## Effect
Applies `gpaco_clo_cofix` which requires:
- A witness relation R with R x y
- Proof that R ≤ F (rclo clo (R ⊔ upaco (F ∘ rclo clo) (rg ⊔ r))) ⊔ r

This is more direct but less flexible than `gcofix`.

## See Also
- `gcofix`: for the full coinduction principle with closure accumulation
-/
macro "gcofix'" ih:ident : tactic =>
  `(tactic| (apply Paco.gpaco_clo_cofix _ _ _ _ ?R _; intro _ _ $ih))

/-!
## Monotonicity Automation
-/

/-- Automatically prove monotonicity of relation transformers.

## Signature
`pmonauto` when goal is `Monotone2 F` or `∀ R S, R ≤ S → F R ≤ F S`

## Effect
Tries to prove monotonicity automatically using common patterns:
1. Introduces all universally quantified variables
2. Destructs inductive hypotheses
3. Uses `assumption`, monotonicity lemmas, or `aesop`

## When to Use
When defining a `MonoRel` and need to prove the `mono` field.

## Example
```lean
def MyRel : MonoRel α where
  F := fun R x y => R x y ∨ x = y
  mono := by pmonauto
```

## Limitations
Works for simple monotonicity goals. For complex cases, may need manual proof.

## See Also
- `MonoRel`: bundled monotone relation transformer
- `Monotone2`: the monotonicity property
-/
macro "pmonauto" : tactic =>
  `(tactic| (
    intro R S hRS x y hF
    first
    -- Simple cases: inductive with monotone subterms
    | (cases hF with
       | inl h => left; exact hRS x y h
       | inr h => right; exact h)
    | (cases hF with
       | inl h => left; exact h
       | inr h => right; exact hRS x y h)
    | (cases hF with
       | inl h => left; exact hRS _ _ h
       | inr h => right; exact hRS _ _ h)
    -- Conjunction/disjunction patterns
    | (obtain ⟨h1, h2⟩ := hF; exact ⟨hRS _ _ h1, hRS _ _ h2⟩)
    | (obtain ⟨h1, h2⟩ := hF; constructor <;> first | exact hRS _ _ ‹_› | assumption)
    -- Existential patterns
    | (obtain ⟨w, hw⟩ := hF; exact ⟨w, hRS _ _ hw⟩)
    -- Direct monotonicity
    | exact hRS x y hF
    | exact hRS _ _ hF
    -- Fall back to aesop for complex cases
    | aesop
  ))

/-!
## Combo Tactics

Convenience tactics that combine multiple operations.
-/

/-- Unfold and destruct a paco hypothesis in one step.

## Signature
`pdestruct h` where `h : paco F r x y`

## Effect
Equivalent to: `punfold h; cases h; pclearbot`

Note: The original hypothesis `h` is preserved (not replaced).
The destruction creates new goals for each constructor of F.

## Example
```lean
example (h : paco Bisim r p q) : P := by
  pdestruct h
  -- Creates goal for each Bisim constructor
  -- h is still available with original type
  ...
```

## See Also
- `punfold`: just unfold without destructing
- `pinversion`: similar, emphasizes that original is preserved
-/
macro "pdestruct" h:ident : tactic =>
  `(tactic| (
    have _h_unfolded := Paco.paco_unfold _ _ _ _ $h
    cases _h_unfolded <;> simp only [Paco.upaco_bot] at *
  ))

/-- Unfold and invert a paco hypothesis, preserving the original.

## Signature
`pinversion h` where `h : paco F r x y`

## Effect
Like `pdestruct`, but explicitly preserves the original hypothesis.
Creates subgoals for each constructor of F, with the unfolded
hypothesis components available.

Equivalent to: create unfolded copy, cases on copy, pclearbot

## When to Use
Use `pinversion` instead of `pdestruct` when:
- You want to make clear the original hypothesis is preserved
- You may need to refer to the original `paco` hypothesis later
- You want inversion-like behavior (Coq's `inversion` vs `destruct`)

## Example
```lean
example (h : paco Bisim r p q) : P := by
  pinversion h
  -- h is still `paco Bisim r p q`
  -- new hypotheses from F-structure are in context
  ...
```

## See Also
- `pdestruct`: same behavior, different emphasis
- `punfold`: just unfold without case analysis
-/
macro "pinversion" h:ident : tactic =>
  `(tactic| (
    have _h_inv := Paco.paco_unfold _ _ _ _ $h
    cases _h_inv <;> simp only [Paco.upaco_bot] at *
  ))

end Paco
