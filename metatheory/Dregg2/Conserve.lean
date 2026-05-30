/-
# Dregg2.Conserve — shared conservation lemmas + the `conserve` / `commit_cases` tactics.

A tactics-audit found that the executable kernels (`Exec/Kernel.lean`,
`Exec/Generators.lean`, `Exec/MultiAsset.lean`) repeat — near verbatim — the *same*
`Finset.sum` debit/credit-cancellation argument:

    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]   -- reduce to "the deltas sum to 0"
    <case-split each touched point, rewrite to indicators>
    rw [Finset.sum_add_distrib, sum_indicator …]   -- collapse the indicators
    ring                                           -- the debit cancels the credit

and the *same* fail-closed read-back boilerplate for `def f … := if guard then some … else none`:

    unfold f at h
    by_cases hg : guard
    · rw [if_pos hg] at h; simp only [Option.some.injEq …] at h; subst h; obtain ⟨…⟩ := hg; …
    · rw [if_neg hg] at h; exact absurd h (by simp)

This module factors BOTH into reusable, honest automation, **without touching** any existing
file (retrofitting the existing clones to call these is a deliberate, separate follow-up):

1. `sum_pointUpdate` / `sum_conserve_of_deltas_zero` — the GENERAL conservation lemmas,
   stated over `Finset CellId` and `bal : CellId → ℤ`. The existing Kernel / MultiAsset /
   Generators lemmas COULD be rewritten as one-liners on top of these.
2. `conserve` — a macro tactic closing "this `Finset.sum` = that one" when the per-point
   deltas cancel, that FAILS LOUDLY when they don't (it never falls through to a weaker
   closer that could mask a forgotten `src ≠ dst`).
3. `commit_cases h with pat` — the structural split for a fail-closed `if`-guarded executor:
   it discharges the `none` branch and does the `some`-branch *read-back + guard extraction*
   only; it deliberately may NOT close the live `some`-branch goal (which carries the content).

Discipline: no `axiom` / `admit` / `native_decide` / `sorry`. The tactics cannot fake a goal.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Dregg2.Tactics

namespace Dregg2.Conserve

open scoped BigOperators

/-- A cell identity (kept generic; reuses `Nat` like the executable kernels). -/
abbrev CellId := Nat

/-! ## 1. The general conservation lemma library.

The single-point-indicator value `(∑ c ∈ acc, if c = a then v else 0) = v`, and the two
keystones the executable kernels need: the value of a sum after a pointwise update, and the
conservation criterion "if the per-point deltas sum to zero, the total is unchanged". -/

/-- **Single-point indicator sum.** Summing an indicator that is `v` at exactly `a ∈ acc`
and `0` elsewhere gives `v`. (The general restatement of `Kernel.sum_indicator` /
`MultiAsset.maSumIndicator`.) -/
theorem sum_indicator (acc : Finset CellId) (a : CellId) (v : ℤ) (ha : a ∈ acc) :
    (∑ c ∈ acc, (if c = a then v else 0)) = v := by
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (fun h => absurd ha h)]
  simp

/-- **Sum after a pointwise update — the general lemma.** Updating a balance `bal` to a new
balance `bal'` changes the `Finset.sum` over `acc` by exactly the sum of the per-point
deltas `bal' c - bal c`. This is just `Finset.sum_sub_distrib` packaged so the executable
kernels can read off the total directly:

    (∑ c ∈ acc, bal' c) = (∑ c ∈ acc, bal c) + ∑ c ∈ acc, (bal' c - bal c).

Every existing kernel conservation proof is an instance: pick `bal'` = the post-transfer /
post-mint / post-burn balance, then compute the delta sum (it is `0` for a transfer between
distinct cells, `+amt` for a mint, `-amt` for a burn). -/
theorem sum_pointUpdate (acc : Finset CellId) (bal bal' : CellId → ℤ) :
    (∑ c ∈ acc, bal' c)
      = (∑ c ∈ acc, bal c) + ∑ c ∈ acc, (bal' c - bal c) := by
  rw [Finset.sum_sub_distrib]; ring

/-- **Conservation from cancelling deltas — the general criterion.** If, at every point of
`acc`, the per-point delta `bal' c - bal c` sums to zero, then the total is conserved:
`(∑ c ∈ acc, bal' c) = ∑ c ∈ acc, bal c`. This is the *exact* shape the kernels prove (the
debit `-amt` at `src` cancels the credit `+amt` at `dst`); they could now close it by
supplying the `0`-delta-sum fact. -/
theorem sum_conserve_of_deltas_zero (acc : Finset CellId) (bal bal' : CellId → ℤ)
    (hzero : (∑ c ∈ acc, (bal' c - bal c)) = 0) :
    (∑ c ∈ acc, bal' c) = ∑ c ∈ acc, bal c := by
  rw [sum_pointUpdate acc bal bal', hzero, add_zero]

/-- **Convenience: pointwise-delta conservation.** A debit/credit between two distinct cells
`src ≠ dst`, both in `acc`, conserves the sum — proved by checking the deltas cancel
pointwise (`-amt` at `src`, `+amt` at `dst`, `0` elsewhere) and applying
`sum_conserve_of_deltas_zero`. This is the literal general form of
`Kernel.transfer_sum_conserve` / `MultiAsset.maTransfer_sum_conserve_moved`. -/
theorem sum_transfer_conserve (acc : Finset CellId) (bal : CellId → ℤ)
    (src dst : CellId) (amt : ℤ) (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc,
        (if c = src then bal c - amt else if c = dst then bal c + amt else bal c))
      = ∑ c ∈ acc, bal c := by
  apply sum_conserve_of_deltas_zero
  have hg : ∀ c ∈ acc,
      ((if c = src then bal c - amt else if c = dst then bal c + amt else bal c) - bal c)
        = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) := by
    intro c _
    rcases eq_or_ne c src with h1 | h1
    · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hne]; ring
    · rcases eq_or_ne c dst with h2 | h2
      · subst h2; rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      sum_indicator acc src (-amt) hsrc, sum_indicator acc dst amt hdst]
  ring

-- Axiom-hygiene: pin the proved library to the three standard kernel axioms only.
#assert_axioms sum_indicator
#assert_axioms sum_pointUpdate
#assert_axioms sum_conserve_of_deltas_zero
#assert_axioms sum_transfer_conserve

/-! ## 2. The `conserve` tactic.

Closes a goal `(∑ c ∈ acc, f c) = ∑ c ∈ acc, g c` whose per-point deltas `f c - g c` cancel
**pointwise** (each summand's contribution is individually zero, possibly after `split_ifs`
and discharging the `if`-guards from context). It reduces to "the delta-sum is zero"
(`← sub_eq_zero`, `← Finset.sum_sub_distrib`), then proves each summand is `0`
(`Finset.sum_eq_zero` → `split_ifs` → `simp_all`/`ring`).

This is the genuinely-generic case: re-labellings, `+v-v` round-trips, and any update whose
per-cell net change is zero. The **global** two-point debit/credit cancellation (where the
deltas are individually NONZERO — `-amt` at `src`, `+amt` at `dst` — but sum to zero across
the set) is NOT pointwise and is handled instead by the library lemma `sum_transfer_conserve`
above (which is exactly the factored-out form of `Kernel.transfer_sum_conserve`); see the
`example`s. A macro cannot robustly drive that global collapse because it needs the membership
facts of the *specific* moved cells, so we keep the honest split: `conserve` for pointwise,
`sum_transfer_conserve` for the two-point move.

HONESTY RAIL: the real cancellation is wrapped in `first | <real> | fail "…"`. If the deltas
do NOT actually cancel pointwise, `ring` fails on a nonzero summand and the tactic ERRORS with
a clear message — it never falls through to a weaker closer (`omega`, `decide`, `simp`-only)
that could mask a missing hypothesis. -/

/-- `conserve` — close `(∑ … f) = ∑ … g` when the per-point deltas cancel POINTWISE. Fails
loudly ("conserve: deltas do not cancel …") otherwise; it will NOT silently close a
non-conserving goal. Bring any guard facts (`src ≠ dst`, memberships) into context as
hypotheses first. For the two-point debit/credit *move* (deltas nonzero but globally
cancelling) use the `sum_transfer_conserve` lemma instead. -/
macro "conserve" : tactic =>
  `(tactic|
    first
    | (rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
       refine Finset.sum_eq_zero ?_
       intro _ _
       split_ifs <;> (try simp_all) <;> ring
       -- `done` is load-bearing for the honesty rail: it forces an error (→ fall through to
       -- `fail`) if any summand was left UNCLOSED, so `conserve` can never silently leave a
       -- residual goal masquerading as progress. Either it fully closes, or it fails loud.
       done)
    | fail "conserve: deltas do not cancel pointwise — bring the guard facts (e.g. \
        `src ≠ dst`, memberships) into context, or use `sum_transfer_conserve` for a \
        two-point debit/credit move")

/-! ## 3. The `commit_cases h with pat` tactic.

The fail-closed executor shape is everywhere:

    def f … := if <guard> then some {…} else none

Given `h : f … = some s'`, `commit_cases h with pat`:
- splits the `if` (`split at h`);
- on the `none` branch, closes by deriving a contradiction from `h : none = some s'`;
- on the `some` branch, reads back `h` (`Option.some.injEq`, `Prod.mk.injEq`) and `subst`s,
  then `obtain pat` the (conjunctive) guard `‹_ ∧ _›`,
leaving the live `some`-branch goal OPEN.

(The guard is expected to be a conjunction — the universal shape of these fail-closed
executors, e.g. `authorized ∧ 0 ≤ amt ∧ … ∧ src ≠ dst ∧ …`; `pat` destructures it.)

STRUCTURAL RAIL: it does the read-back + guard extraction ONLY. It does NOT run a closer on
the `some`-branch goal — that goal carries the real content (the conservation / delta fact)
and must be proved explicitly. (It only *discharges* the impossible `none` branch, which is a
pure contradiction, never the live obligation.) -/

/-- `commit_cases h with pat` — split a fail-closed `if guard then some … else none`
hypothesis `h : f … = some s'`. Discharges the `none` branch by contradiction; on the `some`
branch performs the `some`/`Prod` read-back, `subst`s the resulting equation, and
`obtain pat` the guard — leaving the content goal open for you to prove. -/
syntax "commit_cases" ident "with" rcasesPat : tactic
macro_rules
  | `(tactic| commit_cases $h:ident with $pat:rcasesPat) =>
    `(tactic|
      (split at $h:ident
       -- impossible `none` branch FIRST: `h : none = some _` — a pure contradiction, safe to
       -- close. We target it explicitly with `case isFalse` so the closer can NEVER touch the
       -- live `some` branch (avoiding the masking trap where a `none`-closer half-applies to it).
       case isFalse => exact absurd $h:ident (by simp)
       -- only the committed `isTrue` goal remains now. Read it back (`Option`/`Prod` injection,
       -- then `subst` the recovered state equation) and `obtain` the guard — then STOP, leaving
       -- the genuine post-commit obligation OPEN. No closer runs on it.
       simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident
       subst $h:ident
       obtain $pat := ‹_ ∧ _›))

/-! ## Demonstrations / regression tests.

A toy ledger sum + a toy fail-closed executor, in the style of the real kernel proofs. These
`example`s ARE the usage documentation and the regression guard. (No `#assert_axioms` on
`example`s — they are anonymous.) -/

/-! ### `conserve`: pointwise cancellation (the genuinely-generic case). -/

/-- A single-point *re-labelling* with cancelling `+v / −v` deltas conserves the sum.
`conserve` closes it: the per-cell net change is `0`, so it cancels POINTWISE. -/
example (acc : Finset CellId) (bal : CellId → ℤ) (a : CellId) (v : ℤ) :
    (∑ c ∈ acc, (if c = a then bal c + v - v else bal c)) = ∑ c ∈ acc, bal c := by
  conserve

/-- A two-touch update that nets to zero AT EACH cell (debit `amt`, then credit `amt`, same
cell) conserves — again pointwise, so `conserve` closes it. (Contrast the two-CELL move
below, which is global, not pointwise.) -/
example (acc : Finset CellId) (bal : CellId → ℤ) (a : CellId) (amt : ℤ) :
    (∑ c ∈ acc, (if c = a then bal c - amt + amt else bal c)) = ∑ c ∈ acc, bal c := by
  conserve

/-- HONESTY-RAIL demonstration (negative test). The deltas here do NOT cancel — at cell `a`
the net change is `+amt ≠ 0` — so a sound `conserve` MUST fail rather than fake-close the
(false) "conserves" claim. We assert that failure with `fail_if_success`: if `conserve` ever
fell through to a weaker closer that proved this, this `example` would itself fail to compile,
turning the rail into a build-checked regression test. -/
example (_acc : Finset CellId) (_bal : CellId → ℤ) (_a : CellId) (_amt : ℤ) (_hpos : _amt ≠ 0) :
    True := by
  fail_if_success
    (have : (∑ c ∈ _acc, (if c = _a then _bal c + _amt else _bal c)) = ∑ c ∈ _acc, _bal c := by
       conserve)
  trivial

/-! ### The two-CELL move: deltas nonzero pointwise but globally cancelling.

This is NOT a pointwise cancellation (`-amt` at `src`, `+amt` at `dst`), so it is handled by
the factored library lemma `sum_transfer_conserve` — the general form of
`Kernel.transfer_sum_conserve`. A retrofit of the existing clones would replace their whole
proof body with this single `exact`. -/

/-- A transfer between two DISTINCT live cells conserves the total — discharged by the
library lemma `sum_transfer_conserve`, demonstrating the one-line retrofit. -/
example (acc : Finset CellId) (bal : CellId → ℤ) (src dst : CellId) (amt : ℤ)
    (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, (if c = src then bal c - amt else if c = dst then bal c + amt else bal c))
      = ∑ c ∈ acc, bal c := by
  exact sum_transfer_conserve acc bal src dst amt hsrc hdst hne

/-- HONESTY-RAIL for the two-cell move: WITHOUT `src ≠ dst` the debit and credit collapse onto
one cell and do NOT cancel — `sum_transfer_conserve` is (correctly) inapplicable, so no proof
goes through. We document this by showing the lemma genuinely requires `hne`: dropping it
leaves the goal open (here we supply it and succeed; there is no way to close the `src = dst`
version, which would be a false conservation claim). -/
example (acc : Finset CellId) (bal : CellId → ℤ) (src dst : CellId) (amt : ℤ)
    (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, (if c = src then bal c - amt else if c = dst then bal c + amt else bal c))
      = ∑ c ∈ acc, bal c :=
  -- `hne` is load-bearing: `sum_transfer_conserve` will not typecheck without it.
  sum_transfer_conserve acc bal src dst amt hsrc hdst hne

/-! ### `commit_cases`: the fail-closed read-back. -/

/-- A toy fail-closed executor: credit cell `a` by `amt` only when `0 ≤ amt ∧ a ∈ accounts`. -/
def toyExec (accounts : Finset CellId) (bal : CellId → ℤ) (a : CellId) (amt : ℤ) :
    Option (CellId → ℤ) :=
  if 0 ≤ amt ∧ a ∈ accounts then
    some (fun c => if c = a then bal c + amt else bal c)
  else
    none

/-- `commit_cases` splits the executor, kills the `none` branch, reads back the result on the
`some` branch and extracts the guard `⟨hpos, hmem⟩` — leaving us to prove the content. -/
example (accounts : Finset CellId) (bal bal' : CellId → ℤ) (a : CellId) (amt : ℤ)
    (h : toyExec accounts bal a amt = some bal') :
    (∑ c ∈ accounts, bal' c) = (∑ c ∈ accounts, bal c) + amt := by
  unfold toyExec at h
  commit_cases h with ⟨hpos, hmem⟩
  -- Goal is now the live content (sum after the credit); prove it via the general library.
  rw [sum_pointUpdate accounts bal]
  have : (∑ c ∈ accounts, ((if c = a then bal c + amt else bal c) - bal c))
      = ∑ c ∈ accounts, (if c = a then amt else 0) := by
    apply Finset.sum_congr rfl; intro c _; split <;> ring
  rw [this, sum_indicator accounts a amt hmem]

/-- `commit_cases` also handles the AUTHORITY read-back: from a committed run it hands you the
guard, from which the authority conjunct is immediate (the integrity-shadow pattern). -/
example (accounts : Finset CellId) (bal bal' : CellId → ℤ) (a : CellId) (amt : ℤ)
    (h : toyExec accounts bal a amt = some bal') :
    0 ≤ amt := by
  unfold toyExec at h
  commit_cases h with ⟨hpos, hmem⟩
  exact hpos

end Dregg2.Conserve
