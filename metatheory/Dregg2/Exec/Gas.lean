/-
# Dregg2.Exec.Gas — a SOUND, FAIL-CLOSED gas-metering model for the full-op-set turn executor.

`Exec/TurnExecutorFull.lean` runs a `List FullAction` turn (`execFullTurn`) as an all-or-nothing
transaction, step-complete by construction (`execFull_attests`, `execFullTurn_ledger`,
`execFullTurn_conserves`). Those are SAFETY guarantees (conservation / authority / chain-link).
What they do NOT bound is *resource consumption*: an arbitrarily long or expensive turn is still
admissible. This module adds the missing LIVENESS bound — a per-action gas schedule and a metered
executor that runs a turn only while a finite budget suffices, and FAILS CLOSED (no partial state
mutation) the instant the cumulative cost would exceed the budget.

The model sits BESIDE `execFullTurn`, never replacing or weakening it. Concretely we prove the gas
guard is a PURE GUARD: when affordable it returns EXACTLY the un-metered `execFullTurn` state (gas
metering does not alter semantics), and therefore the resulting state still attests everything
`execFull`/`execFullTurn` guarantee (conservation, the per-action `fullActionInv`). Gas ADDS a
liveness bound and REMOVES no safety.

  * `gasCost : FullAction → Nat` — a schedule with DISTINCT, NONZERO costs per kind (a mint costs
    more than a transfer; a delegate more than a revoke; nothing is free — no all-zero vacuity).
  * `totalCost : List FullAction → Nat` — Σ of the per-action costs.
  * `execGas (budget) (acts) (s) : Option (RecChainedState × Nat)` — runs the turn, gating each
    action against the remaining budget BEFORE it commits, and returning the leftover gas. Any
    over-budget action aborts the WHOLE turn to `none` (all-or-nothing, mirroring `execFullTurn`).

THEOREMS (no `sorry`/`axiom`/`admit`/`native_decide`):
  * `gas_monotone`              — a committed metered run leaves remaining gas `= budget − totalCost`
                                  (non-increasing; consumed = Σ over the executed actions).
  * `gas_exhaustion_fails_closed` — `totalCost acts > budget ⇒ execGas = none` (and the caller's
                                  state is untouched: `execGas` returns no state at all).
  * `gas_sufficient_runs`       — `budget ≥ totalCost acts ⇒` the metered run succeeds AND its state
                                  EQUALS the un-metered `execFullTurn` result (pure guard) — PROVIDED
                                  the underlying turn itself commits (the honest precondition: gas
                                  cannot conjure a turn the executor would reject for non-gas
                                  reasons — authority/availability — so the equality is stated for a
                                  turn that `execFullTurn` accepts).
  * `gas_conserves`             — a committed metered run whose net ledger delta is `0` preserves
                                  `recTotal` (delegates to `execFullTurn_conserves`).
  * `gas_preserves_attests`     — every action of a committed metered run attests `fullActionInv`
                                  (delegates to `execFullTurn_each_attests`) — gas removes no safety.

Discipline (REORIENT §6): no `axiom`/`admit`/`native_decide`/`sorry`/`@[implemented_by]`.
`#assert_axioms` on every keystone. Pure, computable, `#eval`-able. Reuses `TurnExecutorFull`; edits
nothing. Verified standalone: `lake env lean Dregg2/Exec/Gas.lean`.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Exec.Gas

open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — The gas schedule: distinct, nonzero per-kind costs.

A `node`/`control` supply op (mint/burn) is the most expensive (it moves the conserved total and
forces a disclosure receipt); a connectivity delegate is mid; a balance/effect move is the base
unit; a revoke is the cheapest mutating op (it only subtracts authority). NONE are zero — there is
no free action, so the bound is never a vacuity. The costs are pairwise distinct across kinds. -/

/-- **The per-action gas schedule.** Distinct, strictly-positive cost per `FullAction` kind:
balance `2`, revoke `1`, delegate `3`, burn `4`, mint `5`. (Mint/burn — the privileged supply ops —
are dearest; revoke — pure subtraction — is cheapest; none is free.) -/
def gasCost : FullAction → Nat
  | .balance _      => 2
  | .delegate _ _ _ => 3
  | .revoke _ _     => 1
  | .mint _ _ _     => 5
  | .burn _ _ _     => 4

/-- **Every action costs gas — PROVED (non-vacuity of the schedule).** No `FullAction` is free, so a
finite budget is a genuine bound on every kind (an all-zero schedule would make every theorem
vacuous; this rules that out). -/
theorem gasCost_pos (fa : FullAction) : 0 < gasCost fa := by
  cases fa <;> simp [gasCost]

/-- **The costs are not all equal — PROVED (the schedule is a real, kind-sensitive price).** A mint
costs strictly more than a balance move; a revoke strictly less. So the bound discriminates between
turn kinds rather than just counting actions. -/
theorem gasCost_distinct :
    gasCost (.revoke 0 0) < gasCost (.balance ⟨0, .transfer, ⟨0, 0, 0, 0⟩⟩) ∧
    gasCost (.balance ⟨0, .transfer, ⟨0, 0, 0, 0⟩⟩) < gasCost (.delegate 0 0 0) ∧
    gasCost (.delegate 0 0 0) < gasCost (.burn 0 0 0) ∧
    gasCost (.burn 0 0 0) < gasCost (.mint 0 0 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [gasCost]

/-- **The total gas a turn would consume** — Σ of the per-action costs. -/
def totalCost (acts : List FullAction) : Nat := (acts.map gasCost).sum

@[simp] theorem totalCost_nil : totalCost [] = 0 := rfl

@[simp] theorem totalCost_cons (a : FullAction) (rest : List FullAction) :
    totalCost (a :: rest) = gasCost a + totalCost rest := by
  simp [totalCost]

/-! ## §2 — `execGas`: the metered executor, gating each action against the remaining budget.

We fold over the turn carrying the remaining budget. BEFORE committing each action we check that its
`gasCost` is affordable (`gasCost a ≤ budget`); if not, the WHOLE turn aborts to `none` (no partial
mutation — the same all-or-nothing discipline as `execFullTurn`). On commit we charge the action's
cost and recurse with the reduced budget. The result carries the committed state AND the leftover
gas. Note the gas check runs FIRST: an under-budget but otherwise-valid turn still fails closed. -/

/-- **The metered turn executor.** Runs the `FullAction` list while the remaining budget suffices,
charging each action's `gasCost`, returning the final state paired with the leftover gas. Fails
closed (`none`) the instant an action's cost would exceed the remaining budget — OR the underlying
`execFull` rejects the action (authority/availability). All-or-nothing: any failure aborts the whole
turn with NO partial state mutation (the caller's `s` is never returned on failure). -/
def execGas (budget : Nat) (acts : List FullAction) (s : RecChainedState) :
    Option (RecChainedState × Nat) :=
  match acts with
  | []        => some (s, budget)
  | a :: rest =>
    if gasCost a ≤ budget then
      match execFull s a with
      | some s' => execGas (budget - gasCost a) rest s'
      | none    => none
    else
      none

/-! ## §3 — `gas_monotone`: remaining gas is non-increasing; consumed = Σ over executed actions.

A committed metered run leaves EXACTLY `budget − totalCost acts` gas — the consumed gas is precisely
the sum of the per-action costs of the (all of the) actions that ran. Since `totalCost ≥ 0`, the
remaining gas never exceeds the budget: monotone non-increasing. -/

/-- **`gas_monotone` — PROVED.** A committed metered run consumes EXACTLY `totalCost acts` gas: the
returned remaining gas is `budget − totalCost acts`. Hence remaining gas is non-increasing across
the run (`leftover ≤ budget`), and the total consumed equals Σ `gasCost` over the executed actions.
Proved by induction on the turn; each step charges exactly `gasCost a`. -/
theorem gas_monotone :
    ∀ (budget : Nat) (acts : List FullAction) (s : RecChainedState) (s' : RecChainedState)
      (g : Nat), execGas budget acts s = some (s', g) → g = budget - totalCost acts
  | budget, [], s, s', g, h => by
      simp only [execGas, Option.some.injEq, Prod.mk.injEq] at h
      simp [h.2]
  | budget, a :: rest, s, s', g, h => by
      simp only [execGas] at h
      by_cases hb : gasCost a ≤ budget
      · rw [if_pos hb] at h
        cases hfa : execFull s a with
        | none => rw [hfa] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hfa] at h
            -- IH: the tail leaves `(budget − gasCost a) − totalCost rest`.
            have htail := gas_monotone (budget - gasCost a) rest s1 s' g h
            rw [htail, totalCost_cons, Nat.sub_sub]
      · rw [if_neg hb] at h; exact absurd h (by simp)

/-- **Remaining gas never exceeds the budget — PROVED (monotone non-increasing).** A direct
corollary of `gas_monotone`: subtraction on `Nat` can only shrink, so the leftover gas of any
committed run is `≤ budget`. -/
theorem gas_leftover_le_budget (budget : Nat) (acts : List FullAction) (s s' : RecChainedState)
    (g : Nat) (h : execGas budget acts s = some (s', g)) : g ≤ budget := by
  rw [gas_monotone budget acts s s' g h]; exact Nat.sub_le _ _

/-! ## §4 — `gas_exhaustion_fails_closed`: over-budget ⇒ `none`, no partial mutation.

The headline SAFETY property of the gas layer: if the turn's total cost exceeds the budget, the
metered run produces NO state at all (`none`) — it never partially applies a prefix of the turn and
leaves the executor mid-mutation. Because `execGas` returns the leftover gas only via `some (_, _)`,
a `none` result means nothing committed. -/

/-- **`gas_exhaustion_fails_closed` — PROVED (the safety property).** If the turn's total cost
strictly exceeds the budget, the metered run FAILS CLOSED: `execGas = none`. No state is returned, so
no partial mutation escapes — the executor never applies a prefix of an unaffordable turn. Proved by
induction: somewhere the running budget cannot cover the next action's `gasCost`, and the `if`-guard
aborts the whole fold. -/
theorem gas_exhaustion_fails_closed :
    ∀ (budget : Nat) (acts : List FullAction) (s : RecChainedState),
      totalCost acts > budget → execGas budget acts s = none
  | budget, [], s, h => by
      simp only [totalCost_nil] at h; exact absurd h (by simp)
  | budget, a :: rest, s, h => by
      simp only [execGas]
      by_cases hb : gasCost a ≤ budget
      · -- This action is affordable; the OVERRUN must lie in the tail.
        rw [if_pos hb]
        cases hfa : execFull s a with
        | none => rfl
        | some s1 =>
            -- `totalCost (a :: rest) > budget` and `gasCost a ≤ budget`
            -- ⇒ `totalCost rest > budget − gasCost a`.
            apply gas_exhaustion_fails_closed (budget - gasCost a) rest s1
            rw [totalCost_cons] at h
            omega
      · rw [if_neg hb]

/-! ## §5 — `gas_sufficient_runs`: when affordable, the metered run is a PURE GUARD.

When the budget covers the whole turn AND the underlying turn itself commits (`execFullTurn` accepts
it — gas cannot conjure a turn the executor rejects for authority/availability reasons), the metered
run succeeds and returns EXACTLY the un-metered `execFullTurn` state. Gas metering does not alter the
semantics of an affordable, valid turn: it is a pure liveness guard layered on top.

This is the honestly-stated theorem. A naive "`budget ≥ totalCost ⇒ execGas succeeds`" is FALSE — an
affordable turn can still be rejected by `execFull` (e.g. an unauthorized mint). So the precondition
is strengthened to "the turn commits un-metered", and the conclusion is the strong one: the metered
state EQUALS the un-metered state. (Improve, don't degrade: we keep the strong equality and pay for
it with the honest precondition.) -/

/-- **`gas_sufficient_runs` — PROVED (pure guard).** If the budget covers the whole turn
(`totalCost acts ≤ budget`) AND the un-metered executor commits the turn (`execFullTurn s acts =
some s'`), then the metered run commits to the SAME state `s'`, leaving `budget − totalCost acts`
gas: `execGas budget acts s = some (s', budget − totalCost acts)`. So gas metering is a pure guard —
it changes nothing about an affordable, valid turn's result. Proved by induction on the turn, with
the per-step affordability discharged from `totalCost_cons` and the state-equality from the shared
`execFull` step. -/
theorem gas_sufficient_runs :
    ∀ (budget : Nat) (acts : List FullAction) (s s' : RecChainedState),
      totalCost acts ≤ budget → execFullTurn s acts = some s' →
      execGas budget acts s = some (s', budget - totalCost acts)
  | budget, [], s, s', _, hturn => by
      simp only [execFullTurn, Option.some.injEq] at hturn
      subst hturn; simp [execGas]
  | budget, a :: rest, s, s', hcost, hturn => by
      simp only [execFullTurn] at hturn
      cases hfa : execFull s a with
      | none => rw [hfa] at hturn; exact absurd hturn (by simp)
      | some s1 =>
          rw [hfa] at hturn
          -- The head is affordable: `gasCost a ≤ totalCost (a :: rest) ≤ budget`.
          have hba : gasCost a ≤ budget := by
            rw [totalCost_cons] at hcost; omega
          -- The tail is affordable against the reduced budget.
          have htailcost : totalCost rest ≤ budget - gasCost a := by
            rw [totalCost_cons] at hcost; omega
          -- IH on the committed tail.
          have hih := gas_sufficient_runs (budget - gasCost a) rest s1 s' htailcost hturn
          simp only [execGas, if_pos hba, hfa, hih, totalCost_cons, Nat.sub_sub]

/-! ## §6 — Safety preserved: a committed metered run still attests everything `execFull` does.

The metered run commits ONLY states the un-metered `execFullTurn` would also commit (the gas guard
only ever ADDS a rejection, never a new acceptance). So we can recover the un-metered turn from any
committed metered run, and then delegate VERBATIM to `TurnExecutorFull`'s safety lemmas:
conservation (`execFullTurn_conserves`) and the per-action `fullActionInv`
(`execFullTurn_each_attests`). Gas adds a liveness bound and removes no safety. -/

/-- **The metered run refines the un-metered turn — PROVED.** Any state a committed metered run
reaches, the un-metered `execFullTurn` reaches too: `execGas budget acts s = some (s', g) ⇒
execFullTurn s acts = some s'`. The gas guard only ever REJECTS more, never accepts more — so every
metered commit is an un-metered commit. This is the bridge that lets every `execFullTurn` safety
lemma transfer to the metered run unchanged. Proved by induction on the turn. -/
theorem execGas_refines_execFullTurn :
    ∀ (budget : Nat) (acts : List FullAction) (s s' : RecChainedState) (g : Nat),
      execGas budget acts s = some (s', g) → execFullTurn s acts = some s'
  | budget, [], s, s', g, h => by
      simp only [execGas, Option.some.injEq, Prod.mk.injEq] at h
      simp [execFullTurn, h.1]
  | budget, a :: rest, s, s', g, h => by
      simp only [execGas] at h
      by_cases hb : gasCost a ≤ budget
      · rw [if_pos hb] at h
        cases hfa : execFull s a with
        | none => rw [hfa] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hfa] at h
            have htail := execGas_refines_execFullTurn (budget - gasCost a) rest s1 s' g h
            simp only [execFullTurn, hfa]; exact htail
      · rw [if_neg hb] at h; exact absurd h (by simp)

/-- **`gas_conserves` — PROVED.** A committed metered run whose net ledger delta is `0`
(balance/authority only, or balanced mint/burn) preserves the conserved supply `recTotal`. Delegates
to `execFullTurn_conserves` via `execGas_refines_execFullTurn` — gas adds no conservation obligation
and removes none. -/
theorem gas_conserves (budget : Nat) (acts : List FullAction) (s s' : RecChainedState) (g : Nat)
    (h : execGas budget acts s = some (s', g)) (hzero : turnLedgerDelta acts = 0) :
    recTotal s'.kernel = recTotal s.kernel :=
  execFullTurn_conserves s s' acts (execGas_refines_execFullTurn budget acts s s' g h) hzero

/-- **`gas_ledger` — PROVED.** A committed metered run moves `recTotal` by exactly the net of the
per-action ledger deltas (`turnLedgerDelta acts`) — the gas layer does not perturb the conservation
ledger. Delegates to `execFullTurn_ledger`. -/
theorem gas_ledger (budget : Nat) (acts : List FullAction) (s s' : RecChainedState) (g : Nat)
    (h : execGas budget acts s = some (s', g)) :
    recTotal s'.kernel = recTotal s.kernel + turnLedgerDelta acts :=
  execFullTurn_ledger s s' acts (execGas_refines_execFullTurn budget acts s s' g h)

/-- **`gas_preserves_attests` — PROVED.** Every action of a committed metered run attests its full
`fullActionInv` (exact ledger conservation ∧ ChainLink ∧ ObsAdvance ∧ the kind-specific
authority/graph/disclosure obligation) — exactly as the un-metered turn does. Delegates to
`execFullTurn_each_attests`. Gas adds a liveness bound and removes NO safety. -/
theorem gas_preserves_attests (budget : Nat) (acts : List FullAction) (s s' : RecChainedState)
    (g : Nat) (h : execGas budget acts s = some (s', g)) :
    ∀ fa ∈ acts, ∃ sa sa', execFull sa fa = some sa' ∧ fullActionInv sa fa sa' :=
  execFullTurn_each_attests s s' acts (execGas_refines_execFullTurn budget acts s s' g h)

/-! ## §7 — Axiom-hygiene tripwires (the honesty pins over the gas model's keystones). -/

#assert_axioms gasCost_pos
#assert_axioms gasCost_distinct
#assert_axioms gas_monotone
#assert_axioms gas_leftover_le_budget
#assert_axioms gas_exhaustion_fails_closed
#assert_axioms gas_sufficient_runs
#assert_axioms execGas_refines_execFullTurn
#assert_axioms gas_conserves
#assert_axioms gas_ledger
#assert_axioms gas_preserves_attests

/-! ## §8 — Non-vacuity: a metered run commits when affordable, fails closed when not.

Reuses `TurnExecutorFull.fs0` (cell 0 bal 100, cell 1 bal 5; actor 9 holds a `node 0` mint cap;
delegator 0 holds a `node 7` cap) and `mixedTurn` (mint +50, transfer, burn −50 → nets to 0). -/

-- `mixedTurn` costs mint(5) + balance(2) + burn(4) = 11 gas.
#eval totalCost mixedTurn                                              -- 11

-- With AMPLE budget (20 ≥ 11) the metered run commits to the SAME state as the un-metered turn,
-- leaving 20 − 11 = 9 gas:
#eval (execGas 20 mixedTurn fs0).map (fun p => (recTotal p.1.kernel, p.2))   -- some (105, 9)
#eval (execGas 20 mixedTurn fs0).map (fun p => p.1.log.length)              -- some 3
-- ...matching the un-metered executor exactly (pure guard):
#eval (execFullTurn fs0 mixedTurn).map (fun s => recTotal s.kernel)         -- some 105

-- With EXACTLY enough budget (11) it still commits, leaving 0 gas:
#eval (execGas 11 mixedTurn fs0).map (fun p => p.2)                         -- some 0

-- With an INSUFFICIENT budget (10 < 11) the metered run FAILS CLOSED — no state at all:
#eval (execGas 10 mixedTurn fs0).isSome                                    -- false

-- Fail-closed even mid-turn: budget 7 covers mint(5)+balance(2)=7 but NOT the burn(4); the whole
-- turn aborts to `none` (no partial commit — the mint is NOT left applied):
#eval (execGas 7 mixedTurn fs0).isSome                                     -- false

-- A single affordable action commits and charges exactly its cost (mint = 5):
#eval (execGas 10 [FullAction.mint 9 0 50] fs0).map (fun p => p.2)         -- some 5
-- ...a single unaffordable action fails closed (revoke costs 1, budget 0):
#eval (execGas 0 [FullAction.revoke 0 7] fs0).isSome                       -- false
-- ...the empty turn always commits, consuming nothing:
#eval (execGas 0 ([] : List FullAction) fs0).map (fun p => p.2)            -- some 0

end Dregg2.Exec.Gas
