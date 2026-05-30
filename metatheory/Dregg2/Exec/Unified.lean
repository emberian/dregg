/-
# Dregg2.Exec.Unified — ONE `KernelOp`, ONE `step`, ONE conservation law.

`Exec/Kernel.lean`, `Exec/Generators.lean`, and `Exec/Caps.lean` each build a *separate*
operation with its own `exec`/`execMint`/`execBurn`/`grant`/`revoke` and its own
conservation/authority fact. This module **unifies** them: a single `inductive KernelOp`
enumerates every kernel action, a single `def step : KernelState → KernelOp → Option
KernelState` dispatches to the (reused, already-proven) primitives, and a single `delta :
KernelOp → ℤ` records each op's effect on the conserved quantity `total`.

The keystone is the unified ledger law `step_delta`:
`step k op = some k' → total k' = total k + delta op`,
with `delta` = `+amt` for `mint`, `-amt` for `burn`, and `0` for the conserving ops
(`transfer`/`grantCap`/`revokeCap`). It is proved by `cases op`, reusing
`exec_conserves` / `execMint_delta` / `execBurn_delta`; the cap-ops conserve because they
touch only `caps`, leaving `accounts`/`bal` (the only things `total` reads) untouched —
the equality is definitional.

Lifting `step_delta` along `Execution.invariant_run` gives both:
- `unified_run_conserves` — across a run of only-conserving ops, `total` is invariant;
- `unified_ledger` — across an arbitrary run, `total = initial + (minted − burned)`.

Pure executable Lean, `#eval`-able. Reuses `Kernel`/`Generators`/`Caps`; edits none.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Dregg2.Exec.Kernel
import Dregg2.Exec.Generators
import Dregg2.Exec.Caps
import Dregg2.Execution

namespace Dregg2.Exec

open Dregg2.Authority Dregg2.Execution

/-- **The unified kernel operation.** Every kernel action — a resource `transfer`, a supply
`mint`/`burn`, or a capability `grantCap`/`revokeCap` — is one constructor of this single
type, replacing the previously-scattered `exec`/`execMint`/`execBurn`/`grant`/`revoke`. -/
inductive KernelOp where
  | transfer  (actor src dst : CellId) (amt : ℤ)
  | mint      (actor cell : CellId) (amt : ℤ)
  | burn      (actor cell : CellId) (amt : ℤ)
  | grantCap  (holder : CellId) (c : Cap)
  | revokeCap (holder : CellId) (c : Cap)

/-- **The unified executable transition.** One `step` dispatches each `KernelOp` to the
already-built primitive: `transfer` ⟶ `Kernel.exec` (on the assembled `Turn`); `mint`/`burn`
⟶ `Generators.execMint`/`execBurn`; `grantCap`/`revokeCap` ⟶ a pure update of `k.caps` via
`Caps.grant`/`Caps.revoke` (cap ops always commit and leave balances untouched). -/
def step (k : KernelState) : KernelOp → Option KernelState
  | .transfer actor src dst amt => exec k { actor := actor, src := src, dst := dst, amt := amt }
  | .mint actor cell amt        => execMint k actor cell amt
  | .burn actor cell amt        => execBurn k actor cell amt
  | .grantCap holder c          => some { k with caps := grant k.caps holder c }
  | .revokeCap holder c         => some { k with caps := revoke k.caps holder c }

/-- **The effect of an op on the conserved quantity `total`.** The conserving ops
(`transfer`, `grantCap`, `revokeCap`) have delta `0`; `mint` raises `total` by `amt`;
`burn` lowers it by `amt`. -/
def delta : KernelOp → ℤ
  | .transfer _ _ _ _ => 0
  | .mint _ _ amt     => amt
  | .burn _ _ amt     => -amt
  | .grantCap _ _     => 0
  | .revokeCap _ _    => 0

/-! ## Cap ops conserve (balances/accounts untouched ⟹ `total` unchanged). -/

/-- A `grantCap` leaves `total` unchanged: it updates only `caps`, and `total` reads only
`accounts`/`bal`. Definitional. -/
theorem total_grant (k : KernelState) (holder : CellId) (c : Cap) :
    total { k with caps := grant k.caps holder c } = total k := rfl

/-- A `revokeCap` leaves `total` unchanged (same reason as `total_grant`). Definitional. -/
theorem total_revoke (k : KernelState) (holder : CellId) (c : Cap) :
    total { k with caps := revoke k.caps holder c } = total k := rfl

/-! ## The unified conservation / ledger law (PROVED). -/

/-- **Unified conservation — PROVED.** Every committed `step` moves `total` by exactly
`delta op`. The single law subsuming `exec_conserves` (`delta = 0`), `execMint_delta`
(`+amt`), `execBurn_delta` (`-amt`), and the two cap-op conservations (`delta = 0`). Proved
by `cases op`, reusing each primitive's already-proven fact. -/
theorem step_delta (k k' : KernelState) (op : KernelOp) (h : step k op = some k') :
    total k' = total k + delta op := by
  cases op with
  | transfer actor src dst amt =>
      -- transfer: reuse `exec_conserves`; `delta = 0`.
      simp only [step] at h
      rw [exec_conserves k k' _ h]; simp [delta]
  | mint actor cell amt =>
      -- mint: reuse `execMint_delta`; `delta = +amt`.
      simp only [step] at h
      rw [execMint_delta k k' actor cell amt h]; rfl
  | burn actor cell amt =>
      -- burn: reuse `execBurn_delta`; `delta = -amt`.
      simp only [step] at h
      rw [execBurn_delta k k' actor cell amt h]; simp [delta]; ring
  | grantCap holder c =>
      -- grantCap: only `caps` changes ⟹ `total` unchanged; `delta = 0`.
      simp only [step, Option.some.injEq] at h
      subst h; rw [total_grant]; simp [delta]
  | revokeCap holder c =>
      -- revokeCap: only `caps` changes ⟹ `total` unchanged; `delta = 0`.
      simp only [step, Option.some.injEq] at h
      subst h; rw [total_revoke]; simp [delta]

/-- A `KernelOp` is **conserving** when its delta is `0` (everything but `mint`/`burn`). -/
def Conserving : KernelOp → Prop
  | .transfer _ _ _ _ => True
  | .mint _ _ _       => False
  | .burn _ _ _       => False
  | .grantCap _ _     => True
  | .revokeCap _ _    => True

/-- A conserving op has zero delta — PROVED (by `cases`). -/
theorem delta_eq_zero_of_conserving (op : KernelOp) (hc : Conserving op) : delta op = 0 := by
  cases op <;> simp_all [Conserving, delta]

/-- **A conserving step preserves `total` — PROVED** (corollary of `step_delta`). -/
theorem step_conserves (k k' : KernelState) (op : KernelOp)
    (hc : Conserving op) (h : step k op = some k') : total k' = total k := by
  rw [step_delta k k' op h, delta_eq_zero_of_conserving op hc, add_zero]

/-! ## The unified `Execution.System` and whole-run laws (PROVED). -/

/-- **The unified system:** a step is any committed `KernelOp` — one transition relation
covering transfer/mint/burn/grant/revoke, replacing the bespoke `kernelSystem`. -/
def unifiedSystem : System where
  Config := KernelState
  Step k k' := ∃ op, step k op = some k'

/-- **The conserving-only sub-system:** a step is any committed *conserving* op. Across a
run of this system `total` is a true invariant. -/
def conservingSystem : System where
  Config := KernelState
  Step k k' := ∃ op, Conserving op ∧ step k op = some k'

/-- **Conservation across a whole conserving run — PROVED** (lifting `step_conserves` via
`Execution.invariant_run`): if every step uses a conserving op, `total` is invariant over
the entire execution. -/
theorem unified_run_conserves {k k' : KernelState} (hrun : Run conservingSystem k k') :
    total k' = total k := by
  have hpres : StepInvariant conservingSystem (fun c => total c = total k) := by
    intro a b ha hstep
    obtain ⟨op, hc, hop⟩ := hstep
    rw [step_conserves a b op hc hop]; exact ha
  exact invariant_run hpres hrun rfl

/-! ## The general ledger law: `total = initial + Σ deltas`.

A `Trace` is a run of the `unifiedSystem` that ALSO records the op list it fired, so we can
state the exact balance equation across mint/burn (not just the conserving case). -/

/-- **A traced run:** like `Execution.Run unifiedSystem` but carrying the list of ops fired,
each with its commit proof. -/
inductive Trace : KernelState → List KernelOp → KernelState → Prop where
  | refl (k : KernelState) : Trace k [] k
  | step {k k' k'' : KernelState} {op : KernelOp} {ops : List KernelOp} :
      step k op = some k' → Trace k' ops k'' → Trace k (op :: ops) k''

/-- The net ledger delta of a trace = sum of the per-op deltas. -/
def traceDelta (ops : List KernelOp) : ℤ := (ops.map delta).sum

/-- **The unified ledger law — PROVED.** Across ANY traced run, the final total equals the
initial total plus the net of all deltas (mints add, burns subtract, the rest contribute
`0`): `total k'' = total k + traceDelta ops`. The single equation governing the whole
mint/burn/transfer/cap-op execution. Proved by induction on the trace, reusing
`step_delta`. -/
theorem unified_ledger {k k'' : KernelState} {ops : List KernelOp}
    (htr : Trace k ops k'') : total k'' = total k + traceDelta ops := by
  induction htr with
  | refl k => simp [traceDelta]
  | step hstep _ ih =>
      rw [ih, step_delta _ _ _ hstep]
      simp only [traceDelta, List.map_cons, List.sum_cons]
      ring

/-- **Conservation as a corollary of the ledger — PROVED.** If a traced run fires only
conserving ops (`traceDelta = 0`), `total` is preserved. -/
theorem unified_ledger_conserves {k k'' : KernelState} {ops : List KernelOp}
    (htr : Trace k ops k'') (hzero : traceDelta ops = 0) : total k'' = total k := by
  rw [unified_ledger htr, hzero, add_zero]

/-! ## It runs (`#eval`). Reuses `Kernel.s0` (cells 0,1; 100+5). -/

/-- A mint of 50 into cell 0 (actor 9 holds a `node` cap on 0), then a transfer of 30 from
0 to 1: net delta `+50`, so `total` goes 105 → 155. -/
def opsDemo : List KernelOp := [.mint 9 0 50, .transfer 0 0 1 30]

#eval delta (.mint 9 0 50)                       -- 50
#eval delta (.transfer 0 0 1 30)                 -- 0
#eval delta (.burn 9 0 40)                       -- -40
#eval traceDelta opsDemo                         -- 50

/-- Start state with a minting authority (actor 9 holds `node 0`). -/
def sLedger : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun a => if a = 9 then [Cap.node 0] else [] }

#eval (step sLedger (.mint 9 0 50)).map total    -- some 155 (= 105 + 50)
#eval (step sLedger (.grantCap 3 (Cap.node 7))).map total  -- some 105 (cap op conserves)
#eval (step sLedger (.transfer 9 0 1 30)).map total        -- some 105 (transfer conserves)
