/-
# Dregg2.Exec.RecordKernel — the kernel laws over a CONTENT-ADDRESSED record cell-state.

`Exec/Kernel.lean` is the verified *micro-core*: its `KernelState.bal : CellId → ℤ` is a single
scalar ledger, and `exec_conserves`/`exec_authorized`/`exec_unauthorized_fails` are PROVED over
that whole-state ℤ. But the concrete dregg2 cell is NOT a scalar — it is `Exec/Value.lean`'s
schema-keyed record `Value` (named fields, `flatten`/`width`/`conforms`, `flatten_width` PROVED).
The construction study's single-highest-leverage move (`docs/rebuild/PHASE-CONSTRUCTION.md §1`,
"The single highest-leverage next move") is to replace the toy scalar ledger with that
content-addressed record cell and re-prove the kernel laws over a NAMED FIELD (`balance`) rather
than the whole-state ℤ — aligning the conserved quantity with `Spec/Conservation`'s domain-typed
conservation (`conservedInDomain Domain.balance`).

This module does exactly that, as a SECOND, parallel kernel ALONGSIDE the scalar one (the
sanctioned fallback when a full in-place lift of `KernelState` ripples too far — here it ripples
across ~8 `Finset.sum`-heavy `Exec/*` files). The toy scalar kernel stays UNTOUCHED and green; we
add `RecordKernelState` + `recKExec` whose cell-state is a `Value` record, conserve the **`balance`
field**, and re-prove ALL THREE kernel laws + the four-conjunct `StepInv` over it. The conserved
quantity becomes a domain measure over a named field — the `Spec.conservedInDomain Domain.balance`
shape — so this is the concrete-instance seam between "verified micro-core" and "verified dregg".

`flatten_width` (from `Value.lean`) is the foundation lemma the *circuit* side rests on; the
*semantic* re-proof here rests on `Value.scalar "balance"` (the named-field read), reusing
`Exec/Kernel.lean`'s already-proved `sum_indicator` over the `balance`-field measure.

Pure, computable, `#eval`-able. Imports `Exec.Program` (for `Value.scalar`/`Value.field`) and
`Exec.Kernel` (for `CellId`/`Turn`/`authorizedB`/`Caps` + the reused `sum_indicator`).
-/
import Dregg2.Exec.Kernel
import Dregg2.Exec.Program

namespace Dregg2.Exec

open Dregg2.Authority Dregg2.Execution
open scoped BigOperators

/-! ## The record cell-state and its `balance`-field measure. -/

/-- The canonical name of a cell's fungible balance field. The conserved quantity lives HERE —
not in the whole-state ℤ, but in this NAMED field of the content-addressed record. -/
def balanceField : FieldName := "balance"

/-- **`balOf v`** — read a cell record's `balance` field as an `Int`, defaulting an
absent/ill-typed field to `0` (fail-soft on the *measure*: a malformed record contributes `0` to
the total, never crashes the sum — the data-tier shadow of `Value.flatten`'s zero-default). This
is the named-field measure that replaces `KernelState.bal`'s whole-state scalar. -/
def balOf (v : Value) : Int := (v.scalar balanceField).getD 0

/-- **Record kernel state:** the finite set of live `accounts`, a per-cell **content-addressed
record** state (`cell : CellId → Value`, each a `Value.record` carrying at least a `balance`
field), and the capability table. This is `KernelState` with `bal : CellId → ℤ` lifted to
`cell : CellId → Value` — the concrete dregg2 cell. -/
structure RecordKernelState where
  /-- The finite set of live cells whose balances are tracked / conserved. -/
  accounts : Finset CellId
  /-- Per-cell content-addressed record state (each carries a `balance` field). -/
  cell     : CellId → Value
  /-- The capability table (lift of l4v `Caps`). -/
  caps     : Caps

/-- **The `balance`-domain measure** over the record cell-state: the total `balance` field across
the live accounts. This is the conserved quantity — a domain measure over the named `balance`
field (the `Spec.conservedInDomain Domain.balance` shape), NOT the whole `Value`. -/
def recTotal (k : RecordKernelState) : ℤ := ∑ c ∈ k.accounts, balOf (k.cell c)

/-! ## The record-cell transfer: debit/credit the `balance` FIELD. -/

/-- Set the `balance` field of a record cell to `v` (overwriting in place; a non-record value
becomes a singleton `balance` record, keeping the update total). This is the named-field write
that the transfer uses — it touches ONLY the `balance` field, leaving every other field of the
content-addressed record intact. -/
def setBalance (cell : Value) (v : Int) : Value :=
  match cell with
  | .record fs => .record (setBalanceList fs v)
  | _          => .record [(balanceField, .int v)]
where
  setBalanceList : List (FieldName × Value) → Int → List (FieldName × Value)
  | [],            v => [(balanceField, .int v)]
  | (k, x) :: rest, v => if k == balanceField then (balanceField, .int v) :: rest
                         else (k, x) :: setBalanceList rest v

/-- After `setBalance cell v`, reading the `balance` field returns exactly `v` (the write/read
law for the named-field measure). -/
theorem setBalance_balOf (cell : Value) (v : Int) : balOf (setBalance cell v) = v := by
  have hlist : ∀ fs : List (FieldName × Value),
      ((Value.record (setBalance.setBalanceList fs v)).scalar balanceField) = some v := by
    intro fs
    induction fs with
    | nil => simp [setBalance.setBalanceList, Value.scalar, Value.field]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setBalance.setBalanceList]
        by_cases hk : (k == balanceField) = true
        · rw [if_pos hk]
          simp [Value.scalar, Value.field, balanceField]
        · have hkf : (k == balanceField) = false := by simpa using hk
          rw [if_neg hk]
          simp only [Value.scalar, Value.field] at ih ⊢
          rw [List.find?_cons_of_neg (by simpa using hkf)]
          exact ih
  unfold balOf setBalance
  cases cell with
  | record fs => rw [hlist fs]; rfl
  | int _  => simp [Value.scalar, Value.field, balanceField]
  | dig _  => simp [Value.scalar, Value.field, balanceField]
  | sym _  => simp [Value.scalar, Value.field, balanceField]

/-- The per-cell record after a transfer: debit `src`'s `balance`, credit `dst`'s, leave every
other cell's record untouched. The named-field analog of `Kernel.transferBal` — but it rewrites
the `balance` FIELD of a `Value` record, not a whole-state ℤ. -/
def recTransfer (cell : CellId → Value) (src dst : CellId) (amt : ℤ) : CellId → Value :=
  fun c =>
    if c = src then setBalance (cell c) (balOf (cell c) - amt)
    else if c = dst then setBalance (cell c) (balOf (cell c) + amt)
    else cell c

/-- **The executable record kernel transition.** Fail-closed: commits only when the actor is
authorized over `src` (reusing `Kernel.authorizedB` — same gate), the amount is non-negative and
available *in the `balance` field*, `src ≠ dst`, and both cells are live accounts. The post-state
rewrites the `balance` field of the two cells; the rest of each content-addressed record is
preserved. -/
def recKExec (k : RecordKernelState) (turn : Turn) : Option RecordKernelState :=
  if authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts then
    some { k with cell := recTransfer k.cell turn.src turn.dst turn.amt }
  else
    none

/-! ## The record kernel satisfies the laws — re-proved over the `balance` FIELD. -/

/-- The `balance`-field delta of a transfer at a single cell, factored into a debit-indicator +
credit-indicator (the named-field analog of `Kernel.transfer_sum_conserve`'s pointwise step). -/
theorem recTransfer_balOf_delta (cell : CellId → Value) (src dst : CellId) (amt : ℤ)
    (hne : src ≠ dst) (c : CellId) :
    balOf (recTransfer cell src dst amt c) - balOf (cell c)
      = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) := by
  unfold recTransfer
  rcases eq_or_ne c src with h1 | h1
  · have hcd : c ≠ dst := by rw [h1]; exact hne
    rw [if_pos h1, setBalance_balOf, if_pos h1, if_neg hcd]
    ring
  · rcases eq_or_ne c dst with h2 | h2
    · rw [if_neg h1, if_pos h2, setBalance_balOf, if_neg h1, if_pos h2]
      ring
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
      ring

/-- **Conservation core (the `balance` field):** a transfer between two distinct live accounts
preserves the total `balance` (debit and credit cancel in the named field). Reuses
`Kernel.sum_indicator` over the `balance`-field measure — the same single-point-cancellation
argument the scalar kernel uses, lifted to the record's `balance` field. -/
theorem recTransfer_balanceSum_conserve (acc : Finset CellId) (cell : CellId → Value)
    (src dst : CellId) (amt : ℤ) (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, balOf (recTransfer cell src dst amt c)) = ∑ c ∈ acc, balOf (cell c) := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hg : ∀ c ∈ acc, balOf (recTransfer cell src dst amt c) - balOf (cell c)
      = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) :=
    fun c _ => recTransfer_balOf_delta cell src dst amt hne c
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      sum_indicator acc src (-amt) hsrc, sum_indicator acc dst amt hdst]
  ring

/-- **Conservation (Law 1) — PROVED of the record kernel over the `balance` FIELD.** Every
committed record-cell turn preserves the total `balance` field across the live accounts. This is
`Kernel.exec_conserves` lifted from the whole-state ℤ to the named `balance` field of a
content-addressed `Value` record — the conserved quantity is now a domain measure over a field,
aligning with `Spec.conservedInDomain Domain.balance`. -/
theorem recKExec_conserves (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') : recTotal k' = recTotal k := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hne, hsrc, hdst⟩ := hg
    simpa [recTotal] using
      recTransfer_balanceSum_conserve k.accounts k.cell turn.src turn.dst turn.amt hsrc hdst hne
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **No state change without authority — PROVED** (the integrity/confinement core for the record
kernel: it never moves a cell's `balance` field on behalf of an unauthorized actor). Same gate
(`authorizedB`) as the scalar kernel — authority is orthogonal to the state representation. -/
theorem recKExec_authorized (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') : authorizedB k.caps turn = true := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed — PROVED.** An unauthorized turn does NOT commit on the record kernel. -/
theorem recKExec_unauthorized_fails (k : RecordKernelState) (turn : Turn)
    (h : authorizedB k.caps turn = false) : recKExec k turn = none := by
  unfold recKExec
  rw [if_neg]
  rintro ⟨ha, _⟩
  rw [h] at ha; exact absurd ha (by simp)

/-- **`recKExec` preserves the account set and cap table** (it rewrites only the `cell` records'
`balance` fields). The structural-frame fact the refinement square reads. PROVED. -/
theorem recKExec_frame (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') : k'.accounts = k.accounts ∧ k'.caps = k.caps := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; rw [← h]; exact ⟨rfl, rfl⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## Whole-execution conservation (the userspace-program layer). -/

/-- The record kernel as an `Execution.System`: a step is any committed record turn. -/
def recKernelSystem : System where
  Config := RecordKernelState
  Step k k' := ∃ turn, recKExec k turn = some k'

/-- **Conservation across an ENTIRE record-kernel run — PROVED** (`Execution.invariant_run`
lifting `recKExec_conserves`); the record-cell analog of `Kernel.kernel_run_conserves`. -/
theorem recKernel_run_conserves {k k' : RecordKernelState} (hrun : Run recKernelSystem k k') :
    recTotal k' = recTotal k := by
  have hpres : StepInvariant recKernelSystem (fun c => recTotal c = recTotal k) := by
    intro a b ha hstep
    obtain ⟨turn, hturn⟩ := hstep
    rw [recKExec_conserves a b turn hturn]; exact ha
  exact invariant_run hpres hrun rfl

/-! ## The four `StepInv` conjuncts over the record cell (the chained record kernel). -/

/-- The record kernel state plus its **receipt chain** (the append-only audit log). The record-cell
analog of `StepComplete.ChainedState`. -/
structure RecChainedState where
  kernel : RecordKernelState
  log    : List Turn

/-- The chained record executor: run `recKExec`, and on success extend the receipt chain. -/
def recCexec (s : RecChainedState) (t : Turn) : Option RecChainedState :=
  match recKExec s.kernel t with
  | some k' => some { kernel := k', log := t :: s.log }
  | none    => none

/-- **The full per-step invariant over the record cell** — all four `StepInv` conjuncts
(Conservation over the `balance` field ∧ Authority ∧ ChainLink ∧ ObsAdvance). The record-cell
realization of `StepComplete.fullStepInv`. -/
def recFullStepInv (s : RecChainedState) (t : Turn) (s' : RecChainedState) : Prop :=
  recTotal s'.kernel = recTotal s.kernel ∧
  authorizedB s.kernel.caps t = true ∧
  s'.log = t :: s.log ∧
  s'.log.length = s.log.length + 1

/-- **`recCexec_attests` — the record kernel is STEP-COMPLETE (PROVED).** Every committed chained
record-cell step attests the FULL `StepInv` over the content-addressed cell: Conservation (of the
`balance` field) ∧ Authority ∧ ChainLink ∧ ObsAdvance. This is `StepComplete.cexec_attests` lifted
to the record cell-state — step-completeness holds BY CONSTRUCTION over the concrete cell, not just
the toy scalar. -/
theorem recCexec_attests {s s' : RecChainedState} {t : Turn} (h : recCexec s t = some s') :
    recFullStepInv s t s' := by
  unfold recCexec at h
  split at h
  · next k' heq =>
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_, rfl, rfl⟩
    · exact recKExec_conserves s.kernel k' t heq           -- Conservation (balance field)
    · exact recKExec_authorized s.kernel k' t heq          -- Authority
  · exact absurd h (by simp)

/-- The chained record kernel as a transition system. -/
def recChainedSystem : System where
  Config := RecChainedState
  Step s s' := ∃ t, recCexec s t = some s'

/-- **Soundness along any record-cell execution — PROVED.** Any state-predicate `Good` preserved by
every step that attests `recFullStepInv` holds at every reachable configuration of the whole chained
record-kernel execution — `Boundary.stepComplete_preserves` realized for the record cell. -/
theorem recChained_sound (Good : RecChainedState → Prop)
    (hpres : ∀ s t s', Good s → recFullStepInv s t s' → Good s')
    {s s' : RecChainedState} (hrun : Run recChainedSystem s s') (hs : Good s) : Good s' := by
  refine invariant_run (S := recChainedSystem) (I := Good) ?_ hrun hs
  intro a b ha hstep
  obtain ⟨t, ht⟩ := hstep
  exact hpres a t b ha (recCexec_attests ht)

/-- **Conservation of the `balance` field across the entire record-cell execution — PROVED**
(the headline instance of `recChained_sound`). -/
theorem recChained_run_conserves {s s' : RecChainedState} (hrun : Run recChainedSystem s s') :
    recTotal s'.kernel = recTotal s.kernel := by
  have : (fun c => recTotal c.kernel = recTotal s.kernel) s' :=
    recChained_sound (fun c => recTotal c.kernel = recTotal s.kernel)
      (by intro a b _ ha hinv; rw [hinv.1]; exact ha) hrun rfl
  exact this

/-! ## Axiom-hygiene tripwires — pin the re-proved keystones over the content-addressed cell. -/

#assert_axioms setBalance_balOf
#assert_axioms recTransfer_balanceSum_conserve
#assert_axioms recKExec_conserves
#assert_axioms recKExec_authorized
#assert_axioms recKExec_unauthorized_fails
#assert_axioms recKExec_frame
#assert_axioms recKernel_run_conserves
#assert_axioms recCexec_attests
#assert_axioms recChained_sound
#assert_axioms recChained_run_conserves

/-! ## It runs (`#eval`) — an account cell as a record. -/

/-- Cell 0's record: balance 100, nonce 0. Cell 1's record: balance 5. -/
def rs0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 0)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else .record [("balance", .int 0)]
    caps := fun _ => [] }

/-- Actor 0 transfers 30 to cell 1 (owns src 0). -/
def rt1 : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }
/-- Actor 2 attempts the same — unauthorized. -/
def rtBad : Turn := { actor := 2, src := 0, dst := 1, amt := 30 }

#eval (recKExec rs0 rt1).isSome                              -- true
#eval (recKExec rs0 rtBad).isSome                             -- false
#eval (recKExec rs0 rt1).map recTotal                        -- some 105 (conserved: 70 + 35)
#eval recTotal rs0                                           -- 105
-- The non-balance field (`nonce`) survives the transfer on the content-addressed record:
#eval (recKExec rs0 rt1).map (fun k => (k.cell 0).scalar "nonce")   -- some (some 0)
#eval (recKExec rs0 rt1).map (fun k => balOf (k.cell 0))            -- some 70

end Dregg2.Exec
