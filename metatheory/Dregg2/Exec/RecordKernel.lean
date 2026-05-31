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

/-! ### The OFF-LEDGER holding-store: the escrow side-table (dregg1's `self.escrows`).

dregg1's `apply_create_escrow` (`turn/src/executor/apply.rs:1674`) does NOT do a balance-conserving
two-cell transfer. It does a SINGLE-cell debit (`set_balance(creator − amount)`, :1766) and inserts
an `EscrowRecord` into an **off-ledger side-table** `self.escrows` (:1770), keyed by `escrow_id`,
carrying `{creator, recipient, amount, resolved}`. `apply_release_escrow` (:1959) credits the
recipient single-handedly and marks the record `resolved`; `apply_refund_escrow` (:2030) credits the
creator single-handedly and marks resolved. So per-effect Σδ ≠ 0 on the cell ledger — conservation
holds only ACROSS the create+release/refund PAIR, with the side-table accounting for the in-flight
amount. We model that side-table faithfully here. -/

/-- **`EscrowRecord`** — one entry of dregg1's off-ledger `escrows` side-table (`apply.rs:1773`),
keyed by `id`, carrying the locked `amount`, the `creator` (refund target) and `recipient` (release
target), and the `resolved` flag (set true once released/refunded). An UNRESOLVED record holds
`amount` of value OUT of the cell ledger — that is the holding-store value the pair conserves. -/
structure EscrowRecord where
  /-- the escrow id (dregg1's `[u8;32]` escrow_id, modelled as a `Nat` key). -/
  id        : Nat
  /-- the creator cell whose balance was debited at create (the refund target). -/
  creator   : CellId
  /-- the recipient cell credited on release. -/
  recipient : CellId
  /-- the locked amount held off-ledger while unresolved. -/
  amount    : ℤ
  /-- false until released/refunded; an unresolved record holds `amount` off-ledger. -/
  resolved  : Bool
deriving DecidableEq, Repr

/-- **Record kernel state:** the finite set of live `accounts`, a per-cell **content-addressed
record** state (`cell : CellId → Value`, each a `Value.record` carrying at least a `balance`
field), and the capability table — PLUS dregg1's two off-ledger side-tables, both DEFAULTING EMPTY
so every existing construction/proof that ignores them is unaffected (the additive extension):

  * `escrows` — the off-ledger escrow holding-store (`self.escrows`); unresolved records hold value
    out of the cell ledger (`apply.rs:1770`);
  * `nullifiers` — the spent-note nullifier SET (`self.note_nullifiers`, `apply.rs:941`); a
    `NoteSpend` inserts its nullifier and is rejected fail-closed if already present (double-spend).

This is `KernelState` with `bal : CellId → ℤ` lifted to `cell : CellId → Value`, additively extended
with the two holding stores — the concrete dregg2 cell + dregg1's real side-table accounting. -/
structure RecordKernelState where
  /-- The finite set of live cells whose balances are tracked / conserved. -/
  accounts : Finset CellId
  /-- Per-cell content-addressed record state (each carries a `balance` field). -/
  cell     : CellId → Value
  /-- The capability table (lift of l4v `Caps`). -/
  caps     : Caps
  /-- The off-ledger escrow holding-store (`self.escrows`); DEFAULTS EMPTY. -/
  escrows    : List EscrowRecord := []
  /-- The spent-note nullifier SET (`self.note_nullifiers`); DEFAULTS EMPTY. -/
  nullifiers : List Nat := []

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

/-! ## §ESCROW — the OFF-LEDGER holding-store semantics (faithful to dregg1's `apply.rs`).

The `recKExec` transfer above is balance-CONSERVING (the `transfer` effect, Σδ = 0). But dregg1's
escrow is NOT a transfer: `apply_create_escrow` debits ONE cell and parks the value in the off-ledger
`escrows` side-table; `apply_release_escrow`/`apply_refund_escrow` credit ONE cell and mark the
record resolved. So per-effect Σδ ≠ 0 on the cell ledger; the conserved quantity is the COMBINED
total (cell-ledger + the value held by unresolved escrows). This section models that faithfully and
proves the REAL invariant: value is conserved ACROSS the create+release/refund pair, with the
side-table accounting for the in-flight amount. -/

/-- **Single-cell credit** — add `amt` to one cell's `balance` field, leaving all other cells and the
side-tables untouched. The named-field realization of dregg1's `set_balance(old + amount)`
(`apply.rs:1964`/`:2035`) — a SINGLE-cell move, NOT a two-cell transfer. -/
def recCredit (cell : CellId → Value) (c : CellId) (amt : ℤ) : CellId → Value :=
  fun x => if x = c then setBalance (cell x) (balOf (cell x) + amt) else cell x

/-- **Single-cell debit** — subtract `amt` from one cell's `balance` field. dregg1's
`set_balance(old − amount)` (`apply.rs:1766`) at create — a SINGLE-cell move. -/
def recDebit (cell : CellId → Value) (c : CellId) (amt : ℤ) : CellId → Value :=
  fun x => if x = c then setBalance (cell x) (balOf (cell x) - amt) else cell x

/-- A single-cell credit shifts the cell-ledger total by `+amt` (the live account `c`'s `balance`
rises by `amt`; every other account is untouched). PROVED. -/
theorem recCredit_recTotal (acc : Finset CellId) (cell : CellId → Value) (c : CellId) (amt : ℤ)
    (hc : c ∈ acc) :
    (∑ x ∈ acc, balOf (recCredit cell c amt x)) = (∑ x ∈ acc, balOf (cell x)) + amt := by
  have key : (∑ x ∈ acc, balOf (recCredit cell c amt x)) - (∑ x ∈ acc, balOf (cell x)) = amt := by
    rw [← Finset.sum_sub_distrib]
    have hg : ∀ x ∈ acc, balOf (recCredit cell c amt x) - balOf (cell x)
        = (if x = c then amt else 0) := by
      intro x _
      unfold recCredit
      by_cases hx : x = c
      · rw [if_pos hx, setBalance_balOf, if_pos hx]; ring
      · rw [if_neg hx, if_neg hx]; ring
    rw [Finset.sum_congr rfl hg, sum_indicator acc c amt hc]
  omega

/-- A single-cell debit shifts the cell-ledger total by `−amt`. PROVED. -/
theorem recDebit_recTotal (acc : Finset CellId) (cell : CellId → Value) (c : CellId) (amt : ℤ)
    (hc : c ∈ acc) :
    (∑ x ∈ acc, balOf (recDebit cell c amt x)) = (∑ x ∈ acc, balOf (cell x)) - amt := by
  have key : (∑ x ∈ acc, balOf (recDebit cell c amt x)) - (∑ x ∈ acc, balOf (cell x)) = -amt := by
    rw [← Finset.sum_sub_distrib]
    have hg : ∀ x ∈ acc, balOf (recDebit cell c amt x) - balOf (cell x)
        = (if x = c then (-amt) else 0) := by
      intro x _
      unfold recDebit
      by_cases hx : x = c
      · rw [if_pos hx, setBalance_balOf, if_pos hx]; ring
      · rw [if_neg hx, if_neg hx]; ring
    rw [Finset.sum_congr rfl hg, sum_indicator acc c (-amt) hc]
  omega

/-! ### The holding-store value measure + the COMBINED conserved total. -/

/-- **`escrowHeld k`** — the total value currently parked in the off-ledger holding-store: the sum of
`amount` over the UNRESOLVED escrow records. This is the value held OUT of the cell ledger between a
create and its release/refund. -/
def escrowHeld (k : RecordKernelState) : ℤ :=
  (k.escrows.filter (fun r => !r.resolved)).foldr (fun r acc => r.amount + acc) 0

/-- **`recTotalWithEscrow k`** — the COMBINED conserved quantity: the cell-ledger `balance` total
PLUS the value held off-ledger by unresolved escrows. This — not the per-cell `recTotal` — is what
the create+release/refund pair conserves, exactly as dregg1's side-table accounting demands. -/
def recTotalWithEscrow (k : RecordKernelState) : ℤ := recTotal k + escrowHeld k

/-- Prepending an UNRESOLVED record raises `escrowHeld` by its `amount`. PROVED (definitional unfold
of the filtered fold). -/
theorem escrowHeld_cons_unresolved (k : RecordKernelState) (r : EscrowRecord) (hr : r.resolved = false) :
    escrowHeld { k with escrows := r :: k.escrows } = escrowHeld k + r.amount := by
  unfold escrowHeld
  simp only [List.filter_cons, show (!r.resolved) = true from by simp [hr],
             Bool.false_eq_true, if_true, List.foldr_cons]
  omega

/-! ### The faithful escrow lifecycle: create (debit + park), release/refund (credit + resolve). -/

/-- **`createEscrowRaw`** — dregg1's `apply_create_escrow` (`apply.rs:1674`) at the state level:
a SINGLE-cell debit of `amount` from `creator` PLUS an insert of an unresolved `EscrowRecord` into the
off-ledger holding-store. NOT a two-cell transfer. The cell-ledger total DROPS by `amount`; the
holding-store value RISES by `amount`; the COMBINED total is preserved. -/
def createEscrowRaw (k : RecordKernelState) (id creator recipient : CellId) (amount : ℤ) :
    RecordKernelState :=
  { k with cell := recDebit k.cell creator amount
           escrows := { id := id, creator := creator, recipient := recipient,
                        amount := amount, resolved := false } :: k.escrows }

/-- Mark the FIRST unresolved escrow record with the given `id` resolved (dregg1's
`escrows.get_mut(escrow_id).resolved = true`, `apply.rs:1969`/`:2040` — a HashMap keyed by id, so
exactly ONE entry is mutated). Records before it, after it, and with other ids are untouched. -/
def markResolved (escrows : List EscrowRecord) (id : Nat) : List EscrowRecord :=
  match escrows with
  | []      => []
  | r :: rs => if r.id = id ∧ r.resolved = false then { r with resolved := true } :: rs
               else r :: markResolved rs id

/-- **`settleEscrowRaw`** — the shared body of `apply_release_escrow`/`apply_refund_escrow`: a
SINGLE-cell credit of `amount` to the settlement target (`recipient` on release, `creator` on refund)
PLUS marking the record resolved. The cell-ledger total RISES by `amount`; the holding-store value
DROPS by `amount` (the record leaves the unresolved set); the COMBINED total is preserved. -/
def settleEscrowRaw (k : RecordKernelState) (id target : CellId) (amount : ℤ) : RecordKernelState :=
  { k with cell := recCredit k.cell target amount
           escrows := markResolved k.escrows id }

/-- **`createEscrow` (executable, fail-closed).** Commits only when the actor is authorized over the
`creator` cell (same `authorizedB` gate as `transfer`), the amount is non-negative and available in
the creator's `balance`, the creator is a live account, and the `id` is NOT already in use (dregg1's
"escrow_id already exists" check, `apply.rs:1736`). On commit: single-cell debit + park the record. -/
def createEscrowK (k : RecordKernelState) (id : Nat) (actor creator recipient : CellId) (amount : ℤ) :
    Option RecordKernelState :=
  if authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ balOf (k.cell creator) ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id) then
    some (createEscrowRaw k id creator recipient amount)
  else none

/-- **`releaseEscrow` (executable, fail-closed).** Looks up the unresolved record by `id`; on success
single-cell credits the `recipient` and marks resolved. Rejects a missing or already-resolved record
(dregg1's "escrow not found" / "already resolved", `apply.rs:1812`/`:1820`). The crypto/condition
check (proof/signatures) is the §8 portal carried at the effect layer — here we model the state move
gated on the record being present-and-unresolved. -/
def releaseEscrowK (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => some (settleEscrowRaw k id r.recipient r.amount)
  | none   => none

/-- **`refundEscrow` (executable, fail-closed).** Looks up the unresolved record by `id`; on success
single-cell credits the `creator` (refund target) and marks resolved (dregg1's `apply_refund_escrow`,
`apply.rs:1976`). The timeout gate is carried at the effect layer. -/
def refundEscrowK (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => some (settleEscrowRaw k id r.creator r.amount)
  | none   => none

/-! ### The REAL escrow invariants. -/

/-- **`escrow_create_debits` — PROVED.** A committed `createEscrow` is a SINGLE-cell debit: the
cell-ledger total `recTotal` DROPS by exactly `amount`, and the holding-store grows by the new
record (it is NOT a balance-conserving transfer on the cell ledger). This is the faithful contrast
with the old paired shadow. -/
theorem escrow_create_debits {k k' : RecordKernelState} {id : Nat} {actor creator recipient : CellId}
    {amount : ℤ} (h : createEscrowK k id actor creator recipient amount = some k') :
    recTotal k' = recTotal k - amount ∧
      k'.escrows = { id := id, creator := creator, recipient := recipient,
                     amount := amount, resolved := false } :: k.escrows := by
  unfold createEscrowK at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ balOf (k.cell creator) ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    refine ⟨?_, rfl⟩
    simp only [recTotal, createEscrowRaw]
    exact recDebit_recTotal k.accounts k.cell creator amount hlive
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`escrow_create_conserves_combined` — PROVED.** A committed `createEscrow` PRESERVES the COMBINED
total (cell-ledger + holding-store): the `−amount` cell-ledger debit is exactly offset by the
`+amount` rise in the off-ledger holding-store. Value MOVES into the side-table; nothing is created
or destroyed. -/
theorem escrow_create_conserves_combined {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {amount : ℤ}
    (h : createEscrowK k id actor creator recipient amount = some k') :
    recTotalWithEscrow k' = recTotalWithEscrow k := by
  unfold createEscrowK at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ balOf (k.cell creator) ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    set newRec : EscrowRecord := { id := id, creator := creator, recipient := recipient,
                                   amount := amount, resolved := false } with hnewRec
    show recTotalWithEscrow (createEscrowRaw k id creator recipient amount)
       = recTotalWithEscrow k
    unfold recTotalWithEscrow createEscrowRaw
    -- The post-state's cell-ledger total: a single-cell debit.
    have hcell : recTotal { k with cell := recDebit k.cell creator amount,
                                   escrows := newRec :: k.escrows }
        = recTotal k - amount := by
      show (∑ x ∈ k.accounts, balOf (recDebit k.cell creator amount x)) = _
      simpa [recTotal] using recDebit_recTotal k.accounts k.cell creator amount hlive
    -- The post-state's holding-store value: the parked record raises it.
    have hheld : escrowHeld { k with cell := recDebit k.cell creator amount,
                                     escrows := newRec :: k.escrows }
        = escrowHeld k + amount := by
      have hc := escrowHeld_cons_unresolved
        { k with cell := recDebit k.cell creator amount } newRec rfl
      simpa [hnewRec] using hc
    rw [hcell, hheld]; ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- The raw escrow-list filtered-sum (the unfolded `escrowHeld`). -/
def heldSum (es : List EscrowRecord) : ℤ :=
  (es.filter (fun r => !r.resolved)).foldr (fun r acc => r.amount + acc) 0

theorem escrowHeld_eq_heldSum (k : RecordKernelState) : escrowHeld k = heldSum k.escrows := rfl

/-- **The pair-conservation CORE (PROVED by list induction).** Marking the FIRST unresolved record
whose id matches `id` as resolved drops the unresolved-held sum by exactly that record's `amount`.
The faithful side-table accounting: when a release/refund resolves the in-flight record, the value it
held leaves the off-ledger store by precisely its amount. `markResolved` and `find?` walk the list in
lockstep on the same `id ∧ unresolved` predicate, so the dropped amount is exactly the found record's. -/
theorem heldSum_markResolved_found (id : Nat) (r : EscrowRecord) :
    ∀ (es : List EscrowRecord),
      es.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      heldSum (markResolved es id) = heldSum es - r.amount := by
  intro es
  induction es with
  | nil => intro hfind; simp [List.find?] at hfind
  | cons hd tl ih =>
      intro hfind
      simp only [List.find?_cons] at hfind
      by_cases hmatch : (hd.id = id ∧ hd.resolved = false)
      · -- head matches the predicate: it IS the found, unresolved record.
        obtain ⟨hid, hres⟩ := hmatch
        rw [show (decide (hd.id = id ∧ hd.resolved = false)) = true from by simp [hid, hres]] at hfind
        simp only [Option.some.injEq] at hfind
        -- hfind : hd = r ; rewrite the goal's `r` back to `hd`.
        subst hfind
        unfold heldSum markResolved
        rw [if_pos ⟨hid, hres⟩]
        -- LHS: head now resolved ⇒ filtered OUT; RHS: head was unresolved ⇒ filtered IN.
        simp only [List.filter_cons,
                   show (!({hd with resolved := true} : EscrowRecord).resolved) = false from by simp,
                   show (!hd.resolved) = true from by simp [hres],
                   Bool.false_eq_true, if_false, if_true, List.foldr_cons]
        omega
      · -- head does NOT match the predicate: carried unchanged; recurse on the tail.
        rw [show (decide (hd.id = id ∧ hd.resolved = false)) = false from by
              simp [decide_eq_false_iff_not, hmatch]] at hfind
        have ihr := ih hfind
        -- markResolved (hd::tl) id = hd :: markResolved tl id (head doesn't match).
        have hmr : markResolved (hd :: tl) id = hd :: markResolved tl id := by
          conv_lhs => rw [markResolved]
          rw [if_neg hmatch]
        rw [hmr]
        -- Both heldSums share the same head `hd`; the tail delta is `ihr`.
        unfold heldSum
        simp only [List.filter_cons]
        by_cases hhdres : hd.resolved = false
        · rw [show (!hd.resolved) = true from by simp [hhdres]]
          simp only [Bool.false_eq_true, if_true, List.foldr_cons]
          have ihr' : (List.filter (fun r => !r.resolved) (markResolved tl id)).foldr
              (fun r acc => r.amount + acc) 0
              = (List.filter (fun r => !r.resolved) tl).foldr (fun r acc => r.amount + acc) 0
                - r.amount := ihr
          rw [ihr']; ring
        · rw [show (!hd.resolved) = false from by simp [hhdres]]
          simp only [Bool.false_eq_true, if_false]
          have ihr' : (List.filter (fun r => !r.resolved) (markResolved tl id)).foldr
              (fun r acc => r.amount + acc) 0
              = (List.filter (fun r => !r.resolved) tl).foldr (fun r acc => r.amount + acc) 0
                - r.amount := ihr
          rw [ihr']

/-- **`escrow_settle_conserves_combined` — PROVED.** A release/refund that settles the found record
to `target` (`recipient` on release, `creator` on refund) PRESERVES the COMBINED total: the `+amount`
single-cell credit is exactly offset by the holding-store DROP as the record leaves the unresolved
set. Value moves OUT of the side-table back onto the ledger; the combined total is fixed. -/
theorem escrow_settle_conserves_combined (k : RecordKernelState) (id target : CellId) (r : EscrowRecord)
    (htgt : target ∈ k.accounts)
    (hfind : k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r) :
    recTotalWithEscrow (settleEscrowRaw k id target r.amount) = recTotalWithEscrow k := by
  have hcell : recTotal (settleEscrowRaw k id target r.amount) = recTotal k + r.amount := by
    show (∑ x ∈ k.accounts, balOf (recCredit k.cell target r.amount x)) = _
    simpa [recTotal] using recCredit_recTotal k.accounts k.cell target r.amount htgt
  have hheld : escrowHeld (settleEscrowRaw k id target r.amount) = escrowHeld k - r.amount := by
    show heldSum (markResolved k.escrows id) = heldSum k.escrows - r.amount
    exact heldSum_markResolved_found id r k.escrows hfind
  show recTotal (settleEscrowRaw k id target r.amount) + escrowHeld (settleEscrowRaw k id target r.amount)
     = recTotal k + escrowHeld k
  rw [hcell, hheld]; ring

/-- **`releaseEscrow` PRESERVES the COMBINED total — PROVED** (the headline pair-conservation fact for
release). Reads off `escrow_settle_conserves_combined`. -/
theorem releaseEscrow_conserves_combined {k k' : RecordKernelState} {id : Nat}
    (htgt : ∀ r, k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      r.recipient ∈ k.accounts)
    (h : releaseEscrowK k id = some k') :
    recTotalWithEscrow k' = recTotalWithEscrow k := by
  unfold releaseEscrowK at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only [Option.some.injEq] at h; subst h
      exact escrow_settle_conserves_combined k id r.recipient r (htgt r hfind) hfind

/-- **`refundEscrow` PRESERVES the COMBINED total — PROVED** (the headline pair-conservation fact for
refund: value returns to the creator, combined fixed). -/
theorem refundEscrow_conserves_combined {k k' : RecordKernelState} {id : Nat}
    (htgt : ∀ r, k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      r.creator ∈ k.accounts)
    (h : refundEscrowK k id = some k') :
    recTotalWithEscrow k' = recTotalWithEscrow k := by
  unfold refundEscrowK at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only [Option.some.injEq] at h; subst h
      exact escrow_settle_conserves_combined k id r.creator r (htgt r hfind) hfind

/-! ### §NULLIFIER — the spent-note SET (faithful to dregg1's `note_nullifiers`, `apply.rs:941`).

dregg1's `apply_note_spend` does NOT set a `"nullifier_spent"=1` scalar field. It inserts the
nullifier into an off-ledger SET `self.note_nullifiers` with DOUBLE-SPEND REJECTION: if the nullifier
is already present, the turn fails-closed ("double-spend: nullifier already in note_nullifiers set",
`apply.rs:945`). We model that set faithfully and prove no nullifier can be spent twice. -/

/-- **`noteSpendNullifier` (executable, fail-closed).** Insert `nf` into the nullifier set IF it is
NOT already present; reject (fail-closed `none`) on a double-spend (`apply.rs:942`). The crypto
(STARK spending proof + nullifier derivation) is the §8 portal carried at the effect layer; here we
model the ledger-side double-spend gate, which is what prevents replay. -/
def noteSpendNullifier (k : RecordKernelState) (nf : Nat) : Option RecordKernelState :=
  if nf ∈ k.nullifiers then none
  else some { k with nullifiers := nf :: k.nullifiers }

/-- **`note_no_double_spend` — PROVED.** A nullifier already in the spent set CANNOT be spent again:
`noteSpendNullifier` fails-closed. This is the real anti-replay invariant (the SET prevents it), NOT
a scalar flag. -/
theorem note_no_double_spend (k : RecordKernelState) (nf : Nat) (h : nf ∈ k.nullifiers) :
    noteSpendNullifier k nf = none := by
  unfold noteSpendNullifier; rw [if_pos h]

/-- **`note_spend_inserts` — PROVED.** A committed `noteSpendNullifier` actually inserts `nf` into the
set (so a SUBSEQUENT spend of the same `nf` is rejected by `note_no_double_spend`). -/
theorem note_spend_inserts {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') : nf ∈ k'.nullifiers := by
  unfold noteSpendNullifier at h
  by_cases hin : nf ∈ k.nullifiers
  · rw [if_pos hin] at h; exact absurd h (by simp)
  · rw [if_neg hin] at h; simp only [Option.some.injEq] at h; subst h; simp

/-- **`note_spend_then_reject` — PROVED (the composed anti-replay).** After a committed spend of `nf`,
a second spend of the SAME `nf` on the resulting state fails-closed. Double-spend is impossible. -/
theorem note_spend_then_reject {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') : noteSpendNullifier k' nf = none :=
  note_no_double_spend k' nf (note_spend_inserts h)

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
-- The faithful escrow holding-store + nullifier-set keystones:
#assert_axioms recCredit_recTotal
#assert_axioms recDebit_recTotal
#assert_axioms escrowHeld_cons_unresolved
#assert_axioms escrow_create_debits
#assert_axioms escrow_create_conserves_combined
#assert_axioms heldSum_markResolved_found
#assert_axioms escrow_settle_conserves_combined
#assert_axioms releaseEscrow_conserves_combined
#assert_axioms refundEscrow_conserves_combined
#assert_axioms note_no_double_spend
#assert_axioms note_spend_inserts
#assert_axioms note_spend_then_reject

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
