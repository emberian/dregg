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

/-- **An asset identity.** A dregg cell holds MANY assets, and conservation must be **per-asset**,
never one aggregate scalar (`EFFECT-ISA-DESIGN.md:315,320-323`; `dregg2 §2.1`). A turn that moves
5 of asset 0 must leave the supply of asset 1 *literally untouched* — folding all assets into one
sum would let a cell silently swap one asset for another while the aggregate stays put. The
conserved quantity is therefore a *family* indexed by `AssetId` (see `§MULTI-ASSET` below). -/
abbrev AssetId : Type := Nat

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
  /-- **The asset class of the locked value** (`META-FILL C`). dregg cells hold MANY assets, so an
  escrow lock parks `amount` of a SPECIFIC asset — and the combined per-asset measure must move at
  THAT asset only (`recTotalAssetWithEscrow r.asset`), every other asset literally untouched. Added
  ADDITIVELY (`:= 0`) so every existing 5-field `EscrowRecord` literal stays compiling (the default
  fills the 6th); the Wave-4 non-vacuity guard `#eval` LOCKS at a NON-ZERO asset to prove the default
  does NOT collapse to a single-asset shadow. -/
  asset     : AssetId := 0
  /-- **The BRIDGE tag** (Wave-5 `PHASE-BRIDGE`). A cross-chain bridge lock shares the SAME off-ledger
  holding-store as escrow — dregg1's `pending_bridges` is the bridge-shaped twin of `escrows`
  (`cell/src/note_bridge.rs`: a `PendingBridge` parks `value`/`asset_type` while `Locked`, AWAITING the
  other-chain confirmation). We reuse the escrow store with THIS additive tag (`:= false`, so every
  existing 6-field `EscrowRecord` literal stays compiling — the default fills the 7th) rather than a
  parallel side-table (least new machinery). The tag separates the two RESOLUTION semantics: an escrow
  release/refund SETTLES back onto the ledger (combined CONSERVED), whereas a bridge FINALIZE BURNS the
  locked value — it genuinely LEFT for the other chain, a disclosed outflow, so the COMBINED measure
  DROPS by the bridged amount (modelled honestly as a no-credit resolve). A bridge CANCEL
  (timeout/failure) refunds the originator (combined conserved, like escrow refund). -/
  bridge    : Bool := false
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
  /-- **The note COMMITMENT SET** (`META-FILL C`, closing `#121`): the grow-only dual of
  `nullifiers`. dregg1's `apply_note_create` inserts a fresh Pedersen commitment into the off-ledger
  commitment tree (a §8 CryptoPortal-gated range proof guards the hidden value). A `noteCreate` grows
  THIS set (NOT `bal`, NOT `nullifiers`, NOT `escrows`) — so it is bal-NEUTRAL and genuinely distinct
  from escrow/obligation/noteSpend (the `#121` de-conflation). DEFAULTS EMPTY (the additive
  extension, exactly as `nullifiers` was added). -/
  commitments : List Nat := []
  /-- **The genuine per-asset balance ledger** `bal c a` — the (ℤ-valued, debt-capable) amount of
  asset `a` held by cell `c`. dregg cells hold MANY assets; conservation is PER-ASSET
  (`EFFECT-ISA-DESIGN.md:315,320-323`), never one aggregate scalar. DEFAULTS to the empty ledger so
  every existing construction/proof that ignores it is unaffected (the additive extension, exactly
  as `escrows`/`nullifiers` were added). This is the destination conserved measure the per-asset
  transition (`§MULTI-ASSET`) preserves; the scalar `balance` field is its legacy asset-view, and
  the executable `FullAction` dispatch migrates onto `bal` (`DREGG2-GAP-MAP.md FILL 1`). -/
  bal        : CellId → AssetId → ℤ := fun _ _ => 0

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

/-! ## §MULTI-ASSET — the per-asset `CONSERVATION_VECTOR` over the REAL executable state + gate.

`recKExec`/`recTotal` above conserve ONE scalar (the `balance` field). A dregg cell holds MANY
assets, and conservation must be PER-ASSET — a committed turn moving asset `a` must leave EVERY
other asset's supply *literally untouched*; folding all assets into one aggregate would let a cell
silently swap asset A for asset B while the scalar stays put (`EFFECT-ISA-DESIGN.md:315,320-323`;
`DREGG2-GAP-MAP.md FILL 1`, "the #1 soundness gap"). `Exec.MultiAsset` proved exactly this — but
over a deliberately PARALLEL `MACellId`/`maAuthorizedB` toy that "cannot clash with `Kernel.CellId`"
and is imported by nothing executable (a sibling law). Here we re-prove it over the REAL
`RecordKernelState.bal` ledger and the REAL `authorizedB k.caps` gate — the SAME state type and
authority the FFI's `execFullTurn` runs — so the per-asset law is no longer a sibling. (Migrating
the executable `FullAction` dispatch onto `bal` + the negative differential is the next phase.) -/

/-- The per-asset balance ledger after a transfer of asset `a`: debit `src`, credit `dst` in the
`a` column ONLY; every other cell and **every other asset** is returned unchanged. The named-field
`recTransfer`'s multi-asset analog, over the genuine `CellId → AssetId → ℤ` ledger. -/
def recTransferBal (bal : CellId → AssetId → ℤ) (src dst : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun c b =>
    if b = a then
      (if c = src then bal c b - amt else if c = dst then bal c b + amt else bal c b)
    else bal c b

/-- **The executable per-asset transition** over the real record state. Fail-closed: commits only
when the actor is authorized over `src` (the SAME `authorizedB k.caps` gate as the scalar kernel —
NOT `MultiAsset`'s `maAuthorizedB` toy), the amount is non-negative and available *in that asset*,
`src ≠ dst`, and both cells are live accounts. Rewrites ONLY the `bal` ledger's `a` column. -/
def recKExecAsset (k : RecordKernelState) (turn : Turn) (a : AssetId) : Option RecordKernelState :=
  if authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts then
    some { k with bal := recTransferBal k.bal turn.src turn.dst a turn.amt }
  else
    none

/-- **Total supply of asset `a`** over the live accounts — the conserved family, indexed by
`AssetId` (NOT collapsed to one scalar). The per-asset analog of `recTotal`. -/
def recTotalAsset (k : RecordKernelState) (a : AssetId) : ℤ := ∑ c ∈ k.accounts, k.bal c a

/-- Per-asset conservation core (moved asset): for the moved asset `a`, a transfer between two
distinct live accounts preserves its column sum (debit and credit cancel). Reuses `sum_indicator`,
the same single-point-cancellation the scalar kernel uses. -/
theorem recTransferBal_sum_conserve_moved (acc : Finset CellId) (bal : CellId → AssetId → ℤ)
    (src dst : CellId) (a : AssetId) (amt : ℤ) (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, recTransferBal bal src dst a amt c a) = ∑ c ∈ acc, bal c a := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hg : ∀ c ∈ acc, recTransferBal bal src dst a amt c a - bal c a
      = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) := by
    intro c _
    unfold recTransferBal
    rw [if_pos rfl]
    rcases eq_or_ne c src with h1 | h1
    · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hne]; ring
    · rcases eq_or_ne c dst with h2 | h2
      · subst h2; rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      sum_indicator acc src (-amt) hsrc, sum_indicator acc dst amt hdst]
  ring

/-- Per-asset conservation core (untouched asset): for any asset `b ≠ a`, the transfer of asset `a`
leaves the entire `b` column literally unchanged — pointwise, hence the sum. -/
theorem recTransferBal_untouched (bal : CellId → AssetId → ℤ) (src dst : CellId)
    (a b : AssetId) (amt : ℤ) (hb : b ≠ a) (c : CellId) :
    recTransferBal bal src dst a amt c b = bal c b := by
  unfold recTransferBal; rw [if_neg hb]

/-- **THE KEYSTONE — per-asset conservation, PROVED of the EXECUTABLE record kernel over the REAL
gate.** Every committed per-asset transfer preserves `recTotalAsset k b` for EVERY asset `b`: the
moved asset by the debit/credit cancellation, every other asset because its column is untouched.
This is the `CONSERVATION_VECTOR` (`DREGG2-GAP-MAP.md FILL 1`) on the real executable
`RecordKernelState` — the multi-asset refinement of `recKExec_conserves`, no longer a `MultiAsset`
sibling toy. -/
theorem recKExecAsset_conserves_per_asset (k k' : RecordKernelState) (turn : Turn) (a : AssetId)
    (h : recKExecAsset k turn a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold recKExecAsset at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hne, hsrc, hdst⟩ := hg
    show (∑ c ∈ k.accounts, recTransferBal k.bal turn.src turn.dst a turn.amt c b)
        = ∑ c ∈ k.accounts, k.bal c b
    rcases eq_or_ne b a with hb | hb
    · subst hb
      exact recTransferBal_sum_conserve_moved k.accounts k.bal turn.src turn.dst b turn.amt
        hsrc hdst hne
    · exact Finset.sum_congr rfl
        (fun c _ => recTransferBal_untouched k.bal turn.src turn.dst a b turn.amt hb c)
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **No state change without authority — PROVED** for the per-asset kernel: it never moves a cell's
resource on behalf of an unauthorized actor. The REAL `authorizedB` gate, not `MultiAsset`'s
`maAuthorizedB` toy. -/
theorem recKExecAsset_authorized (k k' : RecordKernelState) (turn : Turn) (a : AssetId)
    (h : recKExecAsset k turn a = some k') : authorizedB k.caps turn = true := by
  unfold recKExecAsset at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed — PROVED.** An unauthorized per-asset turn does NOT commit. -/
theorem recKExecAsset_unauthorized_fails (k : RecordKernelState) (turn : Turn) (a : AssetId)
    (h : authorizedB k.caps turn = false) : recKExecAsset k turn a = none := by
  unfold recKExecAsset
  rw [if_neg]
  rintro ⟨ha, _⟩
  rw [h] at ha; exact absurd ha (by simp)

/-- **The cross-asset NON-LAUNDERING fact — PROVED.** A committed transfer of asset `a` CANNOT
change asset `b ≠ a`'s total supply. This is exactly what a SCALAR kernel cannot guarantee: a
scalar that sums one aggregate would accept a turn that mints asset B while burning an equal amount
of asset A (aggregate-conserving, per-asset-VIOLATING). The per-asset ledger makes that laundering
unrepresentable as a single conservative transfer — the soundness content of `CONSERVATION_VECTOR`. -/
theorem recKExecAsset_no_cross_asset_leak (k k' : RecordKernelState) (turn : Turn) (a b : AssetId)
    (h : recKExecAsset k turn a = some k') (_hb : b ≠ a) :
    recTotalAsset k' b = recTotalAsset k b :=
  recKExecAsset_conserves_per_asset k k' turn a h b

/-! ## Per-asset ACCOUNT-GROWTH: a fresh cell, born EMPTY in every asset (`META-FILL C`).

dregg1's `Effect::CreateCell` (`turn/src/executor/apply.rs:748`) is a PRIVILEGED creation of a FRESH
cell that — per `apply_create_cell`'s `CreateCellNonZeroBalance` rejection (`apply.rs:757`) — is born
with `balance == 0` (`Cell::with_balance(.,.,0)`): conservation-NEUTRAL. We grow the per-asset ledger's
index set (`accounts`) while keeping the conserved measure `recTotalAsset` UNCHANGED, by INSERTING the
fresh cell AND resetting its `bal` column to `0` for every asset — so the new term in the sum is exactly
`0`. The `bal`-reset is LOAD-BEARING: a freshly-inserted id that had EVER been credited (a re-inserted
previously-credited id) would silently re-introduce supply on insert. Resetting unconditionally defends
against that (neutrality is PROVED, not assumed). -/

/-- **`createCellIntoAsset` — grow `accounts` by the fresh `newCell` AND reset its per-asset `bal`
column to `0`.** The per-asset analog of `EffectsSupply.createCellInto`, over the `bal` ledger rather
than the named `balance` field. The fresh cell is born EMPTY in EVERY asset (dregg1-faithful
`balance == 0`), so it contributes exactly `0` to every `recTotalAsset b`. -/
def createCellIntoAsset (k : RecordKernelState) (newCell : CellId) : RecordKernelState :=
  { k with accounts := insert newCell k.accounts
           bal := fun c a => if c = newCell then 0 else k.bal c a }

/-- **`recTotalAsset_insert_fresh` — ACCOUNT-GROWTH IS CONSERVATION-NEUTRAL (PROVED).** Growing
`accounts` by a FRESH `newCell` while resetting its `bal` column leaves `recTotalAsset k b` UNCHANGED
for EVERY asset `b`. NON-VACUOUS: the conclusion is an equality of sums over a STRICTLY LARGER index set
(`insert newCell k.accounts`) — it asserts the fresh cell contributes EXACTLY `0` (not that `accounts`
is unchanged: it genuinely grew). The fresh term is `0` because the `bal`-reset wrote it `0`; every OLD
cell is unchanged because `c ≠ newCell` (`hfresh`). Mirrors `EffectsSupply.createCellInto_recTotal`:
`Finset.sum_insert hfresh` for the fresh term + `Finset.sum_congr` for the old cells. Without the
`bal`-reset, a re-inserted previously-credited id would make this FALSE (the supply-amplification hole),
so the reset is load-bearing. -/
theorem recTotalAsset_insert_fresh (k : RecordKernelState) (newCell : CellId) (b : AssetId)
    (hfresh : newCell ∉ k.accounts) :
    recTotalAsset (createCellIntoAsset k newCell) b = recTotalAsset k b := by
  unfold recTotalAsset createCellIntoAsset
  rw [Finset.sum_insert hfresh]
  -- the fresh cell's reset column is `0` (the structure projection beta-reduces the `if`):
  simp only [if_pos, zero_add]
  -- every OLD cell is unchanged (`c ≠ newCell`):
  apply Finset.sum_congr rfl
  intro c hc
  have hcne : c ≠ newCell := fun heq => hfresh (heq ▸ hc)
  simp only [if_neg hcne]

/-- **`createCellIntoAsset_grows_accounts` — the GROWTH has teeth (PROVED).** After `createCellIntoAsset`,
the new cell IS a live account: `newCell ∈ accounts`. Witnesses that the neutrality theorem is NOT a
no-op — the index set genuinely grew. -/
theorem createCellIntoAsset_grows_accounts (k : RecordKernelState) (newCell : CellId) :
    newCell ∈ (createCellIntoAsset k newCell).accounts := by
  unfold createCellIntoAsset; exact Finset.mem_insert_self _ _

/-- **`createCellIntoAsset_caps` — caps framed (PROVED).** Account-growth never edits the cap table. -/
theorem createCellIntoAsset_caps (k : RecordKernelState) (newCell : CellId) :
    (createCellIntoAsset k newCell).caps = k.caps := rfl

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

/-! ## §ESCROW-PER-ASSET — the off-ledger holding-store on the GENUINE per-asset `bal` ledger (`META-FILL C`).

The scalar escrow above (`createEscrowRaw`/`settleEscrowRaw`, `escrowHeld`/`recTotalWithEscrow`)
moves the named `balance` FIELD — ONE asset. But dregg cells hold MANY assets, so an escrow lock
parks `amount` of a SPECIFIC asset (`EscrowRecord.asset`), and the COMBINED conserved quantity must
be PER-ASSET: a lock DROPS that asset's `bal`-ledger supply by `amount` AND RAISES the per-asset
holding-store by `amount` (combined fixed AT that asset), with EVERY OTHER asset literally untouched.
Folding all assets into one combined scalar would let an escrow swap asset A for asset B while the
aggregate stays put — the cross-asset-laundering hole at the holding-store boundary.

We re-found the escrow lifecycle onto the per-asset `bal` ledger via the single-cell `recBalCreditCell`
(the per-asset analog of `recCredit`/`recDebit` — a single-cell, single-asset move), define the
per-asset held sum + combined measure, and re-prove the four conserves-combined facts PER-ASSET as
DROP-IN swaps of the scalar decomposition (the find?/markResolved list lockstep is ASSET-AGNOSTIC; we
narrow the matched-record drop by `r.asset = b`). The scalar escrow stays as the legacy `cell`-view;
these are NEW per-asset SIBLINGS, never a re-proof of the same statement. -/

/-- **`recBalCreditCell` — single-cell, single-asset credit on the per-asset `bal` ledger.** Add `amt`
to cell `c`'s asset `a` column, leaving every other (cell, asset) pair literally untouched. The
per-asset analog of `recCredit` (which moved the scalar `balance` FIELD); `recBalCreditCell c a (-amt)`
is the per-asset DEBIT. This is the per-asset escrow's single-cell move (dregg1's `set_balance`, but
at a NAMED asset column rather than the scalar field). Lives HERE in `RecordKernel` (upstream of both
`TurnExecutorFull` and `EffectsPaired`) so both the executed dispatch and the chained escrow can use
it; it is definitionally the same shape as `TurnExecutorFull.recBalCredit`. -/
def recBalCreditCell (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun x b => if x = c ∧ b = a then bal x b + amt else bal x b

/-- **The per-asset single-cell credit delta — PROVED.** A `recBalCreditCell c a amt` raises asset
`a`'s supply by `amt` (when `c` is live) and leaves EVERY OTHER asset literally untouched. The
per-asset analog of `recCredit_recTotal`, reusing `sum_indicator`. -/
theorem recBalCreditCell_recTotalAsset (acc : Finset CellId) (bal : CellId → AssetId → ℤ)
    (c : CellId) (a : AssetId) (amt : ℤ) (hc : c ∈ acc) (b : AssetId) :
    (∑ x ∈ acc, recBalCreditCell bal c a amt x b)
      = (∑ x ∈ acc, bal x b) + (if b = a then amt else 0) := by
  by_cases hb : b = a
  · rw [if_pos hb]
    have key : (∑ x ∈ acc, recBalCreditCell bal c a amt x b) - (∑ x ∈ acc, bal x b) = amt := by
      rw [← Finset.sum_sub_distrib]
      have hg : ∀ x ∈ acc, recBalCreditCell bal c a amt x b - bal x b = (if x = c then amt else 0) := by
        intro x _
        unfold recBalCreditCell
        by_cases hx : x = c
        · rw [if_pos ⟨hx, hb⟩, if_pos hx]; ring
        · rw [if_neg (by rintro ⟨h, _⟩; exact hx h), if_neg hx]; ring
      rw [Finset.sum_congr rfl hg, sum_indicator acc c amt hc]
    omega
  · rw [if_neg hb, add_zero]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold recBalCreditCell; rw [if_neg (by rintro ⟨_, h⟩; exact hb h)]

/-- The per-asset UNRESOLVED-record predicate: unresolved AND of asset `b` (a `Bool`, so it drives
`List.filter` directly). The asset-filtered refinement of `fun r => !r.resolved`. -/
def heldAssetPred (b : AssetId) (r : EscrowRecord) : Bool := !r.resolved && decide (r.asset = b)

/-- **`escrowHeldAsset k b`** — the per-asset holding-store value: the sum of `amount` over the
UNRESOLVED escrow records WHOSE `asset = b`. The per-asset analog of `escrowHeld`, indexed by
`AssetId` (NEVER one combined scalar) — value parked off the `bal` ledger AT asset `b`. -/
def escrowHeldAsset (k : RecordKernelState) (b : AssetId) : ℤ :=
  (k.escrows.filter (heldAssetPred b)).foldr (fun r acc => r.amount + acc) 0

/-- **`recTotalAssetWithEscrow k b`** — THE COMBINED PER-ASSET conserved quantity: asset `b`'s
`bal`-ledger supply PLUS the value held off-ledger by unresolved escrows AT asset `b`. This — the
per-asset refinement of `recTotalWithEscrow` — is what the per-asset create+settle pair conserves AT
EACH ASSET independently. -/
def recTotalAssetWithEscrow (k : RecordKernelState) (b : AssetId) : ℤ :=
  recTotalAsset k b + escrowHeldAsset k b

/-- The raw per-asset escrow-list filtered-sum (the unfolded `escrowHeldAsset`). -/
def heldSumAsset (es : List EscrowRecord) (b : AssetId) : ℤ :=
  (es.filter (heldAssetPred b)).foldr (fun r acc => r.amount + acc) 0

theorem escrowHeldAsset_eq_heldSumAsset (k : RecordKernelState) (b : AssetId) :
    escrowHeldAsset k b = heldSumAsset k.escrows b := rfl

/-- **`escrowHeldAsset_cons_unresolved` — PROVED (the per-asset prepend delta).** Prepending an
UNRESOLVED record raises `escrowHeldAsset b` by `r.amount` IFF `r.asset = b`, and by `0` otherwise.
NON-VACUOUS: the `if r.asset = b` discriminant has teeth — prepending an asset-A record raises
`escrowHeldAsset A` but leaves `escrowHeldAsset B` (B≠A) literally FIXED. The scalar `escrowHeld_cons`
cannot state the b-indexed version (it has no asset to filter on). -/
theorem escrowHeldAsset_cons_unresolved (k : RecordKernelState) (r : EscrowRecord) (b : AssetId)
    (hr : r.resolved = false) :
    escrowHeldAsset { k with escrows := r :: k.escrows } b
      = escrowHeldAsset k b + (if r.asset = b then r.amount else 0) := by
  unfold escrowHeldAsset
  simp only [List.filter_cons]
  by_cases hab : r.asset = b
  · rw [show heldAssetPred b r = true from by simp [heldAssetPred, hr, hab]]
    simp only [if_true, List.foldr_cons, if_pos hab]
    omega
  · rw [show heldAssetPred b r = false from by simp [heldAssetPred, hab]]
    simp only [Bool.false_eq_true, if_false, if_neg hab, add_zero]

/-- **`heldSumAsset_markResolved_found` — THE PER-ASSET PAIR-CONSERVATION CORE (PROVED by list
induction).** Marking the FIRST unresolved record whose id matches `id` as resolved drops the per-asset
held sum AT asset `b` by `r.amount` IFF the found record's `asset = b`, and by `0` otherwise. The
find?/markResolved lockstep is ASSET-AGNOSTIC (it walks the same `id ∧ unresolved` predicate); the
matched-record drop is narrowed by `r.asset = b`. NON-VACUOUS: settling an asset-A record drops
`escrowHeldAsset A` by its amount and leaves every OTHER asset's held sum literally FIXED. Mirrors
`heldSum_markResolved_found` with `heldSum` → `heldSumAsset · b` and the drop guarded by `r.asset = b`. -/
theorem heldSumAsset_markResolved_found (id : Nat) (r : EscrowRecord) (b : AssetId) :
    ∀ (es : List EscrowRecord),
      es.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      heldSumAsset (markResolved es id) b = heldSumAsset es b - (if r.asset = b then r.amount else 0) := by
  intro es
  induction es with
  | nil => intro hfind; simp [List.find?] at hfind
  | cons hd tl ih =>
      intro hfind
      simp only [List.find?_cons] at hfind
      by_cases hmatch : (hd.id = id ∧ hd.resolved = false)
      · -- head matches: it IS the found, unresolved record.
        obtain ⟨hid, hres⟩ := hmatch
        rw [show (decide (hd.id = id ∧ hd.resolved = false)) = true from by simp [hid, hres]] at hfind
        simp only [Option.some.injEq] at hfind
        subst hfind
        unfold heldSumAsset markResolved
        rw [if_pos ⟨hid, hres⟩]
        simp only [List.filter_cons,
                   show heldAssetPred b ({hd with resolved := true} : EscrowRecord) = false from by
                     simp [heldAssetPred]]
        by_cases hab : hd.asset = b
        · -- found record is OF asset b: LHS drops it (now resolved ⇒ filtered OUT), RHS subtracts amount.
          rw [show heldAssetPred b hd = true from by simp [heldAssetPred, hres, hab]]
          simp only [Bool.false_eq_true, if_false, if_true, List.foldr_cons, if_pos hab]
          omega
        · -- found record is of ANOTHER asset: it was never IN `heldSumAsset b`, so no change.
          rw [show heldAssetPred b hd = false from by simp [heldAssetPred, hab]]
          simp only [Bool.false_eq_true, if_false, if_neg hab, sub_zero]
      · -- head does NOT match: carried unchanged; recurse on the tail.
        rw [show (decide (hd.id = id ∧ hd.resolved = false)) = false from by
              simp [hmatch]] at hfind
        have ihr := ih hfind
        have hmr : markResolved (hd :: tl) id = hd :: markResolved tl id := by
          conv_lhs => rw [markResolved]; rw [if_neg hmatch]
        rw [hmr]
        unfold heldSumAsset
        simp only [List.filter_cons]
        by_cases hhd : heldAssetPred b hd = true
        · rw [hhd]
          simp only [if_true, List.foldr_cons]
          have ihr' : (List.filter (heldAssetPred b) (markResolved tl id)).foldr
              (fun r acc => r.amount + acc) 0
              = (List.filter (heldAssetPred b) tl).foldr (fun r acc => r.amount + acc) 0
                - (if r.asset = b then r.amount else 0) := ihr
          rw [ihr']; ring
        · rw [show heldAssetPred b hd = false from by simpa using hhd]
          simp only [Bool.false_eq_true, if_false]
          have ihr' : (List.filter (heldAssetPred b) (markResolved tl id)).foldr
              (fun r acc => r.amount + acc) 0
              = (List.filter (heldAssetPred b) tl).foldr (fun r acc => r.amount + acc) 0
                - (if r.asset = b then r.amount else 0) := ihr
          rw [ihr']

/-! ### The faithful PER-ASSET escrow lifecycle (over the `bal` ledger). -/

/-- **`createEscrowRawAsset`** — the per-asset create: a SINGLE-cell, single-asset DEBIT of `amount`
from `creator`'s asset `asset` column PLUS an insert of an unresolved `EscrowRecord` (carrying `asset`)
into the off-ledger holding-store. The `bal`-ledger supply of `asset` DROPS by `amount`; the per-asset
holding-store at `asset` RISES by `amount`; the COMBINED per-asset total at `asset` is preserved, every
other asset untouched. The per-asset analog of `createEscrowRaw` (which moved the scalar `cell` field). -/
def createEscrowRawAsset (k : RecordKernelState) (id creator recipient : CellId) (asset : AssetId)
    (amount : ℤ) : RecordKernelState :=
  { k with bal := recBalCreditCell k.bal creator asset (-amount)
           escrows := { id := id, creator := creator, recipient := recipient,
                        amount := amount, resolved := false, asset := asset } :: k.escrows }

/-- **`settleEscrowRawAsset`** — the per-asset settle (release/refund body): a SINGLE-cell,
single-asset CREDIT of `amount` to the settlement target at asset `asset` PLUS marking the record
resolved. The `bal`-ledger supply of `asset` RISES by `amount`; the per-asset holding-store at `asset`
DROPS by `amount`; the COMBINED per-asset total at `asset` is preserved. -/
def settleEscrowRawAsset (k : RecordKernelState) (id target : CellId) (asset : AssetId) (amount : ℤ) :
    RecordKernelState :=
  { k with bal := recBalCreditCell k.bal target asset amount
           escrows := markResolved k.escrows id }

/-- **`createEscrowKAsset` (executable, fail-closed).** Commits only when the actor is authorized over
the `creator` cell (same `authorizedB` gate as `transfer`), the amount is non-negative and available
*in asset `asset`* (`amount ≤ k.bal creator asset`), the creator is a live account, and the `id` is
NOT already in use. On commit: single-cell, single-asset debit + park the asset-typed record. -/
def createEscrowKAsset (k : RecordKernelState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) : Option RecordKernelState :=
  if authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id) then
    some (createEscrowRawAsset k id creator recipient asset amount)
  else none

/-- **`releaseEscrowKAsset` (executable, fail-closed).** Looks up the unresolved record by `id`; on
success single-cell credits the `recipient` AT the record's asset and marks resolved. **SETTLE-LIVENESS
GATE** (`META-FILL C`, decision (7) hardened to a fail-closed gate rather than a carried hypothesis):
the settlement target MUST be a LIVE account (`r.recipient ∈ k.accounts`) — crediting a non-account
would silently DESTROY value (it vanishes from `recTotalAsset`, breaking combined conservation). This
is dregg1-faithful (you cannot credit a non-existent cell) and makes the per-asset combined-conservation
hold UNCONDITIONALLY (the keystone needs no carried `htgt`). -/
def releaseEscrowKAsset (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => if r.recipient ∈ k.accounts then some (settleEscrowRawAsset k id r.recipient r.asset r.amount)
              else none
  | none   => none

/-- **`refundEscrowKAsset` (executable, fail-closed).** Looks up the unresolved record by `id`; on
success single-cell credits the `creator` (refund target) AT the record's asset and marks resolved.
**SETTLE-LIVENESS GATE** (the creator/refund target MUST be a LIVE account) — same rationale as
`releaseEscrowKAsset`: unconditional combined-conservation, dregg1-faithful. -/
def refundEscrowKAsset (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => if r.creator ∈ k.accounts then some (settleEscrowRawAsset k id r.creator r.asset r.amount)
              else none
  | none   => none

/-! ### The REAL per-asset combined-conservation invariants. -/

/-- **`escrow_create_conserves_combined_per_asset` — THE HEADLINE (PROVED).** A committed per-asset
`createEscrowKAsset` PRESERVES the COMBINED per-asset total `recTotalAssetWithEscrow b` for EVERY asset
`b`: at the locked asset, the `bal`-ledger DROPS by `amount` (a real per-asset debit) while the
holding-store RISES by `amount` (combined fixed); at every OTHER asset BOTH terms are literally
unchanged. NON-VACUOUS: lock asset A and `recTotalAsset A` is genuinely lower while
`recTotalAssetWithEscrow A` is unchanged; `recTotalAssetWithEscrow B` (B≠A) unchanged with A's held
value non-zero — the no-cross-asset-laundering content at the escrow boundary. The per-asset drop-in of
`escrow_create_conserves_combined`: `recDebit_recTotal` → `recBalCreditCell_recTotalAsset`;
`escrowHeld_cons_unresolved` → `escrowHeldAsset_cons_unresolved`. -/
theorem escrow_create_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold createEscrowKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    set newRec : EscrowRecord := { id := id, creator := creator, recipient := recipient,
                                   amount := amount, resolved := false, asset := asset } with hnewRec
    show recTotalAssetWithEscrow (createEscrowRawAsset k id creator recipient asset amount) b
       = recTotalAssetWithEscrow k b
    unfold recTotalAssetWithEscrow createEscrowRawAsset
    have hbal : recTotalAsset { k with bal := recBalCreditCell k.bal creator asset (-amount),
                                       escrows := newRec :: k.escrows } b
        = recTotalAsset k b + (if b = asset then (-amount) else 0) := by
      show (∑ x ∈ k.accounts, recBalCreditCell k.bal creator asset (-amount) x b) = _
      exact recBalCreditCell_recTotalAsset k.accounts k.bal creator asset (-amount) hlive b
    have hheld : escrowHeldAsset { k with bal := recBalCreditCell k.bal creator asset (-amount),
                                          escrows := newRec :: k.escrows } b
        = escrowHeldAsset k b + (if asset = b then amount else 0) := by
      have hc := escrowHeldAsset_cons_unresolved
        { k with bal := recBalCreditCell k.bal creator asset (-amount) } newRec b rfl
      simpa [hnewRec] using hc
    rw [hbal, hheld]
    by_cases hba : b = asset
    · subst hba; simp only [if_true, if_pos rfl]; ring
    · rw [if_neg hba, if_neg (fun h => hba h.symm)]; ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`escrow_settle_conserves_combined_per_asset` — PROVED (the settle half, completing the pair).** A
release/refund that settles the found record to `target` PRESERVES the COMBINED per-asset total
`recTotalAssetWithEscrow b` for EVERY asset `b`: at the record's asset the `+amount` single-cell credit
is offset by the holding-store DROP; every other asset is literally unchanged. NON-VACUOUS: the
`target ∈ accounts` hypothesis has TEETH — a credit to a non-account vanishes from `recTotalAsset`,
breaking conservation. The per-asset drop-in of `escrow_settle_conserves_combined`: `recCredit_recTotal`
→ `recBalCreditCell_recTotalAsset`; `heldSum_markResolved_found` → `heldSumAsset_markResolved_found`. -/
theorem escrow_settle_conserves_combined_per_asset (k : RecordKernelState) (id target : CellId)
    (r : EscrowRecord) (b : AssetId) (htgt : target ∈ k.accounts)
    (hfind : k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r) :
    recTotalAssetWithEscrow (settleEscrowRawAsset k id target r.asset r.amount) b
      = recTotalAssetWithEscrow k b := by
  unfold recTotalAssetWithEscrow settleEscrowRawAsset
  have hbal : recTotalAsset { k with bal := recBalCreditCell k.bal target r.asset r.amount,
                                     escrows := markResolved k.escrows id } b
      = recTotalAsset k b + (if b = r.asset then r.amount else 0) := by
    show (∑ x ∈ k.accounts, recBalCreditCell k.bal target r.asset r.amount x b) = _
    exact recBalCreditCell_recTotalAsset k.accounts k.bal target r.asset r.amount htgt b
  have hheld : escrowHeldAsset { k with bal := recBalCreditCell k.bal target r.asset r.amount,
                                        escrows := markResolved k.escrows id } b
      = escrowHeldAsset k b - (if r.asset = b then r.amount else 0) := by
    show heldSumAsset (markResolved k.escrows id) b = heldSumAsset k.escrows b - _
    exact heldSumAsset_markResolved_found id r b k.escrows hfind
  rw [hbal, hheld]
  by_cases hba : b = r.asset
  · subst hba; simp only [if_true, if_pos rfl]; ring
  · rw [if_neg hba, if_neg (fun h => hba h.symm)]; ring

/-- **`releaseEscrowKAsset` PRESERVES the COMBINED per-asset total — PROVED (UNCONDITIONAL).** The
settle-liveness obligation is DISCHARGED by the fail-closed gate (`r.recipient ∈ k.accounts` is checked
in the executor), so no carried `htgt` is needed — a committed release conserves the COMBINED per-asset
total at EVERY asset. Reads off `escrow_settle_conserves_combined_per_asset` with the gate supplying the
liveness premise. -/
theorem releaseEscrowKAsset_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    (b : AssetId) (h : releaseEscrowKAsset k id = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold releaseEscrowKAsset at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hlive : r.recipient ∈ k.accounts
      · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h; subst h
        exact escrow_settle_conserves_combined_per_asset k id r.recipient r b hlive hfind
      · rw [if_neg hlive] at h; exact absurd h (by simp)

/-- **`refundEscrowKAsset` PRESERVES the COMBINED per-asset total — PROVED (UNCONDITIONAL).** The refund
half: value returns to the (LIVE, gate-checked) creator, the COMBINED per-asset total fixed at EVERY
asset; no carried `htgt`. -/
theorem refundEscrowKAsset_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    (b : AssetId) (h : refundEscrowKAsset k id = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold refundEscrowKAsset at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hlive : r.creator ∈ k.accounts
      · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h; subst h
        exact escrow_settle_conserves_combined_per_asset k id r.creator r b hlive hfind
      · rw [if_neg hlive] at h; exact absurd h (by simp)

/-- **`escrow_create_debits_per_asset` — PROVED.** A committed per-asset create DROPS asset `asset`'s
`bal`-ledger supply by `amount` (a real per-asset debit) and grows the holding-store by the asset-typed
record. The per-asset contrast with the combined-conservation: the BARE per-asset ledger genuinely
moves; only the COMBINED measure is fixed. -/
theorem escrow_create_debits_per_asset {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k') :
    recTotalAsset k' asset = recTotalAsset k asset - amount ∧
      k'.escrows = { id := id, creator := creator, recipient := recipient,
                     amount := amount, resolved := false, asset := asset } :: k.escrows := by
  unfold createEscrowKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    refine ⟨?_, rfl⟩
    show (∑ x ∈ k.accounts, recBalCreditCell k.bal creator asset (-amount) x asset) = _
    have := recBalCreditCell_recTotalAsset k.accounts k.bal creator asset (-amount) hlive asset
    simpa [recTotalAsset] using this
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`createEscrowKAsset_authorized` — PROVED.** A committed per-asset create required the actor to be
authorized over the `creator` cell. -/
theorem createEscrowKAsset_authorized {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k') :
    authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true := by
  unfold createEscrowKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §BRIDGE — the cross-chain bridge lock/finalize/cancel on the SHARED escrow holding-store (Wave-5).

dregg1's two-phase bridge (`turn/src/action.rs` `BridgeLock`/`BridgeFinalize`/`BridgeCancel`,
`turn/src/executor/apply.rs:1258`/`:1290`/`:1317`, lowered to `cell/src/note_bridge.rs`
`initiate_bridge`/`finalize_bridge`/`cancel_bridge`) is the bridge-shaped TWIN of escrow:

  * **bridgeLock** (Phase 1, `initiate_bridge`): DEBIT the originator + PARK the value in a `Locked`
    `PendingBridge` record — value inaccessible, AWAITING the other-chain confirmation. The off-ledger
    record is the SAME holding-store as escrow (`PendingBridgeSet` ≈ `escrows`), so we reuse the escrow
    store with a `bridge := true` tag. Double-lock REJECTED (`AlreadyLocked` — dregg1's `is_locked`).
    Combined per-asset CONSERVED (the debit is offset by the held rise) — IDENTICAL to `createEscrow`.
  * **bridgeFinalize** (Phase 3, `finalize_bridge`): the §8 confirmation receipt arrived and verified
    (the destination-federation signature over the nullifier — `verify_bridge_receipt`, the §8 portal);
    the lock resolves and the value LEAVES for the other chain. dregg1 marks the record `Finalized` AND
    makes the nullifier permanent (a real BURN on this side). On the COMBINED measure this is a
    no-credit resolve: the bare `bal` is untouched (the value already left the ledger at lock) but the
    held value DROPS — so `recTotalAssetWithEscrow` DROPS by the bridged amount, a DISCLOSED OUTFLOW
    (like burn). This is the ONE place the holding-store pair does NOT conserve — and honestly so.
  * **bridgeCancel** (Phase 4, `cancel_bridge`): the timeout was reached without a receipt; the note is
    UNLOCKED and the value REFUNDED to the originator. dregg1 marks the record `Cancelled`; the value
    returns to the locker. On the COMBINED measure this is a SETTLE back to the creator (credit + resolve)
    — combined per-asset CONSERVED, IDENTICAL to `refundEscrow`.

We reuse `createEscrowRawAsset` (tagged `bridge := true`), `settleEscrowRawAsset` (for cancel/refund),
`markResolved` (for finalize), and the per-asset held-sum lemmas verbatim — the bridge tag is INERT to
the find?/markResolved lockstep (it filters on `id ∧ unresolved`, not on `bridge`), so all the proof
spine carries. The §8 receipt is carried as a `Prop`-carrier hypothesis exactly as `bridgeMint`'s
foreign finality. -/

/-- **`createBridgeRawAsset`** — the per-asset bridge LOCK: a SINGLE-cell, single-asset DEBIT of `amount`
from the originator's asset `asset` column PLUS an insert of an UNRESOLVED, `bridge := true`-tagged
`EscrowRecord` into the SHARED off-ledger holding-store. The `bal`-ledger supply of `asset` DROPS by
`amount`; the per-asset holding-store at `asset` RISES by `amount`; the COMBINED per-asset total at
`asset` is preserved — IDENTICAL shape to `createEscrowRawAsset`, only the `bridge` tag differs. -/
def createBridgeRawAsset (k : RecordKernelState) (id originator destination : CellId) (asset : AssetId)
    (amount : ℤ) : RecordKernelState :=
  { k with bal := recBalCreditCell k.bal originator asset (-amount)
           escrows := { id := id, creator := originator, recipient := destination,
                        amount := amount, resolved := false, asset := asset, bridge := true } :: k.escrows }

/-- **`bridgeFinalizeRawAsset`** — the bridge FINALIZE body: mark the found record resolved WITHOUT a
credit. The `bal`-ledger is LEFT UNTOUCHED (the value already left the ledger at lock and now leaves for
the other chain — a BURN), but the per-asset holding-store DROPS by `amount` as the record leaves the
unresolved set. So the COMBINED per-asset total DROPS by `amount` — a disclosed OUTFLOW (NOT a settle
back onto the ledger). The honest contrast with `settleEscrowRawAsset` (which credits, conserving). -/
def bridgeFinalizeRawAsset (k : RecordKernelState) (id : Nat) : RecordKernelState :=
  { k with escrows := markResolved k.escrows id }

/-- **`bridgeLockKAsset` (executable, fail-closed).** Commits only when the actor is authorized over the
originator cell (same `authorizedB` gate as `transfer`/escrow-create), the amount is non-negative and
available *in asset `asset`*, the originator is a live account, and the `id` is NOT already in use
(dregg1's `AlreadyLocked` double-lock rejection — `is_locked`). On commit: single-cell debit + park the
bridge-tagged record. The §8 spending proof is carried at the theorem layer. -/
def bridgeLockKAsset (k : RecordKernelState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) : Option RecordKernelState :=
  if authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id) then
    some (createBridgeRawAsset k id originator destination asset amount)
  else none

/-- **`bridgeFinalizeKAsset` (executable, fail-closed).** Looks up the unresolved record by `id` AND
checks the parked record's `(asset, amount)` MATCH the receipt-DISCLOSED `(asset, amount)` (dregg1's
finalize verifies the receipt against the pending bridge — `finalize_bridge` checks nullifier/destination
consistency); on a match, marks it resolved WITHOUT a credit — the value LEFT for the other chain (the
burn). The §8 confirmation receipt (the destination-federation signature, `verify_bridge_receipt`) is the
THEOREM-level portal — here we model the LEDGER move gated on the record being present-and-unresolved (the
`Locked`-state gate) AND matching the disclosed outflow. Rejects a missing/already-resolved/mismatched
record. -/
def bridgeFinalizeKAsset (k : RecordKernelState) (id : Nat) (asset : AssetId) (amount : ℤ) :
    Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => if r.asset = asset ∧ r.amount = amount then some (bridgeFinalizeRawAsset k id) else none
  | none   => none

/-- **`bridgeCancelKAsset` (executable, fail-closed).** Looks up the unresolved record by `id`; on
success single-cell credits the `creator` (the ORIGINATOR — the refund target) AT the record's asset and
marks resolved (dregg1's `cancel_bridge` — note unlocked, value returned to the owner). **SETTLE-LIVENESS
GATE** (the originator MUST be a LIVE account) — same rationale as `refundEscrowKAsset`: crediting a
non-account would silently DESTROY value, breaking combined conservation; this makes the per-asset
combined-conservation hold UNCONDITIONALLY. The timeout gate is carried at the effect/theorem layer. -/
def bridgeCancelKAsset (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => if r.creator ∈ k.accounts then some (settleEscrowRawAsset k id r.creator r.asset r.amount)
              else none
  | none   => none

/-! ### The REAL bridge combined-measure invariants. -/

/-- **`bridge_lock_conserves_combined_per_asset` — PROVED (the LOCK half).** A committed bridge LOCK
PRESERVES the COMBINED per-asset total `recTotalAssetWithEscrow b` for EVERY asset `b`: at the locked
asset the `bal`-ledger DROPS by `amount` while the holding-store RISES by `amount` (combined fixed); at
every OTHER asset BOTH terms are unchanged. The bridge tag is INERT to the measure (`recTotalAssetWithEscrow`
sums on `resolved`/`asset`, not `bridge`), so this is the per-asset escrow-create proof verbatim with
`bridge := true` carried through. NON-VACUOUS: lock asset A and `recTotalAsset A` is genuinely lower while
`recTotalAssetWithEscrow A` is unchanged — the value moved into the holding-store, not destroyed. -/
theorem bridge_lock_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold bridgeLockKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    set newRec : EscrowRecord := { id := id, creator := originator, recipient := destination,
                                   amount := amount, resolved := false, asset := asset, bridge := true } with hnewRec
    show recTotalAssetWithEscrow (createBridgeRawAsset k id originator destination asset amount) b
       = recTotalAssetWithEscrow k b
    unfold recTotalAssetWithEscrow createBridgeRawAsset
    have hbal : recTotalAsset { k with bal := recBalCreditCell k.bal originator asset (-amount),
                                       escrows := newRec :: k.escrows } b
        = recTotalAsset k b + (if b = asset then (-amount) else 0) := by
      show (∑ x ∈ k.accounts, recBalCreditCell k.bal originator asset (-amount) x b) = _
      exact recBalCreditCell_recTotalAsset k.accounts k.bal originator asset (-amount) hlive b
    have hheld : escrowHeldAsset { k with bal := recBalCreditCell k.bal originator asset (-amount),
                                          escrows := newRec :: k.escrows } b
        = escrowHeldAsset k b + (if asset = b then amount else 0) := by
      have hc := escrowHeldAsset_cons_unresolved
        { k with bal := recBalCreditCell k.bal originator asset (-amount) } newRec b rfl
      simpa [hnewRec] using hc
    rw [hbal, hheld]
    by_cases hba : b = asset
    · subst hba; simp only [if_true, if_pos rfl]; ring
    · rw [if_neg hba, if_neg (fun h => hba h.symm)]; ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`bridge_lock_debits_per_asset` — PROVED.** A committed bridge LOCK DROPS the locked asset's
`bal`-ledger supply by `amount` (a real per-asset debit) and grows the holding-store by the bridge-tagged
record — the bare per-asset ledger genuinely MOVES (the contrast with the combined-conservation; the
value is now INACCESSIBLE in the lock, AWAITING the other chain). -/
theorem bridge_lock_debits_per_asset {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    recTotalAsset k' asset = recTotalAsset k asset - amount ∧
      k'.escrows = { id := id, creator := originator, recipient := destination,
                     amount := amount, resolved := false, asset := asset, bridge := true } :: k.escrows := by
  unfold bridgeLockKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    refine ⟨?_, rfl⟩
    show (∑ x ∈ k.accounts, recBalCreditCell k.bal originator asset (-amount) x asset) = _
    have := recBalCreditCell_recTotalAsset k.accounts k.bal originator asset (-amount) hlive asset
    simpa [recTotalAsset] using this
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`bridgeLockKAsset_authorized` — PROVED.** A committed bridge LOCK required the actor to be
authorized over the debited originator cell (the SAME `authorizedB` gate as `transfer`). -/
theorem bridgeLockKAsset_authorized {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true := by
  unfold bridgeLockKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`bridge_finalize_moves_combined_per_asset` — THE BRIDGE HEADLINE (PROVED, the FINALIZE half).** A
committed bridge FINALIZE MOVES the COMBINED per-asset total `recTotalAssetWithEscrow b` by EXACTLY the
disclosed `-amount` at the bridged asset (`-r.amount` when `r.asset = b`), and leaves EVERY OTHER asset
LITERALLY FIXED. The bare `bal` is untouched (no credit), and the held value DROPS as the record leaves
the unresolved set (`heldSumAsset_markResolved_found`) — so the COMBINED measure drops by the bridged
amount. This is the value genuinely LEAVING for the other chain — a disclosed OUTFLOW (like burn), NOT a
conservation claim. The ONE holding-store resolution that does NOT conserve, and honestly so. NON-VACUOUS:
the drop is GUARDED by `r.asset = b`, so the bridged asset falls by exactly `r.amount` while the OTHER
asset is fixed — no cross-asset laundering at the bridge boundary. -/
theorem bridge_finalize_moves_combined_per_asset (k : RecordKernelState) (id : Nat) (r : EscrowRecord)
    (b : AssetId)
    (hfind : k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r) :
    recTotalAssetWithEscrow (bridgeFinalizeRawAsset k id) b
      = recTotalAssetWithEscrow k b - (if r.asset = b then r.amount else 0) := by
  unfold recTotalAssetWithEscrow bridgeFinalizeRawAsset
  -- the `bal` ledger is untouched (no credit on finalize):
  have hbal : recTotalAsset { k with escrows := markResolved k.escrows id } b = recTotalAsset k b := rfl
  -- the held value drops by the found record's amount IFF its asset is `b`:
  have hheld : escrowHeldAsset { k with escrows := markResolved k.escrows id } b
      = escrowHeldAsset k b - (if r.asset = b then r.amount else 0) := by
    show heldSumAsset (markResolved k.escrows id) b = heldSumAsset k.escrows b - _
    exact heldSumAsset_markResolved_found id r b k.escrows hfind
  rw [hbal, hheld]; ring

/-- **`bridgeFinalizeKAsset_moves_combined_per_asset` — THE BRIDGE HEADLINE (PROVED).** A committed bridge
finalize MOVES the COMBINED per-asset measure by EXACTLY the DISCLOSED `-amount` at the disclosed `asset`
(`-amount` when `b = asset`, `0` elsewhere) — a function of the ACTION's disclosed `(asset, amount)`, NOT
of the hidden record (the executor's match-gate ties them). The bridged value LEFT for the other chain: a
disclosed OUTFLOW, no cross-asset laundering (the OTHER asset is literally fixed). The match-gate
(`r.asset = asset ∧ r.amount = amount`) rewrites the record-amount drop of
`bridge_finalize_moves_combined_per_asset` into the disclosed-amount drop. -/
theorem bridgeFinalizeKAsset_moves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    {asset : AssetId} {amount : ℤ} (b : AssetId) (h : bridgeFinalizeKAsset k id asset amount = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b - (if b = asset then amount else 0) := by
  unfold bridgeFinalizeKAsset at h
  cases hfind : k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hm : r.asset = asset ∧ r.amount = amount
      · rw [if_pos hm] at h; simp only [Option.some.injEq] at h
        obtain ⟨hra, hrm⟩ := hm
        rw [← h, bridge_finalize_moves_combined_per_asset k id r b hfind]
        -- rewrite the record's (asset, amount) into the disclosed (asset, amount):
        rw [hra, hrm]
        -- the remaining `if asset = b` vs `if b = asset` differ only by symmetry of `=`:
        by_cases hba : b = asset
        · rw [if_pos hba, if_pos hba.symm]
        · rw [if_neg hba, if_neg (fun heq => hba heq.symm)]
      · rw [if_neg hm] at h; exact absurd h (by simp)

/-- **`bridge_cancel_conserves_combined_per_asset` — PROVED (the CANCEL half, the refund round-trip).** A
committed bridge CANCEL PRESERVES the COMBINED per-asset total at EVERY asset: the value returns to the
(LIVE, gate-checked) originator — the `+amount` credit is offset by the holding-store drop. The timeout
having been reached is the effect-layer gate; here the LEDGER move conserves. UNCONDITIONAL (the
settle-liveness obligation is discharged by the fail-closed `r.creator ∈ accounts` gate). Reads off
`escrow_settle_conserves_combined_per_asset` (the bridge tag is inert to the settle). -/
theorem bridge_cancel_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    (b : AssetId) (h : bridgeCancelKAsset k id = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold bridgeCancelKAsset at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hlive : r.creator ∈ k.accounts
      · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h; subst h
        exact escrow_settle_conserves_combined_per_asset k id r.creator r b hlive hfind
      · rw [if_neg hlive] at h; exact absurd h (by simp)

/-! ### §BRIDGE runs (`#eval`) — the lock/finalize/cancel triple has teeth on the combined measure. -/

/-- A 2-cell, 2-asset bridge fixture: cell 0 holds 100 of asset 1; cell 1 holds 0. Actor 0 owns cell 0
(`node 1` self-cap is not needed — ownership authorizes the lock over src 0). -/
def brg0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 1 then 100 else 0 }

/-- Lock 30 of asset 1 from originator 0 → destination 1, bridge id 9. -/
def brgLocked : Option RecordKernelState := bridgeLockKAsset brg0 9 0 0 1 1 30

-- LOCK: bare ledger DROPS at asset 1 (100→70), held RISES to 30, COMBINED CONSERVED at (100, 0).
#eval (recTotalAssetWithEscrow brg0 1, recTotalAssetWithEscrow brg0 0)                  -- (100, 0)
#eval brgLocked.map (fun k => (recTotalAsset k 1, escrowHeldAsset k 1))                 -- some (70, 30) — bare DOWN, held UP
#eval brgLocked.map (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0))  -- some (100, 0) — CONSERVED both
-- the parked record carries the bridge tag (it is in the SHARED escrow store, tagged):
#eval brgLocked.map (fun k => k.escrows.map (fun r => (r.id, r.amount, r.asset, r.bridge)))  -- some [(9, 30, 1, true)]
-- LOCK then CANCEL (refund to originator 0): COMBINED stays (100, 0), held returns to 0, bal back to 100.
#eval (brgLocked.bind (fun k => bridgeCancelKAsset k 9)).map
        (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0,
                   escrowHeldAsset k 1, recTotalAsset k 1))                             -- some (100, 0, 0, 100) — REFUND round-trip CONSERVED
-- LOCK then FINALIZE (value LEFT for the other chain): COMBINED DROPS by 30 at asset 1 (100→70),
--   asset 0 FIXED at 0; held drops to 0; the bare bal STAYS at 70 (the value already left, now burned).
--   The finalize DISCLOSES the bridged (asset 1, amount 30) — the executor gates on the record matching.
#eval (brgLocked.bind (fun k => bridgeFinalizeKAsset k 9 1 30)).map
        (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0,
                   escrowHeldAsset k 1, recTotalAsset k 1))                             -- some (70, 0, 0, 70) — COMBINED -30 at asset 1, asset 0 FIXED
-- double-finalize fail-closed (the record is already resolved):
#eval ((brgLocked.bind (fun k => bridgeFinalizeKAsset k 9 1 30)).bind
        (fun k => bridgeFinalizeKAsset k 9 1 30)).isSome                                -- false
-- MISMATCHED finalize fail-closed (disclosed amount 99 ≠ parked 30, the receipt-vs-pending check):
#eval (brgLocked.bind (fun k => bridgeFinalizeKAsset k 9 1 99)).isSome                  -- false
-- MISMATCHED-asset finalize fail-closed (disclosed asset 0 ≠ parked 1):
#eval (brgLocked.bind (fun k => bridgeFinalizeKAsset k 9 0 30)).isSome                  -- false
-- double-lock fail-closed (the id is already in use):
#eval (brgLocked.bind (fun k => bridgeLockKAsset k 9 0 0 1 1 10)).isSome                -- false
-- unauthorized lock fail-closed (actor 5 owns nothing):
#eval (bridgeLockKAsset brg0 9 5 0 1 1 30).isSome                                       -- false

#assert_axioms bridge_lock_conserves_combined_per_asset
#assert_axioms bridge_lock_debits_per_asset
#assert_axioms bridgeLockKAsset_authorized
#assert_axioms bridge_finalize_moves_combined_per_asset
#assert_axioms bridgeFinalizeKAsset_moves_combined_per_asset
#assert_axioms bridge_cancel_conserves_combined_per_asset

/-! ### §NOTE-CREATE — the grow-only COMMITMENT SET (faithful to dregg1's `apply_note_create`).

dregg1's `apply_note_create` inserts a fresh Pedersen commitment into the off-ledger commitment tree;
the §8 crypto (range proof on the hidden value) is a `CryptoPortal` carried at the effect layer. The
note's hidden value's ASSET is OUT OF SCOPE here (behind the CryptoPortal) — `noteCreate` is
bal-NEUTRAL: it grows the `commitments` SET only, NOT `bal`/`nullifiers`/`escrows`. (A fresh
commitment is always fresh, so — unlike `noteSpend`'s double-spend gate — there is no rejection; the
grow-only insert is the dual of the nullifier set.) -/

/-- **`noteCreateCommitment` (executable)** — insert a fresh note commitment `cm` into the off-ledger
commitment SET (the grow-only dual of `noteSpendNullifier`). bal-NEUTRAL: it touches NEITHER `bal` NOR
`nullifiers` NOR `escrows`. Always commits (a fresh commitment cannot conflict). -/
def noteCreateCommitment (k : RecordKernelState) (cm : Nat) : RecordKernelState :=
  { k with commitments := cm :: k.commitments }

/-- **`noteCreate_inserts` — PROVED.** A `noteCreateCommitment` actually inserts `cm` into the
commitment set. -/
theorem noteCreate_inserts (k : RecordKernelState) (cm : Nat) :
    cm ∈ (noteCreateCommitment k cm).commitments := by
  unfold noteCreateCommitment; simp

/-- **`noteCreate_recTotalAsset` — PROVED (bal-NEUTRALITY).** A `noteCreateCommitment` leaves
`recTotalAsset b` and `escrowHeldAsset b` (hence `recTotalAssetWithEscrow b`) UNCHANGED for EVERY asset
`b`: it grows only the commitment SET, never the `bal` ledger nor the `escrows` store. -/
theorem noteCreate_recTotalAsset (k : RecordKernelState) (cm : Nat) (b : AssetId) :
    recTotalAsset (noteCreateCommitment k cm) b = recTotalAsset k b
      ∧ escrowHeldAsset (noteCreateCommitment k cm) b = escrowHeldAsset k b := ⟨rfl, rfl⟩

/-! ## §ESCROW-PER-ASSET runs (`#eval`) — the combined measure has teeth + the asset-isolation guard. -/

/-- A 2-cell, 2-asset ledger for the per-asset escrow guard: cell 0 holds 100 of asset 1 (and 0 of
asset 0); cell 1 holds 0 of everything. Cell 0 will lock 30 of asset 1 into escrow id 9 → recipient 1. -/
def res0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 1 then 100 else 0 }

/-- Lock 30 of asset 1 from cell 0 to recipient 1, escrow id 9. -/
def resLocked : Option RecordKernelState := createEscrowKAsset res0 9 0 0 1 1 30

-- NON-VACUITY GUARD (locked at asset≠0): the held value MOVES at asset 1 ONLY.
#eval (escrowHeldAsset res0 1, escrowHeldAsset res0 0)                       -- (0, 0) before
#eval resLocked.map (fun k => (escrowHeldAsset k 1, escrowHeldAsset k 0))    -- some (30, 0) — held GENUINELY non-zero at asset 1, asset 0 UNTOUCHED
-- the BARE per-asset ledger DROPS at asset 1 (a real debit); asset 0 untouched:
#eval resLocked.map (fun k => (recTotalAsset k 1, recTotalAsset k 0))        -- some (70, 0)
-- the COMBINED per-asset measure is CONSERVED at asset 1 AND asset 0:
#eval (recTotalAssetWithEscrow res0 1, recTotalAssetWithEscrow res0 0)       -- (100, 0)
#eval resLocked.map (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0))
                                                                            -- some (100, 0) — CONSERVED both assets
-- SETTLE (release to recipient 1): mirror — combined stays (100,0), held returns to 0, bal back to 100 at asset 1.
#eval (resLocked.bind (fun k => releaseEscrowKAsset k 9)).map
        (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0,
                   escrowHeldAsset k 1, recTotalAsset k 1))                 -- some (100, 0, 0, 100)
-- noteCreate round-trip + noteSpend independence; double-spend fail-closed.
#eval (noteCreateCommitment res0 42).commitments                            -- [42]
#eval (noteSpendNullifier res0 7).map (fun k => k.nullifiers)               -- some [7]
#eval ((noteSpendNullifier res0 7).bind (fun k => noteSpendNullifier k 7)).isSome  -- false

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
-- The per-asset CONSERVATION_VECTOR keystones (FILL 1) over the REAL executable state + gate:
#assert_axioms recTransferBal_sum_conserve_moved
#assert_axioms recTransferBal_untouched
#assert_axioms recKExecAsset_conserves_per_asset
#assert_axioms recKExecAsset_authorized
#assert_axioms recKExecAsset_unauthorized_fails
#assert_axioms recKExecAsset_no_cross_asset_leak
-- The per-asset COMBINED escrow measure + note-commitment keystones (META-FILL C):
#assert_axioms recBalCreditCell_recTotalAsset
#assert_axioms escrowHeldAsset_cons_unresolved
#assert_axioms heldSumAsset_markResolved_found
#assert_axioms escrow_create_conserves_combined_per_asset
#assert_axioms escrow_settle_conserves_combined_per_asset
#assert_axioms releaseEscrowKAsset_conserves_combined_per_asset
#assert_axioms refundEscrowKAsset_conserves_combined_per_asset
#assert_axioms escrow_create_debits_per_asset
#assert_axioms createEscrowKAsset_authorized
#assert_axioms noteCreate_inserts
#assert_axioms noteCreate_recTotalAsset

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

/-! ### §MULTI-ASSET runs (`#eval`) — the per-asset ledger conserves each asset class. -/

/-- A 2-cell, 2-asset ledger: cell 0 holds 100 of asset 0 and 7 of asset 1; cell 1 holds 5 of
asset 0. (The `cell`/`caps` carry trivially; `bal` is the genuine per-asset ledger.) -/
def rms0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                      else if c = 1 then (if a = 0 then 5 else 0) else 0 }

#eval recTotalAsset rms0 0                                            -- 105 (asset 0 supply)
#eval recTotalAsset rms0 1                                            -- 7   (asset 1 supply)
#eval (recKExecAsset rms0 rt1 0).map (fun k => recTotalAsset k 0)     -- some 105 (asset 0 conserved)
#eval (recKExecAsset rms0 rt1 0).map (fun k => recTotalAsset k 1)     -- some 7   (asset 1 UNTOUCHED)
#eval (recKExecAsset rms0 rtBad 0).isSome                             -- false   (unauthorized)
-- moving asset 0 cannot inflate asset 1's supply — the scalar-laundering attack is unrepresentable:
#eval (recKExecAsset rms0 rt1 0).map (fun k => (k.bal 0 0, k.bal 0 1, k.bal 1 0, k.bal 1 1))
                                                                      -- some (70, 7, 35, 0)

end Dregg2.Exec
