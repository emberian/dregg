/-
# Dregg2.Exec.CellPrivacy — the VALUE-RIB: conservation over Pedersen COMMITMENTS.

`Exec/Kernel.lean` runs the conserving turn over a *cleartext* balance function
(`bal : CellId → ℤ`, conserved as `total = Σ bal`). This module lifts that same
conservation **into the hiding regime**: a cell's per-account state is no longer a cleartext
amount but a **commitment** `CryptoKernel.commit value blinding : Digest` to a HIDDEN
amount+blinding, and the conserved quantity is the **homomorphic sum** of those commitments.

The point (`dregg2 §6a/§6.1`, `gaps-1 (d)`, the value-privacy tier): the conservation badge
attests `Σ committed = const` **without revealing the amounts**. A committed transfer moves a
hidden `amt` from `src` to `dst` — `src`'s commitment goes down by `commit amt s`, `dst`'s up
by `commit amt s` — and the homomorphic sum is invariant. The keystone
`committed_transfer_conserves` proves exactly this, **via `commit_hom`** (the §8 RAIL: the
homomorphism is an assumed INTERFACE LAW we USE, never a crypto-soundness theorem we prove).
The *hiding* of the commitments stays a §8 circuit obligation — only the algebraic balance is
proved here.

Parametric over `[CryptoKernel Digest Proof]`; reuses `PrivacyKernel.commitHom`
(`(Int × Int) →+ Digest`, the homomorphism packaged from `commit_hom` + `commit_zero`) and
`PrivacyKernel.commit_sum_kernel` (the `Σ commit = commit (Σ·)` collapse). The cleartext
`Exec.Kernel` machinery (`KernelState`, `total`, `cellObs`, `transferBal`) is reused by
*import*, never redefined. `#eval` demos use the `Reference` kernel (`commit v r := v + r`).
-/
import Dregg2.PrivacyKernel
import Dregg2.Exec.Kernel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Dregg2.Exec.CellPrivacy

open Dregg2.Crypto Dregg2.PrivacyKernel Dregg2.Exec

variable {Digest Proof : Type} [AddCommGroup Digest]

/-! ## The committed cell — per-account state is a commitment to a hidden amount. -/

/-- **A committed cell.** Over a finite set of live `accounts`, each account `i` carries a
HIDDEN amount `amt i` and a blinding factor `blind i`; its *visible* state is the commitment
`CryptoKernel.commit (amt i) (blind i) : Digest`. A verifier sees only the commitments — never
`amt`/`blind`. (This is the value-tier analog of `Exec.KernelState.bal`, with each balance
replaced by a Pedersen commitment to it.) -/
structure CommittedCell (Digest Proof : Type) [AddCommGroup Digest] where
  /-- The finite set of live accounts whose committed value is conserved. -/
  accounts : Finset CellId
  /-- The HIDDEN per-account amount (never revealed; only its commitment is). -/
  amt   : CellId → Int
  /-- The per-account blinding factor (prover-chosen; what makes the commitment hide). -/
  blind : CellId → Int

/-- The **visible** per-account commitment: `commit (amt i) (blind i)`. This is the only
thing a verifier sees for account `i`. -/
def commitmentOf [CryptoKernel Digest Proof] (c : CommittedCell Digest Proof) (i : CellId) :
    Digest :=
  CryptoKernel.commit Proof (c.amt i) (c.blind i)

/-- **The committed total** = the HOMOMORPHIC SUM of the per-account commitments,
`Σ_{i∈accounts} commit (amt i) (blind i)`. This is the hidden-regime analog of `Exec.total`
(`Σ bal`): the conserved quantity, expressed entirely over commitments. By
`commit_sum_kernel` it equals `commit (Σ amt) (Σ blind)` — a single commitment to the
(hidden) grand total — but a verifier can check its *invariance* across a turn without ever
opening it. -/
def committedTotal [CryptoKernel Digest Proof] (c : CommittedCell Digest Proof) : Digest :=
  c.accounts.sum (fun i => commitmentOf (Proof := Proof) c i)

/-- `committedTotal` collapses to a single commitment of the summed amount under the summed
blinding (PROVED via `PrivacyKernel.commit_sum_kernel`, itself `map_sum` of `commitHom`). The
homomorphic sum of the visible commitments IS a commitment to the hidden grand total. -/
theorem committedTotal_eq_commit_sum [CryptoKernel Digest Proof]
    (c : CommittedCell Digest Proof) :
    committedTotal (Proof := Proof) c
      = CryptoKernel.commit Proof (c.accounts.sum c.amt) (c.accounts.sum c.blind) := by
  unfold committedTotal commitmentOf
  exact commit_sum_kernel (Proof := Proof) c.amt c.blind c.accounts

/-! ## The committed transfer — move a HIDDEN amount, hiding-preserving. -/

/-- **A committed transfer of a hidden amount `amt` (blinding `s`) from `src` to `dst`.**
`src`'s hidden amount drops by `amt` and its blinding by `s`; `dst`'s rise by `amt`/`s`. In
the *visible* (commitment) world this means `src`'s commitment is divided by `commit amt s`
and `dst`'s is multiplied by it (additively: `−commit amt s` / `+commit amt s`) — exactly the
homomorphic structure that keeps the sum invariant. The amount `amt` and the transfer blinding
`s` are never revealed; only the resulting commitments change. -/
def committedTransfer [CryptoKernel Digest Proof]
    (c : CommittedCell Digest Proof) (src dst : CellId) (amt s : Int) :
    CommittedCell Digest Proof :=
  { c with
    amt   := fun i => if i = src then c.amt i - amt else if i = dst then c.amt i + amt else c.amt i
    blind := fun i => if i = src then c.blind i - s else if i = dst then c.blind i + s else c.blind i }

/-- A committed transfer leaves the live `accounts` set unchanged. -/
@[simp] theorem committedTransfer_accounts [CryptoKernel Digest Proof]
    (c : CommittedCell Digest Proof) (src dst : CellId) (amt s : Int) :
    (committedTransfer (Proof := Proof) c src dst amt s).accounts = c.accounts := rfl

/-- The summed hidden AMOUNT is unchanged by a committed transfer between two distinct live
accounts (the `−amt`/`+amt` cancel) — the cleartext shadow, used to drive the committed
keystone. -/
theorem committedTransfer_sum_amt [CryptoKernel Digest Proof]
    (c : CommittedCell Digest Proof) {src dst : CellId} {amt s : Int}
    (hsrc : src ∈ c.accounts) (hdst : dst ∈ c.accounts) (hne : src ≠ dst) :
    (committedTransfer (Proof := Proof) c src dst amt s).accounts.sum
        (committedTransfer (Proof := Proof) c src dst amt s).amt
      = c.accounts.sum c.amt := by
  show c.accounts.sum (fun i => if i = src then c.amt i - amt
      else if i = dst then c.amt i + amt else c.amt i) = c.accounts.sum c.amt
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hg : ∀ i ∈ c.accounts,
      (if i = src then c.amt i - amt else if i = dst then c.amt i + amt else c.amt i) - c.amt i
        = (if i = src then (-amt) else 0) + (if i = dst then amt else 0) := by
    intro i _
    rcases eq_or_ne i src with h1 | h1
    · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hne]; ring
    · rcases eq_or_ne i dst with h2 | h2
      · subst h2; rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      sum_indicator c.accounts src (-amt) hsrc, sum_indicator c.accounts dst amt hdst]
  ring

/-- The summed BLINDING is unchanged by a committed transfer between two distinct live
accounts (the `−s`/`+s` cancel). -/
theorem committedTransfer_sum_blind [CryptoKernel Digest Proof]
    (c : CommittedCell Digest Proof) {src dst : CellId} {amt s : Int}
    (hsrc : src ∈ c.accounts) (hdst : dst ∈ c.accounts) (hne : src ≠ dst) :
    (committedTransfer (Proof := Proof) c src dst amt s).accounts.sum
        (committedTransfer (Proof := Proof) c src dst amt s).blind
      = c.accounts.sum c.blind := by
  show c.accounts.sum (fun i => if i = src then c.blind i - s
      else if i = dst then c.blind i + s else c.blind i) = c.accounts.sum c.blind
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hg : ∀ i ∈ c.accounts,
      (if i = src then c.blind i - s else if i = dst then c.blind i + s else c.blind i) - c.blind i
        = (if i = src then (-s) else 0) + (if i = dst then s else 0) := by
    intro i _
    rcases eq_or_ne i src with h1 | h1
    · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hne]; ring
    · rcases eq_or_ne i dst with h2 | h2
      · subst h2; rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      sum_indicator c.accounts src (-s) hsrc, sum_indicator c.accounts dst s hdst]
  ring

/-! ## THE KEYSTONE — committed conservation over HIDDEN amounts. -/

/-- **THE KEYSTONE: `committed_transfer_conserves`.** A committed transfer of a HIDDEN amount
`amt` (transfer blinding `s`) between two distinct live accounts preserves the
`committedTotal` — the homomorphic sum of the per-account commitments is INVARIANT. The
verifier confirms `Σ committed` is unchanged across the turn **without opening `amt` or any
account's value**: this is "the cross-cell balance hypothesis runs over commitments, never
cleartext."

Proved via `commit_hom` (the §8 INTERFACE LAW, USED not proved): collapse each side with
`committedTotal_eq_commit_sum` to `commit (Σ amt) (Σ blind)`, then the summed amount and
summed blinding are each invariant (`committedTransfer_sum_amt`/`_sum_blind`, the `±amt`/`±s`
cancellation), so the two single commitments coincide.

§8: that the commitments *hide* the amounts (leak nothing about `amt i`/`blind i`) is the
cryptographic obligation the Pedersen/Ristretto impl + range-proof circuit discharge — NOT
proved here; only the homomorphic balance is. -/
theorem committed_transfer_conserves [CryptoKernel Digest Proof]
    (c : CommittedCell Digest Proof) {src dst : CellId} {amt s : Int}
    (hsrc : src ∈ c.accounts) (hdst : dst ∈ c.accounts) (hne : src ≠ dst) :
    committedTotal (Proof := Proof) (committedTransfer (Proof := Proof) c src dst amt s)
      = committedTotal (Proof := Proof) c := by
  rw [committedTotal_eq_commit_sum (Proof := Proof),
      committedTotal_eq_commit_sum (Proof := Proof),
      committedTransfer_sum_amt (Proof := Proof) c hsrc hdst hne,
      committedTransfer_sum_blind (Proof := Proof) c hsrc hdst hne]

/-! ## Corollary — the commitment of a CLEARTEXT conserving transfer conserves.

This ties the committed keystone back to the cleartext `Exec.Kernel`: build a `CommittedCell`
whose hidden amounts ARE a `KernelState`'s cleartext balances, commit it, and a cleartext
conserving transfer (the `Exec.transferBal` move) maps to a `committedTransfer` whose
`committedTotal` is preserved — the hiding lift of `Exec.exec_conserves`. -/

/-- Lift a cleartext `KernelState`'s balances into a `CommittedCell` under a chosen blinding
function `bl` (the hidden amount of account `i` is its cleartext balance `k.bal i`). -/
def ofKernelState (Digest Proof : Type) [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (k : KernelState) (bl : CellId → Int) :
    CommittedCell Digest Proof :=
  { accounts := k.accounts, amt := fun i => k.bal i, blind := bl }

/-- **Corollary: the commitment of a cleartext conserving transfer conserves (PROVED).** Take
a `KernelState` `k`, commit its balances under blinding `bl`, and perform the SAME `src⇒dst`
move of cleartext `amt` (transfer blinding `s`) in the committed world: the `committedTotal`
is preserved. So whenever the cleartext kernel would conserve `total` (Law 1,
`Exec.exec_conserves`), its commitment conserves `committedTotal` over hidden amounts. This is
the cleartext→committed bridge: privacy is a *faithful lift* of the conservation law, not a
weakening of it. -/
theorem ofKernelState_transfer_conserves [CryptoKernel Digest Proof]
    (k : KernelState) (bl : CellId → Int) {src dst : CellId} {amt s : Int}
    (hsrc : src ∈ k.accounts) (hdst : dst ∈ k.accounts) (hne : src ≠ dst) :
    committedTotal (Proof := Proof)
        (committedTransfer (Proof := Proof) (ofKernelState Digest Proof k bl) src dst amt s)
      = committedTotal (Proof := Proof) (ofKernelState Digest Proof k bl) :=
  committed_transfer_conserves (Proof := Proof) (ofKernelState Digest Proof k bl) hsrc hdst hne

/-! ## It runs (`#eval`) — over the `Reference` CryptoKernel (`commit v r := v + r`).

The degenerate reference commitment `commit v r = v + r` lets us *see* the conserved committed
total as a concrete `Int`, and watch it stay fixed across a HIDDEN transfer. (With a real
Pedersen impl the commitments would be opaque curve points; the algebra is identical.) -/

open Dregg2.Crypto.Reference in
/-- Two accounts (0,1): account 0 hides amount 100 (blinding 7), account 1 hides amount 5
(blinding 3). -/
def demoCell : CommittedCell Reference.D Reference.P :=
  { accounts := {0, 1}
    amt   := fun i => if i = 0 then 100 else if i = 1 then 5 else 0
    blind := fun i => if i = 0 then 7   else if i = 1 then 3 else 0 }

-- The committed total (reference: 100+7 + 5+3 = 115) — the conserved hidden badge.
#eval committedTotal (Proof := Reference.P) demoCell                       -- 115

-- After hiding-transfer of amount 30 (blinding 4) from account 0 to account 1: still 115.
#eval committedTotal (Proof := Reference.P)
        (committedTransfer (Proof := Reference.P) demoCell 0 1 30 4)        -- 115

-- They are equal — the keystone, evaluated: the committed total is preserved across a hidden
-- transfer (the verifier never saw amount 30).
#eval decide (committedTotal (Proof := Reference.P)
        (committedTransfer (Proof := Reference.P) demoCell 0 1 30 4)
      = committedTotal (Proof := Reference.P) demoCell)                     -- true

end Dregg2.Exec.CellPrivacy
