/-
# Metatheory.Exec.Kernel — the EXECUTABLE dregg2 kernel (the Design-Spec layer).

The l4v `spec/design` analog: a concrete, **computable** kernel whose `exec` function
actually runs a turn, checking BOTH the resource law (conservation) AND authority (the
capability/integrity check), fail-closed. Where `Spec/Abstract` (Core, Authority, Boundary)
states the *laws*, here we build the *machine* and **prove it satisfies them**:
- `exec_conserves` — Law 1 (`Core` conservation) holds of every committed turn (PROVED);
- `exec_authorized` — no state change without authority (the integrity/confinement core);
- `kernel_run_conserves` — conservation across an ARBITRARY kernel execution (via
  `Execution.invariant_run`).

A `Turn` carries both effects at once: a resource move (`src ⇒ dst`, amount) performed
**under the actor's authority** (own `src`, or hold a cap on it). Balances are a total
`CellId → ℤ` over a finite `accounts` set (computable — `Finsupp`'s `+` is noncomputable;
ℤ so debt is representable and conservation is a clean group argument). Caps reuse
`Authority.Cap`/`Caps` (the seL4/l4v lift). Pure executable Lean, `#eval`-able; refines
`Spec/Abstract`. The Rust boundary + crypto stay out (`dregg2 §8`).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Metatheory.Authority.Positional
import Metatheory.Execution
import Metatheory.Tactics

namespace Metatheory.Exec

open Metatheory.Authority Metatheory.Execution

/-- A cell identity (reuses the authority `Label` = `Nat`). -/
abbrev CellId := Label

/-- **Kernel state:** the finite set of live `accounts`, a total balance function (ℤ:
debt-capable, a group), and the capability table. Executable. -/
structure KernelState where
  /-- The finite set of live cells whose balances are tracked / conserved. -/
  accounts : Finset CellId
  /-- Resource balance per cell. -/
  bal      : CellId → ℤ
  /-- The capability table (lift of l4v `Caps`). -/
  caps     : Caps

/-- **A turn:** the `actor` moves `amt` of resource `src ⇒ dst`. Both effects in one turn
— the resource move AND the authority under which it is done (checked by `exec`). -/
structure Turn where
  actor : CellId
  src   : CellId
  dst   : CellId
  amt   : ℤ

/-- **The authority check (computable).** Authorized over `src` iff the actor owns it
(`actor = src`, l4v `troa_lrefl` intra) OR holds a cap on it — a `node` cap, or an
`endpoint` cap carrying `write` (the cross case, an authorized policy edge). -/
def authorizedB (caps : Caps) (turn : Turn) : Bool :=
  (turn.actor == turn.src) ||
  (caps turn.actor).any (fun c =>
    (c == Cap.node turn.src) ||
    (match c with
     | .endpoint t rights => (t == turn.src) && rights.contains Auth.write
     | _ => false))

/-- The balance function after a transfer (debit `src`, credit `dst`). -/
def transferBal (bal : CellId → ℤ) (src dst : CellId) (amt : ℤ) : CellId → ℤ :=
  fun c => if c = src then bal c - amt else if c = dst then bal c + amt else bal c

/-- **The executable kernel transition.** Fail-closed: commits only when the actor is
authorized over `src`, the amount is non-negative and available, `src ≠ dst`, and both
cells are live accounts. -/
def exec (k : KernelState) (turn : Turn) : Option KernelState :=
  if authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts then
    some { k with bal := transferBal k.bal turn.src turn.dst turn.amt }
  else
    none

/-- **Total supply** over the live accounts — the conserved quantity (the concrete
`Core.Conservation` measure). -/
def total (k : KernelState) : ℤ := ∑ c ∈ k.accounts, k.bal c

/-! ## The kernel satisfies the abstract laws (the refinement, PROVED). -/

/-- Sum of a single-point indicator over a set containing the point. -/
theorem sum_indicator (acc : Finset CellId) (a : CellId) (v : ℤ) (ha : a ∈ acc) :
    (∑ c ∈ acc, (if c = a then v else 0)) = v := by
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (fun h => absurd ha h)]
  simp

/-- **Conservation core:** a transfer between two distinct live accounts preserves the
sum (the debit and credit cancel). -/
theorem transfer_sum_conserve (acc : Finset CellId) (bal : CellId → ℤ)
    (src dst : CellId) (amt : ℤ) (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, transferBal bal src dst amt c) = ∑ c ∈ acc, bal c := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hg : ∀ c ∈ acc, transferBal bal src dst amt c - bal c
      = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) := by
    intro c _
    unfold transferBal
    rcases eq_or_ne c src with h1 | h1
    · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hne]; ring
    · rcases eq_or_ne c dst with h2 | h2
      · subst h2; rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      sum_indicator acc src (-amt) hsrc, sum_indicator acc dst amt hdst]
  ring

/-- **Conservation (Law 1) — PROVED of the executable kernel.** Every committed turn
preserves total supply — the concrete refinement of `Core.conservation_ordinary`. -/
theorem exec_conserves (k k' : KernelState) (turn : Turn) (h : exec k turn = some k') :
    total k' = total k := by
  unfold exec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hne, hsrc, hdst⟩ := hg
    simpa [total] using transfer_sum_conserve k.accounts k.bal turn.src turn.dst turn.amt hsrc hdst hne
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **No state change without authority — PROVED** (the integrity/confinement core: the
kernel never moves a cell's resource on behalf of an unauthorized actor; the concrete
shadow of `Authority.Integrity` / l4v `call_kernel_integrity`). -/
theorem exec_authorized (k k' : KernelState) (turn : Turn) (h : exec k turn = some k') :
    authorizedB k.caps turn = true := by
  unfold exec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed — PROVED.** An unauthorized turn does NOT commit. -/
theorem exec_unauthorized_fails (k : KernelState) (turn : Turn)
    (h : authorizedB k.caps turn = false) : exec k turn = none := by
  unfold exec
  rw [if_neg]
  rintro ⟨ha, _⟩
  rw [h] at ha; exact absurd ha (by simp)

/-! ## Whole-execution conservation (the userspace-program layer). -/

/-- The kernel as an `Execution.System`: a step is any committed turn. -/
def kernelSystem : System where
  Config := KernelState
  Step k k' := ∃ turn, exec k turn = some k'

/-- **Conservation across an ENTIRE kernel run — PROVED** (`Execution.invariant_run`
lifting `exec_conserves`); the kernel-level analog of `channel_run_conserves`. -/
theorem kernel_run_conserves {k k' : KernelState} (hrun : Run kernelSystem k k') :
    total k' = total k := by
  have hpres : StepInvariant kernelSystem (fun c => total c = total k) := by
    intro a b ha hstep
    obtain ⟨turn, hturn⟩ := hstep
    rw [exec_conserves a b turn hturn]; exact ha
  exact invariant_run hpres hrun rfl

/-! ## It runs (`#eval`). -/

/-- Cell 0 owns 100, cell 1 owns 5; accounts = {0,1}; empty cap table (so authority is by
ownership only). -/
def s0 : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun _ => [] }

/-- Actor 0 transfers 30 to cell 1 (owns src 0). -/
def t1 : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }
/-- Actor 2 attempts the same — unauthorized (no cap on src 0). -/
def tBad : Turn := { actor := 2, src := 0, dst := 1, amt := 30 }

#eval (exec s0 t1).isSome                       -- true
#eval (exec s0 tBad).isSome                      -- false
#eval (exec s0 t1).map total                     -- some 105 (conserved: 70 + 35)
#eval total s0                                   -- 105

end Metatheory.Exec
