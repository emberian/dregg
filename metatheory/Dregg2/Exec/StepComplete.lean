/-
# Dregg2.Exec.StepComplete — the soundness SPINE (ROADMAP Phase 2).

The single keystone both tracks converge on. `Boundary.lean` proves the abstract result
`stepComplete_preserves`: *if* every step attests the full `StepInv = Conservation ∧
Authority ∧ ChainLink ∧ ObsAdvance`, soundness holds along the whole execution. But in
dregg1 that is **unverified and likely false** (auth runs as plain Rust; `AUTH_ROOT`/
`CONSERVATION_VECTOR`/the chainlink are not all in the proof's PI). Here we make the
executable kernel **genuinely step-complete** and PROVE it — which:
  * turns `Core.conservation_step` from a PRIMITIVE into a THEOREM (it is the
    `Conservation` conjunct of a committed `exec` step), and
  * realizes `Boundary.StepComplete` for a concrete machine, so `stepComplete_preserves`
    fires end-to-end, and
  * unblocks the dregg1→dregg2 cascade of the `turn` executor (the gating risk in
    `docs/rebuild/DREGG1-TO-DREGG2.md`).

We extend the kernel with the **receipt chain** (the append-only log = the ChainLink /
ObsAdvance carrier) and prove every committed chained step attests all four conjuncts.
(The chain's *digest* is a `CryptoKernel.hash` of the log — the Rust/portal's job; the
chain *law* — append-only + advancing — is structural and proved here. This is also the
"field-friendly" shape that makes the future circuit-from-Lean bridge clean.)
-/
import Dregg2.Exec.Kernel
import Dregg2.Execution

namespace Dregg2.Exec

open Dregg2.Execution

/-- The kernel state plus its **receipt chain** (the append-only audit log). The log is
the ChainLink/ObsAdvance carrier: each committed turn extends it, so replay is detectable
(the chain would not advance). Its digest in the real system is `CryptoKernel.hash log`. -/
structure ChainedState where
  kernel : KernelState
  log    : List Turn

/-- The chained executor: run `Kernel.exec` on the state, and on success extend the
receipt chain with the turn. Fail-closed (inherits `exec`'s authority+conservation gate). -/
def cexec (s : ChainedState) (t : Turn) : Option ChainedState :=
  match exec s.kernel t with
  | some k' => some { kernel := k', log := t :: s.log }
  | none    => none

/-! ## The four `StepInv` conjuncts, concretely (the in-circuit PI surface, in Lean). -/

/-- **Conservation conjunct** — total supply preserved (the executable `Core` Law 1). -/
def consP (s : ChainedState) (_t : Turn) (s' : ChainedState) : Prop :=
  total s'.kernel = total s.kernel

/-- **Authority conjunct** — the turn was authorized (the `Authority`/integrity check). -/
def authP (s : ChainedState) (t : Turn) (_s' : ChainedState) : Prop :=
  authorizedB s.kernel.caps t = true

/-- **ChainLink conjunct** — the new state's chain extends the old by exactly this turn
(`previous_receipt_hash` link; no fork, no rewrite). -/
def chainP (s : ChainedState) (t : Turn) (s' : ChainedState) : Prop :=
  s'.log = t :: s.log

/-- **ObsAdvance conjunct** — the observation strictly advances (the chain grew), so a
replayed turn is detectable (it would not advance the chain). -/
def obsP (s : ChainedState) (_t : Turn) (s' : ChainedState) : Prop :=
  s'.log.length = s.log.length + 1

/-- The full per-step invariant: all four conjuncts (the concrete `Boundary.StepInv`). -/
def fullStepInv (s : ChainedState) (t : Turn) (s' : ChainedState) : Prop :=
  consP s t s' ∧ authP s t s' ∧ chainP s t s' ∧ obsP s t s'

/-! ## Step-completeness — PROVED (the spine). -/

/-- **`cexec_attests` — the executable kernel is STEP-COMPLETE (PROVED).** Every committed
chained step attests the FULL `StepInv`: Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance.
This is the concrete realization of `Boundary.StepComplete`, and its first conjunct is
exactly `Core.conservation_step` *as a theorem about the machine* (no longer a primitive). -/
theorem cexec_attests {s s' : ChainedState} {t : Turn} (h : cexec s t = some s') :
    fullStepInv s t s' := by
  unfold cexec at h
  split at h
  · next k' heq =>
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_, rfl, ?_⟩
    · exact exec_conserves s.kernel k' t heq            -- Conservation
    · exact exec_authorized s.kernel k' t heq           -- Authority
    · rfl                                               -- ObsAdvance: (t :: log).length = log.length + 1
  · exact absurd h (by simp)

/-- **`conservation_step` realized — the abstract primitive is now a theorem.** The
`Conservation` conjunct of step-completeness: a committed executable step preserves the
measure. (`Core.conservation_step` was `sorry`'d as the operational obligation; this
discharges it for the executable kernel.) -/
theorem conservation_step_realized {s s' : ChainedState} {t : Turn}
    (h : cexec s t = some s') : total s'.kernel = total s.kernel :=
  (cexec_attests h).1

/-! ## End-to-end soundness along the whole execution (via `Execution.invariant_run`). -/

/-- The chained kernel as a transition system. -/
def chainedSystem : System where
  Config := ChainedState
  Step s s' := ∃ t, cexec s t = some s'

/-- **Soundness along any execution — PROVED.** Any state-predicate `Good` preserved by
every step that attests `fullStepInv` holds at every reachable configuration of the whole
chained-kernel execution. This is `Boundary.stepComplete_preserves` realized for the
concrete machine — step-completeness ⇒ whole-execution safety, end to end. -/
theorem chained_sound (Good : ChainedState → Prop)
    (hpres : ∀ s t s', Good s → fullStepInv s t s' → Good s')
    {s s' : ChainedState} (hrun : Run chainedSystem s s') (hs : Good s) : Good s' := by
  refine invariant_run (S := chainedSystem) (I := Good) ?_ hrun hs
  intro a b ha hstep
  obtain ⟨t, ht⟩ := hstep
  exact hpres a t b ha (cexec_attests ht)

/-- **Conservation across the entire execution — PROVED** (the headline instance of
`chained_sound`): total supply is invariant over any run of the chained kernel. -/
theorem chained_run_conserves {s s' : ChainedState} (hrun : Run chainedSystem s s') :
    total s'.kernel = total s.kernel := by
  have : (fun c => total c.kernel = total s.kernel) s' :=
    chained_sound (fun c => total c.kernel = total s.kernel)
      (by intro a b _ ha hinv; rw [hinv.1]; exact ha) hrun rfl
  exact this

end Dregg2.Exec
