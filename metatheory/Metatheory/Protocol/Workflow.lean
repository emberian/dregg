/-
# Metatheory.Protocol.Workflow — an EXECUTABLE, formally-verified authenticated workflow.

A "DocuSign for authenticated workflows" demonstrator (CI / agents / engineering IDEs):
a multi-party workflow where **every step is capability-gated, protocol-ordered, and
attested** — and where Lean *proves* that no unauthorized or out-of-order step can ever
commit. The worked example is a 3-party code-review/CI sign-off:

    author submits  →  reviewer approves  →  CI bot merges

Each step (i) may be taken ONLY by the authorized party (the capability/role check —
the seL4-grade "who may sign"), (ii) is admissible ONLY in the correct phase (the
choreography order — you cannot merge before approval), and (iii) carries an
**attestation** verified through the `CryptoKernel` portal (the "signature" — and,
because it routes through `verify`, it can be a ZK proof: attest authorization without
revealing the witness).

What makes this more than DocuSign: the guarantees below are **machine-checked**, the
authorization is **capability-secure**, the attestation is **ZK-capable**, and the whole
thing is **agent-native** and **executable** (`#eval`). Parametric over any
`CryptoKernel`; the `#eval`s use the reference kernel (Rust supplies the real one).
-/
import Metatheory.CryptoKernel

namespace Metatheory.Protocol.Workflow

open Metatheory.Crypto

/-- A workflow participant (author = 0, reviewer = 1, CI = 2 in the demo). -/
abbrev Party := Nat

/-- The workflow's phase (its position in the choreography). -/
inductive Phase where
  | init | submitted | approved | merged
  deriving DecidableEq, Repr

/-- The steps of the workflow. -/
inductive StepKind where
  | submit | approve | merge
  deriving DecidableEq, Repr

/-- **The capability/role assignment** — which party is authorized for each step (the
"who may sign this" — in the real system this is a held capability, here a role id). -/
def authorizedParty : StepKind → Party
  | .submit  => 0   -- author
  | .approve => 1   -- reviewer
  | .merge   => 2   -- CI bot

/-- **The choreography order** — the phase each step requires (its precondition). -/
def precond : StepKind → Phase
  | .submit  => .init
  | .approve => .submitted
  | .merge   => .approved

/-- The phase resulting from a step. -/
def postPhase : StepKind → Phase
  | .submit  => .submitted
  | .approve => .approved
  | .merge   => .merged

variable {Digest Proof : Type} [AddCommGroup Digest]

/-- A signed step in the audit trail: the step, who took it, and the attestation
(`Proof`) the `CryptoKernel` verified against the step's statement. -/
structure Receipt (Proof : Type) where
  step  : StepKind
  actor : Party
  att   : Proof

/-- The workflow state: the current phase plus the append-only attested audit trail. -/
structure WState (Proof : Type) where
  phase : Phase
  log   : List (Receipt Proof)

/-- **The executable workflow transition.** A step commits ONLY when all three hold,
fail-closed: (1) the actor is the authorized party (capability), (2) the workflow is in
the step's required phase (choreography order), (3) the attestation `verify`s through the
`CryptoKernel` portal against the step's statement. On commit it advances the phase and
appends an attested receipt. -/
def exec [CryptoKernel Digest Proof] (stmt : Digest)
    (k : WState Proof) (s : StepKind) (actor : Party) (att : Proof) : Option (WState Proof) :=
  if actor = authorizedParty s ∧ k.phase = precond s
      ∧ CryptoKernel.verify stmt att = true then
    some { phase := postPhase s, log := ⟨s, actor, att⟩ :: k.log }
  else
    none

/-! ## The verified guarantees (the value proposition, PROVED). -/

/-- **Authenticity — PROVED:** a step commits ONLY if taken by its authorized party. No
unauthorized party can ever advance the workflow. -/
theorem exec_authorized [CryptoKernel Digest Proof] {stmt : Digest}
    {k k' : WState Proof} {s : StepKind} {actor : Party} {att : Proof}
    (h : exec stmt k s actor att = some k') : actor = authorizedParty s := by
  unfold exec at h
  by_cases hg : actor = authorizedParty s ∧ k.phase = precond s
      ∧ CryptoKernel.verify stmt att = true
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Protocol order — PROVED:** a step commits ONLY in its required phase. The
choreography cannot be skipped (e.g. no merge before approval). -/
theorem exec_in_order [CryptoKernel Digest Proof] {stmt : Digest}
    {k k' : WState Proof} {s : StepKind} {actor : Party} {att : Proof}
    (h : exec stmt k s actor att = some k') : k.phase = precond s := by
  unfold exec at h
  by_cases hg : actor = authorizedParty s ∧ k.phase = precond s
      ∧ CryptoKernel.verify stmt att = true
  · exact hg.2.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Attested — PROVED:** every committed step carries an attestation that the
`CryptoKernel` verified (the "signature" on the audit trail). -/
theorem exec_attested [CryptoKernel Digest Proof] {stmt : Digest}
    {k k' : WState Proof} {s : StepKind} {actor : Party} {att : Proof}
    (h : exec stmt k s actor att = some k') : CryptoKernel.verify stmt att = true := by
  unfold exec at h
  by_cases hg : actor = authorizedParty s ∧ k.phase = precond s
      ∧ CryptoKernel.verify stmt att = true
  · exact hg.2.2
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Tamper-evident audit trail — PROVED:** a committed step only ever APPENDS its
receipt; prior history is never rewritten (the log is append-only). -/
theorem exec_appends [CryptoKernel Digest Proof] {stmt : Digest}
    {k k' : WState Proof} {s : StepKind} {actor : Party} {att : Proof}
    (h : exec stmt k s actor att = some k') :
    k'.log = ⟨s, actor, att⟩ :: k.log := by
  unfold exec at h
  by_cases hg : actor = authorizedParty s ∧ k.phase = precond s
      ∧ CryptoKernel.verify stmt att = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; rw [← h]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **No merge without prior approval — PROVED** (a headline corollary): the CI bot can
merge only from the `approved` phase, which only `approve` (by the reviewer) produces. -/
theorem merge_requires_approved [CryptoKernel Digest Proof] {stmt : Digest}
    {k k' : WState Proof} {actor : Party} {att : Proof}
    (h : exec stmt k .merge actor att = some k') : k.phase = .approved :=
  exec_in_order h

/-! ## It runs (`#eval`, on the reference kernel — Rust supplies the real one). -/

section Demo

/-- The initial workflow state. -/
def s0 : WState Reference.P := { phase := .init, log := [] }

/-- A valid attestation under the reference kernel echoes the statement (`verify = decide
(stmt = att)`); the real kernel checks a signature/ZK proof. We use statement `7`. -/
def att : Reference.P := 7

#eval (exec (7 : Reference.D) s0 .submit 0 att).map (·.phase)        -- some submitted (author, init)
#eval (exec (7 : Reference.D) s0 .merge 2 att).map (·.phase)         -- none (can't merge from init)
#eval (exec (7 : Reference.D) s0 .submit 1 att).map (·.phase)        -- none (reviewer can't submit)
#eval (exec (7 : Reference.D) s0 .submit 0 9).map (·.phase)          -- none (bad attestation: 9 ≠ 7)

/-- The happy path: submit → approve → merge, threaded. -/
def runHappy : Option (WState Reference.P) := do
  let k1 ← exec (7 : Reference.D) s0 .submit 0 att
  let k2 ← exec (7 : Reference.D) k1 .approve 1 att
  exec (7 : Reference.D) k2 .merge 2 att

#eval runHappy.map (·.phase)         -- some merged
#eval runHappy.map (·.log.length)    -- some 3   (three attested receipts in the audit trail)

end Demo

end Metatheory.Protocol.Workflow
