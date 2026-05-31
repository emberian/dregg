/-
# Dregg2.Protocol.WorkflowGuard — the RDII workflow's gates RE-FOUND as `Spec.Guard` instances.

This is the **Spec layer of the first verified application** (PHASE-CONSTRUCTION §2, the
"minimal closed loop for ONE application"; first-90-days step 5). `Protocol/Workflow.lean`
is the executable RDII "DocuSign-for-workflows" demonstrator — author→reviewer→CI, every
step capability-gated, phase-ordered, and attested via the `CryptoKernel.verify` portal. It
already PROVES its guarantees (`exec_authorized` / `exec_in_order` / `exec_attested` /
`merge_requires_approved`) *directly* over the concrete `exec`.

This module **re-founds those guarantees on the abstract `Spec.Guard` law**: it expresses
each workflow gate as a `Spec.Guard` term and PROVES the concrete `Workflow.lean` predicate
is EXACTLY the corresponding `Guard.admits`. The three gates are:

  1. **authorization** — "only the authorized signer may take this step" — a `firstParty`
     Guard over the actor/role field (`req.actor = authorizedParty req.step`). In the RDII
     model "who may sign" is a decidable role check (the held-cap role id), so it is the
     intra-vat *positional* / first-party face of authority (cf. `Coherence §1`); the
     witnessed face is the attestation gate (3).
  2. **phase-ordering** — "release only after review" — a `firstParty` Guard over the phase
     field (`req.phase = precond req.step`), the `allowedTransitions`-style choreography
     precondition.
  3. **attestation** — "the step carries a verifying proof" — a `witnessed` Guard at the
     verify seam (`CryptoKernel.verify stmt att`, the §8 oracle, ZK-capable).

The payoff (the closed loop's Spec side): the workflow's authorization is **machine-checked
from the abstract `Spec.Guard` law down to the running predicate** — the concrete app gate
*refines* the abstract Guard law, with no remainder. `workflow_step_admits_iff_guards` ties
the whole step's admissibility to the conjunction (`Guard.all`) of the three gates: the
workflow step commits *exactly* when the abstract Guard web admits it.

Discipline (matching the lib): faithful `↔`s with real content, every keystone
`#assert_axioms`-clean, no `axiom`/`admit`/`native_decide`/`sorry`. Imports ONLY existing
built modules; touches no sibling file. The attestation gate's `witnessed` branch routes
through the `Verifiable`/`CryptoKernel.verify` oracle — that is the honest §8 seam, NOT a
gap: `admits (witnessed stmt) = Verify stmt (w stmt)`, and the bridge to the workflow's
`verify` is exact under the natural witness supply.
-/
import Dregg2.Protocol.Workflow
import Dregg2.Spec.Guard

namespace Dregg2.Protocol.WorkflowGuard

open Dregg2.Protocol.Workflow
open Dregg2.Spec
open Dregg2.Crypto
open Dregg2.Laws

/-! ## §1 — The `Request`: the facts a workflow gate reads.

A `Spec.Guard` reads a `Request` — the transition/action facts. For the workflow, the gate
reads exactly the three fields `exec`'s `if`-guard inspects: the step kind, the actor, and
the current phase. (No `Nat`-for-semantics: the request bundles the actual workflow fields.)
The attestation is supplied separately — through the verify seam's witness map (§4) — exactly
as `Spec.Guard.admits` splits demand (the guard) from supply (`(req, w)`). -/

/-- **`WFRequest`** — the facts a workflow gate reads: the step, the actor taking it, and
the phase the workflow is in. This IS the trio `Workflow.exec` decides against. -/
structure WFRequest where
  step  : StepKind
  actor : Party
  phase : Phase
  deriving Repr

/-! ## §2 — The three gates as `Spec.Guard` terms.

Each gate is one line over `Guard.firstParty` / `Guard.witnessed`, mirroring the
`Spec/Guard.lean §7` derived reconstructions and `Coherence §1`'s `conferralGuard`. -/

variable {Digest Proof : Type} [AddCommGroup Digest]

/-- **The authorization gate (`firstParty`).** "Only the authorized signer may take this
step": admits iff `req.actor = authorizedParty req.step`. The role/cap check is decidable
*now* (the intra-vat positional face), so it is a `firstParty` Guard — the same shape as
`Coherence.conferralGuard`. `Statement`/`Witness` are free here (no witnessed branch). -/
def authGuard {Statement : Type} : Guard WFRequest Statement :=
  Guard.firstParty (fun req => decide (req.actor = authorizedParty req.step))

/-- **The phase-ordering gate (`firstParty`).** "Release only after review": admits iff
`req.phase = precond req.step` — the choreography precondition (an `allowedTransitions`-style
predicate over the phase field). Decidable now ⇒ `firstParty`. -/
def orderGuard {Statement : Type} : Guard WFRequest Statement :=
  Guard.firstParty (fun req => decide (req.phase = precond req.step))

/-- **The attestation gate (`witnessed`).** "The step carries a verifying proof": a
`witnessed` Guard at the §8 verify seam over the step's statement `stmt`. `admits` routes
through `Verifiable.Verify stmt (w stmt)` — i.e. `CryptoKernel.verify stmt att` under the
natural witness supply (§4). This is `Guard.senderAuthorized` reused for the attestation
claim (the same `witnessed` primitive). ZK-capable, fail-closed. -/
def attestGuard (stmt : Digest) : Guard WFRequest Digest :=
  Guard.witnessed stmt

/-- **The whole-step gate** — the conjunction (`Guard.all`, the meet ∧) of the three gates.
This is the abstract Guard web for one workflow step: authorized AND in-order AND attested. -/
def stepGuard (stmt : Digest) : Guard WFRequest Digest :=
  Guard.all [authGuard, orderGuard, attestGuard stmt]

/-! ## §3 — The natural witness supply.

`Guard.admits` takes a witness map `w : Statement → Witness` supplied at evaluation time. The
workflow's attestation `att : Proof` is the witness for the step's statement; the natural
supply is the constant map `fun _ => att`. (For the `firstParty` gates the supply is
irrelevant — they never touch the seam.) -/

/-- The witness supply that hands the workflow's attestation `att` to the verify seam. -/
def wsupply (att : Proof) : Digest → Proof := fun _ => att

/-! ## §4 — The refinement equivalences (the real content).

Each concrete `Workflow.lean` gate check IS, with no remainder, the corresponding
`Guard.admits`. We prove the `↔` per gate, then assemble the whole-step `↔`. The verify
oracle is the `Verifiable Digest Proof` instance INDUCED by the `CryptoKernel`
(`verifiableOfCryptoKernel`), so the witnessed branch's `Verify` IS `CryptoKernel.verify`. -/

section Refinement

variable [CryptoKernel Digest Proof]

/-- **`workflow_authz_is_guard` (PROVED) — the authorization gate refines the abstract Guard.**
The concrete workflow authorization check (`actor = authorizedParty s`, the predicate behind
`Workflow.exec_authorized`) holds IFF the abstract `authGuard` admits the request. The app's
"who may sign" gate is EXACTLY a `Spec.Guard.firstParty` admission — machine-checked from the
abstract law to the running role check. -/
theorem workflow_authz_is_guard (s : StepKind) (actor : Party) (phase : Phase)
    (att : Proof) :
    Guard.admits (authGuard (Statement := Digest)) ⟨s, actor, phase⟩ (wsupply att) = true
      ↔ actor = authorizedParty s := by
  unfold authGuard
  rw [Guard.admits_firstParty]
  exact decide_eq_true_iff

/-- **`workflow_order_is_guard` (PROVED) — the phase-ordering gate refines the abstract Guard.**
The concrete choreography check (`phase = precond s`, the predicate behind
`Workflow.exec_in_order`) holds IFF the abstract `orderGuard` admits. The app's "release only
after review" precondition is EXACTLY a `Spec.Guard.firstParty` admission. -/
theorem workflow_order_is_guard (s : StepKind) (actor : Party) (phase : Phase)
    (att : Proof) :
    Guard.admits (orderGuard (Statement := Digest)) ⟨s, actor, phase⟩ (wsupply att) = true
      ↔ phase = precond s := by
  unfold orderGuard
  rw [Guard.admits_firstParty]
  exact decide_eq_true_iff

/-- **`workflow_attest_is_guard` (PROVED) — the attestation gate refines the abstract Guard.**
The concrete attestation check (`CryptoKernel.verify stmt att = true`, the predicate behind
`Workflow.exec_attested`) holds IFF the abstract `attestGuard stmt` admits under the natural
supply. The app's "the step carries a verifying proof" gate is EXACTLY a `Spec.Guard.witnessed`
admission at the §8 verify seam — the oracle, honestly stated, NOT a hidden gap. -/
theorem workflow_attest_is_guard (stmt : Digest) (s : StepKind) (actor : Party) (phase : Phase)
    (att : Proof) :
    Guard.admits (attestGuard stmt) ⟨s, actor, phase⟩ (wsupply att) = true
      ↔ CryptoKernel.verify stmt att = true := by
  unfold attestGuard wsupply
  rw [Guard.admits_witnessed]
  rfl

/-! ## §5 — The whole-step refinement (the app-level statement).

The workflow step's `exec` `if`-guard is the conjunction of the three concrete checks; the
abstract `stepGuard` is `Guard.all` of the three abstract gates. They coincide. -/

/-- **`workflow_step_admits_iff_guards` (PROVED) — the closed-loop Spec statement.**
The whole-step abstract Guard web (`stepGuard stmt` = the `Guard.all` conjunction of
authorization, ordering, and attestation) admits the request `⟨s, actor, phase⟩` under the
natural supply EXACTLY when all three concrete `Workflow.exec` checks hold. So the workflow
step is admissible *precisely when the abstract Guard law admits it* — the app's authorization
is machine-checked from the abstract `Spec.Guard` down to the running predicate, no remainder.
This is the Spec side of the first verified application. -/
theorem workflow_step_admits_iff_guards (stmt : Digest)
    (s : StepKind) (actor : Party) (phase : Phase) (att : Proof) :
    Guard.admits (stepGuard stmt) ⟨s, actor, phase⟩ (wsupply att) = true
      ↔ (actor = authorizedParty s ∧ phase = precond s
          ∧ CryptoKernel.verify stmt att = true) := by
  unfold stepGuard
  rw [Guard.admits_all]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (workflow_authz_is_guard s actor phase att).mp
        (h authGuard (by simp))
    · exact (workflow_order_is_guard s actor phase att).mp
        (h orderGuard (by simp))
    · exact (workflow_attest_is_guard stmt s actor phase att).mp
        (h (attestGuard stmt) (by simp))
  · rintro ⟨ha, ho, hv⟩ g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact (workflow_authz_is_guard s actor phase att).mpr ha
    · exact (workflow_order_is_guard s actor phase att).mpr ho
    · exact (workflow_attest_is_guard stmt s actor phase att).mpr hv

/-- **`exec_admits_step_guard` (PROVED) — `exec` commits ⇒ the abstract Guard web admits.**
The executable bridge: whenever the concrete `Workflow.exec` commits a step (returns `some`),
the abstract `stepGuard` admits the corresponding request. So every step the running workflow
takes is one the abstract `Spec.Guard` law sanctions — the refinement direction the app needs.
(The three concrete consequences are exactly `Workflow.exec_authorized` / `exec_in_order` /
`exec_attested`, here re-collected onto the Guard web.) -/
theorem exec_admits_step_guard (stmt : Digest)
    {k k' : WState Proof} {s : StepKind} {actor : Party} {att : Proof}
    (h : Workflow.exec stmt k s actor att = some k') :
    Guard.admits (stepGuard stmt) ⟨s, actor, k.phase⟩ (wsupply att) = true :=
  (workflow_step_admits_iff_guards stmt s actor k.phase att).mpr
    ⟨Workflow.exec_authorized h, Workflow.exec_in_order h, Workflow.exec_attested h⟩

end Refinement

/-! ## §6 — Discriminating smoke checks (`example`/`#eval`, fail-closed).

On the reference kernel (`verify stmt att = decide (stmt = att)`; statement `7`, good att
`7`), the abstract Guard web ADMITS an authorized in-order attested step and REJECTS any step
that is out-of-order, unauthorized, or unattested. These are the negative regression guards:
the Guard refinement is DISCRIMINATING, not vacuous. -/

section Smoke

open Dregg2.Crypto.Reference

/-- The good attestation under the reference kernel (echoes statement `7`). -/
private def gAtt : Reference.P := 7
/-- A bad attestation (`9 ≠ 7` ⇒ `verify` rejects). -/
private def bAtt : Reference.P := 9

/-- ADMITS: author (0) submits from `init` with a valid attestation — all three gates pass. -/
example :
    Guard.admits (stepGuard (Digest := Reference.D) 7)
      ⟨.submit, 0, .init⟩ (wsupply gAtt) = true := by
  rw [workflow_step_admits_iff_guards]
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- REJECTS (out of order): merge from `init` — the order gate fails (precond is `approved`). -/
example :
    Guard.admits (stepGuard (Digest := Reference.D) 7)
      ⟨.merge, 2, .init⟩ (wsupply gAtt) = false := by
  rw [Bool.eq_false_iff, ne_eq, workflow_step_admits_iff_guards]
  decide

/-- REJECTS (unauthorized): reviewer (1) tries to submit — the auth gate fails. -/
example :
    Guard.admits (stepGuard (Digest := Reference.D) 7)
      ⟨.submit, 1, .init⟩ (wsupply gAtt) = false := by
  rw [Bool.eq_false_iff, ne_eq, workflow_step_admits_iff_guards]
  decide

/-- REJECTS (unattested): author submits in-order but with a bad attestation (`9 ≠ 7`) — the
attestation gate (the §8 verify seam) fails. Fail-closed. -/
example :
    Guard.admits (stepGuard (Digest := Reference.D) 7)
      ⟨.submit, 0, .init⟩ (wsupply bAtt) = false := by
  rw [Bool.eq_false_iff, ne_eq, workflow_step_admits_iff_guards]
  decide

-- The same, executable, as `#eval` (the discriminating admit/reject vector):
#eval Guard.admits (stepGuard (Digest := Reference.D) 7)
  ⟨.submit, 0, .init⟩ (wsupply gAtt)   -- true   (authorized, in-order, attested)
#eval Guard.admits (stepGuard (Digest := Reference.D) 7)
  ⟨.merge, 2, .init⟩ (wsupply gAtt)    -- false  (out of order: can't merge from init)
#eval Guard.admits (stepGuard (Digest := Reference.D) 7)
  ⟨.submit, 1, .init⟩ (wsupply gAtt)   -- false  (unauthorized: reviewer can't submit)
#eval Guard.admits (stepGuard (Digest := Reference.D) 7)
  ⟨.submit, 0, .init⟩ (wsupply bAtt)   -- false  (unattested: bad proof 9 ≠ 7)

end Smoke

/-! ## §7 — Axiom-hygiene tripwires.

Each refinement keystone depends ONLY on the three standard kernel axioms (no `sorryAx`):
the three per-gate equivalences, the whole-step web equivalence, and the `exec`⇒admits
bridge. This certifies the workflow's authorization is genuinely machine-checked from the
abstract `Spec.Guard` law down to the running predicate — not a `sorry`-alias. -/

#assert_axioms workflow_authz_is_guard
#assert_axioms workflow_order_is_guard
#assert_axioms workflow_attest_is_guard
#assert_axioms workflow_step_admits_iff_guards
#assert_axioms exec_admits_step_guard

end Dregg2.Protocol.WorkflowGuard
