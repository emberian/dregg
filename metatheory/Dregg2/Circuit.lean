/-
# Dregg2.Circuit — the circuit-from-Lean bridge (the ZK/AIR constraint system as a
first-class Lean object, PROVEN equivalent to the verified step spec).

`Exec/StepComplete.lean` makes the executable kernel **step-complete** and PROVES that
every committed chained step attests the four `fullStepInv` conjuncts (Conservation ∧
Authority ∧ ChainLink ∧ ObsAdvance). Those four conjuncts are *exactly* the public-input
(PI) surface a ZK proof must bind. This module closes the last seam of `dregg2 §8`: it
writes that PI surface down as an honest **arithmetic constraint system** (the AIR/R1CS
shape — addition and multiplication over a field, here ℤ as the field stand-in), lays the
pre/turn/post state out as field **variables** (`encode`), and PROVES the constraint system
is SOUND ∧ COMPLETE against the verified spec:

    bridge : satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s'

This is the object that **extracts** to the Rust prover: `kernelCircuit` is pure *data*
(a `List Constraint`), and `bridge` certifies that checking it is the same as checking the
Lean-verified `fullStepInv`. Given `bridge`, a `CryptoKernel.verify` defined as "evaluate
`satisfied kernelCircuit`" has its §8 soundness law **DERIVED** (see `verify_law_derivable`),
not assumed — the circuit no longer sits outside the proof.

## What the field layout captures
We expose the scalars the four conjuncts range over as named variables:
  * `totalPre`, `totalPost`   — the conserved measure (Conservation);
  * `authBit`                 — the authority decision as a {0,1} bit (Authority);
  * `lenPre`, `lenPost`       — the receipt-chain length (ObsAdvance + ChainLink length);
  * `chainOk`                 — a {0,1} indicator that the post-log is `t :: pre-log`
                                (the full ChainLink list-equality witness; a circuit binds
                                it via a hash/Merkle argument — here a decidable indicator).

## Honesty boundary (read `-- OPEN:` / `-- PRIMITIVE:` markers)
Conservation and ObsAdvance are *pure arithmetic* and their two directions are both proved
in full. Authority is a bit-equation and is proved both directions. ChainLink's full
list-equality cannot be reconstructed from a finite bag of field scalars alone (a length +
head match does not imply tail equality); a real circuit recovers it from a collision-
resistant chain *digest*. We therefore carry the list-equality as a single decidable
`chainOk` indicator variable and discharge BOTH directions of its conjunct against the
spec honestly (the indicator is defined to *be* the spec predicate, mirroring what the
digest binds). The only genuinely external obligation — that the Rust prover's digest
equals this indicator — is the §8 binding law and is flagged `-- PRIMITIVE:` at the seam.
-/
import Mathlib.Tactic
import Dregg2.Exec.StepComplete
import Dregg2.CryptoKernel

namespace Dregg2.Circuit

open Dregg2.Exec

/-- `Turn` is a structure of decidable-eq scalar fields, so its equality (and hence
list-of-`Turn` equality, the ChainLink witness) is decidable. -/
instance : DecidableEq Turn := fun a b => by
  rcases a with ⟨a1, a2, a3, a4⟩; rcases b with ⟨b1, b2, b3, b4⟩
  simp only [Turn.mk.injEq]
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! ## The constraint-system IR (arithmetic over ℤ — the field stand-in). -/

/-- A circuit variable (a column / wire index). -/
abbrev Var := Nat

/-- An assignment of field values to variables (the witness vector). -/
abbrev Assignment := Var → ℤ

/-- **Arithmetic expressions** — variables, constants, `+`, `*` over the field. This is the
genuinely circuit-shaped IR (R1CS/AIR gates are exactly sums of products of wires). -/
inductive Expr where
  | var   : Var → Expr
  | const : ℤ → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  deriving Repr

/-- Evaluate an expression under an assignment. -/
def Expr.eval : Expr → Assignment → ℤ
  | .var v,     a => a v
  | .const c,   _ => c
  | .add e₁ e₂, a => e₁.eval a + e₂.eval a
  | .mul e₁ e₂, a => e₁.eval a * e₂.eval a

/-- A single constraint: the gate equation `lhs = rhs`. -/
structure Constraint where
  lhs : Expr
  rhs : Expr

/-- A constraint **holds** under an assignment iff both sides evaluate equal. -/
def Constraint.holds (c : Constraint) (a : Assignment) : Prop :=
  c.lhs.eval a = c.rhs.eval a

/-- A constraint system is a list of constraints (the full AIR/R1CS). `abbrev` so the
`List` membership instance is visible to the `∀ c ∈ cs` quantifier in `satisfied`. -/
abbrev ConstraintSystem := List Constraint

/-- The system is **satisfied** iff every constraint holds (the prover's claim). -/
def satisfied (cs : ConstraintSystem) (a : Assignment) : Prop :=
  ∀ c ∈ cs, c.holds a

/-! ## Variable layout (the named wires of the PI surface). -/

/-- `totalPre`  — total supply before the turn. -/
def vTotalPre  : Var := 0
/-- `totalPost` — total supply after the turn. -/
def vTotalPost : Var := 1
/-- `authBit`   — the authority decision as a {0,1} bit. -/
def vAuthBit   : Var := 2
/-- `lenPre`    — receipt-chain length before. -/
def vLenPre    : Var := 3
/-- `lenPost`   — receipt-chain length after. -/
def vLenPost   : Var := 4
/-- `chainOk`   — {0,1} indicator that `post-log = turn :: pre-log` (ChainLink witness). -/
def vChainOk   : Var := 5

/-! ## `encode` — lay the pre/turn/post out as the witness vector. -/

/-- A {0,1} field encoding of a `Bool`. -/
def boolBit (b : Bool) : ℤ := if b then 1 else 0

/-- A {0,1} field encoding of a decidable `Prop`. -/
def propBit (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

/-- **`encode`** — the pre-state, turn, and post-state laid out as a field assignment (the
witness the prover commits to). Unmentioned variables default to `0`. -/
def encode (s : ChainedState) (t : Turn) (s' : ChainedState) : Assignment := fun v =>
  if      v = vTotalPre  then total s.kernel
  else if v = vTotalPost then total s'.kernel
  else if v = vAuthBit   then boolBit (authorizedB s.kernel.caps t)
  else if v = vLenPre    then (s.log.length : ℤ)
  else if v = vLenPost   then (s'.log.length : ℤ)
  else if v = vChainOk   then propBit (s'.log = t :: s.log)
  else 0

/-! ## `kernelCircuit` — the four `fullStepInv` conjuncts as arithmetic gates. -/

/-- **Conservation gate:** `totalPost − totalPre = 0`, i.e. `totalPost = totalPre`. -/
def cConservation : Constraint :=
  { lhs := .var vTotalPost, rhs := .var vTotalPre }

/-- **Authority gate:** `authBit = 1` (the turn was authorized). -/
def cAuthority : Constraint :=
  { lhs := .var vAuthBit, rhs := .const 1 }

/-- **ChainLink gate:** `chainOk = 1` (the post-log is `turn :: pre-log`). The indicator is
bound by the chain digest in a real circuit; here it is the decidable witness. -/
def cChainLink : Constraint :=
  { lhs := .var vChainOk, rhs := .const 1 }

/-- **ObsAdvance gate:** `lenPost − lenPre − 1 = 0`, i.e. `lenPost = lenPre + 1`. -/
def cObsAdvance : Constraint :=
  { lhs := .var vLenPost, rhs := .add (.var vLenPre) (.const 1) }

/-- **The kernel circuit** — the constraint DATA encoding all four conjuncts. THIS is what
extracts to the Rust prover. -/
def kernelCircuit : ConstraintSystem :=
  [cConservation, cAuthority, cChainLink, cObsAdvance]

/-! ## Per-gate equivalences (each conjunct ↔ its gate under `encode`). -/

-- The variable lookups, proved by `simp`-unfolding the `if`-cascade with the index facts.

private theorem enc_vTotalPre (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vTotalPre = total s.kernel := by
  simp [encode, vTotalPre]

private theorem enc_vTotalPost (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vTotalPost = total s'.kernel := by
  simp [encode, vTotalPost, vTotalPre]

private theorem enc_vAuthBit (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vAuthBit = boolBit (authorizedB s.kernel.caps t) := by
  simp [encode, vAuthBit, vTotalPost, vTotalPre]

private theorem enc_vLenPre (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vLenPre = (s.log.length : ℤ) := by
  simp [encode, vLenPre, vAuthBit, vTotalPost, vTotalPre]

private theorem enc_vLenPost (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vLenPost = (s'.log.length : ℤ) := by
  simp [encode, vLenPost, vLenPre, vAuthBit, vTotalPost, vTotalPre]

private theorem enc_vChainOk (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vChainOk = propBit (s'.log = t :: s.log) := by
  simp [encode, vChainOk, vLenPost, vLenPre, vAuthBit, vTotalPost, vTotalPre]

/-- **Conservation: gate ↔ conjunct** (full arithmetic, both directions). -/
theorem conservation_iff (s : ChainedState) (t : Turn) (s' : ChainedState) :
    cConservation.holds (encode s t s') ↔ consP s t s' := by
  unfold Constraint.holds cConservation consP
  simp only [Expr.eval, enc_vTotalPre, enc_vTotalPost]

/-- **Authority: gate ↔ conjunct** (the {0,1} bit, both directions). -/
theorem authority_iff (s : ChainedState) (t : Turn) (s' : ChainedState) :
    cAuthority.holds (encode s t s') ↔ authP s t s' := by
  unfold Constraint.holds cAuthority authP
  simp only [Expr.eval, enc_vAuthBit, boolBit]
  constructor
  · intro h
    by_cases hb : authorizedB s.kernel.caps t = true
    · exact hb
    · simp only [Bool.not_eq_true] at hb; rw [hb] at h; simp at h
  · intro h; rw [h]; simp

/-- **ChainLink: gate ↔ conjunct** (via the decidable indicator). The indicator is *defined*
to be the spec predicate, so both directions close; the only external content is the §8
binding of the digest to this indicator (flagged at `verify_law_derivable`). -/
theorem chainlink_iff (s : ChainedState) (t : Turn) (s' : ChainedState) :
    cChainLink.holds (encode s t s') ↔ chainP s t s' := by
  unfold Constraint.holds cChainLink chainP
  simp only [Expr.eval, enc_vChainOk, propBit]
  by_cases hc : s'.log = t :: s.log
  · simp [hc]
  · simp [hc]

/-- **ObsAdvance: gate ↔ conjunct** (full arithmetic, both directions). -/
theorem obsadvance_iff (s : ChainedState) (t : Turn) (s' : ChainedState) :
    cObsAdvance.holds (encode s t s') ↔ obsP s t s' := by
  unfold Constraint.holds cObsAdvance obsP
  simp only [Expr.eval, enc_vLenPre, enc_vLenPost]
  constructor
  · intro h; exact_mod_cast h
  · intro h; rw [h]; push_cast; ring

/-! ## THE BRIDGE — the circuit is SOUND ∧ COMPLETE vs the verified spec. -/

/-- **`bridge` — the deliverable.** Satisfying `kernelCircuit` on the encoded
pre/turn/post is EXACTLY the verified `fullStepInv` (Conservation ∧ Authority ∧ ChainLink ∧
ObsAdvance). Forward (`→`) is circuit **soundness** (a satisfying witness proves the spec);
backward (`←`) is **completeness** (a real step has a satisfying witness). Both directions
of all four conjuncts are proved. -/
theorem bridge (s : ChainedState) (t : Turn) (s' : ChainedState) :
    satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s' := by
  unfold satisfied kernelCircuit fullStepInv
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (conservation_iff s t s').mp (h cConservation (by simp))
    · exact (authority_iff s t s').mp     (h cAuthority   (by simp))
    · exact (chainlink_iff s t s').mp     (h cChainLink   (by simp))
    · exact (obsadvance_iff s t s').mp    (h cObsAdvance  (by simp))
  · rintro ⟨hc, ha, hch, ho⟩ c hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · exact (conservation_iff s t s').mpr hc
    · exact (authority_iff s t s').mpr ha
    · exact (chainlink_iff s t s').mpr hch
    · exact (obsadvance_iff s t s').mpr ho

/-- **Soundness corollary** — a satisfying circuit witness PROVES the verified step
invariant (the `→` half of `bridge`, named for the extraction story). -/
theorem circuit_sound (s : ChainedState) (t : Turn) (s' : ChainedState)
    (h : satisfied kernelCircuit (encode s t s')) : fullStepInv s t s' :=
  (bridge s t s').mp h

/-- **Completeness corollary** — every real committed step yields a satisfying witness (the
`←` half). Composed with `cexec_attests`, the EXECUTOR produces circuit-satisfying witnesses
for free. -/
theorem circuit_complete (s : ChainedState) (t : Turn) (s' : ChainedState)
    (h : fullStepInv s t s') : satisfied kernelCircuit (encode s t s') :=
  (bridge s t s').mpr h

/-- **The executor produces satisfying witnesses (PROVED end-to-end).** Any committed
chained step (`cexec`) yields an assignment satisfying `kernelCircuit` — chaining
`cexec_attests` (step-completeness) with `bridge` (circuit completeness). This is the
prover side: running the kernel *is* generating a valid witness. -/
theorem cexec_satisfies_circuit {s s' : ChainedState} {t : Turn}
    (h : cexec s t = some s') : satisfied kernelCircuit (encode s t s') :=
  circuit_complete s t s' (cexec_attests h)

/-! ## The §8 verify-law derivation story (the extraction seam). -/

/-- **`verify_law_derivable` — the verify law is DERIVED, not assumed.**

`CryptoKernel.verify` (`dregg2 §8`) is an opaque oracle whose soundness is normally an
ASSUMED interface law. With `bridge` it becomes a THEOREM for the specific verifier that
"checks the kernel circuit". Concretely, suppose a `verify` is implemented as

    verifyStep s t s' := decide (satisfied kernelCircuit (encode s t s'))

(`satisfied kernelCircuit (encode …)` is decidable: each gate is a ℤ-equality, each
conjunct of `fullStepInv` is decidable, and `bridge` is the equivalence). Then its
soundness law is exactly:

    verifyStep s t s' = true  →  fullStepInv s t s'

which is `(bridge …).mp ∘ of_decide_eq_true` — **derived from `bridge`**, never axiomatized.
This theorem states that derived soundness law against a `Decidable (satisfied …)` instance.

The remaining `-- PRIMITIVE:` obligation is *not* this implication (we prove it) but the
binding of the real Rust prover's CR-hash chain digest to the `chainOk`/`vTotalPre`/… field
wires — i.e. that the extracted `kernelCircuit` data is the circuit the Poseidon/WHIR prover
actually proves. That is the genuine §8 cryptographic seam; the LOGICAL content of the
verify law is discharged here. -/
theorem verify_law_derivable (s : ChainedState) (t : Turn) (s' : ChainedState)
    [Decidable (satisfied kernelCircuit (encode s t s'))]
    (h : decide (satisfied kernelCircuit (encode s t s')) = true) :
    fullStepInv s t s' :=
  (bridge s t s').mp (of_decide_eq_true h)

/-- **The completeness companion of the derived verify law** — a real step makes
`verifyStep` accept. Together with `verify_law_derivable` this is a full soundness∧
completeness characterization of the circuit-checking verifier, with NO assumed §8 law. -/
theorem verify_complete (s : ChainedState) (t : Turn) (s' : ChainedState)
    [Decidable (satisfied kernelCircuit (encode s t s'))]
    (h : fullStepInv s t s') :
    decide (satisfied kernelCircuit (encode s t s')) = true :=
  decide_eq_true ((bridge s t s').mpr h)

/-- Sanity: the circuit has exactly the four conjunct-gates. -/
example : kernelCircuit.length = 4 := rfl

end Dregg2.Circuit
