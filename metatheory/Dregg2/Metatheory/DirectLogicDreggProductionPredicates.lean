/-
# Direct-logic certificates for four additional production predicates

This module extends the application corpus beyond the original admission,
upgrade, clearance, and strand examples.  Each workload below is tied to a
decision that the DREGG runtime or light-client path actually consumes:

* the executable transfer gate, including positional/capability authority;
* the shielded-note proof-and-freshness commit gate;
* the fail-closed interchain trust-rung wire verdict; and
* a bounded four-leaf instance of the recursive proof-of-holdings fold.

`source` records the natural source AST, with shared conjunctions represented
once rather than DNF-expanded to manufacture a benchmark win.
`certifyPublic` runs the checked optimizer and lowers the result to the live
quadratic BoolGraph DescriptorIR2 backend.  Arithmetic, membership, capability
search, proof verification, and equality stay explicit atoms: this module
certifies their Boolean composition and public binding, not their internals.

## Compiler boundary

The reusable front end is `ProductionPredicate Input n`: `Formula n` is the
small typed Boolean AST, `atomBits : Input → Fin n → Bool` is the only atom
interface, and `correct` relates the AST to the typed production decision.
`ProductionPredicate.compile` then supplies one checked optimizer/BoolGraph/
DescriptorIR2 route for every instance.  Its generic `optimized_correct`,
`public_sound`, and `canonical_complete` theorems mean application workloads
only prove the semantic bridge once; they do not re-prove compiler soundness.
Crucially, this front end does **not** pretend that a public atom vector
authenticates the state it describes.  `PublicAtomContract` names the remaining
composition obligation: a context/commitment gadget must force every published
zero residual to equal the corresponding `atomBits` computation.  Once such a
contract is supplied, `public_sound` composes it with compiler soundness.  A
future in-AIR atom gadget discharges that contract; this module does not launder
it into the Boolean compiler.

Standalone and additive: no umbrella import is changed here.
-/

import Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
import Dregg2.Exec.Kernel
import Dregg2.Circuit.Spec.notenullifier
import Dregg2.Bridge.InterchainAdapterDecision
import Dregg2.Bridge.HoldingFoldRecursive

namespace Dregg2.Metatheory.DirectLogicDreggProductionPredicates

open Dregg2.Metatheory.DirectLogicOptimizerCertificate
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
open Dregg2.Circuit.DescriptorIR2 (Satisfied2 VmTrace)

set_option autoImplicit false

abbrev Formula := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula

private def a0 {n : Nat} (h : 0 < n := by omega) : Formula n := .atom ⟨0, h⟩
private def a1 {n : Nat} (h : 1 < n := by omega) : Formula n := .atom ⟨1, h⟩
private def a2 {n : Nat} (h : 2 < n := by omega) : Formula n := .atom ⟨2, h⟩
private def a3 {n : Nat} (h : 3 < n := by omega) : Formula n := .atom ⟨3, h⟩
private def a4 {n : Nat} (h : 4 < n := by omega) : Formula n := .atom ⟨4, h⟩
private def a5 {n : Nat} (h : 5 < n := by omega) : Formula n := .atom ⟨5, h⟩
private def a6 {n : Nat} (h : 6 < n := by omega) : Formula n := .atom ⟨6, h⟩

/-! ## 0. Reusable typed production-predicate front end -/

/-- A typed production predicate at the Boolean atom boundary.  `Formula n` is
the front-end AST; `atomBits` is the sole elaboration interface from a typed
runtime input into its `n` Boolean observations. -/
structure ProductionPredicate (Input : Type) (n : Nat) where
  atomBits : Input → Fin n → Bool
  source : Formula n
  decision : Input → Prop
  correct : ∀ input, Formula.Holds (fun a => atomBits input a = true) source ↔ decision input

namespace ProductionPredicate

def atoms {Input : Type} {n : Nat} (p : ProductionPredicate Input n)
    (input : Input) : Fin n → Prop := fun a => p.atomBits input a = true

/-- The one compiler entry: checked formula optimization followed by the live
public BoolGraph DescriptorIR2 lowering. -/
def compile {Input : Type} {n : Nat} (p : ProductionPredicate Input n) :
    PublicLiveCertificate n := certifyPublic p.source

/-- The explicit boundary between typed production context and the currently
public atom-vector descriptor.  This record is an obligation, not an
authenticator: an integrated context/commitment gadget must construct it. -/
structure PublicAtomContract {Input : Type} {n : Nat}
    (p : ProductionPredicate Input n) (input : Input) (t : VmTrace) : Prop where
  exact : ∀ a, PublicTruth t.pub a ↔ p.atoms input a

theorem optimized_correct {Input : Type} {n : Nat} (p : ProductionPredicate Input n)
    (input : Input) :
    Formula.Holds (p.atoms input) p.compile.optimized ↔ p.decision input := by
  calc
    Formula.Holds (p.atoms input) p.compile.optimized ↔
        Formula.Holds (p.atoms input) p.source := by
          exact (optimize_holds_iff (p.atoms input) p.source).symm
    _ ↔ p.decision input := p.correct input

/-- Generic arbitrary-trace soundness.  The only application obligation is the
atom boundary: each public zero-residual must mean the corresponding typed
`atomBits` observation. -/
theorem public_sound (hash : List Int → Int) {Input : Type} {n : Nat}
    (p : ProductionPredicate Input n) (input : Input) (t : VmTrace)
    (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor p.compile.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (binding : PublicAtomContract p input t) :
    p.decision input := by
  apply (p.correct input).mp
  have hpublic := checked_public_statement_sound hash p.compile
    (by simpa [compile] using checkPublicLive_certify p.source) t hne hsat
  have hsource := (formula_holds_congr (PublicTruth t.pub) (p.atoms input)
    binding.exact p.compile.source).mp hpublic
  exact hsource

/-- Generic constructive completeness on the canonical public trace.  No
application-specific witness construction is needed after `correct`: the
BoolGraph compiler supplies every auxiliary deterministically. -/
theorem canonical_complete (hash : List Int → Int) {Input : Type} {n : Nat}
    (p : ProductionPredicate Input n) (input : Input) (hdecision : p.decision input) :
    Satisfied2 hash (publicDescriptor p.compile.optimized) (fun _ => 0)
      (fun _ => (0, 0)) []
      (publicCanonicalTrace (p.atomBits input) p.compile.optimized) := by
  apply public_canonical_trace_complete
  have hsource : Formula.Holds (p.atoms input) p.source :=
    (p.correct input).mpr hdecision
  have hopt := (optimize_holds_iff (p.atoms input) p.source).mp hsource
  exact hopt

end ProductionPredicate

/-! ## 1. Executable transfer admission, with the authority disjunction exposed

`Exec.exec` commits only if its five resource/liveness gates hold and
`authorizedB` holds.  `authorizedB` is itself the real two-arm decision:
positional self-authority, or a capability search.  The source keeps the common
gates shared, matching the natural AST rather than expanding to DNF.
-/

namespace TransferWorkload

open Dregg2.Authority
open Dregg2.Exec

/-- The capability-search arm of the production `authorizedB` definition. -/
def capAuthorizes (caps : Caps) (turn : Turn) : Bool :=
  (caps turn.actor).any (fun c =>
    (c == Cap.node turn.src) ||
    (match c with
     | .endpoint t rights => (t == turn.src) && rights.contains Auth.write
     | _ => false))

/-- The five transfer gates common to positional and capability authority. -/
def common : Formula 7 :=
  .and (a2) (.and (a3) (.and (a4) (.and (a5) (a6))))

/-- Natural AST for `common && (self || cap)`. -/
def source : Formula 7 :=
  .and common (.or (a0) (a1))

/-- Executable atom elaboration for the live transfer gate. -/
def atomBits (k : KernelState) (turn : Turn) : Fin 7 → Bool
  | ⟨0, _⟩ => turn.actor == turn.src
  | ⟨1, _⟩ => capAuthorizes k.caps turn
  | ⟨2, _⟩ => decide (0 ≤ turn.amt)
  | ⟨3, _⟩ => decide (turn.amt ≤ k.bal turn.src)
  | ⟨4, _⟩ => decide (turn.src ≠ turn.dst)
  | ⟨5, _⟩ => decide (turn.src ∈ k.accounts)
  | ⟨6, _⟩ => decide (turn.dst ∈ k.accounts)
  | ⟨_, _⟩ => false

def truth (k : KernelState) (turn : Turn) : Fin 7 → Prop :=
  fun a => atomBits k turn a = true

theorem source_iff_exec_guard (k : KernelState) (turn : Turn) :
    Formula.Holds (truth k turn) source ↔
      (authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts) := by
  simp only [source, common, a0, a1, a2, a3, a4, a5, a6, truth, atomBits,
    decide_eq_true_eq, Formula.Holds]
  unfold authorizedB capAuthorizes
  simp only [Bool.or_eq_true, beq_iff_eq]
  aesop

/-- All-input equivalence to whether the executable kernel commits the turn. -/
theorem source_iff_exec_commits (k : KernelState) (turn : Turn) :
    Formula.Holds (truth k turn) source ↔ (Dregg2.Exec.exec k turn).isSome = true := by
  rw [source_iff_exec_guard]
  unfold Dregg2.Exec.exec
  by_cases h : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt
      ∧ turn.amt ≤ k.bal turn.src ∧ turn.src ≠ turn.dst
      ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts <;> simp [h]

structure Input where
  state : KernelState
  turn : Turn

def frontend : ProductionPredicate Input 7 where
  atomBits := fun input => atomBits input.state input.turn
  source := source
  decision := fun input => (Dregg2.Exec.exec input.state input.turn).isSome = true
  correct := by
    intro input
    exact source_iff_exec_commits input.state input.turn

def certificate : PublicLiveCertificate 7 := frontend.compile

theorem optimized_iff_exec_commits (k : KernelState) (turn : Turn) :
    Formula.Holds (truth k turn) certificate.optimized ↔
      (Dregg2.Exec.exec k turn).isSome = true := by
  exact frontend.optimized_correct { state := k, turn := turn }

end TransferWorkload

/-! ## 2. Shielded-note commit: proof verification and nullifier freshness

The live `noteSpendA` arm commits exactly when its §8 proof bit is true and
the nullifier is absent from the committed spent set.  This already-minimal
two-conjunct workload is an important negative control: the optimizer must not
invent a saving where none exists.
-/

namespace NoteSpendWorkload

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.NoteNullifier

def source : Formula 2 := .and (a0) (a1)

def atomBits (st : RecChainedState) (nf : Nat) (spendProof : Bool) : Fin 2 → Bool
  | ⟨0, _⟩ => spendProof
  | ⟨1, _⟩ => decide (nf ∉ st.kernel.nullifiers)
  | ⟨_, _⟩ => false

def truth (st : RecChainedState) (nf : Nat) (spendProof : Bool) : Fin 2 → Prop :=
  fun a => atomBits st nf spendProof a = true

theorem source_iff_noteSpendGuard (st : RecChainedState) (nf : Nat)
    (spendProof : Bool) :
    Formula.Holds (truth st nf spendProof) source ↔
      noteSpendGuard st nf spendProof := by
  simp only [source, a0, a1, Formula.Holds]
  simp only [truth, atomBits]
  simp [noteSpendGuard]

/-- Exact all-input equivalence to existence of a committed production note spend. -/
theorem source_iff_noteSpend_commits (st : RecChainedState) (nf actor : Nat)
    (spendProof : Bool) :
    Formula.Holds (truth st nf spendProof) source ↔
      ∃ st', execFullA st (.noteSpendA nf actor spendProof) = some st' := by
  rw [source_iff_noteSpendGuard]
  exact (execFullA_noteSpend_commits_iff st nf actor spendProof).symm

structure Input where
  state : RecChainedState
  nullifier : Nat
  actor : Nat
  spendProof : Bool

def frontend : ProductionPredicate Input 2 where
  atomBits := fun input => atomBits input.state input.nullifier input.spendProof
  source := source
  decision := fun input => ∃ st', execFullA input.state
    (.noteSpendA input.nullifier input.actor input.spendProof) = some st'
  correct := by
    intro input
    exact source_iff_noteSpend_commits input.state input.nullifier input.actor input.spendProof

def certificate : PublicLiveCertificate 2 := frontend.compile

theorem optimized_iff_noteSpend_commits (st : RecChainedState) (nf actor : Nat)
    (spendProof : Bool) :
    Formula.Holds (truth st nf spendProof) certificate.optimized ↔
      ∃ st', execFullA st (.noteSpendA nf actor spendProof) = some st' := by
  exact frontend.optimized_correct
      { state := st, nullifier := nf, actor := actor, spendProof := spendProof }

end NoteSpendWorkload

/-! ## 3. Interchain trust-rung wire verdict

The exported bridge decision admits `tag = 0` (verified proof) or a nonzero
payload at `tag = 1/2` (resolved-valid watchtower / quorum committee).  Unknown
and RPC tags fail closed.  The source is already the factored natural AST.
-/

namespace InterchainWorkload

open Dregg2.Bridge.InterchainAdapterDecision

def source : Formula 4 :=
  .or (a0) (.and (a3) (.or (a1) (a2)))

def atomBits (tag payload : Int) : Fin 4 → Bool
  | ⟨0, _⟩ => tag == 0
  | ⟨1, _⟩ => tag == 1
  | ⟨2, _⟩ => tag == 2
  | ⟨3, _⟩ => payload != 0
  | ⟨_, _⟩ => false

def truth (tag payload : Int) : Fin 4 → Prop :=
  fun a => atomBits tag payload a = true

/-- Exact all-wire equivalence, including the unknown-tag fail-closed case. -/
theorem source_iff_reachedConsensusWire (tag payload : Int) :
    Formula.Holds (truth tag payload) source ↔
      reachedConsensusWire tag payload = true := by
  simp only [source, a0, a1, a2, a3, truth, atomBits, beq_iff_eq, Formula.Holds]
  unfold reachedConsensusWire
  by_cases h0 : tag = 0
  · subst h0; simp
  · rw [if_neg (by simpa using h0)]
    by_cases h1 : tag = 1
    · subst h1; simp
    · rw [if_neg (by simpa using h1)]
      by_cases h2 : tag = 2
      · subst h2; simp
      · rw [if_neg (by simpa using h2)]
        simp [h0, h1, h2]

structure Input where
  tag : Int
  payload : Int

def frontend : ProductionPredicate Input 4 where
  atomBits := fun input => atomBits input.tag input.payload
  source := source
  decision := fun input => reachedConsensusWire input.tag input.payload = true
  correct := by
    intro input
    exact source_iff_reachedConsensusWire input.tag input.payload

def certificate : PublicLiveCertificate 4 := frontend.compile

theorem optimized_iff_reachedConsensusWire (tag payload : Int) :
    Formula.Holds (truth tag payload) certificate.optimized ↔
      reachedConsensusWire tag payload = true := by
  exact frontend.optimized_correct { tag := tag, payload := payload }

end InterchainWorkload

/-! ## 4. Four-leaf recursive proof-of-holdings acceptance

This is a bounded production-shaped slice of `foldAccept`, the recursive light
client's conjunction of per-step verifier results.  A fixed four-leaf slice is
enough to put the fold through the public DescriptorIR2 path while preserving
the actual `StepVerifier.accept` atoms.  It is also an already-normal negative
control: reassociation alone is not reported as an optimization.
-/

namespace HoldingFoldWorkload

open Dregg2.Bridge.ProofOfHoldingsGeneric
open Dregg2.Bridge.HoldingFoldRecursive

def source : Formula 4 := .and (a0) (.and (a1) (.and (a2) (a3)))

def atomBits {C : ChainParams} (sv : StepVerifier C)
    (h0 h1 h2 h3 : GHolding C) : Fin 4 → Bool
  | ⟨0, _⟩ => sv.accept h0
  | ⟨1, _⟩ => sv.accept h1
  | ⟨2, _⟩ => sv.accept h2
  | ⟨3, _⟩ => sv.accept h3
  | ⟨_, _⟩ => false

def truth {C : ChainParams} (sv : StepVerifier C)
    (h0 h1 h2 h3 : GHolding C) : Fin 4 → Prop :=
  fun a => atomBits sv h0 h1 h2 h3 a = true

theorem source_iff_foldAccept {C : ChainParams} (sv : StepVerifier C)
    (h0 h1 h2 h3 : GHolding C) :
    Formula.Holds (truth sv h0 h1 h2 h3) source ↔
      foldAccept C sv [h0, h1, h2, h3] = true := by
  simp only [source, a0, a1, a2, a3, Formula.Holds]
  simp only [truth, atomBits]
  simp [foldAccept]
  aesop

structure Input (C : ChainParams) where
  h0 : GHolding C
  h1 : GHolding C
  h2 : GHolding C
  h3 : GHolding C

def frontend {C : ChainParams} (sv : StepVerifier C) : ProductionPredicate (Input C) 4 where
  atomBits := fun input => atomBits sv input.h0 input.h1 input.h2 input.h3
  source := source
  decision := fun input => foldAccept C sv [input.h0, input.h1, input.h2, input.h3] = true
  correct := by
    intro input
    exact source_iff_foldAccept sv input.h0 input.h1 input.h2 input.h3

/-- The compiled descriptor is verifier-independent: `sv` elaborates atom
values, while the four-input Boolean shape is shared by every chain. -/
def certificate : PublicLiveCertificate 4 := certifyPublic source

theorem optimized_iff_foldAccept {C : ChainParams} (sv : StepVerifier C)
    (h0 h1 h2 h3 : GHolding C) :
    Formula.Holds (truth sv h0 h1 h2 h3) certificate.optimized ↔
      foldAccept C sv [h0, h1, h2, h3] = true := by
  exact (frontend sv).optimized_correct { h0 := h0, h1 := h1, h2 := h2, h3 := h3 }

end HoldingFoldWorkload

/-! ## 5. Arbitrary-trace public-descriptor soundness

Every residual input is bound to a public input by the generic live lowering,
but that public vector is not by itself authenticated to a production context.
Each theorem therefore requires the typed `PublicAtomContract`; under exactly
that obligation, an arbitrary nonempty satisfying trace proves the named
production decision.  No canonical-witness assumption appears.
-/

namespace TransferWorkload

theorem public_descriptor_sound (hash : List Int → Int)
    (k : Dregg2.Exec.KernelState) (turn : Dregg2.Exec.Turn)
    (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor certificate.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (binding : ProductionPredicate.PublicAtomContract frontend ⟨k, turn⟩ t) :
    (Dregg2.Exec.exec k turn).isSome = true := by
  apply ProductionPredicate.public_sound hash frontend
    { state := k, turn := turn } t hne
  · simpa [certificate] using hsat
  · exact binding

end TransferWorkload

namespace NoteSpendWorkload

theorem public_descriptor_sound (hash : List Int → Int)
    (st : Dregg2.Exec.RecChainedState) (nf actor : Nat) (spendProof : Bool)
    (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor certificate.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (binding : ProductionPredicate.PublicAtomContract frontend
      ⟨st, nf, actor, spendProof⟩ t) :
    ∃ st', Dregg2.Exec.TurnExecutorFull.execFullA st
      (.noteSpendA nf actor spendProof) = some st' := by
  apply ProductionPredicate.public_sound hash frontend
    { state := st, nullifier := nf, actor := actor, spendProof := spendProof } t hne
  · simpa [certificate] using hsat
  · exact binding

end NoteSpendWorkload

namespace InterchainWorkload

theorem public_descriptor_sound (hash : List Int → Int) (tag payload : Int)
    (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor certificate.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (binding : ProductionPredicate.PublicAtomContract frontend ⟨tag, payload⟩ t) :
    Dregg2.Bridge.InterchainAdapterDecision.reachedConsensusWire tag payload = true := by
  apply ProductionPredicate.public_sound hash frontend
    { tag := tag, payload := payload } t hne
  · simpa [certificate] using hsat
  · exact binding

end InterchainWorkload

namespace HoldingFoldWorkload

open Dregg2.Bridge.ProofOfHoldingsGeneric
open Dregg2.Bridge.HoldingFoldRecursive

theorem public_descriptor_sound (hash : List Int → Int) {C : ChainParams}
    (sv : StepVerifier C) (h0 h1 h2 h3 : GHolding C)
    (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor certificate.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (binding : ProductionPredicate.PublicAtomContract (frontend sv)
      ⟨h0, h1, h2, h3⟩ t) :
    foldAccept C sv [h0, h1, h2, h3] = true := by
  apply ProductionPredicate.public_sound hash (frontend sv)
    { h0 := h0, h1 := h1, h2 := h2, h3 := h3 } t hne
  · exact hsat
  · exact binding

end HoldingFoldWorkload

/-! ## 6. Exact natural-AST DescriptorIR2 ledgers

All four production ASTs are already factored naturally, so the optimizer
honestly reports no structural saving.  These are nevertheless useful absolute
costs for the live atom-vector backend.  Counts include `n` public bindings and
the final linear acceptance equation; multiplication and auxiliary counts are
the materialized quadratic BoolGraph costs. -/

theorem transfer_exact_live_ledger :
    (graphConstraints TransferWorkload.source).length = 33 ∧
    (graphConstraints TransferWorkload.certificate.optimized).length = 33 ∧
    (publicDescriptor TransferWorkload.source).constraints.length = 41 ∧
    (publicDescriptor TransferWorkload.certificate.optimized).constraints.length = 41 ∧
    (publicDescriptor TransferWorkload.certificate.optimized).piCount = 7 ∧
    emittedMultiplications TransferWorkload.source = 33 ∧
    emittedMultiplications TransferWorkload.certificate.optimized = 33 ∧
    (publicDescriptor TransferWorkload.source).traceWidth - 7 = 20 ∧
    (publicDescriptor TransferWorkload.certificate.optimized).traceWidth - 7 = 20 ∧
    (publicDescriptor TransferWorkload.source).traceWidth = 27 ∧
    (publicDescriptor TransferWorkload.certificate.optimized).traceWidth = 27 := by
  decide

theorem transfer_natural_ast_unchanged :
    TransferWorkload.certificate.optimized = TransferWorkload.source := by
  decide

theorem noteSpend_exact_live_ledger :
    (graphConstraints NoteSpendWorkload.source).length = 8 ∧
    (graphConstraints NoteSpendWorkload.certificate.optimized).length = 8 ∧
    (publicDescriptor NoteSpendWorkload.source).constraints.length = 11 ∧
    (publicDescriptor NoteSpendWorkload.certificate.optimized).constraints.length = 11 ∧
    (publicDescriptor NoteSpendWorkload.certificate.optimized).piCount = 2 ∧
    emittedMultiplications NoteSpendWorkload.source = 8 ∧
    emittedMultiplications NoteSpendWorkload.certificate.optimized = 8 ∧
    (publicDescriptor NoteSpendWorkload.source).traceWidth - 2 = 5 ∧
    (publicDescriptor NoteSpendWorkload.certificate.optimized).traceWidth - 2 = 5 ∧
    (publicDescriptor NoteSpendWorkload.source).traceWidth = 7 ∧
    (publicDescriptor NoteSpendWorkload.certificate.optimized).traceWidth = 7 := by
  decide

theorem noteSpend_natural_ast_unchanged :
    NoteSpendWorkload.certificate.optimized = NoteSpendWorkload.source := by
  decide

theorem interchain_exact_live_ledger :
    (graphConstraints InterchainWorkload.source).length = 18 ∧
    (graphConstraints InterchainWorkload.certificate.optimized).length = 18 ∧
    (publicDescriptor InterchainWorkload.source).constraints.length = 23 ∧
    (publicDescriptor InterchainWorkload.certificate.optimized).constraints.length = 23 ∧
    (publicDescriptor InterchainWorkload.certificate.optimized).piCount = 4 ∧
    emittedMultiplications InterchainWorkload.source = 18 ∧
    emittedMultiplications InterchainWorkload.certificate.optimized = 18 ∧
    (publicDescriptor InterchainWorkload.source).traceWidth - 4 = 11 ∧
    (publicDescriptor InterchainWorkload.certificate.optimized).traceWidth - 4 = 11 ∧
    (publicDescriptor InterchainWorkload.source).traceWidth = 15 ∧
    (publicDescriptor InterchainWorkload.certificate.optimized).traceWidth = 15 := by
  decide

theorem interchain_natural_ast_unchanged :
    InterchainWorkload.certificate.optimized = InterchainWorkload.source := by
  decide

theorem holdingFold_exact_live_ledger :
    (graphConstraints HoldingFoldWorkload.source).length = 18 ∧
    (graphConstraints HoldingFoldWorkload.certificate.optimized).length = 18 ∧
    (publicDescriptor HoldingFoldWorkload.source).constraints.length = 23 ∧
    (publicDescriptor HoldingFoldWorkload.certificate.optimized).constraints.length = 23 ∧
    (publicDescriptor HoldingFoldWorkload.certificate.optimized).piCount = 4 ∧
    emittedMultiplications HoldingFoldWorkload.source = 18 ∧
    emittedMultiplications HoldingFoldWorkload.certificate.optimized = 18 ∧
    (publicDescriptor HoldingFoldWorkload.source).traceWidth - 4 = 11 ∧
    (publicDescriptor HoldingFoldWorkload.certificate.optimized).traceWidth - 4 = 11 ∧
    (publicDescriptor HoldingFoldWorkload.source).traceWidth = 15 ∧
    (publicDescriptor HoldingFoldWorkload.certificate.optimized).traceWidth = 15 := by
  decide

theorem holdingFold_natural_ast_unchanged :
    HoldingFoldWorkload.certificate.optimized = HoldingFoldWorkload.source := by
  decide

/-! ## 7. Checker and hygiene gates -/

#guard checkPublicLive TransferWorkload.certificate
#guard checkPublicLive NoteSpendWorkload.certificate
#guard checkPublicLive InterchainWorkload.certificate
#guard checkPublicLive HoldingFoldWorkload.certificate

#assert_axioms TransferWorkload.source_iff_exec_commits
#assert_axioms TransferWorkload.public_descriptor_sound
#assert_axioms NoteSpendWorkload.source_iff_noteSpend_commits
#assert_axioms NoteSpendWorkload.public_descriptor_sound
#assert_axioms InterchainWorkload.source_iff_reachedConsensusWire
#assert_axioms InterchainWorkload.public_descriptor_sound
#assert_axioms HoldingFoldWorkload.source_iff_foldAccept
#assert_axioms HoldingFoldWorkload.public_descriptor_sound
#assert_axioms ProductionPredicate.optimized_correct
#assert_axioms ProductionPredicate.public_sound
#assert_axioms ProductionPredicate.canonical_complete

end Dregg2.Metatheory.DirectLogicDreggProductionPredicates
