/-
  Pancake/LadderPanSem.lean — the orb ladder, stated against CakeML's own panSem.

  The rungs of "datacake down to the bytes" that live in Lean are restated here
  about `P3.Pan.evaluate`: the HOL4 definition `panSem$evaluate` (CakeML
  ed31510b3, 'a := 64), exported mechanically into `PanSem/` by DreggNet's
  p3-bridge exporter and re-checked there (constructors, every exported HOL
  defining equation re-proved in Lean, vectors computed in both kernels). The
  statements below mention only the export's `evaluate`, its state, and the
  syntactic embedding `liftProg` of the orb compiler's output into panLang.
  Sem.lean appears only inside proofs.

  How the proofs go. Every rung was first proved about Sem.lean's `PancakeSem`
  (ProofProducing, ServeExportServes, unchanged). `PanSemAgree.evaluate_agree`
  carries a Sem.lean run to the panSem run of the same program, provided the
  program is SCOPED (every `assign` writes a local that is already bound). So
  Sem.lean is retained as a proved layer, not as the semantics: the orb compiler's
  ~20k lines of emit-correctness proofs stay where they are, and this file is
  the only place where the ladder meets the semantics the HOL4 compiler theorem
  is about. Re-proving those files directly against the export would duplicate
  them without changing what is trusted.

  What the restatement adds to the orb's contract:
   * `WordLocals hs`: every local visible to the program holds a word (panSem
     locals may hold structs; the orb's programs only ever see words).
   * `BoundPan Γ hs`: the locals the stage assigns are bound on entry. panSem's
     `Assign` returns `Error` on an unbound local (`is_valid_value`), which
     Sem.lean silently continues past (`sem_lean_assign_unscoped_disagrees`).
     For a `Stage` this is a real precondition: a stage that assigns `result`
     runs on panSem only from a state where `result` is already declared.
   * The scoping side condition `Scoped Γ p` on the emitted program, discharged
     by the decision procedure `scopedB` for concrete programs.

  AXIOMS: every theorem ⊆ {propext, Classical.choice, Quot.sound} (§6).
-/
import Pancake.PanSemAgree
import Pancake.ProofProducing
import Pancake.ServeExportServes

set_option autoImplicit false
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

namespace Pancake.LadderPanSem

open P3.Pan P3.Agree
open Pancake.EmitCorrectCompose (Refines Stage WF emit denote)
open Pancake.EmitCorrectClock (RefinesClk)
open Pancake.ProofProducing (emitServe emitServe_correct closedDemo)

variable {θ : Type}

/-! ## 1. panSem states the orb's programs run in -/

/-- Every local the orb's programs can name holds a word. -/
def WordLocals (hs : state θ) : Prop :=
  ∀ k x, hs.locals (nm k) = some x → ∃ w, x = VW w

/-- The locals in `Γ` are bound to words on entry. -/
def BoundPan (Γ : List String) (hs : state θ) : Prop :=
  ∀ k ∈ Γ, ∃ w, hs.locals (nm k) = some (VW w)

/-- The Sem.lean view of a panSem state (the abstraction function). -/
noncomputable def ofPan (hs : state θ) : Pancake.PancakeState (ffi_state θ) where
  locals k := match hs.locals (nm k) with
    | some (.Val (.Word w)) => some w
    | _ => none
  memory a := match hs.memory a with
    | .Word w => w
  memaddrs a := decide (hs.memaddrs a)
  be := decide hs.be
  clock := hs.clock
  ffi := hs.ffi
  baseAddr := hs.base_addr

theorem SR_ofPan {hs : state θ} (hw : WordLocals hs) : SR (ofPan hs) hs where
  locals k := by
    simp only [ofPan]
    cases h : hs.locals (nm k) with
    | none => rfl
    | some x =>
      obtain ⟨w, rfl⟩ := hw k x h
      rfl
  memory := by
    funext a; simp only [ofPan]
  memaddrs := by funext a; simp [ofPan]
  be := by simp [ofPan]
  clock := rfl
  ffi := rfl
  base := rfl

/-- `SR` pins the Sem.lean state: it is `ofPan` of the panSem state. -/
theorem SR_eq_ofPan {ss : Pancake.PancakeState (ffi_state θ)} {hs : state θ}
    (h : SR ss hs) : ss = ofPan hs := by
  obtain ⟨l, m, ma, b, c, f, ba⟩ := ss
  have hl := h.locals; have hm := h.memory; have hma := h.memaddrs
  have hb := h.be; have hc := h.clock; have hf := h.ffi; have hba := h.base
  simp only [ofPan, hm, hma, hb, hc, hf, hba, Bool.decide_eq_true]
  congr
  funext k
  rw [hl k]; dsimp only; cases l k <;> rfl

theorem bound_ofPan {Γ : List String} {hs : state θ} (hb : BoundPan Γ hs) :
    Bound Γ (ofPan hs) := by
  intro k hk
  obtain ⟨w, hw⟩ := hb k hk
  simp [ofPan, hw, VW]

theorem wordLocals_of_SR {ss : Pancake.PancakeState (ffi_state θ)} {hs : state θ}
    (h : SR ss hs) : WordLocals hs := by
  intro k x hx
  rw [h.locals k] at hx
  cases hk : ss.locals k with
  | none => simp [hk] at hx
  | some w => simp [hk] at hx; exact ⟨w, hx.symm⟩

/-! ## 2. Scoping, decided -/

/-- A decision procedure for `Scoped`. -/
def scopedB : List String → Pancake.PancakeProg → Bool
  | _, .skip => true
  | Γ, .dec v _ c => scopedB (v :: Γ) c
  | Γ, .assign v _ => Γ.contains v
  | _, .store _ _ => true
  | _, .extCall _ _ _ _ _ => true
  | Γ, .seq a b => scopedB Γ a && scopedB Γ b
  | Γ, .cond _ a b => scopedB Γ a && scopedB Γ b
  | Γ, .while_ _ c => scopedB Γ c
  | _, .ret _ => true
  | _, .storeByte _ _ => true

theorem scoped_of_scopedB : ∀ (Γ : List String) (p : Pancake.PancakeProg),
    scopedB Γ p = true → Scoped Γ p
  | _, .skip, _ => trivial
  | Γ, .dec v _ c, h => scoped_of_scopedB (v :: Γ) c h
  | Γ, .assign v _, h => by simpa [scopedB, Scoped] using h
  | _, .store _ _, _ => trivial
  | _, .extCall _ _ _ _ _, _ => trivial
  | Γ, .seq a b, h => by
      simp only [scopedB, Bool.and_eq_true] at h
      exact ⟨scoped_of_scopedB Γ a h.1, scoped_of_scopedB Γ b h.2⟩
  | Γ, .cond _ a b, h => by
      simp only [scopedB, Bool.and_eq_true] at h
      exact ⟨scoped_of_scopedB Γ a h.1, scoped_of_scopedB Γ b h.2⟩
  | Γ, .while_ _ c, h => scoped_of_scopedB Γ c h
  | _, .ret _, _ => trivial
  | _, .storeByte _ _, _ => trivial

/-! ## 3. Rung [2]: the proof-producing translator, against panSem

`Refines o p φ` (EmitCorrectCompose) says the Sem.lean run of `p` terminates
normally in `φ s` with the clock unchanged. `RefinesPan Γ p φ` says the same of
the EXPORTED panSem `evaluate` on `liftProg p`, from every panSem state with
word locals and `Γ` bound. -/

/-- The exported panSem `evaluate` of `liftProg p` terminates normally (`NONE`)
from every panSem state with word locals and `Γ` bound, in a state whose
Sem.lean view is `φ` of the entry's, with the same clock. -/
def RefinesPan (Γ : List String) (p : Pancake.PancakeProg)
    (φ : Pancake.PancakeState (ffi_state θ) → Pancake.PancakeState (ffi_state θ)) : Prop :=
  ∀ hs : state θ, WordLocals hs → BoundPan Γ hs →
    (evaluate (liftProg p, hs)).1 = none ∧
    SR (φ (ofPan hs)) (evaluate (liftProg p, hs)).2 ∧
    (evaluate (liftProg p, hs)).2.clock = hs.clock

/-- **The bridge for rung [2].** A Sem.lean refinement of a scoped program is a
refinement on the exported panSem. -/
theorem refinesPan_of_refines (ev : final_event → Pancake.FinalEvent)
    {Γ : List String} {p : Pancake.PancakeProg}
    {φ : Pancake.PancakeState (ffi_state θ) → Pancake.PancakeState (ffi_state θ)}
    (h : Refines (oracleOf ev) p φ) (hsc : Scoped Γ p) : RefinesPan Γ p φ := by
  intro hs hw hb
  have hSR := SR_ofPan hw
  obtain ⟨hrun, hclk⟩ := h (ofPan hs)
  obtain ⟨hr, hsr, _⟩ := evaluate_agree ev (ofPan hs).clock p Γ (ofPan hs) hs
    (Nat.le_refl _) hsc (bound_ofPan hb) hSR
  rw [hrun] at hr hsr
  refine ⟨(RR_none hr).2 rfl, hsr, ?_⟩
  rw [hsr.clock]; exact hclk

/-- **`translateCert`, on panSem.** For every well-formed stage whose emitted
program is scoped by `Γ`, the emitted program, run by CakeML's own `evaluate`,
refines the stage's denotation. (The certificate the orb's compiler produces
is now a statement about the HOL4 semantics' Lean export.) -/
def translateCertPan (ev : final_event → Pancake.FinalEvent) (Γ : List String)
    (st : Stage (ffi_state θ)) (h : WF (oracleOf ev) st) (hsc : Scoped Γ (emitServe st)) :
    { p : Pancake.PancakeProg // RefinesPan Γ p (denote st) } :=
  ⟨emitServe st, refinesPan_of_refines ev (emitServe_correct _ st h) hsc⟩

/-- Loop-bearing stages (`RefinesClk`, clock consumed, with a precondition),
against panSem. -/
def RefinesClkPan (Γ : List String) (p : Pancake.PancakeProg)
    (P : Pancake.PancakeState (ffi_state θ) → Prop)
    (Q : Pancake.PancakeState (ffi_state θ) → Pancake.PancakeState (ffi_state θ) → Prop) : Prop :=
  ∀ hs : state θ, WordLocals hs → BoundPan Γ hs → P (ofPan hs) →
    (evaluate (liftProg p, hs)).1 = none ∧
    WordLocals (evaluate (liftProg p, hs)).2 ∧
    Q (ofPan hs) (ofPan (evaluate (liftProg p, hs)).2) ∧
    (evaluate (liftProg p, hs)).2.clock ≤ hs.clock

theorem refinesClkPan_of_refinesClk (ev : final_event → Pancake.FinalEvent)
    {Γ : List String} {p : Pancake.PancakeProg}
    {P : Pancake.PancakeState (ffi_state θ) → Prop}
    {Q : Pancake.PancakeState (ffi_state θ) → Pancake.PancakeState (ffi_state θ) → Prop}
    (h : RefinesClk (oracleOf ev) p P Q) (hsc : Scoped Γ p) : RefinesClkPan Γ p P Q := by
  intro hs hw hb hP
  have hSR := SR_ofPan hw
  obtain ⟨s', hrun, hQ, hclk⟩ := h (ofPan hs) hP
  obtain ⟨hr, hsr, _⟩ := evaluate_agree ev (ofPan hs).clock p Γ (ofPan hs) hs
    (Nat.le_refl _) hsc (bound_ofPan hb) hSR
  rw [hrun] at hr hsr
  refine ⟨(RR_none hr).2 rfl, wordLocals_of_SR hsr, ?_, ?_⟩
  · rw [← SR_eq_ofPan hsr]; exact hQ
  · rw [hsr.clock]; exact hclk

/-! ### Instances: the translator's demos, on panSem -/

/-- DEMO A (`closedDemo`: `if 0 < 1 then a := 42 else a := 99; b := 7`),
compiled by the translator, run by panSem's `evaluate`: from any state with
`a` and `b` declared it terminates normally with `b ↦ 7` and `a ↦ 42`. -/
theorem closedDemo_panSem (hs : state θ) (hw : WordLocals hs) (hb : BoundPan ["a", "b"] hs) :
    (evaluate (liftProg (emitServe (closedDemo (σ := ffi_state θ))), hs)).1 = none ∧
    (evaluate (liftProg (emitServe (closedDemo (σ := ffi_state θ))), hs)).2.locals (nm "a") =
      some (VW 42) ∧
    (evaluate (liftProg (emitServe (closedDemo (σ := ffi_state θ))), hs)).2.locals (nm "b") =
      some (VW 7) := by
  let ev : final_event → Pancake.FinalEvent := fun _ => ⟨""⟩
  have hsc : Scoped ["a", "b"] (emitServe (closedDemo (σ := ffi_state θ))) :=
    scoped_of_scopedB _ _ rfl
  have hp : RefinesPan ["a", "b"] (emitServe (closedDemo (σ := ffi_state θ)))
      (denote closedDemo) :=
    (translateCertPan ev ["a", "b"] closedDemo (Pancake.ProofProducing.closedDemo_wf _) hsc).2
  obtain ⟨h1, h2, _⟩ := hp hs hw hb
  refine ⟨h1, ?_, ?_⟩
  · rw [h2.locals "a"]
    simp [denote, closedDemo, Pancake.ProofProducing.assignPrim, Pancake.setLocal, VW]
  · rw [h2.locals "b"]
    simp [denote, closedDemo, Pancake.ProofProducing.assignPrim, Pancake.setLocal, VW]

/-! ## 4. Rung [3]: the emitted serve, against panSem

`serveExport_serves_get` / `_405` (ServeExportServes) are about the Sem.lean
run of `serveModel`, the program `lower (serveExport …)` returns. Here they are
about `evaluate (liftProg (serveModel …), hs)`, with every hypothesis on the
panSem state `hs` and the response bytes read back with panSem's own
`mem_load_byte`. -/

/-- The common transfer: a Sem.lean serve run that returns `r` and lands `bs`
at `outBase` is a panSem run that returns `r` and lands `bs` at `outBase`. -/
theorem serve_transfer (ev : final_event → Pancake.FinalEvent) (P : Pancake.PancakeProg)
    (hsc : Scoped [] P) (hs : state θ) (hw : WordLocals hs) (r : Pancake.Word)
    (outBase : Pancake.Word) (bs : List Nat)
    (h : ∃ s', Pancake.PancakeSem (oracleOf ev) P (ofPan hs) = (some (.return_ r), s') ∧
      LowerBridgeSem.MemBytesAtB s'.memory (ofPan hs).memaddrs (ofPan hs).be outBase bs) :
    (evaluate (liftProg P, hs)).1 = some (.Return (VW r)) ∧
      ∀ i, i < bs.length →
        mem_load_byte (evaluate (liftProg P, hs)).2.memory hs.memaddrs hs.be
            (outBase + BitVec.ofNat 64 i)
          = some ((BitVec.ofNat 64 bs[i]!).setWidth 8) := by
  obtain ⟨s', hsem, hmb⟩ := h
  have hSR := SR_ofPan hw
  obtain ⟨hr, hsr, _⟩ := evaluate_agree ev (ofPan hs).clock P [] (ofPan hs) hs
    (Nat.le_refl _) hsc (fun _ hk => by simp at hk) hSR
  rw [hsem] at hr hsr
  refine ⟨?_, fun i hi => ?_⟩
  · generalize (evaluate (liftProg P, hs)).1 = q at hr
    rcases q with _ | ⟨_ | _ | _ | _ | ⟨⟨⟨w0⟩⟩ | _ | _⟩ | _ | _⟩ <;> simp_all [RR]
  · rw [hsr.memory, hSR.memaddrs, hSR.be]
    exact (mem_load_byte_agree s'.memory (ofPan hs).memaddrs (ofPan hs).be _).trans (hmb i hi)

/-- The serve's input hypotheses, read on the panSem state, give the Sem.lean ones. -/
theorem serve_inputs {hs : state θ} (hw : WordLocals hs) {outBase reqAddr : Pancake.Word}
    {b : BitVec 8} {n : Nat}
    (hout : hs.locals (nm "out") = some (VW outBase))
    (hreq : hs.locals (nm "req") = some (VW reqAddr))
    (hbyte : mem_load_byte hs.memory hs.memaddrs hs.be reqAddr = some b)
    (haddr : ∀ i, i < n → hs.memaddrs (byte_align (outBase + BitVec.ofNat 64 i))) :
    (ofPan hs).locals "out" = some outBase ∧ (ofPan hs).locals "req" = some reqAddr ∧
    Pancake.memLoadByte (ofPan hs).memory (ofPan hs).memaddrs (ofPan hs).be reqAddr = some b ∧
    (∀ i, i < n → (ofPan hs).memaddrs (Pancake.byteAlign (outBase + BitVec.ofNat 64 i)) = true) := by
  have hSR := SR_ofPan hw
  refine ⟨by simp [ofPan, hout, VW], by simp [ofPan, hreq, VW], ?_, fun i hi => ?_⟩
  · rw [← mem_load_byte_agree, ← hSR.memory, ← hSR.memaddrs, ← hSR.be]; exact hbyte
  · have := haddr i hi
    rw [byte_align_agree] at this
    simpa [ofPan] using this

theorem storeAssignModel_scoped (Γ : List String) (dst cnt : String) (k : Nat)
    (h : cnt ∈ Γ) : ∀ ps, Scoped Γ (ServeExportServes.storeAssignModel dst cnt k ps)
  | [] => by simpa [ServeExportServes.storeAssignModel, Scoped] using h
  | _ :: ps => by
    simp only [ServeExportServes.storeAssignModel, Scoped, true_and]
    exact storeAssignModel_scoped Γ dst cnt k h ps

/-- The serve program is scoped from the empty context: every `assign` it makes
targets a local its own `dec`s bound (`method`, `count`). -/
theorem serveModel_scoped' (bs200 bs405 : List Nat) :
    Scoped [] (ServeExportServes.serveModel bs200 bs405) := by
  simp [ServeExportServes.serveModel, ServeExportServes.decodeModel, Scoped,
    storeAssignModel_scoped]

/-- **`serveExport_serves_get`, on panSem.** For a GET request (first byte `'G'`),
CakeML's `evaluate` of the lowered emitted serve returns `ValWord |bs200|`, and the
200 response is in memory at `out`, byte for byte, read with panSem's
`mem_load_byte`. -/
theorem serveExport_serves_get_panSem (hs : state θ) (hw : WordLocals hs)
    (bs200 bs405 : List Nat) (outBase reqAddr : Pancake.Word)
    (hout : hs.locals (nm "out") = some (VW outBase))
    (hreq : hs.locals (nm "req") = some (VW reqAddr))
    (hget : mem_load_byte hs.memory hs.memaddrs hs.be reqAddr = some (71 : BitVec 8))
    (haddr : ∀ i, i < bs200.length → hs.memaddrs (byte_align (outBase + BitVec.ofNat 64 i)))
    (hinj : ∀ i j, i < bs200.length → j < bs200.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    (evaluate (liftProg (ServeExportServes.serveModel bs200 bs405), hs)).1 =
        some (.Return (VW (BitVec.ofNat 64 bs200.length))) ∧
      ∀ i, i < bs200.length →
        mem_load_byte (evaluate (liftProg (ServeExportServes.serveModel bs200 bs405), hs)).2.memory
            hs.memaddrs hs.be (outBase + BitVec.ofNat 64 i)
          = some ((BitVec.ofNat 64 bs200[i]!).setWidth 8) := by
  let ev : final_event → Pancake.FinalEvent := fun _ => ⟨""⟩
  obtain ⟨ho, hr, hb, ha⟩ := serve_inputs (n := bs200.length) hw hout hreq hget haddr
  exact serve_transfer ev _ (serveModel_scoped' bs200 bs405) hs hw _ outBase bs200
    (ServeExportServes.serveExport_serves_get (oracleOf ev) (ofPan hs) bs200 bs405 outBase reqAddr
      ho hr hb ha hinj)

/-- **`serveExport_serves_405`, on panSem.** For a request whose method byte is
`'X'`, CakeML's `evaluate` of the lowered emitted serve returns `ValWord |bs405|`
and the 405 response is in memory at `out`. -/
theorem serveExport_serves_405_panSem (hs : state θ) (hw : WordLocals hs)
    (bs200 bs405 : List Nat) (outBase reqAddr : Pancake.Word)
    (hout : hs.locals (nm "out") = some (VW outBase))
    (hreq : hs.locals (nm "req") = some (VW reqAddr))
    (hbyte : mem_load_byte hs.memory hs.memaddrs hs.be reqAddr = some (88 : BitVec 8))
    (haddr : ∀ i, i < bs405.length → hs.memaddrs (byte_align (outBase + BitVec.ofNat 64 i)))
    (hinj : ∀ i j, i < bs405.length → j < bs405.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    (evaluate (liftProg (ServeExportServes.serveModel bs200 bs405), hs)).1 =
        some (.Return (VW (BitVec.ofNat 64 bs405.length))) ∧
      ∀ i, i < bs405.length →
        mem_load_byte (evaluate (liftProg (ServeExportServes.serveModel bs200 bs405), hs)).2.memory
            hs.memaddrs hs.be (outBase + BitVec.ofNat 64 i)
          = some ((BitVec.ofNat 64 bs405[i]!).setWidth 8) := by
  let ev : final_event → Pancake.FinalEvent := fun _ => ⟨""⟩
  obtain ⟨ho, hr, hb, ha⟩ := serve_inputs (n := bs405.length) hw hout hreq hbyte haddr
  exact serve_transfer ev _ (serveModel_scoped' bs200 bs405) hs hw _ outBase bs405
    (ServeExportServes.serveExport_serves_405 (oracleOf ev) (ofPan hs) bs200 bs405 outBase reqAddr
      ho hr hb ha hinj)

/-- **REAL, GET → 200, on panSem.** The emitted serve (`serveExport BS200 BS405`, the
PFun printed to `serve_slice_export.pnk`) lowers to `P`, and CakeML's `evaluate` of
`P` on a GET returns `|serialize resp200|` with `serialize resp200` in memory. -/
theorem serveExport_serves_get_real_panSem (hs : state θ) (hw : WordLocals hs)
    (outBase reqAddr : Pancake.Word)
    (hout : hs.locals (nm "out") = some (VW outBase))
    (hreq : hs.locals (nm "req") = some (VW reqAddr))
    (hget : mem_load_byte hs.memory hs.memaddrs hs.be reqAddr = some (71 : BitVec 8))
    (haddr : ∀ i, i < ServeExportServes.BS200.length →
        hs.memaddrs (byte_align (outBase + BitVec.ofNat 64 i)))
    (hinj : ∀ i j, i < ServeExportServes.BS200.length → j < ServeExportServes.BS200.length →
        i ≠ j → outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ P, Lower.lower (ServeEmit.serveExport ServeExportServes.BS200 ServeExportServes.BS405) = some P ∧
      (evaluate (liftProg P, hs)).1 =
        some (.Return (VW (BitVec.ofNat 64 ServeExportServes.BS200.length))) ∧
      ∀ i, i < ServeExportServes.BS200.length →
        mem_load_byte (evaluate (liftProg P, hs)).2.memory hs.memaddrs hs.be
            (outBase + BitVec.ofNat 64 i)
          = some ((BitVec.ofNat 64 ServeExportServes.BS200[i]!).setWidth 8) :=
  ⟨_, ServeExportServes.serveExport_lowers _ _,
   serveExport_serves_get_panSem hs hw _ _ outBase reqAddr hout hreq hget haddr hinj⟩

/-- **REAL, non-method → 405, on panSem.** -/
theorem serveExport_serves_405_real_panSem (hs : state θ) (hw : WordLocals hs)
    (outBase reqAddr : Pancake.Word)
    (hout : hs.locals (nm "out") = some (VW outBase))
    (hreq : hs.locals (nm "req") = some (VW reqAddr))
    (hbyte : mem_load_byte hs.memory hs.memaddrs hs.be reqAddr = some (88 : BitVec 8))
    (haddr : ∀ i, i < ServeExportServes.BS405.length →
        hs.memaddrs (byte_align (outBase + BitVec.ofNat 64 i)))
    (hinj : ∀ i j, i < ServeExportServes.BS405.length → j < ServeExportServes.BS405.length →
        i ≠ j → outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ P, Lower.lower (ServeEmit.serveExport ServeExportServes.BS200 ServeExportServes.BS405) = some P ∧
      (evaluate (liftProg P, hs)).1 =
        some (.Return (VW (BitVec.ofNat 64 ServeExportServes.BS405.length))) ∧
      ∀ i, i < ServeExportServes.BS405.length →
        mem_load_byte (evaluate (liftProg P, hs)).2.memory hs.memaddrs hs.be
            (outBase + BitVec.ofNat 64 i)
          = some ((BitVec.ofNat 64 ServeExportServes.BS405[i]!).setWidth 8) :=
  ⟨_, ServeExportServes.serveExport_lowers _ _,
   serveExport_serves_405_panSem hs hw _ _ outBase reqAddr hout hreq hbyte haddr hinj⟩

/-! ## 5. Hypotheses inhabited

A concrete panSem state (`out ↦ 16`, `req ↦ 8`, byte 88 at address 8, address
16 mapped) satisfies every premise of the 405 rung for a one-byte response, and
the rung then computes; a state with `a`, `b` declared satisfies DEMO A's. -/

noncomputable def hsW (f : ffi_state θ) : state θ :=
  { locals := fun k => if k = nm "out" then some (VW 16) else if k = nm "req" then some (VW 8)
                       else if k = nm "a" then some (VW 0) else if k = nm "b" then some (VW 0)
                       else none,
    globals := FEMPTY, structs := [], code := FEMPTY, eshapes := FEMPTY,
    memory := fun a => .Word (if a = 8 then 88 else 0),
    memaddrs := fun a => a = 8 ∨ a = 16, sh_memaddrs := fun _ => False,
    clock := 0, be := False, ffi := f, base_addr := 0, top_addr := 0 }

theorem hsW_wordLocals (f : ffi_state θ) : WordLocals (hsW f) := by
  intro k x hx
  simp only [hsW] at hx
  split at hx; · exact ⟨16, (Option.some.inj hx).symm⟩
  split at hx; · exact ⟨8, (Option.some.inj hx).symm⟩
  split at hx; · exact ⟨0, (Option.some.inj hx).symm⟩
  split at hx; · exact ⟨0, (Option.some.inj hx).symm⟩
  simp at hx

theorem ladder_hypotheses_inhabited (f : ffi_state θ) :
    WordLocals (hsW f) ∧ BoundPan ["a", "b"] (hsW f) ∧
    (hsW f).locals (nm "out") = some (VW 16) ∧ (hsW f).locals (nm "req") = some (VW 8) ∧
    mem_load_byte (hsW f).memory (hsW f).memaddrs (hsW f).be 8 = some (88 : BitVec 8) ∧
    (∀ i, i < [7].length → (hsW f).memaddrs (byte_align (16 + BitVec.ofNat 64 i))) ∧
    (∀ i j, i < [7].length → j < [7].length → i ≠ j →
        (16 : Pancake.Word) + BitVec.ofNat 64 i ≠ 16 + BitVec.ofNat 64 j) := by
  have hab : nm "a" ≠ nm "out" ∧ nm "a" ≠ nm "req" ∧ nm "b" ≠ nm "out" ∧ nm "b" ≠ nm "req" ∧
      nm "b" ≠ nm "a" ∧ nm "req" ≠ nm "out" :=
    ⟨fun e => by simpa using nm_inj e, fun e => by simpa using nm_inj e,
     fun e => by simpa using nm_inj e, fun e => by simpa using nm_inj e,
     fun e => by simpa using nm_inj e, fun e => by simpa using nm_inj e⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hab
  refine ⟨hsW_wordLocals f, ?_, by simp [hsW], by simp [hsW, h6], ?_, ?_, ?_⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ⟨0, by simp [hsW, h1, h2]⟩
    · exact ⟨0, by simp [hsW, h3, h4, h5]⟩
  · have e : byte_align (8 : BitVec 64) = 8 := by
      rw [byte_align_agree]; decide
    simp only [mem_load_byte, hsW, e]
    simp
    rw [show (False : Prop) = (false = true) by simp, get_byte_agree]; decide
  · intro i hi
    simp at hi; subst hi
    have e : byte_align ((16 : BitVec 64) + BitVec.ofNat 64 0) = 16 := by
      rw [byte_align_agree]; decide
    simp only [hsW, e]; simp
  · intro i j hi hj hne; simp at hi hj; omega

/-- The 405 rung on the inhabited state: it returns 1 and lands the byte 7 at
address 16, read back with panSem's `mem_load_byte`. -/
theorem serve_405_panSem_witness (f : ffi_state θ) :
    (evaluate (liftProg (ServeExportServes.serveModel [] [7]), hsW f)).1 =
      some (.Return (VW 1)) ∧
    mem_load_byte (evaluate (liftProg (ServeExportServes.serveModel [] [7]), hsW f)).2.memory
        (hsW f).memaddrs (hsW f).be 16 = some 7 := by
  obtain ⟨hw, _, ho, hr, hb, ha, hi⟩ := ladder_hypotheses_inhabited f
  have h := serveExport_serves_405_panSem (hsW f) hw [] [7] 16 8 ho hr hb ha hi
  exact ⟨h.1, by simpa using h.2 0 (by decide)⟩

/-- **A limit of rung [2] as the orb compiler states it (Codex round 3).**
`WF` asks every guard and assignment to evaluate in EVERY Sem.lean state, so a
stage whose leaves read a local (`redirectStatusStage`, `httpStamp`,
`crlfStamp` in ProofProducing) is certified only under a hypothesis no state
family satisfies: here, the redirect stage's `∀ s, s.locals "code" = some …`
fails on the state with no locals. `translateCertPan` inherits this; its
instances are meaningful only for stages with closed leaves (`closedDemo`).
Stages that read locals belong in the precondition form (`RefinesClk` /
`RefinesClkPan`), whose `P` can say the local is bound. -/
theorem wf_reading_local_uninhabited (codeVal : Pancake.PancakeState (ffi_state θ) → Pancake.Word)
    (f : ffi_state θ) :
    ¬ ∀ s : Pancake.PancakeState (ffi_state θ), s.locals "code" = some (codeVal s) := by
  intro h
  have := h (ss0 f)
  simp [ss0] at this

/-- DEMO A on the inhabited state. -/
theorem closedDemo_panSem_witness (f : ffi_state θ) :
    (evaluate (liftProg (emitServe (closedDemo (σ := ffi_state θ))), hsW f)).2.locals (nm "b") =
      some (VW 7) := by
  obtain ⟨hw, hb, _⟩ := ladder_hypotheses_inhabited f
  exact (closedDemo_panSem (hsW f) hw hb).2.2

end Pancake.LadderPanSem

/-! ## 6. Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound}. -/
#print axioms Pancake.LadderPanSem.refinesPan_of_refines
#print axioms Pancake.LadderPanSem.translateCertPan
#print axioms Pancake.LadderPanSem.refinesClkPan_of_refinesClk
#print axioms Pancake.LadderPanSem.closedDemo_panSem
#print axioms Pancake.LadderPanSem.serveExport_serves_get_panSem
#print axioms Pancake.LadderPanSem.serveExport_serves_405_panSem
#print axioms Pancake.LadderPanSem.serveExport_serves_get_real_panSem
#print axioms Pancake.LadderPanSem.serveExport_serves_405_real_panSem
#print axioms Pancake.LadderPanSem.serve_405_panSem_witness
#print axioms Pancake.LadderPanSem.closedDemo_panSem_witness
#print axioms Pancake.LadderPanSem.wf_reading_local_uninhabited
