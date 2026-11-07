/-
# `Dregg2.Circuit.FriDecodedTraceWitness` — L5·R4b: from R4a's decoded trace matrix to the
`TraceWitnessed` legs — the AIR-satisfaction half, assembled on the LANDED ALI/quotient chain,
with the DEEP linkage named as the precise residual.

## The R4b ASSESS verdict (the load-bearing question, answered first)

**Q: does "the verifier ACCEPTS" + "the decoded trace is the low-degree word" discharge the
AIR-constraint leg (`MainAirAcceptF`)?** The answer splits the DEEP-ALI argument into its two
classical halves, and they have OPPOSITE status in this tree:

  * **The ALI/quotient half is LANDED** (accept ⟹ the constraints hold on the trace, GIVEN the
    opened-values↔trace-polynomials link): `verifyAlgo_accept_forces_table_identity`
    (`OodQuotientConsistency.lean:197` — acceptance FORCES the batched OOD identity, a theorem),
    `commitmentOpening_binds_of_poseidon2CR` (`OodCommitmentBinding` — opened = committed under
    the `Poseidon2SpongeCR` floor), `rlc_debatch` (`OodSoundnessGame` — Schwartz–Zippel
    de-batching at a non-exceptional Λ), `hood_of_oodColumnLayout` (`OodColumnLayout.lean:218` —
    the ∀-descriptor composition of the three), and
    `ood_forces_mainAirAccept_field_of_residuals` (`FieldIntegerLift.lean:139` —
    `{hood, hnonexc} ⟹ MainAirAcceptF`, with the `hZrow`/`hCrow` axes discharged in-tree).
    Composed descriptor-polymorphically at `AlgoStarkSoundTransferV3.mainAirAcceptF_of_floor`
    and `AlgoStarkSoundGeneral.algoStarkSound_of_memoryLegs`. This file USES that chain — the
    AIR leg below is DERIVED, never assumed.

  * **The DEEP half is a GENUINE GAP** (the opened OOD values are consistent with the COMMITTED
    — now DECODED — columns). Every landed composition Skolemizes the trace
    (`FriLdtExtract`'s `tr` field, `AlgoStarkSoundGeneral.lean:134`) and carries the
    column-layout equation `hlayout` as a hypothesis about that free trace. Nothing ties the
    opened `constraintEval`/`vanishingAtZeta`/`quotientAtZeta` to the unique interpolants R4a
    decodes out of the commitment. THE MISSING THEOREM (the knowledge-soundness core):

      for an accepting run whose committed matrix `M` is `ColsClose`-close, with `T` the unique
      decoded trace (`FriDecodedTraceReadout.colsClose_unique_trace`) and `p_j` the per-column
      interpolants, the verifier's opened OOD data satisfies
      `(oodBatchResidual d (decodedVmTrace T …) ζ qp).eval Λ
         = cast vCommitted − cast (A.mul vanishingAtZeta quotientAtZeta)`
      (+ the ε-form non-exceptionality of ζ/Λ as the honest probabilistic remainder).

    What closes it, precisely, in three sub-pieces:
      1. a Lean model of the deployed DEEP quotient — the FRI input word IS the α-RLC of the
         per-column quotients `(p_j(X) − opened_j)/(X − ζ)` over the opened rows
         (`fri/src/verifier.rs:620-640` at rev `82cfad7`); this seam is deliberately unmodeled
         (`DeployedTraceExtract.lean:414-419` names it as the RLC input-reduction residual);
      2. the quotient-consistency step — DEEP-quotient word inside the decoding radius ⟹ every
         claimed OOD value equals `p_j(ζ)` (factor theorem + unique decoding), distributed from
         the RLC batch to the individual columns by BCIKS correlated agreement — the primitive
         is NAMED (`FriCorrelatedAgreementSharp.CorrelatedAgreementLine`, with the reduction
         proven at the wrap instance) but UNPROVEN, and no deployed-instance wire exists;
      3. the domain re-base — the OOD modeler interpolates trace row `i` at `ω₂₇^i`
         (`TraceColumnInterp.lean:34-37`, `domainSize = 2^27`) while the deployed decode reads
         row `i` at `ω₂₄^(8·i)` (`FriDecodedTraceReadout.rowPt`); `constraintPoly` of the
         decoded trace must be tied to the decoded ω₂₄-interpolants across that model change.

    This is the honest wall of L5/R4b — research-grade proof engineering (2 is the core; 1 and
    3 are heavy modeling), NOT dischargeable from the landed machinery. It is carried below as
    `DecodedLdtLink` — the FriLdtExtract payload AT THE DECODED TRACE, minus what the
    identification discharges — never as `MainAirAcceptF`, never as `hood`.

## What this file BUILDS (all sorry-free, no axiom, no carrier)

  1. **The field-vector→`VmTrace` identification** (§1): `decodedVmTrace` — a decoded matrix as
     a deployed `VmTrace` (canonical ℤ-lifts of the BabyBear entries), generic in the row count
     `n` and instantiated at the deployed `2^21`, with the readout equations,
     `rows.length = 2^21 ≤ domainSize` (the `hcap` conjunct of the landed bundles, now a
     THEOREM), and FAITHFULNESS (`decodedVmTrace_faithful` — the identification loses nothing,
     mirroring R4a's `trace_pins_codeword`).
  2. **The decode as a FUNCTION** (§2): `decodedMatrix` — R4a's `∃!` turned into
     extraction-as-data, with its defining property, uniqueness, and the composed `∃!` at the
     `VmTrace` (`colsClose_unique_vmTrace`). FIRE on R4a's concrete fixtures: the corrupted
     `fireWord24` commitment decodes to the all-ones trace, whose `VmTrace` rows READ `1`.
  3. **The L5 assembly at the REALISTIC deployed instance** (§4):
     `positiveRadiusTraceDecode_decoded` — `PositiveRadiusTraceDecode … friSetupDeployed
     oracle 7340032` (the `2^24`-point, rate-`1/8` instance of `FriDeployedRateInstance`, NOT
     the size-16 toy `friSetupK8`; radius = the true UD radius R4a inherits from R2). Its
     residuals are EXACTLY {`Poseidon2SpongeCR`, `DecodedLdtLink`, `DecodedBusLink`} + the
     graduated-shape facts; per accepting close run, `MainAirAcceptF` is DERIVED by the landed
     ALI chain, the sites/ranges/memory legs (7 of the 11 `TraceWitnessed` legs) are DISCHARGED
     structurally, and the non-arith arm is derived from the bus models.

## `TraceWitnessed` legs (`DeployedTraceExtract.lean:176-189`) — the R4b scorecard

  |  leg                                   | status here                                        |
  |----------------------------------------|----------------------------------------------------|
  |  1 `MainAirAcceptF`                    | DERIVED (landed ALI chain; DEEP link = the residual)|
  |  2 non-arith (LogUp) arm               | DERIVED from `BusModelOk` models (`DecodedBusLink`) |
  |  3 `siteHoldsAll` hashSites            | DISCHARGED (graduated shape, `hsites`)              |
  |  4 ranges                              | DISCHARGED (graduated shape, `hranges`)             |
  |  5 `maddrs.Nodup`                      | DISCHARGED (mem/map-free structural legs)           |
  |  6 memLog addr closure                 | DISCHARGED (")                                      |
  |  7 `Disciplined`                       | DISCHARGED (")                                      |
  |  8 `MemCheck`                          | DISCHARGED (")                                      |
  |  9 `tf .memory` assembly               | DISCHARGED (aux tables chosen memory-empty)         |
  | 10 `tf .mapOps` assembly               | DISCHARGED (")                                      |
  | 11 published-commit link               | CARRIED (`tracePublishedCommit` is `opaque`,        |
  |                                        |  `CircuitSoundness.lean:466` — a deployment fact;   |
  |                                        |  same posture as the committed `FriLdtExtractV3`)   |

  Honest scope notes: the mem/map discharge is for GRADUATED (all-lookup non-arith, mem/map-free)
  descriptors — the deployed `transferV3` class (`positiveRadiusTraceDecode_transferV3`);
  descriptors with real memory ops owe their memory legs exactly as
  `AlgoStarkSoundGeneral.MemoryLegs` states them. `pub`/aux-`tf` remain extractor-supplied data:
  R4b pins the MAIN-TRACE ROWS to the commitment's decode; the aux-table columns' own decode is a
  further rung (their soundness enters through `BusModelOk`, which is carried, not faked).

No sorry, no axiom, `#assert_axioms` on every theorem.

⚑ NO LONGER PURELY ADDITIVE (2026-07-25): `decodedLdtLink_of_friLdtExtract` was DELETED from this
file. It was the only route into the DEEP-ALI residual `DecodedLdtLink`, and its hypothesis —
`AlgoStarkSoundGeneral.FriLdtExtract` — is PROVED to force `CircuitSoundness.verifyBatch` to reject
EVERY input at the deployed `cfg*` arguments, i.e. it was an EMPTY premise. See the deletion note at
the `DecodedLdtLink` definition below; the replacement is
`FriFsDecodedOodRepair.decodedLdtLinkCons_of_friLdtExtractCons`, landing in `DecodedLdtLinkCons`.
⚠ `DecodedLdtLink` itself (retained here) still states the SINGLETON `oodPoint = [ood]` and is
therefore still refuted on accepting runs — it is kept as the subject of
`FriFsDecodedOodRepair.decodedLdtLink_makes_verifyBatch_reject_every_close_run`, not as a premise
anything should newly consume.
-/
import Dregg2.Circuit.FriDecodedTraceReadout
import Dregg2.Circuit.DeployedTraceExtract
import Dregg2.Circuit.AlgoStarkSoundGeneral

namespace Dregg2.Circuit.FriDecodedTraceWitness

open Polynomial
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.DescriptorIR2
  (VmTrace EffectVmDescriptor2 envAt VmConstraint2 Lookup TraceFamily zeroAsg TableId
   memLog mapLog)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith)
open Dregg2.Circuit.FriSoundness (closeN disagree)
open Dregg2.Circuit.RsUniqueDecoding (evalVec)
open Dregg2.Circuit.FriDeployedRateInstance (friSetupDeployed pR omega24)
open Dregg2.Circuit.FriCloseNUniqueDecode
  (friSetupDeployed_closeN_decode oneWord oneWord_mem fireWord24 fireWord24_close
   deployed_decode_pins)
open Dregg2.Circuit.FriDecodedTraceReadout
  (rowPt traceIdx colsClose_unique_trace oneWord_evalVec_C1)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.DeployedTraceExtract (TraceWitnessed PositiveRadiusTraceDecode)
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo FriParams RecursionVk FriChecks FriCore FieldArith TableOpening fullChecks)
open Dregg2.Circuit.CircuitSoundness
  (Registry BatchPublicInputs BatchProof tracePublishedCommit)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly ood_forces_mainAirAccept_field_of_residuals)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.OodColumnLayout (oodBatchResidual hood_of_oodColumnLayout)
open Dregg2.Circuit.LogUpColumnLayout (BusModelOk)
open Dregg2.Circuit.AlgoStarkSoundGeneral
  (AcceptsFull FriLdtExtract MemMapFree memoryLegs_of_lookupShape nonArithArm_of_busModels)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)

set_option autoImplicit false

/-! ## §1 — The field-vector→`VmTrace` identification.

A decoded trace matrix (R4a's readout: rows = the trace rows, columns = the committed trace
columns) becomes a deployed `VmTrace` by taking the CANONICAL integer lift of each BabyBear
entry (`ZMod.val` — the unique representative in `[0, p)`; the lift is canonical, so the
identification is lossless, not a many-one collapse). Everything here is generic in the row
count `n`; the deployed instantiation is `n := 2^21` (R4a's trace subdomain). `pub` and the
aux-table family remain extractor data (see the header's honest-scope note). -/

/-- Row `i` of a decoded matrix as a deployed row `Assignment`: variable `v` reads the
canonical ℤ-lift of column `v`'s decoded value; variables beyond the committed width read `0`. -/
def decodedRow {n numCols : ℕ} (T : MatrixOracle (Fin n) numCols BabyBear)
    (i : Fin n) : Assignment :=
  fun v => if h : v < numCols then ((T i ⟨v, h⟩).val : ℤ) else 0

/-- The readout equation on the committed width. -/
theorem decodedRow_apply {n numCols : ℕ} (T : MatrixOracle (Fin n) numCols BabyBear)
    (i : Fin n) (j : Fin numCols) :
    decodedRow T i (j : ℕ) = ((T i j).val : ℤ) := by
  unfold decodedRow
  rw [dif_pos j.isLt, Fin.eta]

/-- The lift is CANONICAL: every entry lands in `[0, p)` — one representative per field value,
so the trace rows carry exactly the decoded matrix, no aliasing. -/
theorem decodedRow_canonical {n numCols : ℕ} (T : MatrixOracle (Fin n) numCols BabyBear)
    (i : Fin n) (j : Fin numCols) :
    0 ≤ decodedRow T i (j : ℕ) ∧ decodedRow T i (j : ℕ) < (babyBearP : ℤ) := by
  rw [decodedRow_apply]
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast (T i j).val_lt⟩

/-- **The decoded `VmTrace`**: the decoded matrix as main-trace rows (canonical lifts), with
extractor-supplied public inputs and aux-table family. -/
def decodedVmTrace {n numCols : ℕ} (T : MatrixOracle (Fin n) numCols BabyBear)
    (pubA : Assignment) (tf : TraceFamily) : VmTrace :=
  { rows := List.ofFn (fun i : Fin n => decodedRow T i)
  , pub  := pubA
  , tf   := tf }

@[simp] theorem decodedVmTrace_rows_length {n numCols : ℕ}
    (T : MatrixOracle (Fin n) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily) :
    (decodedVmTrace T pubA tf).rows.length = n := by
  simp only [decodedVmTrace, List.length_ofFn]

@[simp] theorem decodedVmTrace_tf {n numCols : ℕ}
    (T : MatrixOracle (Fin n) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily) :
    (decodedVmTrace T pubA tf).tf = tf := rfl

/-- **The `hcap` conjunct of the landed extraction bundles is a THEOREM at the decoded trace**
(`2^21 ≤ 2^27 = TraceColumnInterp.domainSize`) — the first bundle conjunct the identification
genuinely discharges (`FriLdtExtract` carries it as a hypothesis; `DecodedLdtLink` §3 drops it). -/
theorem decodedVmTrace_hcap {numCols : ℕ}
    (T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily) :
    (decodedVmTrace T pubA tf).rows.length ≤ domainSize := by
  rw [decodedVmTrace_rows_length]
  norm_num [domainSize]

/-- **The trace READS the decoded matrix**: the row environment at trace row `i`, variable `j`,
is the canonical lift of the decoded value `T i j`. -/
theorem decodedVmTrace_envAt_loc {n numCols : ℕ}
    (T : MatrixOracle (Fin n) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily)
    (i : Fin n) (j : Fin numCols) :
    (envAt (decodedVmTrace T pubA tf) (i : ℕ)).loc (j : ℕ) = ((T i j).val : ℤ) := by
  have hlen : (i : ℕ) < (decodedVmTrace T pubA tf).rows.length := by
    rw [decodedVmTrace_rows_length]; exact i.isLt
  simp only [envAt]
  rw [List.getD_eq_getElem _ _ hlen]
  show ((List.ofFn fun i : Fin n => decodedRow T i)[(i : ℕ)]'(by simp)) (j : ℕ) = _
  rw [List.getElem_ofFn]
  simp only [Fin.eta, decodedRow, Fin.isLt, dite_true]

/-- The readout round-trips: casting the trace's ℤ entry back to BabyBear recovers the decoded
field value — the ℤ-lift carries no information loss. -/
theorem decodedVmTrace_envAt_cast {n numCols : ℕ}
    (T : MatrixOracle (Fin n) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily)
    (i : Fin n) (j : Fin numCols) :
    (((envAt (decodedVmTrace T pubA tf) (i : ℕ)).loc (j : ℕ) : ℤ) : BabyBear) = T i j := by
  rw [decodedVmTrace_envAt_loc, Int.cast_natCast]
  exact ZMod.natCast_rightInverse (T i j)

/-- **FAITHFULNESS — the identification loses nothing** (the `VmTrace` half of R4a's
`trace_pins_codeword`): two decoded matrices with the same trace are the SAME matrix. With R4a's
`colsClose_unique_trace` this makes commitment → codewords → trace matrix → `VmTrace` injective
end-to-end on the decoded objects. -/
theorem decodedVmTrace_faithful {n numCols : ℕ}
    {T T' : MatrixOracle (Fin n) numCols BabyBear}
    {pubA pubA' : Assignment} {tf tf' : TraceFamily}
    (h : decodedVmTrace T pubA tf = decodedVmTrace T' pubA' tf') : T = T' := by
  funext i j
  have h1 : (envAt (decodedVmTrace T pubA tf) (i : ℕ)).loc (j : ℕ)
      = (envAt (decodedVmTrace T' pubA' tf') (i : ℕ)).loc (j : ℕ) := by rw [h]
  rw [decodedVmTrace_envAt_loc, decodedVmTrace_envAt_loc] at h1
  have hval : (T i j).val = (T' i j).val := Int.natCast_inj.mp h1
  calc T i j = (((T i j).val : ℕ) : BabyBear) := (ZMod.natCast_rightInverse (T i j)).symm
    _ = (((T' i j).val : ℕ) : BabyBear) := by rw [hval]
    _ = T' i j := ZMod.natCast_rightInverse (T' i j)

/-! ## §2 — The decode as a FUNCTION (extraction-as-data), on R4a's `∃!`. -/

/-- **`decodedMatrix`** — THE decoded trace matrix of a `ColsClose`-close batched commitment:
R4a's unique object (`colsClose_unique_trace`), as data. -/
noncomputable def decodedMatrix {numCols : ℕ}
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 M) :
    MatrixOracle (Fin (2 ^ 21)) numCols BabyBear :=
  (colsClose_unique_trace M hcols).choose

/-- The defining property: each column of `decodedMatrix` is the trace-subdomain restriction of
that column's unique `natDegree < 2^21` interpolant of the unique in-radius codeword. -/
theorem decodedMatrix_spec {numCols : ℕ}
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 M) :
    ∀ j, ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
      g ∈ friSetupDeployed.C ∧ (disagree (M.col j) g).card ≤ 7340032 ∧
      p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
      (decodedMatrix M hcols).col j = fun i => p.eval (rowPt i) :=
  (colsClose_unique_trace M hcols).choose_spec.1

/-- Uniqueness: ANY matrix with the property IS `decodedMatrix`. -/
theorem decodedMatrix_unique {numCols : ℕ}
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 M)
    (T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear)
    (hT : ∀ j, ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
      g ∈ friSetupDeployed.C ∧ (disagree (M.col j) g).card ≤ 7340032 ∧
      p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
      T.col j = fun i => p.eval (rowPt i)) :
    T = decodedMatrix M hcols :=
  (colsClose_unique_trace M hcols).choose_spec.2 T hT

/-- **⚑ The unique decoded `VmTrace` of a close batched commitment** — R4a's `∃!` transported
across the §1 identification: for fixed extractor data `(pubA, tf)`, EXACTLY ONE `VmTrace` is
the decoded trace of the commitment. Uniqueness is via `decodedVmTrace_faithful` — the
identification is lossless, so the `∃!` survives the type change. -/
theorem colsClose_unique_vmTrace {numCols : ℕ}
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 M)
    (pubA : Assignment) (tf : TraceFamily) :
    ∃! t : VmTrace, ∃ T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear,
      t = decodedVmTrace T pubA tf ∧
      ∀ j, ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
        g ∈ friSetupDeployed.C ∧ (disagree (M.col j) g).card ≤ 7340032 ∧
        p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
        T.col j = fun i => p.eval (rowPt i) := by
  refine ⟨decodedVmTrace (decodedMatrix M hcols) pubA tf,
    ⟨decodedMatrix M hcols, rfl, decodedMatrix_spec M hcols⟩, ?_⟩
  rintro t ⟨T, rfl, hT⟩
  rw [decodedMatrix_unique M hcols T hT]

/-! ### §2-FIRE — the concrete corrupted commitment decodes to the all-ones `VmTrace`.

R4a's fixture: `fireWord24` is the all-ones codeword with coordinate 0 flipped (corruption
real). Its 1-column commitment is `ColsClose`-close, `decodedMatrix` computes to the all-ones
matrix (the corruption is REPAIRED by the decode), and the decoded `VmTrace` rows read `1`. -/

/-- The fixture's `ColsClose` hypothesis, discharged from R4a/R2's concrete `fireWord24_close`. -/
theorem fireMatrix_colsClose :
    MatrixOracle.ColsClose friSetupDeployed.C 7340032 (MatrixOracle.ofWord fireWord24) :=
  (MatrixOracle.colsClose_ofWord_iff friSetupDeployed.C 7340032 fireWord24).mpr fireWord24_close

/-- **FIRE** — the decode-as-data COMPUTES on the corrupted fixture: `decodedMatrix` of the
`fireWord24` commitment IS the all-ones matrix. (Existence via `g := oneWord`, `p := C 1`;
the distance bound by pinning the in-radius codeword to `oneWord`, `deployed_decode_pins`.) -/
theorem decodedMatrix_fire :
    decodedMatrix (MatrixOracle.ofWord fireWord24) fireMatrix_colsClose
      = fun (_ : Fin (2 ^ 21)) (_ : Fin 1) => (1 : BabyBear) := by
  refine (decodedMatrix_unique _ fireMatrix_colsClose _ (fun j => ?_)).symm
  obtain ⟨g, ⟨hgC, hgd⟩, -⟩ := friSetupDeployed_closeN_decode fireWord24_close
  have hone : g = oneWord := deployed_decode_pins g hgC hgd
  rw [hone] at hgC hgd
  have hcol : (MatrixOracle.ofWord fireWord24).col j = fireWord24 := rfl
  refine ⟨oneWord, Polynomial.C 1, hgC, ?_, ?_, oneWord_evalVec_C1, ?_⟩
  · rw [hcol]; exact hgd
  · rw [Polynomial.natDegree_C]; norm_num
  · funext i
    simp [MatrixOracle.col]

/-- **FIRE (the trace reads out)** — the decoded `VmTrace` of the corrupted commitment reads `1`
at every row and committed column: the §1 identification and the §2 decode compose on concrete
deployed-parameter data, and the corrupted coordinate is repaired in the witness trace. -/
theorem decodedVmTrace_fire (pubA : Assignment) (tf : TraceFamily)
    (i : Fin (2 ^ 21)) (j : Fin 1) :
    (envAt (decodedVmTrace
        (decodedMatrix (MatrixOracle.ofWord fireWord24) fireMatrix_colsClose) pubA tf)
      (i : ℕ)).loc (j : ℕ) = 1 := by
  rw [decodedVmTrace_envAt_loc, decodedMatrix_fire]
  haveI : Fact (1 < babyBearP) := ⟨by norm_num⟩
  rw [ZMod.val_one]
  rfl

/-- **BITE (faithfulness is load-bearing)** — distinct decoded matrices yield DISTINCT traces:
the all-zeros and all-ones matrices do not collapse. So the identification genuinely transports
distinctions (uniqueness in `colsClose_unique_vmTrace` is not by degeneracy). -/
theorem decodedVmTrace_bites (pubA : Assignment) (tf : TraceFamily) :
    decodedVmTrace (fun (_ : Fin (2 ^ 21)) (_ : Fin 1) => (0 : BabyBear)) pubA tf
      ≠ decodedVmTrace (fun (_ : Fin (2 ^ 21)) (_ : Fin 1) => (1 : BabyBear)) pubA tf := by
  intro h
  have := congrFun (congrFun (decodedVmTrace_faithful h) ⟨0, by norm_num⟩) 0
  exact zero_ne_one this

/-! ## §3 — The extraction function and THE NAMED RESIDUALS at the decoded trace.

`decodedTr` totalizes the decode (the default off the close branch is never reached by the
assembly — `PositiveRadiusTraceDecode` supplies `ColsClose` per run). The residual `Prop`s are
the `FriLdtExtract` payload AT `decodedTr` — the trace is NO LONGER Skolemized: what remains
hypothetical is exactly the DEEP linkage (header, "the missing theorem"), the ε-form FS
non-exceptionality, the bus models, and the published-commit deployment fact. The `hcap`
conjunct is GONE — discharged by `decodedVmTrace_hcap`/`decodedTr_rows_le`. -/

/-- The default (never-decoded) trace. -/
def defaultTrace : VmTrace := { rows := [], pub := zeroAsg, tf := fun _ => [] }

open Classical in
/-- **`decodedTr`** — the R4b extraction function: on a `ColsClose`-close committed matrix, THE
decoded `VmTrace` (R4a's unique object through the §1 identification); otherwise the default. -/
noncomputable def decodedTr {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily) :
    BatchPublicInputs → BatchProof → VmTrace :=
  fun pi π =>
    if h : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π) then
      decodedVmTrace (decodedMatrix (oracle pi π) h) (pubA pi π) (tfam pi π)
    else defaultTrace

/-- On the close branch, `decodedTr` IS the decoded trace (proof-irrelevant in the closeness
witness). This is the pin: the bundle's trace is R4a's decoded object, not a free function. -/
theorem decodedTr_of_colsClose {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (pi : BatchPublicInputs) (π : BatchProof)
    (h : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π)) :
    decodedTr oracle pubA tfam pi π
      = decodedVmTrace (decodedMatrix (oracle pi π) h) (pubA pi π) (tfam pi π) := by
  simp only [decodedTr]
  rw [dif_pos h]

/-- **The witness trace READS the unique interpolants**: under closeness, row `i` / variable `j`
of the extraction's trace is the canonical lift of `p_j(ω₂₄^(8·i))` for THE unique decoded
interpolant `p_j` of committed column `j` — the R4b identity, machine-checked end-to-end. -/
theorem decodedTr_readout {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (pi : BatchPublicInputs) (π : BatchProof)
    (h : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π)) (j : Fin numCols) :
    ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
      g ∈ friSetupDeployed.C ∧ (disagree ((oracle pi π).col j) g).card ≤ 7340032 ∧
      p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
      ∀ i : Fin (2 ^ 21),
        (envAt (decodedTr oracle pubA tfam pi π) (i : ℕ)).loc (j : ℕ)
          = ((p.eval (rowPt i)).val : ℤ) := by
  obtain ⟨g, p, hgC, hgd, hpd, hpe, hcol⟩ := decodedMatrix_spec (oracle pi π) h j
  refine ⟨g, p, hgC, hgd, hpd, hpe, fun i => ?_⟩
  rw [decodedTr_of_colsClose oracle pubA tfam pi π h, decodedVmTrace_envAt_loc]
  rw [show decodedMatrix (oracle pi π) h i j
      = (decodedMatrix (oracle pi π) h).col j i from rfl, hcol]

/-- The extraction's trace satisfies the modeler's row cap UNCONDITIONALLY — the bundle conjunct
`(tr pi π).rows.length ≤ domainSize` (`FriLdtExtract`) is a theorem here, so `DecodedLdtLink`
below does not carry it. -/
theorem decodedTr_rows_le {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (pi : BatchPublicInputs) (π : BatchProof) :
    (decodedTr oracle pubA tfam pi π).rows.length ≤ domainSize := by
  simp only [decodedTr]
  split
  · exact decodedVmTrace_hcap _ _ _
  · simp [defaultTrace, domainSize]

/-- With memory/map-empty aux data, the extraction's trace has empty aux memory/map tables —
the `MemMapFree` input of the landed mem/map-free assembler, PROVEN for `decodedTr`. -/
theorem decodedTr_memMapFree {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (htfMem : ∀ pi π, tfam pi π .memory = []) (htfMap : ∀ pi π, tfam pi π .mapOps = [])
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) :
    MemMapFree perm RATE toNat params vk core A initState logN view
      (decodedTr oracle pubA tfam) := by
  intro pi π _
  constructor
  · simp only [decodedTr]
    split
    · rw [decodedVmTrace_tf]
      exact htfMem pi π
    · rfl
  · simp only [decodedTr]
    split
    · rw [decodedVmTrace_tf]
      exact htfMap pi π
    · rfl

/-- **`DecodedLdtLink` — THE NAMED DEEP-ALI RESIDUAL** (header: "the missing theorem", as a
`Prop`). The `FriLdtExtract` payload with the trace PINNED to `decodedTr` (R4a's decode) and the
`hcap` conjunct removed (discharged): per accepting `ColsClose`-close run, the OOD point/RLC
challenge/quotients/table opening with Merkle recompute data, the column-layout equation AT THE
DECODED TRACE, the ε-form FS non-exceptionality of Λ and ζ, and the published-commit link.
Contains NO `hood`, NO `MainAirAcceptF`, NO `hbus`, NO trace Skolemization — closing it is
exactly the DEEP quotient work itemized in the header (sub-pieces 1–3). -/
def DecodedLdtLink {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π) →
    ∃ (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      (view pi π).1.oodPoint = [ood] ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      (oodBatchResidual d (decodedTr oracle pubA tfam pi π) ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      Λ ∉ exceptionalSet (oodBatchResidual d (decodedTr oracle pubA tfam pi π) ζ qp) ∧
      (∀ c ∈ d.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly d (decodedTr oracle pubA tfam pi π) c
                - vanishingPoly (decodedTr oracle pubA tfam pi π) * qp c)) ∧
      tracePublishedCommit (decodedTr oracle pubA tfam pi π) = pi.toPublished

/-! **⚑ DELETED 2026-07-25 — `decodedLdtLink_of_friLdtExtract`.** It supplied `DecodedLdtLink` from
`AlgoStarkSoundGeneral.FriLdtExtract` at `decodedTr`. That bundle is PROVED to force
`CircuitSoundness.verifyBatch` to reject EVERY input at the deployed `cfg*` arguments
(`ApexOodLaneRepair.friLdtExtract_makes_verifyBatch_reject_everything`), so the adapter's hypothesis
was an EMPTY premise and it was the only route into the DEEP-ALI residual. Its replacement is
`FriFsDecodedOodRepair.decodedLdtLinkCons_of_friLdtExtractCons`, which lands directly in
`DecodedLdtLinkCons` (the `ood :: oodRest` shape `FriVerifier.batchTablesCheck` matches at
`FriVerifier.lean:805`) from `ApexOodLaneRepair.FriLdtExtractCons`. No twin is kept: routing the
old adapter through `decodedLdtLink_imp_cons` would have preserved the empty ENTRY — and that
transport is itself DELETED as of 2026-07-30, when `DecodedLdtLinkCons` gained the per-run opening
residual the landed link never carried. -/

/-- **`DecodedBusLink`** — the LogUp bus models AT the decoded trace (the aux-column analogue of
the DEEP link; `BusModelOk` is `LogUpColumnLayout`'s named FS side-condition bundle, carried
here exactly as the landed general assembler carries `BusModelFamily`). -/
def DecodedBusLink {F : Type*} [Field F] [DecidableEq F] {numCols : ℕ}
    (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π) →
    ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
      ∃ mult : List ℕ, BusModelOk fp embed d (decodedTr oracle pubA tfam pi π) l.table mult

/-! ## §4 — ⚑ THE L5 ASSEMBLY: `PositiveRadiusTraceDecode` at the REALISTIC deployed instance.

`friSetupDeployed` (`FriDeployedRateInstance.lean:454`): `|ι| = 2^24`, rate `1/8`, arity `8` —
the realistic-domain instance, NOT the size-16 toy `friSetupK8` the §3′ structure fields were
pinned at. Radius `7340032` = the true unique-decoding radius (R2/R4a, sharp both polarities).
HONEST caveat: this is the single-fold-resolution instance — the multi-LAYER fold tower of the
deployed FRI (and the intermediate layers' membership moving into the probabilistic assembly)
remains L5/L6 engineering beyond this rung, as `DeployedTraceExtract` §3′ already names. -/

/-! ## §4.1 — ⚑ DELETED 2026-07-25: `positiveRadiusTraceDecode_decoded` / `…_transferV3`.

They assembled `PositiveRadiusTraceDecode` from the LANDED `DecodedLdtLink` — the residual whose
singleton OOD conclusion is PROVED to force `CircuitSoundness.verifyBatch` to reject EVERY
`ColsClose`-close run at the deployed `cfg*` arguments
(`FriFsDecodedOodRepair.decodedLdtLink_makes_verifyBatch_reject_every_close_run`), i.e. they
delivered `TraceWitnessed` only on runs the deployed verifier rejects — and, independently, from a
BASE-typed challenge (`ζ Λ : BabyBear`) where the deployed `ζ`/`Λ` are quartic-extension elements
(`ExtFieldChallenge.lean:8-15`), which is not a restriction of the deployed equation but a different
equation over a strictly smaller value space (`OodExtChallengeLayout.extLayout_value_beyond_base`,
fired at `transferV3`).

They are SUPERSEDED, exactly and without loss, by the single chain in `FriFsDecodedOodRepair`:

* `positiveRadiusTraceDecode_decoded_extChallenges` / `…_transferV3_extChallenges` — the assembly
  with BOTH challenge families at the deployed typing (`DecodedLdtLinkExtCons BB4` +
  `DecodedBusLinkExt`), same conclusion at the same `friSetupDeployed`/UD-radius-`7340032` instance;
* `positiveRadiusTraceDecode_decoded_extCons` — the OOD half alone;
* `positiveRadiusTraceDecode_decoded_cons` — the base-typed link, now a COROLLARY of the above via
  `decodedLdtLinkExtCons_of_decodedLdtLinkCons`.

⚑ 2026-07-30: the line that stood here — "anyone holding the landed `DecodedLdtLink` recovers the
deleted statements verbatim as `positiveRadiusTraceDecode_decoded_cons … (decodedLdtLink_imp_cons …
h)`" — is FALSE now and is corrected rather than left. `decodedLdtLink_imp_cons` is DELETED:
`DecodedLdtLinkCons` gained the PER-RUN opening residual `¬ OpeningColl` (the honest replacement for
the refuted `Poseidon2SpongeCR` the assembly used to thread) and the landed link never carried it.
Holding the landed link recovers nothing, which costs nothing, because that link is one this tree
PROVES makes `verifyBatch` reject every close run at the deployed arguments. The statements are
deleted rather than kept because a twin of a statement that is provably about nothing at deployment
is exactly what this campaign is removing. -/

/-! ## §5 — TEETH on the assembly (the derived AIR leg is genuine, both polarities). -/

/-- **The assembled conclusion BITES** — `TraceWitnessed`'s AIR leg is falsifiable: the
committed tampered-gate trace cannot satisfy the `MainAirAcceptF` the assembly derives, so the
`DecodedLdtLink` residual cannot be met by a lying layout equation about a tampered trace
without paying the exceptional-set escape (the ε the FS legs honestly carry). -/
theorem decoded_air_leg_bites :
    ¬ MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
        Dregg2.Circuit.AirChecksSatisfied.tTampered :=
  Dregg2.Circuit.AirChecksSatisfied.tampered_gate_unacceptedF

/-- **The assembled conclusion FIRES** — the derived `MainAirAcceptF` conjunct is inhabited on
the committed honest witness, so the assembly's target is not vacuously unsatisfiable. -/
theorem decoded_air_leg_fires :
    MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
      Dregg2.Circuit.AirChecksSatisfied.tHonest :=
  Dregg2.Circuit.AirChecksSatisfied.honest_mainAirAcceptF

/-! ## §6 — Axiom hygiene. -/

#assert_axioms decodedRow_apply
#assert_axioms decodedRow_canonical
#assert_axioms decodedVmTrace_rows_length
#assert_axioms decodedVmTrace_tf
#assert_axioms decodedVmTrace_hcap
#assert_axioms decodedVmTrace_envAt_loc
#assert_axioms decodedVmTrace_envAt_cast
#assert_axioms decodedVmTrace_faithful
#assert_axioms decodedMatrix_spec
#assert_axioms decodedMatrix_unique
#assert_axioms colsClose_unique_vmTrace
#assert_axioms fireMatrix_colsClose
#assert_axioms decodedMatrix_fire
#assert_axioms decodedVmTrace_fire
#assert_axioms decodedVmTrace_bites
#assert_axioms decodedTr_of_colsClose
#assert_axioms decodedTr_readout
#assert_axioms decodedTr_rows_le
#assert_axioms decodedTr_memMapFree
#assert_axioms decoded_air_leg_bites
#assert_axioms decoded_air_leg_fires

end Dregg2.Circuit.FriDecodedTraceWitness
