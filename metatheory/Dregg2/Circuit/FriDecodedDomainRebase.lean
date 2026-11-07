/-
# `Dregg2.Circuit.FriDecodedDomainRebase` — L5·R4b SUB-PIECE 3: the ω₂₇-vs-ω₂₄ domain re-base.

## The mismatch, as VERIFIED in the files (not as described)

Two layers index the SAME trace rows at DIFFERENT field elements:

  * the OOD/constraint modeler puts trace row `i` at `ω₂₇^i`
    (`TraceColumnInterp.rowPt`, `TraceColumnInterp.lean:37`; `domainSize = 2^27`);
  * the FRI decode readout puts trace row `i` at `ω₂₄^(8·i)`
    (`FriDecodedTraceReadout.rowPt`, `FriDecodedTraceReadout.lean:115`), and
    `ω₂₄ = ω₂₇^8` (`FriDeployedRateInstance.lean:412`).

So the decode's row `i` is `ω₂₇^(64·i)` — CONFIRMED, the prompt's arithmetic is right. The two
are genuinely different points (`decodePt_ne_interpPt_one`), and modeler row 1 is not ANY decode
row (`interpPt_one_ne_decodePt`); the indexings overlap on exactly the rows `64 ∣ i`
(`interpPt_mem_decodeRange_iff`), i.e. `2^15` of the `2^21` modeler rows.

## The reconciliation (this file)

**It reconciles.** The stride is `64` and `64 · 2^21 = 2^27` EXACTLY: the decode's trace
subdomain is the stride-`64` sub-family of the modeler's committed `2^27` domain
(`decodePt_eq_interpPt` — an index identity, no approximation), and the substitution that moves
between them is `X ↦ X^64` (`rebase`), with the degree budget inflating by exactly the stride and
still fitting the modeler's domain with zero slack (`rebase64_natDegree_lt`).

## Scope — what is proven, and what is NOT

PROVEN (no `sorry`, no axiom beyond the three kernel ones; `#assert_axioms` on 39 declarations):
  1. §1 — both indexings pinned as explicit functions of the row index (`interpPt`, `decodePt`,
     each equal to its file's `rowPt` by `rfl`), the exponent identity `decodePt i = interpPt
     (64·i)`, `64 · 2^21 = 2^27 = domainSize` (zero slack), injectivity of each family on the
     trace-row range, injectivity of the re-indexing `i ↦ 64·i` (a genuine re-index, not a
     collapse), the exact overlap, and the differing row-SHIFT multipliers `ω₂₇` vs `ω₂₇^64`
     (which is what any transition/`nextShift` reasoning turns on).
  2. §2 — the change of variable: `(p(X^64)).eval (ω₂₇^i) = p.eval (ω₂₄^(8i))`, exact and
     hypothesis-free (`rebase_eval_basePt` generic, `rebase64_eval_interpPt` deployed), the
     degree transport `natDegree p < 2^21 ⟹ natDegree p(X^64) < 2^27` (`rebase64_natDegree_lt` —
     a low-degree witness for one indexing IS one for the other), and re-base faithfulness on the
     decode's low-degree witnesses (`rebase64_inj_lowDegree`).
  3. §3 — the EXACT alternative (`interpolate_stridePt_eq_self`, deployed instance
     `interpolate_decodePt_eq_self`): re-basing the modeler's NODE FAMILY to stride `64` makes the
     two layers' column polynomials literally EQUAL — no substitution, no remainder. The modeler's
     development uses `rowPt` only through injectivity on the row range, which the decode's family
     also has, so this is a live definition change for `TraceColumnInterp.rowPt`, not a wish.
  4. §4 — the CONSUMER direction (decode ⟶ modeler, the direction `DecodedLdtLink` needs, since
     the link is phrased in modeler objects and sub-piece 2 produces decode-side facts): for the
     decoded `VmTrace`, the modeler's `colPoly` agrees with the re-based decode interpolant at
     every row (`colPoly_decodedVmTrace_eval`) and IS the Lagrange interpolant of it on the
     modeler's node family (`colPoly_decodedVmTrace_eq_interpolate`), pinned as the unique
     `natDegree < 2^21` such polynomial (`colPoly_decodedVmTrace_pinned`).
  5. §5 — the discrepancy off the rows, exactly: the difference vanishes on all `2^21` rows and is
     therefore divisible by the row-vanishing polynomial `Z = ∏_{i<2^21}(X − ω₂₇^i)`
     (`rowVanishing_dvd_of_rows_zero`, `rebase64_sub_colPoly_isRoot`), giving
     `p(ζ^64) = colPoly(ζ) + Z(ζ)·h(ζ)` at any `ζ` (`eval_correspondence_of_factor`); and the
     discrepancy is NOT vacuous — for `natDegree p ≥ 2^15` the two are different polynomials
     (`rebase64_ne_colPoly`).
  6. §6 — the same bridge at the actual R4b extraction object `decodedTr`
     (`decodedTr_colPoly_rebase`), which is what `DecodedLdtLink` (`FriDecodedTraceWitness:450`)
     names.
  7. §7 — FIRED on a concrete instance: `ZMod 17`, `ω = 3` of order `16`, stride `4` (so the
     stride root is `13`, of order `4`, and `4·4 = 16` fills the domain as `64·2^21 = 2^27` does),
     decode polynomial `X² + 1`. The two indexings give DIFFERENT points at row 1 (`3` vs `13`)
     and the re-base makes them read the SAME computed values (`0` at row 1, `2` at row 2); the
     exact re-base returns `X² + 1` on the nose.

NOT PROVEN / HONEST LIMITS:
  * This file does NOT close `DecodedLdtLink`. It closes only its named sub-piece 3 (the domain
    re-base). Sub-pieces 1 (the DEEP-quotient RLC input model) and 2 (correlated-agreement
    quotient consistency) are untouched and remain the wall.
  * With the CURRENT `TraceColumnInterp.rowPt`, `colPoly` and `p(X^64)` agree on the `2^21` trace
    rows and NOT as polynomials (§5). So an OOD claim about `p_j(ζ)` transports to the modeler's
    `colPoly` at `ζ` only up to `Z(ζ)·h(ζ)`. Sub-piece 2 must either take its OOD point in the
    decode's coordinate (`ζ ↦ ζ^64`) or adopt §3's stride-`64` node family, which removes the
    correction entirely. That is a REAL constraint on how sub-pieces 2 and 3 compose.
  * §5's two halves are deliberately NOT composed into one deployed `∃h ∀ζ` theorem: putting
    `Lagrange.nodal (Finset.range (2^21)) interpPt` into that position makes the KERNEL's defeq
    check expand the `2^21`-fold product and diverge (measured: >150 s, `deterministic timeout`).
    Composition at the use site is one line and checks fine. The same hazard is why `colPoly` of
    `decodedVmTrace` is reached through `colPoly_eq_interpolate_envAt` (a general-`t` `rfl`) and
    never by a `rfl` at the decoded trace, which would force `List.ofFn` over `Fin (2^21)`.

This file changes NO existing definition. Additive; imports read-only.
-/
import Dregg2.Circuit.FriDecodedTraceWitness

namespace Dregg2.Circuit.FriDecodedDomainRebase

open Polynomial
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DescriptorIR2 (VmTrace TraceFamily envAt)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDecodedTraceWitness (decodedVmTrace decodedTr)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §0 — The re-base algebra, over any field.

Two node families on a root `ω`: the BASE family `i ↦ ω^i` (the modeler's shape) and the
STRIDE-`s` family `i ↦ (ω^s)^i` (the decode's shape). The change of variable between them is the
substitution `X ↦ X^s`. -/

section Generic

variable {F : Type*} [Field F]

/-- Row `i` at `ω^i` — the BASE indexing (the OOD/constraint modeler's shape). -/
def basePt (ω : F) (i : ℕ) : F := ω ^ i

/-- Row `i` at `(ω^s)^i` — the STRIDE-`s` indexing (the FRI decode's shape). -/
def stridePt (ω : F) (s i : ℕ) : F := (ω ^ s) ^ i

/-- The stride family is the base family re-indexed by `i ↦ s·i`. -/
theorem stridePt_eq_basePt (ω : F) (s i : ℕ) : stridePt ω s i = basePt ω (s * i) := by
  rw [stridePt, basePt, ← pow_mul]

/-- **The re-base substitution** `X ↦ X^s`. -/
noncomputable def rebase (s : ℕ) (p : Polynomial F) : Polynomial F := p.comp (Polynomial.X ^ s)

@[simp] theorem rebase_eval (s : ℕ) (p : Polynomial F) (x : F) :
    (rebase s p).eval x = p.eval (x ^ s) := by
  rw [rebase, eval_comp, eval_pow, eval_X]

/-- **⚑ THE CHANGE OF VARIABLE.** Reading `p` at the STRIDE point of row `i` is reading the
re-based `p(X^s)` at the BASE point of the same row `i`. Exact, no hypotheses. -/
theorem rebase_eval_basePt (ω : F) (s i : ℕ) (p : Polynomial F) :
    (rebase s p).eval (basePt ω i) = p.eval (stridePt ω s i) := by
  rw [rebase_eval, basePt, stridePt, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The re-base is a RING map on polynomials — the AIR's arithmetic composition transports
term by term. -/
@[simp] theorem rebase_add (s : ℕ) (p q : Polynomial F) :
    rebase s (p + q) = rebase s p + rebase s q := by
  simp only [rebase, add_comp]

@[simp] theorem rebase_mul (s : ℕ) (p q : Polynomial F) :
    rebase s (p * q) = rebase s p * rebase s q := by
  simp only [rebase, mul_comp]

@[simp] theorem rebase_sub (s : ℕ) (p q : Polynomial F) :
    rebase s (p - q) = rebase s p - rebase s q := by
  simp only [rebase, sub_comp]

@[simp] theorem rebase_C (s : ℕ) (a : F) : rebase s (Polynomial.C a) = Polynomial.C a := by
  simp only [rebase, C_comp]

/-- The degree cost of the re-base is EXACTLY the stride. -/
theorem rebase_natDegree (s : ℕ) (p : Polynomial F) :
    (rebase s p).natDegree = p.natDegree * s := by
  simp only [rebase, natDegree_comp, natDegree_X_pow]

/-- A degree-`< D` witness for the stride family re-bases to a degree-`< D·s` witness for the
base family. -/
theorem rebase_natDegree_lt {s D : ℕ} (hs : 0 < s) {p : Polynomial F} (hp : p.natDegree < D) :
    (rebase s p).natDegree < D * s := by
  rw [rebase_natDegree]
  exact Nat.mul_lt_mul_of_lt_of_le hp le_rfl hs

end Generic

/-! ## §1 — The two DEPLOYED indexings, pinned, and the exponent identity between them. -/

open Dregg2.Circuit.BabyBearFriDeployed (omega27)
open Dregg2.Circuit.FriDeployedRateInstance (omega24)
open Dregg2.Circuit.TraceColumnInterp (domainSize omega27_isPrimitiveRoot)

/-- **The OOD/constraint modeler's row point**, pinned as an explicit function of the row index:
row `i` at `ω₂₇^i`. This IS `TraceColumnInterp.rowPt` (`interpPt_eq_rowPt`, definitional). -/
noncomputable def interpPt (i : ℕ) : BabyBear := omega27 ^ i

theorem interpPt_eq_rowPt (i : ℕ) : interpPt i = TraceColumnInterp.rowPt i := rfl

theorem interpPt_eq_basePt (i : ℕ) : interpPt i = basePt omega27 i := rfl

/-- **The FRI decode's row point**, pinned as an explicit function of the row index: row `i` at
`ω₂₄^(8·i)`. This IS `FriDecodedTraceReadout.rowPt` (`decodePt_eq_readoutRowPt`,
definitional). -/
noncomputable def decodePt (i : ℕ) : BabyBear := omega24 ^ (8 * i)

theorem decodePt_eq_readoutRowPt (i : Fin (2 ^ 21)) :
    decodePt (i : ℕ) = FriDecodedTraceReadout.rowPt i := rfl

/-- The deployed stride is `64 = 8 · 8`: the blowup `8` of the decode readout composed with the
`ω₂₄ = ω₂₇^8` step of the deployed domain. -/
theorem deployed_stride : (64 : ℕ) = 8 * 8 := by norm_num

theorem decodePt_eq_stridePt (i : ℕ) : decodePt i = stridePt omega27 64 i := by
  simp only [decodePt, stridePt, Dregg2.Circuit.FriDeployedRateInstance.omega24, ← pow_mul]
  congr 1
  ring

/-- **⚑ THE EXPONENT IDENTITY.** The decode's trace row `i` sits at the modeler's index `64·i`:
`ω₂₄^(8i) = (ω₂₇^8)^(8i) = ω₂₇^(64i)`. The two layers index the same row at points that are
related by a pure RE-INDEXING of the modeler's family, at stride `64`. -/
theorem decodePt_eq_interpPt (i : ℕ) : decodePt i = interpPt (64 * i) := by
  rw [decodePt_eq_stridePt, stridePt_eq_basePt, interpPt_eq_basePt]

/-- The stride uses the modeler's whole committed domain with ZERO slack:
`64 · 2^21 = 2^27 = domainSize`. -/
theorem stride_fills_domain : 64 * 2 ^ 21 = domainSize := by
  norm_num [domainSize]

/-- The re-indexing lands INSIDE the modeler's committed domain for every trace row. -/
theorem stride_index_lt {i : ℕ} (hi : i < 2 ^ 21) : 64 * i < domainSize := by
  rw [← stride_fills_domain]
  omega

/-- The re-indexing `i ↦ 64·i` is INJECTIVE — the model change is a genuine re-indexing, never a
collapse of distinct rows onto one point. -/
theorem stride_index_injective : Function.Injective (fun i : ℕ => 64 * i) := by
  intro i j h
  simpa using h

/-! ### Injectivity of each indexing on the trace-row range. -/

/-- The modeler's indexing is injective on any in-domain row range
(`TraceColumnInterp.rowPt_injective_on_range`). -/
theorem interpPt_injOn {n : ℕ} (hn : n ≤ domainSize) :
    Set.InjOn interpPt (Finset.range n) :=
  TraceColumnInterp.rowPt_injective_on_range hn

/-- Index-level injectivity of the modeler's family inside the committed domain. -/
theorem interpPt_inj_of_lt {i j : ℕ} (hi : i < domainSize) (hj : j < domainSize)
    (h : interpPt i = interpPt j) : i = j :=
  omega27_isPrimitiveRoot.pow_inj hi hj h

/-- The decode's indexing is injective on the `2^21` trace rows — via the exponent identity and
the modeler's primitivity, matching `FriDecodedTraceReadout.rowPt_injective`. -/
theorem decodePt_injOn : Set.InjOn decodePt (Finset.range (2 ^ 21)) := by
  intro i hi j hj h
  rw [decodePt_eq_interpPt, decodePt_eq_interpPt] at h
  have := interpPt_inj_of_lt (stride_index_lt (Finset.mem_range.mp hi))
    (stride_index_lt (Finset.mem_range.mp hj)) h
  omega

/-! ### The mismatch is REAL — the two indexings are genuinely different points. -/

/-- The two indexings DISAGREE already at row 1: the modeler reads `ω₂₇`, the decode reads
`ω₂₇^64`. -/
theorem decodePt_ne_interpPt_one : decodePt 1 ≠ interpPt 1 := by
  intro h
  rw [decodePt_eq_interpPt] at h
  have := interpPt_inj_of_lt (by norm_num [domainSize]) (by norm_num [domainSize]) h
  omega

/-- Stronger: the modeler's row-1 point is not ANY decode row point — the modeler's node set is
not contained in the decode's trace subdomain. -/
theorem interpPt_one_ne_decodePt {i : ℕ} (hi : i < 2 ^ 21) : decodePt i ≠ interpPt 1 := by
  intro h
  rw [decodePt_eq_interpPt] at h
  have := interpPt_inj_of_lt (stride_index_lt hi) (by norm_num [domainSize]) h
  omega

/-- **The exact overlap.** A modeler row point `i < 2^21` is a decode row point iff `64 ∣ i` —
the two indexings share exactly `2^15` of the `2^21` rows, and differ on the rest. -/
theorem interpPt_mem_decodeRange_iff {i : ℕ} (hi : i < 2 ^ 21) :
    (∃ k, k < 2 ^ 21 ∧ decodePt k = interpPt i) ↔ 64 ∣ i := by
  constructor
  · rintro ⟨k, hk, hpt⟩
    rw [decodePt_eq_interpPt] at hpt
    have := interpPt_inj_of_lt (stride_index_lt hk)
      (lt_of_lt_of_le hi (by norm_num [domainSize])) hpt
    exact ⟨k, this.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by omega, decodePt_eq_interpPt k⟩

/-! ### The row-SHIFT multipliers differ — the transition-constraint half of the mismatch. -/

theorem interpPt_succ (i : ℕ) : interpPt (i + 1) = omega27 * interpPt i := by
  rw [interpPt, interpPt, pow_succ]
  ring

theorem decodePt_succ (i : ℕ) : decodePt (i + 1) = omega27 ^ 64 * decodePt i := by
  rw [decodePt_eq_interpPt, decodePt_eq_interpPt, interpPt, interpPt,
    show 64 * (i + 1) = 64 * i + 64 by ring, pow_add]
  ring

/-- The two layers advance a row by DIFFERENT multipliers: `ω₂₇` for the modeler, `ω₂₇^64` for
the decode. Any transition/`nextShift` reasoning is model-relative until the re-base is
applied. -/
theorem shift_multipliers_differ : (omega27 : BabyBear) ≠ omega27 ^ 64 := by
  intro h
  have h' : interpPt 1 = interpPt 64 := by
    rw [interpPt, interpPt, pow_one]
    exact h
  have := interpPt_inj_of_lt (by norm_num [domainSize]) (by norm_num [domainSize]) h'
  omega

/-! ## §2 — The deployed re-base substitution `X ↦ X^64`. -/

/-- **The deployed re-base**: `p ↦ p(X^64)`. -/
noncomputable def rebase64 (p : Polynomial BabyBear) : Polynomial BabyBear := rebase 64 p

/-- **⚑ THE RE-BASE BRIDGE (deployed).** The decode reads `p` at `ω₂₄^(8i)`; the modeler reads
the re-based `p(X^64)` at `ω₂₇^i`; these are THE SAME VALUE — for every polynomial, every row
index, with no hypotheses. This is the change of variable the two layers differ by. -/
theorem rebase64_eval_interpPt (p : Polynomial BabyBear) (i : ℕ) :
    (rebase64 p).eval (interpPt i) = p.eval (decodePt i) := by
  rw [rebase64, interpPt_eq_basePt, decodePt_eq_stridePt]
  exact rebase_eval_basePt omega27 64 i p

/-- The same bridge, spelled at the two files' OWN row-point functions. -/
theorem rebase64_eval_rowPt (p : Polynomial BabyBear) (i : Fin (2 ^ 21)) :
    (rebase64 p).eval (TraceColumnInterp.rowPt (i : ℕ))
      = p.eval (FriDecodedTraceReadout.rowPt i) :=
  rebase64_eval_interpPt p (i : ℕ)

theorem rebase64_natDegree (p : Polynomial BabyBear) :
    (rebase64 p).natDegree = p.natDegree * 64 :=
  rebase_natDegree 64 p

/-- **The degree budget transports, with zero slack.** A decode interpolant of
`natDegree < 2^21` (the code's degree bound, which R4a proved EQUALS the trace length) re-bases
to `natDegree < 2^27 = domainSize` — exactly the modeler's committed domain size, since
`64 · 2^21 = 2^27`. A low-degree witness for the decode's indexing is a low-degree witness for
the modeler's. -/
theorem rebase64_natDegree_lt {p : Polynomial BabyBear} (hp : p.natDegree < 2 ^ 21) :
    (rebase64 p).natDegree < domainSize := by
  have h := rebase_natDegree_lt (s := 64) (D := 2 ^ 21) (by norm_num) hp
  rw [rebase64]
  simpa [domainSize] using h

/-- The re-base LOSES NOTHING on the decode's witnesses: `p(X^64) = q(X^64)` forces `p = q` for
the decode's `natDegree < 2^18·8 = 2^21` interpolants. -/
theorem rebase64_inj_lowDegree {p q : Polynomial BabyBear}
    (hp : p.natDegree < 2 ^ 18 * 8) (hq : q.natDegree < 2 ^ 18 * 8)
    (h : rebase64 p = rebase64 q) : p = q := by
  refine FriDecodedTraceReadout.trace_readout_pins_interpolant hp hq fun i => ?_
  rw [← rebase64_eval_rowPt, ← rebase64_eval_rowPt, h]

/-! ## §3 — The EXACT re-base: move the NODE FAMILY, and the two interpolants coincide. -/

/-- **Interpolating on a stride family returns the polynomial ON THE NOSE.** For a
`natDegree < n` polynomial `p`, Lagrange interpolation of the values `p` takes on an injective
stride-`s` node family recovers `p` exactly — no substitution, no remainder. -/
theorem interpolate_stridePt_eq_self {F : Type*} [Field F] {n s : ℕ} {ω : F}
    (hinj : Function.Injective (fun i : Fin n => stridePt ω s (i : ℕ)))
    {p : Polynomial F} (hp : p.natDegree < n) :
    Lagrange.interpolate Finset.univ (fun i : Fin n => stridePt ω s (i : ℕ))
        (fun i => p.eval (stridePt ω s (i : ℕ))) = p := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hdeg : p.degree < ((Finset.univ : Finset (Fin n)).card : WithBot ℕ) := by
    rw [hcard]
    rcases eq_or_ne p 0 with rfl | h0
    · simp only [degree_zero]
      exact WithBot.bot_lt_coe _
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp hp
  exact (Lagrange.eq_interpolate hinj.injOn hdeg).symm

/-- The decode's node family is injective, in the `Fin (2^21)` shape §3 wants. -/
theorem stridePt64_injective :
    Function.Injective (fun i : Fin (2 ^ 21) => stridePt omega27 64 (i : ℕ)) := by
  intro i j h
  simp only [← decodePt_eq_stridePt] at h
  exact Fin.ext (decodePt_injOn (Finset.mem_coe.mpr (Finset.mem_range.mpr i.isLt))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr j.isLt)) h)

/-- **⚑ THE MODEL CHANGE, EXACT.** Re-basing the MODELER's node family to the decode's
(stride `64`) makes the modeler's interpolant of the decoded trace values EQUAL the decode's own
interpolant — literally, not up to a remainder. `TraceColumnInterp`'s whole development uses
`rowPt` only through injectivity on the row range (`rowPt_injective_on_range`), which the
decode's family has (`decodePt_injOn`, `FriDecodedTraceReadout.rowPt_injective`); so this is a
live definition change for `TraceColumnInterp.rowPt`, not a wish. -/
theorem interpolate_decodePt_eq_self {p : Polynomial BabyBear} (hp : p.natDegree < 2 ^ 21) :
    Lagrange.interpolate Finset.univ (fun i : Fin (2 ^ 21) => decodePt (i : ℕ))
        (fun i => p.eval (decodePt (i : ℕ))) = p := by
  simp only [decodePt_eq_stridePt]
  exact interpolate_stridePt_eq_self stridePt64_injective hp

/-! ## §4 — THE CONSUMER DIRECTION: decode ⟶ modeler, at the decoded trace.

`DecodedLdtLink` (`FriDecodedTraceWitness.lean:450`) is phrased in MODELER objects
(`constraintPoly`/`oodBatchResidual` of `decodedTr`), while sub-piece 2 will deliver facts about
the DECODE-side interpolants `p_j`. So the direction the consumer needs is decode ⟶ modeler, and
that is the direction proven here. (The reverse, modeler ⟶ decode, is NOT needed by the link and
is NOT proven under the current node families; §3's exact re-base gives it outright once the
modeler's node family is changed to the decode's.) -/

/-- The modeler's column polynomial of a decoded trace agrees with the RE-BASED decode
interpolant at every trace row point. -/
theorem colPoly_decodedVmTrace_eval {numCols : ℕ}
    (T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily)
    (j : Fin numCols) {p : Polynomial BabyBear}
    (hp : ∀ i : Fin (2 ^ 21), T i j = p.eval (FriDecodedTraceReadout.rowPt i))
    (i : Fin (2 ^ 21)) :
    (TraceColumnInterp.colPoly (decodedVmTrace T pubA tf) (j : ℕ)).eval (interpPt (i : ℕ))
      = (rebase64 p).eval (interpPt (i : ℕ)) := by
  have hcap := FriDecodedTraceWitness.decodedVmTrace_hcap T pubA tf
  have hi : (i : ℕ) < (decodedVmTrace T pubA tf).rows.length := by
    rw [FriDecodedTraceWitness.decodedVmTrace_rows_length]
    exact i.isLt
  rw [rebase64_eval_interpPt, interpPt_eq_rowPt,
    TraceColumnInterp.colPoly_eval _ _ hcap _ hi,
    FriDecodedTraceWitness.decodedVmTrace_envAt_cast, hp i]
  rfl

/-- The modeler's `colPoly`, spelled as a Lagrange interpolation of the ROW-ENVIRONMENT values on
the modeler's node family. Definitional; stated for a general `t` (instantiating it at
`decodedVmTrace` by `rfl` would force `List.ofFn` over `Fin (2^21)` to unfold). -/
theorem colPoly_eq_interpolate_envAt (t : VmTrace) (col : ℕ) :
    TraceColumnInterp.colPoly t col
      = Lagrange.interpolate (Finset.range t.rows.length) interpPt
          (fun i => (((envAt t i).loc col : ℤ) : BabyBear)) := rfl

/-- **⚑ THE SUB-PIECE-3 BRIDGE.** The modeler's column polynomial of the decoded trace IS the
Lagrange interpolant, on the MODELER's node family `ω₂₇^i`, of the RE-BASED decode interpolant
`p(X^64)`. This converts a fact about the decode-side `p` into a fact about the OOD-modeler-side
`colPoly` of the very same trace. -/
theorem colPoly_decodedVmTrace_eq_interpolate {numCols : ℕ}
    (T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily)
    (j : Fin numCols) {p : Polynomial BabyBear}
    (hp : ∀ i : Fin (2 ^ 21), T i j = p.eval (FriDecodedTraceReadout.rowPt i)) :
    TraceColumnInterp.colPoly (decodedVmTrace T pubA tf) (j : ℕ)
      = Lagrange.interpolate (Finset.range (2 ^ 21)) interpPt
          (fun i => (rebase64 p).eval (interpPt i)) := by
  have hval : ∀ i ∈ Finset.range (2 ^ 21),
      (((envAt (decodedVmTrace T pubA tf) i).loc (j : ℕ) : ℤ) : BabyBear)
        = (rebase64 p).eval (interpPt i) := by
    intro i hi
    have hi' : i < 2 ^ 21 := Finset.mem_range.mp hi
    rw [rebase64_eval_interpPt]
    have hcast := FriDecodedTraceWitness.decodedVmTrace_envAt_cast T pubA tf ⟨i, hi'⟩ j
    rw [hp ⟨i, hi'⟩] at hcast
    exact hcast
  rw [colPoly_eq_interpolate_envAt, FriDecodedTraceWitness.decodedVmTrace_rows_length]
  exact Lagrange.interpolate_eq_of_values_eq_on _ _ hval

/-- The modeler's column polynomial of a decoded trace has `natDegree < 2^21` — it is the
low-degree representative, on the modeler's nodes, of the re-based interpolant. -/
theorem colPoly_decodedVmTrace_natDegree_lt {numCols : ℕ}
    (T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily)
    (col : ℕ) :
    (TraceColumnInterp.colPoly (decodedVmTrace T pubA tf) col).natDegree < 2 ^ 21 := by
  have hinj : Set.InjOn interpPt (Finset.range (2 ^ 21)) :=
    interpPt_injOn (by norm_num [domainSize])
  have hdeg := Lagrange.degree_interpolate_lt
    (r := fun i => (((envAt (decodedVmTrace T pubA tf) i).loc col : ℤ) : BabyBear)) hinj
  rw [Finset.card_range] at hdeg
  have hq' : (TraceColumnInterp.colPoly (decodedVmTrace T pubA tf) col).degree
      < ((2 ^ 21 : ℕ) : WithBot ℕ) := by
    rw [colPoly_eq_interpolate_envAt, FriDecodedTraceWitness.decodedVmTrace_rows_length]
    exact hdeg
  set q := TraceColumnInterp.colPoly (decodedVmTrace T pubA tf) col with hq
  rcases eq_or_ne q 0 with h0 | h0
  · rw [h0, natDegree_zero]
    norm_num
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hq'

/-- **The pinning the consumer applies.** `colPoly` of the decoded trace is THE `natDegree < 2^21`
polynomial that agrees with the re-based decode interpolant on the modeler's `2^21` row points:
anything else with those two properties IS it. -/
theorem colPoly_decodedVmTrace_pinned {numCols : ℕ}
    (T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily)
    (j : Fin numCols) {p : Polynomial BabyBear}
    (hp : ∀ i : Fin (2 ^ 21), T i j = p.eval (FriDecodedTraceReadout.rowPt i))
    {q : Polynomial BabyBear} (hqd : q.natDegree < 2 ^ 21)
    (hagree : ∀ i < 2 ^ 21, q.eval (interpPt i) = (rebase64 p).eval (interpPt i)) :
    q = TraceColumnInterp.colPoly (decodedVmTrace T pubA tf) (j : ℕ) := by
  refine Dregg2.Circuit.LowDegreeUniqueness.lowDegree_agree_forces_eq q _
    ((Finset.range (2 ^ 21)).image interpPt) hqd
    (colPoly_decodedVmTrace_natDegree_lt T pubA tf (j : ℕ)) ?_ ?_
  · rw [Finset.card_image_of_injOn (interpPt_injOn (by norm_num [domainSize])),
      Finset.card_range]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i < 2 ^ 21 := Finset.mem_range.mp hi
    rw [hagree i hi', ← colPoly_decodedVmTrace_eval T pubA tf j hp ⟨i, hi'⟩]

/-! ## §5 — THE HONEST LIMIT: exact ON THE ROWS, and a `Z`-multiple off them.

With the CURRENT `TraceColumnInterp.rowPt`, the re-base is exact on the `2^21` trace rows and NOT
as a polynomial identity: `p(X^64)` has degree up to `64·(2^21−1)` while `colPoly` has degree
`< 2^21`. Their difference is divisible by the row-vanishing (nodal) polynomial `Z`, and is
NONZERO whenever `2^15 ≤ natDegree p`. So an OOD claim about `p_j(ζ)` transports to the modeler's
`colPoly` at `ζ` only up to `Z(ζ)` — this is a real constraint on how sub-piece 2 composes with
sub-piece 3, not a formality. §3's node-family change removes it entirely. -/

/-- A polynomial vanishing on an injective node family is divisible by that family's nodal
polynomial. -/
theorem nodal_dvd_of_eval_eq_zero {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {v : ι → F} (hv : Set.InjOn v s) {f : Polynomial F}
    (hf : ∀ i ∈ s, f.eval (v i) = 0) : Lagrange.nodal s v ∣ f := by
  rw [Lagrange.nodal_eq]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro a ha b hb hab
    exact isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero_of_ne (fun h => hab (hv ha hb h))).isUnit
  · intro i hi
    exact dvd_iff_isRoot.mpr (hf i hi)

/-- The row-vanishing (nodal) polynomial of the MODELER's trace-row node family is
`Z = ∏_{i < 2^21} (X − ω₂₇^i)`, of degree exactly `2^21`. (It is written out rather than hidden
behind a `def`: with a `def` wrapper the kernel's defeq check unfolds the `Finset.range (2^21)`
product and does not terminate.) -/
theorem rowVanishing_natDegree :
    (Lagrange.nodal (Finset.range (2 ^ 21)) interpPt).natDegree = 2 ^ 21 := by
  rw [Lagrange.natDegree_nodal, Finset.card_range]

/-- Divisibility by the nodal polynomial of the first `n` modeler rows, `n` generic (so the
kernel never meets the concrete `Finset.range (2 ^ 21)`). -/
private theorem rowVanishing_dvd_of_rows_zero_gen {n : ℕ} (hn : n ≤ domainSize)
    (f : Polynomial BabyBear) (hf : ∀ i < n, f.eval (interpPt i) = 0) :
    Lagrange.nodal (Finset.range n) interpPt ∣ f :=
  nodal_dvd_of_eval_eq_zero (interpPt_injOn hn) (fun i hi => hf i (Finset.mem_range.mp hi))

/-- Divisibility by the row-vanishing polynomial, generic in `f`. -/
theorem rowVanishing_dvd_of_rows_zero (f : Polynomial BabyBear)
    (hf : ∀ i < 2 ^ 21, f.eval (interpPt i) = 0) :
    Lagrange.nodal (Finset.range (2 ^ 21)) interpPt ∣ f :=
  rowVanishing_dvd_of_rows_zero_gen (by norm_num [domainSize]) f hf

/-- The re-base difference vanishes at every modeler trace-row point. -/
theorem rebase64_sub_colPoly_isRoot {numCols : ℕ}
    (T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily)
    (j : Fin numCols) {p : Polynomial BabyBear}
    (hp : ∀ i : Fin (2 ^ 21), T i j = p.eval (FriDecodedTraceReadout.rowPt i))
    {i : ℕ} (hi : i < 2 ^ 21) :
    (rebase64 p - TraceColumnInterp.colPoly (decodedVmTrace T pubA tf) (j : ℕ)).eval
      (interpPt i) = 0 := by
  rw [eval_sub, ← colPoly_decodedVmTrace_eval T pubA tf j hp ⟨i, hi⟩, sub_self]

/-- **⚑ THE EXACT DISCREPANCY, at an arbitrary point.** Once `p(X^64) − q = Z·h` (which
`rowVanishing_dvd_of_rows_zero` supplies for `q := colPoly` of the decoded trace, via
`rebase64_sub_colPoly_isRoot`), the two layers' readings at ANY point `ζ` are related by
`p(ζ^64) = q(ζ) + Z(ζ)·h(ζ)`. Off the trace subdomain `Z(ζ) ≠ 0`, so this correction term is
exactly what sub-piece 2 must carry — or eliminate by adopting §3's node-family change.

(The two halves are kept separate on purpose: composing them into one deployed statement puts
`Lagrange.nodal (Finset.range (2^21)) interpPt` into a position where the KERNEL's defeq check
expands the `2^21`-fold product and does not terminate. Composition at the use site — supply the
`Z·h` factorisation, then apply this — is one line and checks fine.) -/
theorem eval_correspondence_of_factor (p q Z h : Polynomial BabyBear)
    (hfac : rebase64 p - q = Z * h) (ζ : BabyBear) :
    p.eval (ζ ^ 64) = q.eval ζ + Z.eval ζ * h.eval ζ := by
  have hev := congrArg (Polynomial.eval ζ) hfac
  rw [eval_sub, eval_mul, rebase64, rebase_eval] at hev
  linear_combination hev

/-- **The discrepancy is NOT vacuous.** Whenever the decode interpolant has `natDegree ≥ 2^15`,
`p(X^64)` and the modeler's column polynomial are DIFFERENT polynomials — the re-base genuinely
leaves a remainder off the trace rows. -/
theorem rebase64_ne_colPoly {numCols : ℕ}
    (T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear) (pubA : Assignment) (tf : TraceFamily)
    (col : ℕ) {p : Polynomial BabyBear} (hdeg : 2 ^ 15 ≤ p.natDegree) :
    rebase64 p ≠ TraceColumnInterp.colPoly (decodedVmTrace T pubA tf) col := by
  intro heq
  have h1 : (rebase64 p).natDegree = p.natDegree * 64 := rebase64_natDegree p
  have h2 := colPoly_decodedVmTrace_natDegree_lt T pubA tf col
  rw [← heq, h1] at h2
  have : 2 ^ 15 * 64 ≤ p.natDegree * 64 := Nat.mul_le_mul_right 64 hdeg
  omega

/-! ## §6 — At the R4b EXTRACTION OBJECT (`decodedTr`), which is what `DecodedLdtLink` names. -/

open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof)
open Dregg2.Circuit.FriDeployedRateInstance (friSetupDeployed)

/-- **⚑ SUB-PIECE 3, AT THE OBJECT THE LINK USES.** For a `ColsClose`-close committed matrix,
the modeler's column polynomial of `decodedTr`'s trace IS the interpolant, on the modeler's node
family, of the RE-BASED unique decode interpolant `p_j` of committed column `j`. This is the
conversion `DecodedLdtLink` needs in order to consume sub-piece 2's output: sub-piece 2 speaks
about `p_j`; `DecodedLdtLink` speaks about `constraintPoly`/`colPoly` of `decodedTr`. -/
theorem decodedTr_colPoly_rebase {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π))
    (j : Fin numCols) :
    ∃ p : Polynomial BabyBear,
      p.natDegree < 2 ^ 18 * 8 ∧
      (∀ i : Fin (2 ^ 21),
        FriDecodedTraceWitness.decodedMatrix (oracle pi π) hcols i j
          = p.eval (FriDecodedTraceReadout.rowPt i)) ∧
      TraceColumnInterp.colPoly (decodedTr oracle pubA tfam pi π) (j : ℕ)
        = Lagrange.interpolate (Finset.range (2 ^ 21)) interpPt
            (fun i => (rebase64 p).eval (interpPt i)) := by
  obtain ⟨g, p, hgC, hgd, hpd, hpe, hcol⟩ :=
    FriDecodedTraceWitness.decodedMatrix_spec (oracle pi π) hcols j
  have hval : ∀ i : Fin (2 ^ 21),
      FriDecodedTraceWitness.decodedMatrix (oracle pi π) hcols i j
        = p.eval (FriDecodedTraceReadout.rowPt i) := fun i => congrFun hcol i
  refine ⟨p, hpd, hval, ?_⟩
  rw [FriDecodedTraceWitness.decodedTr_of_colsClose oracle pubA tfam pi π hcols]
  exact colPoly_decodedVmTrace_eq_interpolate _ _ _ j hval

/-! ## §7 — FIRE: the re-base on a small concrete instance.

`ZMod 17` has multiplicative order `16 = 2^4` — the same 2-adic shape as BabyBear's `2^27`, at a
size the kernel can decide. `ω = 3` plays `ω₂₇`; the stride is `4` (playing `64`); `4 · 4 = 16`
fills the domain exactly as `64 · 2^21 = 2^27` does; the toy decode polynomial is `X² + 1`. -/

section Fire

local instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The toy field. -/
abbrev F17 : Type := ZMod 17

/-- The toy root has the right order: `3^16 = 1`, `3^8 = −1` (so `orderOf 3 = 16`), and the
stride root `3^4 = 13` has order `4` — the toy analogue of `ω₂₇` and `ω₂₇^64`. -/
theorem fire_root_orders :
    (3 : F17) ^ 16 = 1 ∧ (3 : F17) ^ 8 = -1 ∧
    ((3 : F17) ^ 4) ^ 4 = 1 ∧ ((3 : F17) ^ 4) ^ 2 ≠ 1 := by decide

/-- **FIRE — the mismatch is real in miniature.** Row 1 sits at `3` for the modeler-analogue base
family and at `13` for the decode-analogue stride family: DIFFERENT points, as `ω₂₇` vs `ω₂₇^64`
at deployed size. -/
theorem fire_points_differ :
    basePt (3 : F17) 1 = 3 ∧ stridePt (3 : F17) 4 1 = 13 ∧ (3 : F17) ≠ 13 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The toy decode-side polynomial `X² + 1` — degree `2`, inside the `4`-row budget. -/
noncomputable def fireP : Polynomial F17 := Polynomial.X ^ 2 + Polynomial.C 1

theorem fireP_eval (x : F17) : fireP.eval x = x ^ 2 + 1 := by
  simp [fireP]

theorem fireP_natDegree : fireP.natDegree = 2 := by
  simp only [fireP]
  exact natDegree_X_pow_add_C

/-- **⚑ FIRE — the bridge.** At every toy row, the re-based `p(X⁴)` read at the BASE point equals
`p` read at the STRIDE point: the general change of variable, instantiated. -/
theorem fire_bridge (i : ℕ) :
    (rebase 4 fireP).eval (basePt (3 : F17) i) = fireP.eval (stridePt (3 : F17) 4 i) :=
  rebase_eval_basePt 3 4 i fireP

/-- **⚑ FIRE — non-vacuous.** The shared values are COMPUTED, at points that genuinely differ:
row 1 reads `0` at `3` (re-based) and at `13` (decode-side); row 2 reads `2` at both. -/
theorem fire_bridge_values :
    (rebase 4 fireP).eval (basePt (3 : F17) 1) = 0 ∧
    fireP.eval (stridePt (3 : F17) 4 1) = 0 ∧
    (rebase 4 fireP).eval (basePt (3 : F17) 2) = 2 ∧
    fireP.eval (stridePt (3 : F17) 4 2) = 2 := by
  have h1 : basePt (3 : F17) 1 = 3 := by decide
  have h2 : stridePt (3 : F17) 4 1 = 13 := by decide
  have h3 : basePt (3 : F17) 2 = 9 := by decide
  have h4 : stridePt (3 : F17) 4 2 = 16 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rebase_eval, h1, fireP_eval]; decide
  · rw [h2, fireP_eval]; decide
  · rw [rebase_eval, h3, fireP_eval]; decide
  · rw [h4, fireP_eval]; decide

theorem fire_stridePt_injective :
    Function.Injective (fun i : Fin 4 => stridePt (3 : F17) 4 (i : ℕ)) := by
  have h : ∀ a b : Fin 4,
      stridePt (3 : F17) 4 (a : ℕ) = stridePt (3 : F17) 4 (b : ℕ) → a = b := by decide
  exact fun a b hab => h a b hab

/-- **⚑ FIRE — the exact re-base.** Interpolating the toy decode values on the STRIDE node family
returns `X² + 1` ON THE NOSE: §3's model change, instantiated and computed. -/
theorem fire_interpolate_exact :
    Lagrange.interpolate Finset.univ (fun i : Fin 4 => stridePt (3 : F17) 4 (i : ℕ))
        (fun i => fireP.eval (stridePt (3 : F17) 4 (i : ℕ))) = fireP :=
  interpolate_stridePt_eq_self fire_stridePt_injective (by rw [fireP_natDegree]; norm_num)

/-- **FIRE — the degree cost.** `p(X⁴)` has degree `8 ≥ 4`: off the four rows it is NOT a
degree-`< 4` modeler polynomial, exactly as `rebase64_ne_colPoly` says at deployed size. -/
theorem fire_rebase_natDegree : (rebase 4 fireP).natDegree = 8 := by
  rw [rebase_natDegree, fireP_natDegree]

end Fire

/-! ## §8 — Axiom audit. -/

#assert_axioms rebase_eval_basePt
#assert_axioms rebase_natDegree
#assert_axioms rebase_natDegree_lt
#assert_axioms decodePt_eq_stridePt
#assert_axioms decodePt_eq_interpPt
#assert_axioms stride_fills_domain
#assert_axioms stride_index_lt
#assert_axioms interpPt_injOn
#assert_axioms decodePt_injOn
#assert_axioms decodePt_ne_interpPt_one
#assert_axioms interpPt_one_ne_decodePt
#assert_axioms interpPt_mem_decodeRange_iff
#assert_axioms interpPt_succ
#assert_axioms decodePt_succ
#assert_axioms shift_multipliers_differ
#assert_axioms rebase64_eval_interpPt
#assert_axioms rebase64_eval_rowPt
#assert_axioms rebase64_natDegree_lt
#assert_axioms rebase64_inj_lowDegree
#assert_axioms interpolate_stridePt_eq_self
#assert_axioms interpolate_decodePt_eq_self
#assert_axioms colPoly_eq_interpolate_envAt
#assert_axioms colPoly_decodedVmTrace_eval
#assert_axioms colPoly_decodedVmTrace_eq_interpolate
#assert_axioms colPoly_decodedVmTrace_natDegree_lt
#assert_axioms colPoly_decodedVmTrace_pinned
#assert_axioms nodal_dvd_of_eval_eq_zero
#assert_axioms rowVanishing_natDegree
#assert_axioms rowVanishing_dvd_of_rows_zero
#assert_axioms rebase64_sub_colPoly_isRoot
#assert_axioms eval_correspondence_of_factor
#assert_axioms rebase64_ne_colPoly
#assert_axioms decodedTr_colPoly_rebase
#assert_axioms fire_root_orders
#assert_axioms fire_points_differ
#assert_axioms fire_bridge
#assert_axioms fire_bridge_values
#assert_axioms fire_interpolate_exact
#assert_axioms fire_rebase_natDegree

end Dregg2.Circuit.FriDecodedDomainRebase
