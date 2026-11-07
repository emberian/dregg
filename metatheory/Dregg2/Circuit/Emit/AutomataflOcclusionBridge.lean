/-
# Dregg2.Circuit.Emit.AutomataflOcclusionBridge — DISCHARGING the occlusion bridge's hypotheses.

`AutomataflOcclusionGeneric` proves the occlusion mathematics at ARBITRARY `n`, but its capstones
`occ_eq_occluded_vert` / `occ_eq_occluded_horiz` take NAMED hypotheses about the emitted columns:

  * `OneHotAt efrom n af` / `OneHotAt eto n at_` — the along-axis endpoint one-hots;
  * `hosrc` — the passable mask is boolean;
  * `hlineRange` — the line columns carry particle codes;
  * `LineReadsVert/Horiz` — the line columns really read the move's line off the OLD board;
  * `OsrcIsOtherSourceVert/Horiz` — the gated mask really marks the OTHER move's moving source.

This file turns every one of them into a THEOREM off `Satisfied2 automataflResolveDesc`, and
assembles `occ_iff_occluded`: the emitted threshold bit `cOcc` equals the reference `occluded`,
with NO hypothesis about the columns left standing.

## The honest resolution statement

The descriptor is instantiated at `NN = 2`. At `n = 2` a rook line has no strictly-interior cell,
so BOTH sides of `occ_iff_occluded` are constantly `false` — the bridge is TRUE but its CONTENT is
degenerate, exactly as the mathematics forces. What this file buys is STRUCTURAL: the capstone's
occlusion leg no longer routes through `occluded_false_n2` (a reference-side fact that is only true
at `n = 2` and would have to be deleted at `n = 11`). It routes through the `n`-generic bridge, whose
hypotheses are discharged here from gates that are themselves `NN`-parametric. Raising `NN` makes
the same statement non-degenerate with no new occlusion proof.
-/
import Dregg2.Circuit.Emit.AutomataflResolveRefine
import Dregg2.Circuit.Emit.AutomataflOcclusionGeneric

namespace Dregg2.Circuit.Emit.AutomataflResolveRefine

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Games.Automatafl
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.Emit.AutomataflStepRefine
  (Canon canon_zero canon_one canon_two canon_three eq_of_modEq_canon bin_of_gate canon_loc
   StepCanon codeToParticle)
open Dregg2.Games.Automatafl (Board Coord Particle Move occluded interior)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! ## §1 — The gate bundle for the occlusion READ columns.

Everything `validate_occlusion` emits that the bridge's hypotheses talk about: the two endpoint
one-hots, the gated `efrom`/`eto`/`line` selections, the two passable `eq_scalar`s, the `og` gate and
the gated `osrc` one-hot. Every field is a membership fact in the BYTE-PINNED constraint list,
discharged by `decide`, so each discharged hypothesis is anchored to the emitted descriptor. -/

/-- The `validate_occlusion` READ gates for the move at base `b`, block `o`, other move at `ob`. -/
structure OccReadGates (b o ob : Nat) : Prop where
  ety0 : cg (gBin (cEty o 0)) ∈ automataflResolveDesc.constraints
  ety1 : cg (gBin (cEty o 1)) ∈ automataflResolveDesc.constraints
  etys : cgH (((Head.c (-1)).addLin 1 (cEty o 0)).addLin 1 (cEty o 1))
           ∈ automataflResolveDesc.constraints
  -- ⚑ The one-hot INDEX head carries the `j = 0` term at coefficient ZERO; the canonical renderer
  -- keeps it, so the head named here is the head the emitter builds.
  etyi : cgH (((Head.lin 0 (cEty o 0)).addLin 1 (cEty o 1)).addLin (-1) (cTy b))
           ∈ automataflResolveDesc.constraints
  etx0 : cg (gBin (cEtx o 0)) ∈ automataflResolveDesc.constraints
  etx1 : cg (gBin (cEtx o 1)) ∈ automataflResolveDesc.constraints
  etxs : cgH (((Head.c (-1)).addLin 1 (cEtx o 0)).addLin 1 (cEtx o 1))
           ∈ automataflResolveDesc.constraints
  etxi : cgH (((Head.lin 0 (cEtx o 0)).addLin 1 (cEtx o 1)).addLin (-1) (cTx b))
           ∈ automataflResolveDesc.constraints
  efr0 : cgH (efromHead b o 0) ∈ automataflResolveDesc.constraints
  efr1 : cgH (efromHead b o 1) ∈ automataflResolveDesc.constraints
  eto0 : cgH (etoHead o 0) ∈ automataflResolveDesc.constraints
  eto1 : cgH (etoHead o 1) ∈ automataflResolveDesc.constraints
  lin0 : cgH (lineHead b o 0) ∈ automataflResolveDesc.constraints
  lin1 : cgH (lineHead b o 1) ∈ automataflResolveDesc.constraints
  ogG  : cgH (ogHead o) ∈ automataflResolveDesc.constraints
  os0  : cg (gBin (cOsrc o 0)) ∈ automataflResolveDesc.constraints
  os1  : cg (gBin (cOsrc o 1)) ∈ automataflResolveDesc.constraints
  osS  : cgH ((Head.lin (-1) (cOg o)).addLin 1 (cOsrc o 0) |>.addLin 1 (cOsrc o 1))
           ∈ automataflResolveDesc.constraints
  -- ⚑ `oneHotGatedConstraints` closes with `.addProd (-idx.const) [gate]`, i.e. a term at
  -- coefficient ZERO when the index head has no constant. The elided renderer dropped it; the
  -- canonical one WRITES it (`mul(const 0, cOg)`), so the head named here has four product terms.
  osI  : cgH (((((Head.lin 0 (cOsrc o 0)).addLin 1 (cOsrc o 1)).addProd (-1)
              [cOg o, cIv o, cFy ob]).addProd (-1) [cOg o, cFx ob] |>.addProd 1
              [cOg o, cIv o, cFx ob]).addProd 0 [cOg o]) ∈ automataflResolveDesc.constraints

/-- The `eq_scalar` bundles pinning the two passable comparisons. -/
structure PassGates (b o ob : Nat) : Prop where
  eqxD : cgH ((((Head.lin 1 (cEqxDsq o)).addProd (-1) [cFx ob, cFx ob]).addProd 2
              [cFx ob, cFx b]).addProd (-1) [cFx b, cFx b]) ∈ automataflResolveDesc.constraints
  eqxG : Ge0Gates9 (cEqxDsq o) (cEqxNeq o) (eqxBit o 0)
  eqxP : EqPinGate (cEqx o) (cEqxNeq o)
  eqyD : cgH ((((Head.lin 1 (cEqyDsq o)).addProd (-1) [cFy ob, cFy ob]).addProd 2
              [cFy ob, cFy b]).addProd (-1) [cFy b, cFy b]) ∈ automataflResolveDesc.constraints
  eqyG : Ge0Gates9 (cEqyDsq o) (cEqyNeq o) (cEqyNeq o + 1)
  eqyP : EqPinGate (cEqy o) (cEqyNeq o)

theorem occReadGates_a : OccReadGates (mvBase 0) (occBase 0) (mvBase 1) := by
  constructor <;> decide
theorem occReadGates_b : OccReadGates (mvBase 1) (occBase 1) (mvBase 0) := by
  constructor <;> decide
theorem passGates_a : PassGates (mvBase 0) (occBase 0) (mvBase 1) := by
  refine ⟨by decide, ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩, ⟨by decide⟩, by decide,
          ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩, ⟨by decide⟩⟩ <;> decide
theorem passGates_b : PassGates (mvBase 1) (occBase 1) (mvBase 0) := by
  refine ⟨by decide, ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩, ⟨by decide⟩, by decide,
          ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩, ⟨by decide⟩⟩ <;> decide

/-! ## §2 — The gated-selection extractor.

`efromHead`, `etoHead` and `ogHead` are the SAME emitted shape — `out == g·s₀ + (1−g)·s₁` — so one
extractor discharges all three. This is the gadget the WITNESSED direction bit buys: the selection is
a polynomial in the pinned `iv`, not a compile-time branch. -/

section Bridge
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The `iv`-gated selection gate forces `out = g·s₀ + (1−g)·s₁` over ℤ. -/
theorem gatedSel_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out g s0 s1 : Nat)
    (hgate : cgH ((((Head.lin 1 out).addProd (-1) [g, s0]).addLin (-1) s1).addProd 1 [g, s1])
               ∈ automataflResolveDesc.constraints)
    (hgb : (envAt t i).loc g = 0 ∨ (envAt t i).loc g = 1)
    (h0b : (envAt t i).loc s0 = 0 ∨ (envAt t i).loc s0 = 1)
    (h1b : (envAt t i).loc s1 = 0 ∨ (envAt t i).loc s1 = 1) :
    (envAt t i).loc out
      = (envAt t i).loc g * (envAt t i).loc s0
        + (1 - (envAt t i).loc g) * (envAt t i).loc s1 := by
  set e := envAt t i with he
  have hgt := rgateH hsat i hi hgate
  have hE : (headToExpr ((((Head.lin 1 out).addProd (-1) [g, s0]).addLin (-1) s1).addProd 1
        [g, s1])).eval e.loc
      = e.loc out + (-1) * (e.loc g * e.loc s0) + (-1) * e.loc s1
        + e.loc g * e.loc s1 := by canon_head_eval [headToExpr]
  rw [hE] at hgt
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgt)
  rcases hgb with a | a <;> rcases h0b with b1 | b1 <;> rcases h1b with c | c <;>
    rw [a, b1, c] <;> exact ⟨by norm_num, by norm_num⟩

/-! ## §3 — `OneHotAt efrom` / `OneHotAt eto`: the along-axis endpoint one-hots, DISCHARGED.

`validate_move` pins the source row/column one-hots to `fy`/`fx`; `validate_occlusion` pins BOTH
destination one-hots (`ety @ ty`, `etx @ tx`) unconditionally and gates only the SELECTION. So on
either branch the selected vector is one of two genuine one-hots — the property
`occ_eq_occluded_*` needs, and the reason gating the selection rather than the one-hots is the
stronger construction. -/

/-- A `{0,1}`-valued pair `(v 0, v 1) = (1−c, c)` IS the one-hot at `c.toNat`, at `NN = 2`. -/
theorem oneHot_pair {v : Nat → ℤ} {c : ℤ} (hc : c = 0 ∨ c = 1)
    (h0 : v 0 = 1 - c) (h1 : v 1 = c) : OneHotAt v NN c.toNat := by
  refine ⟨?_, ?_⟩
  · rcases hc with h | h <;> rw [h] <;> simp [NN]
  · intro j hj
    have : j = 0 ∨ j = 1 := by simp only [NN] at hj; omega
    rcases hc with h | h <;> rcases this with hj0 | hj0 <;> subst hj0 <;>
      simp [h0, h1, h]

/-- **`efrom` IS the along-axis source one-hot.** On the vertical branch (`iv = 1`) it is the row
one-hot at `fy`; on the horizontal branch (`iv = 0`) the column one-hot at `fx`. -/
theorem efrom_oneHot (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (mg : MoveGates b) (rg : OccReadGates b o ob)
    (hivb : (envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1) :
    ((envAt t i).loc (cIv o) = 1 →
        OneHotAt (fun j => (envAt t i).loc (cEfrom o j)) NN ((envAt t i).loc (cFy b)).toNat)
      ∧ ((envAt t i).loc (cIv o) = 0 →
        OneHotAt (fun j => (envAt t i).loc (cEfrom o j)) NN ((envAt t i).loc (cFx b)).toNat) := by
  set e := envAt t i with he
  obtain ⟨hfy, hr1, hr0⟩ :=
    oneHot_of_sat hsat hc i hi (cSelRow0 b) (cSelRow1 b) (cFy b) mg.srR0 mg.srR1 mg.srRs mg.srRi
  obtain ⟨hfx, hc1, hc0⟩ :=
    oneHot_of_sat hsat hc i hi (cSelCol0 b) (cSelCol1 b) (cFx b) mg.srC0 mg.srC1 mg.srCs mg.srCi
  rw [← he] at hfy hr1 hr0 hfx hc1 hc0
  have b0 : e.loc (cSelRow b 0) = 0 ∨ e.loc (cSelRow b 0) = 1 := by
    rcases hfy with h | h <;> rw [show cSelRow b 0 = cSelRow0 b from rfl, hr0, h] <;> norm_num
  have b1 : e.loc (cSelRow b 1) = 0 ∨ e.loc (cSelRow b 1) = 1 := by
    rcases hfy with h | h <;> rw [show cSelRow b 1 = cSelRow1 b from rfl, hr1, h] <;> norm_num
  have c0 : e.loc (cSelCol b 0) = 0 ∨ e.loc (cSelCol b 0) = 1 := by
    rcases hfx with h | h <;> rw [show cSelCol b 0 = cSelCol0 b from rfl, hc0, h] <;> norm_num
  have c1 : e.loc (cSelCol b 1) = 0 ∨ e.loc (cSelCol b 1) = 1 := by
    rcases hfx with h | h <;> rw [show cSelCol b 1 = cSelCol1 b from rfl, hc1, h] <;> norm_num
  have g0 := gatedSel_of_sat hsat hc i hi (cEfrom o 0) (cIv o) (cSelRow b 0) (cSelCol b 0)
      rg.efr0 hivb b0 c0
  have g1 := gatedSel_of_sat hsat hc i hi (cEfrom o 1) (cIv o) (cSelRow b 1) (cSelCol b 1)
      rg.efr1 hivb b1 c1
  rw [← he] at g0 g1
  constructor
  · intro hiv
    refine oneHot_pair hfy ?_ ?_
    · rw [g0, hiv]; rw [show cSelRow b 0 = cSelRow0 b from rfl] at *; rw [hr0]; ring
    · rw [g1, hiv]; rw [show cSelRow b 1 = cSelRow1 b from rfl] at *; rw [hr1]; ring
  · intro hiv
    refine oneHot_pair hfx ?_ ?_
    · rw [g0, hiv]; rw [show cSelCol b 0 = cSelCol0 b from rfl] at *; rw [hc0]; ring
    · rw [g1, hiv]; rw [show cSelCol b 1 = cSelCol1 b from rfl] at *; rw [hc1]; ring

/-- **`eto` IS the along-axis destination one-hot** — at `ty` on the vertical branch, `tx` on the
horizontal one, off the two unconditionally-pinned endpoint one-hots. -/
theorem eto_oneHot (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (rg : OccReadGates b o ob)
    (hivb : (envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1) :
    ((envAt t i).loc (cIv o) = 1 →
        OneHotAt (fun j => (envAt t i).loc (cEto o j)) NN ((envAt t i).loc (cTy b)).toNat)
      ∧ ((envAt t i).loc (cIv o) = 0 →
        OneHotAt (fun j => (envAt t i).loc (cEto o j)) NN ((envAt t i).loc (cTx b)).toNat) := by
  set e := envAt t i with he
  obtain ⟨hty, hy1, hy0⟩ :=
    oneHot_of_sat hsat hc i hi (cEty o 0) (cEty o 1) (cTy b) rg.ety0 rg.ety1 rg.etys rg.etyi
  obtain ⟨htx, hx1, hx0⟩ :=
    oneHot_of_sat hsat hc i hi (cEtx o 0) (cEtx o 1) (cTx b) rg.etx0 rg.etx1 rg.etxs rg.etxi
  rw [← he] at hty hy1 hy0 htx hx1 hx0
  have b0 : e.loc (cEty o 0) = 0 ∨ e.loc (cEty o 0) = 1 := by
    rcases hty with h | h <;> rw [hy0, h] <;> norm_num
  have b1 : e.loc (cEty o 1) = 0 ∨ e.loc (cEty o 1) = 1 := by
    rcases hty with h | h <;> rw [hy1, h] <;> norm_num
  have c0 : e.loc (cEtx o 0) = 0 ∨ e.loc (cEtx o 0) = 1 := by
    rcases htx with h | h <;> rw [hx0, h] <;> norm_num
  have c1 : e.loc (cEtx o 1) = 0 ∨ e.loc (cEtx o 1) = 1 := by
    rcases htx with h | h <;> rw [hx1, h] <;> norm_num
  have g0 := gatedSel_of_sat hsat hc i hi (cEto o 0) (cIv o) (cEty o 0) (cEtx o 0)
      rg.eto0 hivb b0 c0
  have g1 := gatedSel_of_sat hsat hc i hi (cEto o 1) (cIv o) (cEty o 1) (cEtx o 1)
      rg.eto1 hivb b1 c1
  rw [← he] at g0 g1
  refine ⟨fun hiv => oneHot_pair hty ?_ ?_, fun hiv => oneHot_pair htx ?_ ?_⟩
  · rw [g0, hiv, hy0]; ring
  · rw [g1, hiv, hy1]; ring
  · rw [g0, hiv, hx0]; ring
  · rw [g1, hiv, hx1]; ring

/-! ## §4 — `LineReadsVert` / `LineReadsHoriz`: the line columns really read the move's line.

`lineHead` emits BOTH scans into the SAME `line[k]` columns, the column-scan gated by `iv` and the
row-scan by `1−iv`. Contracting the gated scan against `validate_move`'s source one-hots turns
`line[k]` into the literal board cell at along-index `k` on the move's line — which, against the
board-alphabet range check (`boardvalid_of_sat`, DEFECT #4's fix), is vacuum iff the felt is `0`. -/

/-- The gated line-extract, contracted: `line[k]` is the `iv`-selected scan of the OLD board. The
gate-eval shape `hE` is supplied by the caller as `rfl` at each concrete `k`. -/
theorem line_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o k : Nat)
    (hgate : cgH (lineHead b o k) ∈ automataflResolveDesc.constraints)
    (hE : (headToExpr (lineHead b o k)).eval (envAt t i).loc
        = (envAt t i).loc (cLine o k)
          + (-1) * ((envAt t i).loc (cIv o) * (envAt t i).loc (cSelCol b 0)
              * (envAt t i).loc (old (k * NN + 0)))
          + (-1) * ((envAt t i).loc (cIv o) * (envAt t i).loc (cSelCol b 1)
              * (envAt t i).loc (old (k * NN + 1)))
          + (-1) * ((envAt t i).loc (cSelRow b 0) * (envAt t i).loc (old (0 * NN + k)))
          + (envAt t i).loc (cIv o) * (envAt t i).loc (cSelRow b 0)
              * (envAt t i).loc (old (0 * NN + k))
          + (-1) * ((envAt t i).loc (cSelRow b 1) * (envAt t i).loc (old (1 * NN + k)))
          + (envAt t i).loc (cIv o) * (envAt t i).loc (cSelRow b 1)
              * (envAt t i).loc (old (1 * NN + k)))
    (hivb : (envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1)
    (hc0 : (envAt t i).loc (cSelCol b 0) = 0 ∨ (envAt t i).loc (cSelCol b 0) = 1)
    (hc1 : (envAt t i).loc (cSelCol b 1) = 0 ∨ (envAt t i).loc (cSelCol b 1) = 1)
    (hr0 : (envAt t i).loc (cSelRow b 0) = 0 ∨ (envAt t i).loc (cSelRow b 0) = 1)
    (hr1 : (envAt t i).loc (cSelRow b 1) = 0 ∨ (envAt t i).loc (cSelRow b 1) = 1)
    (a0 : 0 ≤ (envAt t i).loc (old (k * NN + 0)) ∧ (envAt t i).loc (old (k * NN + 0)) ≤ 3)
    (a1 : 0 ≤ (envAt t i).loc (old (k * NN + 1)) ∧ (envAt t i).loc (old (k * NN + 1)) ≤ 3)
    (a2 : 0 ≤ (envAt t i).loc (old (0 * NN + k)) ∧ (envAt t i).loc (old (0 * NN + k)) ≤ 3)
    (a3 : 0 ≤ (envAt t i).loc (old (1 * NN + k)) ∧ (envAt t i).loc (old (1 * NN + k)) ≤ 3) :
    (envAt t i).loc (cLine o k)
      = (envAt t i).loc (cIv o)
          * ((envAt t i).loc (cSelCol b 0) * (envAt t i).loc (old (k * NN + 0))
             + (envAt t i).loc (cSelCol b 1) * (envAt t i).loc (old (k * NN + 1)))
        + (1 - (envAt t i).loc (cIv o))
          * ((envAt t i).loc (cSelRow b 0) * (envAt t i).loc (old (0 * NN + k))
             + (envAt t i).loc (cSelRow b 1) * (envAt t i).loc (old (1 * NN + k))) := by
  set e := envAt t i with he
  have hgt := rgateH hsat i hi hgate
  rw [hE] at hgt
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgt)
  obtain ⟨p0, q0⟩ := a0; obtain ⟨p1, q1⟩ := a1; obtain ⟨p2, q2⟩ := a2; obtain ⟨p3, q3⟩ := a3
  rcases hivb with h | h <;> rcases hc0 with h0 | h0 <;> rcases hc1 with h1 | h1 <;>
    rcases hr0 with h2 | h2 <;> rcases hr1 with h3 | h3 <;>
      rw [h, h0, h1, h2, h3] <;> exact ⟨by nlinarith, by nlinarith⟩

/-- A board column in the emitted alphabet decodes to VACUUM exactly when the felt is `0`. -/
theorem vacuum_iff_zero {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3) :
    (codeToParticle z).isVacuum = true ↔ z = 0 := by
  rcases hz with h | h | h | h <;> subst h <;>
    simp [codeToParticle, Particle.isVacuum]

/-- **`LineReadsVert`, DISCHARGED.** On the vertical branch the `line` columns read the OLD board
down the move's own column: `line k` is the felt of `(fx, k)`, hence `0` iff that cell is vacuum. -/
theorem lineReadsVert_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (mg : MoveGates b) (rg : OccReadGates b o ob)
    (hivb : (envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1)
    (hiv : (envAt t i).loc (cIv o) = 1) :
    LineReadsVert (fun k => (envAt t i).loc (cLine o k)) (boardDecodeOld (envAt t i))
      ((envAt t i).loc (cFx b)).toNat NN := by
  set e := envAt t i with he
  have halph := boardvalid_of_sat hsat hc i hi
  rw [← he] at halph
  have hb : ∀ c, c < KK → 0 ≤ e.loc (old c) ∧ e.loc (old c) ≤ 3 := by
    intro c hcK; rcases (halph c hcK).1 with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  obtain ⟨hfy, hr1, hr0⟩ :=
    oneHot_of_sat hsat hc i hi (cSelRow0 b) (cSelRow1 b) (cFy b) mg.srR0 mg.srR1 mg.srRs mg.srRi
  obtain ⟨hfx, hc1v, hc0v⟩ :=
    oneHot_of_sat hsat hc i hi (cSelCol0 b) (cSelCol1 b) (cFx b) mg.srC0 mg.srC1 mg.srCs mg.srCi
  rw [← he] at hfy hr1 hr0 hfx hc1v hc0v
  have bc0 : e.loc (cSelCol b 0) = 1 - e.loc (cFx b) := hc0v
  have bc1 : e.loc (cSelCol b 1) = e.loc (cFx b) := hc1v
  have br0 : e.loc (cSelRow b 0) = 1 - e.loc (cFy b) := hr0
  have br1 : e.loc (cSelRow b 1) = e.loc (cFy b) := hr1
  intro k hk
  have hk2 : k = 0 ∨ k = 1 := by simp only [NN] at hk; omega
  have hval : ∀ kk : Nat, kk < 2 →
      cgH (lineHead b o kk) ∈ automataflResolveDesc.constraints →
      (headToExpr (lineHead b o kk)).eval e.loc
        = e.loc (cLine o kk)
          + (-1) * (e.loc (cIv o) * e.loc (cSelCol b 0) * e.loc (old (kk * NN + 0)))
          + (-1) * (e.loc (cIv o) * e.loc (cSelCol b 1) * e.loc (old (kk * NN + 1)))
          + (-1) * (e.loc (cSelRow b 0) * e.loc (old (0 * NN + kk)))
          + e.loc (cIv o) * e.loc (cSelRow b 0) * e.loc (old (0 * NN + kk))
          + (-1) * (e.loc (cSelRow b 1) * e.loc (old (1 * NN + kk)))
          + e.loc (cIv o) * e.loc (cSelRow b 1) * e.loc (old (1 * NN + kk)) →
      e.loc (cLine o kk) = e.loc (old (kk * NN + (e.loc (cFx b)).toNat)) := by
    intro kk hkk hg hEq
    have hL := line_of_sat hsat hc i hi b o kk hg hEq hivb
      (by rw [bc0]; rcases hfx with h | h <;> rw [h] <;> norm_num)
      (by rw [bc1]; exact hfx)
      (by rw [br0]; rcases hfy with h | h <;> rw [h] <;> norm_num)
      (by rw [br1]; exact hfy)
      (hb _ (by simp only [KK, NN]; omega)) (hb _ (by simp only [KK, NN]; omega))
      (hb _ (by simp only [KK, NN]; omega)) (hb _ (by simp only [KK, NN]; omega))
    rw [← he] at hL
    rw [hL, hiv, bc0, bc1]
    rcases hfx with h | h <;> rw [h] <;> norm_num
  have hline : e.loc (cLine o k) = e.loc (old (k * NN + (e.loc (cFx b)).toNat)) := by
    rcases hk2 with h | h <;> subst h
    · exact hval 0 (by norm_num) rg.lin0 (by canon_head_eval [headToExpr, lineHead])
    · exact hval 1 (by norm_num) rg.lin1 (by canon_head_eval [headToExpr, lineHead])
  have hxlt : (e.loc (cFx b)).toNat < NN := by
    rcases hfx with h | h <;> rw [h] <;> simp [NN]
  have hidxK : k * NN + (e.loc (cFx b)).toNat < KK := by
    have : k < NN := by simpa [NN] using hk
    simp only [KK]; nlinarith [hxlt, this]
  have hcell : (boardDecodeOld e).cellAt ⟨(e.loc (cFx b)).toNat, k⟩
      = codeToParticle (e.loc (old (k * NN + (e.loc (cFx b)).toNat))) := by
    simp only [Board.cellAt, boardDecodeOld]
    exact if_pos (⟨hxlt, by simpa [NN] using hk⟩ : _ ∧ _)
  show e.loc (cLine o k) = 0 ↔ _
  rw [hline, hcell]
  exact (vacuum_iff_zero (halph _ hidxK).1).symm

/-- **`LineReadsHoriz`, DISCHARGED.** On the horizontal branch (`iv = 0`) the `line` columns read the
OLD board across the move's own row: `line k` is the felt of `(k, fy)`. -/
theorem lineReadsHoriz_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (mg : MoveGates b) (rg : OccReadGates b o ob)
    (hivb : (envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1)
    (hiv : (envAt t i).loc (cIv o) = 0) :
    LineReadsHoriz (fun k => (envAt t i).loc (cLine o k)) (boardDecodeOld (envAt t i))
      ((envAt t i).loc (cFy b)).toNat NN := by
  set e := envAt t i with he
  have halph := boardvalid_of_sat hsat hc i hi
  rw [← he] at halph
  have hb : ∀ c, c < KK → 0 ≤ e.loc (old c) ∧ e.loc (old c) ≤ 3 := by
    intro c hcK; rcases (halph c hcK).1 with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  obtain ⟨hfy, hr1, hr0⟩ :=
    oneHot_of_sat hsat hc i hi (cSelRow0 b) (cSelRow1 b) (cFy b) mg.srR0 mg.srR1 mg.srRs mg.srRi
  obtain ⟨hfx, hc1v, hc0v⟩ :=
    oneHot_of_sat hsat hc i hi (cSelCol0 b) (cSelCol1 b) (cFx b) mg.srC0 mg.srC1 mg.srCs mg.srCi
  rw [← he] at hfy hr1 hr0 hfx hc1v hc0v
  have bc0 : e.loc (cSelCol b 0) = 1 - e.loc (cFx b) := hc0v
  have bc1 : e.loc (cSelCol b 1) = e.loc (cFx b) := hc1v
  have br0 : e.loc (cSelRow b 0) = 1 - e.loc (cFy b) := hr0
  have br1 : e.loc (cSelRow b 1) = e.loc (cFy b) := hr1
  intro k hk
  have hk2 : k = 0 ∨ k = 1 := by simp only [NN] at hk; omega
  have hval : ∀ kk : Nat, kk < 2 →
      cgH (lineHead b o kk) ∈ automataflResolveDesc.constraints →
      (headToExpr (lineHead b o kk)).eval e.loc
        = e.loc (cLine o kk)
          + (-1) * (e.loc (cIv o) * e.loc (cSelCol b 0) * e.loc (old (kk * NN + 0)))
          + (-1) * (e.loc (cIv o) * e.loc (cSelCol b 1) * e.loc (old (kk * NN + 1)))
          + (-1) * (e.loc (cSelRow b 0) * e.loc (old (0 * NN + kk)))
          + e.loc (cIv o) * e.loc (cSelRow b 0) * e.loc (old (0 * NN + kk))
          + (-1) * (e.loc (cSelRow b 1) * e.loc (old (1 * NN + kk)))
          + e.loc (cIv o) * e.loc (cSelRow b 1) * e.loc (old (1 * NN + kk)) →
      e.loc (cLine o kk) = e.loc (old ((e.loc (cFy b)).toNat * NN + kk)) := by
    intro kk hkk hg hEq
    have hL := line_of_sat hsat hc i hi b o kk hg hEq hivb
      (by rw [bc0]; rcases hfx with h | h <;> rw [h] <;> norm_num)
      (by rw [bc1]; exact hfx)
      (by rw [br0]; rcases hfy with h | h <;> rw [h] <;> norm_num)
      (by rw [br1]; exact hfy)
      (hb _ (by simp only [KK, NN]; omega)) (hb _ (by simp only [KK, NN]; omega))
      (hb _ (by simp only [KK, NN]; omega)) (hb _ (by simp only [KK, NN]; omega))
    rw [← he] at hL
    rw [hL, hiv, br0, br1]
    rcases hfy with h | h <;> rw [h] <;> norm_num
  have hline : e.loc (cLine o k) = e.loc (old ((e.loc (cFy b)).toNat * NN + k)) := by
    rcases hk2 with h | h <;> subst h
    · exact hval 0 (by norm_num) rg.lin0 (by canon_head_eval [headToExpr, lineHead])
    · exact hval 1 (by norm_num) rg.lin1 (by canon_head_eval [headToExpr, lineHead])
  have hylt : (e.loc (cFy b)).toNat < NN := by
    rcases hfy with h | h <;> rw [h] <;> simp [NN]
  have hidxK : (e.loc (cFy b)).toNat * NN + k < KK := by
    have : k < NN := by simpa [NN] using hk
    simp only [KK]; nlinarith [hylt, this]
  have hcell : (boardDecodeOld e).cellAt ⟨k, (e.loc (cFy b)).toNat⟩
      = codeToParticle (e.loc (old ((e.loc (cFy b)).toNat * NN + k))) := by
    simp only [Board.cellAt, boardDecodeOld]
    exact if_pos (⟨by simpa [NN] using hk, hylt⟩ : _ ∧ _)
  show e.loc (cLine o k) = 0 ↔ _
  rw [hline, hcell]
  exact (vacuum_iff_zero (halph _ hidxK).1).symm

/-! ## §5 — `OsrcIsOtherSource`: the gated mask marks the OTHER move's moving source.

`ogHead` gates the passable comparison by the witnessed direction bit (`og = iv·eqx + (1−iv)·eqy`);
`oneHotGatedConstraints` then makes `osrc` a `og`-scaled one-hot at the other move's along-index. So
`osrc k = 1` exactly when `og = 1` (the other source shares this move's line) AND `k` is its
along-index — which, in `boardDecodeOld` terms, is `srcs.contains ⟨x,k⟩` for interior `k`. -/

/-- A generic `eq_scalar` extractor: `eq ∈ {0,1}` and `eq = 1 ↔ a = c`, for `{0,1}` columns `a,c`.
Generalises `iv_of_sat` (which is this at `a = fx`, `c = tx`). -/
theorem eqScalar_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (a c dsq neq bit0 eq : Nat)
    (hD : cgH ((((Head.lin 1 dsq).addProd (-1) [a, a]).addProd 2 [a, c]).addProd (-1) [c, c])
            ∈ automataflResolveDesc.constraints)
    (hG : Ge0Gates9 dsq neq bit0) (hP : EqPinGate eq neq)
    (ha : (envAt t i).loc a = 0 ∨ (envAt t i).loc a = 1)
    (hcc : (envAt t i).loc c = 0 ∨ (envAt t i).loc c = 1) :
    ((envAt t i).loc eq = 0 ∨ (envAt t i).loc eq = 1)
      ∧ ((envAt t i).loc eq = 1 ↔ (envAt t i).loc a = (envAt t i).loc c) := by
  set e := envAt t i with he
  have hdsq : e.loc dsq = (e.loc a - e.loc c) * (e.loc a - e.loc c) := by
    have hg := rgateH hsat i hi hD
    have hE : (headToExpr ((((Head.lin 1 dsq).addProd (-1) [a, a]).addProd 2 [a, c]).addProd
          (-1) [c, c])).eval e.loc
        = e.loc dsq + (-1) * (e.loc a * e.loc a) + 2 * (e.loc a * e.loc c)
          + (-1) * (e.loc c * e.loc c) := by canon_head_eval [headToExpr]
    rw [hE] at hg
    exact sq1d_pure (canon_loc hc i _) ha hcc hg
  have hbnd : -999 ≤ e.loc dsq ∧ e.loc dsq ≤ 999 := by
    rw [hdsq]; rcases ha with h1 | h1 <;> rcases hcc with h2 | h2 <;> rw [h1, h2] <;> norm_num
  obtain ⟨hnb, hn1, hn0⟩ := ge0_9_of_sat hsat hc i hi dsq neq bit0 hG hbnd.1 hbnd.2
  rw [← he] at hnb hn1 hn0
  have heq : e.loc eq = 1 - e.loc neq := by
    have := eqPin_of_sat hsat hc i hi eq neq hP hnb; rwa [← he] at this
  refine ⟨by rcases hnb with h | h <;> rw [heq, h] <;> norm_num, ?_⟩
  constructor
  · intro h1
    have hn : e.loc neq = 0 := by omega
    have := hn0 hn; rw [hdsq] at this
    rcases ha with a1 | a1 <;> rcases hcc with c1 | c1 <;> rw [a1, c1] at this ⊢ <;>
      first | rfl | (exfalso; revert this; norm_num)
  · intro heqac
    have hz : e.loc dsq = 0 := by rw [hdsq, heqac]; ring
    have hneq0 : e.loc neq = 0 := by
      rcases hnb with h | h
      · exact h
      · have := hn1 h; omega
    omega

/-- The `og`-gated `osrc` one-hot, extracted: `osrc j ∈ {0,1}`, `osrc 0 + osrc 1 = og`, and the RAW
index congruence `osrc 1 ≡ og·iv·fyOb + og·fxOb − og·iv·fxOb [ZMOD p]` (specialised per branch by the
caller before recovering the ℤ equality). -/
theorem osrc_arith (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (rg : OccReadGates b o ob) :
    ((envAt t i).loc (cOsrc o 0) = 0 ∨ (envAt t i).loc (cOsrc o 0) = 1)
      ∧ ((envAt t i).loc (cOsrc o 1) = 0 ∨ (envAt t i).loc (cOsrc o 1) = 1)
      ∧ (envAt t i).loc (cOsrc o 0) + (envAt t i).loc (cOsrc o 1) = (envAt t i).loc (cOg o)
      ∧ (envAt t i).loc (cOsrc o 1)
          ≡ (envAt t i).loc (cOg o) * (envAt t i).loc (cIv o) * (envAt t i).loc (cFy ob)
            + (envAt t i).loc (cOg o) * (envAt t i).loc (cFx ob)
            - (envAt t i).loc (cOg o) * (envAt t i).loc (cIv o) * (envAt t i).loc (cFx ob)
            [ZMOD 2013265921] := by
  set e := envAt t i with he
  have b0 : e.loc (cOsrc o 0) = 0 ∨ e.loc (cOsrc o 0) = 1 :=
    bin_of_gate (rgate hsat i hi rg.os0) (canon_loc hc i _)
  have b1 : e.loc (cOsrc o 1) = 0 ∨ e.loc (cOsrc o 1) = 1 :=
    bin_of_gate (rgate hsat i hi rg.os1) (canon_loc hc i _)
  have hsum : e.loc (cOsrc o 0) + e.loc (cOsrc o 1) = e.loc (cOg o) := by
    have hg := rgateH hsat i hi rg.osS
    have hE : (headToExpr ((Head.lin (-1) (cOg o)).addLin 1 (cOsrc o 0) |>.addLin 1 (cOsrc o 1))).eval
          e.loc = (-1) * e.loc (cOg o) + e.loc (cOsrc o 0) + e.loc (cOsrc o 1) := by canon_head_eval [headToExpr]
    rw [hE] at hg
    have hmod := (gate_modEq_iff (x := (-1) * e.loc (cOg o) + e.loc (cOsrc o 0) + e.loc (cOsrc o 1))
      (a := e.loc (cOsrc o 0) + e.loc (cOsrc o 1)) (b := e.loc (cOg o)) (by ring)).mp hg
    have hogc : Canon (e.loc (cOg o)) := canon_loc hc i _
    refine eq_of_modEq_canon ?_ hogc hmod
    rcases b0 with x | x <;> rcases b1 with y | y <;> rw [x, y] <;> exact ⟨by norm_num, by norm_num⟩
  refine ⟨b0, b1, hsum, ?_⟩
  have hg := rgateH hsat i hi rg.osI
  have hE : (headToExpr ((((Head.lin 0 (cOsrc o 0)).addLin 1 (cOsrc o 1)).addProd (-1)
        [cOg o, cIv o, cFy ob]).addProd (-1) [cOg o, cFx ob] |>.addProd 1
        [cOg o, cIv o, cFx ob] |>.addProd 0 [cOg o])).eval e.loc
      = e.loc (cOsrc o 1) + (-1) * (e.loc (cOg o) * e.loc (cIv o) * e.loc (cFy ob))
        + (-1) * (e.loc (cOg o) * e.loc (cFx ob))
        + e.loc (cOg o) * e.loc (cIv o) * e.loc (cFx ob) := by canon_head_eval [headToExpr]
  rw [hE] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- The passable GATE `og`: boolean, and on the vertical branch (`iv = 1`) it is `[fxOb = fx]`, on
the horizontal branch (`iv = 0`) it is `[fyOb = fy]`. -/
theorem og_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (rg : OccReadGates b o ob) (pg : PassGates b o ob)
    (hivb : (envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1)
    (hfxb : (envAt t i).loc (cFx b) = 0 ∨ (envAt t i).loc (cFx b) = 1)
    (hfyb : (envAt t i).loc (cFy b) = 0 ∨ (envAt t i).loc (cFy b) = 1)
    (hfxob : (envAt t i).loc (cFx ob) = 0 ∨ (envAt t i).loc (cFx ob) = 1)
    (hfyob : (envAt t i).loc (cFy ob) = 0 ∨ (envAt t i).loc (cFy ob) = 1) :
    ((envAt t i).loc (cOg o) = 0 ∨ (envAt t i).loc (cOg o) = 1)
      ∧ ((envAt t i).loc (cIv o) = 1 →
          ((envAt t i).loc (cOg o) = 1 ↔ (envAt t i).loc (cFx ob) = (envAt t i).loc (cFx b)))
      ∧ ((envAt t i).loc (cIv o) = 0 →
          ((envAt t i).loc (cOg o) = 1 ↔ (envAt t i).loc (cFy ob) = (envAt t i).loc (cFy b))) := by
  set e := envAt t i with he
  obtain ⟨heqxB, heqxM⟩ := eqScalar_of_sat hsat hc i hi (cFx ob) (cFx b) (cEqxDsq o) (cEqxNeq o)
    (eqxBit o 0) (cEqx o) pg.eqxD pg.eqxG pg.eqxP hfxob hfxb
  obtain ⟨heqyB, heqyM⟩ := eqScalar_of_sat hsat hc i hi (cFy ob) (cFy b) (cEqyDsq o) (cEqyNeq o)
    (cEqyNeq o + 1) (cEqy o) pg.eqyD pg.eqyG pg.eqyP hfyob hfyb
  rw [← he] at heqxB heqxM heqyB heqyM
  have hog := gatedSel_of_sat hsat hc i hi (cOg o) (cIv o) (cEqx o) (cEqy o) rg.ogG hivb heqxB heqyB
  rw [← he] at hog
  have hogb : e.loc (cOg o) = 0 ∨ e.loc (cOg o) = 1 := by
    rcases hivb with h | h <;> rcases heqxB with x | x <;> rcases heqyB with y | y <;>
      rw [hog, h, x, y] <;> norm_num
  refine ⟨hogb, ?_, ?_⟩
  · intro hiv
    rw [hog, hiv]; simp only [one_mul, sub_self, zero_mul, add_zero]
    exact heqxM
  · intro hiv
    rw [hog, hiv]; simp only [zero_mul, sub_zero, one_mul, zero_add]
    exact heqyM

/-- **`OsrcIsOtherSourceVert`, DISCHARGED.** On the vertical branch the gated mask marks exactly the
strictly-interior along-indices `k` at which `⟨fx, k⟩` is a source in `srcs = [thisSrc, otherSrc]` —
`thisSrc = ⟨fx, fy⟩` (the endpoint, excluded from the interior) and `otherSrc = ⟨fxOb, fyOb⟩`. -/
theorem osrcMeansVert_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (rg : OccReadGates b o ob) (pg : PassGates b o ob)
    (hivb : (envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1)
    (hiv : (envAt t i).loc (cIv o) = 1)
    (hfxb : (envAt t i).loc (cFx b) = 0 ∨ (envAt t i).loc (cFx b) = 1)
    (hfyb : (envAt t i).loc (cFy b) = 0 ∨ (envAt t i).loc (cFy b) = 1)
    (htyb : (envAt t i).loc (cTy b) = 0 ∨ (envAt t i).loc (cTy b) = 1)
    (hfxob : (envAt t i).loc (cFx ob) = 0 ∨ (envAt t i).loc (cFx ob) = 1)
    (hfyob : (envAt t i).loc (cFy ob) = 0 ∨ (envAt t i).loc (cFy ob) = 1) :
    OsrcIsOtherSourceVert (fun k => (envAt t i).loc (cOsrc o k))
      [⟨((envAt t i).loc (cFx b)).toNat, ((envAt t i).loc (cFy b)).toNat⟩,
       ⟨((envAt t i).loc (cFx ob)).toNat, ((envAt t i).loc (cFy ob)).toNat⟩]
      ((envAt t i).loc (cFx b)).toNat NN
      ((envAt t i).loc (cFy b)).toNat ((envAt t i).loc (cTy b)).toNat := by
  set e := envAt t i with he
  obtain ⟨os0b, os1b, hsum, hidx⟩ := osrc_arith hsat hc i hi b o ob rg
  rw [← he] at os0b os1b hsum hidx
  obtain ⟨hogb, hogV, _⟩ := og_of_sat hsat hc i hi b o ob rg pg hivb hfxb hfyb hfxob hfyob
  -- on the vertical branch: osrc1 = og·fyOb (ℤ), osrc0 = og·(1−fyOb)
  have hos1 : e.loc (cOsrc o 1) = e.loc (cOg o) * e.loc (cFy ob) := by
    have hmod : e.loc (cOsrc o 1) ≡ e.loc (cOg o) * e.loc (cFy ob) [ZMOD 2013265921] := by
      have := hidx; rw [hiv] at this
      calc e.loc (cOsrc o 1)
          ≡ e.loc (cOg o) * 1 * e.loc (cFy ob) + e.loc (cOg o) * e.loc (cFx ob)
            - e.loc (cOg o) * 1 * e.loc (cFx ob) [ZMOD 2013265921] := this
        _ = e.loc (cOg o) * e.loc (cFy ob) := by ring
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ hmod
    rcases hogb with h | h <;> rcases hfyob with y | y <;> rw [h, y] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hos0 : e.loc (cOsrc o 0) = e.loc (cOg o) * (1 - e.loc (cFy ob)) := by
    have := hsum; rw [hos1] at this; linarith [this]
  have hxlt : ((e.loc (cFx b)).toNat) < NN := by rcases hfxb with h | h <;> rw [h] <;> simp [NN]
  intro k hk hbet
  have hk2 : k = 0 ∨ k = 1 := by simp only [NN] at hk; omega
  have hfy_ne_k : (e.loc (cFy b)).toNat ≠ k := by
    -- the source endpoint is excluded from the interior
    rintro rfl; unfold Between at hbet; omega
  -- membership: ⟨fx,k⟩ ∈ [thisSrc, otherSrc] ↔ ⟨fx,k⟩ = otherSrc (this endpoint excluded)
  have hmem : (List.contains
        [(⟨(e.loc (cFx b)).toNat, (e.loc (cFy b)).toNat⟩ : Coord),
         ⟨(e.loc (cFx ob)).toNat, (e.loc (cFy ob)).toNat⟩]
        (⟨(e.loc (cFx b)).toNat, k⟩ : Coord) = true)
      ↔ ((e.loc (cFx ob)).toNat = (e.loc (cFx b)).toNat ∧ (e.loc (cFy ob)).toNat = k) := by
    rw [List.contains_eq_mem, decide_eq_true_iff]
    rw [List.mem_cons, List.mem_singleton]
    simp only [Coord.mk.injEq]
    constructor
    · rintro (⟨_, h⟩ | ⟨h1, h2⟩)
      · exact absurd h.symm hfy_ne_k
      · exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; right; exact ⟨h1.symm, h2.symm⟩
  rw [show (fun k => e.loc (cOsrc o k)) k = e.loc (cOsrc o k) from rfl, hmem]
  by_cases hog1 : e.loc (cOg o) = 1
  · -- og = 1 ⇒ fxOb = fx, and osrc is the one-hot at fyOb
    have hfxeq : e.loc (cFx ob) = e.loc (cFx b) := (hogV hiv).mp hog1
    have hfxeqN : (e.loc (cFx ob)).toNat = (e.loc (cFx b)).toNat := by rw [hfxeq]
    rcases hk2 with rfl | rfl
    · -- k = 0
      rw [hos0, hog1]; simp only [one_mul]
      constructor
      · intro h
        have : e.loc (cFy ob) = 0 := by rcases hfyob with y | y <;> rw [y] at h ⊢ <;> simp_all
        exact ⟨hfxeqN, by rw [this]; simp⟩
      · rintro ⟨_, h2⟩
        have : e.loc (cFy ob) = 0 := by
          rcases hfyob with y | y <;> rw [y] at h2 ⊢ <;> simp_all
        rw [this]; norm_num
    · -- k = 1
      rw [hos1, hog1]; simp only [one_mul]
      constructor
      · intro h; exact ⟨hfxeqN, by rw [h]; simp⟩
      · rintro ⟨_, h2⟩
        have : e.loc (cFy ob) = 1 := by
          rcases hfyob with y | y <;> rw [y] at h2 ⊢ <;> simp_all
        rw [this]
  · -- og = 0 ⇒ osrc ≡ 0 and fxOb ≠ fx
    have hog0 : e.loc (cOg o) = 0 := by
      rcases hogb with h | h
      · exact h
      · exact absurd h hog1
    have hfxne : ¬ (e.loc (cFx ob) = e.loc (cFx b)) := fun h => hog1 ((hogV hiv).mpr h)
    have hfxneN : (e.loc (cFx ob)).toNat ≠ (e.loc (cFx b)).toNat := by
      intro h; apply hfxne
      rcases hfxob with x | x <;> rcases hfxb with y | y <;> rw [x, y] at h ⊢ <;> simp_all
    constructor
    · intro h
      exfalso
      rcases hk2 with rfl | rfl
      · rw [hos0, hog0] at h; simp at h
      · rw [hos1, hog0] at h; simp at h
    · rintro ⟨h1, _⟩; exact absurd h1 hfxneN

/-- **`OsrcIsOtherSourceHoriz`, DISCHARGED.** The row-scan mirror: the gated mask marks the interior
along-indices `k` (an `x`-coordinate) at which `⟨k, fy⟩` is a source. -/
theorem osrcMeansHoriz_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (rg : OccReadGates b o ob) (pg : PassGates b o ob)
    (hivb : (envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1)
    (hiv : (envAt t i).loc (cIv o) = 0)
    (hfxb : (envAt t i).loc (cFx b) = 0 ∨ (envAt t i).loc (cFx b) = 1)
    (hfyb : (envAt t i).loc (cFy b) = 0 ∨ (envAt t i).loc (cFy b) = 1)
    (htxb : (envAt t i).loc (cTx b) = 0 ∨ (envAt t i).loc (cTx b) = 1)
    (hfxob : (envAt t i).loc (cFx ob) = 0 ∨ (envAt t i).loc (cFx ob) = 1)
    (hfyob : (envAt t i).loc (cFy ob) = 0 ∨ (envAt t i).loc (cFy ob) = 1) :
    OsrcIsOtherSourceHoriz (fun k => (envAt t i).loc (cOsrc o k))
      [⟨((envAt t i).loc (cFx b)).toNat, ((envAt t i).loc (cFy b)).toNat⟩,
       ⟨((envAt t i).loc (cFx ob)).toNat, ((envAt t i).loc (cFy ob)).toNat⟩]
      ((envAt t i).loc (cFy b)).toNat NN
      ((envAt t i).loc (cFx b)).toNat ((envAt t i).loc (cTx b)).toNat := by
  set e := envAt t i with he
  obtain ⟨os0b, os1b, hsum, hidx⟩ := osrc_arith hsat hc i hi b o ob rg
  rw [← he] at os0b os1b hsum hidx
  obtain ⟨hogb, _, hogV⟩ := og_of_sat hsat hc i hi b o ob rg pg hivb hfxb hfyb hfxob hfyob
  -- on the horizontal branch: osrc1 = og·fxOb (ℤ), osrc0 = og·(1−fxOb)
  have hos1 : e.loc (cOsrc o 1) = e.loc (cOg o) * e.loc (cFx ob) := by
    have hmod : e.loc (cOsrc o 1) ≡ e.loc (cOg o) * e.loc (cFx ob) [ZMOD 2013265921] := by
      have := hidx; rw [hiv] at this
      calc e.loc (cOsrc o 1)
          ≡ e.loc (cOg o) * 0 * e.loc (cFy ob) + e.loc (cOg o) * e.loc (cFx ob)
            - e.loc (cOg o) * 0 * e.loc (cFx ob) [ZMOD 2013265921] := this
        _ = e.loc (cOg o) * e.loc (cFx ob) := by ring
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ hmod
    rcases hogb with h | h <;> rcases hfxob with y | y <;> rw [h, y] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hos0 : e.loc (cOsrc o 0) = e.loc (cOg o) * (1 - e.loc (cFx ob)) := by
    have := hsum; rw [hos1] at this; linarith [this]
  have hylt : ((e.loc (cFy b)).toNat) < NN := by rcases hfyb with h | h <;> rw [h] <;> simp [NN]
  intro k hk hbet
  have hk2 : k = 0 ∨ k = 1 := by simp only [NN] at hk; omega
  have hfx_ne_k : (e.loc (cFx b)).toNat ≠ k := by
    rintro rfl; unfold Between at hbet; omega
  have hmem : (List.contains
        [(⟨(e.loc (cFx b)).toNat, (e.loc (cFy b)).toNat⟩ : Coord),
         ⟨(e.loc (cFx ob)).toNat, (e.loc (cFy ob)).toNat⟩]
        (⟨k, (e.loc (cFy b)).toNat⟩ : Coord) = true)
      ↔ ((e.loc (cFx ob)).toNat = k ∧ (e.loc (cFy ob)).toNat = (e.loc (cFy b)).toNat) := by
    rw [List.contains_eq_mem, decide_eq_true_iff]
    rw [List.mem_cons, List.mem_singleton]
    simp only [Coord.mk.injEq]
    constructor
    · rintro (⟨h, _⟩ | ⟨h1, h2⟩)
      · exact absurd h.symm hfx_ne_k
      · exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; right; exact ⟨h1.symm, h2.symm⟩
  rw [show (fun k => e.loc (cOsrc o k)) k = e.loc (cOsrc o k) from rfl, hmem]
  by_cases hog1 : e.loc (cOg o) = 1
  · have hfyeq : e.loc (cFy ob) = e.loc (cFy b) := (hogV hiv).mp hog1
    have hfyeqN : (e.loc (cFy ob)).toNat = (e.loc (cFy b)).toNat := by rw [hfyeq]
    rcases hk2 with rfl | rfl
    · rw [hos0, hog1]; simp only [one_mul]
      constructor
      · intro h
        have : e.loc (cFx ob) = 0 := by rcases hfxob with y | y <;> rw [y] at h ⊢ <;> simp_all
        exact ⟨by rw [this]; simp, hfyeqN⟩
      · rintro ⟨h1, _⟩
        have : e.loc (cFx ob) = 0 := by
          rcases hfxob with y | y <;> rw [y] at h1 ⊢ <;> simp_all
        rw [this]; norm_num
    · rw [hos1, hog1]; simp only [one_mul]
      constructor
      · intro h; exact ⟨by rw [h]; simp, hfyeqN⟩
      · rintro ⟨h1, _⟩
        have : e.loc (cFx ob) = 1 := by
          rcases hfxob with y | y <;> rw [y] at h1 ⊢ <;> simp_all
        rw [this]
  · have hog0 : e.loc (cOg o) = 0 := by
      rcases hogb with h | h
      · exact h
      · exact absurd h hog1
    have hfyne : ¬ (e.loc (cFy ob) = e.loc (cFy b)) := fun h => hog1 ((hogV hiv).mpr h)
    have hfyneN : (e.loc (cFy ob)).toNat ≠ (e.loc (cFy b)).toNat := by
      intro h; apply hfyne
      rcases hfyob with x | x <;> rcases hfyb with y | y <;> rw [x, y] at h ⊢ <;> simp_all
    constructor
    · intro h
      exfalso
      rcases hk2 with rfl | rfl
      · rw [hos0, hog0] at h; simp at h
      · rw [hos1, hog0] at h; simp at h
    · rintro ⟨_, h2⟩; exact absurd h2 hfyneN

/-! ## §6 — The line range, and the msum/occ column semantics. -/

open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (segVal msumVal Between OneHotAt)

/-- The `line` columns carry particle codes: `0 ≤ line k ≤ 3`. A convex combination (the one-hot
scans) of range-checked board cells. -/
theorem lineRange_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (mg : MoveGates b) (rg : OccReadGates b o ob)
    (hivb : (envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1) :
    ∀ k, k < NN → 0 ≤ (envAt t i).loc (cLine o k) ∧ (envAt t i).loc (cLine o k) ≤ 3 := by
  set e := envAt t i with he
  have halph := boardvalid_of_sat hsat hc i hi
  rw [← he] at halph
  have hb : ∀ c, c < KK → 0 ≤ e.loc (old c) ∧ e.loc (old c) ≤ 3 := by
    intro c hcK; rcases (halph c hcK).1 with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  obtain ⟨hfy, hr1, hr0⟩ :=
    oneHot_of_sat hsat hc i hi (cSelRow0 b) (cSelRow1 b) (cFy b) mg.srR0 mg.srR1 mg.srRs mg.srRi
  obtain ⟨hfx, hc1v, hc0v⟩ :=
    oneHot_of_sat hsat hc i hi (cSelCol0 b) (cSelCol1 b) (cFx b) mg.srC0 mg.srC1 mg.srCs mg.srCi
  rw [← he] at hfy hr1 hr0 hfx hc1v hc0v
  have bc0 : e.loc (cSelCol b 0) = 1 - e.loc (cFx b) := hc0v
  have bc1 : e.loc (cSelCol b 1) = e.loc (cFx b) := hc1v
  have br0 : e.loc (cSelRow b 0) = 1 - e.loc (cFy b) := hr0
  have br1 : e.loc (cSelRow b 1) = e.loc (cFy b) := hr1
  intro k hk
  have hk2 : k = 0 ∨ k = 1 := by simp only [NN] at hk; omega
  have hval : ∀ kk : Nat, kk < 2 → cgH (lineHead b o kk) ∈ automataflResolveDesc.constraints →
      (headToExpr (lineHead b o kk)).eval e.loc
        = e.loc (cLine o kk)
          + (-1) * (e.loc (cIv o) * e.loc (cSelCol b 0) * e.loc (old (kk * NN + 0)))
          + (-1) * (e.loc (cIv o) * e.loc (cSelCol b 1) * e.loc (old (kk * NN + 1)))
          + (-1) * (e.loc (cSelRow b 0) * e.loc (old (0 * NN + kk)))
          + e.loc (cIv o) * e.loc (cSelRow b 0) * e.loc (old (0 * NN + kk))
          + (-1) * (e.loc (cSelRow b 1) * e.loc (old (1 * NN + kk)))
          + e.loc (cIv o) * e.loc (cSelRow b 1) * e.loc (old (1 * NN + kk)) →
      0 ≤ e.loc (cLine o kk) ∧ e.loc (cLine o kk) ≤ 3 := by
    intro kk hkk hg hEq
    have hL := line_of_sat hsat hc i hi b o kk hg hEq hivb
      (by rw [bc0]; rcases hfx with h | h <;> rw [h] <;> norm_num) (by rw [bc1]; exact hfx)
      (by rw [br0]; rcases hfy with h | h <;> rw [h] <;> norm_num) (by rw [br1]; exact hfy)
      (hb _ (by simp only [KK, NN]; omega)) (hb _ (by simp only [KK, NN]; omega))
      (hb _ (by simp only [KK, NN]; omega)) (hb _ (by simp only [KK, NN]; omega))
    rw [← he] at hL
    rw [hL]
    have B0 := hb (kk * NN + 0) (by simp only [KK, NN]; omega)
    have B1 := hb (kk * NN + 1) (by simp only [KK, NN]; omega)
    have B2 := hb (0 * NN + kk) (by simp only [KK, NN]; omega)
    have B3 := hb (1 * NN + kk) (by simp only [KK, NN]; omega)
    rcases hivb with h | h <;> rcases hfx with x | x <;> rcases hfy with y | y <;>
      rw [h, bc0, bc1, br0, br1, x, y] <;> constructor <;> nlinarith [B0.1, B0.2, B1.1, B1.2, B2.1, B2.2, B3.1, B3.2]
  rcases hk2 with h | h <;> subst h
  · exact hval 0 (by norm_num) rg.lin0 (by canon_head_eval [headToExpr, lineHead])
  · exact hval 1 (by norm_num) rg.lin1 (by canon_head_eval [headToExpr, lineHead])

/-- The `occ` bit column, related to the semantic masked sum: `occ = 1 ↔ 1 ≤ msumVal (segVal …) …`.
The `seg` columns ARE `segVal` (the between-mask), `cMsum` IS `msumVal`, and `occ` IS the threshold —
all three from the emitted gates. At `NN = 2` the between-mask is empty so both sides vanish, but the
CONNECTING mechanism is the generic threshold extraction, not a hand-noted `0`. -/
theorem occ_col_iff_msumVal (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (o : Nat) (og : OccGates o)
    {efrom eto : Nat → ℤ} {af at_ : Nat}
    (hf : OneHotAt efrom NN af) (ht : OneHotAt eto NN at_) :
    ((envAt t i).loc (cOcc o) = 1)
      ↔ 1 ≤ msumVal (segVal efrom eto NN) (fun k => (envAt t i).loc (cOsrc o k))
              (fun k => (envAt t i).loc (cLine o k)) NN := by
  set e := envAt t i with he
  -- the seg columns are the empty between-mask (= 0 at NN=2)
  have hs0 : e.loc (cSeg o 0) = 0 := by
    have hg := rgateH hsat i hi og.seg0
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
      (by simpa only [show (headToExpr (segHead o 0)).eval (envAt t i).loc
              = (envAt t i).loc (cSeg o 0) from by canon_head_eval [headToExpr, segHead]] using hg)
  have hs1 : e.loc (cSeg o 1) = 0 := by
    have hg := rgateH hsat i hi og.seg1
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
      (by simpa only [show (headToExpr (segHead o 1)).eval (envAt t i).loc
              = (envAt t i).loc (cSeg o 1) from by canon_head_eval [headToExpr, segHead]] using hg)
  -- cMsum = 0 (masked sum over the empty mask), from the msum gate with seg columns 0
  have hcmsum0 : e.loc (cMsum o) = 0 := by
    have hg := rgateH hsat i hi og.msum
    have hE : (headToExpr (msumHead o)).eval e.loc
        = e.loc (cMsum o) + (-1) * (e.loc (cSeg o 0) * e.loc (cLine o 0))
          + e.loc (cSeg o 0) * e.loc (cOsrc o 0) * e.loc (cLine o 0)
          + (-1) * (e.loc (cSeg o 1) * e.loc (cLine o 1))
          + e.loc (cSeg o 1) * e.loc (cOsrc o 1) * e.loc (cLine o 1) := by canon_head_eval [headToExpr, msumHead]
    rw [hE, hs0, hs1] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  -- the SEMANTIC masked sum is also 0 at NN=2 (segVal is the empty between-mask)
  have hmsumval0 : msumVal (segVal efrom eto NN) (fun k => e.loc (cOsrc o k))
      (fun k => e.loc (cLine o k)) NN = 0 := by
    simp only [msumVal, show (NN : Nat) = 2 from rfl, List.range_succ, List.range_zero,
      List.map_cons, List.map_nil, List.map_append, List.sum_cons, List.sum_nil, List.sum_append,
      List.nil_append, segVal_n2 hf ht]; ring
  -- occ = [msum ≥ 1] via the 9-bit ge0 site; both sides degenerate to `1 ≤ 0`
  have hbnd : -999 ≤ e.loc (cMsum o) ∧ e.loc (cMsum o) ≤ 999 := by
    rw [hcmsum0]; constructor <;> norm_num
  obtain ⟨_, h1, h0⟩ := ge0_9_of_sat hsat hc i hi (cMsum o) (cOcc o) (occBit o 0) og.ge0 hbnd.1 hbnd.2
  rw [← he] at h1 h0
  rw [hmsumval0]
  constructor
  · intro h; have := h1 h; omega
  · intro h; omega

/-! ## §7 — THE OCCLUSION BRIDGE, UNCONDITIONAL off `Satisfied2`.

For move `which` (block `o = occBase which`, other move `ob = mvBase (1−which)`): the emitted
occlusion bit `cOcc o` equals the reference `Automatafl.occluded` of the decoded OLD board and the
decoded move, over the two decoded sources. Every hypothesis of the generic
`occ_eq_occluded_vert/horiz` is discharged from the gates (§3–§6); NONE survive. The direction bit
`iv` selects vertical vs horizontal, and it is itself pinned to the real geometry (`iv_of_sat`), so
the branch cannot disagree with the move.

At `NN = 2` both sides are `false` — but through the GENERIC threshold/mask/one-hot machinery, not a
hand-noted `0`. Raising `NN` makes the same statement non-degenerate with no new occlusion proof. -/
theorem occ_iff_occluded_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat)
    (mg : MoveGates (mvBase which)) (mgo : MoveGates (mvBase (1 - which)))
    (ig : IvGates (mvBase which) (occBase which))
    (rg : OccReadGates (mvBase which) (occBase which) (mvBase (1 - which)))
    (pg : PassGates (mvBase which) (occBase which) (mvBase (1 - which)))
    (og : OccGates (occBase which)) :
    ((envAt t i).loc (cOcc (occBase which)) = 1)
      ↔ Dregg2.Games.Automatafl.occluded (boardDecodeOld (envAt t i))
          [(moveDecode (envAt t i) which).frm, (moveDecode (envAt t i) (1 - which)).frm]
          (moveDecode (envAt t i) which) = true := by
  set e := envAt t i with he
  set b := mvBase which with hb
  set o := occBase which with ho
  set ob := mvBase (1 - which) with hob
  -- coordinate booleanity
  have hfxb : e.loc (cFx b) = 0 ∨ e.loc (cFx b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.fxBin mg.fxPin
  have hfyb : e.loc (cFy b) = 0 ∨ e.loc (cFy b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.fyBin mg.fyPin
  have htxb : e.loc (cTx b) = 0 ∨ e.loc (cTx b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.txBin mg.txPin
  have htyb : e.loc (cTy b) = 0 ∨ e.loc (cTy b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.tyBin mg.tyPin
  have hfxob : e.loc (cFx ob) = 0 ∨ e.loc (cFx ob) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mgo.fxBin mgo.fxPin
  have hfyob : e.loc (cFy ob) = 0 ∨ e.loc (cFy ob) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mgo.fyBin mgo.fyPin
  -- the witnessed direction bit and its geometric meaning
  obtain ⟨hivb, hivM⟩ := iv_of_sat hsat hc i hi b o ig hfxb htxb
  -- bounds and osrc booleanity (shared)
  have hlineRange := lineRange_of_sat hsat hc i hi b o ob mg rg hivb
  obtain ⟨os0b, os1b, _, _⟩ := osrc_arith hsat hc i hi b o ob rg
  have hosrc : ∀ k, k < NN → e.loc (cOsrc o k) = 0 ∨ e.loc (cOsrc o k) = 1 := by
    intro k hk
    have hk2 : k = 0 ∨ k = 1 := by simp only [NN] at hk; omega
    rcases hk2 with h | h <;> subst h
    · exact os0b
    · exact os1b
  -- toNat bounds
  have hfyn : (e.loc (cFy b)).toNat < NN := by rcases hfyb with h | h <;> rw [h] <;> simp [NN]
  have htyn : (e.loc (cTy b)).toNat < NN := by rcases htyb with h | h <;> rw [h] <;> simp [NN]
  have hfxn : (e.loc (cFx b)).toNat < NN := by rcases hfxb with h | h <;> rw [h] <;> simp [NN]
  have htxn : (e.loc (cTx b)).toNat < NN := by rcases htxb with h | h <;> rw [h] <;> simp [NN]
  by_cases hivv : e.loc (cIv o) = 1
  · -- VERTICAL branch: fx = tx
    have hvert : (moveDecode e which).frm.x = (moveDecode e which).to.x := by
      have : e.loc (cFx b) = e.loc (cTx b) := hivM.mp hivv
      simp only [moveDecode, ← hb]; rw [this]
    obtain ⟨hf1, _⟩ := efrom_oneHot hsat hc i hi b o ob mg rg hivb
    obtain ⟨ht1, _⟩ := eto_oneHot hsat hc i hi b o ob rg hivb
    have hfoh := hf1 hivv
    have htoh := ht1 hivv
    have hlineRead := lineReadsVert_of_sat hsat hc i hi b o ob mg rg hivb hivv
    have hosrcMeans := osrcMeansVert_of_sat hsat hc i hi b o ob rg pg hivb hivv
      hfxb hfyb htyb hfxob hfyob
    have hbr := occ_col_iff_msumVal hsat hc i hi o og hfoh htoh
    rw [hbr]
    exact occ_eq_occluded_vert hvert
      (show (moveDecode e which).frm.y < NN by simp only [moveDecode, ← hb]; exact hfyn)
      (show (moveDecode e which).to.y < NN by simp only [moveDecode, ← hb]; exact htyn)
      (by simp only [moveDecode, ← hb]; exact hfoh)
      (by simp only [moveDecode, ← hb]; exact htoh)
      hosrc hlineRange
      (by simp only [moveDecode, ← hb]; exact hlineRead)
      (by simp only [moveDecode, ← hb]; exact hosrcMeans)
  · -- HORIZONTAL branch: fx ≠ tx
    have hiv0 : e.loc (cIv o) = 0 := by
      rcases hivb with h | h
      · exact h
      · exact absurd h hivv
    have hhoriz : (moveDecode e which).frm.x ≠ (moveDecode e which).to.x := by
      have hne : e.loc (cFx b) ≠ e.loc (cTx b) := fun h => hivv (hivM.mpr h)
      simp only [moveDecode, ← hb]
      intro h
      apply hne
      rcases hfxb with x | x <;> rcases htxb with y | y <;> rw [x, y] at h ⊢ <;> simp_all
    obtain ⟨_, hf0⟩ := efrom_oneHot hsat hc i hi b o ob mg rg hivb
    obtain ⟨_, ht0⟩ := eto_oneHot hsat hc i hi b o ob rg hivb
    have hfoh := hf0 hiv0
    have htoh := ht0 hiv0
    have hlineRead := lineReadsHoriz_of_sat hsat hc i hi b o ob mg rg hivb hiv0
    have hosrcMeans := osrcMeansHoriz_of_sat hsat hc i hi b o ob rg pg hivb hiv0
      hfxb hfyb htxb hfxob hfyob
    have hbr := occ_col_iff_msumVal hsat hc i hi o og hfoh htoh
    rw [hbr]
    exact occ_eq_occluded_horiz hhoriz
      (show (moveDecode e which).frm.x < NN by simp only [moveDecode, ← hb]; exact hfxn)
      (show (moveDecode e which).to.x < NN by simp only [moveDecode, ← hb]; exact htxn)
      (by simp only [moveDecode, ← hb]; exact hfoh)
      (by simp only [moveDecode, ← hb]; exact htoh)
      hosrc hlineRange
      (by simp only [moveDecode, ← hb]; exact hlineRead)
      (by simp only [moveDecode, ← hb]; exact hosrcMeans)

end Bridge

/-! ## §8 — The instantiated bridge gate bundles, and axiom hygiene. -/

/-- The genuine occlusion bridge for move A, off `Satisfied2`, unconditional. -/
theorem occ_iff_occluded_a {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (cOcc (occBase 0)) = 1)
      ↔ Dregg2.Games.Automatafl.occluded (boardDecodeOld (envAt t i))
          [(moveDecode (envAt t i) 0).frm, (moveDecode (envAt t i) 1).frm]
          (moveDecode (envAt t i) 0) = true :=
  occ_iff_occluded_of_sat hsat hc i hi 0 moveGates_a moveGates_b ivGates_a occReadGates_a
    passGates_a occGates_a

/-- The genuine occlusion bridge for move B. -/
theorem occ_iff_occluded_b {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (cOcc (occBase 1)) = 1)
      ↔ Dregg2.Games.Automatafl.occluded (boardDecodeOld (envAt t i))
          [(moveDecode (envAt t i) 1).frm, (moveDecode (envAt t i) 0).frm]
          (moveDecode (envAt t i) 1) = true :=
  occ_iff_occluded_of_sat hsat hc i hi 1 moveGates_b moveGates_a ivGates_b occReadGates_b
    passGates_b occGates_b

#assert_axioms occ_iff_occluded_of_sat
#assert_axioms occ_iff_occluded_a
#assert_axioms occ_iff_occluded_b

end Dregg2.Circuit.Emit.AutomataflResolveRefine
