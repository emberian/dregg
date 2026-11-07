import Dregg2.Circuit.Emit.MinaWrapAggregationData
import Dregg2.Circuit.Emit.MinaWrapGroupGate
/-!
# Dregg2.Circuit.Emit.MinaWrapAggregationGate — the 47-term polyscale aggregation of a REAL
Mina devnet block's Wrap commitments, in-kernel.

RUNG 2 of the Wrap group check. `MinaWrapGroupGate` built `ft_comm`; this file folds it, together
with the other 46 commitments of Mina devnet block **539508**, into the aggregate that
`SRS::verify` feeds to its terminal `msm == 0`.

Separate module for a measured reason, not taste: at 47 terms the fold is ~12000 nested ladder
steps, and elaborating it alongside §1-6 took the single `lean` process to 14 GB before the
heartbeat cap stopped it. Split, each process stays bounded.

Facts below are `native_decide`, pinned `#assert_compiled` (since 2026-11-06); no `sorry`. NOT imported by the `Dregg2`
root, per house practice for gates.

⚑ **SPLIT (data ⇢ `MinaWrapAggregationData`).** `XI`, `COMBINE_POINTS`, `COMBINED_GOLD` and
`combinedComm` now live in `Dregg2.Circuit.Emit.MinaWrapAggregationData`, in THIS namespace,
imported below. The seven theorems are unchanged and `#assert_namespace_axioms` still covers the
whole namespace. The move exists because every importer of this gate wanted a literal and none
of them cites a theorem — so each was reducing four 47-term Pallas MSMs in the kernel to read a
list of coordinates.
-/

namespace Dregg2.Circuit.Emit.MinaWrapAggregationGate

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.MinaWrapGroupGate
  (Pt chunkedComm ftComm F_COMM_GOLD FT_COMM_GOLD)

set_option autoImplicit false
set_option maxRecDepth 20000000
set_option maxHeartbeats 4000000

/-- **`combine_points_are_on_pallas`** — all 47 are real Pallas points (the block's witness,
permutation, quotient and recursion commitments, and the verifier index's own), and so is the
aggregate, which is a finite point. -/
theorem combine_points_are_on_pallas :
    (COMBINE_POINTS.all (projOnCurveM pN curveB) && projOnCurveM pN curveB COMBINED_GOLD
      && !isInfM pN COMBINED_GOLD) = true := by native_decide

/-- **`combine_list_is_47_long`** — the count `verifier.rs` produces for this Wrap shape
(2 recursion + public + ft + z + 6 selectors + 15 w + 15 coefficients + 6 sigma), which is also
the `es_len` C8 folds over on the scalar side. -/
theorem combine_list_is_47_long : COMBINE_POINTS.length = 47 := by native_decide

/-- **`combine_slot_3_is_our_ftComm`** — the `ft_comm` slot of the aggregation IS the point §5
assembled. The two rungs are the same object, not two objects that happen to agree. -/
theorem combine_slot_3_is_our_ftComm :
    projEqM pN (COMBINE_POINTS.getD 3 Oproj) ftComm = true := by native_decide

/-- **`combinedComm_reproduces_kimchi`** — the 47-term Horner fold over the real commitments
reproduces o1-labs' aggregate. 46 further 255-bit ladders and 47 complete adds. -/
theorem combinedComm_reproduces_kimchi :
    projEqM pN combinedComm COMBINED_GOLD = true := by native_decide

/-- **`combinedComm_from_our_ftComm`** — and it still does when the `ft_comm` slot is filled by
the value the kernel ASSEMBLED in §5 (in its projective form, `Z != 1`) rather than the dumped
gold. This is the weld: `ft_comm` is consumed, not merely compared. -/
theorem combinedComm_from_our_ftComm :
    projEqM pN (chunkedComm XI (COMBINE_POINTS.set 3 ftComm)) COMBINED_GOLD = true := by native_decide

/-- **`tamper_polyscale`** — one added to `xi`. -/
theorem tamper_polyscale :
    projEqM pN (chunkedComm (XI + 1) COMBINE_POINTS) COMBINED_GOLD = false := by native_decide

/-- **`tamper_ft_slot`** — the `ft_comm` slot filled with a DIFFERENT real Pallas point from the
same block (`f_comm`, which differs from `ft_comm` by exactly the Maller term). A verifier that
skipped Maller's optimization lands here. -/
theorem tamper_ft_slot :
    projEqM pN (chunkedComm XI (COMBINE_POINTS.set 3 F_COMM_GOLD)) COMBINED_GOLD
      = false := by native_decide


-- Every theorem in this file is a fact about block 539508's data, checked by compiled evaluation and
-- pinned `#assert_compiled` below (since 2026-11-06), so there is no kernel-clean namespace to pin.

#assert_compiled tamper_ft_slot
#assert_compiled tamper_polyscale
#assert_compiled combinedComm_from_our_ftComm
#assert_compiled combinedComm_reproduces_kimchi
#assert_compiled combine_slot_3_is_our_ftComm
#assert_compiled combine_list_is_47_long
#assert_compiled combine_points_are_on_pallas
end Dregg2.Circuit.Emit.MinaWrapAggregationGate
