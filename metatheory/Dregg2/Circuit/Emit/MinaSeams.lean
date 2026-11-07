/-
# `Dregg2.Circuit.Emit.MinaSeams` — ⚑ THE THREE RUNNING SEAMS, AS OBJECTS. ξ, `v′`, fresh-sponge.

## What this file deploys

The three `cb.connect` groups that today force the Mina wrap tower's cross-descriptor conjuncts —
and that until now existed only as Rust index arithmetic plus prose — each as a `SeamSpec`:

* **`xiSeam`** — the 32 welds of `mina_wrap_finalize_fold::fold_endo_into_finalize`: the
  endo-lift's published ξ block IS the conjunction's published record-ξ block, limb for limb.
* **`vPrimeSeam`** — the 16 welds + 16 zero-pins of the kimchi gadget
  (`connect_chain_root_v_prime`'s content): the finalize root's `v′` block IS the low 128 bits of
  the phase-2 chain root's terminal squeeze.
* **`freshSpongeSeam`** — the 96 zero-pins: the chain root's incoming sponge state is `(0,0,0)`.

Each carries **S1** (the pin list names exactly the published slots it claims to — memberships in
the actual `EffectAir` leg lists, kernel-clean) and **S2** (`SeamCertifies`: left sentence ∧ right
sentence ∧ `SeamEq` → composed sentence, over the same objects the child files' theorems use —
`endoLiftQ`, `PastaIPA.bEval`, `Core.perm`). ⚑ S2 is shown REFUTABLE: `xi_seam_S2_needs_the_seam`
and `v_prime_seam_S2_needs_the_seam` prove the seam-dropped implication FALSE on concrete claims.

## ⚑ The port, and the census

`conjunctionPortedAir` declares PI block `[0, SK)` of `dregg-mina-wrap-conjunction::v1` a **PORT**
backed by the column island `[XI_SQ, XI_CL + SK)` — the object form of
`no_arithmetic_call_names_an_xi_block`, with FULL leg coverage (`portIslandFree`, compiled;
the kernel-clean partial theorems remain in the conjunction file). `zeta_is_not_a_port` is the red
pole. `xiPortCovered : CoveredPort` is the census: it does not elaborate unless a registered seam
covers every slot of the port, so a free-but-published block without a named seam is a build
failure, not a finding.

## ⚠ Standing, said plainly

A `SeamSpec` does not turn recursion wiring into AIR. The connects are still issued by
`circuit-prove` (`seam.rs::apply_seam`, a READER of the emitted JSON); the recursion circuit still
proves on a box and inherits the undischarged FRI/STARK floor. What changed: the seam's indices are
Lean-emitted with S1 naming their denotations, the composition is a named refutable theorem instead
of prose, and an uncovered port cannot elaborate.

## Axiom hygiene

Kernel-clean except where marked: the whole-leg-list island walks and the real-block chain facts
are `native_decide` + `#assert_compiled` (the conjunction file measured that the kernel cannot walk
the sound-multiply legs' `readCols`; the 46-permutation chain facts were always compiled). No
`sorry`, no `#guard`, no new axiom.
-/
import Dregg2.Circuit.Emit.SeamSpec
import Dregg2.Circuit.Emit.MinaWrapConjunctionAir
import Dregg2.Circuit.Emit.MinaWrapXiEndoLift
import Dregg2.Circuit.Emit.MinaPhase2Chain
import Dregg2.Circuit.Emit.MinaWrapOpeningGate
import Dregg2.Circuit.Emit.LightClientMinaAir
import Dregg2.Circuit.Emit.LightClientMinaLinkAir

namespace Dregg2.Circuit.Emit.MinaSeams

open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.Seam
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB limbAt qLimb)
open Dregg2.Circuit.Emit.PastaCurve (lambdaPallas)
open Dregg2.Circuit.Emit.MinaWrapXiEndoLift (endoLiftQ endoAir endoPIs VP OUT V_CHAL XI
  endoProg the_polyscale_is_the_endo_lift_of_the_squeeze
  the_emitted_pis_are_the_challenge_and_the_polyscale)
open Dregg2.Circuit.Emit.MinaWrapConjunctionAir (XI_SQ XI_CL ZETA ZETAW RSQ B_CL NCHAL CJ_PI_COUNT
  PI_XI PI_ZETA PI_ZETAW PI_R PI_B0 conjunctionAir)
open Dregg2.Circuit.Emit.LightClientMinaAir (CONJ_VK_LANES CHAINLINK_VK_LANES)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (Fq CHAL_F CHAL_INV_F)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §0 — THE CLAIM LAYOUTS, mirrored from the deployed readers.

The Rust sources of truth: `recursion-verify/src/chain_root.rs` (`in(96) ‖ out(96) ‖ acc(8)`),
`recursion-verify/src/kimchi_root.rs` and `circuit-prove/src/mina_wrap_finalize_fold.rs`
(`v′(32) ‖ ζ(32) ‖ ζω(32) ‖ r(32) ‖ b0(32)`). The leaf claims ARE the descriptors' PI vectors.
`circuit-prove/tests/seam_specs.rs` pins the emitted JSON against those readers, so a drift here is
a named red on the Rust side and a failed `rfl` on this one. -/

/-- The endo-lift leaf claim: its whole PI vector, `v′(32) ‖ ξ(32)`. -/
def ENDO_CLAIM_LEN : Nat := 2 * SK
/-- The conjunction leaf claim: its whole PI vector, `ξ(32) ‖ ζ(32) ‖ ζω(32) ‖ r(32) ‖ b0(32)`. -/
def CONJ_CLAIM_LEN : Nat := 5 * SK
/-- Three sponge lanes of 32 limbs. -/
def CHAIN_STATE_WIDTH : Nat := 3 * SK
/-- The chain root's ordered-transcript commitment width. -/
def CHAIN_ACC_WIDTH : Nat := 8
/-- The phase-2 chain ROOT claim: `in_state(96) ‖ out_state(96) ‖ acc(8)`. Claim slot `k` is chain
descriptor PI slot `k` for `k < 192` (the leaf expose copies the PI prefix; the fold preserves it —
`mina_phase2_chain_leaf.rs`), and the acc is fold-computed. -/
def CHAIN_CLAIM_LEN : Nat := 2 * CHAIN_STATE_WIDTH + CHAIN_ACC_WIDTH
/-- Claim offset of the chain root's outgoing lane 0 — descriptor PI slot `3·SK`. -/
def CHAIN_OUT_LANE0 : Nat := CHAIN_STATE_WIDTH
/-- The finalize root claim: `v′` block first (from the endo leaf), then the conjunction's four. -/
def FINALIZE_CLAIM_LEN : Nat := 5 * SK
/-- `v′ = LINK_V_RAW mod 2^128`, and `128 / SB = 16`. -/
def V_PRIME_LIMBS : Nat := 16
/-- The chain fold is 46 links, one absorbed pair per link. -/
def CHAIN_LINKS : Nat := 46

/-- ⚑ **THE FINALIZE CLAIM IS INDEX-ALIGNED WITH BOTH CHILDREN.** Slot `[0,SK)` is the endo leaf's
`v′` PI block at the SAME indices; slots `[SK, 5·SK)` are the conjunction's ζ/ζω/r/b0 PI blocks at
the SAME indices. This is why a seam against the finalize ROOT can name descriptor PI slots
directly. (The Rust twin is `the_claim_layout_has_no_aliasing`.) -/
theorem the_finalize_claim_is_index_aligned :
    PI_ZETA = SK ∧ PI_ZETAW = 2 * SK ∧ PI_R = 3 * SK ∧ PI_B0 = 4 * SK
      ∧ FINALIZE_CLAIM_LEN = CONJ_CLAIM_LEN ∧ CHAIN_OUT_LANE0 = 3 * SK
      ∧ V_PRIME_LIMBS * SB = 128 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, by decide⟩
  decide

/-! ## §1 — THE MEASURED FINGERPRINT LANES.

`CONJ_VK_LANES` and `CHAINLINK_VK_LANES` are `LightClientMinaAir`'s measured literals (one source;
a seam that copied them would be the two-constants-drift shape). The endo-lift had no Lean-side
lanes, so they are measured here. -/

/-- `effect_vm_descriptor2_semantic_fingerprint(dregg-mina-xi-endo-lift::v1)`, as `Faithful9` key
lanes. Measured 2026-08-08 by `circuit/examples/conj_fingerprint.rs` over the served artifact:

    circuit/descriptors/by-name/mina-xi-endo-lift.json  dregg-mina-xi-endo-lift::v1
    w=687  pi=64  cons=948
    fp=e3c8fbc7cb13d751cd4fb857e9aa097b4c550561cc84ca779650fbc03c8d231a

⚑ **RE-MEASURED 2026-08-11 AFTER THE CANONICAL-RECORD CHANGE.** `2ad7e48c8` changed the binary
record hashed for every descriptor even when its JSON did not move. The same served artifact now
fingerprints to `31ba24ea8831694c3c1b963fc8f2d12d93600680734eaa966ef93c31872b2ebf`, i.e. the
nine lanes below; the pure-Lean all-pin resolver independently reaches the same served descriptor.

⚠ FLAG DAY coupling: re-emitting `mina-xi-endo-lift.json` moves this literal and re-emits every
seam JSON that names it. The Rust reader (`seam.rs`) RECOMPUTES the lanes from the descriptor it
loads and refuses a mismatch, so a stale literal here is a loud red, not a silent misname. -/
def ENDO_VK_LANES : List ℤ :=
  [170179121, 55151687, 92720915, 65376383, 101266141, 121225219, 96098985, 283518879, 12529195]

/-! ## §2 — THE THREE SEAMS. -/

/-- ⚑ **THE ξ SEAM** — `fold_endo_into_finalize`'s 32 connects: endo claim slots `[SK, 2·SK)` (the
lifted ξ) welded to conjunction claim slots `[PI_XI, PI_XI + SK)` (the record's ξ). -/
def xiSeam : SeamSpec :=
  { name  := "dregg-seam-xi-endo-to-conjunction::v1"
  , left  := { claim := "mina-endo-leaf", claimLen := ENDO_CLAIM_LEN
             , descName := "dregg-mina-xi-endo-lift::v1", descLanes := ENDO_VK_LANES }
  , right := { claim := "mina-conjunction-leaf", claimLen := CONJ_CLAIM_LEN
             , descName := "dregg-mina-wrap-conjunction::v1", descLanes := CONJ_VK_LANES }
  , pins := (List.range SK).map (fun i => (SK + i, PI_XI + i))
  , zeroLeft := [], zeroRight := [] }

/-- ⚑ **THE `v′` SEAM** — the kimchi gadget's groups 2 and 3: chain-root claim slots
`[CHAIN_OUT_LANE0, +16)` (outgoing lane 0's low limbs) welded to finalize claim slots `[0, 16)`
(the `v′` block), and finalize slots `[16, 32)` zero-pinned (the truncation half of the "low 128
bits" reading — without it a prover picks 128 free high bits). -/
def vPrimeSeam : SeamSpec :=
  { name  := "dregg-seam-chain-vprime-to-finalize::v1"
  , left  := { claim := "mina-phase2-chain-root", claimLen := CHAIN_CLAIM_LEN
             , descName := "dregg-pasta-fq-chainlink::v1", descLanes := CHAINLINK_VK_LANES }
  , right := { claim := "mina-finalize-root", claimLen := FINALIZE_CLAIM_LEN
             , descName := "dregg-mina-xi-endo-lift::v1", descLanes := ENDO_VK_LANES }
  , pins := (List.range V_PRIME_LIMBS).map (fun i => (CHAIN_OUT_LANE0 + i, i))
  , zeroLeft := []
  , zeroRight := (List.range (SK - V_PRIME_LIMBS)).map (fun i => V_PRIME_LIMBS + i) }

/-- ⚑ **THE FRESH-SPONGE SEAM** — the gadget's group 1: the chain root's whole incoming state
`[0, 96)` zero-pinned. Before this was a constraint of the parent proof,
`ChainClaim::starts_from_a_fresh_sponge` was a HOST predicate a consumer could forget. The right
end is the finalize root (the fold's other child); no right-slot is touched. -/
def freshSpongeSeam : SeamSpec :=
  { name  := "dregg-seam-chain-fresh-sponge::v1"
  , left  := { claim := "mina-phase2-chain-root", claimLen := CHAIN_CLAIM_LEN
             , descName := "dregg-pasta-fq-chainlink::v1", descLanes := CHAINLINK_VK_LANES }
  , right := { claim := "mina-finalize-root", claimLen := FINALIZE_CLAIM_LEN
             , descName := "dregg-mina-xi-endo-lift::v1", descLanes := ENDO_VK_LANES }
  , pins := [], zeroLeft := List.range CHAIN_STATE_WIDTH, zeroRight := [] }

theorem xiSeam_wf : xiSeam.wf = true := by decide
theorem vPrimeSeam_wf : vPrimeSeam.wf = true := by decide
theorem freshSpongeSeam_wf : freshSpongeSeam.wf = true := by decide

/-! ## §3 — S1: the pin lists name exactly the published slots they claim to.

Each conjunct is a MEMBERSHIP in the actual `EffectAir` leg list — the pin leg publishing that
column at that PI slot exists in the deployed AIR object. Kernel-clean: the memberships are
constructed, not decided (`AirLeg` has no `DecidableEq`, and none is needed to BUILD a `Mem`). -/

/-- The endo leaf's claim slot `SK + i` is published by the `.last`-row pin of the machine's `OUT`
register — the lifted ξ (`the_machine_computes_the_endo_lift`). -/
theorem xi_seam_left_slot_publishes_the_lifted_block (i : Nat) (hi : i < SK) :
    AirLeg.pin ⟨VmRow.last, Dregg2.Circuit.Emit.MinaWrapCommitMachine.regCol OUT + i, SK + i⟩
      ∈ endoAir.legs := by
  show _ ∈ (Dregg2.Circuit.Emit.MinaWrapCommitMachine.commitAir qLimb
      (Dregg2.Circuit.Emit.MinaWrapCommitStages.instrs endoProg)).legs
    ++ Dregg2.Circuit.Emit.MinaWrapCommitStages.pinPair VP OUT
  refine List.mem_append_right _ ?_
  refine List.mem_append_right _ ?_
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- The endo leaf's claim slot `i` (`i < SK`) is published by the `.first`-row pin of the machine's
`VP` register — the prechallenge `v′`. This is also the right end of the `v′` seam: the finalize
claim's `v′` block is this block, index-aligned. -/
theorem v_prime_block_is_the_endo_input (i : Nat) (hi : i < SK) :
    AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapCommitMachine.regCol VP + i, 0 + i⟩
      ∈ endoAir.legs := by
  show _ ∈ (Dregg2.Circuit.Emit.MinaWrapCommitMachine.commitAir qLimb
      (Dregg2.Circuit.Emit.MinaWrapCommitStages.instrs endoProg)).legs
    ++ Dregg2.Circuit.Emit.MinaWrapCommitStages.pinPair VP OUT
  refine List.mem_append_right _ ?_
  refine List.mem_append_left _ ?_
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- The conjunction's claim slot `PI_XI + i` is published by the `.first`-row pin of `XI_CL` — the
deferred record's ξ, held on every row by the thread. -/
theorem xi_seam_right_slot_publishes_the_records_xi (i : Nat) (hi : i < SK) :
    AirLeg.pin ⟨VmRow.first, XI_CL + i, PI_XI + i⟩ ∈ conjunctionAir.legs := by
  show _ ∈ Dregg2.Circuit.Emit.MinaWrapConjunctionAir.bodyLegs
    ++ Dregg2.Circuit.Emit.MinaWrapConjunctionAir.threadLegs
  refine List.mem_append_left _ ?_
  show _ ∈ _ ++ Dregg2.Circuit.Emit.MinaWrapConjunctionAir.piPins
  refine List.mem_append_right _ ?_
  show _ ∈ ((((Dregg2.Circuit.Emit.MinaWrapConjunctionAir.pinBlock XI_CL PI_XI
      ++ _) ++ _) ++ _) ++ _)
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ ?_)))
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- ⚑ **S1 FOR THE ξ SEAM.** The pin list is exactly `{(SK + i, PI_XI + i) | i < SK}`, the left
slots are the endo-lift's published lifted-ξ block, and the right slots are the conjunction's
published record-ξ block. -/
theorem the_xi_seam_welds_the_lift_to_the_record :
    xiSeam.pins = (List.range SK).map (fun i => (SK + i, PI_XI + i))
    ∧ (∀ i, i < SK →
        AirLeg.pin ⟨VmRow.last, Dregg2.Circuit.Emit.MinaWrapCommitMachine.regCol OUT + i, SK + i⟩
          ∈ endoAir.legs)
    ∧ (∀ i, i < SK → AirLeg.pin ⟨VmRow.first, XI_CL + i, PI_XI + i⟩ ∈ conjunctionAir.legs) :=
  ⟨rfl, xi_seam_left_slot_publishes_the_lifted_block, xi_seam_right_slot_publishes_the_records_xi⟩

/-- The chain descriptor's PI slot `3·SK + i` is published by the `.last`-row pin of register 4 —
the OUTGOING sponge lane 0 (`the_outgoing_lanes_are_registers_4_5_0`). Claim slot
`CHAIN_OUT_LANE0 + i` is this PI slot (the claim's first 192 lanes are the PI prefix). -/
theorem chain_out_lane0_is_register_four (i : Nat) (hi : i < SK) :
    AirLeg.pin ⟨VmRow.last, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 4 + i, 3 * SK + i⟩
      ∈ Dregg2.Circuit.Emit.MinaPhase2Chain.chainAir.legs := by
  show _ ∈ (Dregg2.Circuit.Emit.MinaWrapVerifierProgram.programAir qLimb
      Dregg2.Circuit.Emit.MinaWrapVerifierSponge.absorbProg).legs
    ++ Dregg2.Circuit.Emit.MinaPhase2Chain.chainPins
  refine List.mem_append_right _ ?_
  show _ ∈ ((((((( Dregg2.Circuit.Emit.MinaWrapVerifierSponge.pinBlock VmRow.first 0 0
      ++ _) ++ _) ++ Dregg2.Circuit.Emit.MinaWrapVerifierSponge.pinBlock VmRow.last 4 (3 * SK))
      ++ _) ++ _) ++ _) ++ _)
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ ?_))))
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- The chain descriptor's incoming-state PI slots `b·SK + i` (`b < 3`) are published by the
`.first`-row pins of registers 0, 1, 2 — the whole incoming Poseidon state. -/
theorem chain_in_state_is_registers_0_1_2 (i : Nat) (hi : i < SK) :
    (AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 0 + i, 0 + i⟩
        ∈ Dregg2.Circuit.Emit.MinaPhase2Chain.chainAir.legs)
    ∧ (AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 1 + i, SK + i⟩
        ∈ Dregg2.Circuit.Emit.MinaPhase2Chain.chainAir.legs)
    ∧ (AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 2 + i,
          2 * SK + i⟩
        ∈ Dregg2.Circuit.Emit.MinaPhase2Chain.chainAir.legs) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · show _ ∈ (Dregg2.Circuit.Emit.MinaWrapVerifierProgram.programAir qLimb
          Dregg2.Circuit.Emit.MinaWrapVerifierSponge.absorbProg).legs
        ++ Dregg2.Circuit.Emit.MinaPhase2Chain.chainPins
      refine List.mem_append_right _ ?_
      show _ ∈ ((((((( Dregg2.Circuit.Emit.MinaWrapVerifierSponge.pinBlock VmRow.first 0 0
          ++ Dregg2.Circuit.Emit.MinaWrapVerifierSponge.pinBlock VmRow.first 1 SK)
          ++ Dregg2.Circuit.Emit.MinaWrapVerifierSponge.pinBlock VmRow.first 2 (2 * SK))
          ++ _) ++ _) ++ _) ++ _) ++ _)
      first
        | exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))))))
        | exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))))))
        | exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
              (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))))))

/-- ⚑ **S1 FOR THE `v′` SEAM** — the name `mina_kimchi_verifier_gadget.rs`'s R1 obligation asked
for. The pin list is exactly the low `V_PRIME_LIMBS` limbs of outgoing lane 0 (published by the
chain descriptor's register-4 `.last` pins) welded to the finalize `v′` block (published by the
endo-lift's `VP` `.first` pins), the zero-pins are exactly the remaining `SK − V_PRIME_LIMBS`
limbs, and the truncation width is 128 bits — below which the prechallenge genuinely lives
(`the_prechallenges_are_below_the_truncation`). -/
theorem the_v_prime_seam_is_the_terminal_squeeze :
    vPrimeSeam.pins = (List.range V_PRIME_LIMBS).map (fun i => (CHAIN_OUT_LANE0 + i, i))
    ∧ vPrimeSeam.zeroRight = (List.range (SK - V_PRIME_LIMBS)).map (fun i => V_PRIME_LIMBS + i)
    ∧ V_PRIME_LIMBS * SB = 128 ∧ V_CHAL < 2 ^ 128
    ∧ (∀ i, i < SK →
        AirLeg.pin ⟨VmRow.last, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 4 + i,
            3 * SK + i⟩
          ∈ Dregg2.Circuit.Emit.MinaPhase2Chain.chainAir.legs)
    ∧ (∀ i, i < SK →
        AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapCommitMachine.regCol VP + i, 0 + i⟩
          ∈ endoAir.legs) := by
  refine ⟨rfl, rfl, by decide, ?_, chain_out_lane0_is_register_four,
    v_prime_block_is_the_endo_input⟩
  exact Dregg2.Circuit.Emit.MinaWrapXiEndoLift.the_prechallenges_are_below_the_truncation.1

/-- ⚑ **S1 FOR THE FRESH-SPONGE SEAM.** The zero-pins are exactly the chain claim's whole incoming
state, those slots are the chain descriptor's register-0/1/2 `.first` pins, and "fresh" is
`PastaPoseidonFq.newSponge.st = [0, 0, 0]` — the state the reference sponge itself starts from. -/
theorem the_fresh_sponge_seam_zeroes_the_whole_incoming_state :
    freshSpongeSeam.zeroLeft = List.range CHAIN_STATE_WIDTH
    ∧ Dregg2.Circuit.Emit.PastaPoseidonFq.newSponge.st = [0, 0, 0]
    ∧ (∀ i, i < SK →
        (AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 0 + i, 0 + i⟩
            ∈ Dregg2.Circuit.Emit.MinaPhase2Chain.chainAir.legs)
        ∧ (AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 1 + i,
              SK + i⟩
            ∈ Dregg2.Circuit.Emit.MinaPhase2Chain.chainAir.legs)
        ∧ (AirLeg.pin ⟨VmRow.first, Dregg2.Circuit.Emit.MinaWrapVerifierProgram.regCol 2 + i,
              2 * SK + i⟩
            ∈ Dregg2.Circuit.Emit.MinaPhase2Chain.chainAir.legs)) :=
  ⟨rfl, rfl, chain_in_state_is_registers_0_1_2⟩

/-! ## §4 — CLAIM-BLOCK PLUMBING: `Renders` builders over `piBlock` concatenations. -/

open Dregg2.Circuit.Emit.MinaWrapCommitStages (piBlock)

private theorem length_piBlock (a : Nat) : (piBlock a).length = SK := by
  simp [Dregg2.Circuit.Emit.MinaWrapCommitStages.piBlock]

private theorem getD_piBlock_head (a : Nat) (rest : List ℤ) (i : Nat) (hi : i < SK) :
    (piBlock a ++ rest).getD i 0 = limbAt a i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [length_piBlock]; exact hi)]
  simp [Dregg2.Circuit.Emit.MinaWrapCommitStages.piBlock, hi]

private theorem getD_piBlock_skip (a : Nat) (rest : List ℤ) (i : Nat) :
    (piBlock a ++ rest).getD (SK + i) 0 = rest.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [length_piBlock]; omega),
    length_piBlock, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

private theorem renders_head {a : Nat} (rest : List ℤ) (ha : a < 2 ^ (SB * SK)) :
    Renders (piBlock a ++ rest) 0 a :=
  ⟨ha, fun i hi => by simpa using getD_piBlock_head a rest i hi⟩

private theorem renders_shift {rest : List ℤ} {lo s : Nat} (a : Nat)
    (h : Renders rest lo s) : Renders (piBlock a ++ rest) (SK + lo) s := by
  refine ⟨h.1, fun i hi => ?_⟩
  have harith : SK + lo + i = SK + (lo + i) := by omega
  rw [harith, getD_piBlock_skip]
  exact h.2 i hi

private theorem renders_last {a : Nat} (ha : a < 2 ^ (SB * SK)) : Renders (piBlock a) 0 a := by
  have h := renders_head (a := a) [] ha
  rwa [List.append_nil] at h

/-! ## §5 — ⚑ S2 FOR THE ξ SEAM, WITH BOTH POLES.

The sentences are stated over CLAIM VECTORS, in the same objects the child files' theorems use:
`endoLiftQ` (the tree's only `to_field`) on the left, `PastaIPA.bEval` (the function
`conjunction_forces` concludes against) on the right.

⚑ **Read `ConjLeafSays` honestly: its ξ coordinate appears in NO equation.** That is the wound,
carried into the sentence rather than papered over — the conjunction descriptor renders ξ and
derives nothing from it (`no_arithmetic_call_names_an_xi_block`; the port declaration in §8). The
composed sentence's crossing conjunct `xi = endoLiftQ lambdaPallas v'` is EXACTLY what only the
seam supplies, which is why dropping `SeamEq` makes S2 false (`xi_seam_S2_needs_the_seam`) instead
of merely unproved. -/

/-- What the endo leaf's claim says: the second block is the endomorphism lift of the first. -/
def EndoLeafSays (lv : List ℤ) : Prop :=
  ∃ v' : Nat, Renders lv 0 v' ∧ Renders lv SK (endoLiftQ lambdaPallas v')

/-- What the conjunction leaf's claim says: five rendered blocks; the carried challenge vector is
welded to its inverses; and `b0` is the `bEval` combination at ζ, ζω, `r`. ξ is rendered and — by
the AIR's own theorem — constrained by nothing here. -/
def ConjLeafSays (rv : List ℤ) : Prop :=
  ∃ (xi zeta zetaw r b0 : Nat) (chals chalinvs : List Fq),
    Renders rv PI_XI xi ∧ Renders rv PI_ZETA zeta ∧ Renders rv PI_ZETAW zetaw
    ∧ Renders rv PI_R r ∧ Renders rv PI_B0 b0
    ∧ chals.length = NCHAL ∧ chalinvs.length = NCHAL
    ∧ (∀ i, i < NCHAL → chals.getD i 0 * chalinvs.getD i 0 = 1)
    ∧ ((b0 : Fq) = Dregg2.Circuit.Emit.PastaIPA.bEval (zeta : Fq) chals
        + (r : Fq) * Dregg2.Circuit.Emit.PastaIPA.bEval (zetaw : Fq) chals)

/-- The finalize root's sentence: the conjunction's record-ξ IS the endo lift of the published
`v′` — the crossing conjunct — and the conjunction sentence holds. -/
def FinalizeRootSays (lv rv : List ℤ) : Prop :=
  ∃ v' xi : Nat, Renders lv 0 v' ∧ Renders rv PI_XI xi
    ∧ xi = endoLiftQ lambdaPallas v'
    ∧ ConjLeafSays rv

/-- ⚑ **S2 FOR THE ξ SEAM.** The 32 welds transport the lifted block onto the record block, so the
composed sentence's crossing conjunct follows. The proof crosses `Renders.eq_of_weld` — elementwise
limb equality at full width is value equality, no digest, no birthday bound. -/
theorem xi_seam_certifies : SeamCertifies xiSeam EndoLeafSays ConjLeafSays FinalizeRootSays := by
  rintro lv rv ⟨v', hv, hxiL⟩ hR hseam
  obtain ⟨xi, zeta, zetaw, r, b0, chals, chalinvs, hxiR, hrest⟩ := hR
  refine ⟨v', xi, hv, hxiR, ?_, xi, zeta, zetaw, r, b0, chals, chalinvs, hxiR, hrest⟩
  obtain ⟨hpins, -, -⟩ := hseam
  have hweld : ∀ i, i < SK → lv.getD (SK + i) 0 = rv.getD (PI_XI + i) 0 := fun i hi =>
    hpins (SK + i, PI_XI + i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  exact (Renders.eq_of_weld hxiL hxiR hweld).symm

/-- The ξ seam as a `CertifiedSeam` — the bundle that cannot be built without S2. -/
def xiCertifiedSeam : CertifiedSeam EndoLeafSays ConjLeafSays FinalizeRootSays :=
  { spec := xiSeam, wf := xiSeam_wf, certifies := xi_seam_certifies }

/-! ### §5a — the honest pole: the block's own claims satisfy everything, seam included. -/

/-- The honest endo-leaf claim IS the emitted PI vector. -/
def honestEndoClaim : List ℤ := endoPIs

private theorem honestEndo_as_blocks : honestEndoClaim = piBlock V_CHAL ++ piBlock XI := by
  show endoPIs = _
  rw [the_emitted_pis_are_the_challenge_and_the_polyscale,
    Dregg2.Circuit.Emit.MinaWrapCommitStages.piPair_is_two_blocks]

private theorem honestEndo_renders_vchal : Renders honestEndoClaim 0 V_CHAL := by
  rw [honestEndo_as_blocks]
  exact renders_head _ (by decide)

private theorem honestEndo_renders_xi : Renders honestEndoClaim SK XI := by
  rw [honestEndo_as_blocks]
  have h : Renders (piBlock V_CHAL ++ piBlock XI) (SK + 0) XI :=
    renders_shift _ (renders_last (by decide))
  simpa using h

theorem honestEndo_says : EndoLeafSays honestEndoClaim := by
  refine ⟨V_CHAL, honestEndo_renders_vchal, ?_⟩
  rw [the_polyscale_is_the_endo_lift_of_the_squeeze]
  exact honestEndo_renders_xi

/-- The real block's Wrap-side scalars, as canonical `Nat`s (the same values
`EmitMinaWrapConjunction` renders into the tracked conjunction fixture). -/
def ZETA_N : Nat := (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA).val
def ZETAW_N : Nat := (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETAW).val
def R_N : Nat := (Dregg2.Circuit.Emit.MinaRealBlockGate.UU).val
def B0_N : Nat := Dregg2.Circuit.Emit.MinaWrapOpeningGate.B0

/-- The honest conjunction-leaf claim: the block's own ξ, ζ, ζω, `r`, `b0`. -/
def honestConjClaim : List ℤ :=
  piBlock XI ++ (piBlock ZETA_N ++ (piBlock ZETAW_N ++ (piBlock R_N ++ piBlock B0_N)))

private theorem honestConj_renders_xi : Renders honestConjClaim PI_XI XI :=
  renders_head _ (by decide)

/-! ### §5b — ⚑ THE `bEval`/`bPoly` WELD, kernel-clean and general.

`PastaIPA.bEval` (what `conjunction_forces` concludes against — direct `x ^ 2^j` powers) and
`MinaWrapOpeningGate.bPoly` (what the block facts are proved against — a squaring tower,
deliberately, because a kernel `decide` through `x ^ 16384` via `npowRec` is linear and infeasible)
are two renderings of the SAME product. Until now nothing in the tree said so. This is the bridge
that lets the honest pole cite `b0_is_the_b_polynomial` instead of re-deciding a 15-round `bEval`
the kernel cannot afford. -/

private theorem sqTower_getD (x : Fq) :
    ∀ (n j : Nat), j < n →
      (Dregg2.Circuit.Emit.MinaWrapOpeningGate.sqTower x n).getD j 0 = x ^ 2 ^ j := by
  intro n
  induction n generalizing x with
  | zero => intro j hj; omega
  | succ m ih =>
      intro j hj
      cases j with
      | zero =>
          simp [Dregg2.Circuit.Emit.MinaWrapOpeningGate.sqTower]
      | succ k =>
          have hk : k < m := by omega
          show (Dregg2.Circuit.Emit.MinaWrapOpeningGate.sqTower (x * x) m).getD k 0 = _
          rw [ih (x * x) k hk]
          rw [← pow_two x, ← pow_mul]
          congr 1
          rw [pow_succ, Nat.mul_comm]

/-- Fold-congruence for a product accumulator over `List.range`. -/
private theorem foldl_mul_congr {f g : Nat → Fq} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    ∀ z : Fq, (List.range n).foldl (fun acc i => acc * f i) z
      = (List.range n).foldl (fun acc i => acc * g i) z := by
  induction n with
  | zero => intro z; rfl
  | succ m ih =>
      intro z
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (fun i hi => h i (by omega)) z, h m (by omega)]

private theorem bPoly_eq_prod (cs : List Fq) (x : Fq) :
    Dregg2.Circuit.Emit.MinaWrapOpeningGate.bPoly cs x
      = ((List.range cs.length).map
          (fun i => 1 + cs.getD i 0 * x ^ 2 ^ (cs.length - 1 - i))).prod := by
  unfold Dregg2.Circuit.Emit.MinaWrapOpeningGate.bPoly
  rw [List.prod_eq_foldl, List.foldl_map]
  exact foldl_mul_congr (fun i hi => by
    rw [sqTower_getD x cs.length (cs.length - 1 - i) (by omega)]) 1

private theorem bEval_eq_prod (x : Fq) (cs : List Fq) :
    Dregg2.Circuit.Emit.PastaIPA.bEval x cs
      = ((List.range cs.length).map
          (fun i => 1 + cs.getD i 0 * x ^ 2 ^ (cs.length - 1 - i))).prod := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      show Dregg2.Circuit.Emit.PastaIPA.bEval x rest * (1 + c * x ^ 2 ^ rest.length) = _
      rw [ih]
      simp only [List.length_cons]
      rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
      have htail :
          ((List.range rest.length).map
            ((fun i => 1 + (c :: rest).getD i 0 * x ^ 2 ^ (rest.length + 1 - 1 - i))
              ∘ Nat.succ)).prod
          = ((List.range rest.length).map
              (fun i => 1 + rest.getD i 0 * x ^ 2 ^ (rest.length - 1 - i))).prod := by
        refine congrArg List.prod (List.map_congr_left (fun i hi => ?_))
        have hi' := List.mem_range.mp hi
        simp only [Function.comp_apply, List.getD_cons_succ]
        have he : rest.length + 1 - 1 - Nat.succ i = rest.length - 1 - i := by omega
        rw [he]
      rw [htail]
      have hhead : 1 + (c :: rest).getD 0 0 * x ^ 2 ^ (rest.length + 1 - 1 - 0)
          = 1 + c * x ^ 2 ^ rest.length := by
        simp
      rw [hhead]
      ring

/-- ⚑ **THE WELD OF THE TWO b-POLYNOMIAL IMPLEMENTATIONS.** General, kernel-clean. -/
theorem bEval_eq_bPoly (x : Fq) (cs : List Fq) :
    Dregg2.Circuit.Emit.PastaIPA.bEval x cs
      = Dregg2.Circuit.Emit.MinaWrapOpeningGate.bPoly cs x := by
  rw [bEval_eq_prod, bPoly_eq_prod]

private instance : NeZero qN := ⟨by decide⟩

/-- The cast facts the honest pole needs: `.val` round-trips on the block's scalars. -/
private theorem casts_roundtrip :
    ((ZETA_N : ℕ) : Fq) = Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA
    ∧ ((ZETAW_N : ℕ) : Fq) = Dregg2.Circuit.Emit.MinaRealBlockGate.ZETAW
    ∧ ((R_N : ℕ) : Fq) = Dregg2.Circuit.Emit.MinaRealBlockGate.UU := by
  refine ⟨ZMod.natCast_rightInverse _, ZMod.natCast_rightInverse _,
    ZMod.natCast_rightInverse _⟩

theorem honestConj_says : ConjLeafSays honestConjClaim := by
  refine ⟨XI, ZETA_N, ZETAW_N, R_N, B0_N, CHAL_F, CHAL_INV_F,
    honestConj_renders_xi,
    ?_, ?_, ?_, ?_, by decide, by decide, by decide, ?_⟩
  · exact renders_shift _ (renders_head _ (by decide))
  · show Renders honestConjClaim (2 * SK) ZETAW_N
    have h : Renders honestConjClaim (SK + (SK + 0)) ZETAW_N :=
      renders_shift _ (renders_shift _ (renders_head _ (by decide)))
    exact h
  · show Renders honestConjClaim (3 * SK) R_N
    have h : Renders honestConjClaim (SK + (SK + (SK + 0))) R_N :=
      renders_shift _ (renders_shift _ (renders_shift _ (renders_head _ (by decide))))
    exact h
  · show Renders honestConjClaim (4 * SK) B0_N
    have h : Renders honestConjClaim (SK + (SK + (SK + (SK + 0)))) B0_N :=
      renders_shift _ (renders_shift _ (renders_shift _ (renders_shift _
        (renders_last (by decide)))))
    exact h
  · obtain ⟨hz, hzw, hr⟩ := casts_roundtrip
    rw [hz, hzw, hr, bEval_eq_bPoly, bEval_eq_bPoly]
    exact Dregg2.Circuit.Emit.MinaWrapOpeningGate.b0_is_the_b_polynomial.symm

/-- ⚑ **THE HONEST POLE** — `SeamEq` is INHABITED at the block's own claims and the composed
sentence holds there. Without this, `xi_seam_certifies` could be green over an unsatisfiable
`SeamEq` and certify nothing. -/
theorem the_xi_seam_composes_on_the_block :
    SeamEq xiSeam honestEndoClaim honestConjClaim
    ∧ FinalizeRootSays honestEndoClaim honestConjClaim := by
  constructor
  · refine ⟨?_, by simp [xiSeam], by simp [xiSeam]⟩
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hiSK := List.mem_range.mp hi
    show honestEndoClaim.getD (SK + i) 0 = honestConjClaim.getD (PI_XI + i) 0
    rw [honestEndo_renders_xi.2 i hiSK, honestConj_renders_xi.2 i hiSK]
  · exact ⟨V_CHAL, XI, honestEndo_renders_vchal, honestConj_renders_xi,
      the_polyscale_is_the_endo_lift_of_the_squeeze.symm, honestConj_says⟩

/-! ### §5c — ⚑⚑ THE RED POLE: S2 WITHOUT ITS SEAM HYPOTHESIS IS FALSE.

Not unprovable — FALSE, on concrete claims: the block's own honest endo leaf against a fully
sentence-satisfying conjunction claim whose ξ block carries `0`. Both child sentences hold; the
composed sentence does not, because nothing relates the two ξ blocks. A composition theorem that
survived this deletion would be `P → P` wearing a name. -/

/-- A conjunction claim that satisfies `ConjLeafSays` with ξ = 0: ζ = ζω = 0 collapses `bEval` to
`1` (`bEval_zero`), so `b0 = 1 + r`. Every gate-sentence holds; only the seam is betrayed. -/
def forgedConjClaim : List ℤ :=
  piBlock 0 ++ (piBlock 0 ++ (piBlock 0 ++ (piBlock 3 ++ piBlock 4)))

private theorem bEval_zero (cs : List Fq) :
    Dregg2.Circuit.Emit.PastaIPA.bEval (0 : Fq) cs = 1 := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      show Dregg2.Circuit.Emit.PastaIPA.bEval (0 : Fq) rest
          * (1 + c * (0 : Fq) ^ 2 ^ rest.length) = 1
      rw [ih, zero_pow (Nat.two_pow_pos rest.length).ne']
      ring

private theorem forgedConj_renders_zero : Renders forgedConjClaim PI_XI 0 :=
  renders_head _ (by decide)

theorem forgedConj_says : ConjLeafSays forgedConjClaim := by
  refine ⟨0, 0, 0, 3, 4, List.replicate NCHAL 1, List.replicate NCHAL 1,
    forgedConj_renders_zero,
    renders_shift _ (renders_head _ (by decide)), ?_, ?_, ?_,
    by simp, by simp, by decide, ?_⟩
  · show Renders forgedConjClaim (2 * SK) 0
    have h : Renders forgedConjClaim (SK + (SK + 0)) 0 :=
      renders_shift _ (renders_shift _ (renders_head _ (by decide)))
    exact h
  · show Renders forgedConjClaim (3 * SK) 3
    have h : Renders forgedConjClaim (SK + (SK + (SK + 0))) 3 :=
      renders_shift _ (renders_shift _ (renders_shift _ (renders_head _ (by decide))))
    exact h
  · show Renders forgedConjClaim (4 * SK) 4
    have h : Renders forgedConjClaim (SK + (SK + (SK + (SK + 0)))) 4 :=
      renders_shift _ (renders_shift _ (renders_shift _ (renders_shift _
        (renders_last (by decide)))))
    exact h
  · simp only [Nat.cast_zero, bEval_zero]
    norm_num

/-- ⚑⚑ **THE REFUTER.** Delete `SeamEq` from S2 and the implication is FALSE. Kernel-clean: the
witnesses are the block's honest endo claim and `forgedConjClaim`, and the contradiction is
`0 ≠ XI` — the lift the seam would have forced the record to carry. -/
theorem xi_seam_S2_needs_the_seam :
    ¬ (∀ lv rv, EndoLeafSays lv → ConjLeafSays rv → FinalizeRootSays lv rv) := by
  intro h
  obtain ⟨v', xi, hv, hxi, hlift, -⟩ :=
    h honestEndoClaim forgedConjClaim honestEndo_says forgedConj_says
  have hv' : v' = V_CHAL :=
    Renders.eq_of_weld hv honestEndo_renders_vchal (fun _ _ => rfl)
  have hxi0 : xi = 0 :=
    Renders.eq_of_weld hxi forgedConj_renders_zero (fun _ _ => rfl)
  rw [hv', the_polyscale_is_the_endo_lift_of_the_squeeze] at hlift
  rw [hxi0] at hlift
  exact absurd hlift.symm (by decide : XI ≠ 0)

/-! ## §6 — THE CHAIN SENTENCES, AND S2 FOR THE `v′` AND FRESH-SPONGE SEAMS. -/

/-- One absorb link over an arbitrary pair — the SAME step `MinaPhase2Chain.linkStep` runs, with
the tape abstracted. -/
def absorbStep (st : List Nat) (p : Nat × Nat) : List Nat :=
  Dregg2.Circuit.Emit.PastaPoseidonFq.Core.perm fqParams
    [(st.getD 0 0 + p.1) % qN, (st.getD 1 0 + p.2) % qN, st.getD 2 0]

/-- The chain fold over a tape of absorbed pairs. -/
def absorbFold (init : List Nat) : List (Nat × Nat) → List Nat
  | [] => init
  | p :: rest => absorbFold (absorbStep init p) rest

theorem absorbFold_append (init : List Nat) (a b : List (Nat × Nat)) :
    absorbFold init (a ++ b) = absorbFold (absorbFold init a) b := by
  induction a generalizing init with
  | nil => rfl
  | cons p t ih =>
      simp only [List.cons_append, absorbFold]
      exact ih _

/-- ⚑ The abstract fold IS `MinaPhase2Chain.chainState` at the block's own tape — structural, no
permutation evaluated. -/
theorem absorbFold_is_the_chain (n : Nat) :
    absorbFold Dregg2.Circuit.Emit.PastaPoseidonFq.newSponge.st
        ((List.range n).map Dregg2.Circuit.Emit.MinaPhase2Chain.linkX)
      = Dregg2.Circuit.Emit.MinaPhase2Chain.chainState n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [List.range_succ, List.map_append, absorbFold_append, ih]
      rfl

/-- What the chain fold ROOT's claim says: its in-state and out-state blocks render a 3-lane pair
related by the 46-link absorb fold over SOME tape. ⚠ WHICH tape is the `transcript_acc` HOST
comparison's business (`mina_kimchi_verifier_gadget` §"WHAT THE ROOT DOES NOT SAY" item 0) — the
tape here is existential, faithfully. -/
def ChainRootSays (cv : List ℤ) : Prop :=
  ∃ (inSt outSt : List Nat) (tape : List (Nat × Nat)),
    inSt.length = 3 ∧ outSt.length = 3 ∧ tape.length = CHAIN_LINKS
    ∧ (∀ k, k < 3 → Renders cv (k * SK) (inSt.getD k 0))
    ∧ (∀ k, k < 3 → Renders cv (CHAIN_STATE_WIDTH + k * SK) (outSt.getD k 0))
    ∧ outSt = absorbFold inSt tape

/-- The right end's needed sentence: the finalize root publishes a canonical `v′` block. -/
def FinalizePublishesVPrime (rv : List ℤ) : Prop := ∃ v' : Nat, Renders rv 0 v'

/-- The `v′` composition: the published `v′` IS the low 128 bits of the chain's terminal
squeeze — `the_chain_ends_at_the_blocks_challenges`' reading, as a sentence about two claims. -/
def KimchiVPrimeSays (cv rv : List ℤ) : Prop :=
  ∃ (outLane0 v' : Nat), Renders cv CHAIN_OUT_LANE0 outLane0 ∧ Renders rv 0 v'
    ∧ v' = outLane0 % 2 ^ 128

/-- ⚑ **S2 FOR THE `v′` SEAM.** The 16 welds carry the low limbs; the 16 zero-pins force the high
limbs; `Seam.prefix_weld` is the arithmetic that turns the pair into `v' = outLane0 mod 2^128`. -/
theorem v_prime_seam_certifies :
    SeamCertifies vPrimeSeam ChainRootSays FinalizePublishesVPrime KimchiVPrimeSays := by
  rintro cv rv ⟨inSt, outSt, tape, -, -, -, -, hout, -⟩ ⟨v', hv⟩ hseam
  obtain ⟨hpins, -, hzr⟩ := hseam
  have hout0 : Renders cv CHAIN_OUT_LANE0 (outSt.getD 0 0) := by
    have h := hout 0 (by omega)
    exact h
  refine ⟨outSt.getD 0 0, v', hout0, hv, ?_⟩
  have h128 : (2 : Nat) ^ 128 = 2 ^ (SB * V_PRIME_LIMBS) := by decide
  rw [h128]
  refine prefix_weld (by decide) hv hout0 ?_ ?_
  · intro i hi
    have h := hpins (CHAIN_OUT_LANE0 + i, i)
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simpa using h.symm
  · intro i h16 hiSK
    have hVP : V_PRIME_LIMBS = 16 := rfl
    have hSK32 : SK = 32 := rfl
    have h := hzr i (List.mem_map.mpr
      ⟨i - V_PRIME_LIMBS, List.mem_range.mpr (by omega), by omega⟩)
    simpa using h

/-- What the fresh-sponge seam buys, composed: the SAME chain sentence with the in-state no longer
existential — it is the fresh sponge, `newSponge.st`. -/
def ChainStartsFresh (cv : List ℤ) : Prop :=
  ∃ (outSt : List Nat) (tape : List (Nat × Nat)),
    outSt.length = 3 ∧ tape.length = CHAIN_LINKS
    ∧ (∀ k, k < 3 → Renders cv (CHAIN_STATE_WIDTH + k * SK) (outSt.getD k 0))
    ∧ outSt = absorbFold Dregg2.Circuit.Emit.PastaPoseidonFq.newSponge.st tape

/-- ⚑ **S2 FOR THE FRESH-SPONGE SEAM.** 96 zero-pins collapse the rendered in-state to `[0,0,0]` —
which IS `newSponge.st`, so the fold's origin stops being a prover choice.

⚠ REFUTABILITY, stated honestly: this S2's composed sentence quantifies the tape existentially
(as the root genuinely does), and refuting the seam-dropped form would require exhibiting a state
UNREACHABLE from the fresh sponge under every tape — inverting Poseidon. The load-bearing refuters
live on the ξ and `v′` seams; this seam's zero-pins are the same mechanism at the same width. -/
theorem fresh_sponge_seam_certifies :
    SeamCertifies freshSpongeSeam ChainRootSays (fun _ => True) (fun cv _ => ChainStartsFresh cv) := by
  rintro cv rv ⟨inSt, outSt, tape, hinlen, houtlen, htlen, hin, hout, hfold⟩ - hseam
  obtain ⟨-, hzl, -⟩ := hseam
  have hz : ∀ k, k < 3 → inSt.getD k 0 = 0 := by
    intro k hk
    refine (hin k hk).eq_zero ?_
    intro i hi
    refine hzl (k * SK + i) (List.mem_range.mpr ?_)
    have hSK : SK = 32 := rfl
    have hW : CHAIN_STATE_WIDTH = 96 := rfl
    rw [hSK] at hi
    rw [hSK, hW]
    omega
  have hfresh : inSt = Dregg2.Circuit.Emit.PastaPoseidonFq.newSponge.st := by
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hinlen
    have h0 : a = 0 := by simpa using hz 0 (by omega)
    have h1 : b = 0 := by simpa using hz 1 (by omega)
    have h2 : c = 0 := by simpa using hz 2 (by omega)
    subst h0 h1 h2
    rfl
  exact ⟨outSt, tape, houtlen, htlen, hout, by rw [← hfresh]; exact hfold⟩

/-! ### §6a — ⚑ THE `v′` REFUTER, on the block's own chain. -/

/-- The real chain root's claim, rendered from `chainState` symbolically — no permutation is
evaluated to STATE this; the compiled facts enter only where marked. -/
def realChainClaim : List ℤ :=
  piBlock ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 0).getD 0 0)
    ++ (piBlock ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 0).getD 1 0)
    ++ (piBlock ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 0).getD 2 0)
    ++ (piBlock ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 0 0)
    ++ (piBlock ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 1 0)
    ++ (piBlock ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 2 0)
    ++ List.replicate CHAIN_ACC_WIDTH 0)))))

/-- ⚑ COMPILED: the terminal chain state is three lanes, each canonical. (46 Poseidon
permutations of a 255-bit state — the same trust `the_chain_ends_at_the_blocks_challenges`
already carries.) -/
theorem chain_out_is_canonical :
    (Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).length = 3
    ∧ (Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 0 0 < 2 ^ (SB * SK)
    ∧ (Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 1 0 < 2 ^ (SB * SK)
    ∧ (Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 2 0 < 2 ^ (SB * SK) := by
  native_decide

/-- A zero finalize claim — `FinalizePublishesVPrime` holds of it with `v′ = 0`. -/
def zeroFinalizeClaim : List ℤ := List.replicate FINALIZE_CLAIM_LEN 0

private theorem zeroFinalize_renders : Renders zeroFinalizeClaim 0 0 := by
  refine ⟨by positivity, fun i hi => ?_⟩
  have hlt : 0 + i < FINALIZE_CLAIM_LEN := by
    have : SK = 32 := by decide
    have : FINALIZE_CLAIM_LEN = 160 := by decide
    omega
  show (List.replicate FINALIZE_CLAIM_LEN (0 : ℤ)).getD (0 + i) 0 = limbAt 0 i
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp only [hlt, if_pos]
  simp [Dregg2.Circuit.Emit.PastaFieldSound.limbAt]

theorem realChain_says : ChainRootSays realChainClaim := by
  refine ⟨Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 0,
    Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46,
    (List.range CHAIN_LINKS).map Dregg2.Circuit.Emit.MinaPhase2Chain.linkX,
    rfl, chain_out_is_canonical.1, by simp, ?_, ?_, (absorbFold_is_the_chain 46).symm⟩
  · intro k hk
    interval_cases k
    · exact renders_head _ (by decide)
    · show Renders realChainClaim (1 * SK) _
      have h : Renders realChainClaim (SK + 0) ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 0).getD 1 0) :=
        renders_shift _ (renders_head _ (by decide))
      simpa using h
    · show Renders realChainClaim (2 * SK) _
      have h : Renders realChainClaim (SK + (SK + 0))
          ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 0).getD 2 0) :=
        renders_shift _ (renders_shift _ (renders_head _ (by decide)))
      exact h
  · have hb : ∀ k, k < 3 →
        (Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD k 0 < 2 ^ (SB * SK) := by
      intro k hk
      interval_cases k
      · exact chain_out_is_canonical.2.1
      · exact chain_out_is_canonical.2.2.1
      · exact chain_out_is_canonical.2.2.2
    intro k hk
    interval_cases k
    · show Renders realChainClaim (CHAIN_STATE_WIDTH + 0 * SK) _
      have h : Renders realChainClaim (SK + (SK + (SK + 0)))
          ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 0 0) :=
        renders_shift _ (renders_shift _ (renders_shift _ (renders_head _ (hb 0 (by omega)))))
      exact h
    · show Renders realChainClaim (CHAIN_STATE_WIDTH + 1 * SK) _
      have h : Renders realChainClaim (SK + (SK + (SK + (SK + 0))))
          ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 1 0) :=
        renders_shift _ (renders_shift _ (renders_shift _ (renders_shift _
          (renders_head _ (hb 1 (by omega))))))
      exact h
    · show Renders realChainClaim (CHAIN_STATE_WIDTH + 2 * SK) _
      have h : Renders realChainClaim (SK + (SK + (SK + (SK + (SK + 0)))))
          ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 2 0) :=
        renders_shift _ (renders_shift _ (renders_shift _ (renders_shift _ (renders_shift _
          (renders_head _ (hb 2 (by omega)))))))
      exact h

/-- ⚑⚑ **THE `v′` REFUTER.** Drop `SeamEq` and the implication is FALSE on the real block's own
chain claim against a zero `v′`: the composed sentence would force `0 = WRAP_V_CHAL`. Compiled
facts: the chain lanes' canonicity and `the_chain_ends_at_the_blocks_challenges`. -/
theorem v_prime_seam_S2_needs_the_seam :
    ¬ (∀ cv rv, ChainRootSays cv → FinalizePublishesVPrime rv → KimchiVPrimeSays cv rv) := by
  intro h
  obtain ⟨outLane0, v', hout, hv, heq⟩ :=
    h realChainClaim zeroFinalizeClaim realChain_says ⟨0, zeroFinalize_renders⟩
  -- the two Renders at CHAIN_OUT_LANE0 name one value
  have hb0 : (Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 0 0 < 2 ^ (SB * SK) :=
    chain_out_is_canonical.2.1
  have hreal : Renders realChainClaim CHAIN_OUT_LANE0
      ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 0 0) := by
    have h' : Renders realChainClaim (SK + (SK + (SK + 0)))
        ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 0 0) :=
      renders_shift _ (renders_shift _ (renders_shift _ (renders_head _ hb0)))
    exact h'
  have hlane : outLane0 = (Dregg2.Circuit.Emit.MinaPhase2Chain.chainState 46).getD 0 0 :=
    Renders.eq_of_weld hout hreal (fun _ _ => rfl)
  have hv0 : v' = 0 := Renders.eq_of_weld hv zeroFinalize_renders (fun _ _ => rfl)
  rw [hv0, hlane] at heq
  rw [Dregg2.Circuit.Emit.MinaPhase2Chain.the_chain_ends_at_the_blocks_challenges.1] at heq
  exact absurd heq.symm
    (by decide : Dregg2.Circuit.Emit.MinaBlockFqTranscript.WRAP_V_CHAL ≠ 0)

/-! ## §7 — THE CERTIFIED BUNDLES for the chain seams. -/

def vPrimeCertifiedSeam : CertifiedSeam ChainRootSays FinalizePublishesVPrime KimchiVPrimeSays :=
  { spec := vPrimeSeam, wf := vPrimeSeam_wf, certifies := v_prime_seam_certifies }

def freshSpongeCertifiedSeam :
    CertifiedSeam ChainRootSays (fun _ => True) (fun cv _ => ChainStartsFresh cv) :=
  { spec := freshSpongeSeam, wf := freshSpongeSeam_wf, certifies := fresh_sponge_seam_certifies }

/-! ## §8 — ⚑ THE PORT, AND THE CENSUS.

`no_arithmetic_call_names_an_xi_block` inverted into an OBJECT: the conjunction DECLARES its ξ
block a port, the declaration cannot be built unless the block is published and genuinely free, and
the census cannot be built unless a registered seam covers it. -/

/-- The ξ port: PI slots `[PI_XI, PI_XI + SK)`, backed by the column island `[XI_SQ, XI_CL + SK)` —
BOTH ξ blocks, the published record and the free squeeze twin it is compared to. -/
def xiPort : PiPort :=
  { name := "xi", lo := PI_XI, width := SK, colLo := XI_SQ, colWidth := 2 * SK }

/-- ⚑ COMPILED (the kernel measurably cannot walk the sound-multiply legs' `readCols` —
`MinaWrapConjunctionAir` §"the LEG level"): NO leg of the conjunction AIR joins the ξ island to any
other column. Full leg coverage — the base-list caveat of `no_arithmetic_call_names_an_xi_block`
is closed at compiled trust. -/
theorem conjunction_xi_island_is_free : portIslandFree conjunctionAir xiPort = true := by
  native_decide

/-- ⚑ **THE RED POLE.** ζ is NOT a port: `seedLegs` joins its island to the fold registers. The
verdict can refuse, so the declaration means something. -/
theorem zeta_is_not_a_port :
    portIslandFree conjunctionAir
      { name := "zeta?", lo := PI_ZETA, width := SK, colLo := ZETA, colWidth := SK } = false := by
  native_decide

/-- The conjunction's declared port set — a plain list, so the census theorem's proof term
references no compiled verdict. -/
def conjunctionPortSet : List PiPort := [xiPort]

/-- ⚑ **THE PORTED AIR** — the conjunction carrying its port declaration in its type. -/
def conjunctionPortedAir : PortedAir :=
  { air := conjunctionAir
  , piCount := CJ_PI_COUNT
  , ports := conjunctionPortSet
  , wf := by decide
  , pinned := by
      intro p hp i hi
      have hp' : p = xiPort := by
        simpa [conjunctionPortSet] using hp
      subst hp'

      refine ⟨⟨VmRow.first, XI_CL + i, PI_XI + i⟩,
        xi_seam_right_slot_publishes_the_records_xi i hi, rfl, ?_, ?_⟩
      · show xiPort.colLo ≤ XI_CL + i
        have h1 : xiPort.colLo = 0 := by decide
        omega
      · show XI_CL + i < xiPort.colLo + xiPort.colWidth
        have h1 : xiPort.colLo = 0 := by decide
        have h2 : xiPort.colWidth = 64 := by decide
        have h3 : XI_CL = 32 := by decide
        have h4 : xiPort.width = 32 := by decide
        rw [h4] at hi
        omega
  , free := by
      show ([xiPort].all (portIslandFree conjunctionAir)) = true
      rw [List.all_cons, List.all_nil, Bool.and_true]
      exact conjunction_xi_island_is_free }

/-! ## §8b — ⚑⚑ THE RECURSION-SEAM PORTS: every deployed `bound := none` `proofBind` either has
its commit surface declared as a COVERED port here, or is counted as UNCOVERED by a theorem that
will shrink.

## The class, named before the objects

`descriptor_ir2.rs`'s `proofBind` arm emits polynomials over a seam's `commit` lanes only under
`if let Some(b) = &p.bound`. Every Mina light-client seam is `bound := none` — and CORRECTLY so:
their commit lanes are either PI-bound columns (a `bound` congruence could only compare a column
to itself, `feedback-a-pin-against-its-own-definition-is-decoration`) or descriptor constants. So
the commit surfaces are PORTS in this module's §4 sense: published, island-free, meaningful only
under external forcing. What was missing was the OBJECT saying which weld forces each one —
`LightClientAnchorConnectivity`'s census counted the declarations as joins instead (fixed
2026-08-08, same day as this section, together with `legJoinsAcross`'s `.bind` arm — without that
arm the island verdicts below would have scored the seams' own DECLARATIONS as joins and refused
exactly the ports the mechanism exists for).

## The census of the five served `bound := none` seams, and the three closure kinds

  * `minaHeadAir` §2c (tip): commit = the nine PI-bound `TIP_STATE` columns. **Covered by
    `headTipSeam` below** — the executor's REFUSAL 13/14a/14b as an emitted object, elementwise,
    no digest. Both polarities: `mina_head_verifier.rs` §"REFUSALS 13-14 — BOTH POLARITIES".
  * `minaHeadAir` §2b (chainlink): commit = the nine PI-bound `SUB_PI` columns — a blake3 DIGEST
    of the sub-proof's PI vector, not slot-for-slot weldable. **Covered by the named weld
    `check_transcript_binding` (REFUSAL 4)**, declared as a `WeldCover`.
  * `minaHeadAir` §2d (conjunction): same shape at `CONJ_PI`. ⚑⚑ **Covered by the named weld
    `check_conjunction_binding` (REFUSAL 15) since 2026-08-08** — which, from 2026-08-06 to that
    day, was DEAD CODE: defined, documented, called by NOTHING, no wire field to call it with, no
    test. This census found it while declaring the cover; the wiring (wire fields REQUIRED so old
    blobs refuse to decode, the dispatch call after a conjunction-STARK verify + program pin by
    guard column 58, both polarities) landed with `conjPiWeld` below. The historical count
    (`the_conjunction_commitment_port_has_no_live_weld = 1`) is retired by
    `the_head_commitment_ports_are_weld_covered = 0`.
  * `minaLinkAir` §2b (state hash) and §2c (body chain): commit = salt CONSTANTS plus row columns.
    The PI-visible surface is `BODYHASH` (20..28) and `BODY_ACC` (29..36) — declared as ports
    below. ⚑⚑ **Covered by the named weld `check_body_chain_binding` (REFUSAL 16) since
    2026-08-08** — the seventeen-slot executor comparison against `MinaStateBodyHashChain`'s root
    claim this docblock used to name as the owed object: `BODY_ACC` elementwise against the root's
    `transcript_acc`, `BODYHASH` against the `Faithful9` re-limbing of its squeezed lane 0, the
    chain head refused against the `MinaProtoStateBody` salt, under a second operator-pinned
    recursion-vk anchor (the two towers' claim shapes are identical; the fingerprint is the only
    discriminator). `the_link_body_ports_have_no_registered_cover = 2` is retired by
    `the_link_body_ports_are_weld_covered = 0`. ⚠ Still an EXECUTOR comparison, not a fold
    `cb.connect` — and the `BODYHASH` half CANNOT be a `SeamSpec` (nine 29-bit lanes against
    thirty-two 8-bit limbs is a re-limbing, outside the pin vocabulary), which is why the cover is
    a `WeldCover` and not a seam. ⚠ The per-row halves (mid-row `PARENT`/`BODYHASH`/`OWNHASH`
    triples the unconditional guards declare) are not PI slots at all; their forcing is
    `Satisfied2Custom.proofBound`'s per-row existential, discharged today only by test-side
    absorb-proof verification (`mina_statehash_seam_proves.rs`) — that residual is the seams' own
    docblocks' and is not restated as covered here.

Two more `bound := none` binds live outside the served light-client cone and are counted where
they live: the `-fs` weld (`MinaWrapClosingAir.deltaAbsorbBindLeg`, commit = `TR_IN` constants ‖
manifest-pinned addend cells ‖ PI-published squeeze — every var lane forced on the guarded row by
`deltaPinLegs`/`trOutPinLegs`; the squeeze↔sub-proof tie is the executor's `c` recompute, its §3),
and the Custom/Settle carve-outs (`vkPin := none ∧ bound := none` by design; the cover is the
fold's lane-by-lane `connect`, `prove_custom_binding_node`, counted by `proofBindDeclarative`). -/

/-- The head verify leaf claim: its whole 39-slot PI vector. -/
def HEAD_CLAIM_LEN : Nat := 39
/-- The link segment leaf claim: its whole 46-slot PI vector. ⚑ **37 → 46 on 2026-08-10** — the
`PI_HEAD_OWN` publication that gives `LightClientMinaLinkAir.stateHashBindLeg`'s
`state-hash-preimage` port an output to land on. -/
def LINK_CLAIM_LEN : Nat := 46

/-- `effect_vm_descriptor2_semantic_fingerprint(dregg-mina-lightclient-verify::v1)`, as
`Faithful9` key lanes. Measured 2026-08-08 (`conj_fingerprint` over the served artifact,
`fp=e64df5b6…`, `w=77 pi=39 cons=74`); the same nine digits `MinaAccumulatorAir.MINA_HEAD_VK_LANES`
pins — deliberately NOT imported from there: importing that module makes every exe in this file's
import cone evaluate the whole 3 068-column accumulator at initialization (measured:
`emit_seam_specs` ran for minutes instead of milliseconds). `seam_specs.rs` recomputes these lanes
from the served bytes and refuses drift, so a stale literal here is a loud red, not a silent
misname. ⚠ FLAG DAY coupling: re-emitting `dregg-mina-lightclient-verify-v1.json` moves this
literal, the accumulator's pin, and this seam's JSON.

⚑ Final cascade measurement, 2026-08-11: the canonical-record leaf widening propagated through
the link into a `77/39/74` head whose fingerprint is
`2a431795898a925498fff71d753050c3303f83a4ce5fd0f09ba5db35787c2d32`. -/
def HEAD_VK_LANES : List ℤ :=
  [353846058, 76829772, 503309845, 6351419, 334695477, 266818113, 376423233, 252099444, 3288444]

/-- ⚑⚑ **THE HEAD↔LINK SEAM — the executor's REFUSAL 13/14a/14b as an object.** Nineteen pins:
the nine tip lanes (REFUSAL 13 — these ARE the head seam's `commit` vector, welded elementwise at
`8·29 + 24 = 256` bits, no digest, no birthday bound), the nine anchor lanes (14a) and the anchor
height (14b, head slot 29 to link slot 18).

⚠ **THE TWENTIETH REFUSAL IS AFFINE AND CANNOT BE A PIN.** REFUSAL 14c checks
`link PI[19] = head PI[18] − head PI[29]` — a relation, not an equality of slots, outside
`SeamSpec`'s vocabulary. It stays the executor's, named here so the seam is not read as the whole
of `check_segment_binding`.

⚠ **APPLIED BY THE EXECUTOR, NOT BY A FOLD.** `check_segment_binding` compares these slots
natively after verifying both STARKs; no `apply_seam` call site exists yet. The object is emitted
so the index arithmetic has ONE author and the ports census has a cover to name; when a fold takes
this weld in-circuit it becomes a reader of this artifact. Fingerprint lanes: `HEAD_VK_LANES`
above (measured, Rust-regated) and `LightClientMinaAir.LINK_VK_LANES` (the head's own pin of the
link descriptor, one source); `seam_specs.rs` recomputes both from the served bytes and refuses
drift. -/
def headTipSeam : SeamSpec :=
  { name  := "dregg-seam-head-tip-to-link::v1"
  , left  := { claim := "mina-head-leaf", claimLen := HEAD_CLAIM_LEN
             , descName := "dregg-mina-lightclient-verify::v1"
             , descLanes := HEAD_VK_LANES }
  , right := { claim := "mina-link-leaf", claimLen := LINK_CLAIM_LEN
             , descName := "dregg-mina-lightclient-link::v1"
             , descLanes := LightClientMinaAir.LINK_VK_LANES }
  , pins  := (List.range 9).map (fun i =>
                (LightClientMinaAir.PI_ANCHOR_STATE i, LightClientMinaLinkAir.PI_ANCHOR i))
             ++ (List.range 9).map (fun i =>
                (LightClientMinaAir.PI_TIP_STATE i, LightClientMinaLinkAir.PI_TIP i))
             ++ [(LightClientMinaAir.PI_ANCHOR_H, LightClientMinaLinkAir.PI_ANCHOR_H)]
  , zeroLeft := [], zeroRight := [] }

theorem headTipSeam_wf : headTipSeam.wf = true := by decide

/-- The nineteen pins, as the concrete slot pairs the executor's loops walk. -/
theorem head_tip_seam_pins_are_the_nineteen :
    headTipSeam.pins
      = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8),
         (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 16),
         (17, 17), (29, 18)] := by decide

/-! ### S1 for the head↔link seam: every welded slot is published by a real pin leg of the
deployed AIR objects, constructed as memberships (no `DecidableEq` on `AirLeg`). -/

private theorem head_anchor_slot_published (i : Nat) (hi : i < 9) :
    AirLeg.pin ⟨VmRow.first, LightClientMinaAir.ANCHOR_STATE i,
        LightClientMinaAir.PI_ANCHOR_STATE i⟩
      ∈ LightClientMinaAir.minaHeadAir.legs := by
  interval_cases i <;>
    simp [LightClientMinaAir.minaHeadAir, LightClientMinaAir.anchorStatePins,
      LightClientMinaAir.tipStatePins, LightClientMinaAir.subPiPins,
      LightClientMinaAir.conjPiPins, LightClientMinaAir.wrapBindLegs,
      LightClientMinaAir.linkBindLegs, LightClientMinaAir.conjBindLegs]

private theorem head_tip_slot_published (i : Nat) (hi : i < 9) :
    AirLeg.pin ⟨VmRow.first, LightClientMinaAir.TIP_STATE i,
        LightClientMinaAir.PI_TIP_STATE i⟩
      ∈ LightClientMinaAir.minaHeadAir.legs := by
  interval_cases i <;>
    simp [LightClientMinaAir.minaHeadAir, LightClientMinaAir.anchorStatePins,
      LightClientMinaAir.tipStatePins, LightClientMinaAir.subPiPins,
      LightClientMinaAir.conjPiPins, LightClientMinaAir.wrapBindLegs,
      LightClientMinaAir.linkBindLegs, LightClientMinaAir.conjBindLegs]

private theorem head_subpi_slot_published (i : Nat) (hi : i < 9) :
    AirLeg.pin ⟨VmRow.first, LightClientMinaAir.SUB_PI i, LightClientMinaAir.PI_SUB_PI i⟩
      ∈ LightClientMinaAir.minaHeadAir.legs := by
  interval_cases i <;>
    simp [LightClientMinaAir.minaHeadAir, LightClientMinaAir.anchorStatePins,
      LightClientMinaAir.tipStatePins, LightClientMinaAir.subPiPins,
      LightClientMinaAir.conjPiPins, LightClientMinaAir.wrapBindLegs,
      LightClientMinaAir.linkBindLegs, LightClientMinaAir.conjBindLegs]

private theorem head_conjpi_slot_published (i : Nat) (hi : i < 9) :
    AirLeg.pin ⟨VmRow.first, LightClientMinaAir.CONJ_PI i, LightClientMinaAir.PI_CONJ_PI i⟩
      ∈ LightClientMinaAir.minaHeadAir.legs := by
  interval_cases i <;>
    simp [LightClientMinaAir.minaHeadAir, LightClientMinaAir.anchorStatePins,
      LightClientMinaAir.tipStatePins, LightClientMinaAir.subPiPins,
      LightClientMinaAir.conjPiPins, LightClientMinaAir.wrapBindLegs,
      LightClientMinaAir.linkBindLegs, LightClientMinaAir.conjBindLegs]

private theorem link_anchor_slot_published (i : Nat) (hi : i < 9) :
    AirLeg.pin ⟨VmRow.first, LightClientMinaLinkAir.PARENT i, LightClientMinaLinkAir.PI_ANCHOR i⟩
      ∈ LightClientMinaLinkAir.minaLinkAir.legs := by
  interval_cases i <;>
    simp [LightClientMinaLinkAir.minaLinkAir, LightClientMinaLinkAir.anchorPins,
      LightClientMinaLinkAir.tipPins, LightClientMinaLinkAir.bodyHashPins,
      LightClientMinaLinkAir.bodyAccPins]

private theorem link_tip_slot_published (i : Nat) (hi : i < 9) :
    AirLeg.pin ⟨VmRow.last, LightClientMinaLinkAir.OWNHASH i, LightClientMinaLinkAir.PI_TIP i⟩
      ∈ LightClientMinaLinkAir.minaLinkAir.legs := by
  interval_cases i <;>
    simp [LightClientMinaLinkAir.minaLinkAir, LightClientMinaLinkAir.anchorPins,
      LightClientMinaLinkAir.tipPins, LightClientMinaLinkAir.bodyHashPins,
      LightClientMinaLinkAir.bodyAccPins]

private theorem link_bodyhash_slot_published (j : Nat) (hj : j < 9) :
    AirLeg.pin ⟨VmRow.first, LightClientMinaLinkAir.BODYHASH j,
        LightClientMinaLinkAir.PI_BODYHASH j⟩
      ∈ LightClientMinaLinkAir.minaLinkAir.legs := by
  have hmem : AirLeg.pin ⟨VmRow.first, LightClientMinaLinkAir.BODYHASH j,
      LightClientMinaLinkAir.PI_BODYHASH j⟩ ∈ LightClientMinaLinkAir.bodyHashPins :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  -- ⚠ NOT a hand-counted `mem_append_left/right` chain: that spelling encodes the leg list's
  -- APPEND NESTING, so appending a pin block anywhere reds it with a type mismatch rather than a
  -- statement change. It did, on the 2026-08-10 `headOwnPins` flag day.
  simp only [LightClientMinaLinkAir.minaLinkAir, List.mem_append]
  tauto

private theorem link_bodyacc_slot_published (j : Nat) (hj : j < 8) :
    AirLeg.pin ⟨VmRow.first, LightClientMinaLinkAir.BODY_ACC j,
        LightClientMinaLinkAir.PI_BODY_ACC j⟩
      ∈ LightClientMinaLinkAir.minaLinkAir.legs := by
  have hmem : AirLeg.pin ⟨VmRow.first, LightClientMinaLinkAir.BODY_ACC j,
      LightClientMinaLinkAir.PI_BODY_ACC j⟩ ∈ LightClientMinaLinkAir.bodyAccPins :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [LightClientMinaLinkAir.minaLinkAir, List.mem_append]
  tauto

/-- ⚑ **S1 FOR THE HEAD↔LINK SEAM.** Every left endpoint is a slot the head AIR publishes with a
real pin leg, every right endpoint one the link AIR publishes — the tip's right end deliberately
the LAST-row `OWNHASH` pin, which is what makes the weld "the published tip is the chain's last
element" rather than a comparison of two copies. -/
theorem the_head_tip_seam_welds_published_slots :
    (∀ i, i < 9 →
      AirLeg.pin ⟨VmRow.first, LightClientMinaAir.TIP_STATE i,
          LightClientMinaAir.PI_TIP_STATE i⟩ ∈ LightClientMinaAir.minaHeadAir.legs)
    ∧ (∀ i, i < 9 →
      AirLeg.pin ⟨VmRow.last, LightClientMinaLinkAir.OWNHASH i,
          LightClientMinaLinkAir.PI_TIP i⟩ ∈ LightClientMinaLinkAir.minaLinkAir.legs)
    ∧ (∀ i, i < 9 →
      AirLeg.pin ⟨VmRow.first, LightClientMinaAir.ANCHOR_STATE i,
          LightClientMinaAir.PI_ANCHOR_STATE i⟩ ∈ LightClientMinaAir.minaHeadAir.legs)
    ∧ (∀ i, i < 9 →
      AirLeg.pin ⟨VmRow.first, LightClientMinaLinkAir.PARENT i,
          LightClientMinaLinkAir.PI_ANCHOR i⟩ ∈ LightClientMinaLinkAir.minaLinkAir.legs) :=
  ⟨head_tip_slot_published, link_tip_slot_published,
   head_anchor_slot_published, link_anchor_slot_published⟩

/-! ### The head's four ports, and the link's two. -/

/-- The head's pinned-anchor port: PI 0..8, the `ANCHOR_STATE` island. Externally forced twice —
against cell-program state (REFUSAL 1) and against the link sub-proof (REFUSAL 14a, the seam). -/
def anchorPort : PiPort := { name := "anchor-state", lo := 0, width := 9, colLo := 12, colWidth := 9 }
/-- The head's tip port: PI 9..17, the `TIP_STATE` island — the §2c seam's commit surface. -/
def tipPort : PiPort := { name := "tip-state", lo := 9, width := 9, colLo := 21, colWidth := 9 }
/-- The head's chainlink-commitment port: PI 20..28, the `SUB_PI` island — the §2b seam's commit
surface, digest-shaped. -/
def subPiPort : PiPort :=
  { name := "sub-proof-commitment", lo := 20, width := 9, colLo := 40, colWidth := 9 }
/-- The head's conjunction-commitment port: PI 30..38, the `CONJ_PI` island — §2d's. -/
def conjPiPort : PiPort :=
  { name := "conjunction-commitment", lo := 30, width := 9, colLo := 68, colWidth := 9 }

def headPortSet : List PiPort := [anchorPort, tipPort, subPiPort, conjPiPort]

/-- ⚑ COMPILED: no emitted polynomial of the head AIR joins any of the four port islands to the
rest of the trace. The `.bind` legs do not — `bound := none` emits nothing over `commit`, which is
`legJoinsAcross`'s emission-faithful `.bind` arm doing its job (under the old declaration-reading
default arm this verdict would be FALSE at the tip and both commitment islands, i.e. the ports
would be unrepresentable exactly where they are needed). -/
theorem head_port_islands_are_free :
    ([anchorPort, tipPort, subPiPort, conjPiPort].all
      (portIslandFree LightClientMinaAir.minaHeadAir)) = true := by native_decide

/-- ⚑ **THE RED POLE.** `ANCHOR_H` is NOT a port: G1/G4 join its column to the slack and height
columns, so the verdict can refuse and the declarations above mean something. -/
theorem anchor_h_is_not_a_port :
    portIslandFree LightClientMinaAir.minaHeadAir
      { name := "anchor-h?", lo := 29, width := 1
      , colLo := LightClientMinaAir.ANCHOR_H, colWidth := 1 } = false := by native_decide

/-- ⚑ **THE HEAD, PORTED** — the verify AIR carrying its four port declarations in its type:
published (a real pin leg per slot, from the island) and island-free (no emitted polynomial joins
a port column to the rest of the trace; the §2b/§2c/§2d binds don't, because `bound := none` emits
nothing over `commit` — `legJoinsAcross`'s emission-faithful `.bind` arm). -/
def headPortedAir : PortedAir :=
  { air := LightClientMinaAir.minaHeadAir
  , piCount := HEAD_CLAIM_LEN
  , ports := headPortSet
  , wf := by decide
  , pinned := by
      intro p hp i hi
      simp only [headPortSet, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · refine ⟨⟨VmRow.first, LightClientMinaAir.ANCHOR_STATE i,
          LightClientMinaAir.PI_ANCHOR_STATE i⟩, head_anchor_slot_published i hi, ?_, ?_, ?_⟩ <;>
        simp only [LightClientMinaAir.ANCHOR_STATE, LightClientMinaAir.PI_ANCHOR_STATE,
          LightClientMinaAir.STATE_LIMBS, anchorPort] at hi ⊢ <;> omega
      · refine ⟨⟨VmRow.first, LightClientMinaAir.TIP_STATE i,
          LightClientMinaAir.PI_TIP_STATE i⟩, head_tip_slot_published i hi, ?_, ?_, ?_⟩ <;>
        simp only [LightClientMinaAir.TIP_STATE, LightClientMinaAir.PI_TIP_STATE,
          LightClientMinaAir.STATE_LIMBS, tipPort] at hi ⊢ <;> omega
      · refine ⟨⟨VmRow.first, LightClientMinaAir.SUB_PI i,
          LightClientMinaAir.PI_SUB_PI i⟩, head_subpi_slot_published i hi, ?_, ?_, ?_⟩ <;>
        simp only [LightClientMinaAir.SUB_PI, LightClientMinaAir.PI_SUB_PI,
          LightClientMinaAir.STATE_LIMBS, subPiPort] at hi ⊢ <;> omega
      · refine ⟨⟨VmRow.first, LightClientMinaAir.CONJ_PI i,
          LightClientMinaAir.PI_CONJ_PI i⟩, head_conjpi_slot_published i hi, ?_, ?_, ?_⟩ <;>
        simp only [LightClientMinaAir.CONJ_PI, LightClientMinaAir.PI_CONJ_PI,
          LightClientMinaAir.STATE_LIMBS, conjPiPort] at hi ⊢ <;> omega
  , free := head_port_islands_are_free }

/-- The link's body-hash port: PI 20..28, the `BODYHASH` island. -/
def bodyHashPort : PiPort :=
  { name := "body-hash", lo := 20, width := 9, colLo := 22, colWidth := 9 }
/-- The link's body-chain-accumulator port: PI 29..36, the `BODY_ACC` island. -/
def bodyAccPort : PiPort :=
  { name := "body-acc", lo := 29, width := 8, colLo := 40, colWidth := 8 }

def linkPortSet : List PiPort := [bodyHashPort, bodyAccPort]

/-- COMPILED: the two body islands are free in the link AIR — the seams' declarations do not join
them (emission-faithful `.bind` arm), the `.limbs`/lookup legs are arity-1, and the chain windows
never name them. -/
theorem link_port_islands_are_free :
    ([bodyHashPort, bodyAccPort].all
      (portIslandFree LightClientMinaLinkAir.minaLinkAir)) = true := by native_decide

/-- The link, ported: its two body surfaces declared. Buildable — published and island-free —
which is exactly why the UNCOVERED count below is the loud object and not this one. -/
def linkPortedAir : PortedAir :=
  { air := LightClientMinaLinkAir.minaLinkAir
  , piCount := LINK_CLAIM_LEN
  , ports := linkPortSet
  , wf := by decide
  , pinned := by
      intro p hp i hi
      simp only [linkPortSet, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · refine ⟨⟨VmRow.first, LightClientMinaLinkAir.BODYHASH i,
          LightClientMinaLinkAir.PI_BODYHASH i⟩, link_bodyhash_slot_published i hi, ?_, ?_, ?_⟩ <;>
        simp only [LightClientMinaLinkAir.BODYHASH, LightClientMinaLinkAir.PI_BODYHASH,
          LightClientMinaAir.STATE_LIMBS, bodyHashPort] at hi ⊢ <;> omega
      · refine ⟨⟨VmRow.first, LightClientMinaLinkAir.BODY_ACC i,
          LightClientMinaLinkAir.PI_BODY_ACC i⟩, link_bodyacc_slot_published i hi, ?_, ?_, ?_⟩ <;>
        simp only [LightClientMinaLinkAir.BODY_ACC, LightClientMinaLinkAir.PI_BODY_ACC,
          LightClientMinaAir.STATE_LIMBS, bodyAccPort] at hi ⊢ <;> omega
  , free := link_port_islands_are_free }

/-! ### The covers. -/

/-- The tip port, covered by the head↔link seam. -/
def tipPortCovered : CoveredPort :=
  { descName := "dregg-mina-lightclient-verify::v1", port := tipPort, seam := headTipSeam }

/-- The anchor port, covered by the same seam (REFUSAL 14a's nine pins). -/
def anchorPortCovered : CoveredPort :=
  { descName := "dregg-mina-lightclient-verify::v1", port := anchorPort, seam := headTipSeam }

/-- ⚑ The chainlink-commitment port's cover: the executor weld that RECOMPUTES the digest of the
sub-proof's PI vector and refuses the nine lanes against it — REFUSAL 4, `check_transcript_binding`,
CALLED in the dispatch path (`verify`, after the accumulator discharge) and both-polarity tested
(`a_head_declaring_the_sub_proof_it_presents_is_accepted` /
`a_head_presenting_a_different_sub_proof_is_refused`). Digest-shaped, so no `SeamSpec` can express
it. -/
def subPiWeld : WeldCover :=
  { descName := "dregg-mina-lightclient-verify::v1", port := subPiPort
  , welder := "dregg_turn::executor::mina_head_verifier::check_transcript_binding"
  , subProgram := CHAINLINK_VK_LANES }

/-! ⚑⚑ **THE CONJUNCTION-COMMITMENT PORT'S WELD — dead code from 2026-08-06 to 2026-08-08, wired
the day this census counted it.**

The finding, kept in full because it is the class this repo's doctrine opens with:
`mina_head_verifier.rs` DEFINED REFUSAL 15 (`check_conjunction_binding`, a full digest-recompute
weld with its own domain-separation context), its docblock described the check — and **nothing
called it**: absent from the `verify` dispatch, no wire fields to call it WITH, zero tests. The
same audit found REFUSAL 4 called and tested, and REFUSAL 13/14 called and tested — this was the
one dead limb, and `the_conjunction_commitment_port_has_no_live_weld = 1` counted it while it
stood. A `WeldCover` naming an uncalled function would have been a declaration wearing a cover, so
none was built until the owed object landed — which it did, 2026-08-08, in exactly the shape the
count demanded: `conjunction_public_inputs`/`conjunction_proof` REQUIRED on the wire (an old blob
refuses to decode), the dispatch call after a conjunction-STARK verify + a program pin resolved by
guard column `FINALIZE_XI_B_PROVED` (58), and both polarities in `mina_head_verifier.rs`'s
REFUSAL-15 suite (`a_head_declaring_the_conjunction_it_presents_is_accepted` /
`a_head_presenting_a_different_conjunction_is_refused`, falsifier checked non-zero and in-width).

⚠ What the weld does NOT buy is unchanged and stays said: nothing relates the conjunction
sub-proof's ξ to the block whose head this is — that is `fold_endo_into_finalize`'s 32 connects
(the ξ seam above), whose root this executor still does not consume. -/

/-- ⚑ The conjunction-commitment port's cover: the executor weld that RECOMPUTES the digest of the
conjunction sub-proof's PI vector and refuses the nine lanes against it — REFUSAL 15,
`check_conjunction_binding`, CALLED in the dispatch (`verify`, after the conjunction STARK) and
both-polarity tested since 2026-08-08. Digest-shaped, so no `SeamSpec` can express it. -/
def conjPiWeld : WeldCover :=
  { descName := "dregg-mina-lightclient-verify::v1", port := conjPiPort
  , welder := "dregg_turn::executor::mina_head_verifier::check_conjunction_binding"
  , subProgram := CONJ_VK_LANES }

/-- The deployed seam registry. -/
def minaSeamRegistry : List SeamSpec := [xiSeam, vPrimeSeam, freshSpongeSeam, headTipSeam]

/-- ⚑ **THE CENSUS CONSTRUCTOR** — does not elaborate unless the ξ seam covers every slot of the
ξ port. A new port with no covering seam cannot be added to `minaCoveredPorts`. -/
def xiPortCovered : CoveredPort :=
  { descName := "dregg-mina-wrap-conjunction::v1", port := xiPort, seam := xiSeam }

/-- Every SEAM-coverable declared port is covered by a registered seam. Goes red the day such a
port is declared without one. ⚑ Extended 2026-08-08 with the head's anchor and tip ports (covered
by `headTipSeam`); the head's two DIGEST-shaped ports and the link's two body ports are
weld-covered and censused separately below (`the_head_commitment_ports_are_weld_covered`,
`the_link_body_ports_are_weld_covered` — both `= []` since the same day, having stood at 1 and 2
as counted wounds). -/
theorem every_declared_port_is_covered_by_a_named_seam :
    ([("dregg-mina-wrap-conjunction::v1", conjunctionPortSet),
      ("dregg-mina-lightclient-verify::v1", [anchorPort, tipPort])].all fun ps =>
      ps.2.all fun p => minaSeamRegistry.any fun s => seamCoversPort s ps.1 p) = true := by
  decide

/-- …and the ported structures declare exactly the censused sets. -/
theorem the_ported_air_declares_the_censused_set :
    conjunctionPortedAir.ports = conjunctionPortSet
      ∧ headPortedAir.ports = headPortSet
      ∧ linkPortedAir.ports = linkPortSet :=
  ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE WELD-COVERED PORT** — the chainlink-commitment port carries a named, CALLED, tested
welder and the nine fingerprint lanes of the program its sub-proof must be of, and those lanes are
THE seam's own `vkPin` literal (one source, not a transcription). -/
theorem the_subproof_commitment_port_is_weld_covered :
    subPiWeld.port = subPiPort
      ∧ subPiWeld.subProgram = CHAINLINK_VK_LANES
      ∧ subPiWeld.descName = "dregg-mina-lightclient-verify::v1" :=
  ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE CONJUNCTION WELD-COVER, censused like its sibling** — named, CALLED, tested welder
(REFUSAL 15's suite), and the nine fingerprint lanes ARE the seam's own `vkPin` literal (one
source, not a transcription). -/
theorem the_conjunction_commitment_port_is_weld_covered :
    conjPiWeld.port = conjPiPort
      ∧ conjPiWeld.subProgram = CONJ_VK_LANES
      ∧ conjPiWeld.descName = "dregg-mina-lightclient-verify::v1" :=
  ⟨rfl, rfl, rfl⟩

/-- ⚑⚑⚑ **THE VERIFY-SIDE UNCOVERED COUNT IS ZERO — every one of the head's four declared ports
has a registered seam or a live weld.** From 2026-08-06 to 2026-08-08 this stood at `= 1` with
literal `[conjPiPort]` (`the_conjunction_commitment_port_has_no_live_weld` — the section docblock
above keeps the finding); REFUSAL 15's wiring retired it. Refutable by construction: a fifth port
declared without a cover moves the count, and this theorem must MOVE with it, never be narrated
around. -/
theorem the_head_commitment_ports_are_weld_covered :
    (headPortSet.filter fun p =>
      !(minaSeamRegistry.any fun s =>
          seamCoversPort s "dregg-mina-lightclient-verify::v1" p)
      && !([subPiWeld, conjPiWeld].any fun w => w.port == p)) = [] := by
  decide

/-- ⚑ The body-hash port's cover: `check_body_chain_binding`'s second half (REFUSAL 16d), the
`Faithful9` re-limbing of the body-chain root's squeezed `state_body_hash` against the link's
published nonet. `subProgram` is the body chain's program (`dregg-pasta-fp-chainlink::v1`), THE
seam's own `vkPin` literal (one source).

⚠ **THIS IS THE EXECUTOR'S COVER, AND THE PORT ALSO HAS A SEAM.**
`MinaBodyHashRelimbSeams.bodyHashPortCovered` covers the same nine slots with a `CoveredPort` over
`bodyHashLaneSeam` — a stronger census object, since its `covers` obligation is decided rather than
a Rust string Lean cannot check. Both exist because they close different things: the seam is an
emitted artifact no fold applies yet, and REFUSAL 16d is what a NODE runs today. When the fold
lands, this value and `the_link_body_ports_are_weld_covered` go together. -/
def bodyHashWeld : WeldCover :=
  { descName := "dregg-mina-lightclient-link::v1", port := bodyHashPort
  , welder := "dregg_turn::executor::mina_head_verifier::check_body_chain_binding"
  , subProgram := LightClientMinaLinkAir.FP_CHAINLINK_VK_LANES }

/-- ⚑ The body-accumulator port's cover: the same welder's first half — the 8 `BODY_ACC` lanes
elementwise against the root claim's `transcript_acc` (same BabyBear encoding both sides). An
elementwise weld ACROSS a recursion-root claim rather than a sub-proof PI vector, so still a
`WeldCover`: `SeamSpec` ends are descriptor-keyed and a fold root has no descriptor, only an
operator-pinned `recursion_vk_fingerprint` (REFUSAL 16a/b). -/
def bodyAccWeld : WeldCover :=
  { descName := "dregg-mina-lightclient-link::v1", port := bodyAccPort
  , welder := "dregg_turn::executor::mina_head_verifier::check_body_chain_binding"
  , subProgram := LightClientMinaLinkAir.FP_CHAINLINK_VK_LANES }

/-- ⚑⚑⚑ **THE LINK-SIDE UNCOVERED COUNT IS ZERO — the seventeen-slot weld landed 2026-08-08.**
This stood as `the_link_body_ports_have_no_registered_cover = 2` from the day the ports were
declared: no fold `cb.connect`ed them, no executor compared them, `turn`'s
`LINK_PI_BODYHASH_BASE`/`LINK_PI_BODY_ACC_BASE` had no reader. `check_body_chain_binding`
(REFUSAL 16, both polarities tested, wire field REQUIRED so an old blob refuses to decode) is the
owed seventeen-slot weld against `MinaStateBodyHashChain`'s root claim, and these two `WeldCover`s
are its census objects. Same refutability as the head's: a new link port without a cover moves
this literal. -/
theorem the_link_body_ports_are_weld_covered :
    (linkPortSet.filter fun p =>
      !(minaSeamRegistry.any fun s =>
          seamCoversPort s "dregg-mina-lightclient-link::v1" p)
      && !([bodyHashWeld, bodyAccWeld].any fun w => w.port == p)) = [] := by
  decide

/-! ## §9 — axiom hygiene. Kernel-clean except the marked compiled facts. -/

#assert_axioms xiSeam_wf
#assert_axioms vPrimeSeam_wf
#assert_axioms freshSpongeSeam_wf
#assert_axioms the_finalize_claim_is_index_aligned
#assert_axioms the_xi_seam_welds_the_lift_to_the_record
#assert_axioms the_v_prime_seam_is_the_terminal_squeeze
#assert_axioms the_fresh_sponge_seam_zeroes_the_whole_incoming_state
#assert_axioms xi_seam_certifies
#assert_axioms bEval_eq_bPoly
#assert_axioms honestEndo_says
#assert_axioms honestConj_says
#assert_axioms the_xi_seam_composes_on_the_block
#assert_axioms forgedConj_says
#assert_axioms xi_seam_S2_needs_the_seam
#assert_axioms absorbFold_is_the_chain
#assert_axioms v_prime_seam_certifies
#assert_axioms fresh_sponge_seam_certifies
#assert_axioms every_declared_port_is_covered_by_a_named_seam
#assert_axioms headTipSeam_wf
#assert_axioms head_tip_seam_pins_are_the_nineteen
#assert_axioms the_head_tip_seam_welds_published_slots
#assert_axioms the_subproof_commitment_port_is_weld_covered
#assert_axioms the_conjunction_commitment_port_is_weld_covered
#assert_axioms the_head_commitment_ports_are_weld_covered
#assert_axioms the_link_body_ports_are_weld_covered

#assert_compiled chain_out_is_canonical
#assert_compiled realChain_says
#assert_compiled v_prime_seam_S2_needs_the_seam
#assert_compiled conjunction_xi_island_is_free
#assert_compiled zeta_is_not_a_port
#assert_compiled head_port_islands_are_free
#assert_compiled anchor_h_is_not_a_port
#assert_compiled link_port_islands_are_free
-- Compiled, not kernel-clean: the `PortedAir` values carry their compiled island verdicts, so any
-- theorem that NAMES one inherits the `native_decide` record. That is the honest tag, not a demotion.
#assert_compiled the_ported_air_declares_the_censused_set

end Dregg2.Circuit.Emit.MinaSeams
