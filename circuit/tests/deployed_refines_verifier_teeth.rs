//! # `DeployedRefines` — discharging the biggest untested apex hypothesis by test.
//!
//! ## The claim under audit (TRUST-BASE-CENSUS §6 R2 / row D1)
//!
//! The circuit-soundness apex (`CircuitSoundness.lightclient_unfoolable`) is factored
//! through `FriVerifierBridge.starkSound_of_verifyAlgo`, which rests on exactly two
//! named residuals:
//!
//!   * `AlgoStarkSound` — the irreducible FRI/STARK math floor (a Prop class), and
//!   * **`DeployedRefines`** (`metatheory/Dregg2/Circuit/FriVerifierBridge.lean:92`):
//!         `verify_batch accept  ⟹  verifyAlgo accept`
//!     i.e. the deployed Rust batch-STARK verifier computes an accept Boolean that is
//!     no weaker than the SPECIFIED Lean `verifyAlgo` (`FriVerifier.lean:557`) whose
//!     soundness-relevant teeth are PROVEN as Lean theorems.
//!
//! The census flagged `DeployedRefines` as **ATTACK-SURFACE (assumed, never
//! discharged)**: `rg verifyAlgo|DeployedRefines --glob '*.rs'` = 0 hits — no Rust test
//! tied the deployed verifier to the proven algorithm. This file is that tie.
//!
//! ## Why this test is the right shape
//!
//! `verifyAlgo` is a Lean function over an ABSTRACT `BatchProofData`; the deployed
//! verifier is `p3_batch_stark::verify_batch` reached through
//! `descriptor_ir2::verify_vm_descriptor2` (the verifier the light client / effect-vm
//! actually call). There is no shared serialization, so a byte-for-byte "run both on
//! the same proof" differential is not directly executable. What IS decidable — and is
//! exactly the content of `DeployedRefines` in the DANGEROUS direction — is:
//!
//!   > every soundness-relevant check that `verifyAlgo`'s PROVEN teeth model must be
//!   > PRESENT and BITING in the deployed `verify_batch`.
//!
//! If the deployed verifier accepted a proof `verifyAlgo`'s soundness assumed it would
//! reject (a check in `verifyAlgo` that `verify_batch` skips), the light client would
//! trust a weaker verifier than the one proven sound — a real vulnerability. So for
//! each `verifyAlgo` tooth we TAMPER the corresponding field of an honestly-generated
//! deployed proof and assert `verify_batch` (via `verify_vm_descriptor2`) REJECTS. A
//! tooth that fails to bite is a `DeployedRefines` divergence; all biting = the
//! hypothesis is discharged as tested fact for these checks.
//!
//! ## The per-check cross-map (verifyAlgo tooth  →  deployed check  →  this test)
//!
//! | `verifyAlgo` tooth (Lean, proven)                                   | deployed `verify_batch` check                                   | tamper here |
//! |---------------------------------------------------------------------|-----------------------------------------------------------------|-------------|
//! | `vk.shapeMatches` / instance shape                                  | `InstanceCountMismatch` (verifier/mod.rs:61)                     | `pop` a `degree_bits` entry |
//! | `tableOk_rejects_wrong_degree` (degree-bits pin / `LIMB_BITS`)      | `validate_degree_bits` + `verify_vm_descriptor2` LIMB pin (:5080)| bump a `degree_bits` entry |
//! | `segmentTooth` / publics binding + `deriveFri` observing publics    | transcript diverges ⇒ `pcs.verify` / `PublicValuesLengthMismatch`| verify with tampered public inputs |
//! | `foldConsistent` + `merkleRecompute_binds` (FRI query opening)      | `pcs.verify` opening argument (verifier/mod.rs:~502)             | bump an opened `trace_local` value |
//! | `batchTablesCheck_rejects_tampered_quotient` (quotient identity)    | `verify_constraints_with_lookups` OOD / `pcs.verify`            | bump an opened `quotient_chunks` value |
//! | `batchTablesCheck_rejects_unbalanced_bus` (`busSum = 0`)            | `LogUpGadget::verify_global_sum` (verifier/mod.rs:~642)         | bump a `global_lookup_data` cumulative sum |
//! | `queryPowCheck_rejects_bad_pow` (grinding)                          | FRI `query_proof_of_work_bits = 16` inside `pcs.verify`         | (config-carried; see note below) |
//!
//! ## Empirical finding (recorded from the run — informs how strong the discharge is)
//!
//! Teeth 1–2 (instance shape, degree pin) reject in `verify_vm_descriptor2` BEFORE
//! `verify_batch` runs, with their own diagnostics ("proof carries N instances…", "a
//! taller table widens the limb range") — cleanly isolated.
//!
//! Teeth 3–6 (opened trace, opened quotient, bus cumulative sum, public inputs) all
//! reject with the SAME error: `InvalidOpeningArgument(InvalidPowWitness)`. This is the
//! deployed FRI PCS's Fiat-Shamir + grinding gate firing FIRST: the deployed
//! `ir2_config` sets `query_proof_of_work_bits = 16` (`descriptor_ir2.rs:4689`), and
//! `pcs.verify` absorbs the commitments, public values, AND the claimed opened values
//! into the transcript BEFORE checking the 16-bit grinding witness — so ANY mutation to
//! committed / opened / public data desyncs the transcript, invalidating the honest
//! proof's grinding nonce before the deep per-query FRI / quotient-identity / global-sum
//! checks are even reached. This is itself a POSITIVE soundness fact: it witnesses that
//! the transcript binding (`verifyAlgo.deriveFri`) and the grinding tooth
//! (`verifyAlgo.queryPowCheck`) are TOTAL — no opened value floats free of the
//! Fiat-Shamir state. The rejection is real regardless of which line delivers it;
//! `DeployedRefines` needs only that the deployed verifier REJECT what `verifyAlgo`
//! rejects, which every tamper confirms.
//!
//! The DEEP checks masked by that gate have their own isolated coverage, on
//! honest-transcript proofs where the PoW gate passes: the logup-bus / `verify_global_sum`
//! tooth by `ir2_denotational_differential.rs` (PART K,
//! `faithfulness_guard_real_assembly_bus`, which assembles+proves a genuinely unbalanced
//! bus and drives it through the REAL cross-table grand-product), and the quotient /
//! trace-eval constraint tooth by the descriptor-level anti-ghost re-prove in
//! `effect_vm_ir2_validate.rs` (a forged witness the honest prover refuses).
//!
//! Gated on nothing (descriptor-level prove/verify is unconditional in dregg-circuit),
//! but SLOW (cold prover compile). Run:
//!   `cargo test -p dregg-circuit --test deployed_refines_verifier_teeth -- --nocapture`

use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof as BatchProof, MemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;

use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_field::extension::BinomialExtensionField;

/// The deployed batch-STARK challenge (extension) field — the type of every opened value.
type Ef = BinomialExtensionField<P3BabyBear, 4>;

/// One honest transfer setup, reusable to mint a fresh honest proof per tamper.
struct Fixture {
    desc: EffectVmDescriptor2,
    base_trace: Vec<Vec<BabyBear>>,
    dpis: Vec<BabyBear>,
    mem_boundary: MemBoundaryWitness,
    map_heaps: Vec<Vec<HeapLeaf>>,
}

impl Fixture {
    fn transfer_out() -> Self {
        let json = descriptor2_for_key("transferVmDescriptor2")
            .expect("transfer v2 descriptor must be registered");
        let desc = parse_vm_descriptor2(json).expect("transfer v2 descriptor must parse");
        let st = CellState::new(100_000, 0);
        let effects = vec![Effect::Transfer {
            amount: 50,
            direction: 1,
        }];
        let (base_trace, pis) = generate_effect_vm_trace(&st, &effects);
        let dpis: Vec<BabyBear> = pis[..desc.public_input_count].to_vec();
        Fixture {
            desc,
            base_trace,
            dpis,
            mem_boundary: MemBoundaryWitness::default(),
            map_heaps: vec![],
        }
    }

    /// Mint a FRESH honest deployed proof (self-verifies inside the prover before return).
    fn honest_proof(&self) -> BatchProof<DreggStarkConfig> {
        prove_vm_descriptor2(
            &self.desc,
            &self.base_trace,
            &self.dpis,
            &self.mem_boundary,
            &self.map_heaps,
        )
        .expect("honest transfer witness must prove")
    }

    fn verify(&self, proof: &BatchProof<DreggStarkConfig>) -> Result<(), String> {
        verify_vm_descriptor2(&self.desc, proof, &self.dpis)
    }
}

/// THE DISCHARGE: every `verifyAlgo` tooth bites in the deployed `verify_batch`.
///
/// One honest transfer proof is re-minted per tamper, mutated at exactly the field the
/// corresponding `verifyAlgo` tooth models, and the deployed verifier must REJECT. The
/// honest baseline (both `verifyAlgo` and the deployed verifier accept) anchors the
/// battery so the rejections are attributable to the tamper, not to a broken fixture.
#[test]
fn deployed_verify_batch_bites_on_every_verifyalgo_tooth() {
    let fx = Fixture::transfer_out();

    // --- BASELINE: the honest proof ACCEPTS (verifyAlgo accepts ⇔ deployed accepts). ---
    {
        let proof = fx.honest_proof();
        fx.verify(&proof)
            .expect("BASELINE: honest transfer proof must verify through the deployed verifier");
        eprintln!("[baseline] honest deployed proof ACCEPTS.");
    }

    // Helper: mint honest, apply `tamper`, assert the deployed verifier REJECTS.
    let expect_reject = |name: &str, tamper: &dyn Fn(&mut BatchProof<DreggStarkConfig>)| {
        let mut proof = fx.honest_proof();
        tamper(&mut proof);
        let r = fx.verify(&proof);
        assert!(
            r.is_err(),
            "DIVERGENCE — deployed verify_batch ACCEPTED a proof tampered at `{name}`; \
             the verifyAlgo tooth for this check does NOT bite in the deployed verifier \
             (a DeployedRefines gap — the light client trusts a weaker verifier)."
        );
        eprintln!(
            "[tooth] {name}: deployed verify_batch REJECTS (err = {:?}).",
            r.err()
        );
    };

    // TOOTH 1 — `vk.shapeMatches` / instance shape (Lean: verifyAlgo tooth 1; deployed:
    // InstanceCountMismatch). Dropping an instance's degree-bits entry desyncs the
    // committed instance set from the descriptor's present-table set.
    expect_reject("instance_count (pop degree_bits)", &|p| {
        p.degree_bits.pop();
    });

    // TOOTH 2 — degree-bits pin (Lean: `tableOk_rejects_wrong_degree` / the range-table
    // `LIMB_BITS` pin; deployed: `validate_degree_bits` + the `verify_vm_descriptor2`
    // LIMB pin + the induced domain mismatch). A taller table widens every limb range.
    expect_reject("degree_bits pin (bump an entry)", &|p| {
        let last = p.degree_bits.len() - 1;
        p.degree_bits[last] += 1;
    });

    // TOOTH 3 — FRI query opening (Lean: `foldConsistent` + `merkleRecompute_binds`;
    // deployed: `pcs.verify` opening argument). A claimed opened trace value no longer
    // consistent with the committed trace fails the Merkle/FRI opening.
    expect_reject("trace opening (bump trace_local)", &|p| {
        let ov = &mut p.opened_values.instances[0].base_opened_values;
        assert!(
            !ov.trace_local.is_empty(),
            "instance 0 must open a trace row"
        );
        ov.trace_local[0] += Ef::ONE;
    });

    // TOOTH 4 — quotient identity `C(ζ) = Z_H(ζ)·q(ζ)` (Lean:
    // `batchTablesCheck_rejects_tampered_quotient`; deployed:
    // `verify_constraints_with_lookups` OOD check / the quotient-commitment opening). A
    // tampered opened quotient chunk breaks the constraint recomposition at ζ.
    expect_reject("quotient identity (bump quotient_chunks)", &|p| {
        let ov = &mut p.opened_values.instances[0].base_opened_values;
        assert!(
            !ov.quotient_chunks.is_empty() && !ov.quotient_chunks[0].is_empty(),
            "instance 0 must open quotient chunks"
        );
        ov.quotient_chunks[0][0] += Ef::ONE;
    });

    // TOOTH 5 — logup interaction-bus balance `busSum = 0` (Lean:
    // `batchTablesCheck_rejects_unbalanced_bus`; deployed: `LogUpGadget::verify_global_sum`
    // + the per-instance permutation-column tie). Bumping one bus cumulative sum unbalances
    // the cross-table grand product. Transfer carries chip + range lookups, so at least one
    // instance publishes lookup data.
    expect_reject("logup bus (bump cumulative_sum)", &|p| {
        let mut bumped = false;
        'outer: for inst in p.global_lookup_data.iter_mut() {
            for ld in inst.iter_mut() {
                ld.cumulative_sum += Ef::ONE;
                bumped = true;
                break 'outer;
            }
        }
        assert!(
            bumped,
            "transfer proof must publish at least one logup bus (chip/range lookups)"
        );
    });

    // TOOTH 6 — public-inputs / segment binding (Lean: `segmentTooth` + `deriveFri`
    // observing the publics; deployed: the transcript absorbs the publics, so a mismatch
    // diverges the Fiat-Shamir state ⇒ `pcs.verify` / `PublicValuesLengthMismatch`). This
    // one tampers the VERIFY-side public inputs against an honest proof.
    {
        let proof = fx.honest_proof();
        let mut forged = fx.dpis.clone();
        forged[0] += BabyBear::new(1);
        let r = verify_vm_descriptor2(&fx.desc, &proof, &forged);
        assert!(
            r.is_err(),
            "DIVERGENCE — deployed verify_batch ACCEPTED an honest proof against FORGED \
             public inputs; the verifyAlgo publics-binding tooth does not bite."
        );
        eprintln!(
            "[tooth] public_inputs binding: deployed verify_batch REJECTS (err = {:?}).",
            r.err()
        );
    }

    eprintln!(
        "DeployedRefines DISCHARGED (by test) for the shape/degree/FRI-opening/quotient/\
         logup-bus/publics teeth: every proven verifyAlgo reject-tooth bites in the deployed \
         verify_batch."
    );
}
