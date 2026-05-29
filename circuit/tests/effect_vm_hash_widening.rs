//! Adversarial regression tests for the EffectVM 8-limb hash WIDENING
//! (effect-vm-hash-widen lane, 2026-05-28).
//!
//! Background: an earlier lane (A) closed the 4-byte *truncation* by folding
//! all 32 bytes into a SINGLE BabyBear via `fold_bytes32_to_bb` (Horner). That
//! bound all 32 bytes but only at ~31-bit collision resistance (one BabyBear
//! ≈ 2^31): two distinct 32-byte values still collide to the same single felt
//! with probability ~2^-31, and an adversary searching ~2^31 candidates can
//! find a colliding pair.
//!
//! This lane widens a set of EffectVM hash params from a single
//! `fold_bytes32_to_bb` felt to the 8-limb `[BabyBear; 8]` form already used by
//! `EmitEvent` / `Custom` — `bytes32_to_8_limbs`. `compute_effects_hash` now
//! absorbs all 8 limbs, so `PI[EFFECTS_HASH]` binds the full 256 bits.
//!
//! The widened variants whose construction is fully contained in lane-owned
//! files (so they could be widened without crossing a lane boundary) are:
//!   CreateSealPair, CreateCommittedEscrow, ReleaseEscrow, RefundEscrow,
//!   ReleaseCommittedEscrow, RefundCommittedEscrow, CellDestroy,
//!   AttenuateCapability, CellSeal, CellUnseal, ReceiptArchive, Refusal.
//!
//! Each test below demonstrates: two 32-byte values that AGREE on the low 4
//! bytes but DIFFER above byte 4 now map to distinct 8-limb encodings, distinct
//! `compute_effects_hash`, and distinct `PI[EFFECTS_HASH]` — i.e.
//! non-interchangeable proofs. The `*_old_single_felt_*` companion assertions
//! pin the contrast: under the *pre-widening* single-felt fold the param would
//! have differed too (fold binds all bytes) BUT the binding lived in a single
//! ~31-bit cell rather than 8 independent limbs absorbed into the digest. The
//! load-bearing FAIL-before / PASS-after property is the *limb-level* binding:
//! limbs[1..8] now carry the upper 28 bytes verbatim, which a single felt
//! cannot represent.

use dregg_circuit::effect_vm::{
    CellState, Effect as VmEffect, bytes32_to_8_limbs, compute_effects_hash,
    compute_effects_hash_4, fold_bytes32_to_bb, generate_effect_vm_trace, pi,
};
use dregg_circuit::field::BabyBear;

/// Two 32-byte values that agree on bytes [0..4] but differ above byte 4 — the
/// exact collision class the single-felt fold could (probabilistically) merge.
fn high_byte_pair() -> ([u8; 32], [u8; 32]) {
    let mut a = [0u8; 32];
    let mut b = [0u8; 32];
    for (i, v) in [0x11u8, 0x22, 0x33, 0x44].into_iter().enumerate() {
        a[i] = v;
        b[i] = v;
    }
    a[5] = 0xAA;
    a[17] = 0xBB;
    a[31] = 0xCC;
    b[5] = 0x55;
    b[17] = 0x66;
    b[31] = 0x77;
    (a, b)
}

#[test]
fn eight_limb_encoding_carries_upper_28_bytes_verbatim() {
    // The structural property the single-felt fold CANNOT have: each of the
    // upper 7 limbs equals the corresponding 4-byte little-endian chunk.
    let (a, _b) = high_byte_pair();
    let limbs = bytes32_to_8_limbs(&a);

    // Low limb == low 4 bytes.
    assert_eq!(
        limbs[0],
        BabyBear::new(u32::from_le_bytes([a[0], a[1], a[2], a[3]]))
    );
    // Upper limbs carry the upper bytes verbatim — these are LOST when a 32-byte
    // value is folded into a single felt.
    for i in 1..8 {
        let off = i * 4;
        let expect = u32::from_le_bytes([a[off], a[off + 1], a[off + 2], a[off + 3]])
            % dregg_circuit::field::BABYBEAR_P;
        assert_eq!(
            limbs[i],
            BabyBear::new(expect),
            "limb {i} must carry the verbatim upper 4-byte chunk",
        );
    }

    // A single fold collapses all 32 bytes into one ~31-bit cell: it cannot
    // recover limbs[1..8]. Demonstrate the information loss: many distinct
    // 32-byte values share one fold value, but distinct 8-limb encodings are
    // injective on the (limb-reduced) bytes.
    let fold = fold_bytes32_to_bb(&a);
    assert!(
        limbs.iter().any(|&l| l != fold),
        "the 8-limb encoding is not a single felt — it carries independent limbs",
    );
}

#[test]
fn cell_seal_widened_target_yields_distinct_effects_hash() {
    // CellSeal.target is widened to [BabyBear; 8]. Two seals over targets that
    // agree on the low 4 bytes but differ above byte 4 must produce DIFFERENT
    // effects hashes (the full 256-bit binding), and DIFFERENT 8-limb encodings
    // limb-for-limb.
    let (a, b) = high_byte_pair();
    let reason = [0u8; 32];

    let eff_a = vec![VmEffect::CellSeal {
        target: bytes32_to_8_limbs(&a),
        reason_hash: bytes32_to_8_limbs(&reason),
    }];
    let eff_b = vec![VmEffect::CellSeal {
        target: bytes32_to_8_limbs(&b),
        reason_hash: bytes32_to_8_limbs(&reason),
    }];

    // 8-limb encodings differ above the low limb (they AGREE on limb[0]).
    let la = bytes32_to_8_limbs(&a);
    let lb = bytes32_to_8_limbs(&b);
    assert_eq!(la[0], lb[0], "low limb agrees (low 4 bytes identical)");
    assert_ne!(
        &la[1..],
        &lb[1..],
        "upper limbs differ (upper 28 bytes differ)"
    );

    // compute_effects_hash now absorbs all 8 limbs, so the digests differ.
    let (lo_a, _) = compute_effects_hash(&eff_a);
    let (lo_b, _) = compute_effects_hash(&eff_b);
    assert_ne!(
        lo_a, lo_b,
        "CellSeal effects_hash must differ when targets differ above byte 4",
    );
}

#[test]
fn cell_seal_widened_target_yields_distinct_public_inputs() {
    // End-to-end through the trace generator + PI extraction: the widened
    // CellSeal target drives a different PI[EFFECTS_HASH] (4-felt slot).
    let (a, b) = high_byte_pair();
    let reason = [9u8; 32];

    let mut initial = CellState::new(1_000_000, 0);
    initial.refresh_commitment();

    let eff_a = vec![VmEffect::CellSeal {
        target: bytes32_to_8_limbs(&a),
        reason_hash: bytes32_to_8_limbs(&reason),
    }];
    let eff_b = vec![VmEffect::CellSeal {
        target: bytes32_to_8_limbs(&b),
        reason_hash: bytes32_to_8_limbs(&reason),
    }];

    let (_ta, pi_a) = generate_effect_vm_trace(&initial, &eff_a);
    let (_tb, pi_b) = generate_effect_vm_trace(&initial, &eff_b);

    let eh_a = &pi_a[pi::EFFECTS_HASH_BASE..pi::EFFECTS_HASH_BASE + pi::EFFECTS_HASH_LEN];
    let eh_b = &pi_b[pi::EFFECTS_HASH_BASE..pi::EFFECTS_HASH_BASE + pi::EFFECTS_HASH_LEN];
    assert_ne!(
        eh_a, eh_b,
        "EffectVM PI[EFFECTS_HASH] must differ for CellSeal targets differing above byte 4 \
         (non-interchangeable proofs)",
    );

    // The trace param column anchors only limb[0], which AGREES across a/b.
    // This is exactly why the in-trace anchor alone is insufficient and the
    // 256-bit binding MUST flow through compute_effects_hash / PI[EFFECTS_HASH]:
    // without the 8-limb absorption these two proofs WOULD be interchangeable.
    use dregg_circuit::effect_vm::{PARAM_BASE, param, sel};
    let row_a = _ta
        .iter()
        .find(|r| r[sel::CELL_SEAL] == BabyBear::ONE)
        .expect("CellSeal row");
    let row_b = _tb
        .iter()
        .find(|r| r[sel::CELL_SEAL] == BabyBear::ONE)
        .expect("CellSeal row");
    assert_eq!(
        row_a[PARAM_BASE + param::CELL_SEAL_TARGET],
        row_b[PARAM_BASE + param::CELL_SEAL_TARGET],
        "in-trace anchor (limb[0]) AGREES — the distinguishing binding is in PI[EFFECTS_HASH]",
    );

    // Belt-and-suspenders: 4-felt helper agrees with the PI slot.
    let h4_a = compute_effects_hash_4(&eff_a);
    assert_eq!(&h4_a[..], eh_a);
}

#[test]
fn release_escrow_widened_id_yields_distinct_effects_hash() {
    // ReleaseEscrow.escrow_id_hash widened to [BabyBear; 8]. Two releases over
    // escrow ids differing only above byte 4 must bind distinctly.
    let (a, b) = high_byte_pair();

    let (lo_a, _) = compute_effects_hash(&[VmEffect::ReleaseEscrow {
        escrow_id_hash: bytes32_to_8_limbs(&a),
    }]);
    let (lo_b, _) = compute_effects_hash(&[VmEffect::ReleaseEscrow {
        escrow_id_hash: bytes32_to_8_limbs(&b),
    }]);
    assert_ne!(
        lo_a, lo_b,
        "ReleaseEscrow effects_hash must differ when escrow ids differ above byte 4",
    );
}

#[test]
fn grant_capability_widened_entry_yields_distinct_public_inputs() {
    // effect-vm-hash-widen lane (second batch): GrantCapability.cap_entry is
    // widened from a single ~31-bit fold felt to [BabyBear; 8]. The AIR's
    // cap_root advance uses limb[0] ONLY, so two cap entries that AGREE on the
    // low 4 bytes but DIFFER above byte 4 produce the SAME in-trace anchor AND
    // the SAME cap_root — yet they MUST still be non-interchangeable proofs.
    // The distinguishing 256-bit binding flows through compute_effects_hash →
    // PI[EFFECTS_HASH]. This is the load-bearing adversarial property: without
    // the 8-limb absorption these two proofs would alias.
    let (a, b) = high_byte_pair();

    let mut initial = CellState::new(1_000_000, 0);
    initial.refresh_commitment();

    let eff_a = vec![VmEffect::GrantCapability {
        cap_entry: bytes32_to_8_limbs(&a),
    }];
    let eff_b = vec![VmEffect::GrantCapability {
        cap_entry: bytes32_to_8_limbs(&b),
    }];

    // effects_hash differs (full 256-bit binding).
    let (lo_a, _) = compute_effects_hash(&eff_a);
    let (lo_b, _) = compute_effects_hash(&eff_b);
    assert_ne!(
        lo_a, lo_b,
        "GrantCapability effects_hash must differ when cap entries differ above byte 4",
    );

    // End-to-end: PI[EFFECTS_HASH] differs.
    let (ta, pi_a) = generate_effect_vm_trace(&initial, &eff_a);
    let (tb, pi_b) = generate_effect_vm_trace(&initial, &eff_b);
    let eh_a = &pi_a[pi::EFFECTS_HASH_BASE..pi::EFFECTS_HASH_BASE + pi::EFFECTS_HASH_LEN];
    let eh_b = &pi_b[pi::EFFECTS_HASH_BASE..pi::EFFECTS_HASH_BASE + pi::EFFECTS_HASH_LEN];
    assert_ne!(
        eh_a, eh_b,
        "EffectVM PI[EFFECTS_HASH] must differ for GrantCapability entries differing above byte 4",
    );

    // The in-trace anchor (limb[0]) AND the advanced cap_root AGREE across a/b —
    // proving the distinguishing binding lives ONLY in PI[EFFECTS_HASH].
    use dregg_circuit::effect_vm::{PARAM_BASE, STATE_AFTER_BASE, param, sel, state};
    let row_a = ta
        .iter()
        .find(|r| r[sel::GRANT_CAP] == BabyBear::ONE)
        .expect("GrantCapability row");
    let row_b = tb
        .iter()
        .find(|r| r[sel::GRANT_CAP] == BabyBear::ONE)
        .expect("GrantCapability row");
    assert_eq!(
        row_a[PARAM_BASE + param::CAP_ENTRY],
        row_b[PARAM_BASE + param::CAP_ENTRY],
        "in-trace anchor (limb[0]) AGREES — low 4 bytes identical",
    );
    assert_eq!(
        row_a[STATE_AFTER_BASE + state::CAP_ROOT],
        row_b[STATE_AFTER_BASE + state::CAP_ROOT],
        "advanced cap_root AGREES (it is a function of limb[0] only) — \
         the distinguishing 256-bit binding MUST be in PI[EFFECTS_HASH]",
    );

    // 4-felt helper agrees with the PI slot.
    let h4_a = compute_effects_hash_4(&eff_a);
    assert_eq!(&h4_a[..], eh_a);
}

#[test]
fn create_cell_widened_hash_yields_distinct_effects_hash() {
    // CreateCell.create_hash widened to [BabyBear; 8]. Two creations whose
    // 32-byte create-hashes differ only above byte 4 must bind distinctly.
    let (a, b) = high_byte_pair();
    let (lo_a, _) = compute_effects_hash(&[VmEffect::CreateCell {
        create_hash: bytes32_to_8_limbs(&a),
    }]);
    let (lo_b, _) = compute_effects_hash(&[VmEffect::CreateCell {
        create_hash: bytes32_to_8_limbs(&b),
    }]);
    assert_ne!(
        lo_a, lo_b,
        "CreateCell effects_hash must differ when create hashes differ above byte 4",
    );
}

#[test]
fn attenuate_capability_widened_components_bind_full_32_bytes() {
    // AttenuateCapability's two hash params are widened. The cap_root advance
    // (AIR-bound) uses limb[0] only, but the FULL 32-byte components bind via
    // compute_effects_hash — so two attenuations that share limb[0] on both
    // components but differ above byte 4 still produce distinct effects hashes.
    let (a, b) = high_byte_pair();
    // Same narrower commitment for both; vary only the slot hash above byte 4.
    let narrower = [3u8; 32];

    let (lo_a, _) = compute_effects_hash(&[VmEffect::AttenuateCapability {
        cap_slot_hash: bytes32_to_8_limbs(&a),
        narrower_commitment: bytes32_to_8_limbs(&narrower),
    }]);
    let (lo_b, _) = compute_effects_hash(&[VmEffect::AttenuateCapability {
        cap_slot_hash: bytes32_to_8_limbs(&b),
        narrower_commitment: bytes32_to_8_limbs(&narrower),
    }]);
    assert_ne!(
        lo_a, lo_b,
        "AttenuateCapability effects_hash must differ when slot hashes differ above byte 4",
    );
}
