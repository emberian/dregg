//! Helper functions for the Effect VM AIR.
//!
//! Limb splitting/joining and the `compute_effects_hash` family that
//! produces the per-cell effects digest pinned into PI[EFFECTS_HASH_BASE].

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_many, hash_many_8};

use super::{AUX_BASE, Effect, aux_off};

/// Split a u64 into two BabyBear elements: `(lo = value mod 2^30, hi = value >> 30)`.
///
/// ⚠ **NOT INJECTIVE, IN TWO SEPARATE PLACES — and the contract that stood here
/// ("both values fit in BabyBear (< 2^31)" / "fits in u32 since val < 2^64") was
/// FALSE.** Measured, both poles pinned by
/// `circuit/tests/split_u64_is_not_injective.rs`:
///
///  * `hi` is `(val >> 30) as u32`, and `val >> 30` reaches `2^34` — so the `as u32`
///    **truncates bits 62..64 outright**. `split_u64(2^62)` equals `split_u64(0)` in
///    BOTH limbs, not merely the low one.
///  * `BabyBear::new` then reduces mod `p ≈ 2^31`, so `hi` aliases again at a value
///    period of `p · 2^30 ≈ 2^61`.
///
/// The limb pair is therefore faithful only on `[0, 2^61)`, and the LOW LIMB ALONE is faithful
/// only on `[0, 2^30)`. `param::NOTE_VALUE_HI` (the companion limb) is written by
/// `effect_vm/trace.rs` on both note rows and read by NOTHING: no gate, no PI pin, no verifier.
///
/// ⚑ **THE ACCUMULATOR CONSUMER IS GONE, 2026-07-31.** Until then `cell/src/commitment_set.rs`,
/// `cell/src/nullifier_set.rs` and `cell/src/revoked_set.rs` `accumulator_leaf` carried this low
/// limb into the committed root, so the signed consensus anchor was `2^30`-periodic in a note
/// value. All three now commit the exact tagged linked leaf (`dom ‖ addr17 ‖ value4 ‖ next17`,
/// four `u16` value limbs), `accumulator_leaf` is deleted, and the anchor binds all 64 bits —
/// `turn/tests/note_value_alias_at_2_30_closed.rs`. What still reads this low limb is the
/// IN-CIRCUIT map-op (`param::NOTE_VALUE_LO`), which is the remaining, named residual. The Lean
/// tooth is `metatheory/Dregg2/Bignum/LedgerBalance.lean` `accumulatorLeaf_aliases_at_2_30`.
///
/// ⚑ The arithmetic is DEPLOYED and is deliberately not changed here: this felt pair
/// is the balance-limb encoding the in-circuit 30-bit range proof runs on, it is the
/// preimage `compute_effects_hash_4` absorbs, and the low limb is the leaf value the
/// noteSpend/noteCreate grow-gates open against BY CONSTRAINT
/// (`prmCol NOTE_VALUE_LO`). Widening any of that is a descriptor re-emit plus a VK
/// rotation, not a helper edit.
pub fn split_u64(val: u64) -> (BabyBear, BabyBear) {
    let lo = (val & 0x3FFF_FFFF) as u32; // lower 30 bits
    let hi = (val >> 30) as u32; // bits 30..62 ONLY — bits 62..64 are truncated here
    (BabyBear::new(lo), BabyBear::new(hi))
}

/// Reconstruct a u64 from split BabyBear limbs.
#[allow(dead_code)]
fn join_u64(lo: BabyBear, hi: BabyBear) -> u64 {
    (lo.0 as u64) | ((hi.0 as u64) << 30)
}

/// **THE single family-F1 encoding in the tree** — 8 BabyBear limbs, 4 little-endian bytes each,
/// reduced mod `p`. Position 0 carries bytes `[0..4]`; position 7 carries bytes `[28..32]`.
///
/// Every former duplicate (`bytes32_to_8_limbs`'s callers, the three nested
/// `bytes32_to_8_felts` clones, `bytes32_to_limbs`, `bytes_to_babybear_vec`,
/// `stark_delegation_bytes32_to_babybear`) now calls THIS body. That collapse moved zero bytes:
/// all of them computed the same map. Keeping one body is the point — a second name for the same
/// arithmetic is how the ~17-implementation zoo grew.
///
/// ⚠ **NOT injective, and NOT "canonical".** The word "canonical" used to appear here and is
/// exactly what invited the re-inventions. The mod-`p` reduction identifies a 4-byte chunk `x`
/// with `x + p`, so a colliding pair is CONSTRUCTED in `O(1)` — no grind — wherever the
/// bytes are attacker-chosen. It is deterministic and identical on both projectors, which is why
/// a collision over-includes (an honest turn goes UNSAT) rather than authorizing a forgery; that
/// is an availability property, not a binding one.
///
/// ⚑ **THE ALIAS RATE IS 100%, NOT 53.1% — corrected 2026-08-02.** This doc used to say "a
/// uniformly random chunk needs reducing with probability `1 − p/2^32 = 53.1%`", and every reader
/// since has taken 53.1% for the rate at which a chunk HAS an alias. It is not; it is the rate at
/// which a chunk IS the non-canonical representative, which is a different and more flattering
/// question. `2p = 4026531842 < 2^32`, so `[0, 2^32)` covers every residue class at least twice:
/// `2^32 − 2p = 268435454` residues have THREE `u32` representatives and the other `1744830467`
/// have TWO. **Every chunk value has a sibling**, so every 32-byte value has at least `2^8 = 256`
/// byte-distinct siblings with an identical limb vector (`2^256/p^8 = 2^8.74` on average).
/// Measured by execution — `10000/10000` — in `circuit/tests/degraded_felt_wound_measure.rs`, and
/// proved in general as `every_chunk_has_a_sibling` in
/// `metatheory/Dregg2/Circuit/CapLeafTargetLanes9.lean`, which also refutes this encoder's
/// injectivity (`capFoldLimbs_not_injective`) on the exhibited pair.
///
/// The canonical codec is `dregg_codec::Limbs16` (16 little-endian u16 limbs, injective) with
/// `dregg_codec::Digest8` for committed fixed-width slots. Migrating this call graph onto it is
/// Stage 2 of `docs/DESIGN-canonical-byte-felt-codec.md` — VK-affecting, so not done here.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
#[inline]
pub fn bytes32_to_8_limbs(b: &[u8; 32]) -> [BabyBear; 8] {
    let mut out = [BabyBear::ZERO; 8];
    for i in 0..8 {
        let off = i * 4;
        let v = u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
        out[i] = BabyBear::new(v % crate::field::BABYBEAR_P);
    }
    out
}

/// The free lanes' radix, `2^28`. Strictly below `p = 2013265921`, so a free lane NEVER reduces —
/// `BabyBear::new` is the identity on every value this encoder puts in lanes 2..8. Lean twin:
/// `Dregg2.Circuit.FieldLanes9.CH`, with `CH_lt_P` proved by `decide`.
const LANE9_CH: u32 = 1 << 28;

/// **THE FIELDS NONET — the one and only `fields[0..8]` lane encoder.** The Rust twin of the Lean
/// authority `metatheory/Dregg2/Circuit/FieldLanes9.lean` (`fieldToLanes9`).
///
/// It replaced `field_limbs8`, which is **DELETED, not deprecated** (2026-07-31). There is no second
/// fields encoder to drift against and no compatibility body kept "so downstream forwards remain
/// valid": lane 0/1 agreement was the reason nothing broke while both were live, and two shapes that
/// agree today are two shapes that disagree later.
///
/// ## Substrate, stated plainly
///
/// **The Lean file is the authority; this is its twin.** `fieldToLanes9_injective` and
/// `lanes9ToField_fieldToLanes9` are machine-checked theorems (`#assert_axioms`-clean) about the
/// LEAN encoder — an explicit bijection onto its image with a total decoder and a left inverse, not
/// a hash bound and not a birthday bound. **They are not theorems about this Rust function.** There
/// is no formal semantics of Rust and this body is not extracted from the Lean; what pins the two
/// together is the Lean-COMPUTED protocol vectors and the round-trip sweep in
/// `circuit/tests/field_lanes9_injective.rs`. Read that as "case-tested against a verified spec",
/// never as "verified".
///
/// ## Why nine
///
/// `p = 2013265921`, `log₂ p = 30.907`: eight lanes carry **247.26 bits** against a 32-byte field's
/// **256**, so *no* 8-lane encoding of 32 bytes is injective under ANY chunking — pigeonhole, before
/// a line of code is read. That is why every previous repair of this octet (an eight-way Horner
/// fold, then a `u32 % p` chunking, then a Poseidon2 image over an injective preimage) moved the
/// attacker's COST and never reached injectivity; the last of them priced out at a `2^92.7`
/// collision, below the ~124-bit bar quoted elsewhere in this tree. `P^8 < 2^256 ≤ P^9`
/// (`nine_lanes_is_the_minimum`): nine is the minimum, and this is that encoding.
///
/// ## The layout
///
/// ```text
///   lane 0   = u32::from_be_bytes(b[28..32]) % p      -- the kernel u64 lane's lo32, deployed ABI
///   lane 1   = u32::from_be_bytes(b[24..28]) % p      -- the kernel u64 lane's hi32, deployed ABI
///
///   q0 = u32::from_be_bytes(b[28..32]) / p            -- in {0,1,2}, since 2p < 2^32
///   q1 = u32::from_be_bytes(b[24..28]) / p            -- in {0,1,2}
///   carry = q0 + 4·q1                                 -- ≤ 10, ONE base-256 digit
///
///   W = ofDigits 256 ([b[0], …, b[23]] ++ [carry])    -- 25 base-256 digits, low first
///   lane 2+i = (W / 2^(28i)) % 2^28,  i = 0..6        -- seven 28-bit digits, low first
/// ```
///
/// `W < 11·2^192 < 2^196 = (2^28)^7`, so it is EXACTLY seven base-`2^28` digits and nothing
/// reduces. `7 × 28 = 196` is the tight fit, and the `u32 % p` lane shape — the shape that aliased —
/// never appears among the free lanes.
///
/// ## Why lanes 0 and 1 could not move
///
/// Together they are the kernel's u64 lane (`field_from_u64`'s payload window, bytes `24..32`):
/// lane 0 is welded to the v1 face column `stateBase + FIELD_BASE + i`, forced by `gFieldWriteP1`
/// against `param1`, and read by `field_to_u64`; lane 1 is the staged capacity descriptors' named
/// hi-pin slot. The escrow / discharge / vault welds, `setfield_encoder_window_gate` and every app
/// encoder (`deos-js-core::pack_u64`, `starbridge-web-surface::pack_coord`) depend on lane 0
/// carrying the RAW numeric value **for `v < p = 2013265921`** — not `v < 2^31`, which is what the
/// deleted `field_limbs8` doc claimed until 2026-07-30 and is false across the 134-million-wide
/// window `[p, 2^31)`. Above `p` lane 0 is the residue and the quotient rides lane 8.
/// So injectivity had to come from the seven free lanes PLUS those two — never by moving them. The
/// pinned pair is asserted against an INDEPENDENT transcription of the ABI (big-endian `u32` over
/// `b[28..32]` / `b[24..28]`, reduced) in
/// `field_lanes9_injective.rs::lanes_0_and_1_are_the_deployed_big_endian_u64_window`, not against a
/// second encoder body — the previous pin compared this function to `field_limbs8`, which meant it
/// went silent the moment that twin was deleted.
///
/// Lane 0 STILL ALIASES on its own — `x` and `x + p` share it, and that is the pinned ABI. What
/// changed is that the ALIAS NO LONGER REACHES THE VECTOR: the quotient it drops is carried in the
/// carry digit and therefore in lane 8. That pair is the alias pole of the test.
///
/// The exact inverse is [`field_from_lanes9`] (Lean `lanes9ToField`).
#[inline]
pub fn field_limbs9(b: &[u8; 32]) -> [BabyBear; 9] {
    let p = crate::field::BABYBEAR_P;
    let lo = u32::from_be_bytes([b[28], b[29], b[30], b[31]]);
    let hi = u32::from_be_bytes([b[24], b[25], b[26], b[27]]);

    let mut out = [BabyBear::ZERO; 9];
    out[0] = BabyBear::new(lo % p);
    out[1] = BabyBear::new(hi % p);

    // THE DISAMBIGUATION DIGIT. `2p = 4026531842 < 2^32`, so each quotient is 0, 1 or 2 and the
    // digit is `≤ 2 + 4·2 = 10 < 16`: it fits ONE base-256 byte with its top four bits clear, which
    // is what makes 7 × 28 = 196 bits an exact fit for the 25 source digits' 200.
    let carry = (lo / p) + 4 * (hi / p);
    debug_assert!(
        carry < 16,
        "carry digit {carry} must be < 16 — its top nibble is the 4 bits 7×28=196 does not cover"
    );

    // W's 25 base-256 digits, low first: the 24 bytes the pinned lanes carry NOTHING about, then
    // the carry. Streamed into seven 28-bit limbs through a bit accumulator (W is 196 bits; there
    // is no u196).
    let mut src = [0u8; 25];
    src[..24].copy_from_slice(&b[..24]);
    src[24] = carry as u8;

    let mut acc: u64 = 0;
    let mut nbits: u32 = 0;
    let mut next = 0usize;
    for lane in out[2..9].iter_mut() {
        while nbits < 28 {
            let byte = if next < src.len() { src[next] } else { 0 };
            acc |= (byte as u64) << nbits;
            next += 1;
            nbits += 8;
        }
        // `< 2^28 < p`, so this reduction is the identity — the free lanes never reduce.
        *lane = BabyBear::new((acc as u32) & (LANE9_CH - 1));
        acc >>= 28;
        nbits -= 28;
    }
    debug_assert_eq!(acc, 0, "the 4 bits above 196 must be zero — carry < 16");
    out
}

/// **THE DECODER** — the exact inverse of [`field_limbs9`] on its image, and TOTAL everywhere else.
/// The Rust twin of Lean `Dregg2.Circuit.FieldLanes9.lanes9ToField`.
///
/// Totality matters: this is an adversarial-test entry point, so a forged lane vector (a "free"
/// lane ≥ `2^28`, up to `p−1`) must still decode to *something* rather than panic or wrap. It
/// mirrors Lean's `decWord = ofDigits CH (laneList L)` exactly, including on those inputs —
/// `Σ lanes[2+i]·(2^28)^i < 2^200` even at the maximum, so the 25 base-256 digits are complete and
/// the accumulation is done with carry propagation over a 26-byte buffer rather than a 196-bit
/// stream.
///
/// `field_from_lanes9(&field_limbs9(&b)) == b` for EVERY `b` is the Lean theorem
/// `lanes9ToField_fieldToLanes9`; in this crate it is a swept test, not a proof.
#[inline]
pub fn field_from_lanes9(lanes: &[BabyBear; 9]) -> [u8; 32] {
    // W = Σ_{i<7} lanes[2+i] · (2^28)^i, as little-endian base-256 digits. The terms OVERLAP when a
    // free lane exceeds 2^28 (only a forged vector does), so this is a carry-propagating add rather
    // than a concatenation of digits.
    let mut w = [0u8; 26];
    for i in 0..7usize {
        let bits = 28 * i;
        // 28·i mod 8 ∈ {0, 4}; the lane is < p < 2^31, so the shifted value is < 2^35.
        let mut v = (lanes[2 + i].as_u32() as u64) << (bits % 8);
        let mut j = bits / 8;
        while v != 0 && j < w.len() {
            let s = w[j] as u64 + (v & 0xFF);
            w[j] = (s & 0xFF) as u8;
            v = (v >> 8) + (s >> 8);
            j += 1;
        }
    }

    let carry = w[24] as u64;
    let p = crate::field::BABYBEAR_P as u64;
    // Undo the pinned lanes' `mod p` reduction with the quotients the carry digit held.
    let hi = lanes[1].as_u32() as u64 + (carry / 4) * p;
    let lo = lanes[0].as_u32() as u64 + (carry % 4) * p;

    let mut out = [0u8; 32];
    out[..24].copy_from_slice(&w[..24]);
    out[24..28].copy_from_slice(&((hi & 0xFFFF_FFFF) as u32).to_be_bytes());
    out[28..32].copy_from_slice(&((lo & 0xFFFF_FFFF) as u32).to_be_bytes());
    out
}

/// The KEY nonet's radix exponent: lanes 0..=7 are base-`2^29` digits. `2^29 = 536870912 < p`, so
/// **no lane ever reduces** and the encoding is not a `mod p` map. Lean twin:
/// `Dregg2.Circuit.KeyLanes9.K`, and the emitted layout carries the same number as
/// [`super::layout_generated::KEY_LANE_BITS`] — the pin below compares the two.
const KEY9_LANE_BITS: usize = 29;

/// The top lane's width, `2^256 / (2^29)^8 = 2^24`. NARROWER by construction, and that is
/// load-bearing rather than incidental: a *uniform* nine-lane check at 29 bits admits
/// `[0, …, 0, 2^24]`, whose value is exactly `2^256` and which decodes byte-for-byte to the
/// all-zero key. Lean twin: `Dregg2.Circuit.KeyLanes9.KTOP`.
const KEY9_TOP_BITS: usize = 24;

/// The pin, against the EMITTED layout rather than against these two constants' own sum — two
/// independent sources, so this is a gate and not a decoration. A lane widening that forgets the
/// top lane cannot survive it, and neither can a Lean-side move that does not reach this file.
const KEY_NONET_MATCHES_THE_EMITTED_LAYOUT: () = assert!(
    KEY9_LANE_BITS == super::layout_generated::KEY_LANE_BITS
        && KEY9_TOP_BITS == super::layout_generated::KEY_TOP_BITS
        && 8 * KEY9_LANE_BITS + KEY9_TOP_BITS == 256
);

/// **THE OWNER-KEY NONET'S NINE IN-BLOCK COLUMNS**, lane order — the Rust counterpart of Lean
/// `Emit.KeyCanonicity9Emit.deployedKeyCols`, which is likewise a FUNCTION of the layout rather
/// than a ninth constant beside it.
///
/// ⚠ **NOT contiguous, and never reconstructible with a stride.** Lanes 0..=7 are the deployed
/// octet at `B_PUBKEY_OCTET = 105`; lane 8 is at `B_PUBKEY_NINTH_LANE = 186`, past the whole
/// completion band. A `[base + i for i in 0..9]` here would silently claim column 113, which
/// belongs to `fields[0]`'s completion window — the shape that made ~143 rotated members UNSAT
/// across the `178 → 184` flag day.
///
/// The two indices come from genuinely different places in the emitted layout — the octet BASE
/// table and the NINTH-LANE table — and the assertion below compares this construction against
/// both of them positionally. That is what makes it a gate rather than a pin against its own
/// definition: move the lane in Lean without moving its octet, or vice versa, and this stops
/// compiling.
pub const PUBKEY_NONET_LANE_COL: [usize; 9] = {
    use super::layout_generated::{
        B_PUBKEY_NINTH_LANE, B_PUBKEY_OCTET, ROTATED_OCTET_BASES, ROTATED_OCTET_NINTH_LANES,
    };
    // The owner key is app-PI octet index 2 of the three carrier octets.
    assert!(ROTATED_OCTET_BASES[2] == B_PUBKEY_OCTET);
    assert!(ROTATED_OCTET_NINTH_LANES[2] == B_PUBKEY_NINTH_LANE);
    // The ninth lane must be an ABSORBED pre-limb or `wireCommitR` never folds it and the column
    // carries nothing — the exact condition Lean states as `lane8_is_absorbed_iff`.
    assert!(B_PUBKEY_NINTH_LANE < super::layout_generated::NUM_PRE_LIMBS);
    // …and it must not alias the octet band it completes, NOR sit flush against it. ⚑ This read
    // `>= B_PUBKEY_OCTET + 8` until 2026-08-08, which ADMITS the one geometry the docblock above
    // forbids: at exactly `B_PUBKEY_OCTET + 8` the nonet IS contiguous and `[base + i; 9]` — the
    // stride reconstruction this whole table exists to make impossible — silently becomes correct,
    // so the next reader who writes one is not stopped. STRICT.
    assert!(B_PUBKEY_NINTH_LANE > B_PUBKEY_OCTET + 8);
    [
        B_PUBKEY_OCTET,
        B_PUBKEY_OCTET + 1,
        B_PUBKEY_OCTET + 2,
        B_PUBKEY_OCTET + 3,
        B_PUBKEY_OCTET + 4,
        B_PUBKEY_OCTET + 5,
        B_PUBKEY_OCTET + 6,
        B_PUBKEY_OCTET + 7,
        B_PUBKEY_NINTH_LANE,
    ]
};

/// **THE KEY NONET — a 32-byte canonical value → nine BabyBear lanes, base `2^29`, little-endian.**
/// The Rust twin of the Lean authority `metatheory/Dregg2/Circuit/KeyLanes9.lean` (`keyToLanes9`):
/// read the 32 bytes as one little-endian 256-bit number and take its nine base-`2^29` digits.
/// Lanes 0..=7 are below `2^29`; lane 8 is below `2^24` because `2^256 / (2^29)^8 = 2^24`. The
/// image is therefore **exactly `2^256`** — the encoding step loses nothing and there is no
/// encoding collision to bound at all.
///
/// ## What this body is, and what it is not
///
/// It is not a new transcription. `trace.rs::canonical_id_to_felts_4` inlined this exact loop and
/// now calls it, so the count of bodies in the tree did not change — what changed is that the
/// fourth twin has a NAME, and therefore an entry in the cross-check
/// (`commit/tests/key_octet_f2_twins_and_the_hole.rs`) that the other three already had. An
/// unnamed inline copy is precisely the copy a twin test cannot see.
///
/// The other three are `dregg_commit::typed::canonical_32_to_lanes_9` (the authoring site),
/// `dregg_cell::commitment::canonical_to_babybear_nonet`, and
/// `dregg_storage::commitment::canonical_32_to_lanes_9`. They are deliberately independent
/// re-typings: re-typing IS the review, and the `178 → 184` flag day rotted on a derived constant
/// that had been "improved" into a relation.
///
/// ## Substrate, stated plainly
///
/// `keyToLanes9_injective` and `keyLanes9ToBytes_keyToLanes9` are machine-checked **Lean** theorems
/// — a total decoder plus a left inverse, not a hash bound and not a birthday bound. There is no
/// formal semantics of Rust and this body is not extracted from that Lean. What pins the two is the
/// round-trip sweep against [`key_from_lanes9`] and the twin corpus. Read that as "case-tested
/// against a verified spec", never as "verified".
///
/// ## ⚠ A key needs INJECTIVITY, not collision resistance
///
/// The figure to quote here is **`2^256` image, injective** — never the `2^123.63` birthday
/// collision bound, which is the answer for a *hash node* and has been misquoted in this key's
/// place more than once. Eight BabyBear lanes carry `8 · log₂ p = 247.26` bits against 256 and lose
/// by pigeonhole whatever they contain; nine carry 278.16, which is why `2^256` fits inside them
/// with room and why the top lane must be checked at 24 bits rather than 29.
#[inline]
pub fn key_limbs9(canonical: &[u8; 32]) -> [BabyBear; 9] {
    let () = KEY_NONET_MATCHES_THE_EMITTED_LAYOUT;
    std::array::from_fn(|i| {
        let bit = i * KEY9_LANE_BITS;
        // 29 bits starting at an offset of 0..=7 spans at most 36 bits, so a five-byte window is
        // always enough and always fits a u64.
        let mut acc: u64 = 0;
        for k in 0..5usize {
            if let Some(byte) = canonical.get(bit / 8 + k) {
                acc |= u64::from(*byte) << (8 * k);
            }
        }
        acc >>= bit % 8;
        BabyBear::new((acc & ((1u64 << KEY9_LANE_BITS) - 1)) as u32)
    })
}

/// **THE KEY DECODER** — total, and the left inverse of [`key_limbs9`] on every 32-byte value. The
/// Rust twin of Lean `Dregg2.Circuit.KeyLanes9.keyLanes9ToBytes`.
///
/// Total on *every* lane vector, including vectors outside the encoder's image, which it reads
/// modulo `2^256` exactly as the Lean does. That totality is what makes the canonicity envelope's
/// exhibit expressible at all: `[0, …, 0, 2^24]` has every lane below `2^29`, so it passes a
/// *uniform* nine-lane range check, and it decodes byte-for-byte to the all-zero key. The
/// envelope's second leg — lane 8 below `2^24` — is what refuses it, and it is not a consequence
/// of the first.
#[inline]
pub fn key_from_lanes9(lanes: &[BabyBear; 9]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, lane) in lanes.iter().enumerate() {
        let v = u64::from(lane.as_u32());
        for k in 0..KEY9_LANE_BITS {
            if (v >> k) & 1 == 1 {
                let bit = i * KEY9_LANE_BITS + k;
                if bit < 256 {
                    out[bit / 8] |= 1 << (bit % 8);
                }
            }
        }
    }
    out
}

/// **THE SOVEREIGN KEY_COMMIT TEETH — the ONE denotation the AIR, the producer and the executor
/// all name.**
///
/// The four published `SOVEREIGN_WITNESS_KEY_COMMIT` felts of a committed owner-key NONET:
///
/// ```text
///   teeth[q] = chip_absorb_all_lanes(4, [nonet[KEY_COMMIT_QUAD_IDX[q][j]] for j in 0..4])[0]
/// ```
///
/// `chip_absorb_all_lanes(4, x)[0]` is bit-identically `poseidon2::hash_4_to_1(x)` and is EXACTLY
/// one arity-4 row of the deployed Poseidon2 chip, so the four quads are the four chip lookups the
/// Lean-authored gate emits (`Emit.CarrierOctetGates.keyCommitSpec` / `keyCommitConstraints`).
///
/// ## ⚑ Why this function exists at all — the wound it closes (2026-08-08)
///
/// This recipe used to be spelled THREE times: once in the Lean AIR, once as a
/// `const QUAD_IDX: [[usize; 4]; 4]` hand-typed inside
/// `trace_rotated::append_sovereign_key_commit_rider`, and once — by reference — in
/// `TurnExecutor::pubkey_to_witness_key_commit`, which simply called
/// `dregg_commit::typed::canonical_32_to_felts_4`. On 2026-08-01 the key-nonet flag day
/// (`6441705e8`) rewrote THAT function into a single arity-16 absorb over the nonet, on a census
/// which recorded the four-felt id fold as off-AIR — "no descriptor width, no PI count, no VK". The
/// census missed this consumer. From that commit the executor computed one function and the AIR
/// forced a different one: transcript divergence, `InvalidPowWitness`, and
/// `rotated_sovereign_make_sovereign_proves_and_verifies` red while its nine record-pin siblings
/// passed.
///
/// The single-file repair — point the executor back at the octet recipe — was FORBIDDEN, because
/// the octet cover was itself the second half of the wound: `KEY_COMMIT_QUAD_IDX` read only lanes
/// 0..7, and lane 8 is the ONLY committed column carrying source bit 255, which RFC 8032 makes an
/// Ed25519 key's x-sign. A key and its negation — a keypair whose private half is `-a mod L`, which
/// an attacker HOLDS — therefore published bit-identical teeth. Row 2 now reads `[8, 0, 4, 2]`
/// instead of `[0, 4, 2, 6]`: full nine-lane cover, unchanged arity, unchanged
/// `KEY_COMMIT_SPAN = 32`, unchanged trace width.
///
/// ## Substrate, stated plainly
///
/// [`KEY_COMMIT_QUAD_IDX`](super::layout_generated::KEY_COMMIT_QUAD_IDX) is GENERATED by
/// `EmitLayoutManifest.lean` from `CarrierOctetGates.quadIdx`, so the matrix has ONE source and
/// this body is its reader. The FOLD (four arity-4 absorbs, project lane 0) is written once here
/// and called by both the producer rider and the executor — but it is a Rust re-typing of the Lean
/// `keyCommitSpec`, not an extraction from it. There is no formal semantics of Rust. Read this as
/// "one emitted matrix, one Rust fold, pinned to the Lean spec by a differential" — never as
/// "verified".
#[inline]
pub fn key_commit_teeth_from_nonet(nonet: &[BabyBear; 9]) -> [BabyBear; 4] {
    use super::layout_generated::{KEY_COMMIT_QUAD_IDX, KEY_NONET_LANES};
    // The emitted matrix indexes a NONET. If a future emit narrows it back to eight lanes this
    // stops compiling rather than silently re-opening the A/-A collision.
    const _: () = assert!(KEY_NONET_LANES == 9);
    std::array::from_fn(|q| {
        let inputs: [BabyBear; 4] = std::array::from_fn(|j| nonet[KEY_COMMIT_QUAD_IDX[q][j]]);
        crate::descriptor_ir2::chip_absorb_all_lanes(4, &inputs)[0]
    })
}

/// [`key_commit_teeth_from_nonet`] of a 32-byte Ed25519 public key — the executor-side entry point
/// (`TurnExecutor::pubkey_to_witness_key_commit`). The nonet is [`key_limbs9`], which is what the
/// producer writes into [`PUBKEY_NONET_LANE_COL`], so the executor's teeth and the committed
/// columns' teeth are the same function of the same value.
#[inline]
pub fn key_commit_teeth(pubkey: &[u8; 32]) -> [BabyBear; 4] {
    key_commit_teeth_from_nonet(&key_limbs9(pubkey))
}

/// Fold of a full 32-byte value into a single BabyBear. **⚠ NOT collision-resistant — `O(1)`, and
/// `O(1)` even for a CHOSEN TARGET.** This doc used to open with "Collision-resistant fold" and
/// claim `~2^-31`; both are wrong, and the repo's own test says so
/// (`circuit/tests/effects_hash_fold_and_burn_target_width.rs`,
/// `fold_bytes32_to_bb_collides_in_o1_because_it_is_linear`, which exhibits the constructor).
///
/// `Σ limbᵢ · MIX^i (mod p)` is an **onto F_p-linear form** on the limb vector. Therefore:
/// finding a colliding pair is one linear solve, and finding a preimage of ANY chosen felt is one
/// linear solve. The `~2^-31` figure is the probability that two INDEPENDENT UNIFORM inputs
/// happen to collide — it is not an adversarial cost, and an adversary here pays none. It also
/// sits on top of the mod-`p` limb encoding, so it inherits that aliasing upstream.
///
/// This is the single worst arithmetic in the tree by attacker cost. It survives here because a
/// collision over-includes (both producer and verifier project identically, so an honest turn goes
/// UNSAT) rather than authorizing a forgery — availability, not theft. Migrating it is Stage 2/4 of
/// `docs/DESIGN-canonical-byte-felt-codec.md`; the replacement is `dregg_codec::Digest8`, never a
/// better one-felt fold, because no one-felt image of a 32-byte value is acceptable at a security
/// boundary (`2^15.45` birthday).
///
/// CLOSED (effect-vm-hash-truncation lane, 2026-05-28): the previous
/// `hash_to_bb` / `field_element_to_bb` projectors took ONLY the first 4 bytes
/// of each 32-byte hash/field element, so the EffectVM proof bound only 4
/// bytes of each value (P1-2 in AUDIT-turn-executor.md). Two effects differing
/// solely in bytes `[4..32]` projected to the *identical* BabyBear and thus to
/// the identical `compute_effects_hash` / `PI[EFFECTS_HASH]` — interchangeable
/// proofs.
///
/// This fold makes the felt a function of ALL 32 bytes via a Horner evaluation
/// over the 8 four-byte limbs in the BabyBear field:
///
/// ```text
///   fold = Σ_{i=0}^{7} limb_i · MIX^i   (mod p)
/// ```
///
/// where `limb_i` is the i-th little-endian 4-byte chunk and `MIX` is a fixed non-trivial field
/// element. Distinct invertible weights mean flipping a byte changes the output *by default*, and
/// two INDEPENDENT UNIFORM inputs collide with ~`1/p ≈ 2^-31` — which is strictly better than the
/// previous *guaranteed* collision whenever the low 4 bytes matched, and is still not a binding
/// property. Linearity means an adversary never draws from that distribution: they solve.
///
/// Both the executor projector (`effect_vm_bridge.rs`) and the SDK projector
/// (`cipherclerk.rs`) call THIS function, so their per-effect felts agree
/// byte-for-byte by construction. The full-strength 256-bit binding for the
/// EmitEvent/Custom families is carried by their 8-limb fields; this fold is
/// the single-felt closure for the remaining identity/hash params, which the
/// AIR pins into a param column and `compute_effects_hash` absorbs.
#[inline]
pub fn fold_bytes32_to_bb(b: &[u8; 32]) -> BabyBear {
    // Fixed non-trivial mixing constant (a 31-bit prime, < p). Chosen to be
    // far from 0/1 so the Horner weights MIX^i are well-distributed.
    const MIX: u32 = 0x4FD3_9C8B % crate::field::BABYBEAR_P;
    let mix = BabyBear::new(MIX);
    let limbs = bytes32_to_8_limbs(b);
    let mut acc = BabyBear::ZERO;
    // Horner: acc = ((..(limb7)*mix + limb6)*mix + ...)*mix + limb0
    for i in (0..8).rev() {
        acc = acc * mix + limbs[i];
    }
    acc
}

/// Canonical 32-byte encoding of an `Effect::Refusal` reason: the
/// `offered_action_commitment` with the reason discriminant XOR'd into its
/// low 4 bytes (little-endian). Projected into 8 limbs by both the executor
/// and SDK projectors, this binds the FULL 32-byte commitment plus the
/// discriminant across all 8 limbs (the prior single-felt
/// `discriminant + fold_bytes32_to_bb(commitment)` form bound only ~31 bits). ⚠ The "~256-bit
/// strength" this doc used to claim holds only because the input is a Poseidon2/BLAKE3 IMAGE, not
/// because of the encoder: the 8-limb split is mod-`p` aliasable in `O(1)` for CHOSEN bytes. The
/// strength is the hash's, borrowed.
///
/// Both `turn::executor::effect_vm_bridge` and `sdk::cipherclerk` call this so
/// their `[BabyBear; 8]` encodings agree byte-for-byte (protocol-tests
/// differential invariant).
#[inline]
pub fn refusal_reason_bytes(commitment: &[u8; 32], discriminant: u32) -> [u8; 32] {
    let mut out = *commitment;
    let low = u32::from_le_bytes([out[0], out[1], out[2], out[3]]) ^ discriminant;
    out[0..4].copy_from_slice(&low.to_le_bytes());
    out
}

/// Decompose a u64 into 4 BabyBear limbs (16 bits each, little-endian).
/// Returns `[lo16, mid_lo16, mid_hi16, hi16]` so the limbs sum back to
/// the original via `Σ limbs[i] * 2^(16*i)`. Used to project full-u64
/// effect values into the AIR PI without 30-bit truncation
/// (CAVEAT-LAYER-COVERAGE.md §6.5).
#[inline]
pub fn u64_to_4_limbs_16(value: u64) -> [BabyBear; 4] {
    [
        BabyBear::new((value & 0xFFFF) as u32),
        BabyBear::new(((value >> 16) & 0xFFFF) as u32),
        BabyBear::new(((value >> 32) & 0xFFFF) as u32),
        BabyBear::new(((value >> 48) & 0xFFFF) as u32),
    ]
}

/// Inverse of [`u64_to_4_limbs_16`]: reconstruct a u64 from 4 BabyBear
/// limbs of 16 bits each. Returns `None` if any limb exceeds 2^16
/// (rejects out-of-range limbs — adversarial-test entry point).
#[inline]
pub fn u64_from_4_limbs_16(limbs: &[BabyBear; 4]) -> Option<u64> {
    let mut acc: u64 = 0;
    for (i, l) in limbs.iter().enumerate() {
        let v = l.0 as u64;
        if v >= (1u64 << 16) {
            return None;
        }
        acc |= v << (16 * i);
    }
    Some(acc)
}

/// Stage 2 (sealing honesty): bit-decompose `reserved = sealed_mask | (mode << 8)`
/// into 8 boolean mask bits + 1 boolean mode bit, and write them into the
/// row's reserved-bit aux slots. The AIR's per-row unconditional decomposition
/// constraint verifies the witness against `state_before.RESERVED`.
pub(crate) fn fill_reserved_bits(row: &mut [BabyBear], sealed_mask: u32, mode_flag: u32) {
    row[AUX_BASE + aux_off::RESERVED_BIT_0] = BabyBear::new(sealed_mask & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_1] = BabyBear::new((sealed_mask >> 1) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_2] = BabyBear::new((sealed_mask >> 2) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_3] = BabyBear::new((sealed_mask >> 3) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_4] = BabyBear::new((sealed_mask >> 4) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_5] = BabyBear::new((sealed_mask >> 5) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_6] = BabyBear::new((sealed_mask >> 6) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_7] = BabyBear::new((sealed_mask >> 7) & 1);
    row[AUX_BASE + aux_off::RESERVED_MODE] = BabyBear::new(mode_flag & 1);
}

/// W9-RANGECHECK: bit-decompose the *new* (state_after) balance limbs into
/// the `NEW_BAL_LO_BIT_BASE` / `NEW_BAL_HI_BIT_BASE` aux columns so the AIR's
/// per-row range / underflow constraint (booleanity + recomposition) is
/// satisfiable for honest traces.
///
/// `new_balance` is the post-effect cell balance. We split it the same way
/// `split_u64` does (lo = low 30 bits, hi = balance >> 30) and write 30
/// boolean bits per limb.
///
/// ⚑ **THESE COLUMNS ARE DELETED BEFORE THEY ARE PROVED, AND THE UNDERFLOW CLAIM THAT USED TO
/// BE HERE WAS FALSE.** This said the recomposition "pins each limb into `[0, 2^30)` and —
/// because a wrapped (underflowed) debit lands ≥ 2^30 — rejects modular-subtraction underflow
/// in-circuit", and that "a malicious prover that writes a wrapped limb cannot produce a
/// consistent 30-bit decomposition".
///
/// Both sentences are wrong. `p = 2013265921 < 2^31`, so an underflow of magnitude `k` lands at
/// `p - k`, which is BELOW `2^30` for every `k > 939524097` — such a value has a perfectly
/// consistent 30-bit decomposition and the constraint accepts it
/// (`Dregg2.Circuit.RangeFieldContainment.underflow_admitted_at_30_iff`, both directions,
/// `#assert_axioms`-clean).
///
/// It is moot on the wire regardless: the columns this writes (absolute 126..156 and 156..186)
/// fall inside the E1 kill-set run `(101, 186)` that every wide-registry member deletes
/// (`e1_compact_generated::E1_COMPACT_TABLE`), and `trace_rotated::compact_e1_columns` drops
/// them from the producer's rows. Nothing deployed evaluates them. The real over-debit refusal
/// is the availability weld's 15-bit borrow chain plus its no-final-borrow gate — see the note
/// on `columns::BAL_LIMB_BITS`.
///
/// This function survives because the v1-face row shape is still built before compaction, not
/// because the constraint it feeds carries any weight.
pub(crate) fn fill_balance_limb_bits(row: &mut [BabyBear], new_balance: u64) {
    let lo = (new_balance & 0x3FFF_FFFF) as u32; // low 30 bits
    let hi = new_balance >> 30; // remaining bits
    debug_assert!(
        hi < (1u64 << super::BAL_LIMB_BITS),
        "balance_hi {} exceeds 2^{} — out of the in-circuit range proof",
        hi,
        super::BAL_LIMB_BITS
    );
    for i in 0..super::BAL_LIMB_BITS {
        row[AUX_BASE + aux_off::NEW_BAL_LO_BIT_BASE + i] = BabyBear::new((lo >> i) & 1);
        row[AUX_BASE + aux_off::NEW_BAL_HI_BIT_BASE + i] = BabyBear::new(((hi >> i) & 1) as u32);
    }
}

/// The ordered felt preimage of the effects hash — one domain tag per effect
/// followed by that effect's bound parameters.
///
/// Split out of `compute_effects_hash` so the NARROW legacy squeeze and the wide
/// [`compute_effects_hash_4`] squeeze absorb the **same** preimage through the
/// same sponge, rather than the wide form re-hashing the narrow form's output
/// (`finalSqueezeOnly_still_conflates` — the laundering shape this repair
/// removed; see `docs/WOUND-felt-width-boundaries-2026-07-19.md` #30).
fn effects_hash_inputs(effects: &[Effect]) -> Vec<BabyBear> {
    let mut hasher_inputs = Vec::new();
    for effect in effects {
        match effect {
            Effect::NoOp => {
                hasher_inputs.push(BabyBear::ZERO);
            }
            Effect::Transfer { amount, direction } => {
                hasher_inputs.push(BabyBear::ONE);
                let (lo, hi) = split_u64(*amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(BabyBear::new(*direction));
            }
            Effect::SetField { field_idx, value } => {
                hasher_inputs.push(BabyBear::new(2));
                hasher_inputs.push(BabyBear::new(*field_idx));
                hasher_inputs.push(*value);
            }
            Effect::GrainTurn { values, fee } => {
                // Tag 6 = `sel::GRAIN_TURN`; the five lane-0 values, then the fee limbs.
                hasher_inputs.push(BabyBear::new(6));
                hasher_inputs.extend_from_slice(values);
                let (lo, hi) = split_u64(*fee);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::GrantCapability { cap_entry, phase_b } => {
                hasher_inputs.push(BabyBear::new(3));
                // 32-byte widening: absorb all 8 limbs (~256-bit binding).
                hasher_inputs.extend_from_slice(cap_entry);
                // Phase B2: a witnessed granter-side delegation row absorbs its
                // direction felt + the held slot_hash, so the public encoding
                // distinguishes the delegation row from a recipient install and
                // commits to WHICH held slot the membership-open authenticates.
                // Legacy (None) rows absorb nothing extra — byte-identical to
                // the pre-B2 encoding.
                if let Some(w) = phase_b {
                    hasher_inputs.push(BabyBear::ONE);
                    hasher_inputs.push(w.held.slot_hash);
                }
            }
            Effect::RevokeCapability { slot_hash, .. } => {
                hasher_inputs.push(BabyBear::new(24));
                hasher_inputs.extend_from_slice(slot_hash);
            }
            Effect::EmitEvent {
                topic_hash,
                payload_hash,
            } => {
                hasher_inputs.push(BabyBear::new(25));
                hasher_inputs.extend_from_slice(topic_hash);
                hasher_inputs.extend_from_slice(payload_hash);
            }
            Effect::SetPermissions { permissions_hash } => {
                hasher_inputs.push(BabyBear::new(26));
                hasher_inputs.extend_from_slice(permissions_hash);
            }
            Effect::SetVerificationKey { vk_hash } => {
                hasher_inputs.push(BabyBear::new(27));
                hasher_inputs.extend_from_slice(vk_hash);
            }

            Effect::RefreshDelegation {
                child_hash,
                snapshot_value,
            } => {
                hasher_inputs.push(BabyBear::new(29));
                // 32-byte widening: absorb all 8 limbs of the refreshed child
                // key AND all 8 of the new snapshot commitment, so the public
                // encoding binds WHICH delegation was re-armed and to WHAT value
                // (no reflexive ambiguity — a forged snapshot/child changes the hash).
                hasher_inputs.extend_from_slice(child_hash);
                hasher_inputs.extend_from_slice(snapshot_value);
            }
            Effect::IncrementNonce => {
                hasher_inputs.push(BabyBear::new(53));
            }
            Effect::RevokeDelegation { child_hash } => {
                hasher_inputs.push(BabyBear::new(30));
                hasher_inputs.extend_from_slice(child_hash);
            }
            Effect::CreateCell { create_hash } => {
                hasher_inputs.push(BabyBear::new(31));
                hasher_inputs.extend_from_slice(create_hash);
            }
            Effect::SpawnWithDelegation { spawn_hash } => {
                hasher_inputs.push(BabyBear::new(32));
                hasher_inputs.extend_from_slice(spawn_hash);
            }

            Effect::ExerciseViaCapability { exercise_hash } => {
                hasher_inputs.push(BabyBear::new(34));
                hasher_inputs.extend_from_slice(exercise_hash);
            }
            Effect::Introduce { intro_hash } => {
                hasher_inputs.push(BabyBear::new(35));
                hasher_inputs.extend_from_slice(intro_hash);
            }
            Effect::PipelinedSend { send_hash } => {
                hasher_inputs.push(BabyBear::new(36));
                hasher_inputs.extend_from_slice(send_hash);
            }

            Effect::BridgeMint {
                value_lo,
                mint_hash,
                value_full,
            } => {
                hasher_inputs.push(BabyBear::new(40));
                hasher_inputs.push(*value_lo);
                hasher_inputs.push(*mint_hash);
                let limbs = u64_to_4_limbs_16(*value_full);
                hasher_inputs.extend_from_slice(&limbs);
            }

            Effect::Mint {
                value_lo,
                mint_hash,
                value_full,
            } => {
                // SUPPLY-MODEL.md Stage 2b: the dedicated supply-mint binds under
                // its OWN domain tag (`sel::MINT = 14`), distinct from BridgeMint's
                // 40, so the two mints commit to disjoint effects-hash classes — a
                // supply-mint can never collide with / be replayed as a bridge-mint.
                hasher_inputs.push(BabyBear::new(14));
                hasher_inputs.push(*value_lo);
                hasher_inputs.push(*mint_hash);
                let limbs = u64_to_4_limbs_16(*value_full);
                hasher_inputs.extend_from_slice(&limbs);
            }

            Effect::NoteSpend { nullifier, value } => {
                hasher_inputs.push(BabyBear::new(4));
                hasher_inputs.push(*nullifier);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::NoteCreate { commitment, value } => {
                hasher_inputs.push(BabyBear::new(5));
                hasher_inputs.push(*commitment);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }

            Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } => {
                hasher_inputs.push(BabyBear::new(8));
                hasher_inputs.extend_from_slice(program_vk_hash);
                hasher_inputs.extend_from_slice(proof_commitment);
            }

            Effect::MakeSovereign => {
                hasher_inputs.push(BabyBear::new(12));
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                child_vk_derived,
            } => {
                hasher_inputs.push(BabyBear::new(13));
                hasher_inputs.push(*factory_vk);
                hasher_inputs.push(*child_vk_derived);
            }

            // ---- Near-miss aliasing closure (#100 follow-up) ----
            // Domain-tag bytes are reserved in the selector index space
            // (46, 47, 48 — matching `sel::BURN`, `sel::CELL_DESTROY`,
            // `sel::ATTENUATE_CAPABILITY`).
            Effect::Burn {
                target_hash,
                amount_lo,
                amount_full,
            } => {
                hasher_inputs.push(BabyBear::new(46));
                // 32-byte widening (felt-width #25): absorb all 8 limbs of the
                // burn target, the shape `CellDestroy` twenty lines below already
                // used. The prior single `push` bound ~31 bits of the target cell.
                hasher_inputs.extend_from_slice(target_hash);
                hasher_inputs.push(*amount_lo);
                // Bind the full u64 via 4×16-bit limbs (mirrors
                // BridgeMint / BridgeLock / CreateEscrow) so the proof
                // commits to the entire amount, not just the low 30 bits.
                let limbs = u64_to_4_limbs_16(*amount_full);
                hasher_inputs.extend_from_slice(&limbs);
            }
            Effect::CellDestroy {
                target_hash,
                death_certificate_hash,
            } => {
                hasher_inputs.push(BabyBear::new(47));
                hasher_inputs.extend_from_slice(target_hash);
                hasher_inputs.extend_from_slice(death_certificate_hash);
            }
            Effect::AttenuateCapability {
                cap_slot_hash,
                narrower_commitment,
                // Phase-B witness is NOT part of the public effects_hash binding;
                // the two 8-limb commitments are the canonical commitment.
                phase_b: _,
            } => {
                hasher_inputs.push(BabyBear::new(48));
                hasher_inputs.extend_from_slice(cap_slot_hash);
                hasher_inputs.extend_from_slice(narrower_commitment);
            }
            // ---- AIR-impl lane #119: CellSeal / CellUnseal / ReceiptArchive / Refusal ----
            // Domain tags 49–52 match `sel::CELL_SEAL` through `sel::REFUSAL`.
            Effect::CellSeal {
                target,
                reason_hash,
            } => {
                hasher_inputs.push(BabyBear::new(49));
                hasher_inputs.extend_from_slice(target);
                hasher_inputs.extend_from_slice(reason_hash);
            }
            Effect::CellUnseal { target } => {
                hasher_inputs.push(BabyBear::new(50));
                hasher_inputs.extend_from_slice(target);
            }
            Effect::ReceiptArchive {
                target,
                archive_end_height,
                terminal_receipt_hash,
            } => {
                hasher_inputs.push(BabyBear::new(51));
                hasher_inputs.extend_from_slice(target);
                // archive_end_height is a scalar height, not a 32-byte hash.
                hasher_inputs.push(*archive_end_height);
                hasher_inputs.extend_from_slice(terminal_receipt_hash);
            }
            Effect::Refusal {
                target,
                reason_hash,
            } => {
                hasher_inputs.push(BabyBear::new(52));
                hasher_inputs.extend_from_slice(target);
                hasher_inputs.extend_from_slice(reason_hash);
            }
        }
    }
    hasher_inputs
}

/// Compute the NARROW legacy effects hash for a sequence of effects.
/// Returns (lo, hi) BabyBear elements.
///
/// ⚠ **This is a ~31-bit digest** — `hash_many` squeezes ONE rate felt, and the
/// "hi" element is `hash_2_to_1(h, 0xEFFEC7)`, a function of that same felt, so
/// the pair's image has at most `p ≈ 2^31` points. Its collision resistance is
/// ~2^15.5 (birthday), NOT the width the two felts suggest. Use
/// [`compute_effects_hash_4`] at any boundary that binds; this form is kept for
/// the legacy `PI[EFFECTS_HASH_LO]` alias and for callers that only need the
/// historical felt. `sdk::full_turn_proof::effect_action_binding` still binds
/// position 0 alone — the residual named in
/// `docs/WOUND-felt-width-boundaries-2026-07-19.md` #31.
pub fn compute_effects_hash(effects: &[Effect]) -> (BabyBear, BabyBear) {
    let h = hash_many(&effects_hash_inputs(effects));
    // Split into two elements for wider coverage (legacy 2-felt form).
    let h2 = hash_2_to_1(h, BabyBear::new(0xEFFEC7));
    (h, h2)
}

/// The 4-felt effects hash carried at `PI[EFFECTS_HASH_BASE..+4]` — FOUR GENUINE
/// SPONGE SQUEEZES over the effect preimage.
///
/// Each lane is a rate-position squeeze of the Poseidon2 sponge that absorbed
/// [`effects_hash_inputs`], so every lane depends on the ENTIRE effect list and
/// the four together give ~124-bit collision resistance — matching the FRI floor
/// and the `Faithful8` state commitment beside them in the same PI vector.
///
/// # What this replaced, and why the old form's claimed width was FALSE
///
/// Until the felt-width #30 repair this was
/// `[h, hash_4_to_1([h,1,0,0]), hash_4_to_1([h,2,0,0]), hash_4_to_1([h,3,0,0])]`
/// with `h = compute_effects_hash(effects).0` — a single ~31-bit felt. All four
/// lanes were FUNCTIONS OF THAT ONE FELT, so the tuple's image had at most
/// `p ≈ 2^31` points and two effect lists agreeing on `h` produced a BYTE-IDENTICAL
/// 4-felt PI. The doc-comment claimed "~124-bit collision resistance"; the true
/// figure was ~2^15.5 birthday. That is exactly `finalSqueezeOnly_still_conflates`
/// (`metatheory/Dregg2/Cell/InterfaceIdWidth.lean`) with the sign flipped —
/// widening the FINAL SQUEEZE of a one-felt chain launders nothing, and here the
/// chain's own output *was* the one felt. Every "32-byte widening: absorb all 8
/// limbs (~256-bit binding)" arm inside `effects_hash_inputs` was therefore
/// cosmetic AT THIS BOUNDARY until this repair; they are load-bearing now.
///
/// `hash_many_8`'s own contract states the law this obeys: it "must not be bolted
/// only onto the final squeeze of a one-felt chain" — so it absorbs the REAL
/// preimage, not `h`.
///
/// Position 0 is NO LONGER guaranteed to equal `compute_effects_hash(effects).0`
/// (`hash_many_8` squeezes the same absorb state, but the equality is explicitly
/// not part of that primitive's contract — do not rely on it).
pub fn compute_effects_hash_4(effects: &[Effect]) -> [BabyBear; 4] {
    let wide = hash_many_8(&effects_hash_inputs(effects));
    [wide[0], wide[1], wide[2], wide[3]]
}
