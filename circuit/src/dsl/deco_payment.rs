//! `dregg-circuit::dsl::deco_payment` — the FELT-DOMAIN Stripe/DECO payment identity.
//!
//! The DECO carrier's anti-vacuity keystone (`docs/deos/DECO-CARRIER-PLAN.md` §1,
//! Step 1). The deployed `stripeMint`/`decoMint` row publishes a felt-domain
//! `payment_hash` PI, and the recursion DECO leaf
//! (`circuit-prove::deco_leaf_adapter`) recomputes it IN-AIR from its PI-pinned
//! fact columns — so the two meet in ONE felt domain. This is the direct twin of
//! [`crate::dsl::note_spending::note_spend_mint_hash_felt`] (the bridge carrier).
//!
//! ## ⚑ THE ANTI-VACUITY LAW — felt-domain, NEVER byte-domain BLAKE3
//!
//! The anchor MUST be [`deco_payment_hash_felt`] — a Poseidon2 `hash_fact` chain
//! over the PaymentFacts felts, recomputable in-AIR. It must NEVER be the
//! executor's byte-domain BLAKE3 `payment_nullifier`
//! (`bridge/src/stripe_mirror.rs::payment_nullifier`), which "a circuit could not
//! recompute" — the exact mistake `BridgeBackingAttack`/`DecoBackingAttack` catch.
//! The BLAKE3 nullifier stays the executor's consume-once double-mint key
//! (`note_nullifiers`); the felt `payment_hash` is the light-client-witnessable
//! binding.
//!
//! ## The trust factoring (Option B, per the plan)
//!
//! The in-AIR leaf verifies only the Poseidon2 commitment binding
//! `PaymentFacts → payment_hash` (DecoRelation gates 3/4/5, `Deco.lean`). The
//! ed25519 server-key signature (gate 1), the HMAC-SHA256 transcript MAC (gate 2),
//! and the raw TLS/JSON parse stay OFF-AIR, executor-verified, carried as the named
//! §8 carriers — exactly what `Deco.lean::deco_binds_payment` already proves.

use crate::field::BabyBear;
use crate::poseidon2::{hash_fact, hash_many};

/// **THE FELT-DOMAIN PAYMENT IDENTITY** — the in-circuit-recomputable Stripe/DECO
/// `payment_hash`. The ONE canonical definition the executor projector, the deployed
/// descriptor producer, and the recursion DECO leaf all share (the twin of
/// [`crate::dsl::note_spending::note_spend_mint_hash_felt`]).
///
/// `hash_fact(hash_fact(amountCents, [currency, recipient]), [paymentIntentId])`
///
/// over the felt-decomposed `PaymentFacts{amountCents, currency, recipient,
/// paymentIntentId}` (`metatheory/Dregg2/Crypto/Deco.lean::PaymentFacts`). Binds the
/// whole payment identity: how much, in which currency, to which dregg cell, under
/// which payment-intent id (the consume-once replay nonce). The DECO leaf recomputes
/// this IN-AIR from its PI-pinned fact columns and exposes it at its claim lane; the
/// deployed row publishes the SAME felt at its `payment_hash` PI slot — so a forged
/// payment identity no verified DECO commitment backs is a `connect` conflict, UNSAT.
pub fn deco_payment_hash_felt(
    amount_cents: BabyBear,
    currency: BabyBear,
    recipient: BabyBear,
    payment_intent: BabyBear,
) -> BabyBear {
    let m1 = hash_fact(amount_cents, &[currency, recipient]);
    hash_fact(m1, &[payment_intent])
}

/// The high bit of the single-felt amount limb. Stripe cents fit comfortably under
/// `2^30` (the `$1,000,000.00` governance ceiling = `100_000_000` cents `< 2^30 ≈
/// 1.07e9`); the mask makes the felt encoding total, matching the `value_lo` limb
/// convention of the bridge carrier (`note_spending::bridge_mint_hash_felt`).
const AMOUNT_LIMB_BITS: u32 = 30;

/// A canonical Poseidon2 felt of a variable-length UTF-8 string (the currency code
/// or the payment-intent id): the sponge `hash_many` over the string's bytes as
/// felts. Collision-resistant under `Poseidon2SpongeCR` — the carrier that makes the
/// fold's paymentIntentId linkage bind a light-client-visible key.
pub fn felt_of_str(s: &str) -> BabyBear {
    let felts: Vec<BabyBear> = s.bytes().map(|b| BabyBear::new(b as u32)).collect();
    hash_many(&felts)
}

/// [`deco_payment_hash_felt`] from the RAW Stripe attestation material — the
/// executor/SDK entry point (`bridge/src/stripe_mirror.rs` holds a `String`
/// currency / payment-intent id and a 32-byte `recipient` CellId, not felts). The
/// byte→felt encoding here is the DECO twin of
/// [`crate::dsl::note_spending::bridge_mint_hash_felt`]:
///
///   * `amount_cents`: the low-`2^30` limb (total for any valid Stripe amount);
///   * `currency` / `payment_intent_id`: the canonical string felt [`felt_of_str`];
///   * `recipient`: the 32-byte CellId compressed via `hash_many(encode_hash(..))`
///     (the `bytes_to_babybear` convention shared with the bridge recipient/root).
///
/// So the identity is over the SAME felts the DECO leaf recomputes in-AIR — the
/// byte↔felt tie is this projection, not a laundered re-hash.
pub fn stripe_payment_hash_felt(
    amount_cents: u64,
    currency: &str,
    recipient: &[u8; 32],
    payment_intent_id: &str,
) -> BabyBear {
    let amount_lo = BabyBear::new((amount_cents & ((1u64 << AMOUNT_LIMB_BITS) - 1)) as u32);
    deco_payment_hash_felt(
        amount_lo,
        felt_of_str(currency),
        hash_many(&BabyBear::encode_hash(recipient)),
        felt_of_str(payment_intent_id),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The felt identity is a stable two-level `hash_fact` chain (the note-spend
    /// mint-hash shape) — the composition the leaf recomputes lane-for-lane.
    #[test]
    fn payment_hash_is_the_two_level_chain() {
        let a = BabyBear::new(2500);
        let c = BabyBear::new(840);
        let r = BabyBear::new(0x1234);
        let pi = BabyBear::new(0x99);
        let m1 = hash_fact(a, &[c, r]);
        assert_eq!(deco_payment_hash_felt(a, c, r, pi), hash_fact(m1, &[pi]));
    }

    /// THE ANTI-DOUBLE-MINT LINKAGE (cheap): two payments differing ONLY in their
    /// payment-intent id carry DISTINCT identities — so a published `payment_hash`
    /// pins WHICH paymentIntentId was minted against (the fold half of the
    /// double-mint guard; the executor's `note_nullifiers` set-uniqueness ranges
    /// over that same key).
    #[test]
    fn identity_binds_the_payment_intent() {
        let a = BabyBear::new(2500);
        let c = BabyBear::new(840);
        let r = BabyBear::new(0x1234);
        let h1 = deco_payment_hash_felt(a, c, r, BabyBear::new(1));
        let h2 = deco_payment_hash_felt(a, c, r, BabyBear::new(2));
        assert_ne!(
            h1, h2,
            "distinct payment-intent ids ⇒ distinct payment identities"
        );
    }

    /// The byte-domain projection agrees with the felt-domain identity over the same
    /// decomposed felts — the byte↔felt tie is the projection, not a re-hash.
    #[test]
    fn byte_projection_matches_felt_identity() {
        let recipient = [0xCDu8; 32];
        let byte = stripe_payment_hash_felt(2500, "usd", &recipient, "pi_abc123");
        let felt = deco_payment_hash_felt(
            BabyBear::new(2500),
            felt_of_str("usd"),
            hash_many(&BabyBear::encode_hash(&recipient)),
            felt_of_str("pi_abc123"),
        );
        assert_eq!(byte, felt);
    }

    /// Distinct payment-intent id STRINGS map to distinct felts (the `felt_of_str`
    /// CR at the identity level) — the executor's replay nonce and the fold's
    /// linkage key move together.
    #[test]
    fn distinct_intent_strings_distinct_felts() {
        assert_ne!(felt_of_str("pi_001"), felt_of_str("pi_002"));
    }
}
