//! The honest static/dynamic boundary — what this toolkit CAN and CANNOT
//! certify from a constructed-but-not-submitted artifact alone.
//!
//! The `Dregg2.AssuranceCase` states five guarantees (A Authority, B
//! Conservation, C Integrity, D Freshness, E Unfoolability) over the kernel
//! and the running executor. Of those, only the parts decidable from the
//! ARTIFACT'S SHAPE are checkable here. The rest need live state, the
//! executor, or the proof — and claiming otherwise would launder vacuity.
//! This module is the machine-and-human-readable statement of that line.

/// What is **statically checkable** from the artifact alone (this crate).
pub const STATIC_CHECKABLE: &[(&str, &str)] = &[
    (
        "B (conservation) — move sum",
        "Per asset, the forest's Transfer / balance_change / note value MOVES \
         net to exactly zero. Decidable: it is arithmetic over the artifact's \
         own numbers.",
    ),
    (
        "A (non-amplification) — IN-FOREST edges",
        "A grant that exceeds a cap delegated to the granting cell EARLIER IN \
         THE SAME FOREST is a provable amplification. Decidable for the \
         in-artifact delegation chain.",
    ),
    (
        "well-formedness",
        "Authorization::Unchecked outside genesis, OneOf-carrying-Unchecked, \
         empty actions, no-op exercises. Pure structural shape.",
    ),
    (
        "ring balance (B specialization)",
        "A settlement ring's legs close a cycle and net every participant to \
         zero per asset. Decidable over the leg list.",
    ),
    (
        "escrow conservation (app: escrow-market)",
        "released + refunded == escrowed over the escrow cell's value slots — \
         the FLASHWELL AffineEq the executor enforces at settle, restated over \
         the forest's SetField writes. Exact when the forest writes the escrow, \
         else supply the prior-committed amount.",
    ),
    (
        "provenance chain (app: agent-provenance)",
        "The committed entry digests form exactly the honest blake3 hash chain \
         entry_i = blake3(prev ‖ claim_i) of the published claims (verify_chain, \
         byte-identical to the app). A tampered / reordered / dropped entry is \
         detectable from the artifact + claims.",
    ),
    (
        "bounty lifecycle (app: bounty-board)",
        "The STATE writes across the forest are a strictly-increasing walk of a \
         known ladder (OPEN→CLAIMED→SUBMITTED→PAID) — the StrictMonotonic caveat. \
         No re-entry (double-claim), no rewind (re-open). Decidable over the \
         ordered writes (+ optional prior committed state).",
    ),
    (
        "exposure bound (app: stripe-reserve)",
        "Σ provisional-exposure ≤ reserve — the `≤` twin of escrow's `==`. The \
         forest's Mint / BridgeMint RAISE and Burn RETIRE an exposure counter \
         (the `drawn` spent-provisional column check_conservation drops at its \
         `_ => {}`), and the sum must not exceed the disclosed reserve ceiling R \
         (the Trustline draw_within_line bound). Exact when the forest writes the \
         reserve slot, else supply the prior-committed reserve.",
    ),
];

/// What is **dynamic** — needs the live executor / state / proof, and is
/// therefore OUT OF SCOPE for this crate (route to `dregg-intent::
/// verified_settle` or submit-and-verify the receipt instead).
pub const DYNAMIC_ONLY: &[(&str, &str)] = &[
    (
        "A (non-amplification) — the HOLDING half",
        "Whether the signer actually HELD the capability it grants (the live \
         c-list lookup). A grant over a target not delegated in-forest is \
         NOT flagged here — holding is a live-state question.",
    ),
    (
        "B (conservation) — sufficiency / underflow",
        "Whether `from` actually HAS the value it moves. A conserving forest \
         can still be rejected for insufficient balance — a live-balance check.",
    ),
    (
        "WHO — credential / signature validity",
        "ed25519 signature verification, STARK auth-proof checks, bearer-cap \
         and caveat-chain (HMAC) discharge against the live ShadowHostCtx \
         (block_height, frozen set, stored_head, budget, intro_lifetime). \
         These are §8 crypto carriers, not artifact shape.",
    ),
    (
        "C (integrity) — the whole-state commitment",
        "Whether the receipt binds the WHOLE post-state (Poseidon2 state \
         commitment). Produced by the executor; verified against the proof. \
         No artifact-only check exists.",
    ),
    (
        "D (freshness) — nullifier / replay / revocation",
        "Whether a spent note's nullifier was fresh, whether a stored cap \
         outlived its grantor's revocation epoch. Needs the live nullifier \
         set and the grantor's current delegation_epoch.",
    ),
    (
        "E (unfoolability) — the aggregate proof",
        "The recursive history fold a light client verifies. This is the \
         proof, not the turn — entirely downstream of submission.",
    ),
    (
        "BridgeMint cross-federation value",
        "A bridged note's value conservation is a portable-proof property \
         across federations, not a within-forest sum — not netted by \
         check_conservation.",
    ),
    (
        "exposure bound — whether the reserve is FUNDED",
        "The `≤` check (check_exposure_bound) compares Σ provisional-exposure \
         against the reserve CEILING it resolves from a slot (or prior_reserve). \
         Whether that reserve is actually FUNDED — hard collateral really posted \
         on the live cell backing the ceiling — is a live-state question, exactly \
         as a BridgeMint's claimed value is trusted from its portable proof and \
         not re-derived here. A within-ceiling turn can still be rejected if the \
         reserve fund is not really there.",
    ),
    (
        "app checks — the LIVE prior-cell state",
        "The app-level checks (escrow conservation, bounty lifecycle, \
         provenance chain) decide the invariant over the forest's INTENDED \
         writes. When the invariant spans turns (a settle that conserves the \
         escrow a prior turn bound; a lifecycle advance from the committed \
         state; a provenance append onto an existing chain), the prior value \
         lives on the live cell. The checks accept it as an explicit argument \
         (prior_escrowed / prior_state / prior_committed) — pass the committed \
         state to close the cross-turn relation; with neither an in-forest \
         write nor a prior, the check reports the unresolved slot rather than \
         passing vacuously.",
    ),
];

/// Render the boundary as a human-readable report (used by the CLI's
/// `--boundary` flag and embeddable in SDK explanations).
pub fn report() -> String {
    let mut s = String::new();
    s.push_str("=== STATIC (checked by dregg-userspace-verify, from the artifact alone) ===\n");
    for (name, desc) in STATIC_CHECKABLE {
        s.push_str(&format!("  [✓] {name}\n      {desc}\n"));
    }
    s.push_str("\n=== DYNAMIC (NOT checkable here — needs executor / live state / proof) ===\n");
    for (name, desc) in DYNAMIC_ONLY {
        s.push_str(&format!("  [·] {name}\n      {desc}\n"));
    }
    s.push_str(
        "\nThis toolkit is the cheap pre-flight (necessary, not sufficient). A Pass means \
         the artifact is well-shaped and self-conserving; it does NOT mean the executor \
         will accept it. For the dynamic half, route through \
         dregg-intent::verified_settle or submit and verify the receipt.\n",
    );
    s
}
