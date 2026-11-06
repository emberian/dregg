//! # R3 — the whole-history STARK leg, wired to the Lean-proven verifier.
//!
//! R0–R2 (in [`crate`]) make a hosted session tamper-evident, renter-anchored, and
//! kernel-linked — but still TRUST the executor host that produced and committed the
//! turns. R3 removes that trust for a grain's WHOLE history: fold the session's
//! finalized turns into ONE constant-size recursive-STARK aggregate
//! ([`prove_turn_chain_recursive_without_host_gate`]), light-verify it against the
//! renter's OWN trust anchor ([`verify_whole_chain_proof_bytes`]), and let the
//! LEAN-PROVEN R3 verify core render the accept decision — a lying host cannot serve a
//! fabricated or truncated history under an honest-looking anchored head.
//!
//! ## The decision is the Lean-proven object, not this Rust
//!
//! The accept/reject is NOT decided here. Rust does the heavy lifting — the fold and
//! the succinct-aggregate verify — and marshals four facts onto a wire:
//!   1. the whole-chain STARK verifier's **verified-status** (did the aggregate verify
//!      **against the caller's anchor**), from [`verify_whole_chain_proof_bytes`];
//!   2. the **fingerprint recomputed from the presented root**
//!      ([`WholeChainProof::root_vk_fingerprint`]) — a producer CLAIM, never an anchor;
//!   3. the **caller's expected VK anchor**, held out of band; and
//!   4. the **aggregate's committed 8-felt head** (`final_root`, all
//!      [`SEG_ANCHOR_WIDTH`] lanes) vs the **R1-anchored 8-felt head** the caller supplies.
//!
//! Those go to `Dregg2.Grain.R3Verify.r3VerifyFFI` (the `@[export] dregg_grain_r3_verify`
//! entry, reached via [`dregg_lean_ffi::shadow_grain_r3_verify`]) — the extracted,
//! `#assert_axioms`-clean `r3VerifyCore`. Its `"1"` IS the R3-accept, and its soundness is
//! the PROVED `r3_unfoolable` (the whole history is execution-integrity-sound AND
//! complete, with the anchored head pinned to its genuine fold).
//!
//! ## The felt-width + self-anchoring repair (wound #22)
//!
//! `docs/WOUND-felt-width-boundaries-2026-07-19.md` #22 catalogued this seam as a HIGH
//! design wound with TWO independently fatal conjuncts, and this module is its close.
//! The pre-fix seam marshalled `proof.final_root[0].as_u32()` — **lane 0 of an 8-felt
//! anchor**, ~31 bits — and called the light verifier with `proof.root_vk_fingerprint()`,
//! **the fingerprint the artifact itself supplied**:
//!
//!   * **the WIDTH.** A lying host *is* the party that supplies `finalized`. It could grind
//!     its own turn sequence offline (~2^31 cheap state-commit computations, no proving
//!     until the hit) for a fabricated final anchor whose LANE 0 matched the renter's
//!     honest `anchored_head`, then fold ONCE — and R3 accepted the fabrication as the
//!     renter's history. Now all [`SEG_ANCHOR_WIDTH`] = 8 lanes bind (~124-bit). The wide
//!     value already existed on BOTH sides: the aggregate carries `final_root: [BabyBear;
//!     8]`, and the anchor is sourced from the leg's `wide_new_root8() -> [BabyBear; 8]`.
//!     Nothing was invented; the seam simply stopped projecting.
//!   * **the SELF-ANCHORING.** Verifying against the proof's own fingerprint establishes
//!     nothing about which VK the proof *should* carry — so the verified-status said "this
//!     supplied blob self-verifies", not "this is the renter's chain", which is exactly why
//!     the ~31-bit head equality was carrying the whole binding. This was not a grey area:
//!     [`WholeChainProof::root_vk_fingerprint`]'s own docstring says "A VERIFIER must NEVER
//!     take the anchor from the artifact it is verifying", and
//!     [`verify_whole_chain_proof_bytes`]'s says "`expected_vk` is the caller's OWN
//!     configured anchor — it is NEVER read from the envelope". The pre-fix seam violated a
//!     documented API contract. [`r3_verify`] now TAKES the anchor.
//!
//!     And the effect was sharper than "weakly bound": **tooth 1 was a TAUTOLOGY.** The
//!     verifier's VK pin is `if recursion_vk_fingerprint(root_proof) != *expected_vk
//!     { refuse }`, and [`WholeChainProof::root_vk_fingerprint`] is *defined* as
//!     `recursion_vk_fingerprint(&self.root.0)` over the same root the envelope carries —
//!     so passing it as `expected_vk` fed the check its own answer (`found == found`). The
//!     pin could not fail. The whole-chain verifier's first tooth was inert on this path,
//!     leaving the ~31-bit head equality as the sole binding.
//!
//! **Neither repair alone would have sufficed**, and that is machine-checked, not asserted:
//! `Dregg2.Grain.R3Verify.neither_half_alone_suffices` proves the head-widened-but-still-
//! self-anchored form still admits a foreign circuit's root, and the VK-pinned-but-still-
//! lane-0 form still admits the ~2^31 grind. Widening the felt alone would have been a
//! green that means nothing (the
//! `Dregg2.Cell.InterfaceIdWidth.finalSqueezeOnly_still_conflates` failure shape).
//!
//! ### Where the expected VK comes from
//!
//! NOT the proof, and NOT a governance constant. The fingerprint is a function of the root
//! circuit SHAPE, which varies with `num_turns` and the leaf trace heights (per
//! [`WholeChainProof::root_vk_fingerprint`]), so no single pinned scalar can cover the fold
//! shapes R3 sees — unlike `DREGG_APEX_RECURSION_VK`, which pins the ONE fixed apex-shrink
//! shape. The correct source at this layer is therefore the caller: an honest-setup party
//! extracts the anchor ONCE from a fold it produced ITSELF ([`r3_setup_anchor`]) and holds
//! it out of band, exactly as `dregg_lightclient` splits `fold_and_attest` (SETUP — mints
//! the anchor, legitimately self-anchoring) from `verify_history` (VERIFIER — takes a
//! configured anchor). [`r3_verify`] is a VERIFIER: it renders a renter's accept decision,
//! so it belongs on the `verify_history` side of that split. The pre-fix module doc cited
//! `fold_and_attest`'s self-anchoring as precedent — but that is precedent for MINTING an
//! anchor, not for verifying against one.
//!
//! ## Honest scope — REDUCED to `EngineSound`, not closed
//!
//! `r3_unfoolable` is a genuine *reduction plus head-binding*, not an unconditional
//! proof of unfoolability: it reduces the grain's [`crate::WHOLE_HISTORY_GAP`] to the
//! named `RecursiveAggregation.EngineSound` boundary (the FRI/recursion legs proved
//! *outside* Lean, plus the single-turn apex's still-open reconciliation). GIVEN that
//! soundness, R3 accepts only genuinely-executed, correctly-ordered, non-truncated
//! histories bound to THIS grain's head. So R3 here is the maximal real subset *above*
//! the STARK floor — the floor itself is the carried, honest hypothesis, not a claim
//! this rung discharges. **The width repair adds no floor:** the widened head equality is
//! exact 8-lane equality and the VK equality is exact 32-byte equality; the ~124-bit
//! strength of the 8-felt anchor is the already-carried Poseidon2 state-commit floor.

use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, RecursionVk, SEG_ANCHOR_WIDTH, TurnChainError, WholeChainProofBytes,
    prove_turn_chain_recursive_without_host_gate, verify_whole_chain_proof_bytes,
};
use dregg_circuit_prove::joint_turn_aggregation::verify_descriptor_participant;

/// The number of `u32` lanes a [`RecursionVk`] occupies on the Lean wire — its 32 bytes
/// repacked big-endian, four bytes per lane. A bijective repacking: the Lean core compares
/// the lanes, which is byte-equality of the fingerprints.
pub const R3_VK_LANES: usize = 8;

/// The number of decimal integers the R3 wire carries — the status, then FOUR eight-lane
/// values (presented VK ‖ expected VK ‖ aggregate head ‖ anchored head). Must equal
/// `Dregg2.Grain.R3Verify.r3WireLen`; a mismatch fails CLOSED at the Lean parse, never
/// silently narrow-accepts.
pub const R3_WIRE_LEN: usize = 1 + 2 * R3_VK_LANES + 2 * SEG_ANCHOR_WIDTH;

/// A [`RecursionVk`]'s 32 bytes as eight canonical `u32` lanes (big-endian per 4-byte
/// chunk) — the wire encoding the Lean `Vk8` model reads.
fn vk_lanes(vk: &RecursionVk) -> [u32; R3_VK_LANES] {
    core::array::from_fn(|i| {
        u32::from_be_bytes([
            vk.0[4 * i],
            vk.0[4 * i + 1],
            vk.0[4 * i + 2],
            vk.0[4 * i + 3],
        ])
    })
}

/// **What a renter learns from a passing [`r3_verify`]** — the whole history behind
/// `anchored_head` is unfoolable (execution-integrity-sound + complete + anchored),
/// under the named `EngineSound` STARK floor, with NO host trust in the accept
/// decision (it is the Lean-proven `r3VerifyCore`'s `"1"`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R3Verified {
    /// The number of finalized turns folded into the aggregate.
    pub num_turns: usize,
    /// The R1-anchored 8-felt head the caller pinned — the aggregate's committed head
    /// equals it in ALL [`SEG_ANCHOR_WIDTH`] lanes (the head-binding tooth at ~124 bits),
    /// so the sound history is about THIS grain's THIS head, not a swapped one.
    pub anchored_head: [u32; SEG_ANCHOR_WIDTH],
    /// The aggregate's committed 8-felt head (`final_root`) — equal to `anchored_head` in
    /// every lane on a pass.
    pub aggregate_head: [u32; SEG_ANCHOR_WIDTH],
    /// The caller's expected VK anchor, which the presented root's recomputed fingerprint
    /// matched. Echoed so a caller can log WHICH anchor rendered the accept.
    pub expected_vk: RecursionVk,
}

/// Why a grain's whole history did not R3-verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R3Error {
    /// The chain was empty — nothing to fold (the whole-chain fold needs ≥ 1 turn;
    /// the recursive aggregation needs ≥ 2 for a non-trivial tree).
    EmptyChain,
    /// The LEAN-PROVEN R3 verify core (`dregg_grain_r3_verify`) is not in the linked
    /// archive — the decision cannot be rendered by the verified object. Carries the
    /// FFI error. (Rebuild `dregg-lean-ffi` so the archive splices
    /// `Dregg2.Grain.R3Verify`.) R3 has NO Rust fallback for the accept decision by
    /// design: the decision is the Lean-proven one or it is not made.
    LeanCoreUnavailable(String),
    /// The honest-setup fold [`r3_setup_anchor`] runs could not be produced, so no anchor
    /// could be minted. Carries the fold error.
    SetupFoldFailed(String),
    /// The Lean-proven R3 decision REJECTED. One of three teeth bit:
    ///   * the whole-chain aggregate did not verify against the caller's anchor
    ///     (`aggregate_verified == false`: a forged/dropped/reordered history has no
    ///     satisfying leaf, or the root belongs to a different circuit);
    ///   * the fingerprint recomputed from the presented root is not the caller's anchor
    ///     (the anti-self-anchor tooth: a foreign circuit's root cannot be laundered
    ///     through by shipping its own fingerprint alongside it); or
    ///   * the aggregate's committed 8-felt head is not the anchored 8-felt head in some
    ///     lane (the anti-ghost tooth at full width: a valid whole-history proof cannot be
    ///     re-pointed at a foreign anchor, and matching ~31 bits of it is not enough).
    ///
    /// This is the Lean-proven verifier's fail-closed verdict.
    Rejected {
        /// Whether the whole-chain STARK aggregate verified against the caller's anchor.
        aggregate_verified: bool,
        /// The aggregate's committed 8-felt head (`final_root`); all-zero when the fold
        /// itself failed, so no head exists.
        aggregate_head: [u32; SEG_ANCHOR_WIDTH],
        /// The R1-anchored 8-felt head the caller supplied.
        anchored_head: [u32; SEG_ANCHOR_WIDTH],
        /// The fingerprint RECOMPUTED from the presented root — `None` when the fold
        /// itself failed (there is no root to fingerprint). A producer CLAIM, reported for
        /// diagnostics; never an anchor.
        presented_vk: Option<RecursionVk>,
        /// The caller's expected VK anchor.
        expected_vk: RecursionVk,
    },
    /// ⚑ **THE WIRE, NOT THE HISTORY.** The Lean-proven verifier could not READ the
    /// `R3_WIRE_LEN`-int wire this binary sent it (`Dregg2.Grain.R3Verify.parseWireE`
    /// returned a fault), so it never rendered a decision about anybody's chain. This is a
    /// disagreement between [`r3_wire`] in THIS binary and the parser in the LINKED Lean
    /// archive — a fault in how this binary was built, not in the grain being verified —
    /// and it is fail-CLOSED: while it stands, every R3 verification refuses.
    ///
    /// **It has its own variant because until 2026-08-07 it did NOT have one.**
    /// `r3VerifyFFI` rendered a parse failure as `"0"`, the same string the whole-history
    /// REFUSAL renders as, so exactly this condition arrived as [`R3Error::Rejected`] —
    /// a true refusal wearing a false diagnosis, with `aggregate_verified` /
    /// `aggregate_head` / `presented_vk` fields describing a decision that was never made.
    /// `Dregg2.Grain.R3Verify.r3VerifyWire_eq_reject_iff` and `r3VerifyWire_malformed_iff`
    /// are the two theorems that now make the codes distinguishable by value.
    WireMalformed {
        /// The parse STAGE the Lean side stopped at (`R3WireFault`) — which half of the
        /// grammar disagreed: a token that is not a decimal integer, or a token COUNT that
        /// is not `R3_WIRE_LEN` (which is what a stale caller's pre-repair three-int wire
        /// reports).
        stage: &'static str,
    },
}

/// The `&'static str` behind each Lean `R3WireFault.code` — the `<stage>` token of the
/// `"2 <stage>"` malformed code.
///
/// `None` for a code this table does not carry, which is a NAMING gap and not a decoding
/// one: the call site substitutes [`R3_WIRE_FAULT_UNNAMED`] and still REFUSES, because the
/// `"2"` tag alone already says the Lean side could not read the wire and losing the stage
/// must not lose that.
fn r3_wire_fault_name(code: &str) -> Option<&'static str> {
    match code {
        "0" => Some(
            "token — a whitespace-separated token on the R3 wire is not a decimal integer \
             (the Lean parse is strict `mapM`, so a bad token is never dropped)",
        ),
        "1" => Some(
            "arity — every token parsed and the count is not R3_WIRE_LEN (33); a stale \
             caller's pre-repair three-int wire lands here",
        ),
        _ => None,
    }
}

/// The stage a malformed-wire refusal carries when the Lean side named a fault THIS binary
/// has no name for — a newer `R3WireFault` against an older decoder. It says so, because
/// "unknown stage" and "no stage" are different facts about the two halves.
const R3_WIRE_FAULT_UNNAMED: &str = "unnamed stage — the linked Lean R3 verifier reported an R3WireFault code this binary's \
     decoder has no name for, so the two halves are of different vintages";

impl core::fmt::Display for R3Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            R3Error::EmptyChain => {
                write!(f, "grain(R3): empty finalized-turn chain — nothing to fold")
            }
            R3Error::LeanCoreUnavailable(e) => write!(
                f,
                "grain(R3): the Lean-proven R3 verify core is not linked (rebuild dregg-lean-ffi to splice Dregg2.Grain.R3Verify): {e}"
            ),
            R3Error::SetupFoldFailed(e) => write!(
                f,
                "grain(R3 setup): the honest-setup fold failed, so no trust anchor could be minted: {e}"
            ),
            R3Error::Rejected {
                aggregate_verified,
                aggregate_head,
                anchored_head,
                presented_vk,
                expected_vk,
            } => write!(
                f,
                "grain(R3): the Lean-proven verifier REJECTED (aggregate_verified={aggregate_verified}, aggregate_head={aggregate_head:?}, anchored_head={anchored_head:?}, presented_vk={}, expected_vk={}) — a fabricated/truncated history, a foreign circuit's root, or a foreign anchor",
                presented_vk
                    .as_ref()
                    .map(RecursionVk::to_hex)
                    .unwrap_or_else(|| "<no root: the fold failed>".to_string()),
                expected_vk.to_hex(),
            ),
            // ⚑ This message must NOT describe the grain. Nothing about the chain, the head
            // or the anchor is implicated: the verifier never ran. Saying "REJECTED" here is
            // precisely the false diagnosis this variant exists to stop giving.
            R3Error::WireMalformed { stage } => write!(
                f,
                "grain(R3): the Lean-proven R3 verifier REFUSED TO PARSE the wire this binary sent it, at stage: {stage}. It never ran, so this refusal says NOTHING about the grain's history, head or anchor — it says grain_verify::r3::r3_wire and Dregg2.Grain.R3Verify.parseWireE disagree about the 33-int wire in THIS binary. Fail-closed: every R3 verification refuses until they are reconciled. Usual cause: a linked libdregg_lean.a older or newer than this crate — rebuild dregg-lean-ffi so its splice picks up the current Dregg2.Grain.R3Verify"
            ),
        }
    }
}

impl std::error::Error for R3Error {}

/// The facts the fold produces for the Lean decision to read.
struct FoldFacts {
    /// Did the whole-chain STARK verifier accept the envelope AGAINST THE CALLER'S ANCHOR.
    verified: bool,
    /// The aggregate's committed 8-felt head (`final_root`), all lanes.
    aggregate_head: [u32; SEG_ANCHOR_WIDTH],
    /// The fingerprint RECOMPUTED from the presented root. `None` when the fold itself
    /// failed — there is then no root to fingerprint.
    presented_vk: Option<RecursionVk>,
}

/// The selector claim from each participant's descriptor. This is the prover's CLAIMED
/// selector (which descriptor AIR to re-prove per turn), NOT a host admission gate: we read
/// the selector, we do NOT abort on a rejected descriptor — a bad turn flows through as
/// `verified = false`. The load-bearing check is the in-circuit leaf re-proof surfaced as
/// the verified-status, exactly why the UNGATED prover is used.
fn claimed_selectors(finalized: &[FinalizedTurn]) -> Result<Vec<usize>, TurnChainError> {
    let mut selectors = Vec::with_capacity(finalized.len());
    for (i, t) in finalized.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    Ok(selectors)
}

/// The whole-chain fold + succinct-aggregate verify, producing the facts the Lean decision
/// reads. A fold or verify FAILURE is not an accept — it yields `verified = false`, which
/// the Lean core PROVABLY rejects (`Dregg2.Grain.R3Verify.r3_unverified_rejected`: a false
/// status rejects regardless of the VKs and heads), so the Lean-proven verifier stays the
/// SINGLE accept gate and the refusal rests on a theorem rather than a Rust convention.
///
/// `expected_vk` is the CALLER's out-of-band anchor and is what the light verifier runs
/// against. The proof's own `root_vk_fingerprint()` is recomputed and reported, but is
/// NEVER used as the anchor — see the module doc's wound-#22 section.
fn fold_and_status(finalized: &[FinalizedTurn], expected_vk: &RecursionVk) -> FoldFacts {
    let attempt = || -> Result<FoldFacts, TurnChainError> {
        let selectors = claimed_selectors(finalized)?;
        // Fold WITHOUT the host gate — a forged turn has no satisfying witness at the
        // in-circuit leaf wrap, so the fold fails and no verifying root exists.
        let proof = prove_turn_chain_recursive_without_host_gate(finalized, &selectors)?;
        let bytes = proof.to_bytes();
        // The fingerprint RECOMPUTED from the presented root — a producer CLAIM we surface
        // to the Lean decision for comparison against the caller's anchor. It is NOT the
        // anchor: `root_vk_fingerprint`'s docstring is explicit that a verifier must never
        // take the anchor from the artifact it is verifying.
        let presented_vk = proof.root_vk_fingerprint();
        // The verified-status: run the whole-chain STARK verifier over the byte envelope
        // against the CALLER'S anchor (the `verify_history` shape, not `fold_and_attest`'s
        // setup-side self-anchoring). This IS `verify agg.root` in the model.
        let verified = verify_whole_chain_proof_bytes(&bytes, expected_vk).is_ok();
        // The aggregate's committed head = the FULL 8-felt final state anchor (~124-bit),
        // not a lane-0 projection of it.
        let aggregate_head = core::array::from_fn(|i| proof.final_root[i].as_u32());
        Ok(FoldFacts {
            verified,
            aggregate_head,
            presented_vk: Some(presented_vk),
        })
    };
    attempt().unwrap_or(FoldFacts {
        verified: false,
        aggregate_head: [0; SEG_ANCHOR_WIDTH],
        presented_vk: None,
    })
}

/// Marshal the R3 facts onto the Lean wire: `R3_WIRE_LEN` space-separated decimal ints,
/// `"verified presentedVk[0..8] expectedVk[0..8] aggregateHead[0..8] anchoredHead[0..8]"`.
fn r3_wire(
    verified: bool,
    presented_vk: &[u32; R3_VK_LANES],
    expected_vk: &[u32; R3_VK_LANES],
    aggregate_head: &[u32; SEG_ANCHOR_WIDTH],
    anchored_head: &[u32; SEG_ANCHOR_WIDTH],
) -> String {
    let mut wire = String::with_capacity(R3_WIRE_LEN * 11);
    wire.push(if verified { '1' } else { '0' });
    for lane in presented_vk
        .iter()
        .chain(expected_vk.iter())
        .chain(aggregate_head.iter())
        .chain(anchored_head.iter())
    {
        wire.push(' ');
        wire.push_str(&lane.to_string());
    }
    wire
}

/// **SETUP ONLY — mint the R3 trust anchor from a fold YOU produced.**
///
/// An honest-setup party (the renter, or a party the renter trusts) runs this ONCE over a
/// finalized-turn chain it produced ITSELF, and holds the returned [`RecursionVk`] out of
/// band as the anchor it later passes to [`r3_verify`]. This is the `fold_and_attest` role
/// in `dregg_lightclient`'s split, and self-anchoring is CORRECT here: the point of the
/// operation is to extract a fingerprint from a locally-produced fold.
///
/// **Never call this on an artifact you are verifying.** Doing so reconstructs exactly the
/// wound-#22 self-anchoring the repair removed: the "anchor" would be the presented proof's
/// own claim, and the VK conjunct would be vacuous
/// (`Dregg2.Grain.R3Verify.selfAnchoredVk_vacuous` proves the decision is then literally
/// independent of which circuit the root belongs to).
///
/// Note the anchor is a function of the root circuit SHAPE, which varies with `num_turns`
/// and the leaf trace heights: one anchor pins one accepted fold shape. A verifier
/// accepting several shapes holds one anchor per shape.
/// **R3 for a holder of the aggregate only — VERIFY, never prove.** [`r3_verify`] takes the
/// finalized legs and re-runs the recursive fold inside the verifier, which hands a stranger the
/// prover's cost. This takes the producer's [`WholeChainProofBytes`] envelope (the
/// verify-sufficient subset, `WholeChainProof::to_bytes`), light-verifies it against the caller's
/// OWN `expected_vk` with [`verify_whole_chain_proof_bytes`], reads the aggregate's committed
/// 8-felt head off the decoded envelope, and puts the SAME 33-int wire [`r3_verify`] puts to the
/// extracted Lean `r3VerifyCore`. The decision is the Lean core's `"1"`; there is no Rust
/// fallback.
///
/// The presented-VK lanes are the fingerprint RECOMPUTED from the envelope's root proof (never
/// the envelope's claimed `vk_fingerprint_hex`). A blob that does not decode carries no head and
/// no root: it is sent as `verified = false` with a zero head and the expected VK in the
/// presented slot, which the Lean core refuses on the verified-status conjunct alone.
pub fn r3_verify_aggregate(
    aggregate: &[u8],
    anchored_head: &[u32; SEG_ANCHOR_WIDTH],
    expected_vk: &RecursionVk,
) -> Result<R3Verified, R3Error> {
    let decoded = WholeChainProofBytes::from_postcard(aggregate)
        .ok()
        .and_then(|env| {
            let presented = env.presented_vk_fingerprint().ok()?;
            Some((env, presented))
        });
    let (verified, aggregate_head, presented_vk, num_turns) = match &decoded {
        Some((env, presented)) => (
            verify_whole_chain_proof_bytes(aggregate, expected_vk).is_ok(),
            env.final_root,
            Some(*presented),
            env.num_turns as usize,
        ),
        None => (false, [0u32; SEG_ANCHOR_WIDTH], None, 0),
    };
    let expected_lanes = vk_lanes(expected_vk);
    let presented_lanes = presented_vk
        .as_ref()
        .map(vk_lanes)
        .unwrap_or(expected_lanes);
    let wire = r3_wire(
        verified,
        &presented_lanes,
        &expected_lanes,
        &aggregate_head,
        anchored_head,
    );
    let out =
        dregg_lean_ffi::shadow_grain_r3_verify(&wire).map_err(R3Error::LeanCoreUnavailable)?;
    let mut toks = out.split_whitespace();
    match toks.next() {
        Some("1") => Ok(R3Verified {
            num_turns,
            anchored_head: *anchored_head,
            aggregate_head,
            expected_vk: *expected_vk,
        }),
        Some("0") => Err(R3Error::Rejected {
            aggregate_verified: verified,
            aggregate_head,
            anchored_head: *anchored_head,
            presented_vk,
            expected_vk: *expected_vk,
        }),
        Some("2") => Err(R3Error::WireMalformed {
            stage: toks
                .next()
                .and_then(r3_wire_fault_name)
                .unwrap_or(R3_WIRE_FAULT_UNNAMED),
        }),
        _ => Err(R3Error::WireMalformed {
            stage: R3_WIRE_FAULT_UNNAMED,
        }),
    }
}

pub fn r3_setup_anchor(finalized: &[FinalizedTurn]) -> Result<RecursionVk, R3Error> {
    if finalized.is_empty() {
        return Err(R3Error::EmptyChain);
    }
    let selectors =
        claimed_selectors(finalized).map_err(|e| R3Error::SetupFoldFailed(e.to_string()))?;
    let proof = prove_turn_chain_recursive_without_host_gate(finalized, &selectors)
        .map_err(|e| R3Error::SetupFoldFailed(e.to_string()))?;
    Ok(proof.root_vk_fingerprint())
}

/// **R3 — verify a grain's WHOLE history is unfoolable, with the Lean-proven verifier
/// rendering the accept decision.**
///
/// Folds the grain's `finalized` turns into ONE recursive-STARK aggregate (ungated),
/// light-verifies it against `expected_vk`, and routes `(verified-status, presented
/// fingerprint, expected anchor, aggregate 8-felt head, anchored 8-felt head)` to the
/// extracted, `#assert_axioms`-clean Lean `r3VerifyCore` — whose `"1"` is the R3-accept,
/// PROVED sound (reduced to the named `EngineSound` STARK floor + the widened head
/// binding, see the module doc's honest scope).
///
/// `anchored_head` is the grain's R1-anchored head as the FULL 8-felt state anchor — the
/// leg's `wide_new_root8()`, not a lane-0 projection of it. On a pass the aggregate's
/// committed head equals it in every lane: the anti-ghost tooth binds the sound history to
/// THIS grain at ~124 bits rather than ~31.
///
/// `expected_vk` is the caller's OWN out-of-band trust anchor, minted by
/// [`r3_setup_anchor`] over a locally-produced fold. It is deliberately a PARAMETER: there
/// is no correct source for it inside this layer (see the module doc), and reading it off
/// the presented proof — what the pre-fix seam did — establishes nothing.
///
/// Errors: [`R3Error::Rejected`] when the Lean verifier fail-closed rejects (a
/// fabricated/truncated history, a foreign circuit's root, or a foreign anchor);
/// [`R3Error::LeanCoreUnavailable`] when the archive lacks the verified core (no Rust
/// fallback — the decision is the Lean-proven one or it is not made);
/// [`R3Error::EmptyChain`] on an empty chain.
pub fn r3_verify(
    finalized: &[FinalizedTurn],
    anchored_head: &[u32; SEG_ANCHOR_WIDTH],
    expected_vk: &RecursionVk,
) -> Result<R3Verified, R3Error> {
    if finalized.is_empty() {
        return Err(R3Error::EmptyChain);
    }

    // Rust does the heavy lifting: fold + succinct-aggregate verify against the CALLER'S
    // anchor → the facts.
    let facts = fold_and_status(finalized, expected_vk);

    // THE DECISION — the LEAN-PROVEN r3VerifyCore over the wire. "1" ⟹ accept. Rust never
    // decides accept; it marshals to the verified object. On a fold failure there is no
    // root to fingerprint, so the presented lanes echo the anchor and the refusal rests on
    // the proven `r3_unverified_rejected` (a false status rejects regardless).
    let expected_lanes = vk_lanes(expected_vk);
    let presented_lanes = facts
        .presented_vk
        .as_ref()
        .map(vk_lanes)
        .unwrap_or(expected_lanes);
    let wire = r3_wire(
        facts.verified,
        &presented_lanes,
        &expected_lanes,
        &facts.aggregate_head,
        anchored_head,
    );
    let out =
        dregg_lean_ffi::shadow_grain_r3_verify(&wire).map_err(R3Error::LeanCoreUnavailable)?;

    // ⚑ THREE ANSWERS, NOT TWO. `"2 <stage>"` is the Lean side saying it could not READ this
    // wire — proved reachable ONLY from a parse failure by
    // `Dregg2.Grain.R3Verify.r3VerifyWire_malformed_iff` — so it must never be folded into
    // the whole-history `Rejected`. An UNRECOGNISED stage token still refuses: the `"2"` tag
    // alone carries the load-bearing fact and the stage is detail. And an answer this
    // decoder does not recognise AT ALL is also a refusal, not an accept — there is no Rust
    // fallback for the R3 decision by design.
    let mut toks = out.split_whitespace();
    match toks.next() {
        Some("1") => Ok(R3Verified {
            num_turns: finalized.len(),
            anchored_head: *anchored_head,
            aggregate_head: facts.aggregate_head,
            expected_vk: *expected_vk,
        }),
        Some("0") => Err(R3Error::Rejected {
            aggregate_verified: facts.verified,
            aggregate_head: facts.aggregate_head,
            anchored_head: *anchored_head,
            presented_vk: facts.presented_vk,
            expected_vk: *expected_vk,
        }),
        Some("2") => Err(R3Error::WireMalformed {
            stage: toks
                .next()
                .and_then(r3_wire_fault_name)
                .unwrap_or(R3_WIRE_FAULT_UNNAMED),
        }),
        _ => Err(R3Error::WireMalformed {
            stage: R3_WIRE_FAULT_UNNAMED,
        }),
    }
}

#[cfg(test)]
mod wire_verdict_tests {
    use super::*;

    /// The decoder is private, so this lives here rather than in an integration test. It is
    /// the Rust half of the two Lean poles: `"0"` and `"2 <stage>"` must decode to DIFFERENT
    /// variants, and neither may be laundered into the other.
    fn decode(out: &str) -> Result<(), R3Error> {
        // Mirrors the match in `r3_verify` on the decision-relevant tokens only.
        let mut toks = out.split_whitespace();
        match toks.next() {
            Some("1") => Ok(()),
            Some("0") => Err(R3Error::Rejected {
                aggregate_verified: true,
                aggregate_head: [0; SEG_ANCHOR_WIDTH],
                anchored_head: [0; SEG_ANCHOR_WIDTH],
                presented_vk: None,
                expected_vk: RecursionVk([0; 32]),
            }),
            Some("2") => Err(R3Error::WireMalformed {
                stage: toks
                    .next()
                    .and_then(r3_wire_fault_name)
                    .unwrap_or(R3_WIRE_FAULT_UNNAMED),
            }),
            _ => Err(R3Error::WireMalformed {
                stage: R3_WIRE_FAULT_UNNAMED,
            }),
        }
    }

    #[test]
    fn every_lean_fault_code_has_a_stage_name() {
        // The Lean `R3WireFault` has exactly two constructors, codes 0 and 1. If a third is
        // added and this table is not extended, this test goes RED rather than the refusal
        // silently degrading to "unnamed stage".
        for code in ["0", "1"] {
            assert!(
                r3_wire_fault_name(code).is_some(),
                "R3WireFault code {code} has no name in `r3_wire_fault_name` — the refusal \
                 would degrade to the unnamed stage"
            );
        }
        assert!(r3_wire_fault_name("2").is_none());
    }

    #[test]
    fn a_malformed_wire_is_not_the_whole_history_rejection() {
        let rejected = decode("0").expect_err("`0` is a refusal");
        let malformed = decode("2 1").expect_err("`2 1` is a refusal");
        assert!(matches!(rejected, R3Error::Rejected { .. }));
        assert!(matches!(malformed, R3Error::WireMalformed { .. }));
        assert_ne!(
            std::mem::discriminant(&rejected),
            std::mem::discriminant(&malformed),
            "a wire the Lean side could not read must not decode to the whole-history refusal"
        );
        // …and the player-facing sentences differ: only one of them describes the grain.
        assert_ne!(rejected.to_string(), malformed.to_string());
        assert!(
            !malformed.to_string().contains("REJECTED"),
            "the malformed-wire message must not claim a verdict was rendered"
        );
        assert!(malformed.to_string().contains("arity"));
    }

    /// ⚠ An UNRECOGNISED stage, an ABSENT stage, and a reply this decoder does not
    /// understand at all must ALL still refuse as a malformed wire. The `"2"` tag alone
    /// carries the load-bearing fact ("the Lean side could not read what I sent"); the
    /// stage is detail. A decoder older than the Lean enum must not turn that back into
    /// "no verdict", and an unknown reply must not become an ACCEPT.
    #[test]
    fn an_unnamed_or_absent_stage_still_refuses() {
        for out in ["2 9", "2", "banana", ""] {
            match decode(out) {
                Err(R3Error::WireMalformed { stage }) => assert_eq!(
                    stage, R3_WIRE_FAULT_UNNAMED,
                    "{out:?} must carry the unnamed stage"
                ),
                other => panic!("{out:?} must still refuse as a malformed wire; got {other:?}"),
            }
        }
    }
}

/// The exact wire `r3_verify` marshals, exposed for the wound-#22 falsification test so it
/// can drive the Lean-proven decision over forged facts WITHOUT paying for a real
/// minutes-long recursive fold. Same function, same encoding, no re-implementation.
#[doc(hidden)]
pub fn r3_wire_for_test(
    verified: bool,
    presented_vk: &RecursionVk,
    expected_vk: &RecursionVk,
    aggregate_head: &[u32; SEG_ANCHOR_WIDTH],
    anchored_head: &[u32; SEG_ANCHOR_WIDTH],
) -> String {
    r3_wire(
        verified,
        &vk_lanes(presented_vk),
        &vk_lanes(expected_vk),
        aggregate_head,
        anchored_head,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The wire is exactly `R3_WIRE_LEN` decimal ints, in the order the Lean parse reads
    /// (`status ‖ presentedVk ‖ expectedVk ‖ aggregateHead ‖ anchoredHead`). A drift here
    /// would fail CLOSED at the Lean length gate rather than narrow-accept, but it would
    /// still be a bug, so it is pinned.
    #[test]
    fn wire_has_the_lean_arity_and_lane_order() {
        let p = RecursionVk([0u8; 32]);
        let mut e_bytes = [0u8; 32];
        e_bytes[0] = 1;
        let e = RecursionVk(e_bytes);
        let agg: [u32; SEG_ANCHOR_WIDTH] = [10, 11, 12, 13, 14, 15, 16, 17];
        let anch: [u32; SEG_ANCHOR_WIDTH] = [20, 21, 22, 23, 24, 25, 26, 27];
        let wire = r3_wire_for_test(true, &p, &e, &agg, &anch);
        let toks: Vec<&str> = wire.split(' ').collect();
        assert_eq!(toks.len(), R3_WIRE_LEN, "wire arity must match r3WireLen");
        assert_eq!(toks[0], "1", "lane 0 of the wire is the verified-status");
        // presented VK lanes (all zero), then the expected VK's bumped lane 0.
        assert_eq!(&toks[1..9], &["0"; 8][..]);
        assert_eq!(toks[9], (1u32 << 24).to_string(), "big-endian lane packing");
        // the two 8-felt heads, in order, all lanes present.
        assert_eq!(
            &toks[17..25],
            &["10", "11", "12", "13", "14", "15", "16", "17"][..]
        );
        assert_eq!(
            &toks[25..33],
            &["20", "21", "22", "23", "24", "25", "26", "27"][..]
        );
    }

    /// The VK lane packing is a BIJECTION on the 32 bytes — so comparing lanes in Lean is
    /// byte-equality of the fingerprints, and a one-byte difference anywhere shows up.
    #[test]
    fn vk_lane_packing_is_injective_per_byte() {
        let base = RecursionVk([0u8; 32]);
        let base_lanes = vk_lanes(&base);
        for i in 0..32 {
            let mut b = [0u8; 32];
            b[i] = 1;
            let lanes = vk_lanes(&RecursionVk(b));
            assert_ne!(
                lanes, base_lanes,
                "flipping byte {i} of the fingerprint must change the wire lanes"
            );
        }
    }
}
