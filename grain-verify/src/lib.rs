//! # `grain-verify` — the crown weld, CONSUMER side.
//!
//! *THE-GRAIN.md face #1 (Unfoolable): the road toward "you can prove exactly what
//! it did."*
//!
//! A hosted agent's session IS a turn/receipt chain — so a renter should be able to
//! re-witness what their agent did, holding only the artifact the host hands back
//! and re-running nothing. This crate is the consumer side of the honest ladder
//! **R0 → R1 → R2 → R3** (see "The ladder" table below): rungs R0–R2 are LANDED
//! and verified here; the whole is **tamper-evidence + a renter anchor + kernel-
//! turn linkage**, not yet trustlessness — R3 (the whole-history STARK leg,
//! [`WHOLE_HISTORY_GAP`]) is the honest gap.
//!
//! ## ⚠ What it gives today, and what it deliberately does NOT
//!
//! A [`GrainAttestation`] wraps the cumulative, signed receipt chain a hosted
//! [`dregg_agent::session::Session`] produces ([`Session::report`] →
//! [`AgentRunReport`]). [`GrainAttestation::verify`] **composes the existing
//! verifier** [`dregg_agent::agent::verify_agent_run`] — it does not reimplement
//! chain / budget verification — and adds two independent teeth: the report-level
//! **headroom identity** and the **per-step within-budget** reading (no mid-chain
//! excursion, checks the whole chain not just the tip).
//!
//! The honest guarantee: **a holder of the genuine signer key + tip can detect
//! IN-TRANSIT MUTATION of a real report** — a forged/tampered/spliced/reordered
//! receipt, a mid-chain over-budget step, an inflated headroom. That is real and
//! useful. But it is NOT "trust no host", and NOT "nothing else":
//!
//! - **The host holds the receipt key.** Since R0 (`6f58b7086`) the key is a
//!   *random persisted secret*, not `BLAKE3(agent_id)` — so a third-party
//!   report-holder can no longer re-derive it and forge (that hole is closed). But
//!   the **host that runs the session still holds the secret** and can forge a
//!   self-consistent chain. Host-independence does NOT come from a "better receipt
//!   key" (the host runs the signer, whatever it is): it comes from moving the
//!   anchor to a renter-held key (R1, below) and the STARK leg (R3), whose
//!   soundness a key-holding host cannot break.
//! - **Completeness ("nothing else") is not enforced.** Nothing forces every
//!   action the agent took to be receipted; a host can make an off-chain call and
//!   simply never seal a receipt, leaving no contradiction. Completeness is exactly
//!   what the whole-history STARK leaf would add and the signature chain does not.
//!
//! So a passing [`GrainVerified`] means *this report was not mutated in transit*,
//! given an independently-known genuine signer. The 32-byte pin is *(signer key,
//! chain tip)* — see [`GrainAttestation::signer`] / [`GrainAttestation::tip`].
//!
//! ## R1 — the renter finality anchor (LANDED): anti-rewrite + anti-truncation
//!
//! The two limits above (public-derived key, no completeness) are the reason
//! tamper-evidence is not yet unfoolability, and closing them fully is R3 (the
//! whole-history STARK leg, [`WHOLE_HISTORY_GAP`]). But a large, *third-party-
//! verifiable* slice can be closed WITHOUT any circuit, by moving the trust anchor
//! from a host-held key to a **renter-held** one. That is R1, and it ships here:
//!
//! - **[`GenesisPin`]** — at rent the renter supplies a nonce; the platform binds
//!   it to the session signer and re-exposes it in the attestation, so a renter
//!   *recognizes their own session* ("this is MY grain, not a host-fabricated
//!   one"). Honest strength: the nonce is a platform-recorded binding to the
//!   signer, not (yet) forced into the chain's cryptographic genesis — that would
//!   need a dregg-agent change to seed the receipt chain from the nonce.
//! - **[`RenterCheckpoint`] + [`CountersignedCheckpoint`]** — at goal boundaries
//!   the platform offers `(head_root, num_turns)`; the renter **countersigns** it
//!   with THEIR ed25519 key ([`countersign_checkpoint`]), an out-of-band
//!   acknowledgement "I saw the chain reach here". The platform can never forge
//!   this (it does not hold the renter key).
//! - **the two R1 teeth** in [`GrainAttestation::verify`] / [`verify_for_renter`]:
//!   the shown chain must have **≥ num_turns** receipts (**anti-truncation**: a
//!   host cannot show fewer turns than the renter acknowledged — no hiding a
//!   suffix the renter already saw) AND the receipt at the acknowledged position
//!   must hash to the countersigned **head_root** (**anti-rewrite**: a host cannot
//!   present a different history for the acknowledged prefix). A third party
//!   holding `(attestation + renter pubkey + genesis nonce)` checks both, trusting
//!   no host and re-running nothing.
//!
//! Honest scope: R1 gives anti-rewrite/anti-truncation **relative to a renter-
//! acknowledged checkpoint** — it does not by itself prove EXECUTION INTEGRITY of
//! the turns (that a receipt corresponds to a genuine kernel transition), which is
//! exactly R3's whole-history STARK leg. R1 + R3 compose: R1 anchors *which*
//! history to a renter's own key; R3 proves *that* history was genuinely executed.
//!
//! ## R2 — actions become kernel turns, receipts become views (LANDED)
//!
//! R1 anchors *which* history to the renter's key, but a receipt is still just a
//! signed log line — nothing ties it to the kernel. R2 closes that: the
//! `grain-turn` crate (breadstuffs side) implements the `GrainTurnMinter` seam
//! with a REAL `dregg_sdk::ToolGateway::invoke` — every admitted agent action is
//! executed as a **genuine committed executor turn** on a grain turn-cell (the
//! executor's own `calls_made` `FieldLte`/`Monotonic` caveat enforcing the meter
//! HOST-SIDE, and the turn witnessing the action commit / consumed total / heap
//! root as committed state), and the turn's `turn_hash` is sealed into the
//! receipt as its `turn_receipt_hash`. [`verify_r2`](GrainAttestation::verify_r2)
//! / [`verify_r2_for_renter`](GrainAttestation::verify_r2_for_renter) are the
//! consumer teeth: every admitted receipt must be a VIEW over a turn in the
//! executor's committed-turn manifest — an unlinked receipt (the default
//! parallel-universe path) or a fabricated link is REJECTED. Honest scope: R2
//! still trusts the executor host that produced the manifest and committed the
//! turns; it does not re-execute them.
//!
//! ## R3 — the whole-history STARK leg (THE GAP; the road to unfoolability)
//!
//! dregg ships a stronger endpoint: the whole-history light client
//! (`dregg_lightclient::verify_history`) folds a chain of [`FinalizedTurn`]s into
//! ONE recursive STARK aggregate and re-witnesses it against a VK anchor, so a
//! verifier is protected even against a host that HOLDS the signing key (a
//! self-consistent forged chain still has no satisfying leaf). Composing it — with
//! R1's renter anchor pinning *which* history — is what turns this ladder from
//! tamper-evident into unfoolable. We do **not** compose it here yet: R2's grain
//! turns are genuine committed executor turns, but they are not yet minted as the
//! input `verify_history` folds:
//!
//! - `verify_history` consumes `WholeChainProof` built (via `fold_and_attest`)
//!   from `FinalizedTurn { participant: DescriptorParticipant::rotated(leg) }`,
//!   where `leg` is a **real rotated EffectVM multi-table STARK proof** over
//!   before/after `dregg_cell::Cell` state, publishing the 8-felt (~124-bit)
//!   Poseidon2 wide state-commit roots (PI 42/43) the recursion folds.
//! - a grain turn today is committed and hash-linked into the receipt, but no
//!   rotated wide-anchored leg is minted per turn, so there is nothing for the
//!   recursion to fold.
//!
//! So the remaining bridge is a **breadstuffs-side build** in `grain-turn`, not a
//! wiring gap this crate can close: mint each grain turn's rotated wide-anchored
//! EffectVM leg, then this crate can additionally fold the session and hand the
//! renter a 32-byte `verify_history` check. Until then this crate ships the
//! **maximal real subset over `verify_agent_run`**. See [`WHOLE_HISTORY_GAP`] for
//! the exact, machine-readable ask.
//!
//! ## The ladder, one line each (rung ↔ verifier)
//!
//! | rung | closes | verifier here |
//! |------|--------|---------------|
//! | R0 | third-party forgery (random persisted receipt key) + in-transit mutation | [`GrainAttestation::verify`] |
//! | R1 | host rewrite/truncation vs a renter-acknowledged checkpoint | [`GrainAttestation::verify_for_renter`] |
//! | R2 | receipts with no kernel behind them (meter only session-local) | [`GrainAttestation::verify_r2`] / [`verify_r2_for_renter`](GrainAttestation::verify_r2_for_renter) |
//! | R3 | host fabrication — execution integrity + completeness (GAP) | [`WHOLE_HISTORY_GAP`] |
//!
//! Each rung's verifier RUNS every rung below it: `verify_for_renter` includes
//! `verify`; `verify_r2*` includes the base (and, via `verify_r2_for_renter`, the
//! renter anchor). One ladder, not four bolted-on checks.
//!
//! [`Session::report`]: dregg_agent::session::Session::report
//! [`FinalizedTurn`]: https://docs — dregg_circuit_prove::ivc_turn_chain::FinalizedTurn

use dregg_agent::agent::{AgentRunReport, AgentVerifyError, verify_agent_run};
use dregg_agent::receipt::{ReceiptBody, ReceiptSigner, verify_signature};
use dregg_agent::session::Session;
use serde::{Deserialize, Serialize};

/// The exact gap between what a hosted session supplies today and what the
/// whole-history light client (`dregg_lightclient::verify_history`) needs — the
/// breadstuffs-side ask for the crown weld. Surfaced as a constant so a caller /
/// dashboard can render the honest boundary instead of guessing.
pub const WHOLE_HISTORY_GAP: &str = "\
R3 GAP: dregg_lightclient::verify_history needs a WholeChainProof folded (via \
fold_and_attest) from FinalizedTurn{participant: rotated(leg)} legs — real rotated \
EffectVM multi-table STARK proofs over before/after dregg_cell::Cell state \
publishing 8-felt Poseidon2 wide state-commit roots (PI 42/43). \
LANDED BELOW IT: R0 — the receipt key is a random persisted secret (third-party \
forgery closed; the HOST still holds it). R1 — the renter finality anchor \
(GenesisPin + CountersignedCheckpoint) gives third-party-verifiable ANTI-REWRITE + \
ANTI-TRUNCATION relative to a renter-acknowledged checkpoint, no circuit needed. \
R2 — every admitted agent action IS a genuine committed executor turn (grain-turn's \
ToolGatewayMinter over dregg_sdk::ToolGateway::invoke; the executor's calls_made \
caveat meters host-side) and each receipt's turn_receipt_hash links it \
(verify_r2 / verify_r2_for_renter check the links against the committed-turn \
manifest). \
REMAINING BREADSTUFFS ASK (grain-turn): mint each grain turn's rotated \
wide-anchored EffectVM leg alongside the committed turn, then grain-verify can \
fold the session via fold_and_attest -> verify_history (THE-GRAIN crown-weld #3 / \
gap #7) and execution integrity + in-chain completeness become FRI-floor theorems \
— R1 anchors WHICH history, R2 anchors each receipt TO a committed turn, R3 proves \
THAT history genuinely executed. Until then grain-verify ships the maximal real \
subset over verify_agent_run: tamper-evident + renter-anchored + kernel-linked, \
not unfoolable.";

/// **R1 — the renter finality anchor's genesis half.** The nonce the renter chose
/// at rent, bound to the session signer the platform anchored it to. A renter
/// pins their nonce out-of-band and recognizes their own session in an
/// attestation ("this is MY grain, not a host-fabricated one").
///
/// Honest strength: `renter_nonce` is a *platform-recorded* binding to `signer`,
/// re-exposed in the attestation — NOT (yet) forced into the chain's cryptographic
/// genesis (that needs a dregg-agent change to seed the receipt chain from the
/// nonce). It lets a renter recognize the session and pin the signer; it does not
/// alone prove the host could not have run a *parallel* session under a different
/// nonce (the countersigned checkpoint is what pins the actual history).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenesisPin {
    /// The renter-chosen nonce, supplied at rent.
    pub renter_nonce: [u8; 32],
    /// The session receipt-chain signer this nonce was bound to at rent.
    pub signer: [u8; 32],
}

/// Domain separator for the bytes a renter countersigns over a [`RenterCheckpoint`].
pub const RENTER_CHECKPOINT_DOMAIN: &[u8] = b"dregg-grain-renter-checkpoint-v1";

/// **R1 — a checkpoint the platform offers at a goal boundary for the renter to
/// countersign.** `head_root` is the chain tip (the 32-byte commitment to the
/// session so far); `num_turns` is how many receipts are under it. A renter
/// countersigns this to acknowledge "I saw the chain reach exactly here".
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RenterCheckpoint {
    /// The chain tip at this point — the receipt hash of the `num_turns`-th receipt.
    pub head_root: [u8; 32],
    /// The number of receipts (turns) committed under `head_root`.
    pub num_turns: u64,
}

impl RenterCheckpoint {
    /// The canonical, domain-separated bytes the renter signs (and a verifier
    /// re-derives). Binds the head root and the turn count together, so neither can
    /// be moved without invalidating the countersignature.
    pub fn signing_bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(RENTER_CHECKPOINT_DOMAIN.len() + 40);
        v.extend_from_slice(RENTER_CHECKPOINT_DOMAIN);
        v.extend_from_slice(&self.head_root);
        v.extend_from_slice(&self.num_turns.to_le_bytes());
        v
    }
}

/// **R1 — a renter-countersigned checkpoint.** The renter's ed25519 signature over
/// a [`RenterCheckpoint`], under a key the platform does not hold. This is the
/// renter's out-of-band acknowledgement that anchors "which history" to the
/// renter's own authority; the anti-rewrite/anti-truncation teeth check the shown
/// chain against it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CountersignedCheckpoint {
    /// The acknowledged checkpoint.
    pub checkpoint: RenterCheckpoint,
    /// The renter's public key (pinned by a third-party verifier out-of-band).
    pub renter_pubkey: [u8; 32],
    /// ed25519 signature over [`RenterCheckpoint::signing_bytes`].
    pub renter_sig: Vec<u8>,
}

impl CountersignedCheckpoint {
    /// `true` iff the renter countersignature verifies over the checkpoint's
    /// canonical bytes under `renter_pubkey`. Fail-closed on any malformed input.
    pub fn sig_verifies(&self) -> bool {
        verify_signature(
            &self.renter_pubkey,
            &self.checkpoint.signing_bytes(),
            &self.renter_sig,
        )
    }
}

/// **The renter side of R1** — countersign a checkpoint with the renter's own
/// ed25519 key (a 32-byte secret seed the renter holds; the platform never does).
/// Uses dregg-agent's [`ReceiptSigner::sign_raw`] over the checkpoint's
/// domain-separated bytes. The resulting [`CountersignedCheckpoint`] is what the
/// renter POSTs back to `<grain-host>/checkpoint`.
pub fn countersign_checkpoint(
    renter_seed: [u8; 32],
    checkpoint: RenterCheckpoint,
) -> CountersignedCheckpoint {
    let signer = ReceiptSigner::from_seed(renter_seed);
    let renter_sig = signer.sign_raw(&checkpoint.signing_bytes());
    CountersignedCheckpoint {
        checkpoint,
        renter_pubkey: signer.public(),
        renter_sig,
    }
}

/// The **renter-facing artifact** over a hosted session: its cumulative, signed
/// receipt chain wrapped so a renter can re-witness it. Serializable — this is the
/// bytes a host hands back and a renter (in-browser, offline) verifies.
///
/// Build one with [`attest`](GrainAttestation::attest) over a live
/// [`Session`], or [`from_report`](GrainAttestation::from_report) over a report
/// received over the wire. Verify with [`verify`](GrainAttestation::verify) (or
/// [`verify_against_signer`](GrainAttestation::verify_against_signer) to also pin
/// the promised signer key, the VK-anchor analogue).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GrainAttestation {
    /// The cumulative run report — every goal's receipts in ONE signed chain plus
    /// the budget bound. The whole session as one re-witnessable artifact.
    pub report: AgentRunReport,
    /// **R1** — the renter's genesis pin (the nonce they chose at rent, bound to
    /// the chain signer), when the platform recorded one. Lets a renter recognize
    /// their own session; checked by [`verify`](Self::verify) /
    /// [`verify_for_renter`](Self::verify_for_renter).
    #[serde(default)]
    pub genesis: Option<GenesisPin>,
    /// **R1** — the latest renter-countersigned checkpoint the platform holds for
    /// this grain, when the renter has acknowledged one. The anti-rewrite/anti-
    /// truncation teeth check the shown chain extends exactly this.
    #[serde(default)]
    pub checkpoint: Option<CountersignedCheckpoint>,
}

impl GrainAttestation {
    /// **Attest a live hosted session** — snapshot its cumulative signed receipt
    /// chain into the renter-facing artifact. Cheap: reads
    /// [`Session::report`](dregg_agent::session::Session::report). Carries no R1
    /// anchor; attach one with [`with_genesis`](Self::with_genesis) /
    /// [`with_checkpoint`](Self::with_checkpoint) (the platform does this in
    /// `AgentPlatform::attest`).
    pub fn attest(session: &Session) -> GrainAttestation {
        GrainAttestation {
            report: session.report(),
            genesis: None,
            checkpoint: None,
        }
    }

    /// Wrap a report received over the wire (a renter who fetched the artifact
    /// from the host / a relayer, never having held the `Session`).
    pub fn from_report(report: AgentRunReport) -> GrainAttestation {
        GrainAttestation {
            report,
            genesis: None,
            checkpoint: None,
        }
    }

    /// Attach the renter's genesis pin (R1). Builder form.
    pub fn with_genesis(mut self, genesis: GenesisPin) -> GrainAttestation {
        self.genesis = Some(genesis);
        self
    }

    /// Attach the latest renter-countersigned checkpoint (R1). Builder form.
    pub fn with_checkpoint(mut self, checkpoint: CountersignedCheckpoint) -> GrainAttestation {
        self.checkpoint = Some(checkpoint);
        self
    }

    /// The checkpoint a renter would countersign for the CURRENT chain tip:
    /// `(head_root = tip, num_turns = receipts.len())`. `None` if the session has
    /// committed nothing yet (no tip to acknowledge). This is what
    /// `GET <grain-host>/checkpoint` returns.
    pub fn checkpoint_to_countersign(&self) -> Option<RenterCheckpoint> {
        self.tip().map(|head_root| RenterCheckpoint {
            head_root,
            num_turns: self.report.receipts.len() as u64,
        })
    }

    /// The receipt-chain signer public key — the trust anchor a renter pins
    /// out-of-band (the key the host promised is *their* agent's), exactly as a
    /// light client pins a VK. Verification is meaningful only against a pinned
    /// signer; see [`verify_against_signer`](Self::verify_against_signer).
    pub fn signer(&self) -> [u8; 32] {
        self.report.signer
    }

    /// The chain tip — the final committed receipt hash, the 32-byte commitment to
    /// the WHOLE session (`None` if the agent committed nothing). Pinned alongside
    /// [`signer`](Self::signer).
    pub fn tip(&self) -> Option<[u8; 32]> {
        self.report.tip()
    }

    /// The agent id the receipts name (whose session this was).
    pub fn agent(&self) -> &str {
        &self.report.agent
    }

    /// **Re-witness the attestation (tamper-evidence, given a genuine pinned
    /// signer — see the crate note on why this is not yet host-independent).**
    /// Composes
    /// [`verify_agent_run`] (chain genuine + ordered + single-signer; consumed ≤
    /// budget at the tip; tip agrees with the report total) and adds the two
    /// independent teeth it does not cover:
    ///
    /// 1. **headroom identity** — `report.headroom == (budget − consumed).max(0)`.
    ///    Headroom is an unsigned report field; a report cannot overstate the
    ///    could-still-do bound.
    /// 2. **per-step within-budget** — for EVERY receipt (not just the tip):
    ///    `consumed_after` is non-decreasing, never exceeds the ceiling, and
    ///    `headroom_after == (budget − consumed_after).max(0)`. Catches a
    ///    mid-chain budget excursion / inconsistent accounting a tip-only check
    ///    would miss.
    ///
    /// Returns [`GrainVerified`] — what the renter learns.
    pub fn verify(&self) -> Result<GrainVerified, GrainVerifyError> {
        // Tooth set A — the composed verifier: chain genuine, ordered,
        // single-signer, nothing spliced/hidden/reordered, consumed ≤ budget at
        // the tip, tip agrees with the report total.
        let run = verify_agent_run(&self.report).map_err(GrainVerifyError::Run)?;

        let budget = self.report.budget;

        // Tooth B — the headroom identity (an unsigned report field): the
        // "everything it could still have done" bound is EXACT, not inflated.
        let expected_headroom = (budget - self.report.consumed).max(0);
        if self.report.headroom != expected_headroom {
            return Err(GrainVerifyError::HeadroomInconsistent {
                claimed: self.report.headroom,
                expected: expected_headroom,
            });
        }

        // Tooth C — per-step within-budget, over the WHOLE chain (verify_agent_run
        // only checks the tip). This catches an *inconsistent* forgery (a mutated
        // genuine report with a mid-chain over-budget step or phantom spend); it does
        // NOT catch a *consistent* forgery — a key-holder builds a chain where every
        // step is within budget, so this tooth is vacuous against the host (see the
        // crate note; the STARK leg is what closes that gap).
        let mut prev = 0i64;
        for r in &self.report.receipts {
            if r.consumed_after < prev {
                return Err(GrainVerifyError::NonMonotonicSpend { seq: r.seq });
            }
            if r.consumed_after > budget {
                return Err(GrainVerifyError::StepOverBudget {
                    seq: r.seq,
                    consumed_after: r.consumed_after,
                    budget,
                });
            }
            let expect_hr = (budget - r.consumed_after).max(0);
            if r.headroom_after != expect_hr {
                return Err(GrainVerifyError::StepHeadroomInconsistent {
                    seq: r.seq,
                    claimed: r.headroom_after,
                    expected: expect_hr,
                });
            }
            prev = r.consumed_after;
        }

        // Tooth set D (R1 — the renter finality anchor): if a genesis pin / a
        // renter-countersigned checkpoint is present, the shown chain must NOT have
        // rewritten or truncated relative to what the renter acknowledged. Runs
        // after the chain has been re-witnessed above, so `receipt_hash()` is sound.
        self.check_anchor()?;

        Ok(GrainVerified {
            agent: self.report.agent.clone(),
            actions: run.actions,
            consumed: run.consumed,
            budget: run.budget,
            headroom: run.headroom,
            signer: self.report.signer,
            tip: self.report.tip(),
        })
    }

    /// [`verify`](Self::verify) that ALSO pins the signer — the renter checks the
    /// chain was produced by the key the host promised is their agent's (the
    /// VK-anchor analogue: a valid chain by the WRONG key is refused). Without
    /// this pin, any host could hand back a valid chain by a key it minted; the
    /// pin is what makes "*my* agent" meaningful.
    pub fn verify_against_signer(
        &self,
        expected_signer: &[u8; 32],
    ) -> Result<GrainVerified, GrainVerifyError> {
        if &self.report.signer != expected_signer {
            return Err(GrainVerifyError::SignerMismatch {
                expected: *expected_signer,
                found: self.report.signer,
            });
        }
        self.verify()
    }

    /// **R1 — the renter/third-party verify.** [`verify`](Self::verify) that ALSO
    /// PINS the renter's own pubkey and genesis nonce, and REQUIRES the anchor to
    /// be present. A third party holding `(attestation + renter pubkey + genesis
    /// nonce)` uses this to check the host neither **rewrote** nor **truncated** the
    /// history relative to what the renter acknowledged, trusting no host and
    /// re-running nothing:
    ///
    /// - the attestation must carry a [`GenesisPin`] whose `renter_nonce` is the
    ///   renter's (else the host swapped in a different session), and
    /// - a [`CountersignedCheckpoint`] whose `renter_pubkey` is the renter's (else
    ///   the host countersigned with a key it minted), and
    /// - all of [`verify`](Self::verify)'s teeth pass — including the two R1 teeth
    ///   (anti-truncation: `num_turns` receipts are shown; anti-rewrite: the
    ///   receipt at the acknowledged position hashes to the countersigned
    ///   `head_root`).
    ///
    /// Requiring the anchor closes the omission hole: a renter who countersigned a
    /// checkpoint will not accept an attestation that simply drops it.
    pub fn verify_for_renter(
        &self,
        renter_pubkey: &[u8; 32],
        genesis_nonce: &[u8; 32],
    ) -> Result<GrainVerified, GrainVerifyError> {
        let g = self
            .genesis
            .as_ref()
            .ok_or(GrainVerifyError::MissingGenesis)?;
        if &g.renter_nonce != genesis_nonce {
            return Err(GrainVerifyError::GenesisNonceMismatch {
                expected: *genesis_nonce,
                found: g.renter_nonce,
            });
        }
        let cs = self
            .checkpoint
            .as_ref()
            .ok_or(GrainVerifyError::MissingCheckpoint)?;
        if &cs.renter_pubkey != renter_pubkey {
            return Err(GrainVerifyError::RenterKeyMismatch {
                expected: *renter_pubkey,
                found: cs.renter_pubkey,
            });
        }
        self.verify()
    }

    /// **R2 — the kernel-turn tooth (THE-GRAIN.md face #1, rung R2: "actions become
    /// kernel turns, receipts become views").** [`verify`](Self::verify) that ALSO
    /// requires every admitted receipt to be a VIEW over a GENUINE committed kernel
    /// turn: its `turn_receipt_hash` must be `Some` AND name a turn in
    /// `committed_turns` (the executor host's manifest of turns it committed for
    /// this session). A receipt with a `None` link (the default parallel-universe
    /// path, where the action never became a kernel turn) OR a link naming no
    /// committed turn (a fabricated hash) is REJECTED. Both teeth bite.
    ///
    /// The `carryover:` genesis receipt a re-attach seeds
    /// ([`AgentCloud::restore_consumed`](dregg_agent::agent::AgentCloud)) is a
    /// synthetic root step, not an agent action, so it is exempt from the link
    /// requirement.
    ///
    /// ## Honest scope (R2, not R3)
    ///
    /// This proves each receipt is bound to a turn the executor host committed, and
    /// — because the agent run loop only seals a receipt when the executor ADMITTED
    /// the turn (its `calls_made` `FieldLte`/`Monotonic` caveat) — that the meter
    /// was enforced HOST-SIDE, not merely session-local. It still TRUSTS the
    /// executor host that produced `committed_turns` and committed those turns:
    /// nothing here re-executes them. Removing that trust — proving *that* each
    /// turn genuinely executed a kernel transition — is R3's whole-history STARK
    /// leg ([`WHOLE_HISTORY_GAP`]); R2 anchors each receipt to a committed turn, R3
    /// proves the turn ran. (A tampered link is caught even earlier: it is bound
    /// into the signed receipt hash, so [`verify`](Self::verify) already rejects it
    /// with a bad signature — this tooth is what catches a *self-consistent* chain
    /// that simply never became kernel turns.)
    pub fn verify_r2(&self, committed_turns: &[[u8; 32]]) -> Result<R2Verified, GrainVerifyError> {
        let base = self.verify()?;
        let linked = self.check_turn_links(committed_turns)?;
        Ok(R2Verified { base, linked })
    }

    /// **The full landed ladder in ONE call (R0 + R1 + R2).**
    /// [`verify_for_renter`](Self::verify_for_renter) (the renter/third-party R1
    /// check: renter pubkey + genesis nonce pinned, anchor REQUIRED, anti-rewrite +
    /// anti-truncation) PLUS the R2 kernel-turn link teeth
    /// ([`verify_r2`](Self::verify_r2)'s: every admitted receipt views a turn in
    /// `committed_turns`). This is what a renter holding all three pins — their
    /// pubkey, their genesis nonce, and the executor's committed-turn manifest —
    /// runs to get everything short of R3 ([`WHOLE_HISTORY_GAP`]).
    pub fn verify_r2_for_renter(
        &self,
        renter_pubkey: &[u8; 32],
        genesis_nonce: &[u8; 32],
        committed_turns: &[[u8; 32]],
    ) -> Result<R2Verified, GrainVerifyError> {
        let base = self.verify_for_renter(renter_pubkey, genesis_nonce)?;
        let linked = self.check_turn_links(committed_turns)?;
        Ok(R2Verified { base, linked })
    }

    /// The R2 link teeth (shared by [`verify_r2`](Self::verify_r2) and
    /// [`verify_r2_for_renter`](Self::verify_r2_for_renter)): every admitted
    /// receipt must carry a `turn_receipt_hash` naming a turn in
    /// `committed_turns`. Returns how many linked. Run only AFTER the chain has
    /// been re-witnessed (the links ride the signed bodies).
    fn check_turn_links(&self, committed_turns: &[[u8; 32]]) -> Result<usize, GrainVerifyError> {
        let mut linked = 0usize;
        for r in &self.report.receipts {
            // The re-attach carryover genesis is a synthetic root step, not an
            // agent action — it legitimately carries no kernel-turn link.
            if r.action.starts_with("carryover:") {
                continue;
            }
            let link = r.attestation.as_ref().and_then(|a| a.turn_receipt_hash);
            match link {
                None => return Err(GrainVerifyError::R2Unlinked { seq: r.seq }),
                Some(h) => {
                    if !committed_turns.iter().any(|t| t == &h) {
                        return Err(GrainVerifyError::R2FabricatedLink {
                            seq: r.seq,
                            found: h,
                        });
                    }
                    linked += 1;
                }
            }
        }
        Ok(linked)
    }

    /// The R1 anchor teeth (a private helper `verify` folds in). Checks — only when
    /// the corresponding anchor field is present — that the shown chain matches what
    /// the renter anchored/acknowledged: the genesis pin names this chain's signer,
    /// the countersignature verifies, and the shown chain neither truncated nor
    /// rewrote the acknowledged prefix. A vacuous no-op when no anchor is attached
    /// (a bare tamper-evidence attestation is unaffected).
    fn check_anchor(&self) -> Result<(), GrainVerifyError> {
        // Genesis pin: it must name THIS chain's signer (else it is a pin for some
        // OTHER session, wrongly attached).
        if let Some(g) = &self.genesis {
            if g.signer != self.report.signer {
                return Err(GrainVerifyError::GenesisSignerMismatch {
                    pin: g.signer,
                    chain: self.report.signer,
                });
            }
        }
        // Countersigned checkpoint: renter sig + anti-truncation + anti-rewrite.
        if let Some(cs) = &self.checkpoint {
            if !cs.sig_verifies() {
                return Err(GrainVerifyError::RenterSigInvalid);
            }
            let n = cs.checkpoint.num_turns;
            if n == 0 {
                return Err(GrainVerifyError::EmptyCheckpoint);
            }
            // ANTI-TRUNCATION: the shown chain must carry at least as many turns as
            // the renter acknowledged — a host cannot show fewer than the renter saw.
            let shown = self.report.receipts.len() as u64;
            if shown < n {
                return Err(GrainVerifyError::Truncated {
                    acknowledged: n,
                    shown,
                });
            }
            // ANTI-REWRITE: the receipt at the acknowledged position must hash to the
            // countersigned head_root — the acknowledged prefix is exactly the one the
            // renter signed, not a different history the host ran.
            let idx = (n - 1) as usize;
            let at = self.report.receipts[idx].receipt_hash();
            if at != Some(cs.checkpoint.head_root) {
                return Err(GrainVerifyError::Rewritten {
                    acknowledged: cs.checkpoint.head_root,
                    found: at,
                    position: n,
                });
            }
        }
        Ok(())
    }
}

/// **What a renter learns** from a passing [`GrainAttestation::verify`] — the
/// whole-session verdict, re-witnessing nothing. Given an independently-known
/// genuine `signer`, holding it means: *this report was not mutated in transit —
/// every one of `actions` receipts is signed + ordered under `signer`, the agent
/// consumed exactly `consumed` of its `budget` ceiling, leaving exactly `headroom`*.
/// It does NOT establish "nothing else" (completeness) or independence from a
/// key-holding host — see the crate note.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainVerified {
    /// The agent id the session ran under.
    pub agent: String,
    /// Admitted actions re-witnessed in the chain (== receipt count).
    pub actions: usize,
    /// Budget consumed across the whole session.
    pub consumed: i64,
    /// The budget ceiling — the hard bound on everything it *could* have done.
    pub budget: i64,
    /// Un-drawn headroom (`budget − consumed`) — un-exercised authority, surfaced.
    pub headroom: i64,
    /// The signer key this verdict is anchored to (pin it out-of-band).
    pub signer: [u8; 32],
    /// The chain tip — the 32-byte commitment to the whole session.
    pub tip: Option<[u8; 32]>,
}

/// **What a renter learns from a passing [`GrainAttestation::verify_r2`]** — the
/// whole-session [`GrainVerified`] verdict PLUS that every admitted receipt is a
/// VIEW over a genuine committed kernel turn (`linked` of them), so the meter was
/// enforced host-side (R2). It does NOT establish that each turn genuinely executed
/// (execution integrity) — that is R3's whole-history STARK leg.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R2Verified {
    /// The base tamper-evidence + budget verdict.
    pub base: GrainVerified,
    /// How many admitted receipts were confirmed as views over committed turns
    /// (the `carryover:` genesis step, if any, is exempt and not counted).
    pub linked: usize,
}

impl R2Verified {
    /// A one-line renter-facing summary.
    pub fn summary(&self) -> String {
        format!(
            "{} — plus all {} action(s) are views over genuine committed kernel turns (R2: the meter is enforced host-side)",
            self.base.summary(),
            self.linked
        )
    }
}

impl GrainVerified {
    /// A one-line renter-facing summary.
    pub fn summary(&self) -> String {
        format!(
            "grain {}: {} action(s) signed + ordered, consumed {}/{} (headroom {}); untampered under the pinned signer",
            self.agent, self.actions, self.consumed, self.budget, self.headroom
        )
    }
}

/// Why a [`GrainAttestation`] failed to re-witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GrainVerifyError {
    /// The composed [`verify_agent_run`] rejected the chain: forged / tampered /
    /// spliced / reordered receipts, or consumed over the ceiling at the tip, or
    /// the tip disagreeing with the report total.
    Run(AgentVerifyError),
    /// The report's `headroom` is not the exact `(budget − consumed).max(0)` bound
    /// — a report overstating the could-still-do headroom (an unsigned field).
    HeadroomInconsistent {
        /// The headroom the report claims.
        claimed: i64,
        /// The exact headroom the budget/consumed imply.
        expected: i64,
    },
    /// A receipt's `consumed_after` decreased — the meter cannot un-spend.
    NonMonotonicSpend {
        /// The offending chain position.
        seq: u64,
    },
    /// A mid-chain step's `consumed_after` exceeds the ceiling — a budget excursion
    /// a tip-only check would miss.
    StepOverBudget {
        /// The offending chain position.
        seq: u64,
        /// The consumed total at that step.
        consumed_after: i64,
        /// The ceiling it exceeds.
        budget: i64,
    },
    /// A receipt's `headroom_after` is not the exact `(budget − consumed_after)`
    /// bound — inconsistent per-step accounting.
    StepHeadroomInconsistent {
        /// The offending chain position.
        seq: u64,
        /// The headroom the receipt claims.
        claimed: i64,
        /// The exact headroom implied.
        expected: i64,
    },
    /// The chain's signer is not the renter's pinned key — a valid chain by the
    /// WRONG authority (only from [`verify_against_signer`]).
    SignerMismatch {
        /// The signer the renter pinned.
        expected: [u8; 32],
        /// The signer the chain actually carries.
        found: [u8; 32],
    },
    /// **R1** — the genesis pin names a signer other than this chain's (a pin for
    /// some other session, wrongly attached).
    GenesisSignerMismatch {
        /// The signer the pin claims.
        pin: [u8; 32],
        /// The signer the chain actually carries.
        chain: [u8; 32],
    },
    /// **R1** — the renter countersignature does not verify over the checkpoint's
    /// canonical bytes under the carried `renter_pubkey` (forged/absent/tampered).
    RenterSigInvalid,
    /// **R1** — a countersigned checkpoint acknowledged zero turns (nothing to
    /// anchor; a checkpoint must cover at least one committed receipt).
    EmptyCheckpoint,
    /// **R1 — ANTI-TRUNCATION** — the shown chain has fewer turns than the renter
    /// countersigned: the host is hiding turns the renter already acknowledged.
    Truncated {
        /// The turn count the renter acknowledged.
        acknowledged: u64,
        /// The turn count the attestation actually shows.
        shown: u64,
    },
    /// **R1 — ANTI-REWRITE** — the receipt at the acknowledged position does not
    /// hash to the countersigned `head_root`: the host ran a DIFFERENT history for
    /// the prefix the renter signed.
    Rewritten {
        /// The head root the renter countersigned.
        acknowledged: [u8; 32],
        /// The head root the shown chain has at that position (`None` if absent).
        found: Option<[u8; 32]>,
        /// The acknowledged turn count (the 1-based position checked).
        position: u64,
    },
    /// **R1** — [`verify_for_renter`](GrainAttestation::verify_for_renter) required
    /// a genesis pin but the attestation carries none (a dropped anchor).
    MissingGenesis,
    /// **R1** — the genesis pin's nonce is not the renter's pinned nonce (a
    /// different session substituted).
    GenesisNonceMismatch {
        /// The nonce the renter pinned.
        expected: [u8; 32],
        /// The nonce the attestation carries.
        found: [u8; 32],
    },
    /// **R1** — [`verify_for_renter`](GrainAttestation::verify_for_renter) required
    /// a countersigned checkpoint but the attestation carries none (a dropped
    /// acknowledgement).
    MissingCheckpoint,
    /// **R1** — the countersigned checkpoint is under a key other than the renter's
    /// pinned pubkey (the host countersigned with a key it minted).
    RenterKeyMismatch {
        /// The renter pubkey the verifier pinned.
        expected: [u8; 32],
        /// The pubkey the countersignature actually carries.
        found: [u8; 32],
    },
    /// **R2** — an admitted receipt carries NO kernel-turn link (`turn_receipt_hash`
    /// is `None`): the action never became a genuine kernel turn (the default
    /// parallel-universe path). The R2 tooth requires every admitted action to be a
    /// view over a committed turn.
    R2Unlinked {
        /// The offending chain position.
        seq: u64,
    },
    /// **R2** — an admitted receipt's kernel-turn link names no turn in the
    /// committed-turn manifest (a fabricated hash the executor never committed).
    R2FabricatedLink {
        /// The offending chain position.
        seq: u64,
        /// The link the receipt carries that no committed turn matches.
        found: [u8; 32],
    },
}

impl core::fmt::Display for GrainVerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            GrainVerifyError::Run(e) => write!(f, "grain: receipt chain did not re-witness: {e}"),
            GrainVerifyError::HeadroomInconsistent { claimed, expected } => write!(
                f,
                "grain: headroom {claimed} is not the exact bound {expected} (budget − consumed)"
            ),
            GrainVerifyError::NonMonotonicSpend { seq } => {
                write!(f, "grain: consumed decreased at receipt seq {seq}")
            }
            GrainVerifyError::StepOverBudget {
                seq,
                consumed_after,
                budget,
            } => write!(
                f,
                "grain: receipt seq {seq} is over budget mid-chain: consumed {consumed_after} > ceiling {budget}"
            ),
            GrainVerifyError::StepHeadroomInconsistent {
                seq,
                claimed,
                expected,
            } => write!(
                f,
                "grain: receipt seq {seq} headroom {claimed} is not the exact bound {expected}"
            ),
            GrainVerifyError::SignerMismatch { .. } => write!(
                f,
                "grain: the chain signer is not the renter's pinned key (wrong authority)"
            ),
            GrainVerifyError::GenesisSignerMismatch { .. } => write!(
                f,
                "grain(R1): the genesis pin names a different signer than this chain (pin for another session)"
            ),
            GrainVerifyError::RenterSigInvalid => write!(
                f,
                "grain(R1): the renter countersignature does not verify (forged/absent/tampered)"
            ),
            GrainVerifyError::EmptyCheckpoint => write!(
                f,
                "grain(R1): the countersigned checkpoint acknowledges zero turns"
            ),
            GrainVerifyError::Truncated {
                acknowledged,
                shown,
            } => write!(
                f,
                "grain(R1 anti-truncation): the chain shows {shown} turn(s) but the renter countersigned {acknowledged} — turns are being hidden"
            ),
            GrainVerifyError::Rewritten { position, .. } => write!(
                f,
                "grain(R1 anti-rewrite): the receipt at acknowledged position {position} does not hash to the countersigned head_root — the prefix was rewritten"
            ),
            GrainVerifyError::MissingGenesis => write!(
                f,
                "grain(R1): verify_for_renter requires a genesis pin, but none is attached"
            ),
            GrainVerifyError::GenesisNonceMismatch { .. } => write!(
                f,
                "grain(R1): the genesis pin's nonce is not the renter's pinned nonce (different session)"
            ),
            GrainVerifyError::MissingCheckpoint => write!(
                f,
                "grain(R1): verify_for_renter requires a countersigned checkpoint, but none is attached"
            ),
            GrainVerifyError::RenterKeyMismatch { .. } => write!(
                f,
                "grain(R1): the checkpoint is countersigned by a key other than the renter's pinned pubkey"
            ),
            GrainVerifyError::R2Unlinked { seq } => write!(
                f,
                "grain(R2): admitted receipt seq {seq} has no kernel-turn link (turn_receipt_hash is None) — the action never became a genuine kernel turn"
            ),
            GrainVerifyError::R2FabricatedLink { seq, .. } => write!(
                f,
                "grain(R2): admitted receipt seq {seq} names a kernel turn that is not in the committed-turn manifest (a fabricated link)"
            ),
        }
    }
}

impl std::error::Error for GrainVerifyError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_agent::agent::{AgentAction, AgentSpec, PlannedBrain, SyntheticMinter, ToolCall};
    use dregg_agent::receipt::ChainError;
    use dregg_agent::toolkit::Toolkit;
    use dregg_agent::tools::{OperatorTools, ShellOut};
    use std::path::Path;

    /// A deterministic echo shell toolkit (side-effect-light).
    fn echo_toolkit(wd: &Path) -> OperatorTools {
        OperatorTools::new(Toolkit::new(), wd).with_shell(|cmd: &str, _cwd: &Path| {
            Ok(ShellOut {
                exit: 0,
                stdout: format!("ran: {cmd}"),
                stderr: String::new(),
                new_cwd: None,
            })
        })
    }

    /// A recorded brain: a fixed plan of shell ops.
    fn shell_plan(cmds: &[&str]) -> PlannedBrain {
        let plan = cmds
            .iter()
            .map(|c| AgentAction::Op(ToolCall::new("shell", [("cmd".to_string(), c.to_string())])))
            .collect();
        PlannedBrain::new(plan)
    }

    fn wd() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "grain-verify-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&p).unwrap();
        p
    }

    /// Drive a two-goal session over a small budget → the artifact under test.
    fn driven_session(seed: [u8; 32], budget: i64) -> (Session, std::path::PathBuf) {
        let dir = wd();
        let tk = echo_toolkit(&dir);
        let spec = AgentSpec::new("ignored", budget).with_shell();
        let mut sess = Session::open_seeded(seed, "dga1_renter", spec).unwrap();
        sess.run_goal("goal one", &mut shell_plan(&["a", "b"]), &tk);
        sess.run_goal("goal two", &mut shell_plan(&["c", "d", "e"]), &tk);
        (sess, dir)
    }

    // ── THE HAPPY PATH: a driven session attests + a renter verifies ──────────
    #[test]
    fn a_driven_session_attests_and_a_renter_verifies() {
        let (sess, dir) = driven_session([1u8; 32], 20);

        let att = GrainAttestation::attest(&sess);
        let v = att.verify().expect("a genuine session re-witnesses");

        assert_eq!(v.actions, 5, "both goals fold into ONE chain (2 + 3)");
        assert_eq!(v.consumed, 5);
        assert_eq!(v.budget, 20);
        assert_eq!(v.headroom, 15, "20 − 5 — un-exercised authority");
        assert_eq!(v.signer, att.signer());
        assert_eq!(v.tip, att.tip());
        assert!(v.tip.is_some(), "the session committed a chain tip");

        // The renter pins the promised signer key → still verifies.
        att.verify_against_signer(&att.signer())
            .expect("the pinned-signer path verifies for the right key");

        // The artifact round-trips as bytes (what a host hands back / a browser reads).
        let bytes = serde_json::to_vec(&att).unwrap();
        let att2: GrainAttestation = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(att2.verify().unwrap(), v, "same verdict off the wire");

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: a TAMPERED action fails (did-nothing-else / genuine) ───────────
    #[test]
    fn a_tampered_action_fails() {
        let (sess, dir) = driven_session([2u8; 32], 20);
        let mut att = GrainAttestation::attest(&sess);

        // Forge what an action was → the signed body no longer matches.
        att.report.receipts[0].action = "shell:forged-i-never-ran-this".into();
        assert!(matches!(
            att.verify(),
            Err(GrainVerifyError::Run(AgentVerifyError::Chain(
                ChainError::BadSignature { .. }
            )))
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: a SPLICED-OUT goal fails (nothing hidden) ──────────────────────
    #[test]
    fn a_spliced_chain_fails() {
        let (sess, dir) = driven_session([3u8; 32], 20);
        let mut att = GrainAttestation::attest(&sess);

        // Remove a receipt from the middle → the prev-hash link breaks.
        att.report.receipts.remove(2);
        assert!(matches!(
            att.verify(),
            Err(GrainVerifyError::Run(AgentVerifyError::Chain(
                ChainError::BrokenLink { .. }
            )))
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: a SHORT / truncated chain (drop the tip) fails the total ───────
    #[test]
    fn a_truncated_chain_fails() {
        let (sess, dir) = driven_session([4u8; 32], 20);
        let mut att = GrainAttestation::attest(&sess);

        // Drop the LAST receipt but keep the report's consumed total → the chain
        // tip no longer agrees with the claimed consumption.
        att.report.receipts.pop();
        assert!(matches!(
            att.verify(),
            Err(GrainVerifyError::Run(
                AgentVerifyError::ConsumedMismatch { .. }
            ))
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: an INJECTED action (nothing else did more) fails ───────────────
    #[test]
    fn an_injected_action_fails() {
        let (sess, dir) = driven_session([5u8; 32], 20);
        let mut att = GrainAttestation::attest(&sess);

        // Splice a real receipt back in as an "extra" action the agent never took
        // → the duplicated seq / broken link is caught. (An action with no genuine
        // signed receipt cannot be added; the chain admits nothing off-band.)
        let forged = att.report.receipts[1].clone();
        att.report.receipts.push(forged);
        assert!(
            att.verify().is_err(),
            "an injected action cannot ride the genuine chain"
        );

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: consumed > budget fails (within budget) ────────────────────────
    #[test]
    fn consumed_over_budget_fails() {
        let (sess, dir) = driven_session([6u8; 32], 20);
        let mut att = GrainAttestation::attest(&sess);
        assert_eq!(att.report.consumed, 5);

        // Lower the ceiling below the (genuine, chained) consumed total → the hard
        // bound is violated even though every receipt is authentic.
        att.report.budget = 4;
        att.report.headroom = 0; // keep the headroom field self-consistent for the budget tooth
        assert!(matches!(
            att.verify(),
            Err(GrainVerifyError::Run(AgentVerifyError::BoundViolated {
                consumed: 5,
                budget: 4
            }))
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: the headroom bound must hold exactly ───────────────────────────
    #[test]
    fn an_inflated_headroom_fails() {
        let (sess, dir) = driven_session([7u8; 32], 20);
        let mut att = GrainAttestation::attest(&sess);
        assert_eq!(att.report.headroom, 15, "20 − 5");

        // Claim MORE could-still-do headroom than the budget allows.
        att.report.headroom = 99;
        assert!(matches!(
            att.verify(),
            Err(GrainVerifyError::HeadroomInconsistent {
                claimed: 99,
                expected: 15
            })
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: the headroom bound HOLDS on the genuine artifact ───────────────
    #[test]
    fn the_headroom_bound_holds() {
        let (sess, dir) = driven_session([8u8; 32], 12);
        let att = GrainAttestation::attest(&sess);
        let v = att.verify().expect("genuine");
        // The bound is exact: consumed + headroom == budget (nothing un-accounted).
        assert_eq!(v.consumed + v.headroom, v.budget, "the bound is airtight");
        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: a valid chain by the WRONG signer is refused when pinned ───────
    #[test]
    fn a_valid_chain_by_the_wrong_signer_is_refused() {
        let (sess, dir) = driven_session([9u8; 32], 20);
        let att = GrainAttestation::attest(&sess);

        // Unpinned verify passes; pinning a DIFFERENT key refuses it.
        att.verify().expect("unpinned genuine chain verifies");
        let wrong = [0xABu8; 32];
        assert!(matches!(
            att.verify_against_signer(&wrong),
            Err(GrainVerifyError::SignerMismatch { .. })
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ═══════════════════════════════════════════════════════════════════════
    // R1 — the renter finality anchor: anti-rewrite + anti-truncation teeth.
    // ═══════════════════════════════════════════════════════════════════════

    const RENTER_SEED: [u8; 32] = [0x5au8; 32];
    const RENTER_NONCE: [u8; 32] = [0x11u8; 32];

    /// Drive goal one only → a genuine SHORTER attestation (2 receipts), then keep
    /// driving goal two → the FULL attestation (5 receipts) over the SAME session.
    /// Both are internally valid; the short one is a real prefix the renter saw.
    fn staged(seed: [u8; 32], budget: i64) -> (Session, std::path::PathBuf) {
        let dir = wd();
        let tk = echo_toolkit(&dir);
        let spec = AgentSpec::new("ignored", budget).with_shell();
        let mut sess = Session::open_seeded(seed, "dga1_renter", spec).unwrap();
        sess.run_goal("goal one", &mut shell_plan(&["a", "b"]), &tk);
        (sess, dir)
    }

    /// The genesis pin the platform would attach for a session, bound to its signer.
    fn genesis_for(att: &GrainAttestation) -> GenesisPin {
        GenesisPin {
            renter_nonce: RENTER_NONCE,
            signer: att.signer(),
        }
    }

    // ── HAPPY PATH: a genuine extension of a countersigned checkpoint verifies ──
    #[test]
    fn r1_a_genuine_extension_of_a_countersigned_checkpoint_verifies() {
        // Renter countersigns EARLY (after goal one, 2 turns); the host then keeps
        // running to 5 turns. The full attestation EXTENDS the acknowledged prefix.
        let (mut sess, dir) = staged([21u8; 32], 40);
        let early = GrainAttestation::attest(&sess);
        let cp = early
            .checkpoint_to_countersign()
            .expect("a 2-turn checkpoint to countersign");
        assert_eq!(cp.num_turns, 2);
        let cs = countersign_checkpoint(RENTER_SEED, cp);
        let renter_pub = cs.renter_pubkey;

        // The host runs more turns; the final attestation carries genesis + the
        // renter's (earlier) countersigned checkpoint.
        let tk = echo_toolkit(&dir);
        sess.run_goal("goal two", &mut shell_plan(&["c", "d", "e"]), &tk);
        let att = GrainAttestation::attest(&sess)
            .with_genesis(genesis_for(&GrainAttestation::attest(&sess)))
            .with_checkpoint(cs);

        // verify() passes (anti-truncation: 5 >= 2; anti-rewrite: receipt[1] hashes
        // to the countersigned head_root).
        let v = att.verify().expect("a genuine extension verifies");
        assert_eq!(v.actions, 5);
        // The full renter/third-party check with both pins.
        att.verify_for_renter(&renter_pub, &RENTER_NONCE)
            .expect("the pinned renter/third-party check passes");

        // Round-trips off the wire with the anchor intact.
        let bytes = serde_json::to_vec(&att).unwrap();
        let att2: GrainAttestation = serde_json::from_slice(&bytes).unwrap();
        att2.verify_for_renter(&renter_pub, &RENTER_NONCE)
            .expect("same verdict off the wire, anchor intact");

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: a TRUNCATED attestation (fewer turns than countersigned) fails ──
    #[test]
    fn r1_a_truncated_attestation_is_rejected() {
        // The renter countersigns the FULL 5-turn tip; the host then shows only the
        // genuine 2-turn prefix — hiding the 3 turns the renter acknowledged.
        let (mut sess, dir) = staged([22u8; 32], 40);
        let two_turn = GrainAttestation::attest(&sess); // genuine, internally valid
        let tk = echo_toolkit(&dir);
        sess.run_goal("goal two", &mut shell_plan(&["c", "d", "e"]), &tk);
        let full = GrainAttestation::attest(&sess);
        let cp = full.checkpoint_to_countersign().unwrap();
        assert_eq!(cp.num_turns, 5);
        let cs = countersign_checkpoint(RENTER_SEED, cp);
        let renter_pub = cs.renter_pubkey;

        // Attach the 5-turn countersigned checkpoint to the 2-turn attestation.
        let truncated = two_turn
            .with_genesis(genesis_for(&full))
            .with_checkpoint(cs);
        assert!(matches!(
            truncated.verify(),
            Err(GrainVerifyError::Truncated {
                acknowledged: 5,
                shown: 2
            })
        ));
        assert!(matches!(
            truncated.verify_for_renter(&renter_pub, &RENTER_NONCE),
            Err(GrainVerifyError::Truncated { .. })
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: a REWRITTEN history (head_root absent from the chain) fails ─────
    #[test]
    fn r1_a_rewritten_history_is_rejected() {
        // The renter countersigns a checkpoint over session A. The host presents a
        // DIFFERENT genuine history (session B) — internally valid, but its receipt
        // at the acknowledged position does NOT hash to A's countersigned head_root.
        let (sess_a, dir_a) = driven_session([23u8; 32], 40);
        let att_a = GrainAttestation::attest(&sess_a);
        let cp_a = att_a.checkpoint_to_countersign().unwrap();
        assert_eq!(cp_a.num_turns, 5);
        let cs_a = countersign_checkpoint(RENTER_SEED, cp_a);

        // B is a DIFFERENT genuine history — different tool-calls, so the receipt
        // CONTENT (and thus the content-only head_root) differs from A's. (A's and
        // B's roots would coincide for identical actions: the head_root commits to
        // WHAT was done, not to the signing key — exactly the anti-rewrite target.)
        let dir_b = wd();
        let tk_b = echo_toolkit(&dir_b);
        let spec_b = AgentSpec::new("ignored", 40).with_shell();
        let mut sess_b = Session::open_seeded([24u8; 32], "dga1_renter", spec_b).unwrap();
        sess_b.run_goal("goal one", &mut shell_plan(&["v", "w"]), &tk_b);
        sess_b.run_goal("goal two", &mut shell_plan(&["x", "y", "z"]), &tk_b);
        let att_b = GrainAttestation::attest(&sess_b);
        // B's chain is genuine and long enough (5 turns), so truncation does NOT
        // bite — only the anti-rewrite tooth does.
        assert_eq!(att_b.report.receipts.len(), 5);
        let rewritten = att_b.with_checkpoint(cs_a);
        assert!(matches!(
            rewritten.verify(),
            Err(GrainVerifyError::Rewritten { position: 5, .. })
        ));

        std::fs::remove_dir_all(&dir_a).ok();
        std::fs::remove_dir_all(&dir_b).ok();
    }

    // ── TOOTH: a forged / absent renter countersignature fails ────────────────
    #[test]
    fn r1_a_forged_or_absent_countersignature_is_rejected() {
        let (sess, dir) = driven_session([25u8; 32], 40);
        let att = GrainAttestation::attest(&sess);
        let cp = att.checkpoint_to_countersign().unwrap();
        let cs = countersign_checkpoint(RENTER_SEED, cp);
        let renter_pub = cs.renter_pubkey;

        // FORGED: flip the renter signature bytes → the countersignature is invalid.
        let mut forged = cs.clone();
        forged.renter_sig[0] ^= 0xff;
        let att_forged = att.clone().with_checkpoint(forged);
        assert!(matches!(
            att_forged.verify(),
            Err(GrainVerifyError::RenterSigInvalid)
        ));

        // ABSENT: a renter who countersigned will not accept an attestation that
        // simply drops the acknowledgement (verify_for_renter REQUIRES it).
        let att_bare = att.clone().with_genesis(genesis_for(&att));
        assert!(matches!(
            att_bare.verify_for_renter(&renter_pub, &RENTER_NONCE),
            Err(GrainVerifyError::MissingCheckpoint)
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: the renter-key + genesis-nonce pins bite a substituted anchor ──
    #[test]
    fn r1_the_renter_and_genesis_pins_bite() {
        let (sess, dir) = driven_session([26u8; 32], 40);
        let att = GrainAttestation::attest(&sess);
        let cp = att.checkpoint_to_countersign().unwrap();
        let cs = countersign_checkpoint(RENTER_SEED, cp);
        let renter_pub = cs.renter_pubkey;
        let full = att
            .clone()
            .with_genesis(genesis_for(&att))
            .with_checkpoint(cs);

        // The genuine pins pass.
        full.verify_for_renter(&renter_pub, &RENTER_NONCE)
            .expect("genuine pins verify");

        // A DIFFERENT renter pubkey (a key the host minted) is refused.
        let host_key = [0x77u8; 32];
        assert!(matches!(
            full.verify_for_renter(&host_key, &RENTER_NONCE),
            Err(GrainVerifyError::RenterKeyMismatch { .. })
        ));

        // A DIFFERENT genesis nonce (a substituted session) is refused.
        let wrong_nonce = [0x99u8; 32];
        assert!(matches!(
            full.verify_for_renter(&renter_pub, &wrong_nonce),
            Err(GrainVerifyError::GenesisNonceMismatch { .. })
        ));

        // A genesis pin naming the WRONG chain signer is refused by verify().
        let mis_genesis = att.clone().with_genesis(GenesisPin {
            renter_nonce: RENTER_NONCE,
            signer: [0x00u8; 32],
        });
        assert!(matches!(
            mis_genesis.verify(),
            Err(GrainVerifyError::GenesisSignerMismatch { .. })
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ═══════════════════════════════════════════════════════════════════════
    // R2 — the kernel-turn tooth: admitted receipts must be views over genuine
    // committed kernel turns. (Driven with the SyntheticMinter: the seam is
    // real; the GENUINE-executor witness lives in the `grain-turn` crate.)
    // ═══════════════════════════════════════════════════════════════════════

    /// Drive a two-goal session THROUGH a minter → the minted artifact + the
    /// committed-turn manifest (the recorded turn hashes).
    fn minted_session(
        seed: [u8; 32],
        budget: i64,
        minter: &mut SyntheticMinter,
    ) -> (Session, std::path::PathBuf) {
        let dir = wd();
        let tk = echo_toolkit(&dir);
        let spec = AgentSpec::new("ignored", budget).with_shell();
        let mut sess = Session::open_seeded(seed, "dga1_renter", spec).unwrap();
        sess.run_goal_minted("goal one", &mut shell_plan(&["a", "b"]), &tk, Some(minter));
        sess.run_goal_minted(
            "goal two",
            &mut shell_plan(&["c", "d", "e"]),
            &tk,
            Some(minter),
        );
        (sess, dir)
    }

    // ── HAPPY PATH: every admitted receipt links to a committed turn ──────────
    #[test]
    fn r2_a_minted_session_links_every_receipt_to_a_committed_turn() {
        let mut minter = SyntheticMinter::new();
        let (sess, dir) = minted_session([61u8; 32], 20, &mut minter);
        let manifest = minter.committed_turns().to_vec();
        assert_eq!(manifest.len(), 5, "one committed turn per admitted action");

        let att = GrainAttestation::attest(&sess);
        let v = att
            .verify_r2(&manifest)
            .expect("every admitted receipt views a committed turn");
        assert_eq!(v.linked, 5, "all five actions are views over kernel turns");
        assert_eq!(v.base.actions, 5);

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: an UNLINKED (None) admitted receipt is rejected ────────────────
    #[test]
    fn r2_an_unlinked_receipt_is_rejected() {
        // A session driven WITHOUT a minter (the default parallel-universe path):
        // every receipt's turn_receipt_hash is None — no action became a kernel
        // turn. The R2 tooth rejects it (even with an empty manifest).
        let (sess, dir) = driven_session([62u8; 32], 20);
        let att = GrainAttestation::attest(&sess);
        assert!(matches!(
            att.verify_r2(&[]),
            Err(GrainVerifyError::R2Unlinked { seq: 0 })
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── TOOTH: a link NOT in the committed-turn manifest is rejected ──────────
    #[test]
    fn r2_a_link_absent_from_the_manifest_is_rejected() {
        // A genuinely-minted session (every receipt carries a real Some link), but
        // the verifier's manifest does NOT vouch for those turns (here: empty). The
        // link names no committed turn → REJECTED as fabricated. (A TAMPERED link is
        // caught even earlier by verify()'s signature check; this catches a
        // self-consistent chain whose turns the manifest does not attest.)
        let mut minter = SyntheticMinter::new();
        let (sess, dir) = minted_session([63u8; 32], 20, &mut minter);
        let att = GrainAttestation::attest(&sess);
        assert!(matches!(
            att.verify_r2(&[]),
            Err(GrainVerifyError::R2FabricatedLink { seq: 0, .. })
        ));
        // ...and a manifest MISSING one turn rejects exactly at that receipt.
        let mut partial = minter.committed_turns().to_vec();
        let dropped = partial.remove(2); // drop the 3rd committed turn
        let _ = dropped;
        match att.verify_r2(&partial) {
            Err(GrainVerifyError::R2FabricatedLink { seq, .. }) => {
                assert_eq!(
                    seq, 2,
                    "the tooth bites at the receipt whose turn is unattested"
                )
            }
            other => panic!("expected R2FabricatedLink at seq 2, got {other:?}"),
        }

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── THE FULL LANDED LADDER (R0+R1+R2) composes in ONE call ────────────────
    #[test]
    fn the_full_ladder_composes_and_every_rung_bites() {
        // A minted session (R2 links) whose checkpoint the renter countersigns (R1).
        let mut minter = SyntheticMinter::new();
        let (sess, dir) = minted_session([64u8; 32], 20, &mut minter);
        let manifest = minter.committed_turns().to_vec();

        let base = GrainAttestation::attest(&sess);
        let cp = base.checkpoint_to_countersign().unwrap();
        let cs = countersign_checkpoint(RENTER_SEED, cp);
        let renter_pub = cs.renter_pubkey;
        let att = base
            .clone()
            .with_genesis(genesis_for(&base))
            .with_checkpoint(cs);

        // POSITIVE: all three pins + the manifest → the whole landed ladder passes.
        let v = att
            .verify_r2_for_renter(&renter_pub, &RENTER_NONCE, &manifest)
            .expect("R0+R1+R2 in one call");
        assert_eq!(v.linked, 5);
        assert_eq!(v.base.actions, 5);

        // R1 tooth still bites inside the composed call: a dropped anchor is refused.
        assert!(matches!(
            base.verify_r2_for_renter(&renter_pub, &RENTER_NONCE, &manifest),
            Err(GrainVerifyError::MissingGenesis)
        ));
        // R2 tooth still bites inside the composed call: an unvouched turn is refused.
        let mut partial = manifest.clone();
        partial.remove(0);
        assert!(matches!(
            att.verify_r2_for_renter(&renter_pub, &RENTER_NONCE, &partial),
            Err(GrainVerifyError::R2FabricatedLink { seq: 0, .. })
        ));
        // R0 tooth still bites: tamper an action, everything above refuses.
        let mut forged = att.clone();
        forged.report.receipts[1].action = "shell:forged".into();
        assert!(matches!(
            forged.verify_r2_for_renter(&renter_pub, &RENTER_NONCE, &manifest),
            Err(GrainVerifyError::Run(_))
        ));

        std::fs::remove_dir_all(&dir).ok();
    }
}
