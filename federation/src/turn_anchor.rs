//! Coordination turns may deliberately have `proof_status: "not_required"`.
//! An authenticated anchor then attests committee agreement only; proof-required
//! consumers must still require and verify a full-turn proof. The policy hint is
//! not part of this signed wire object and cannot grant proof validity.
//!
//! **THE PER-TURN ANCHOR** — the committee-signed statement a stranger obtains so that
//! re-verifying a served full-turn STARK is a check against something, instead of a check
//! against the artifact's own claims.
//!
//! # The hole this closes
//!
//! `dregg_sdk::verify_full_turn_bound` takes `expected_turn_hash` / `expected_old_commit` /
//! `expected_new_commit` FROM THE CALLER. Until this type existed, the only production surface
//! serving proofs to a third party (`GET /api/turn/{hash}/proof`) served
//! `{turn_hash, proof_status, proof_len, proof_hex}` and nothing else, so the discord bot's
//! `/proof turn` read the before/after anchors OUT of the artifact and handed them straight back
//! — the two endpoint `CommitmentMismatch` teeth compared `x != x` and structurally could not
//! fire. The turn hash came from the REQUEST URL, which is better (it is not read out of the
//! artifact) but is still whatever the caller typed at a node that may be lying.
//!
//! A [`TurnAnchorV1`] is a **projection of state the federation already signed**. It invents no
//! new authority: every byte in it is either recomputable by the holder or covered by a
//! signature the committee already produced on the finalized path. It is deliberately NOT a
//! node-signed envelope around values the node computed — that would reproduce the same defect
//! one layer out.
//!
//! # The chain of custody, and exactly how far it reaches
//!
//! ```text
//!   committee member's ed25519 signature
//!     over AttestedRoot::signing_message()          <- `quorum_signatures`
//!        which absorbs `receipt_stream_root`
//!     = merkle_root_of_receipt_hashes([receipt_hash])   (ONE leaf per finalized block:
//!                                                        node/src/blocklace_sync.rs:9685-9695)
//!        which absorbs `receipt_hash`
//!     = TurnReceipt::receipt_hash()  (domain `dregg-receipt-v5`)
//!        which absorbs `turn_hash`, `pre_state_hash`, `post_state_hash`, `effects_hash`, `agent`
//! ```
//!
//! So a valid anchor says: *at least `threshold` distinct members of the committee you named
//! signed a statement that this exact receipt — hence this exact turn hash — is the receipt
//! stream of the finalized block `block_id` at height `height`, whose post-state canonical
//! ledger root is `merkle_root`.*
//!
//! ## ⚑ WHAT THE 8-FELT STATE ANCHORS IN HERE ARE — AND ARE NOT
//!
//! `TurnReceipt::{pre,post}_state_hash` are the AIR-bound chip 8-felt consensus commitment
//! (`dregg_turn::state_commit`, packed by `Faithful8::to_bytes32`), so this anchor DOES carry a
//! committee-signed 8-felt per-turn state commit pair. **It is NOT the pair the full-turn proof
//! publishes**, and it must never be handed to `verify_full_turn_bound` as
//! `expected_old_commit` / `expected_new_commit` — doing so refuses every honest proof.
//!
//! ⚠ **THERE ARE FOUR CAUSES, NOT TWO — corrected 2026-08-07.** This docblock named two, as did
//! every other description of the divergence in the tree. Each is independently sufficient, and
//! all four are measured cause-by-cause in
//! `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`:
//!
//! * **`iroot`.** The receipt anchor pins `state_commit::consensus_ctx`'s
//!   `iroot = rotation_witness::empty_iroot()` deliberately (a receipt cannot bind the
//!   commitment its own hash is computed from). ⚠ The proof side does NOT "fold the real receipt
//!   chain" — that is true of exactly one of four producers, the ledgerless sovereign
//!   `cipherclerk`, whose artifacts this endpoint never serves. The live node path folds a
//!   ONE-ENTRY log: `[receipt.receipt_hash()]` on the non-spend and bearer arms
//!   (`blocklace_sync.rs:9239`, `:9319`), `[turn_hash]` on the cap-less spend arm
//!   (`turn_proving.rs:1298`). Three conventions, three different published commits for one
//!   transition.
//! * **`cells_root`.** The receipt anchor folds the WHOLE ledger
//!   (`state_commit::consensus_ctx` -> `rotation_witness::cells_root(ledger)`); the proof's
//!   witness folds a SINGLE-CELL context ledger holding only the actor
//!   (`node/src/turn_proving.rs::rotation_witness_for_self_sovereign_impl`, `ctx_ledger`).
//! * **`revoked_root`** (unnamed before 2026-08-07). The anchor threads the executor's LIVE
//!   `note_revoked.root8()`; `rotation_witness_for_self_sovereign_impl` writes
//!   `empty_revoked_root_8()` unconditionally and has no parameter for it. Dormant until the
//!   federation's first revocation, permanent after.
//! * **`material`** (unnamed before 2026-08-07). `consensus_ctx` hardcodes
//!   `RotationCarrierMaterial::default()`; the proof carries the installed `child_vk` on a
//!   factory turn's AFTER block. ⚑ This is the one cause that should not be closed by moving the
//!   proving side: `factoryV3Carriers` `.piBinding`s that octet as PI 47..54 precisely to EXPOSE
//!   the installed child VK, so zeroing it on the prover would blank a published surface.
//!   (ⓘ Whether any verifier ANCHORS those PIs is NOT established — `executor/proof_verify.rs`
//!   constructs no `RotationCarrierMaterial`. Do not relay a UNSAT claim about it.)
//!
//! They are two different commitments of the same transition. Aligning them is real work; it is
//! priced in `docs/DESIGN-pi-authority.md` and NOT done here. ⚑ But the price is not what that
//! doc assumed: `trace_rotated::fill_block` copies `cells_root` and `iroot` straight out of the
//! producer witness and (per `EffectVmEmitRotationV3.cellsRootGroupCol`'s own docstring) only
//! createCell/factory/spawn constrain the cells group — so three of the four causes converge by
//! moving the PROVING side, at **no VK rotation, no descriptor re-emit and no re-genesis**,
//! because the signed anchor does not move at all. Only `material` moves it.
//!
//! What this anchor therefore delivers to a proof re-verifier TODAY is the **turn identity**,
//! which every effect-vm leg publishes at `pi::TURN_HASH_BASE` and which
//! `verify_full_turn_bound` compares as a required argument.
//!
//! ## ⚑ THE OTHER TWO ARGUMENTS ARE NOW SERVED TOO — but NOT by this type, and deliberately
//!
//! Since 2026-08-07 `GET /api/turn/{h}/anchor` returns, **beside** `anchor_hex` and outside it, a
//! `proof_state_commits` pair: the 8-felt `(old_commit, new_commit)` the serving node's commit
//! path derived for that turn (`node::turn_proving::turn_proof_anchors_config_key` —
//! `RotationTurnWitness::wide_commit_anchors`, generate-only over the executor's trusted pre-state
//! and the turn's effects, independent of the proof bytes, and gated on by
//! `verify_full_turn_bound` before the artifact was published). That is what a checker now passes
//! as `expected_old_commit` / `expected_new_commit`, so the two `CommitmentMismatch` teeth stop
//! comparing `x != x`.
//!
//! ⚠ **It is NOT part of [`TurnAnchorV1`], and must not be moved into it.** This type's whole
//! contract is that every byte in it is either recomputable by the holder or covered by a
//! signature the committee already produced. The derived pair is neither: it is the NODE's claim.
//! Putting it inside the postcard object would launder a node assertion into the anchor's
//! authority — the same defect one layer out, which is exactly what the type's own docs above
//! refuse. It rides in the JSON with `proof_commit_provenance` naming what it is, and
//! `proof_commit_status: "absent"` (⇒ the checker REFUSES) whenever the node did not mint the
//! artifact — a proof-carrying sovereign turn, or one minted by the ledgerless `sdk::cipherclerk`,
//! which cannot compute this chain's whole-ledger rotation context and therefore has no honest
//! pair to serve.
//!
//! Making the pair committee-signed is the four-cause alignment above. ⚑ And a lane that does it
//! should know, before pricing it, that alignment reaches the **BEFORE** anchor only: the
//! published BEFORE commit is `wire_commit_8_chip` over the before-cell's own limbs (the standing
//! differential `circuit/tests/effect_vm_wide_roundtrip.rs::assert_executor_anchor`), so under a
//! shared context it becomes `receipt.pre_state_hash` exactly. The AFTER commit cannot: the wide
//! generator's `fill_block` OVERRIDES the after block's welded `r0..r10`/`cap_root` from the v1
//! trace's post-effect state (`circuit/src/effect_vm/trace_rotated.rs:2730-2736`), and that state
//! is `VM(pre, effects)` — while `receipt.post_state_hash` commits the EXECUTOR's post-cell, which
//! also carries the phase-1 fee debit and the phase-1 nonce bump
//! (`turn/src/executor/execute.rs:652-674`) that no AIR on the classical commit path models. The
//! VM ticks the nonce once per non-padding ROW (`circuit/src/effect_vm/trace.rs:683-1035`) where
//! the executor bumps once per TURN. So the two post-states coincide only for a fee-free turn with
//! exactly one actor effect that is not `IncrementNonce`. **That is a fifth and sixth cause, of a
//! different kind from the four: they are modelling gaps in the proven transition, not context
//! conventions, and no re-parameterisation of `V9RotationContext` closes them.**
//!
//! ## ⚑ WHAT THE >=THRESHOLD COMMITTEE QUORUM COVERS — AND WHAT CHANGED IN v4
//!
//! Two quorum legs ride an `AttestedRoot`, over two different preimages. **Since the
//! finalization-vote domain moved v3 → v4, BOTH reach the receipt:**
//!
//! | leg | preimage | reaches the turn? | who signs it |
//! |---|---|---|---|
//! | `quorum_signatures` (ed25519) | [`AttestedRoot::signing_message`] — absorbs `receipt_stream_root` | **yes** | the LOCAL node only (one push) |
//! | `hybrid_quorum` (ed25519 ∧ ML-DSA-65) | [`AttestedRoot::hybrid_quorum_message`] = `domain-v4 ‖ block_id ‖ merkle_root ‖ framed(receipt_stream_root)` | **yes (v4)** | the assembled CROSS-NODE committee quorum |
//!
//! [`TurnAnchorV1::verify`] counts the UNION of distinct committee members across the two legs,
//! each verified against its own preimage. That is sound because both preimages bind the SAME
//! `(block_id, merkle_root, receipt_stream_root)` of the SAME root: a signer counted from either
//! leg really did sign a statement naming this receipt stream at this chain position.
//!
//! ⚑ **THE HISTORY THIS FIXES, because the refusal it produced was correct and load-bearing.**
//! Through v3 the vote preimage was `(block_id, merkle_root)` only — no per-turn value — and
//! `quorum_signatures` receives exactly one push, the local node's, because
//! `PeerMessage::AttestedRootUpdate` has zero handlers. So on any federation with `threshold > 1`
//! this anchor REFUSED, honestly, rather than reporting a caveat: no committee signature in the
//! tree covered a per-turn value. v4 does not relax that gate. It supplies the missing quorum:
//! the votes the committee already exchanges now bind `receipt_stream_root`, so
//! `>= threshold` distinct members genuinely sign a statement that reaches this turn. A
//! federation that has NOT yet assembled its vote quorum still refuses, and a sub-threshold one
//! still refuses — see `federation/tests/turn_anchor_refusals.rs`.
//!
//! The Lean side moved with it: `Dregg2.Distributed.FinalizationQuorum.quorum_binds_snd` and
//! `FinalityGate.quorum_gate_binds_receipt_stream` are the named theorems that a quorum on the
//! widened pair IS a supermajority of distinct signers agreeing on the receipt-stream component.
//!
//! # The roster is the caller's, never the anchor's
//!
//! [`TurnAnchorV1::verify`] takes the committee it should judge against as an ARGUMENT. The
//! anchor carries a roster only as a convenience for a caller with no configured one, and using
//! it means trusting the server that served the anchor — [`TurnAnchorV1::served_committee`] is
//! named so that call sites cannot pretend otherwise.

use serde::{Deserialize, Serialize};

use dregg_turn::TurnReceipt;
use dregg_types::{AttestedRoot, FederationId, PublicKey, merkle_root_of_receipt_hashes};

use crate::frost::MlDsaPublicKey;
use crate::receipt::verify_hybrid_quorum_sigs;

/// Wire protocol tag. A decoder that does not recognise it REFUSES rather than guessing.
pub const TURN_ANCHOR_PROTOCOL_V1: &str = "DTA1";

/// The committee an anchor is judged against: ed25519 identities, the index-aligned enrolled
/// ML-DSA-65 roster, and the threshold. This is the caller's trust root, supplied out of band
/// (genesis / operator config) — never read out of the anchor being checked.
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct AnchorCommittee {
    /// The committee's ed25519 identities.
    pub ed25519: Vec<PublicKey>,
    /// The genesis-enrolled ML-DSA-65 roster, aligned index-for-index with `ed25519`. May be
    /// empty; the hybrid position leg is then skipped rather than downgraded to ed25519-only.
    pub ml_dsa: Vec<Vec<u8>>,
    /// Signatures required for a quorum. Zero is not an authority.
    pub threshold: usize,
    /// The federation this roster belongs to. An anchor attested by a different federation is
    /// refused — a roster is only a trust root for its own federation.
    pub federation_id: FederationId,
}

/// **The per-turn anchor.** Everything a stranger needs to convince themselves, from a committee
/// roster they already trust, that a given turn hash is the turn the federation finalized at a
/// given chain position.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnAnchorV1 {
    /// [`TURN_ANCHOR_PROTOCOL_V1`]. Refused when unrecognised.
    pub protocol: String,
    /// The turn this anchor is for. Redundant with `receipt.turn_hash` ON PURPOSE: the two are
    /// compared, so a receipt served under the wrong turn's anchor is a named refusal rather
    /// than a silent substitution.
    pub turn_hash: [u8; 32],
    /// The canonical receipt, whole, so the holder recomputes `receipt_hash()` itself instead of
    /// being told it. This is the object the attestation's `receipt_stream_root` roots.
    pub receipt: TurnReceipt,
    /// The attested-root height this turn committed at.
    pub height: u64,
    /// The blocklace block that carried it.
    pub block_id: [u8; 32],
    /// The committee-signed attestation at `height`, carrying BOTH quorum legs.
    pub attested: AttestedRoot,
    /// The roster the SERVER claims. Present only so a caller with no configured committee can
    /// proceed knowingly; see [`TurnAnchorV1::served_committee`].
    pub served_committee: AnchorCommittee,
}

/// Why an anchor was refused. Every arm is a distinct, nameable failure — an anchor never fails
/// "generically", because the whole point is that a holder can say what did not hold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TurnAnchorError {
    /// The `protocol` tag is not [`TURN_ANCHOR_PROTOCOL_V1`].
    UnknownProtocol(String),
    /// The caller supplied no committee (empty roster, or `threshold == 0`). A vacuous quorum is
    /// not an authority.
    NoCommittee { members: usize, threshold: usize },
    /// The attestation was produced by a different federation than the roster belongs to.
    FederationMismatch {
        anchor: FederationId,
        committee: FederationId,
    },
    /// The carried receipt is for a different turn than the anchor claims.
    ReceiptIsForAnotherTurn { anchor: [u8; 32], receipt: [u8; 32] },
    /// The attestation is not at the height/block the anchor claims.
    ChainPositionMismatch {
        anchor_height: u64,
        attested_height: u64,
        anchor_block: [u8; 32],
        attested_block: Option<[u8; 32]>,
    },
    /// The attestation carries no `receipt_stream_root` at all (a legacy v3 root). There is
    /// nothing binding a receipt to it, so it cannot anchor a turn.
    AttestationBindsNoReceiptStream,
    /// The receipt does not hash into the attestation's `receipt_stream_root`.
    ReceiptNotInAttestedStream {
        receipt_hash: [u8; 32],
        recomputed_stream_root: [u8; 32],
        attested_stream_root: [u8; 32],
    },
    /// Fewer than `threshold` DISTINCT committee members signed a preimage that reaches the
    /// receipt, counting the union of both legs. This is the refusal that separates "the
    /// committee said so" from "the node said so" — see the module docs.
    ///
    /// `attestation_signers` is the `quorum_signatures` (attested-root preimage) leg and
    /// `vote_signers` the `hybrid_quorum` (finalization-vote preimage) leg; `signers` is the
    /// size of their UNION, which is what the threshold is measured against. Reporting the two
    /// separately is what lets a holder say *why* — "the node signed but the committee has not
    /// assembled its vote quorum yet" is a different situation from "nobody signed".
    ReceiptQuorumNotMet {
        signers: usize,
        attestation_signers: usize,
        vote_signers: usize,
        threshold: usize,
    },
}

impl std::fmt::Display for TurnAnchorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownProtocol(p) => write!(
                f,
                "unknown turn-anchor protocol `{p}` (expected `{TURN_ANCHOR_PROTOCOL_V1}`)"
            ),
            Self::NoCommittee { members, threshold } => write!(
                f,
                "no committee to judge against: {members} members, threshold {threshold}"
            ),
            Self::FederationMismatch { anchor, committee } => write!(
                f,
                "the attestation is federation {} but the roster is for {}",
                hex::encode(anchor.0),
                hex::encode(committee.0)
            ),
            Self::ReceiptIsForAnotherTurn { anchor, receipt } => write!(
                f,
                "the anchor claims turn {} but carries the receipt of turn {}",
                hex::encode(anchor),
                hex::encode(receipt)
            ),
            Self::ChainPositionMismatch {
                anchor_height,
                attested_height,
                anchor_block,
                attested_block,
            } => write!(
                f,
                "the anchor claims height {anchor_height} block {} but the attestation is height \
                 {attested_height} block {}",
                hex::encode(anchor_block),
                attested_block.map(hex::encode).unwrap_or("none".into())
            ),
            Self::AttestationBindsNoReceiptStream => write!(
                f,
                "the attestation carries no receipt_stream_root, so no signature over it reaches \
                 any receipt"
            ),
            Self::ReceiptNotInAttestedStream {
                receipt_hash,
                recomputed_stream_root,
                attested_stream_root,
            } => write!(
                f,
                "receipt {} roots to {} but the attestation binds {}",
                hex::encode(receipt_hash),
                hex::encode(recomputed_stream_root),
                hex::encode(attested_stream_root)
            ),
            Self::ReceiptQuorumNotMet {
                signers,
                attestation_signers,
                vote_signers,
                threshold,
            } => write!(
                f,
                "only {signers} distinct committee signature(s) cover this receipt \
                 ({attestation_signers} over the attested-root preimage, {vote_signers} over the \
                 v4 finalization-vote preimage); {threshold} required. On the live path the \
                 attested-root leg receives only the local node's signature, so a federation \
                 with threshold > 1 is anchored by the committee's assembled VOTE quorum — \
                 which is absent or short here"
            ),
        }
    }
}

impl std::error::Error for TurnAnchorError {}

/// What a verified anchor establishes. Constructed ONLY by [`TurnAnchorV1::verify`], so holding
/// one is evidence the checks ran.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedTurnAnchor {
    /// **The value to hand `verify_full_turn_bound` as `expected_turn_hash`.** It came out of a
    /// committee-signed receipt, not out of any artifact and not out of a URL.
    pub turn_hash: [u8; 32],
    /// The receipt hash this holder RECOMPUTED (never the served claim).
    pub receipt_hash: [u8; 32],
    /// The finalized height and block.
    pub height: u64,
    pub block_id: [u8; 32],
    /// The post-state canonical ledger root (BLAKE3 whole-image) the attestation binds.
    pub ledger_root: [u8; 32],
    /// The committee-signed 8-felt consensus state commits from the receipt.
    ///
    /// ⚠ **NOT the full-turn proof's published anchors** — see the module docs. Report them,
    /// never pass them to `verify_full_turn_bound`.
    pub receipt_pre_state_commit: [u8; 32],
    pub receipt_post_state_commit: [u8; 32],
    /// Distinct committee members whose signature covers the RECEIPT, counting the UNION of
    /// both legs: `quorum_signatures` over `AttestedRoot::signing_message` and `hybrid_quorum`
    /// over the v4 `AttestedRoot::hybrid_quorum_message`. `>= threshold`, or `verify` would
    /// have refused.
    pub receipt_quorum_signers: usize,
    /// Did a `>= threshold` HYBRID (ed25519 ∧ ML-DSA-65, enrolled-key pinned) committee quorum
    /// sign the v4 finalization-vote preimage — `(block_id, merkle_root, receipt_stream_root)`
    /// — on its own? Decided per signer by the ONE shared rule,
    /// [`crate::receipt::verify_hybrid_quorum_sigs`].
    ///
    /// ⚑ Since v4 this leg DOES reach the receipt, and its signers are counted toward
    /// [`receipt_quorum_signers`](Self::receipt_quorum_signers). It stays a separate reported
    /// field because it is the leg a real multi-node committee assembles, and a holder wants to
    /// know whether acceptance rested on the committee's cross-node quorum or on a single-node
    /// federation's own attestation signature.
    pub position_quorum_met: bool,
    /// The threshold the roster declared.
    pub threshold: usize,
}

impl TurnAnchorV1 {
    /// **Verify this anchor against a committee the CALLER trusts.**
    ///
    /// Every step is recomputation or signature checking; nothing is taken on the server's word.
    /// Acceptance requires `>= threshold` distinct committee signatures over the preimage that
    /// reaches the receipt — see the module docs for why the hybrid vote quorum cannot substitute.
    pub fn verify(
        &self,
        committee: &AnchorCommittee,
    ) -> Result<VerifiedTurnAnchor, TurnAnchorError> {
        if self.protocol != TURN_ANCHOR_PROTOCOL_V1 {
            return Err(TurnAnchorError::UnknownProtocol(self.protocol.clone()));
        }
        if committee.ed25519.is_empty() || committee.threshold == 0 {
            return Err(TurnAnchorError::NoCommittee {
                members: committee.ed25519.len(),
                threshold: committee.threshold,
            });
        }
        if self.attested.federation_id != committee.federation_id {
            return Err(TurnAnchorError::FederationMismatch {
                anchor: self.attested.federation_id,
                committee: committee.federation_id,
            });
        }
        // The receipt must be THIS turn's. Checked before anything derived from it, so a
        // substituted receipt is named rather than surfacing as a stream mismatch.
        if self.receipt.turn_hash != self.turn_hash {
            return Err(TurnAnchorError::ReceiptIsForAnotherTurn {
                anchor: self.turn_hash,
                receipt: self.receipt.turn_hash,
            });
        }
        if self.attested.height != self.height
            || self.attested.blocklace_block_id != Some(self.block_id)
        {
            return Err(TurnAnchorError::ChainPositionMismatch {
                anchor_height: self.height,
                attested_height: self.attested.height,
                anchor_block: self.block_id,
                attested_block: self.attested.blocklace_block_id,
            });
        }

        // RECOMPUTE the receipt hash and the singleton stream root; never read either.
        let receipt_hash = self.receipt.receipt_hash();
        let recomputed = merkle_root_of_receipt_hashes(&[receipt_hash]);
        let Some(attested_stream_root) = self.attested.receipt_stream_root else {
            return Err(TurnAnchorError::AttestationBindsNoReceiptStream);
        };
        if recomputed != attested_stream_root {
            return Err(TurnAnchorError::ReceiptNotInAttestedStream {
                receipt_hash,
                recomputed_stream_root: recomputed,
                attested_stream_root,
            });
        }

        // LEG 1: committee signatures over `AttestedRoot::signing_message()`, which absorbs
        // `receipt_stream_root`. On the live path this leg receives exactly one push — the
        // local node's — so on a real federation it is the SMALLER of the two.
        let attestation_message = self.attested.signing_message();
        let mut receipt_signers: std::collections::HashSet<[u8; 32]> = Default::default();
        for (pk, sig) in &self.attested.quorum_signatures {
            if committee.ed25519.contains(pk) && pk.verify(&attestation_message, sig) {
                receipt_signers.insert(pk.0);
            }
        }
        let attestation_signers = receipt_signers.len();

        // LEG 2: the HYBRID (ed25519 ∧ ML-DSA-65, enrolled-key pinned) committee vote quorum,
        // over `AttestedRoot::hybrid_quorum_message()`. Since the vote domain moved to v4 that
        // preimage absorbs `receipt_stream_root`, so THIS leg reaches the receipt too — and it
        // is the leg a real committee actually assembles. Its signers join the same union.
        let vote_signers = self.vote_quorum_signers(committee);
        let position_quorum_met = vote_signers.len() >= committee.threshold;
        let vote_signer_count = vote_signers.len();
        receipt_signers.extend(vote_signers);

        // THE GATE: `>= threshold` DISTINCT committee members, each having signed SOME preimage
        // that names this receipt stream at this chain position.
        if receipt_signers.len() < committee.threshold {
            return Err(TurnAnchorError::ReceiptQuorumNotMet {
                signers: receipt_signers.len(),
                attestation_signers,
                vote_signers: vote_signer_count,
                threshold: committee.threshold,
            });
        }

        Ok(VerifiedTurnAnchor {
            turn_hash: self.turn_hash,
            receipt_hash,
            height: self.height,
            block_id: self.block_id,
            ledger_root: self.attested.merkle_root,
            receipt_pre_state_commit: self.receipt.pre_state_hash,
            receipt_post_state_commit: self.receipt.post_state_hash,
            receipt_quorum_signers: receipt_signers.len(),
            position_quorum_met,
            threshold: committee.threshold,
        })
    }

    /// The DISTINCT committee members whose HYBRID (ed25519 ∧ ML-DSA-65, enrolled-key pinned)
    /// signature over [`AttestedRoot::hybrid_quorum_message`] verifies — the v4
    /// finalization-vote preimage, which absorbs `receipt_stream_root` and therefore reaches
    /// this turn.
    ///
    /// The `classical ∧ pq` rule itself is [`crate::receipt::verify_hybrid_quorum_sigs`] — the
    /// ONE place it lives, applied by the restart anchor and the cross-fed verifier too — so
    /// this can never drift from it. This function calls that rule at threshold 1 PER SIGNER so
    /// it can report a COUNT rather than a boolean (the anchor's gate is a union across two
    /// legs, so it needs who, not whether). Fail-closed on a misaligned or empty enrolled
    /// ML-DSA roster (that rule refuses rather than downgrading to ed25519-only), on an
    /// undecodable enrolled key, and on a root with no blocklace anchor (no vote preimage).
    fn vote_quorum_signers(&self, committee: &AnchorCommittee) -> Vec<[u8; 32]> {
        let Some(vote_message) = self.attested.hybrid_quorum_message() else {
            return Vec::new();
        };
        let enrolled: Vec<MlDsaPublicKey> = committee
            .ml_dsa
            .iter()
            .filter_map(|k| <[u8; dregg_pq::ML_DSA_PK_LEN]>::try_from(k.as_slice()).ok())
            .map(MlDsaPublicKey)
            .collect();
        // A key that did not decode drops out above, which shortens the roster and makes
        // `verify_hybrid_quorum_sigs`'s length-alignment guard refuse every signer.
        let mut signers: Vec<[u8; 32]> = Vec::new();
        for qs in &self.attested.hybrid_quorum {
            if signers.contains(&qs.pubkey.0) {
                continue;
            }
            // One-signer slice through the SHARED rule: membership, both halves, and the
            // enrolled-key pin are all decided there, never re-implemented here.
            if verify_hybrid_quorum_sigs(
                std::slice::from_ref(qs),
                &vote_message,
                &committee.ed25519,
                &enrolled,
                1,
            ) {
                signers.push(qs.pubkey.0);
            }
        }
        signers
    }

    /// The roster the SERVER claims, for a caller that has none configured.
    ///
    /// ⚠ Verifying against this is verifying against the server: it can name any committee it
    /// likes, including one it wholly controls. The method is named for what it is so no call
    /// site can present the result as committee-verified without saying where the roster came
    /// from. Prefer a roster from genesis or operator config.
    pub fn served_committee(&self) -> &AnchorCommittee {
        &self.served_committee
    }
}
