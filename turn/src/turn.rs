//! Turn: the full atomic transaction unit.
//!
//! A Turn wraps a CallForest with metadata: who initiated it, replay protection
//! via nonce, fee payment, and optional memo/expiration.

use std::collections::HashMap;

use pyana_cell::state::FieldElement;
use pyana_cell::{Cell, CellId, DerivationRecord, LedgerDelta};
use serde::{Deserialize, Serialize};

use crate::action::Symbol;
use crate::error::TurnError;
use crate::forest::CallForest;
use crate::routing::{IntroductionExport, RoutingDirective};

/// Serde helper for `[u8; 64]` (Ed25519 signatures).
mod sw_sig_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        bytes.as_slice().serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Vec::deserialize(de)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

/// Witness data for a sovereign cell in a turn.
///
/// When a turn targets a sovereign cell the federation has stored only a
/// 32-byte state commitment for, the submitter must supply enough material
/// for the executor to (1) reconstruct the cell so per-cell execution can
/// proceed and (2) authenticate the transition as coming from the cell's
/// owning key. The shape mirrors
/// [`pyana_cell::peer_exchange::PeerStateTransition`] one-shot: the cell key
/// signs over `(cell_id, old_commitment, new_commitment, effects_hash,
/// timestamp, sequence)` and an optional STARK proof carries the same
/// transition through `EffectVmAir`.
///
/// The executor verifies:
///
///  1. `cell_id == cell_state.id()` and `old_commitment ==
///     cell_state.state_commitment() == ledger's stored sovereign
///     commitment for cell_id` (anchors the pre-state).
///  2. Ed25519 `signature` over the canonical signing message verifies
///     against `cell_state.public_key()` (binds the transition to the
///     cell's owning key — closes the "any-snooper-can-resubmit" gap).
///  3. `sequence == ledger.last_sovereign_witness_sequence(cell_id) + 1`
///     (per-cell monotonic, no gaps; closes the replay gap even if a
///     future hypothetical commitment collision were ever found).
///  4. If `transition_proof` is `Some`, the STARK is verified via
///     `EffectVmAir` with PIs binding `old_commitment -> new_commitment +
///     effects_hash + cell_id`.
///
/// The `new_commitment` and `effects_hash` declared here are treated as
/// the signer's promise about the post-state; the executor still
/// recomputes both during forest execution. Mismatches surface as
/// `TurnError::EffectsHashMismatch` / `SovereignCommitmentMismatch`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SovereignCellWitness {
    /// The cell ID this witness opens. Must equal `cell_state.id()`.
    pub cell_id: CellId,
    /// The federation's stored pre-state commitment for this cell.
    pub old_commitment: [u8; 32],
    /// The claimed post-state commitment after the witnessed transition.
    pub new_commitment: [u8; 32],
    /// BLAKE3 hash of the effects applied to this cell in the turn.
    pub effects_hash: [u8; 32],
    /// Timestamp the witness was issued at (informational; bound by signature).
    pub timestamp: i64,
    /// Per-cell monotonic counter. Replay protection: must be
    /// `ledger.last_sovereign_witness_sequence(cell_id) + 1`.
    pub sequence: u64,
    /// Ed25519 signature over the canonical signing message produced by
    /// [`SovereignCellWitness::signing_message`], verified against
    /// `cell_state.public_key()`.
    #[serde(with = "sw_sig_serde")]
    pub signature: [u8; 64],
    /// The full cell pre-state (agent-supplied; commitment must match
    /// `old_commitment`).
    pub cell_state: Cell,
    /// Optional STARK proof binding old -> new + effects_hash via
    /// `EffectVmAir`. When present, the executor may verify in lieu of
    /// re-executing — see `PeerStateTransition` for the analogous path.
    #[serde(default)]
    pub transition_proof: Option<Vec<u8>>,
}

impl SovereignCellWitness {
    /// Canonical signing message layout:
    ///   "pyana-sovereign-witness-v1:" ||
    ///   cell_id || old_commitment || new_commitment || effects_hash ||
    ///   timestamp (8 LE) || sequence (8 LE)
    pub fn signing_message(
        cell_id: &CellId,
        old_commitment: &[u8; 32],
        new_commitment: &[u8; 32],
        effects_hash: &[u8; 32],
        timestamp: i64,
        sequence: u64,
    ) -> Vec<u8> {
        const DOMAIN: &[u8] = b"pyana-sovereign-witness-v1:";
        let mut msg = Vec::with_capacity(DOMAIN.len() + 32 + 32 + 32 + 32 + 8 + 8);
        msg.extend_from_slice(DOMAIN);
        msg.extend_from_slice(cell_id.as_bytes());
        msg.extend_from_slice(old_commitment);
        msg.extend_from_slice(new_commitment);
        msg.extend_from_slice(effects_hash);
        msg.extend_from_slice(&timestamp.to_le_bytes());
        msg.extend_from_slice(&sequence.to_le_bytes());
        msg
    }
}

/// An event emitted during turn execution, recorded in the receipt for audit/indexing.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EmittedEvent {
    /// The cell that emitted this event.
    pub cell: CellId,
    /// The topic of this event (hashed method/event name).
    pub topic: Symbol,
    /// Arbitrary data fields.
    pub data: Vec<FieldElement>,
}

/// A custom program proof for CellProgram dispatch within the Effect VM.
///
/// When a sovereign cell has a deployed custom program (e.g., a CDP circuit),
/// and the Effect VM turn includes a Custom effect row, the agent provides
/// this proof alongside the Effect VM proof. The executor:
/// 1. Verifies the Effect VM proof (state transition + conservation)
/// 2. Checks that hash(proof_bytes) == proof_commitment from Effect VM PI
/// 3. Verifies proof_bytes against the custom program identified by vk_hash
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CustomProgramProof {
    /// The serialized proof bytes for the custom program.
    pub proof_bytes: Vec<u8>,
    /// Public inputs for the custom program proof (raw u32 BabyBear values).
    pub public_inputs: Vec<u32>,
}

impl CustomProgramProof {
    /// Convert raw public inputs to BabyBear elements for verification.
    pub fn public_inputs_babybear(&self) -> Vec<pyana_circuit::field::BabyBear> {
        self.public_inputs
            .iter()
            .map(|&v| pyana_circuit::field::BabyBear::new(v))
            .collect()
    }
}

/// A Turn is the atomic unit of agent execution.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Turn {
    pub agent: CellId,
    pub nonce: u64,
    pub call_forest: CallForest,
    pub fee: u64,
    pub memo: Option<String>,
    pub valid_until: Option<i64>,
    #[serde(default)]
    pub previous_receipt_hash: Option<[u8; 32]>,
    /// Hashes of turns this turn depends on (for pipeline/eventual-send semantics).
    #[serde(default)]
    pub depends_on: Vec<[u8; 32]>,
    /// Schnorr conservation proof (serialized `ConservationProof`) for the committed
    /// value path. Required when all notes in the turn use Pedersen value commitments.
    /// The proof demonstrates that `sum(input_commitments) - sum(output_commitments)`
    /// is a commitment to zero (values balance without revealing amounts).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub conservation_proof: Option<Vec<u8>>,
    /// Witnesses for sovereign cells targeted by this turn.
    ///
    /// When a turn's call forest targets a sovereign cell, the agent must provide
    /// the full cell state here. The executor verifies that
    /// `witness.state_proof == witness.cell_state.state_commitment()` and that this
    /// matches the stored commitment in the ledger.
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub sovereign_witnesses: HashMap<CellId, SovereignCellWitness>,
    /// Execution proof for proof-carrying sovereign turns (Phase 3).
    ///
    /// When present, the executor bypasses all state manipulation and instead:
    /// 1. Verifies the STARK proof (binding old_commitment -> new_commitment + effects_hash)
    /// 2. Updates the sovereign cell's commitment directly
    ///
    /// This makes sovereign cell transitions O(1) regardless of internal complexity.
    /// The proof's public inputs layout:
    ///   [old_commitment_bb[0..8], new_commitment_bb[0..8], effects_hash_bb[0..8], cell_id_hash_bb[0..8]]
    /// where each 32-byte value is encoded as 8 BabyBear elements (4 bytes each, LE).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub execution_proof: Option<Vec<u8>>,
    /// The target cell ID for proof-carrying turns. Required when `execution_proof` is Some.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub execution_proof_cell: Option<CellId>,
    /// The new commitment claimed by the execution proof.
    /// The proof's public inputs must include this value. After verification, the
    /// ledger's sovereign commitment is updated to this value.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub execution_proof_new_commitment: Option<[u8; 32]>,
    /// Custom program proofs for CellProgram dispatch.
    ///
    /// When the Effect VM proof contains Custom effect rows, each custom effect
    /// references an external proof via its `proof_commitment`. The actual proofs
    /// are provided here, in the same order as they appear in the effect sequence.
    ///
    /// Verification flow:
    /// 1. Effect VM proof is verified (standard state transition + conservation)
    /// 2. For each custom proof entry:
    ///    - hash(proof_bytes) must match the proof_commitment in the PI
    ///    - The program identified by vk_hash must verify the proof
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub custom_program_proofs: Option<Vec<CustomProgramProof>>,
}

impl Turn {
    // Stage 7-α (R-2 closure / EFFECT-VM-SHAPE-A.md §Receipts): the v3 domain
    // tag covers every semantically load-bearing field on `Turn`, including
    // the execution-proof bundle (`execution_proof`,
    // `execution_proof_cell`, `execution_proof_new_commitment`),
    // `sovereign_witnesses`, `conservation_proof`, and
    // `custom_program_proofs`. The v2 form excluded those, so an attacker
    // with write-access to an in-flight `SignedTurn` could swap any of
    // them without invalidating the signature (the "proof-swap attack").
    //
    // Note for callers: this hash is a content-addressed identifier for
    // the entire `Turn` object. The wallet still signs over its own
    // `compute_turn_bytes` (sdk/src/wallet.rs) which deliberately covers
    // only the fields a wallet sees at sign time; `Turn::hash` is what
    // the executor, receipt chain, and (post-Stage 7-γ.0) the per-cell
    // proof bundle agree on after the fact. Wallet signature compatibility
    // is therefore preserved by this bump.
    pub fn hash(&self) -> [u8; 32] {
        let forest_hash = self.call_forest.compute_hash();
        let mut hasher = blake3::Hasher::new();
        // Domain separation: prevents type confusion with other hash preimages.
        hasher.update(b"pyana-turn-v3:");
        hasher.update(self.agent.as_bytes());
        hasher.update(&self.nonce.to_le_bytes());
        hasher.update(&forest_hash);
        hasher.update(&self.fee.to_le_bytes());
        // Length-prefix the optional memo so the boundary cannot be confused
        // with subsequent fields.
        match &self.memo {
            Some(memo) => {
                hasher.update(&[1u8]);
                let memo_bytes = memo.as_bytes();
                hasher.update(&(memo_bytes.len() as u64).to_le_bytes());
                hasher.update(memo_bytes);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        match self.valid_until {
            Some(valid_until) => {
                hasher.update(&[1u8]);
                hasher.update(&valid_until.to_le_bytes());
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        // Include depends_on to prevent dependency malleability.
        hasher.update(&(self.depends_on.len() as u64).to_le_bytes());
        for dep in &self.depends_on {
            hasher.update(dep);
        }
        // Include previous_receipt_hash to bind to causal ordering.
        match &self.previous_receipt_hash {
            Some(h) => {
                hasher.update(&[1u8]);
                hasher.update(h);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        // --- v3 additions: execution-proof + witness bundle ---
        // execution_proof: opaque proof bytes; hash with presence tag and
        // length prefix so a swap to a different-length proof is caught.
        match &self.execution_proof {
            Some(bytes) => {
                hasher.update(&[1u8]);
                hasher.update(&(bytes.len() as u64).to_le_bytes());
                hasher.update(bytes);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        // execution_proof_cell: which sovereign cell the proof binds.
        match &self.execution_proof_cell {
            Some(cell) => {
                hasher.update(&[1u8]);
                hasher.update(cell.as_bytes());
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        // execution_proof_new_commitment: post-state commitment claimed.
        match &self.execution_proof_new_commitment {
            Some(commit) => {
                hasher.update(&[1u8]);
                hasher.update(commit);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        // conservation_proof: serialized Schnorr proof bytes.
        match &self.conservation_proof {
            Some(bytes) => {
                hasher.update(&[1u8]);
                hasher.update(&(bytes.len() as u64).to_le_bytes());
                hasher.update(bytes);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        // sovereign_witnesses: map of (CellId -> SovereignCellWitness).
        // Sort entries by cell ID for canonical ordering. Bind every
        // soundness-load-bearing field: the (old, new, effects_hash,
        // timestamp, sequence) signing message inputs plus the
        // signature and the cell_state commitment. The transition_proof
        // (if any) is length-prefixed.
        let mut sw_entries: Vec<(&CellId, &SovereignCellWitness)> =
            self.sovereign_witnesses.iter().collect();
        sw_entries.sort_by_key(|(cell, _)| *cell.as_bytes());
        hasher.update(&(sw_entries.len() as u64).to_le_bytes());
        for (cell, witness) in sw_entries {
            hasher.update(cell.as_bytes());
            hasher.update(witness.cell_id.as_bytes());
            hasher.update(&witness.old_commitment);
            hasher.update(&witness.new_commitment);
            hasher.update(&witness.effects_hash);
            hasher.update(&witness.timestamp.to_le_bytes());
            hasher.update(&witness.sequence.to_le_bytes());
            hasher.update(&witness.signature);
            hasher.update(&witness.cell_state.state_commitment());
            match &witness.transition_proof {
                Some(bytes) => {
                    hasher.update(&[1u8]);
                    hasher.update(&(bytes.len() as u64).to_le_bytes());
                    hasher.update(bytes);
                }
                None => {
                    hasher.update(&[0u8]);
                }
            };
        }
        // custom_program_proofs: ordered Vec; bind each proof's bytes and
        // its public-inputs vector.
        match &self.custom_program_proofs {
            Some(proofs) => {
                hasher.update(&[1u8]);
                hasher.update(&(proofs.len() as u64).to_le_bytes());
                for proof in proofs {
                    hasher.update(&(proof.proof_bytes.len() as u64).to_le_bytes());
                    hasher.update(&proof.proof_bytes);
                    hasher.update(&(proof.public_inputs.len() as u64).to_le_bytes());
                    for pi in &proof.public_inputs {
                        hasher.update(&pi.to_le_bytes());
                    }
                }
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        *hasher.finalize().as_bytes()
    }

    pub fn action_count(&self) -> usize {
        self.call_forest.action_count()
    }
}

/// The result of applying a turn to a ledger.
#[derive(Clone, Debug)]
pub enum TurnResult {
    Committed {
        ledger_delta: LedgerDelta,
        receipt: TurnReceipt,
        computrons_used: u64,
    },
    Rejected {
        reason: TurnError,
        at_action: Vec<usize>,
    },
    /// The conditional turn's timeout height has been exceeded.
    /// No state change occurs and no fee is charged.
    Expired,
    /// The conditional turn's condition has not yet been satisfied.
    /// The turn remains in the pending pool.
    Pending,
}

impl TurnResult {
    pub fn is_committed(&self) -> bool {
        matches!(self, TurnResult::Committed { .. })
    }
    pub fn is_rejected(&self) -> bool {
        matches!(self, TurnResult::Rejected { .. })
    }
    pub fn is_expired(&self) -> bool {
        matches!(self, TurnResult::Expired)
    }
    pub fn is_pending(&self) -> bool {
        matches!(self, TurnResult::Pending)
    }

    pub fn unwrap_committed(self) -> (LedgerDelta, TurnReceipt, u64) {
        match self {
            TurnResult::Committed {
                ledger_delta,
                receipt,
                computrons_used,
            } => (ledger_delta, receipt, computrons_used),
            TurnResult::Rejected { reason, at_action } => {
                panic!("turn was rejected at {:?}: {}", at_action, reason)
            }
            TurnResult::Expired => panic!("turn was expired, expected committed"),
            TurnResult::Pending => panic!("turn is pending, expected committed"),
        }
    }

    pub fn unwrap_rejected(self) -> (TurnError, Vec<usize>) {
        match self {
            TurnResult::Rejected { reason, at_action } => (reason, at_action),
            TurnResult::Committed { .. } => panic!("turn was committed, expected rejection"),
            TurnResult::Expired => panic!("turn was expired, expected rejection"),
            TurnResult::Pending => panic!("turn is pending, expected rejection"),
        }
    }
}

/// The finality status of a committed turn receipt.
///
/// In full BFT mode, all receipts are `Final` (backed by quorum certificate).
/// In solo mode, receipts for consensus-path turns are `Tentative` until
/// peer nodes rejoin and validate them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Finality {
    /// Fully finalized by BFT quorum (or fast-path certificate with quorum signatures).
    Final,
    /// Processed by a single node in solo mode, awaiting quorum validation on rejoin.
    /// Safe under the assumption of no Byzantine adversaries (devnet, single-operator).
    Tentative,
}

impl Default for Finality {
    fn default() -> Self {
        Finality::Final
    }
}

/// A receipt produced when a turn is committed, providing cryptographic evidence.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnReceipt {
    pub turn_hash: [u8; 32],
    pub forest_hash: [u8; 32],
    pub pre_state_hash: [u8; 32],
    pub post_state_hash: [u8; 32],
    pub timestamp: i64,
    pub effects_hash: [u8; 32],
    pub computrons_used: u64,
    pub action_count: usize,
    pub previous_receipt_hash: Option<[u8; 32]>,
    pub agent: CellId,
    /// The federation that produced this receipt. Prevents cross-federation replay:
    /// a valid receipt from federation A cannot satisfy a TurnExecuted condition
    /// targeting federation B.
    #[serde(default)]
    pub federation_id: [u8; 32],
    /// Routing directives emitted by three-party introductions in this turn.
    #[serde(default)]
    pub routing_directives: Vec<RoutingDirective>,
    /// GC export registrations from three-party introductions.
    ///
    /// Each entry indicates that `target` was introduced to `recipient`, meaning
    /// the target's owning federation must record `recipient`'s federation as
    /// holding a reference. The node/server layer consumes these to call
    /// `ExportGcManager::record_export`, enabling proper distributed GC via
    /// `DropRef` messages.
    #[serde(default)]
    pub introduction_exports: Vec<IntroductionExport>,
    /// Capability derivation records emitted by Grant, Introduce, SpawnWithDelegation,
    /// and Unseal effects in this turn. Verifiers use these to reconstruct the CDT.
    #[serde(default)]
    pub derivation_records: Vec<DerivationRecord>,
    /// Events emitted during turn execution (for audit trails and off-chain indexing).
    #[serde(default)]
    pub emitted_events: Vec<EmittedEvent>,
    /// Ed25519 signature from the executor over the receipt hash.
    /// When present, this cryptographically binds the receipt to a known executor,
    /// making the federation exit path verifiable (not just a self-reported chain).
    /// Contains exactly 64 bytes when set.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub executor_signature: Option<Vec<u8>>,
    /// Finality status of this receipt.
    /// `Final` when backed by a BFT quorum certificate or full fast-path threshold.
    /// `Tentative` when produced by a solo-mode node awaiting peer validation.
    #[serde(default)]
    pub finality: Finality,
}

impl TurnReceipt {
    /// Compute the BLAKE3 hash of this receipt (for chaining/inclusion proofs).
    /// Note: executor_signature is NOT included (it signs the hash, not vice versa).
    pub fn receipt_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Version-bumped to v2 when federation_id binding was added.
        hasher.update(b"pyana-receipt-v2");
        hasher.update(&self.turn_hash);
        hasher.update(&self.forest_hash);
        hasher.update(&self.pre_state_hash);
        hasher.update(&self.post_state_hash);
        hasher.update(&self.timestamp.to_le_bytes());
        hasher.update(&self.effects_hash);
        hasher.update(&self.computrons_used.to_le_bytes());
        hasher.update(&(self.action_count as u64).to_le_bytes());
        hasher.update(self.agent.as_bytes());
        // Federation binding: prevents cross-federation receipt replay.
        hasher.update(&self.federation_id);
        match &self.previous_receipt_hash {
            Some(h) => {
                hasher.update(&[1u8]);
                hasher.update(h);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        hasher.update(&(self.routing_directives.len() as u64).to_le_bytes());
        for rd in &self.routing_directives {
            hasher.update(&rd.hash());
        }
        hasher.update(&(self.introduction_exports.len() as u64).to_le_bytes());
        for ie in &self.introduction_exports {
            hasher.update(ie.target.as_bytes());
            hasher.update(ie.recipient.as_bytes());
            hasher.update(&ie.authorizing_turn);
            match ie.expires {
                Some(t) => {
                    hasher.update(&[1u8]);
                    hasher.update(&t.to_le_bytes());
                }
                None => {
                    hasher.update(&[0u8]);
                }
            }
        }
        hasher.update(&(self.derivation_records.len() as u64).to_le_bytes());
        for dr in &self.derivation_records {
            hasher.update(&dr.hash());
        }
        hasher.update(&(self.emitted_events.len() as u64).to_le_bytes());
        for ev in &self.emitted_events {
            hasher.update(ev.cell.as_bytes());
            hasher.update(&ev.topic);
            for d in &ev.data {
                hasher.update(d);
            }
        }
        // Finality status binding.
        match self.finality {
            Finality::Final => {
                hasher.update(&[0x01]);
            }
            Finality::Tentative => {
                hasher.update(&[0x02]);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Canonical message the executor signs to populate
    /// [`Self::executor_signature`].
    ///
    /// Per `EFFECT-VM-SHAPE-A.md` Stage 9 R-4, the executor's signature is a
    /// domain-separated commitment to the receipt's load-bearing state
    /// transition — turn identity, the pre/post state pair it claims to advance,
    /// and the wall-clock the executor saw when committing it. This is
    /// deliberately **narrower** than [`Self::receipt_hash`]: a downstream
    /// verifier that does not understand `routing_directives`,
    /// `derivation_records`, etc. can still recover the executor's intent (this
    /// turn took the agent from `pre_state_hash` to `post_state_hash`).
    ///
    /// The signed bytes are:
    /// ```text
    /// "executor-receipt-sig-v1:" || turn_hash || pre_state_hash
    ///                            || post_state_hash || timestamp_le
    /// ```
    ///
    /// `timestamp` plays the role the master plan called `block_height` — it is
    /// the executor's monotonic clock at commit time, which is the field
    /// present on `TurnReceipt` and the right binding for the executor's view
    /// of "when did this happen".
    ///
    /// **v2 (audit F2 / T6 closed):** the canonical signed message also binds
    /// `federation_id` and `agent`. Without these, an executor signature is
    /// recoverable onto a receipt under a different federation_id (because
    /// the signature does not cover that field). Including them here means
    /// downstream verifiers can check the signature *alone* — they no longer
    /// have to independently recompute `receipt_hash` for soundness.
    pub fn canonical_executor_signed_message(&self) -> Vec<u8> {
        const DOMAIN: &[u8] = b"executor-receipt-sig-v2:";
        let agent_bytes = self.agent.as_bytes();
        let mut msg = Vec::with_capacity(DOMAIN.len() + 32 + 32 + 32 + 8 + 32 + agent_bytes.len());
        msg.extend_from_slice(DOMAIN);
        msg.extend_from_slice(&self.turn_hash);
        msg.extend_from_slice(&self.pre_state_hash);
        msg.extend_from_slice(&self.post_state_hash);
        msg.extend_from_slice(&self.timestamp.to_le_bytes());
        msg.extend_from_slice(&self.federation_id);
        msg.extend_from_slice(agent_bytes);
        msg
    }
}
