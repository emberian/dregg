//! Turn: the full atomic transaction unit.
//!
//! A Turn wraps a CallForest with metadata: who initiated it, replay protection
//! via nonce, fee payment, and optional memo/expiration.
//!
//! # Receipts as persistence layer
//!
//! Per `HOUYHNHNM-COMPARISON.md`'s "wait, this changes things" insight
//! (closing section): **the `WitnessedReceipt` chain rooted at each
//! turn IS dregg's persistence layer.** It is *not* an auxiliary
//! observability log. State is recoverable by replaying receipts; the
//! ledger snapshot at any tip is *derived* from the receipt stream;
//! `dregg_persist`'s on-disk structures are caches over this canonical
//! source.
//!
//! Concretely:
//!
//! - Every state transition that an executor applies emits a
//!   [`crate::witnessed_receipt::WitnessedReceipt`] whose
//!   `previous_receipt_hash` chain-links it to the prior receipt for
//!   the same cell. The chain *is* the cell's history.
//! - A verifier replaying the chain re-derives the cell's state. The
//!   on-disk snapshot is a memoization, not the source of truth.
//! - When an operator prunes the hot tail (per
//!   [`dregg_node::config::RetentionPolicy`]), they substitute an
//!   [`dregg_cell::lifecycle::ArchivalAttestation`] for the pruned
//!   prefix — the persistence stream is *still complete*, just
//!   summarized at the cut point.
//!
//! This framing reverses what one might naively assume about the
//! relationship between the receipt chain and "the database." The
//! database is the cache; the receipt chain is the truth.
//!
//! See `NEW-WORLD.md` ("Persistence: receipts are the stream") and
//! `BOUNDARIES.md` for the persistence-as-policy boundary; see
//! `dregg_node::config::RetentionPolicy` and
//! `dregg_wire::message::WireMessage::RequestReceipt` for the wire and
//! operator-side shapes that fall out of this reframe.

use std::collections::HashMap;

use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, DerivationRecord, LedgerDelta};
use serde::{Deserialize, Serialize};

use crate::action::{Effect, Symbol};
use crate::binding_proof::{EffectBindingProof, EffectDependency, EffectWitnessIndex};
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
/// [`dregg_cell_crypto::peer_exchange::PeerStateTransition`] one-shot: the cell key
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
///     cell's owning key and, for nonzero federation ids, to the local
///     federation — closes the "any-snooper-can-resubmit" and
///     cross-federation replay gaps).
///  3. `sequence == ledger.last_sovereign_witness_sequence(cell_id) + 1`
///     (per-cell monotonic, no gaps; closes the replay gap even if a
///     future hypothetical commitment collision were ever found).
///  4. `effects_hash ==
///     SovereignCellWitness::canonical_effects_hash(cell_id, turn's canonical
///     effect sequence)` — the signer's declared effect set must be the effect
///     set this turn actually presents for this cell. Recomputed in
///     `execute.rs` as witness rule 7, BEFORE the forest runs; a mismatch is
///     `TurnError::EffectsHashMismatch`. This is what makes the field in the
///     signing message bind: without it a sovereign owner signs
///     `H(Transfer 10)` and the executor applies `Transfer 20`.
///  5. A `transition_proof` is REFUSED outright (`InvalidExecutionProof`): the
///     v1 hand-AIR witness-STARK verify is retired and the rotated
///     proof-carrying turn is the sovereign attestation path. This witness
///     shape is verified by re-execution, never by proof.
///
/// So the two declarations are checked at two different times and against two
/// different things: `effects_hash` against the turn's own effect sequence
/// before execution (rule 7), and `new_commitment` against the recomputed
/// post-state after execution (`SovereignCommitmentMismatch`, the
/// `SOVEREIGN CELL POST-EXECUTION` block). Neither is a promise taken on
/// faith.
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
    /// Legacy canonical signing message layout for the zero-federation
    /// compatibility path:
    ///   "dregg-sovereign-witness-v1:" ||
    ///   cell_id || old_commitment || new_commitment || effects_hash ||
    ///   timestamp (8 LE) || sequence (8 LE)
    ///
    /// New federation-aware callers should use
    /// [`SovereignCellWitness::signing_message_for_federation`].
    pub fn signing_message(
        cell_id: &CellId,
        old_commitment: &[u8; 32],
        new_commitment: &[u8; 32],
        effects_hash: &[u8; 32],
        timestamp: i64,
        sequence: u64,
    ) -> Vec<u8> {
        const DOMAIN: &[u8] = b"dregg-sovereign-witness-v1:";
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

    /// Canonical federation-bound signing message layout:
    ///   "dregg-sovereign-witness-v2:" ||
    ///   federation_id || cell_id || old_commitment || new_commitment ||
    ///   effects_hash || timestamp (8 LE) || sequence (8 LE)
    ///
    /// The all-zero federation id intentionally preserves the historical v1
    /// message so default-federation tests and old local-only tooling keep
    /// using the same bytes. Configured federations get a domain-separated v2
    /// message that cannot be replayed under another federation id.
    pub fn signing_message_for_federation(
        federation_id: &[u8; 32],
        cell_id: &CellId,
        old_commitment: &[u8; 32],
        new_commitment: &[u8; 32],
        effects_hash: &[u8; 32],
        timestamp: i64,
        sequence: u64,
    ) -> Vec<u8> {
        if *federation_id == [0u8; 32] {
            return Self::signing_message(
                cell_id,
                old_commitment,
                new_commitment,
                effects_hash,
                timestamp,
                sequence,
            );
        }

        const DOMAIN: &[u8] = b"dregg-sovereign-witness-v2:";
        let mut msg = Vec::with_capacity(DOMAIN.len() + 32 + 32 + 32 + 32 + 32 + 8 + 8);
        msg.extend_from_slice(DOMAIN);
        msg.extend_from_slice(federation_id);
        msg.extend_from_slice(cell_id.as_bytes());
        msg.extend_from_slice(old_commitment);
        msg.extend_from_slice(new_commitment);
        msg.extend_from_slice(effects_hash);
        msg.extend_from_slice(&timestamp.to_le_bytes());
        msg.extend_from_slice(&sequence.to_le_bytes());
        msg
    }

    /// Domain separator for the canonical sovereign effects binding.
    pub const EFFECTS_DOMAIN: &'static [u8] = b"dregg-sovereign-effects-v1:";

    /// Does `effect`, applied by an action targeting `action_target`, project
    /// onto `cell_id`?
    ///
    /// Three ways in, and each one closes a specific hole:
    ///
    /// - **The action targets the cell.** This is exactly the condition under
    ///   which the executor DEMANDS a witness for the cell
    ///   (`TurnError::SovereignWitnessRequired`, raised on `action.target`), so
    ///   every effect the cell's witness paid for is in its projection —
    ///   including `ExerciseViaCapability`, whose real target is a c-list slot
    ///   resolved only at apply time and therefore absent from the effect body.
    /// - **The effect names the cell** ([`Effect::participant_cells`]).
    /// - **The effect names NO cell.** Value creation/destruction and cell
    ///   creation (`NoteSpend`/`NoteCreate`/`CreateCell`/…) are attributed to
    ///   every witnessed cell rather than to none, so an unattributed effect can
    ///   never be bundled in under a signature that does not cover it.
    pub fn projects_onto(cell_id: &CellId, action_target: &CellId, effect: &Effect) -> bool {
        if action_target == cell_id {
            return true;
        }
        let participants = effect.participant_cells();
        participants.is_empty() || participants.contains(cell_id)
    }

    /// THE canonical value of [`SovereignCellWitness::effects_hash`].
    ///
    /// ```text
    /// BLAKE3( "dregg-sovereign-effects-v1:"
    ///       ‖ cell_id                               (32)
    ///       ‖ projected_count as u64 LE             (8)
    ///       ‖ for each projected (action_target, effect), IN EXECUTION ORDER:
    ///             action_target (32) ‖ effect.hash() (32) )
    /// ```
    ///
    /// `sequence` is the turn's canonical `(action target, effect)` sequence —
    /// [`Turn::canonical_effect_sequence`], which is the executor's own apply
    /// order. Every producer MUST derive the value through
    /// [`Turn::sovereign_effects_hash`]; a caller-supplied `effects_hash` binds
    /// nothing, which is precisely how this field spent its first life.
    ///
    /// The shape, and why each piece is load-bearing:
    ///
    /// - **Domain separation** so this digest can never be confused with the
    ///   receipt's turn-wide `effects_hash` (a flat BLAKE3 fold of the same
    ///   `Effect::hash()` values, no domain tag, no cell) or with a bare
    ///   `Effect::hash()`.
    /// - **`cell_id` absorbed** so two sovereign cells in one turn get two
    ///   different digests even when their projections coincide. A witness
    ///   digest is not transplantable between cells.
    /// - **Length prefix** so the projection is prefix-free: without it,
    ///   `[a, b]` for one cell and `[a]‖[b]` split across a boundary absorb the
    ///   same stream, which is a signature valid over two different effect sets.
    /// - **`action_target` per entry** so the same effect body under a different
    ///   action target is a different authorization. `Effect::hash()` alone does
    ///   not see the enclosing action.
    /// - **EXECUTION ORDER, not declaration order.** Within an action the
    ///   executor applies regular effects first and permission effects last
    ///   (so an action cannot weaken permissions and then exploit them);
    ///   `canonical_effect_sequence` reproduces that partition. Hashing the
    ///   declared order would let a producer and the executor disagree about
    ///   the same turn.
    ///
    /// **Never zero.** The empty projection still absorbs the domain, the
    /// cell id and a zero count, so `[0u8; 32]` is not a reachable value — a
    /// witness that authorizes no effects has an honest, checkable encoding and
    /// does not need a sentinel.
    pub fn canonical_effects_hash(cell_id: &CellId, sequence: &[(CellId, &Effect)]) -> [u8; 32] {
        let projected: Vec<&(CellId, &Effect)> = sequence
            .iter()
            .filter(|(action_target, effect)| Self::projects_onto(cell_id, action_target, effect))
            .collect();

        let mut hasher = blake3::Hasher::new();
        hasher.update(Self::EFFECTS_DOMAIN);
        hasher.update(cell_id.as_bytes());
        hasher.update(&(projected.len() as u64).to_le_bytes());
        for (action_target, effect) in projected {
            hasher.update(action_target.as_bytes());
            hasher.update(&effect.hash());
        }
        *hasher.finalize().as_bytes()
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

/// Absorb one [`EmittedEvent`] into `hasher` under the canonical **prefix-free**
/// event encoding:
///
/// ```text
/// cell (32) ‖ topic (32) ‖ data.len() as u64 LE (8) ‖ data[0] (32) ‖ … ‖ data[n-1] (32)
/// ```
///
/// This is the single source of truth for how an event contributes to a
/// commitment. Both [`TurnReceipt::receipt_hash`] (domain `dregg-receipt-v5`)
/// and [`crate::finalized_receipt_core_v1`]'s `event_commitment` (domain
/// `dregg-finalized-events-v1`) call it, so the two can no longer drift.
///
/// **Why the `data.len()` prefix is load-bearing.** `data` is variable length
/// and every other component is exactly 32 bytes. Without the count, the
/// concatenation of a *list* of events is not prefix-free: with
/// `e1 = { cell: c1, topic: t1, data: [a, b] }`, `e2 = { cell: c2, topic: t2,
/// data: [] }` and `e1' = { cell: c1, topic: t1, data: [a] }`,
/// `e2' = { cell: b, topic: c2, data: [t2] }`, the two *different* lists
/// `[e1, e2]` and `[e1', e2']` absorb the *identical* byte stream — the field
/// boundaries slide by exactly one 32-byte lane. That is a receipt-hash
/// collision, i.e. two distinct execution outcomes with one executor signature
/// valid over both. Counting the felts pins the boundary.
pub fn absorb_emitted_event(hasher: &mut blake3::Hasher, event: &EmittedEvent) {
    hasher.update(event.cell.as_bytes());
    hasher.update(&event.topic);
    hasher.update(&(event.data.len() as u64).to_le_bytes());
    for field in &event.data {
        hasher.update(field);
    }
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
    /// The 32-byte vk_hash identifying the custom-effect verifier this proof
    /// dispatches to. The executor looks this up in its
    /// [`CustomEffectRegistry`](dregg_cell::CustomEffectRegistry) and invokes
    /// the registered verifier (`proof_verify::enforce_custom_effect_proofs`).
    /// Fail-closed: an unregistered vk_hash rejects the turn. Bound into
    /// [`Turn::hash`] so it cannot be swapped post-signature.
    #[serde(default)]
    pub vk_hash: [u8; 32],
    /// The serialized proof bytes for the custom program.
    pub proof_bytes: Vec<u8>,
    /// Public inputs for the custom program proof (raw u32 BabyBear values).
    pub public_inputs: Vec<u32>,
}

impl CustomProgramProof {
    /// Convert raw public inputs to BabyBear elements for verification.
    pub fn public_inputs_babybear(&self) -> Vec<dregg_circuit::field::BabyBear> {
        self.public_inputs
            .iter()
            .map(|&v| dregg_circuit::field::BabyBear::new(v))
            .collect()
    }

    /// Serialize the raw public inputs to the little-endian byte vector the
    /// registered [`CustomEffectVerifier`](dregg_cell::CustomEffectVerifier)
    /// consumes (4 bytes per u32, in order).
    pub fn public_inputs_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.public_inputs.len() * 4);
        for v in &self.public_inputs {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out
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
    // No `skip_serializing_if`: `Turn` is transmitted via postcard (a
    // non-self-describing format), where omitting a field on serialize but
    // still reading it on deserialize desynchronizes the byte stream ("Found
    // an Option discriminant that wasn't 0 or 1"). Every field must always be
    // written. `#[serde(default)]` keeps JSON tolerant of missing keys.
    #[serde(default)]
    pub conservation_proof: Option<Vec<u8>>,
    /// Witnesses for sovereign cells targeted by this turn.
    ///
    /// When a turn's call forest targets a sovereign cell, the agent must provide
    /// the full cell state here. The executor verifies that
    /// `witness.state_proof == witness.cell_state.state_commitment()` and that this
    /// matches the stored commitment in the ledger.
    #[serde(default)]
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
    #[serde(default)]
    pub execution_proof: Option<Vec<u8>>,
    /// The target cell ID for proof-carrying turns. Required when `execution_proof` is Some.
    #[serde(default)]
    pub execution_proof_cell: Option<CellId>,
    /// The new commitment claimed by the execution proof.
    /// The proof's public inputs must include this value. After verification, the
    /// ledger's sovereign commitment is updated to this value.
    #[serde(default)]
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
    #[serde(default)]
    pub custom_program_proofs: Option<Vec<CustomProgramProof>>,
    /// Sidecar full-fidelity binding proofs, one per Effect that has a
    /// schema in `dregg_circuit::effect_action_air`. The verifier
    /// (`verify_proof_carrying_turn_bundle`) walks this list, looks up
    /// each schema by `schema_id`, reconstructs the expected PI from
    /// the executor's view of the effect's typed parameters, and
    /// verifies the STARK proof. Tampering on any byte of any 32-byte
    /// field, or any bit of any u64 amount, fails verification.
    ///
    /// Empty by default — turns without binding proofs continue to
    /// apply with executor-trusted enforcement (backwards compat).
    /// Turns *with* binding proofs get strong-soundness enforcement.
    ///
    /// See `PROOF-TO-ACTION-BINDING-SWEEP.md` §3.3 + §5.
    #[serde(default)]
    pub effect_binding_proofs: Vec<EffectBindingProof>,
    /// Cross-effect within-turn chain pinnings. Each entry asserts that
    /// the output of one effect equals the input of a later effect
    /// (e.g., NoteSpend's nullifier ↔ BridgeMint's consumed nullifier
    /// when both are in the same turn). The AIR enforces the
    /// algebraic equality; without this, the executor could substitute
    /// a different nullifier for the consumer.
    ///
    /// See `PROOF-TO-ACTION-BINDING-SWEEP.md` §3.3.
    #[serde(default)]
    pub cross_effect_dependencies: Vec<EffectDependency>,
    /// Witness-blob → effect indexing. Pins which witness blob each
    /// effect consumes, preventing the executor from shuffling blobs
    /// so an effect requiring witness K reads bytes meant for effect L.
    ///
    /// See `PROOF-TO-ACTION-BINDING-SWEEP.md` §3.2.
    #[serde(default)]
    pub effect_witness_index_map: Vec<EffectWitnessIndex>,
}

impl Turn {
    // Stage 7-α (R-2 closure / EFFECT-VM-SHAPE-A.md §Receipts): the v3 domain
    // tag covers every semantically load-bearing field on `Turn`, including
    // the execution-proof bundle (`execution_proof`,
    // `execution_proof_cell`, `execution_proof_new_commitment`),
    // `sovereign_witnesses`, and
    // `custom_program_proofs`. The v2 form excluded those, so an attacker
    // with write-access to an in-flight `SignedTurn` could swap any of
    // them without invalidating the signature (the "proof-swap attack").
    //
    // ⚑ ONE FIELD IS DELIBERATELY NOT COVERED, and earlier revisions of this
    // note wrongly listed it as covered: `conservation_proof`. It CANNOT be
    // hashed here, because the Schnorr excess proof is itself computed OVER
    // this hash — `check_committed_conservation` verifies it against
    // `turn.hash()` (`executor/finalize.rs:~272`), so binding the proof into
    // the hash would be circular. The binding therefore runs proof → hash, not
    // hash → proof, and that direction is the sound one: a swapped or stripped
    // `conservation_proof` cannot verify against this turn's hash and its
    // committed legs, so it fails closed. The residual is malleability, not
    // forgery — an in-flight tamper keeps the signature valid and turns the
    // turn into a rejection (a griefing/DoS vector), it does not admit one.
    //
    // Note for callers: this hash is a content-addressed identifier for
    // the entire `Turn` object. The cclerk still signs over its own
    // `compute_turn_bytes` (sdk/src/cipherclerk.rs) which deliberately covers
    // only the fields a cclerk sees at sign time; `Turn::hash` is what
    // the executor, receipt chain, and (post-Stage 7-γ.0) the per-cell
    // proof bundle agree on after the fact. Cipherclerk signature compatibility
    // is therefore preserved by this bump.
    pub fn hash(&self) -> [u8; 32] {
        let forest_hash = self.call_forest.compute_hash();
        self.hash_with_forest(&forest_hash)
    }

    /// `hash()` with an already-computed `forest_hash`. The forest hash is the
    /// most expensive ingredient (a per-action BLAKE3 walk over the whole call
    /// tree); the receipt path computes it ONCE and feeds it to both `turn_hash`
    /// and the receipt's `forest_hash` field, avoiding a second identical walk.
    /// `forest_hash` MUST equal `self.call_forest.compute_hash()` — byte-identity
    /// of the resulting `turn_hash` depends on it (the caller owns that invariant).
    pub fn hash_with_forest(&self, forest_hash: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Domain separation: prevents type confusion with other hash preimages.
        hasher.update(b"dregg-turn-v3:");
        hasher.update(self.agent.as_bytes());
        hasher.update(&self.nonce.to_le_bytes());
        hasher.update(forest_hash);
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
                    // Bind the verifier identity (vk_hash) so the dispatched
                    // verifier cannot be swapped after the turn is signed.
                    hasher.update(&proof.vk_hash);
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
        // --- Proof-to-action binding additions ---
        //
        // To preserve byte-identity with pre-binding-sweep v3 turns
        // (which have no binding proofs / dependencies / witness map),
        // we gate the additional binding-related fields behind a
        // "any present?" presence byte. When all three vectors are
        // empty, no extra bytes are absorbed and the v3 hash is
        // byte-identical to the prior schema. When any are present,
        // a [1u8] discriminator + each vector's length + each element
        // is absorbed. Length prefixes prevent boundary confusion.
        let has_binding_extensions = !self.effect_binding_proofs.is_empty()
            || !self.cross_effect_dependencies.is_empty()
            || !self.effect_witness_index_map.is_empty();
        if has_binding_extensions {
            hasher.update(&[1u8]);
            hasher.update(&(self.effect_binding_proofs.len() as u64).to_le_bytes());
            for bp in &self.effect_binding_proofs {
                bp.hash_into(&mut hasher);
            }
            hasher.update(&(self.cross_effect_dependencies.len() as u64).to_le_bytes());
            for dep in &self.cross_effect_dependencies {
                dep.hash_into(&mut hasher);
            }
            hasher.update(&(self.effect_witness_index_map.len() as u64).to_le_bytes());
            for ewi in &self.effect_witness_index_map {
                ewi.hash_into(&mut hasher);
            }
        }
        *hasher.finalize().as_bytes()
    }

    pub fn action_count(&self) -> usize {
        self.call_forest.action_count()
    }

    /// Is this a COORDINATION turn — observable, append-only, non-state-mutating?
    ///
    /// True iff the call forest is non-empty AND every action in it (recursing
    /// through children) declares no `balance_change` and produces ONLY
    /// [`Effect::EmitEvent`](crate::action::Effect::EmitEvent) effects. Such
    /// turns are oversight traffic (status posts, gate verdicts, chat): they
    /// move no value and mutate no cell state beyond the append-only event log.
    ///
    /// Consumed by the opt-in
    /// [`ComputronCosts::coordination_exempt`](crate::executor::ComputronCosts)
    /// class ("leash, not ledger" — the computron is an oversight budget, not an
    /// economic cost): when a deployment opts in, the executor waives the CHARGE
    /// for this class (a `fee = 0` coordination turn admits) while metering
    /// stays honest — receipts still report the true `computrons_used`. Any
    /// non-`EmitEvent` effect or any `balance_change` disqualifies the whole
    /// turn, so the class cannot leak to value moves.
    pub fn is_coordination(&self) -> bool {
        fn tree_is_coordination(tree: &crate::forest::CallTree) -> bool {
            tree.action.balance_change.is_none()
                && tree
                    .action
                    .effects
                    .iter()
                    .all(|e| matches!(e, crate::action::Effect::EmitEvent { .. }))
                && tree.children.iter().all(tree_is_coordination)
        }
        !self.call_forest.is_empty() && self.call_forest.roots.iter().all(tree_is_coordination)
    }

    /// Every effect this turn will apply, paired with the target of the action
    /// that carries it, **in the executor's apply order**.
    ///
    /// The order is the one `TurnExecutor::execute` + `execute_tree` realize,
    /// and nothing else is a legitimate reading of "this turn's effects":
    ///
    /// 1. roots in index order;
    /// 2. per action, PRE-order — the action's own effects, then its children
    ///    left to right;
    /// 3. within an action, `!is_permission_effect()` first and permission
    ///    effects last (the executor's `partition`, which exists so an action
    ///    cannot weaken permissions and then exploit the weakened state).
    ///
    /// This is total for a turn that commits: `execute_tree` applies every
    /// effect of every action it reaches and returns `Err` (rejecting the whole
    /// turn) otherwise, so on the commit path the applied sequence IS this
    /// sequence. That is what lets a signer — who cannot run the executor —
    /// compute the same digest the executor checks.
    ///
    /// [`crate::forest::CallForest::total_effects`] is NOT this function: it
    /// walks declaration order and drops the action target.
    pub fn canonical_effect_sequence(&self) -> Vec<(CellId, &Effect)> {
        fn walk<'a>(tree: &'a crate::forest::CallTree, out: &mut Vec<(CellId, &'a Effect)>) {
            let target = tree.action.target;
            for effect in tree
                .action
                .effects
                .iter()
                .filter(|e| !e.is_permission_effect())
            {
                out.push((target, effect));
            }
            for effect in tree
                .action
                .effects
                .iter()
                .filter(|e| e.is_permission_effect())
            {
                out.push((target, effect));
            }
            for child in &tree.children {
                walk(child, out);
            }
        }
        let mut out = Vec::new();
        for root in &self.call_forest.roots {
            walk(root, &mut out);
        }
        out
    }

    /// The canonical `effects_hash` a [`SovereignCellWitness`] for `cell_id`
    /// must carry for THIS turn.
    ///
    /// The one entry point for every producer and for the executor's rule-7
    /// check. If a producer computes this any other way, the two definitions
    /// will disagree and the disagreement will be discovered by a rejected
    /// turn rather than by a compiler.
    pub fn sovereign_effects_hash(&self, cell_id: &CellId) -> [u8; 32] {
        SovereignCellWitness::canonical_effects_hash(cell_id, &self.canonical_effect_sequence())
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

/// Which authorization surface CONSUMED the capability a
/// [`ConsumedCapWitness`] records.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConsumedCapAuthPath {
    /// `Authorization::Breadstuff(token)`: the ACTOR presented a breadstuff
    /// token matching a capability in its own c-list (the consumed authority
    /// is the actor's capability).
    Breadstuff,
    /// `Authorization::Bearer` with `DelegationProofData::SignedDelegation`:
    /// the DELEGATOR's c-list capability is the consumed authority (the
    /// bearer proof derives from it; non-amplification was checked against
    /// it).
    BearerSignedDelegation,
}

/// The capability CONSUMED to authorize an action, witnessed against the
/// holder's PRE-state `capability_root` (cap Phase C).
///
/// `collect_derivation_records` records capabilities a turn *creates*
/// (Grant/Introduce/Spawn/Unseal); this is the missing other half — the
/// capability the turn *consumed* to be authorized at all. Without it the
/// authorization leg of a full-turn proof cannot be reconstructed post-hoc
/// (the prodadmis blocker documented at `node/src/turn_proving.rs`), so
/// production AUTHORITY binding (Phase D) is unbuildable.
///
/// The witness carries the FULL 7-field leaf preimage of the canonical
/// openable capability tree (`dregg_circuit::cap_root::CapLeaf` — the
/// sorted-Poseidon2 Merkle scheme Phase A made `capability_root`) plus the
/// sorted-Merkle membership path against the holder's c-list root AS IT WAS
/// IN SCOPE AT AUTHORIZATION TIME (authorization runs before the action's
/// effects apply, so for the first action that consumes a capability this is
/// the turn's pre-state root). All felts are canonical BabyBear values
/// stored as `u32` (the same low-4-byte encoding
/// `dregg_cell::felt_to_bytes32` pins).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsumedCapWitness {
    /// The cell whose c-list HELD the consumed capability (the actor for the
    /// breadstuff path; the delegator for the bearer path).
    pub holder: CellId,
    /// The c-list slot of the consumed capability.
    pub slot: u32,
    /// The call-forest path of the action this capability authorized.
    pub action_path: Vec<usize>,
    /// Which authorization surface consumed it.
    pub auth_path: ConsumedCapAuthPath,
    /// Leaf field 1: the sort key, `cap_root::slot_hash(slot)`.
    pub leaf_slot_hash: u32,
    /// Leaf field 2: the target cell id folded to one felt.
    pub leaf_target: u32,
    /// Leaf field 3: the `AuthRequired` tier tag (+ vk_hash for Custom).
    pub leaf_auth_tag: u32,
    /// Leaf field 4: `EffectMask` low 16 bits.
    pub leaf_mask_lo: u32,
    /// Leaf field 5: `EffectMask` high 16 bits.
    pub leaf_mask_hi: u32,
    /// Leaf field 6: optional expiry height encoding.
    pub leaf_expiry: u32,
    /// Leaf field 7: optional breadstuff hash folded to one felt.
    pub leaf_breadstuff: u32,
    /// Sibling 8-felt digests along the membership path, bottom-up
    /// (`CAP_TREE_DEPTH` entries). Each is a native-`node8` `Digest8` (8 lanes,
    /// canonical BabyBear values stored as `u32`).
    pub siblings: Vec<[u32; 8]>,
    /// Direction bits along the path: 0 = current node is the LEFT child
    /// (sibling on the right), 1 = right.
    pub directions: Vec<u8>,
    /// The canonical FAITHFUL 8-felt capability root the path opens against — the
    /// holder's PRE-state `capability_root` (`Digest8`, lane 0 ‖ lanes 1..7). Lane 0
    /// is the historical scalar root (`compute_canonical_capability_root_felt`).
    pub cap_root: [u32; 8],
}

impl ConsumedCapWitness {
    /// Reconstruct the canonical 7-field [`dregg_circuit::cap_root::CapLeaf`].
    pub fn cap_leaf(&self) -> dregg_circuit::cap_root::CapLeaf {
        use dregg_circuit::field::BabyBear;
        dregg_circuit::cap_root::CapLeaf {
            slot_hash: BabyBear::new(self.leaf_slot_hash),
            target: BabyBear::new(self.leaf_target),
            auth_tag: BabyBear::new(self.leaf_auth_tag),
            mask_lo: BabyBear::new(self.leaf_mask_lo),
            mask_hi: BabyBear::new(self.leaf_mask_hi),
            expiry: BabyBear::new(self.leaf_expiry),
            breadstuff: BabyBear::new(self.leaf_breadstuff),
        }
    }

    /// Recompute the Merkle root implied by the leaf preimage + path.
    /// `None` if the witness is malformed (wrong path length / direction
    /// bits outside {0,1}).
    pub fn recompute_root(&self) -> Option<[u32; 8]> {
        use dregg_circuit::cap_root::{CAP_TREE_DEPTH, cap_node8};
        use dregg_circuit::field::BabyBear;
        if self.siblings.len() != CAP_TREE_DEPTH || self.directions.len() != CAP_TREE_DEPTH {
            return None;
        }
        // The internal-node hash MUST be the canonical native `cap_node8` (the
        // arity-16 `node8` compression `perm(L8 ‖ R8)[0..8]`) the sorted
        // `CanonicalCapTree` folds with — NOT a lane-0 squeeze — or the recomputed
        // top diverges from `tree.root()` and `verify()` rejects a genuine path.
        let mut cur = self.cap_leaf().digest();
        for (sib, dir) in self.siblings.iter().zip(self.directions.iter()) {
            let sib: [BabyBear; 8] = sib.map(BabyBear::new);
            cur = match dir {
                // direction 0 ⇒ current node is the LEFT child (sibling right).
                0 => cap_node8(cur, sib),
                1 => cap_node8(sib, cur),
                _ => return None,
            };
        }
        Some(cur.map(|f| f.as_u32()))
    }

    /// Verify the membership path: the recorded leaf preimage opens to the
    /// recorded `cap_root`. NON-vacuous — a tampered leaf field, sibling,
    /// direction bit, or root makes this false.
    pub fn verify(&self) -> bool {
        self.recompute_root() == Some(self.cap_root)
    }

    /// The 32-byte encoding of `cap_root`'s LANE-0 (the historical scalar root),
    /// byte-identical to `dregg_cell::compute_canonical_capability_root` over the
    /// holder's pre-state c-list (`felt_to_bytes32`: lane-0's low 4 little-endian
    /// bytes, rest zero). The full 8-felt root rides the `cap_root` field.
    pub fn cap_root_bytes32(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[0..4].copy_from_slice(&self.cap_root[0].to_le_bytes());
        out
    }

    /// Domain-separated BLAKE3 digest of every field; folded into
    /// `TurnReceipt::receipt_hash` (v3) so an executor cannot strip or
    /// tamper the consumed-capability disclosure.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-consumed-cap-v1");
        hasher.update(self.holder.as_bytes());
        hasher.update(&self.slot.to_le_bytes());
        hasher.update(&(self.action_path.len() as u64).to_le_bytes());
        for p in &self.action_path {
            hasher.update(&(*p as u64).to_le_bytes());
        }
        hasher.update(&[match self.auth_path {
            ConsumedCapAuthPath::Breadstuff => 1u8,
            ConsumedCapAuthPath::BearerSignedDelegation => 2u8,
        }]);
        for felt in [
            self.leaf_slot_hash,
            self.leaf_target,
            self.leaf_auth_tag,
            self.leaf_mask_lo,
            self.leaf_mask_hi,
            self.leaf_expiry,
            self.leaf_breadstuff,
        ] {
            hasher.update(&felt.to_le_bytes());
        }
        hasher.update(&(self.siblings.len() as u64).to_le_bytes());
        for s in &self.siblings {
            for lane in s {
                hasher.update(&lane.to_le_bytes());
            }
        }
        hasher.update(&(self.directions.len() as u64).to_le_bytes());
        hasher.update(&self.directions);
        for lane in &self.cap_root {
            hasher.update(&lane.to_le_bytes());
        }
        *hasher.finalize().as_bytes()
    }
}

/// A receipt produced when a turn is committed, providing cryptographic evidence.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
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
    #[serde(default)]
    pub executor_signature: Option<Vec<u8>>,
    /// Finality status of this receipt.
    /// `Final` when backed by a BFT quorum certificate or full fast-path threshold.
    /// `Tentative` when produced by a solo-mode node awaiting peer validation.
    #[serde(default)]
    pub finality: Finality,
    /// True when this receipt was produced by decrypting an `EncryptedTurn`
    /// envelope (the Layer-2 privacy path); false for cleartext-`Turn`
    /// submissions. AUDIT-privacy.md §11.2 / BOUNDARIES.md §5: external
    /// verifiers may want to know "this turn arrived over the encrypted
    /// path" without learning anything about its content. The flag itself
    /// is the *only* metadata bit disclosed — it is bound by
    /// `receipt_hash` so a malicious executor cannot strip or forge it.
    #[serde(default)]
    pub was_encrypted: bool,
    /// True when any action in this turn carried an `Effect::Burn`. The
    /// flag is bound into `receipt_hash` so an executor cannot strip the
    /// non-conservation disclosure: a verifier seeing `was_burn = true`
    /// knows total supply on this turn provably did not balance.
    /// Analogous to `was_encrypted` per the Silver-Vision lifecycle plan.
    #[serde(default)]
    pub was_burn: bool,
    /// The capabilities CONSUMED to authorize this turn's actions, each with
    /// a full leaf preimage + sorted-Merkle membership path against the
    /// holder's PRE-state `capability_root` (cap Phase C — the executor half
    /// of production-authority binding). The CONSUMED sibling of
    /// `derivation_records` (which records capabilities the turn CREATES).
    /// Self-sovereign turns (owner-signature authority, no capability
    /// consumed) carry an empty vec. Bound into `receipt_hash` (v3) so the
    /// executor cannot strip or forge the disclosure.
    #[serde(default)]
    pub consumed_capabilities: Vec<ConsumedCapWitness>,
}

impl TurnReceipt {
    /// Compute the BLAKE3 hash of this receipt (for chaining/inclusion proofs).
    /// Note: executor_signature is NOT included (it signs the hash, not vice versa).
    pub fn receipt_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Version-bumped to v2 when federation_id binding was added; to v3
        // when consumed_capabilities binding was added (cap Phase C); to v4
        // when `pre_state_hash` / `post_state_hash` STOPPED being the
        // trusted-Rust BLAKE3 `Ledger::root()` and BECAME the AIR-bound chip
        // 8-felt state commitment (`crate::state_commit`). The fields are the
        // same width — `Faithful8::to_bytes32` packs 8 × 4 LE = exactly 32
        // bytes — so only the VALUE and its MEANING changed. The domain bump
        // fences that: a v3 verifier reconstructing a v4 preimage fails the
        // signature check rather than silently comparing a Poseidon2 anchor
        // against a BLAKE3 root.
        //
        // v5 makes the `emitted_events` absorption PREFIX-FREE. Through v4 an
        // event was absorbed as `cell ‖ topic ‖ data*` with no count in front
        // of the variable-length `data` vector, so the event *list* encoding
        // admitted collisions: two different `Vec<EmittedEvent>` whose field
        // boundaries slide by one 32-byte lane produce the same absorbed byte
        // stream, hence the same receipt hash and one executor signature valid
        // over both outcomes. `absorb_emitted_event` now counts the felts, and
        // is shared verbatim with `finalized_receipt_core_v1::event_commitment`
        // (which already counted) so the two encodings cannot drift again.
        // Same fencing rationale as v4: a v4 verifier reconstructing a v5
        // preimage fails, rather than silently accepting.
        //
        // NB the receipt hash itself stays BLAKE3. That is the dual-hash ADR
        // working as written (`dregg_commit::hash`): this is a non-ZK
        // general-purpose commitment over an already-algebraic anchor, not a
        // value any circuit recomputes.
        hasher.update(b"dregg-receipt-v5");
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
            // v5: prefix-free per-event encoding, shared with
            // `finalized_receipt_core_v1::event_commitment`.
            absorb_emitted_event(&mut hasher, ev);
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
        // Privacy-path disclosure binding: was this receipt produced by
        // decrypting an `EncryptedTurn` envelope? Bound so an executor cannot
        // strip / forge this bit without breaking the receipt hash chain.
        hasher.update(&[if self.was_encrypted { 0x01 } else { 0x00 }]);
        // Burn disclosure binding: did any action in this turn carry an
        // `Effect::Burn`? Bound so an executor cannot strip the non-
        // conservation disclosure. Silver-Vision lifecycle extension.
        hasher.update(&[if self.was_burn { 0x01 } else { 0x00 }]);
        // Consumed-capability binding (v3, cap Phase C): the witnesses for
        // the capabilities this turn CONSUMED to authorize its actions. Bound
        // so an executor cannot strip / tamper the authority disclosure.
        hasher.update(&(self.consumed_capabilities.len() as u64).to_le_bytes());
        for cw in &self.consumed_capabilities {
            hasher.update(&cw.hash());
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
    ///
    /// **v3 (audit P0 #76 closed):** the canonical signed message now binds
    /// the *full* `receipt_hash()`. v2 narrowed the message to the
    /// turn-identity / state-transition prefix, leaving
    /// `effects_hash`, `computrons_used`, `action_count`,
    /// `previous_receipt_hash`, `derivation_records`, `routing_directives`,
    /// `introduction_exports`, `emitted_events`, `finality`,
    /// `was_encrypted`, and `was_burn` unsigned. An executor signature was
    /// therefore recoverable onto a receipt with a tampered
    /// `was_encrypted` bit, a stripped derivation record, or a forged
    /// chain link — none of which v2 covered. By signing the full
    /// canonical `receipt_hash` under a fresh domain string, v3 makes the
    /// signature attest to *every* field bound into `receipt_hash`. The
    /// v2 narrow message is preserved (see
    /// [`Self::canonical_executor_signed_message_v2`]) so existing fixtures and
    /// test vectors can still round-trip; new signers should use v5.
    ///
    /// **v4 (state anchor):** the state fields the message transitively covers
    /// are no longer the trusted-Rust BLAKE3 `Ledger::root()` — they are the
    /// AIR-bound chip 8-felt commitment (`crate::state_commit`). The domain
    /// bumps in lockstep with `dregg-receipt-v4` so an executor signature can
    /// never be replayed across the meaning change.
    ///
    /// **v5 (prefix-free events):** `receipt_hash` now counts each event's
    /// data felts ([`absorb_emitted_event`]), closing a receipt-hash collision
    /// on the emitted-event list. The domain bumps in lockstep with
    /// `dregg-receipt-v5` for exactly the reason v4 did: a v4 verifier
    /// reconstructing a v5 preimage must FAIL the signature check rather than
    /// silently compare two encodings that disagree about where an event's
    /// data ends.
    pub fn canonical_executor_signed_message(&self) -> Vec<u8> {
        const DOMAIN: &[u8] = b"executor-receipt-sig-v5:";
        let receipt_hash = self.receipt_hash();
        let mut msg = Vec::with_capacity(DOMAIN.len() + 32);
        msg.extend_from_slice(DOMAIN);
        msg.extend_from_slice(&receipt_hash);
        msg
    }

    /// Legacy v2 canonical executor-signed message. Preserved for
    /// fixtures and any verifier still expecting the narrow prefix
    /// (turn_hash + pre/post + timestamp + federation_id + agent). New
    /// signers must use [`canonical_executor_signed_message`] (v3) —
    /// see audit P0 #76 for the soundness gap v2 left open.
    pub fn canonical_executor_signed_message_v2(&self) -> Vec<u8> {
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
