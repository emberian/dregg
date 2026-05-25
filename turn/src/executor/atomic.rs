//! Multi-party atomic proofs: sovereign-only and mixed sovereign/hosted turns.

use pyana_cell::{CellId, Ledger};
use serde::{Deserialize, Serialize};

use crate::journal::LedgerJournal;

use super::TurnExecutor;

// =============================================================================
// Multi-Party Atomic Proofs
// =============================================================================

/// A single sovereign cell's proof entry in an atomic multi-party turn.
///
/// Each entry binds a cell to its STARK proof and commitment transition.
/// The `balance_delta` field is a PRE-FLIGHT HINT only: the authoritative delta
/// is EXTRACTED from the proof's public inputs by the verifier. This prevents
/// a submitter from lying about their balance change.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AtomicProofEntry {
    /// The sovereign cell ID.
    pub cell_id: CellId,
    /// The serialized STARK proof bytes.
    pub proof: Vec<u8>,
    /// The old state commitment (must match what the federation stores).
    pub old_commitment: [u8; 32],
    /// The new state commitment (will be stored after verification).
    pub new_commitment: [u8; 32],
    /// The BLAKE3 hash of effects this cell is applying.
    pub effects_hash: [u8; 32],
    /// Pre-flight hint of net balance change (positive = receives, negative = sends).
    /// NOT trusted by the executor: the real delta is extracted from PI[32..34] of the proof.
    /// This field exists for client-side pre-validation and routing hints only.
    pub balance_delta: i64,
}

/// A mixed atomic turn containing both sovereign (proof-carrying) and hosted
/// (federation-executed) cells in a single atomic operation.
///
/// Conservation is enforced across BOTH domains: sovereign deltas (extracted from
/// proofs) plus hosted deltas (computed from execution) must sum to zero.
///
/// SECURITY (C1 fix): the hosted side is now expressed as a `Vec<Action>` so
/// each hosted-side operation carries its own `Authorization` (Ed25519 sig,
/// proof, bearer cap, etc.). Each action's authorization is verified via the
/// standard `verify_authorization` pipeline before its effects are applied.
/// Previously `hosted_effects: Vec<(CellId, Vec<Effect>)>` had no
/// per-cell auth, which allowed any caller of `execute_mixed_atomic` to
/// mutate any hosted cell's balance.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MixedAtomicTurn {
    /// The agent submitting this turn (pays fee, provides nonce).
    pub agent: CellId,
    /// Nonce for replay protection.
    pub nonce: u64,
    /// Fee in computrons.
    pub fee: u64,
    /// Proof-carrying sovereign cell entries.
    pub sovereign_entries: Vec<AtomicProofEntry>,
    /// Hosted-side actions. Each `Action` carries its own authorization, which
    /// is verified before any of its effects apply.
    pub hosted_actions: Vec<crate::action::Action>,
}

/// Result of a successful mixed atomic turn execution.
#[derive(Clone, Debug)]
pub struct MixedAtomicResult {
    /// New commitments for sovereign cells (in order of sovereign_entries).
    pub sovereign_commitments: Vec<[u8; 32]>,
    /// Proven balance deltas for sovereign cells (extracted from proofs).
    pub sovereign_deltas: Vec<i64>,
    /// Computed balance deltas for hosted cells.
    pub hosted_deltas: Vec<i64>,
}

/// An atomic multi-party sovereign turn: multiple sovereign cells each provide
/// a STARK proof of their individual state transition. The executor verifies ALL
/// proofs atomically and checks cross-cell conservation (the sum of all balance
/// deltas must be zero).
///
/// This enables multi-party transactions (e.g., Alice sends to Bob) where each
/// party proves their own transition independently, and the federation verifies
/// that the overall conservation law holds.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AtomicSovereignTurn {
    /// The agent submitting this atomic turn (pays fee, provides nonce).
    pub agent: CellId,
    /// Nonce for replay protection (from the agent cell).
    pub nonce: u64,
    /// Fee in computrons (deducted from agent's balance).
    pub fee: u64,
    /// The proof entries: one per sovereign cell involved.
    pub proofs: Vec<AtomicProofEntry>,
}

/// Errors specific to atomic sovereign turn verification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AtomicTurnError {
    /// No proof entries provided.
    EmptyProofs,
    /// A cell is not registered as sovereign.
    NotSovereign(CellId),
    /// The stored commitment does not match the entry's old_commitment.
    CommitmentMismatch {
        cell: CellId,
        expected: [u8; 32],
        got: [u8; 32],
    },
    /// A STARK proof failed verification.
    ProofFailed { cell: CellId, reason: String },
    /// Cross-cell conservation violated: balance deltas do not sum to zero.
    ConservationViolation { net_excess: i64 },
    /// Agent cell not found (for fee/nonce).
    AgentNotFound(CellId),
    /// Insufficient balance for fee.
    InsufficientFee { available: u64, required: u64 },
    /// Nonce mismatch.
    NonceMismatch { expected: u64, got: u64 },
    /// Duplicate cell in proof entries.
    DuplicateCell(CellId),
    /// A cell referenced by the atomic turn is frozen for migration (P0-4).
    FrozenCell(CellId),
    /// An action in the hosted side failed authorization (C1 fix).
    HostedAuthorizationFailed { cell: CellId, reason: String },
    /// An action in the hosted side failed preconditions or effect application.
    HostedApplyFailed { cell: CellId, reason: String },
}

impl core::fmt::Display for AtomicTurnError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyProofs => write!(f, "atomic turn has no proof entries"),
            Self::NotSovereign(id) => write!(f, "cell {} is not sovereign", id),
            Self::CommitmentMismatch {
                cell,
                expected,
                got,
            } => write!(
                f,
                "commitment mismatch for cell {}: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                cell, expected[0], expected[1], got[0], got[1]
            ),
            Self::ProofFailed { cell, reason } => {
                write!(f, "proof failed for cell {}: {}", cell, reason)
            }
            Self::ConservationViolation { net_excess } => {
                write!(
                    f,
                    "cross-cell conservation violated: net excess = {}",
                    net_excess
                )
            }
            Self::AgentNotFound(id) => write!(f, "agent cell not found: {}", id),
            Self::InsufficientFee {
                available,
                required,
            } => {
                write!(
                    f,
                    "insufficient fee: available {}, required {}",
                    available, required
                )
            }
            Self::NonceMismatch { expected, got } => {
                write!(f, "nonce mismatch: expected {}, got {}", expected, got)
            }
            Self::DuplicateCell(id) => write!(f, "duplicate cell in proof entries: {}", id),
            Self::FrozenCell(id) => {
                write!(f, "cell {} is frozen for migration", id)
            }
            Self::HostedAuthorizationFailed { cell, reason } => {
                write!(
                    f,
                    "hosted action on cell {} failed authorization: {}",
                    cell, reason
                )
            }
            Self::HostedApplyFailed { cell, reason } => {
                write!(
                    f,
                    "hosted action on cell {} failed to apply: {}",
                    cell, reason
                )
            }
        }
    }
}

impl std::error::Error for AtomicTurnError {}

impl TurnExecutor {
    /// Execute an atomic multi-party sovereign turn.
    ///
    /// This verifies ALL proofs atomically and checks cross-cell conservation:
    /// the sum of all `balance_delta` values across entries must be zero.
    ///
    /// On success, all sovereign commitments are updated simultaneously.
    /// On failure (any proof invalid or conservation violated), no state changes.
    pub fn execute_atomic_sovereign(
        &self,
        atomic_turn: &AtomicSovereignTurn,
        ledger: &mut Ledger,
    ) -> Result<Vec<[u8; 32]>, AtomicTurnError> {
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::stark;

        // 0. Basic validation.
        if atomic_turn.proofs.is_empty() {
            return Err(AtomicTurnError::EmptyProofs);
        }

        // Check for duplicate cells.
        let mut seen_cells = std::collections::HashSet::new();
        for entry in &atomic_turn.proofs {
            if !seen_cells.insert(entry.cell_id) {
                return Err(AtomicTurnError::DuplicateCell(entry.cell_id));
            }
        }

        // P0-4: reject any frozen agent or proof-entry cell.
        if self
            .cell_migrations
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .is_frozen(&atomic_turn.agent)
        {
            return Err(AtomicTurnError::FrozenCell(atomic_turn.agent));
        }
        {
            let mig = self
                .cell_migrations
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            for entry in &atomic_turn.proofs {
                if mig.is_frozen(&entry.cell_id) {
                    return Err(AtomicTurnError::FrozenCell(entry.cell_id));
                }
            }
        }

        // 1. Agent validation (fee + nonce).
        let agent_cell = ledger
            .get(&atomic_turn.agent)
            .ok_or(AtomicTurnError::AgentNotFound(atomic_turn.agent))?;
        if agent_cell.state.nonce() != atomic_turn.nonce {
            return Err(AtomicTurnError::NonceMismatch {
                expected: agent_cell.state.nonce(),
                got: atomic_turn.nonce,
            });
        }
        if agent_cell.state.balance() < atomic_turn.fee {
            return Err(AtomicTurnError::InsufficientFee {
                available: agent_cell.state.balance(),
                required: atomic_turn.fee,
            });
        }

        // 2. Verify each proof entry and extract proven balance deltas.
        let mut new_commitments: Vec<(CellId, [u8; 32])> =
            Vec::with_capacity(atomic_turn.proofs.len());
        let mut proven_deltas: Vec<i64> = Vec::with_capacity(atomic_turn.proofs.len());

        for entry in &atomic_turn.proofs {
            let stored_commitment = if let Some(c) = ledger.get_sovereign_commitment(&entry.cell_id)
            {
                *c
            } else if let Some(reg) = ledger.get_sovereign_registration(&entry.cell_id) {
                reg.commitment
            } else {
                return Err(AtomicTurnError::NotSovereign(entry.cell_id));
            };

            if entry.old_commitment != stored_commitment {
                return Err(AtomicTurnError::CommitmentMismatch {
                    cell: entry.cell_id,
                    expected: stored_commitment,
                    got: entry.old_commitment,
                });
            }

            let proof = stark::proof_from_bytes(&entry.proof).map_err(|e| {
                AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: e,
                }
            })?;

            // Stage 1: reconstruct Effect VM PI in the widened layout
            // (resolves REVIEW[effect-vm-coord]). Commitments are 4 felts
            // each; other PIs are forwarded from the proof and bound by
            // the AIR's boundary/transition constraints + the PI matching
            // loop below.
            let old_commit_4 = Self::commitment_to_4bb(&entry.old_commitment);
            let new_commit_4 = Self::commitment_to_4bb(&entry.new_commitment);

            use pyana_circuit::effect_vm::pi;
            let min_pi_count = pi::BASE_COUNT;
            if proof.public_inputs.len() < min_pi_count {
                return Err(AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: format!(
                        "proof has {} public inputs, expected at least {}",
                        proof.public_inputs.len(),
                        min_pi_count
                    ),
                });
            }

            // Forward all PI elements from the proof, then override
            // commitment slots with verifier-derived values.
            let mut public_inputs: Vec<BabyBear> = (0..min_pi_count)
                .map(|i| BabyBear::new_canonical(proof.public_inputs[i]))
                .collect();
            for i in 0..pi::OLD_COMMIT_LEN {
                public_inputs[pi::OLD_COMMIT_BASE + i] = old_commit_4[i];
            }
            for i in 0..pi::NEW_COMMIT_LEN {
                public_inputs[pi::NEW_COMMIT_BASE + i] = new_commit_4[i];
            }

            // Append custom proof entries from the proof's PIs.
            let custom_count_val = public_inputs[pi::CUSTOM_EFFECT_COUNT].0 as usize;
            for i in 0..custom_count_val {
                let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
                if base + pi::CUSTOM_ENTRY_SIZE > proof.public_inputs.len() {
                    break;
                }
                for j in 0..pi::CUSTOM_ENTRY_SIZE {
                    public_inputs.push(BabyBear::new_canonical(proof.public_inputs[base + j]));
                }
            }

            // Verify reconstructed commitment PIs match the proof's embedded PIs
            // (all 4 felts each, Stage 1 widening).
            for i in 0..pi::OLD_COMMIT_LEN {
                let proof_v = BabyBear::new_canonical(proof.public_inputs[pi::OLD_COMMIT_BASE + i]);
                if proof_v != old_commit_4[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "old_commitment in proof does not match stored value (felt {})",
                            i
                        ),
                    });
                }
            }
            for i in 0..pi::NEW_COMMIT_LEN {
                let proof_v = BabyBear::new_canonical(proof.public_inputs[pi::NEW_COMMIT_BASE + i]);
                if proof_v != new_commit_4[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "new_commitment in proof does not match claimed value (felt {})",
                            i
                        ),
                    });
                }
            }

            // Verify against custom program or default AIR (EffectVmAir).
            let vk_hash = self.get_cell_vk_hash(&entry.cell_id, ledger);
            if let Some(vk) = vk_hash {
                if let Some(program) = self.program_registry.get(&vk) {
                    program
                        .verify_transition(&public_inputs, &entry.proof)
                        .map_err(|e| AtomicTurnError::ProofFailed {
                            cell: entry.cell_id,
                            reason: e.to_string(),
                        })?;
                } else {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "cell has vk_hash {:02x}{:02x}... but no matching program",
                            vk[0], vk[1]
                        ),
                    });
                }
            } else {
                let air = pyana_circuit::EffectVmAir::new(proof.trace_len);
                stark::verify(&air, &proof, &public_inputs).map_err(|e| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: e,
                    }
                })?;
            }

            // Extract proven balance delta from PI.
            let proven_delta =
                pyana_circuit::extract_net_delta(&public_inputs).ok_or_else(|| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "failed to extract balance_delta from proof PI".to_string(),
                    }
                })?;
            proven_deltas.push(proven_delta);
            new_commitments.push((entry.cell_id, entry.new_commitment));
        }

        // 3. Conservation check using PROVEN deltas (not declared entry.balance_delta).
        let net_excess: i64 = proven_deltas.iter().sum();
        if net_excess != 0 {
            return Err(AtomicTurnError::ConservationViolation { net_excess });
        }

        // 4. All proofs verified + conservation holds. Commit atomically.
        // Deduct fee and increment nonce.
        {
            let agent = ledger.get_mut(&atomic_turn.agent).unwrap();
            agent
                .state
                .set_balance(agent.state.balance() - atomic_turn.fee);
            agent.state.increment_nonce();
        }

        // Update all sovereign commitments.
        let mut resulting_commitments = Vec::with_capacity(new_commitments.len());
        for (cell_id, new_commitment) in &new_commitments {
            if ledger.is_sovereign(cell_id) {
                let _ = ledger.update_sovereign_commitment(cell_id, *new_commitment);
            } else {
                let old = ledger
                    .get_sovereign_registration(cell_id)
                    .map(|r| r.commitment)
                    .unwrap_or([0u8; 32]);
                let _ = ledger.update_sovereign_registration_commitment(
                    cell_id,
                    old,
                    *new_commitment,
                    self.block_height,
                );
            }
            resulting_commitments.push(*new_commitment);
        }

        Ok(resulting_commitments)
    }

    /// Execute a mixed atomic turn containing both sovereign (proof-carrying) and
    /// hosted (federation-executed) cells in a single atomic operation.
    ///
    /// Conservation is enforced across BOTH: sovereign deltas (extracted from proofs)
    /// plus hosted deltas (computed from execution) must sum to zero.
    ///
    /// SECURITY (C1 fix): every hosted action's authorization is verified through
    /// the standard `verify_authorization` pipeline before any of its effects
    /// apply, and ALL hosted mutations are journaled so that any subsequent
    /// failure (auth, precondition, effect-apply, conservation) rolls back the
    /// entire turn atomically. Previously the hosted side could mutate any
    /// cell's balance without authorization.
    pub fn execute_mixed_atomic(
        &self,
        mixed_turn: &MixedAtomicTurn,
        ledger: &mut Ledger,
    ) -> Result<MixedAtomicResult, AtomicTurnError> {
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::stark;

        if mixed_turn.sovereign_entries.is_empty() && mixed_turn.hosted_actions.is_empty() {
            return Err(AtomicTurnError::EmptyProofs);
        }

        let agent_cell = ledger
            .get(&mixed_turn.agent)
            .ok_or(AtomicTurnError::AgentNotFound(mixed_turn.agent))?;
        if agent_cell.state.nonce() != mixed_turn.nonce {
            return Err(AtomicTurnError::NonceMismatch {
                expected: agent_cell.state.nonce(),
                got: mixed_turn.nonce,
            });
        }
        if agent_cell.state.balance() < mixed_turn.fee {
            return Err(AtomicTurnError::InsufficientFee {
                available: agent_cell.state.balance(),
                required: mixed_turn.fee,
            });
        }

        // P0-4: reject any frozen agent, sovereign-entry cell, or hosted-action
        // target cell.
        {
            let mig = self
                .cell_migrations
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            if mig.is_frozen(&mixed_turn.agent) {
                return Err(AtomicTurnError::FrozenCell(mixed_turn.agent));
            }
            for entry in &mixed_turn.sovereign_entries {
                if mig.is_frozen(&entry.cell_id) {
                    return Err(AtomicTurnError::FrozenCell(entry.cell_id));
                }
            }
            for action in &mixed_turn.hosted_actions {
                if mig.is_frozen(&action.target) {
                    return Err(AtomicTurnError::FrozenCell(action.target));
                }
            }
        }

        // Verify sovereign proofs and extract proven deltas.
        let mut sovereign_deltas: Vec<i64> = Vec::new();
        let mut new_commitments: Vec<(CellId, [u8; 32])> = Vec::new();

        for entry in &mixed_turn.sovereign_entries {
            let stored_commitment = if let Some(c) = ledger.get_sovereign_commitment(&entry.cell_id)
            {
                *c
            } else if let Some(reg) = ledger.get_sovereign_registration(&entry.cell_id) {
                reg.commitment
            } else {
                return Err(AtomicTurnError::NotSovereign(entry.cell_id));
            };

            if entry.old_commitment != stored_commitment {
                return Err(AtomicTurnError::CommitmentMismatch {
                    cell: entry.cell_id,
                    expected: stored_commitment,
                    got: entry.old_commitment,
                });
            }

            let proof = stark::proof_from_bytes(&entry.proof).map_err(|e| {
                AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: e,
                }
            })?;

            // Stage 1: reconstruct Effect VM PI in the widened layout
            // (resolves REVIEW[effect-vm-coord]).
            let old_commit_4 = Self::commitment_to_4bb(&entry.old_commitment);
            let new_commit_4 = Self::commitment_to_4bb(&entry.new_commitment);

            use pyana_circuit::effect_vm::pi;
            let min_pi_count = pi::BASE_COUNT;
            if proof.public_inputs.len() < min_pi_count {
                return Err(AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: format!(
                        "proof has {} public inputs, expected at least {}",
                        proof.public_inputs.len(),
                        min_pi_count
                    ),
                });
            }

            let mut public_inputs: Vec<BabyBear> = (0..min_pi_count)
                .map(|i| BabyBear::new_canonical(proof.public_inputs[i]))
                .collect();
            for i in 0..pi::OLD_COMMIT_LEN {
                public_inputs[pi::OLD_COMMIT_BASE + i] = old_commit_4[i];
            }
            for i in 0..pi::NEW_COMMIT_LEN {
                public_inputs[pi::NEW_COMMIT_BASE + i] = new_commit_4[i];
            }

            // Append custom proof entries from the proof's PIs.
            let custom_count_val = public_inputs[pi::CUSTOM_EFFECT_COUNT].0 as usize;
            for i in 0..custom_count_val {
                let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
                if base + pi::CUSTOM_ENTRY_SIZE > proof.public_inputs.len() {
                    break;
                }
                for j in 0..pi::CUSTOM_ENTRY_SIZE {
                    public_inputs.push(BabyBear::new_canonical(proof.public_inputs[base + j]));
                }
            }

            // Verify commitment PIs match (4 felts each).
            for i in 0..pi::OLD_COMMIT_LEN {
                let proof_v = BabyBear::new_canonical(proof.public_inputs[pi::OLD_COMMIT_BASE + i]);
                if proof_v != old_commit_4[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "old_commitment in proof does not match stored value (felt {})",
                            i
                        ),
                    });
                }
            }
            for i in 0..pi::NEW_COMMIT_LEN {
                let proof_v = BabyBear::new_canonical(proof.public_inputs[pi::NEW_COMMIT_BASE + i]);
                if proof_v != new_commit_4[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "new_commitment in proof does not match claimed value (felt {})",
                            i
                        ),
                    });
                }
            }

            // Verify against custom program or default EffectVmAir.
            let vk_hash = self.get_cell_vk_hash(&entry.cell_id, ledger);
            if let Some(vk) = vk_hash {
                if let Some(program) = self.program_registry.get(&vk) {
                    program
                        .verify_transition(&public_inputs, &entry.proof)
                        .map_err(|e| AtomicTurnError::ProofFailed {
                            cell: entry.cell_id,
                            reason: e.to_string(),
                        })?;
                } else {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "program not found for vk_hash".to_string(),
                    });
                }
            } else {
                let air = pyana_circuit::EffectVmAir::new(proof.trace_len);
                stark::verify(&air, &proof, &public_inputs).map_err(|e| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: e,
                    }
                })?;
            }

            let proven_delta =
                pyana_circuit::extract_net_delta(&public_inputs).ok_or_else(|| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "failed to extract balance_delta from proof PI".to_string(),
                    }
                })?;
            sovereign_deltas.push(proven_delta);
            new_commitments.push((entry.cell_id, entry.new_commitment));
        }

        // ====================================================================
        // HOSTED SIDE (C1 FIX): each hosted action is authorized via the same
        // `verify_authorization` pipeline as `execute()` and applied through
        // `apply_effect` with full journaling. On any failure (auth,
        // precondition, effect, conservation) the entire journal is rolled
        // back -- no partial state is left in the ledger.
        // ====================================================================
        let mut journal = LedgerJournal::with_capacity(16);
        let mut hosted_deltas: Vec<i64> = Vec::with_capacity(mixed_turn.hosted_actions.len());

        for (idx, action) in mixed_turn.hosted_actions.iter().enumerate() {
            // 1. Target cell must exist.
            let target_cell = match ledger.get(&action.target) {
                Some(c) => c.clone(),
                None => {
                    journal.rollback(
                        ledger,
                        &self.obligations,
                        &self.escrows,
                        &self.bridged_nullifiers,
                        &self.note_nullifiers,
                        &self.committed_escrows,
                        &self.committed_escrow_amounts,
                    );
                    return Err(AtomicTurnError::HostedApplyFailed {
                        cell: action.target,
                        reason: format!("hosted action #{} target cell not found", idx),
                    });
                }
            };

            // 2. Authorization (the C1 fix). Use the same gate as `execute()`.
            let path = vec![idx];
            if let Err((err, _path)) = self.verify_authorization(
                action,
                &target_cell,
                ledger,
                &mixed_turn.agent,
                &path,
                mixed_turn.nonce,
            ) {
                journal.rollback(
                    ledger,
                    &self.obligations,
                    &self.escrows,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.committed_escrows,
                    &self.committed_escrow_amounts,
                );
                return Err(AtomicTurnError::HostedAuthorizationFailed {
                    cell: action.target,
                    reason: format!("{err}"),
                });
            }

            // 3. Preconditions.
            if let Err((err, _)) = self.check_preconditions(action, &target_cell, &path) {
                journal.rollback(
                    ledger,
                    &self.obligations,
                    &self.escrows,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.committed_escrows,
                    &self.committed_escrow_amounts,
                );
                return Err(AtomicTurnError::HostedApplyFailed {
                    cell: action.target,
                    reason: format!("{err}"),
                });
            }

            // 4. Apply each effect via apply_effect (which is journaled).
            // Compute the net Transfer delta for this hosted entry for the
            // conservation check after-the-fact.
            let mut net_delta: i64 = 0;
            for effect in &action.effects {
                if let crate::action::Effect::Transfer { from, to, amount } = effect {
                    if from == &action.target {
                        net_delta -= *amount as i64;
                    }
                    if to == &action.target {
                        net_delta += *amount as i64;
                    }
                }
                if let Err((err, _)) = self.apply_effect(
                    effect,
                    ledger,
                    &path,
                    &action.target,
                    &mixed_turn.agent,
                    &mut journal,
                ) {
                    journal.rollback(
                        ledger,
                        &self.obligations,
                        &self.escrows,
                        &self.bridged_nullifiers,
                        &self.note_nullifiers,
                        &self.committed_escrows,
                        &self.committed_escrow_amounts,
                    );
                    return Err(AtomicTurnError::HostedApplyFailed {
                        cell: action.target,
                        reason: format!("{err}"),
                    });
                }
            }
            hosted_deltas.push(net_delta);
        }

        // Cross-domain conservation: sovereign + hosted must sum to zero.
        let total_delta: i64 =
            sovereign_deltas.iter().sum::<i64>() + hosted_deltas.iter().sum::<i64>();
        if total_delta != 0 {
            // Roll back ALL hosted mutations before returning.
            journal.rollback(
                ledger,
                &self.obligations,
                &self.escrows,
                &self.bridged_nullifiers,
                &self.note_nullifiers,
                &self.committed_escrows,
                &self.committed_escrow_amounts,
            );
            return Err(AtomicTurnError::ConservationViolation {
                net_excess: total_delta,
            });
        }

        // ====================================================================
        // COMMIT: hosted mutations are already in place (in `ledger`) via
        // apply_effect; we just commit fee, nonce, and sovereign commitment
        // updates. We deliberately do NOT call rollback on the journal -- we
        // want to keep the mutations; the journal is dropped on success.
        // ====================================================================
        {
            let agent = ledger.get_mut(&mixed_turn.agent).unwrap();
            agent
                .state
                .set_balance(agent.state.balance() - mixed_turn.fee);
            agent.state.increment_nonce();
        }

        for (cell_id, new_commitment) in &new_commitments {
            if ledger.is_sovereign(cell_id) {
                let _ = ledger.update_sovereign_commitment(cell_id, *new_commitment);
            } else {
                let old = ledger
                    .get_sovereign_registration(cell_id)
                    .map(|r| r.commitment)
                    .unwrap_or([0u8; 32]);
                let _ = ledger.update_sovereign_registration_commitment(
                    cell_id,
                    old,
                    *new_commitment,
                    self.block_height,
                );
            }
        }

        Ok(MixedAtomicResult {
            sovereign_commitments: new_commitments.iter().map(|(_, c)| *c).collect(),
            sovereign_deltas,
            hosted_deltas,
        })
    }
}
// =============================================================================
// Adversarial Tests for CRITICAL/P0 fixes (C1, P0-3, P0-4)
// =============================================================================

#[cfg(test)]
mod hardening_tests {
    use super::*;
    use crate::action::{Action, Authorization, DelegationMode, Effect};
    use crate::forest::{CallForest, CallTree};
    use crate::turn::Turn;
    use crate::{ComputronCosts, TurnError, TurnResult};
    use pyana_cell::permissions::{AuthRequired, Permissions};
    use pyana_cell::{Cell, Preconditions};

    fn permissive() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    fn make_permissive_cell(seed: u8, balance: u64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        let token = [0u8; 32];
        let mut cell = Cell::with_balance(pk, token, balance);
        cell.permissions = permissive();
        cell
    }

    fn make_signed_cell(seed: u8, balance: u64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        let token = [0u8; 32];
        // Default permissions: Signature required.
        Cell::with_balance(pk, token, balance)
    }

    fn build_noop_turn(agent: CellId, nonce: u64) -> Turn {
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };
        Turn {
            agent,
            nonce,
            call_forest: CallForest {
                roots: vec![tree],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    // ---------------- P0-3: previous_receipt_hash enforcement ----------------

    /// Submit two turns with the same nonce=0 and `previous_receipt_hash: None`.
    /// The second MUST be rejected -- without the P0-3 fix the executor would
    /// accept both because it never bound the receipt chain at write time.
    #[test]
    fn previous_receipt_hash_replay_blocked() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let turn1 = build_noop_turn(agent_id, 0);
        let r1 = executor.execute(&turn1, &mut ledger);
        assert!(r1.is_committed(), "first turn should commit: {:?}", r1);

        // Second turn from same agent with previous_receipt_hash: None.
        // Reset nonce by building with nonce 1 (which is the actual next nonce).
        let turn2 = build_noop_turn(agent_id, 1);
        let r2 = executor.execute(&turn2, &mut ledger);
        match r2 {
            TurnResult::Rejected {
                reason: TurnError::ReceiptChainMismatch { expected, got },
                ..
            } => {
                assert!(expected.is_some(), "expected = Some(prev_receipt_hash)");
                assert!(got.is_none(), "got = None (the bug pattern)");
            }
            other => panic!("expected ReceiptChainMismatch, got: {:?}", other),
        }
    }

    /// Submit a non-genesis turn whose `previous_receipt_hash` doesn't match
    /// the prior receipt -- MUST be rejected (no rebranching the chain).
    #[test]
    fn previous_receipt_hash_wrong_chain_rejected() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let turn1 = build_noop_turn(agent_id, 0);
        let r1 = executor.execute(&turn1, &mut ledger);
        assert!(r1.is_committed());

        // Build turn2 with WRONG previous_receipt_hash.
        let mut turn2 = build_noop_turn(agent_id, 1);
        turn2.previous_receipt_hash = Some([0xAB; 32]);
        let r2 = executor.execute(&turn2, &mut ledger);
        match r2 {
            TurnResult::Rejected {
                reason: TurnError::ReceiptChainMismatch { expected, got },
                ..
            } => {
                assert!(expected.is_some());
                assert_eq!(got, Some([0xAB; 32]));
            }
            other => panic!("expected ReceiptChainMismatch, got: {:?}", other),
        }
    }

    /// Properly chained sequential turns MUST commit.
    #[test]
    fn previous_receipt_hash_correct_chain_accepted() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let turn1 = build_noop_turn(agent_id, 0);
        let (_, receipt1, _) = executor.execute(&turn1, &mut ledger).unwrap_committed();

        let mut turn2 = build_noop_turn(agent_id, 1);
        turn2.previous_receipt_hash = Some(receipt1.receipt_hash());
        let r2 = executor.execute(&turn2, &mut ledger);
        assert!(
            r2.is_committed(),
            "correctly-chained turn must commit: {:?}",
            r2
        );
    }

    /// A turn that claims a prior receipt when the executor has none on file
    /// MUST be rejected (a cclerk can't fake an established chain).
    #[test]
    fn previous_receipt_hash_genesis_with_some_rejected() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let mut turn = build_noop_turn(agent_id, 0);
        turn.previous_receipt_hash = Some([0x42; 32]);
        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::ReceiptChainMismatch { expected, got },
                ..
            } => {
                assert!(expected.is_none(), "executor has no prior receipt");
                assert_eq!(got, Some([0x42; 32]));
            }
            other => panic!("expected ReceiptChainMismatch, got: {:?}", other),
        }
    }

    // ---------------- P0-4: CellMigrationManager enforcement ----------------

    /// A turn whose agent cell is frozen for migration MUST be rejected.
    #[test]
    fn migration_frozen_agent_blocks_execute() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Freeze the agent cell for migration.
        executor
            .cell_migrations
            .lock()
            .unwrap()
            .begin_migration(agent_id, [0xDD; 32], 0, 100)
            .unwrap();

        let turn = build_noop_turn(agent_id, 0);
        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::CellFrozen { cell },
                ..
            } => assert_eq!(cell, agent_id),
            other => panic!("expected CellFrozen, got: {:?}", other),
        }
    }

    /// A turn that transfers TO a frozen cell MUST be rejected.
    #[test]
    fn migration_frozen_target_blocks_transfer() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 10_000);
        let agent_id = agent.id();
        let target = make_permissive_cell(2, 0);
        let target_id = target.id();
        // Grant agent capability to target so cross-cell check passes.
        let mut a = agent;
        a.capabilities.grant(target_id, AuthRequired::None);
        ledger.insert_cell(a).unwrap();
        ledger.insert_cell(target).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .cell_migrations
            .lock()
            .unwrap()
            .begin_migration(target_id, [0xDD; 32], 0, 100)
            .unwrap();

        // Build a transfer turn (agent -> target).
        let action = Action {
            target: agent_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 100,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };
        let mut turn = build_noop_turn(agent_id, 0);
        turn.call_forest = CallForest {
            roots: vec![tree],
            forest_hash: [0u8; 32],
        };
        turn.fee = 0;

        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::CellFrozen { cell },
                ..
            } => assert_eq!(cell, target_id),
            other => panic!("expected CellFrozen(target), got: {:?}", other),
        }
    }

    /// `execute_atomic_sovereign` MUST reject when a sovereign-entry cell is
    /// frozen.
    #[test]
    fn migration_frozen_blocks_atomic_sovereign() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        let frozen_id = CellId([0xCC; 32]);
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .cell_migrations
            .lock()
            .unwrap()
            .begin_migration(frozen_id, [0xDD; 32], 0, 100)
            .unwrap();

        let atomic = AtomicSovereignTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            proofs: vec![AtomicProofEntry {
                cell_id: frozen_id,
                proof: vec![1, 2, 3, 4],
                old_commitment: [0u8; 32],
                new_commitment: [1u8; 32],
                effects_hash: [0u8; 32],
                balance_delta: 0,
            }],
        };

        let r = executor.execute_atomic_sovereign(&atomic, &mut ledger);
        match r {
            Err(AtomicTurnError::FrozenCell(cell)) => assert_eq!(cell, frozen_id),
            other => panic!("expected FrozenCell, got: {:?}", other),
        }
    }

    // ---------------- CRITICAL C1: execute_mixed_atomic auth ----------------

    /// The CRITICAL fix: a hosted action targeting a cell the caller has no
    /// authority over MUST be rejected by `execute_mixed_atomic`. Without the
    /// fix, the call would mutate the target cell's balance.
    #[test]
    fn mixed_atomic_hosted_unauthorized_rejected() {
        let mut ledger = Ledger::new();
        // Agent (attacker) and victim cell both exist; victim REQUIRES Signature.
        let agent = make_permissive_cell(0xAA, 1000);
        let agent_id = agent.id();
        let victim = make_signed_cell(0xBB, 1000);
        let victim_id = victim.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(victim.clone()).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Attacker constructs a hosted action that targets the victim cell but
        // provides `Authorization::Unchecked` (no signature). The victim cell's
        // default permissions require Signature for SetField; verify_authorization
        // MUST reject.
        let malicious_action = Action {
            target: victim_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: victim_id,
                index: 0,
                value: [0xFF; 32],
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![malicious_action],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(
            matches!(r, Err(AtomicTurnError::HostedAuthorizationFailed { cell, .. }) if cell == victim_id),
            "expected HostedAuthorizationFailed on victim cell, got: {:?}",
            r
        );

        // Victim's state MUST be unchanged.
        let v = ledger.get(&victim_id).unwrap();
        assert_eq!(v.state.fields[0], pyana_cell::state::FIELD_ZERO);
    }

    /// C1 / P1-7: a later hosted-action failure MUST roll back earlier hosted
    /// mutations within the same `execute_mixed_atomic` call.
    #[test]
    fn mixed_atomic_late_failure_rolls_back_hosted_mutations() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xAA, 100);
        let agent_id = agent.id();
        let cell_b = make_permissive_cell(0xBB, 1_000);
        let cell_b_id = cell_b.id();
        let cell_c = make_permissive_cell(0xCC, 50);
        let cell_c_id = cell_c.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(cell_b).unwrap();
        ledger.insert_cell(cell_c).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Action 1: B sends 100 to C (succeeds; both permissive).
        let a1 = Action {
            target: cell_b_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_b_id,
                to: cell_c_id,
                amount: 100,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        // Action 2: C sends 999_999 to B (FAILS: insufficient balance after first
        // action). Journal MUST roll back action 1.
        let a2 = Action {
            target: cell_c_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_c_id,
                to: cell_b_id,
                amount: 999_999,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![a1, a2],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(r.is_err(), "expected late failure, got: {:?}", r);

        // Balances MUST be unchanged (rollback worked).
        assert_eq!(ledger.get(&cell_b_id).unwrap().state.balance(), 1_000);
        assert_eq!(ledger.get(&cell_c_id).unwrap().state.balance(), 50);
    }

    /// P2-2: set_timestamp MUST silently ignore backwards-in-time updates.
    #[test]
    fn set_timestamp_backwards_no_op() {
        let mut executor = TurnExecutor::new(ComputronCosts::zero());
        executor.set_timestamp(100);
        assert_eq!(executor.current_timestamp, 100);
        executor.set_timestamp(50); // backwards
        assert_eq!(executor.current_timestamp, 100, "must not go backwards");
        executor.set_timestamp(100); // same
        assert_eq!(executor.current_timestamp, 100);
        executor.set_timestamp(200); // forward
        assert_eq!(executor.current_timestamp, 200);
    }

    /// A hosted Transfer from a victim's cell MUST be rejected (the attacker
    /// has no Signature for the victim's Send permission).
    #[test]
    fn mixed_atomic_hosted_unauthorized_transfer_blocked() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xAA, 100);
        let agent_id = agent.id();
        let victim = make_signed_cell(0xBB, 10_000);
        let victim_id = victim.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(victim).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Malicious hosted action: transfer from victim -> agent.
        let action = Action {
            target: victim_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: victim_id,
                to: agent_id,
                amount: 5_000,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![action],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(matches!(
            r,
            Err(AtomicTurnError::HostedAuthorizationFailed { .. })
        ));

        // Both balances UNCHANGED.
        assert_eq!(ledger.get(&victim_id).unwrap().state.balance(), 10_000);
        assert_eq!(ledger.get(&agent_id).unwrap().state.balance(), 100);
    }

    // ---------------- R-4: executor_signature actually populated -----------
    //
    // EFFECT-VM-SHAPE-A.md R-4: previously TurnReceipt.executor_signature was
    // never set, so the federation-exit path could not authenticate receipts
    // as having come from a known executor. These tests pin the new behavior:
    //
    //   1. Without a signing key configured, receipts keep the legacy None.
    //   2. With a signing key configured (via `with_executor_signing_key`),
    //      every committed receipt is signed over receipt_hash().
    //   3. The signature verifies under the executor's matching public key
    //      and is rejected under any other key.

    #[test]
    fn executor_signature_default_none() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(7, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let turn = build_noop_turn(agent_id, 0);
        let result = executor.execute(&turn, &mut ledger);
        match result {
            TurnResult::Committed { receipt, .. } => {
                assert!(
                    receipt.executor_signature.is_none(),
                    "without with_executor_signing_key, executor_signature must remain None"
                );
            }
            other => panic!("expected Committed, got {:?}", other),
        }
    }

    #[test]
    fn executor_signature_populated_and_verifies() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(11, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        // Deterministic key seed for the test.
        let seed: [u8; 32] = *b"pyana-test-executor-sk-r4-fix!!!";
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);
        let pk_bytes = sk.verifying_key().to_bytes();

        let executor = TurnExecutor::new(ComputronCosts::zero()).with_executor_signing_key(seed);
        let turn = build_noop_turn(agent_id, 0);

        let result = executor.execute(&turn, &mut ledger);
        let receipt = match result {
            TurnResult::Committed { receipt, .. } => receipt,
            other => panic!("expected Committed, got {:?}", other),
        };

        // Signature is present and exactly 64 bytes.
        let sig_bytes = receipt
            .executor_signature
            .as_ref()
            .expect("executor_signature must be populated when signing key configured");
        assert_eq!(sig_bytes.len(), 64);

        // Chain verification accepts the receipt under the matching key.
        crate::verify::verify_receipt_chain_with_keys(&[receipt.clone()], &[pk_bytes])
            .expect("receipt chain must verify under the executor's public key");

        // ...and rejects it under any other key.
        let mut wrong_key = pk_bytes;
        wrong_key[0] ^= 0x80;
        let err = crate::verify::verify_receipt_chain_with_keys(&[receipt], &[wrong_key])
            .expect_err("verification must fail under a foreign key");
        assert!(
            matches!(
                err,
                crate::verify::VerifyError::ExecutorSignatureInvalid { .. }
            ),
            "expected ExecutorSignatureInvalid, got {:?}",
            err
        );
    }

    // =========================================================================
    // Lane-2 honesty sweep: adversarial tests for Authorization::OneOf and
    // Effect::Refusal. Pre-sweep, the structural primitives existed but no
    // executor-side test ever constructed them, so the defensive cascade
    // (executor.rs ~5812 for OneOf; the new Refusal-vs-mutation guard) was
    // dead code from a coverage standpoint.
    // =========================================================================

    use crate::action::RefusalReason;

    /// Build a single-action turn whose action carries `authorization`
    /// and the given `effects`. Target is the agent itself; no
    /// preconditions; permissive cell so authorization is the only
    /// gate the executor checks.
    fn build_single_action_turn(
        agent: CellId,
        nonce: u64,
        authorization: Authorization,
        effects: Vec<Effect>,
    ) -> Turn {
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization,
            preconditions: Preconditions::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };
        Turn {
            agent,
            nonce,
            call_forest: CallForest {
                roots: vec![tree],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// `Authorization::OneOf { candidates, proof_index }` with `proof_index`
    /// past the end of `candidates` MUST be rejected with an
    /// `InvalidAuthorization` whose reason mentions "out of bounds".
    /// Pins the defensive cascade at executor.rs ~5818.
    #[test]
    fn one_of_rejects_out_of_bounds_proof_index() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0x71, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // 1 candidate, proof_index=5 -> out of bounds.
        let auth = Authorization::OneOf {
            candidates: vec![Authorization::Signature([0u8; 32], [0u8; 32])],
            proof_index: 5,
        };
        let turn = build_single_action_turn(agent_id, 0, auth, vec![]);

        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::InvalidAuthorization { reason },
                ..
            } => {
                assert!(
                    reason.contains("out of bounds"),
                    "expected reason to mention 'out of bounds', got: {reason}"
                );
            }
            other => panic!(
                "expected InvalidAuthorization (out of bounds), got: {:?}",
                other
            ),
        }
    }

    /// `Authorization::OneOf` whose indexed candidate is
    /// `Authorization::Unchecked` MUST be rejected — `OneOf` must not
    /// reduce to an auth-bypass-by-naming-Unchecked surface.
    /// Pins the defensive cascade at executor.rs ~5833.
    #[test]
    fn one_of_rejects_unchecked_indexed_slot() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0x72, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Candidates: [Unchecked, Signature]; indexed slot 0 is Unchecked.
        let auth = Authorization::OneOf {
            candidates: vec![
                Authorization::Unchecked,
                Authorization::Signature([0u8; 32], [0u8; 32]),
            ],
            proof_index: 0,
        };
        let turn = build_single_action_turn(agent_id, 0, auth, vec![]);

        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::InvalidAuthorization { reason },
                ..
            } => {
                assert!(
                    reason.contains("Unchecked"),
                    "expected reason to mention 'Unchecked', got: {reason}"
                );
            }
            other => panic!(
                "expected InvalidAuthorization (Unchecked indexed slot), got: {:?}",
                other
            ),
        }
    }

    /// An action that carries both `Effect::Refusal { cell, .. }` and
    /// `Effect::SetField { cell, .. }` on the SAME cell MUST be rejected
    /// with `RefusalConflictsWithMutation`. Refusal is "evidence of
    /// non-action" — it cannot coexist with a real state mutation
    /// on the same target within a single action.
    #[test]
    fn refusal_conflicts_with_set_field_on_same_cell() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0x73, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let refusal = Effect::Refusal {
            cell: agent_id,
            offered_action_commitment: [0xAB; 32],
            refusal_reason: RefusalReason::Declined,
            proof_witness_index: 0,
        };
        let set_field = Effect::SetField {
            cell: agent_id,
            index: 0,
            value: [0xCD; 32],
        };

        let turn = build_single_action_turn(
            agent_id,
            0,
            Authorization::Unchecked,
            vec![refusal, set_field],
        );

        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason:
                    TurnError::RefusalConflictsWithMutation {
                        cell,
                        ref conflicting_effect,
                    },
                ..
            } => {
                assert_eq!(cell, agent_id);
                assert_eq!(conflicting_effect, "SetField");
            }
            other => panic!("expected RefusalConflictsWithMutation, got: {:?}", other),
        }

        // Agent's slot[0] MUST remain at FIELD_ZERO -- the entire action
        // was rejected closed, no mutation applied.
        assert_eq!(
            ledger.get(&agent_id).unwrap().state.fields[0],
            pyana_cell::state::FIELD_ZERO
        );
    }
}
