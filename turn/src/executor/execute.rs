//! Top-level turn execution: `execute()`, `wrap_witnessed`, `estimate_cost`, `validate_without_apply`.
//!
//! Extracted from `executor/mod.rs` (lines 2994-3812 of pre-decomposition file).

use super::*;

/// Common helper for fee share distribution (50% proposer, 30% treasury, 20% burned).
/// Extracted to eliminate duplication between proof-carrying sovereign fast path
/// and normal forest path (excellence item from conservation followup).
/// Ensures consistent credit timing and logic for post_state_hash / receipt / delta / AR consumers.
fn distribute_fee_shares(
    ledger: &mut Ledger,
    proposer: Option<&CellId>,
    treasury: Option<&CellId>,
    fee: u64,
) {
    let proposer_share = fee / 2;
    let treasury_share = fee * 3 / 10;
    if let Some(pid) = proposer {
        if let Some(p) = ledger.get_mut(pid) {
            p.state.set_balance(p.state.balance() + proposer_share);
        }
        // missing cell => burned (documented)
    }
    if let Some(tid) = treasury {
        if let Some(t) = ledger.get_mut(tid) {
            t.state.set_balance(t.state.balance() + treasury_share);
        }
        // missing cell => burned
    }
}

fn is_zero_hash(bytes: &[u8; 32]) -> bool {
    bytes.iter().all(|b| *b == 0)
}

impl TurnExecutor {
    /// Execute a turn against a ledger, returning the result.
    ///
    /// This is the main entry point. The executor:
    /// 1. Validates turn-level conditions (expiration, nonce, fee).
    /// 2. Creates a journal for efficient rollback (no full ledger clone).
    /// 3. Walks the call forest depth-first.
    /// 4. For each action: checks preconditions, verifies authorization, applies effects.
    /// 5. Meters computrons at each step.
    /// 6. If any action fails: replays journal in reverse to roll back ALL effects.
    /// 7. If successful: produces a TurnReceipt with Merkle hashes.
    /// TRUST-CRITICAL: This function is the sole entry point for all ledger state mutations.
    /// If compromised: arbitrary state changes bypass authorization, preconditions, and fee metering.
    /// The federation's replicated execution ensures all members execute identically; divergence
    /// triggers consensus failure and halts the federation.
    /// Future: once Effect VM covers all effect types, every turn will carry a STARK proof,
    /// making this function a thin verify-and-commit wrapper (trustless).
    pub fn execute(&self, turn: &Turn, ledger: &mut Ledger) -> TurnResult {
        // Phase 0: basic validation.
        if turn.call_forest.is_empty() {
            return TurnResult::Rejected {
                reason: TurnError::EmptyForest,
                at_action: vec![],
            };
        }

        // Check expiration.
        if let Some(valid_until) = turn.valid_until {
            if self.current_timestamp > valid_until {
                return TurnResult::Rejected {
                    reason: TurnError::Expired {
                        valid_until,
                        now: self.current_timestamp,
                    },
                    at_action: vec![],
                };
            }
        }

        // Check agent cell exists.
        let agent_cell = match ledger.get(&turn.agent) {
            Some(cell) => cell,
            None => {
                return TurnResult::Rejected {
                    reason: TurnError::CellNotFound { id: turn.agent },
                    at_action: vec![],
                };
            }
        };

        // Check nonce.
        if agent_cell.state.nonce() != turn.nonce {
            return TurnResult::Rejected {
                reason: TurnError::NonceReplay {
                    expected: agent_cell.state.nonce(),
                    got: turn.nonce,
                },
                at_action: vec![],
            };
        }

        // Check fee coverage (agent must have enough balance for the fee).
        if agent_cell.state.balance() < turn.fee {
            return TurnResult::Rejected {
                reason: TurnError::InsufficientBalance {
                    cell: turn.agent,
                    required: turn.fee,
                    available: agent_cell.state.balance(),
                },
                at_action: vec![],
            };
        }

        // P0-4: Reject turns whose agent cell is frozen for migration. A frozen
        // cell may not initiate any turn.
        if let Err(e) = self.check_not_frozen(&turn.agent) {
            return TurnResult::Rejected {
                reason: e,
                at_action: vec![],
            };
        }
        // Also reject if any cell touched in the call-forest write set is
        // frozen. Per-effect freezing checks are also applied inside
        // `apply_effect` as defence in depth.
        {
            let (_read_set, write_set) = crate::conflict::extract_access_sets(turn);
            for cell_id in &write_set {
                if let Err(e) = self.check_not_frozen(cell_id) {
                    return TurnResult::Rejected {
                        reason: e,
                        at_action: vec![],
                    };
                }
            }
        }

        // P0-3: Receipt-chain self-binding. The agent's claimed
        // `previous_receipt_hash` must match the executor's stored head for
        // this agent. Genesis turns (the agent's first) must use `None`.
        //
        // REVIEW[cclerk-coord]: AUDIT-cclerk.md P3-6 reports that
        // `build_authorized_turn`, `allocate_queue`, `enqueue_message`,
        // `dequeue_message`, and `atomic_queue_tx` all hardcode
        // `previous_receipt_hash: None`. After this fix, every non-first turn
        // from those paths will be rejected with `ReceiptChainMismatch`. The
        // cclerk must be updated to plumb the prior receipt hash (track per
        // agent, populate on build, advance on commit). This check should NOT
        // be relaxed; the cclerk is the side that needs to catch up.
        if let Err(e) = self.check_previous_receipt_hash(&turn.agent, turn.previous_receipt_hash) {
            return TurnResult::Rejected {
                reason: e,
                at_action: vec![],
            };
        }

        // =====================================================================
        // BUDGET GATE: Check silo's bounded-counter slice (Stingray).
        // BEFORE Phase 1 — if the silo's budget slice cannot cover the turn fee,
        // reject without charging the agent (pre-flight check). The budget gate is
        // a silo-level resource limit: exhaustion is not the agent's fault.
        // On subsequent forest failure (Phase 2), the debit is refunded (fast unlock).
        // =====================================================================
        let budget_debit_digest = if let Some(gate_cell) = &self.budget_gate {
            let turn_hash = turn.hash();
            let mut gate = gate_cell.lock().unwrap();
            match gate.try_debit(turn.fee, &turn_hash) {
                Ok(digest) => Some((digest, turn.fee)),
                Err(remaining) => {
                    return TurnResult::Rejected {
                        reason: TurnError::BudgetExhausted {
                            silo_id: gate.silo_id,
                            requested: turn.fee,
                            remaining,
                        },
                        at_action: vec![],
                    };
                }
            }
        } else {
            None
        };

        // Compute pre-state hash before any mutations.
        let pre_state_hash = ledger.root();

        // =====================================================================
        // PHASE 1: Commit fee + nonce (NEVER rolled back).
        // This prevents DoS via expensive-but-failing turns that never pay.
        // =====================================================================
        {
            let agent = ledger.get_mut(&turn.agent).unwrap();
            agent.state.set_balance(agent.state.balance() - turn.fee);
            if !agent.state.increment_nonce() {
                return TurnResult::Rejected {
                    reason: TurnError::NonceOverflow { cell: turn.agent },
                    at_action: vec![],
                };
            }
        }

        // =====================================================================
        // PHASE 3: PROOF-CARRYING SOVEREIGN TURN (fastest path)
        // When execution_proof is present, the executor does ZERO state
        // manipulation. It verifies the STARK proof and updates one 32-byte
        // commitment. This makes sovereign cells scalable — constant work
        // regardless of internal state complexity.
        // =====================================================================
        if let Some(proof_bytes) = &turn.execution_proof {
            let cell_id = match &turn.execution_proof_cell {
                Some(id) => *id,
                None => {
                    // Refund budget debit if we short-circuit.
                    if let (Some(gate_cell), Some((digest, fee))) =
                        (&self.budget_gate, &budget_debit_digest)
                    {
                        gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                    }
                    return TurnResult::Rejected {
                        reason: TurnError::InvalidExecutionProof(
                            "execution_proof present but execution_proof_cell is None".to_string(),
                        ),
                        at_action: vec![],
                    };
                }
            };

            // Check that the cell is sovereign (either in sovereign_commitments or sovereign_registrations).
            if !ledger.is_sovereign(&cell_id) && !ledger.is_sovereign_registered(&cell_id) {
                if let (Some(gate_cell), Some((digest, fee))) =
                    (&self.budget_gate, &budget_debit_digest)
                {
                    gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                }
                return TurnResult::Rejected {
                    reason: TurnError::ProofCarryingRequiresSovereign { cell: cell_id },
                    at_action: vec![],
                };
            }

            match self.verify_and_commit_proof(&cell_id, proof_bytes, turn, ledger) {
                Ok(()) => {
                    // Budget gate: commit the debit after successful proof verification.
                    if let (Some(gate_cell), Some((digest, _fee))) =
                        (&self.budget_gate, &budget_debit_digest)
                    {
                        gate_cell.lock().unwrap().commit_debit(digest);
                    }

                    // Fee distribution via common helper (extracted for consistency).
                    // Now called before post_state_hash + receipt + delta in proof path too.
                    distribute_fee_shares(
                        ledger,
                        self.proposer_cell.as_ref(),
                        self.treasury_cell.as_ref(),
                        turn.fee,
                    );

                    let post_state_hash = ledger.root();
                    let turn_hash = turn.hash();
                    let forest_hash = turn.call_forest.compute_hash();

                    // Audit P0 #78: the proof-carrying path previously emitted a
                    // stub receipt with `effects_hash = H(&[])`,
                    // `computrons_used = 0`, `action_count = 0` even when the
                    // attested transition was non-trivial. Receipt observers
                    // would then see no relation between the receipt and what
                    // the proof actually adjudicated.
                    //
                    // The proof verifier (`verify_and_commit_proof`) binds the
                    // canonical effects_hash (4 BabyBear felts derived from the
                    // turn's effects) into the PI vector and checks that PI
                    // matches the proof, so the proof attests to the same
                    // effects the executor sees here. We therefore recompute
                    // the receipt's BLAKE3 effects_hash from the turn's
                    // call_forest (it's what `verify_and_commit_proof` keyed
                    // its bound effects_hash to), and we report
                    // `action_count` from the call_forest. `computrons_used`
                    // is reported as the proof-carrying base cost — the proof
                    // path bypasses the per-effect execute loop, so the only
                    // honest non-zero "work" attestable here is the executor's
                    // proof-verification budget (proxied via the action_count
                    // weighted base cost — keeps the field load-bearing for
                    // metering verifiers without claiming work that wasn't
                    // measured).
                    let mut effect_hashes: Vec<[u8; 32]> = Vec::new();
                    fn collect_effect_hashes(
                        tree: &crate::forest::CallTree,
                        out: &mut Vec<[u8; 32]>,
                    ) {
                        for effect in &tree.action.effects {
                            out.push(crate::action::Effect::hash(effect));
                        }
                        for child in &tree.children {
                            collect_effect_hashes(child, out);
                        }
                    }
                    for root in &turn.call_forest.roots {
                        collect_effect_hashes(root, &mut effect_hashes);
                    }
                    let effects_hash = self.compute_effects_hash(&effect_hashes);
                    let action_count = turn.call_forest.action_count();
                    // Proof-verification budget proxy: charge one effect_base
                    // computron per declared action so the receipt's
                    // `computrons_used` is at least monotone in the size of
                    // the attested turn body. The proof itself bears the
                    // soundness; this field exists for metering / observability.
                    let computrons_used =
                        self.costs.effect_base.saturating_mul(action_count as u64);

                    let mut receipt = TurnReceipt {
                        turn_hash,
                        forest_hash,
                        pre_state_hash,
                        post_state_hash,
                        timestamp: self.current_timestamp,
                        effects_hash,
                        computrons_used,
                        action_count,
                        previous_receipt_hash: turn.previous_receipt_hash,
                        agent: turn.agent,
                        federation_id: self.local_federation_id,
                        routing_directives: vec![],
                        introduction_exports: vec![],
                        derivation_records: vec![],
                        emitted_events: vec![],
                        executor_signature: None,
                        finality: crate::turn::Finality::Final,
                        // Cleartext path: encrypted-path callers
                        // (`apply_encrypted_turn`) flip this on after the inner
                        // `execute` returns. We can't know here whether we were
                        // entered via an EncryptedTurn wrapper.
                        was_encrypted: false,
                        was_burn: Self::forest_carries_burn(&turn.call_forest),
                    };
                    // R-4: sign the receipt over its canonical hash if the
                    // executor has been configured with a signing key.
                    receipt.executor_signature = self.maybe_sign_receipt(&receipt);

                    let mut delta = dregg_cell::LedgerDelta::new();
                    let mut agent_delta = dregg_cell::CellStateDelta::empty();
                    agent_delta.balance_change = -(turn.fee as i64);
                    agent_delta.nonce_increment = true;
                    delta.updated.push((turn.agent, agent_delta));

                    // Include fee share credits in delta (to match normal path's
                    // compute_delta_from_journal_with_fee which receives the
                    // proposer/treasury cells + fee). This makes the returned
                    // delta (and thus AR / cross-fed consumers) reflect the
                    // full value movement.
                    if let Some(proposer_id) = &self.proposer_cell {
                        let mut d = dregg_cell::CellStateDelta::empty();
                        d.balance_change = (turn.fee / 2) as i64;
                        delta.updated.push((*proposer_id, d));
                    }
                    if let Some(treasury_id) = &self.treasury_cell {
                        let mut d = dregg_cell::CellStateDelta::empty();
                        d.balance_change = (turn.fee * 3 / 10) as i64;
                        delta.updated.push((*treasury_id, d));
                    }

                    // P0-3: record the new chain-head for this agent.
                    self.record_receipt_hash(turn.agent, receipt.receipt_hash());

                    return TurnResult::Committed {
                        ledger_delta: delta,
                        receipt,
                        computrons_used,
                    };
                }
                Err(err) => {
                    // Refund budget debit on proof verification failure.
                    if let (Some(gate_cell), Some((digest, fee))) =
                        (&self.budget_gate, &budget_debit_digest)
                    {
                        gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                    }
                    return TurnResult::Rejected {
                        reason: err,
                        at_action: vec![],
                    };
                }
            }
        }

        // =====================================================================
        // SOVEREIGN CELL WITNESS INJECTION
        // Validate witnesses for sovereign cells referenced in this turn and
        // temporarily inject them into the ledger so the executor can operate
        // on them as if they were hosted. After execution, new commitments are
        // computed and the cells are removed from the hosted store.
        // =====================================================================
        // Collect witness sequences to bump after successful injection.
        let mut sovereign_cell_ids: Vec<CellId> = Vec::new();
        let mut sovereign_witness_sequences: Vec<(CellId, u64)> = Vec::new();
        for (cell_id, witness) in &turn.sovereign_witnesses {
            // 0. Witness key vs payload cell_id self-consistency.
            if witness.cell_id != *cell_id {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!(
                            "sovereign witness payload cell_id {} does not match map key {}",
                            witness.cell_id, cell_id
                        ),
                    },
                    at_action: vec![],
                };
            }
            // 1. Verify the cell is actually sovereign in the ledger.
            let stored_commitment = match ledger.get_sovereign_commitment(cell_id) {
                Some(c) => *c,
                None => {
                    return TurnResult::Rejected {
                        reason: TurnError::InvalidEffect {
                            reason: format!(
                                "sovereign witness provided for non-sovereign cell {}",
                                cell_id
                            ),
                        },
                        at_action: vec![],
                    };
                }
            };
            // 2. Witness declared old_commitment must equal ledger's stored.
            if witness.old_commitment != stored_commitment {
                return TurnResult::Rejected {
                    reason: TurnError::SovereignCommitmentMismatch {
                        cell: *cell_id,
                        expected: stored_commitment,
                        got: witness.old_commitment,
                    },
                    at_action: vec![],
                };
            }
            // 3. cell_state's commitment must equal the witness's declared
            //    old_commitment (and therefore the stored one).
            let computed_commitment = witness.cell_state.state_commitment();
            if computed_commitment != witness.old_commitment {
                return TurnResult::Rejected {
                    reason: TurnError::SovereignCommitmentMismatch {
                        cell: *cell_id,
                        expected: witness.old_commitment,
                        got: computed_commitment,
                    },
                    at_action: vec![],
                };
            }
            // 4. cell_state id must match the witness id (the cell carries
            //    its identity inside its state, so this guards against any
            //    `cell_state` body whose `id()` accessor drifts from the
            //    map key).
            if witness.cell_state.id() != *cell_id {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!(
                            "sovereign witness cell ID mismatch: expected {}, got {}",
                            cell_id,
                            witness.cell_state.id()
                        ),
                    },
                    at_action: vec![],
                };
            }
            // 5. Ed25519 signature against the witnessed cell's public_key.
            //    Since `cell_state.public_key()` is bound into
            //    `state_commitment()` (verified above), the key we verify
            //    against is itself anchored to the federation's stored
            //    sovereign commitment.
            let verifying_key = match VerifyingKey::from_bytes(witness.cell_state.public_key()) {
                Ok(k) => k,
                Err(_) => {
                    return TurnResult::Rejected {
                        reason: TurnError::InvalidEffect {
                            reason: format!(
                                "sovereign witness public key invalid for cell {}",
                                cell_id
                            ),
                        },
                        at_action: vec![],
                    };
                }
            };
            let message = crate::turn::SovereignCellWitness::signing_message_for_federation(
                &self.local_federation_id,
                cell_id,
                &witness.old_commitment,
                &witness.new_commitment,
                &witness.effects_hash,
                witness.timestamp,
                witness.sequence,
            );
            let sig = Signature::from_bytes(&witness.signature);
            if verifying_key.verify_strict(&message, &sig).is_err() {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!("sovereign witness signature invalid for cell {}", cell_id),
                    },
                    at_action: vec![],
                };
            }
            // 6. Per-cell monotonic sequence (no gaps).
            let expected_seq = ledger.last_sovereign_witness_sequence(cell_id) + 1;
            if witness.sequence != expected_seq {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!(
                            "sovereign witness sequence gap for cell {}: expected {}, got {}",
                            cell_id, expected_seq, witness.sequence
                        ),
                    },
                    at_action: vec![],
                };
            }
            // 7. Production sovereign witnesses must name real post-state and
            //    local-effect commitments. All-zero fields are legacy
            //    placeholders, not explicit no-op commitments. A no-op
            //    sovereign transition must still sign the real unchanged
            //    state commitment and the canonical hash of its empty/local
            //    effect set rather than using zero sentinels.
            if is_zero_hash(&witness.new_commitment) {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!(
                            "sovereign witness for cell {} has zero new_commitment placeholder",
                            cell_id
                        ),
                    },
                    at_action: vec![],
                };
            }
            if is_zero_hash(&witness.effects_hash) {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!(
                            "sovereign witness for cell {} has zero effects_hash placeholder",
                            cell_id
                        ),
                    },
                    at_action: vec![],
                };
            }
            // 8. Optional STARK transition proof. When present, the proof
            //    is verified through the same path the executor uses for
            //    Phase 3 proof-carrying turns (see `verify_and_commit_proof`).
            //    The PIs bind `old_commitment -> new_commitment +
            //    effects_hash + cell_id` via `EffectVmAir`. A failed verify
            //    rejects the entire turn.
            if let Some(proof_bytes) = &witness.transition_proof {
                if let Err(e) = self.verify_sovereign_witness_stark(
                    cell_id,
                    &witness.old_commitment,
                    &witness.new_commitment,
                    &witness.effects_hash,
                    proof_bytes,
                ) {
                    return TurnResult::Rejected {
                        reason: e,
                        at_action: vec![],
                    };
                }
            }
            // Temporarily inject the witnessed cell into the ledger for execution.
            // If the cell already exists in the hosted table (e.g., because the
            // sovereign cell IS the agent and was looked up for fee/nonce), replace
            // it with the witnessed state (which is authoritative after commitment check).
            if ledger.get(cell_id).is_some() {
                // Cell already in hosted table (agent = sovereign cell case).
                // Replace with witnessed state to ensure executor operates on correct state.
                if let Some(existing) = ledger.get_mut(cell_id) {
                    *existing = witness.cell_state.clone();
                }
            } else if let Err(_) = ledger.insert_cell(witness.cell_state.clone()) {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!("failed to inject sovereign witness for cell {}", cell_id),
                    },
                    at_action: vec![],
                };
            }
            // Studio trace: sovereign_witness_verified — emitted once per verified witness.
            // Fields match the dregg-observability schema (observability/src/events.rs).
            info!(kind = "sovereign_witness_verified", cell_id = %cell_id, sequence = witness.sequence, has_stark_proof = witness.transition_proof.is_some(), old_commitment = hex::encode(witness.old_commitment), new_commitment = hex::encode(witness.new_commitment), effects_hash = hex::encode(witness.effects_hash));
            sovereign_cell_ids.push(*cell_id);
            sovereign_witness_sequences.push((*cell_id, witness.sequence));
        }

        // =====================================================================
        // BINDING-SWEEP GATE: Verify any sidecar effect-binding proofs,
        // cross-effect chain pins, and witness-index map entries BEFORE the
        // call-forest executes.  This is a turn-level gate: if ANY binding
        // proof fails the PI-matching or STARK check the entire turn is
        // rejected without touching ledger state.
        //
        // We use the snapshot-aware path (`_with_ledger`) so that Burn
        // binding proofs can reconstruct (old_balance, new_balance) from the
        // current ledger state (AIR-SOUNDNESS-AUDIT.md #75).  Sovereign
        // witnesses have already been injected above, so the ledger is
        // complete at this point.
        //
        // Turns that carry NONE of the three binding-extension fields skip
        // the verifier entirely (backwards-compat fast path; the `if` guard
        // mirrors the one already inside `verify_effect_binding_proofs`).
        if !turn.effect_binding_proofs.is_empty()
            || !turn.cross_effect_dependencies.is_empty()
            || !turn.effect_witness_index_map.is_empty()
        {
            if let Err(e) = Self::verify_effect_binding_proofs_with_ledger(turn, Some(ledger)) {
                // No journal yet — only need to undo sovereign witness injection
                // and refund the budget gate before returning.
                for cell_id in &sovereign_cell_ids {
                    ledger.remove(cell_id);
                }
                if let (Some(gate_cell), Some((digest, fee))) =
                    (&self.budget_gate, &budget_debit_digest)
                {
                    gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                }
                return TurnResult::Rejected {
                    reason: e,
                    at_action: vec![],
                };
            }
        }

        // =====================================================================
        // PHASE 2: Execute call forest (rolled back on failure).
        // The journal only records forest effects — fee/nonce are already final.
        // =====================================================================
        let mut journal = LedgerJournal::with_capacity(16);
        let mut computrons_used: u64 = 0;
        let mut all_effects_hashes: Vec<[u8; 32]> = Vec::new();
        let mut excess: i64 = 0; // Mina-style excess: must be zero at turn end.

        for (root_idx, root_tree) in turn.call_forest.roots.iter().enumerate() {
            let result = self.execute_tree(
                root_tree,
                ledger,
                &turn.agent,
                // Top-level: agent owns all its capabilities. This value propagates
                // through Inherit and gates child cross-cell targeting (line ~738),
                // but chain-walking (ParentsOwn vs None) is not yet implemented.
                DelegationMode::ParentsOwn,
                &mut computrons_used,
                turn.fee,
                &mut all_effects_hashes,
                vec![root_idx],
                &mut journal,
                &mut excess,
                turn.nonce,
                &turn.agent,
            );

            if let Err((error, path)) = result {
                // Rollback: replay journal in reverse to restore ledger.
                // Also removes any obligation/escrow/nullifier insertions from
                // the executor's in-memory maps (prevents phantom record attacks).
                journal.rollback(
                    ledger,
                    &self.obligations,
                    &self.escrows,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.committed_escrows,
                    &self.committed_escrow_amounts,
                );
                // Remove temporarily-injected sovereign cells on rollback.
                for cell_id in &sovereign_cell_ids {
                    ledger.remove(cell_id);
                }
                // Fast unlock: refund the budget debit on turn failure.
                if let (Some(gate_cell), Some((digest, fee))) =
                    (&self.budget_gate, &budget_debit_digest)
                {
                    gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                }
                return TurnResult::Rejected {
                    reason: error,
                    at_action: path,
                };
            }
        }

        // Check total cost against fee.
        if computrons_used > turn.fee {
            journal.rollback(
                ledger,
                &self.obligations,
                &self.escrows,
                &self.bridged_nullifiers,
                &self.note_nullifiers,
                &self.committed_escrows,
                &self.committed_escrow_amounts,
            );
            for cell_id in &sovereign_cell_ids {
                ledger.remove(cell_id);
            }
            if let (Some(gate_cell), Some((digest, fee))) =
                (&self.budget_gate, &budget_debit_digest)
            {
                gate_cell.lock().unwrap().fast_unlock(*fee, digest);
            }
            return TurnResult::Rejected {
                reason: TurnError::BudgetExceeded {
                    limit: turn.fee,
                    used: computrons_used,
                },
                at_action: vec![],
            };
        }

        // Check note conservation: for each asset type, sum of spent values must
        // equal sum of created values. This is checked independently of the cell
        // balance excess (notes are a separate value domain).
        if let Err(error) = self.check_note_conservation(turn) {
            journal.rollback(
                ledger,
                &self.obligations,
                &self.escrows,
                &self.bridged_nullifiers,
                &self.note_nullifiers,
                &self.committed_escrows,
                &self.committed_escrow_amounts,
            );
            for cell_id in &sovereign_cell_ids {
                ledger.remove(cell_id);
            }
            if let (Some(gate_cell), Some((digest, fee))) =
                (&self.budget_gate, &budget_debit_digest)
            {
                gate_cell.lock().unwrap().fast_unlock(*fee, digest);
            }
            return TurnResult::Rejected {
                reason: TurnError::NoteConservationViolation {
                    asset_type: error.0,
                    inputs: error.1,
                    outputs: error.2,
                },
                at_action: vec![],
            };
        }

        // Check excess conservation law: must be zero at turn end.
        if excess != 0 {
            journal.rollback(
                ledger,
                &self.obligations,
                &self.escrows,
                &self.bridged_nullifiers,
                &self.note_nullifiers,
                &self.committed_escrows,
                &self.committed_escrow_amounts,
            );
            for cell_id in &sovereign_cell_ids {
                ledger.remove(cell_id);
            }
            if let (Some(gate_cell), Some((digest, fee))) =
                (&self.budget_gate, &budget_debit_digest)
            {
                gate_cell.lock().unwrap().fast_unlock(*fee, digest);
            }
            return TurnResult::Rejected {
                reason: TurnError::ExcessNotZero { excess },
                at_action: vec![],
            };
        }

        // =====================================================================
        // SOVEREIGN CELL POST-EXECUTION: Compute new commitments and remove
        // the temporarily-injected cells from the hosted store.
        // The federation stores only the updated 32-byte commitment.
        // =====================================================================
        for cell_id in &sovereign_cell_ids {
            let Some(cell) = ledger.get(cell_id) else {
                journal.rollback(
                    ledger,
                    &self.obligations,
                    &self.escrows,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.committed_escrows,
                    &self.committed_escrow_amounts,
                );
                for injected_id in &sovereign_cell_ids {
                    ledger.remove(injected_id);
                }
                if let (Some(gate_cell), Some((digest, fee))) =
                    (&self.budget_gate, &budget_debit_digest)
                {
                    gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                }
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!(
                            "sovereign witness cell {} missing after execution",
                            cell_id
                        ),
                    },
                    at_action: vec![],
                };
            };
            let actual_new_commitment = cell.state_commitment();
            let witness = turn
                .sovereign_witnesses
                .get(cell_id)
                .expect("validated sovereign witness must still be present");
            if actual_new_commitment != witness.new_commitment {
                journal.rollback(
                    ledger,
                    &self.obligations,
                    &self.escrows,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.committed_escrows,
                    &self.committed_escrow_amounts,
                );
                for injected_id in &sovereign_cell_ids {
                    ledger.remove(injected_id);
                }
                if let (Some(gate_cell), Some((digest, fee))) =
                    (&self.budget_gate, &budget_debit_digest)
                {
                    gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                }
                return TurnResult::Rejected {
                    reason: TurnError::SovereignCommitmentMismatch {
                        cell: *cell_id,
                        expected: witness.new_commitment,
                        got: actual_new_commitment,
                    },
                    at_action: vec![],
                };
            }
        }
        for cell_id in &sovereign_cell_ids {
            if let Some(cell) = ledger.remove(cell_id) {
                let new_commitment = cell.state_commitment();
                // Update the sovereign commitment in the ledger.
                let _ = ledger.update_sovereign_commitment(cell_id, new_commitment);
            }
        }
        // Bump per-cell witness sequences so a replay is rejected even if a
        // future hypothetical state-commitment cycle round-trips back.
        for (cell_id, seq) in &sovereign_witness_sequences {
            ledger.bump_sovereign_witness_sequence(cell_id, *seq);
        }

        // =====================================================================
        // BUDGET GATE: Commit the debit after successful execution.
        // The tentative debit is now permanent — it can no longer be refunded.
        // =====================================================================
        if let (Some(gate_cell), Some((digest, _fee))) = (&self.budget_gate, &budget_debit_digest) {
            gate_cell.lock().unwrap().commit_debit(digest);
        }

        // =====================================================================
        // PHASE 3: Fee distribution (50% proposer / 30% treasury / 20% burned).
        // Only executed after successful forest execution. If neither proposer
        // nor treasury is configured, all fees are burned (backward compatible).
        // =====================================================================
        // Use extracted helper (removes dupe with proof path).
        distribute_fee_shares(
            ledger,
            self.proposer_cell.as_ref(),
            self.treasury_cell.as_ref(),
            turn.fee,
        );

        self.record_state_constraint_counters(turn, ledger, &journal);

        // Phase 4: Compute receipt.
        let post_state_hash = ledger.root();
        let effects_hash = self.compute_effects_hash(&all_effects_hashes);

        // Compute turn hash.
        let turn_hash = turn.hash();
        let forest_hash = turn.call_forest.compute_hash();

        // Build ledger delta from the journal, Phase 1 (fee + nonce), and Phase 3 (distribution).
        let delta = Self::compute_delta_from_journal_with_fee(
            &journal,
            ledger,
            &turn.agent,
            turn.fee,
            self.proposer_cell.as_ref(),
            self.treasury_cell.as_ref(),
        );

        let mut receipt = TurnReceipt {
            turn_hash,
            forest_hash,
            pre_state_hash,
            post_state_hash,
            timestamp: self.current_timestamp,
            effects_hash,
            computrons_used,
            action_count: turn.call_forest.action_count(),
            previous_receipt_hash: turn.previous_receipt_hash,
            agent: turn.agent,
            federation_id: self.local_federation_id,
            routing_directives: Self::collect_routing_directives(
                &turn.call_forest,
                &turn_hash,
                self.block_height,
                self.max_introduction_lifetime,
            ),
            introduction_exports: Self::collect_introduction_exports(
                &turn.call_forest,
                &turn_hash,
                self.block_height,
                self.max_introduction_lifetime,
            ),
            derivation_records: Self::collect_derivation_records(
                &turn.call_forest,
                self.current_timestamp as u64,
            ),
            emitted_events: Self::collect_emitted_events(&journal),
            executor_signature: None,
            finality: crate::turn::Finality::Final,
            // Cleartext path. `apply_encrypted_turn` re-signs after flipping
            // this bit so the encrypted-arrival fact is bound into the
            // receipt hash AND the executor signature.
            was_encrypted: false,
            // Burn-disclosure flag: true iff any action in the forest
            // carried an `Effect::Burn`. Bound into `receipt_hash` so an
            // executor cannot strip the non-conservation disclosure
            // (Silver-Vision lifecycle plan).
            was_burn: Self::forest_carries_burn(&turn.call_forest),
        };
        // R-4: sign the receipt over its canonical hash if the executor has
        // been configured with a signing key (`with_executor_signing_key`).
        receipt.executor_signature = self.maybe_sign_receipt(&receipt);

        // P0-3: record the new chain-head for this agent.
        self.record_receipt_hash(turn.agent, receipt.receipt_hash());

        TurnResult::Committed {
            ledger_delta: delta,
            receipt,
            computrons_used,
        }
    }

    // -----------------------------------------------------------------------
    // WitnessedReceipt v1 capture hook
    // -----------------------------------------------------------------------
    //
    // The canonical Effect-VM prove site today lives outside this crate
    // (`node/src/mcp.rs::generate_effect_vm_proof`). That site holds the
    // trace + public_inputs + proof_bytes together — exactly the inputs
    // a WitnessedReceipt needs. This helper is the lane-agnostic factory:
    // any caller that already has those inputs plus a committed
    // TurnReceipt can lift them into a scope-(2) replay artifact in one
    // call.
    //
    // We intentionally do NOT prove inside `execute` (the executor remains
    // proof-agnostic on the classical path); we just expose the wrapper
    // so the prove site can call into us without taking a turn-crate
    // refactor as a dependency. See WITNESSED-RECEIPT-CHAIN-DESIGN.md §8.

    /// Wrap a committed receipt with the prove-site's trace + proof bytes
    /// into a [`crate::WitnessedReceipt`].
    ///
    /// Pass `trace = Some(&trace)` to produce a scope-(2) replay artifact
    /// (the trace becomes an inline witness bundle, witness_hash committed).
    /// Pass `trace = None` to produce a scope-(1) artifact (proof + PI
    /// only; witness_hash is all-zeros).
    pub fn wrap_witnessed(
        receipt: crate::turn::TurnReceipt,
        proof_bytes: Vec<u8>,
        public_inputs: Vec<u32>,
        trace: Option<&[Vec<dregg_circuit::field::BabyBear>]>,
    ) -> crate::WitnessedReceipt {
        crate::WitnessedReceipt::from_components(receipt, proof_bytes, public_inputs, trace)
    }

    /// Estimate the computron cost of a turn without applying it.
    pub fn estimate_cost(&self, turn: &Turn) -> u64 {
        let mut total: u64 = 0;
        for root in &turn.call_forest.roots {
            total = total.saturating_add(self.estimate_tree_cost(root));
        }
        total
    }

    /// Validate a turn without applying it. Returns Ok(()) if it would succeed,
    /// or the first error that would be encountered.
    pub fn validate_without_apply(&self, turn: &Turn, ledger: &Ledger) -> Result<(), TurnError> {
        if turn.call_forest.is_empty() {
            return Err(TurnError::EmptyForest);
        }

        if let Some(valid_until) = turn.valid_until {
            if self.current_timestamp > valid_until {
                return Err(TurnError::Expired {
                    valid_until,
                    now: self.current_timestamp,
                });
            }
        }

        let agent_cell = ledger
            .get(&turn.agent)
            .ok_or(TurnError::CellNotFound { id: turn.agent })?;

        if agent_cell.state.nonce() != turn.nonce {
            return Err(TurnError::NonceReplay {
                expected: agent_cell.state.nonce(),
                got: turn.nonce,
            });
        }

        if agent_cell.state.balance() < turn.fee {
            return Err(TurnError::InsufficientBalance {
                cell: turn.agent,
                required: turn.fee,
                available: agent_cell.state.balance(),
            });
        }

        // Estimate cost.
        let estimated = self.estimate_cost(turn);
        if estimated > turn.fee {
            return Err(TurnError::BudgetExceeded {
                limit: turn.fee,
                used: estimated,
            });
        }

        Ok(())
    }

    fn record_state_constraint_counters(
        &self,
        turn: &Turn,
        ledger: &Ledger,
        journal: &LedgerJournal,
    ) {
        let Some(sender) = ledger.get(&turn.agent).map(|cell| *cell.public_key()) else {
            return;
        };

        let mut mutated_cells = std::collections::HashSet::<CellId>::new();
        let mut first_field_old =
            std::collections::HashMap::<(CellId, usize), dregg_cell::FieldElement>::new();
        for entry in journal.entries() {
            match entry {
                crate::journal::JournalEntry::SetField {
                    cell,
                    index,
                    old_value,
                } => {
                    mutated_cells.insert(*cell);
                    first_field_old.entry((*cell, *index)).or_insert(*old_value);
                }
                crate::journal::JournalEntry::SetBalance { cell, .. }
                | crate::journal::JournalEntry::SetNonce { cell, .. }
                | crate::journal::JournalEntry::SetPermissions { cell, .. }
                | crate::journal::JournalEntry::SetVerificationKey { cell, .. }
                | crate::journal::JournalEntry::SetDelegation { cell, .. }
                | crate::journal::JournalEntry::SetDelegationEpoch { cell, .. }
                | crate::journal::JournalEntry::SetProvedState { cell, .. }
                | crate::journal::JournalEntry::GrantCapability { cell, .. }
                | crate::journal::JournalEntry::RevokeCapability { cell, .. }
                | crate::journal::JournalEntry::CreateCell { cell }
                | crate::journal::JournalEntry::SetLifecycle { cell, .. }
                | crate::journal::JournalEntry::AttenuateCapability { cell, .. } => {
                    mutated_cells.insert(*cell);
                }
                _ => {}
            }
        }

        for cell_id in mutated_cells {
            let Some(cell) = ledger.get(&cell_id) else {
                continue;
            };
            let dregg_cell::CellProgram::Predicate(constraints) = &cell.program else {
                continue;
            };
            for constraint in constraints {
                match constraint {
                    dregg_cell::StateConstraint::RateLimit { epoch_duration, .. } => {
                        let epoch = Self::epoch_for_height(self.block_height, *epoch_duration);
                        let mut counters = self.rate_limit_counters.lock().unwrap();
                        let counter = counters.entry((cell_id, sender, epoch)).or_insert(0);
                        *counter = counter.saturating_add(1);
                    }
                    dregg_cell::StateConstraint::RateLimitBySum {
                        slot_index,
                        epoch_duration,
                        ..
                    } => {
                        let idx = *slot_index as usize;
                        let Some(old_value) = first_field_old.get(&(cell_id, idx)) else {
                            continue;
                        };
                        let Some(new_value) = cell.state.fields.get(idx) else {
                            continue;
                        };
                        let old = Self::field_to_u64(old_value);
                        let new = Self::field_to_u64(new_value);
                        let delta = new.saturating_sub(old);
                        if delta == 0 {
                            continue;
                        }
                        let epoch = Self::epoch_for_height(self.block_height, *epoch_duration);
                        let mut counters = self.rate_limit_sum_counters.lock().unwrap();
                        let counter = counters.entry((cell_id, *slot_index, epoch)).or_insert(0);
                        *counter = counter.saturating_add(delta);
                    }
                    _ => {}
                }
            }
        }
    }

    fn field_to_u64(field: &dregg_cell::FieldElement) -> u64 {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&field[24..32]);
        u64::from_be_bytes(bytes)
    }
}
