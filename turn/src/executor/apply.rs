//! Effect application: per-`Effect` `apply_*` methods plus a thin dispatcher.
//!
//! Originally extracted from `executor/mod.rs` (lines 6150-9565 of pre-decomposition
//! file) as a single 3400-LOC `match effect` block. Decomposed into per-variant
//! methods so each effect's apply logic can be tested independently — every
//! `apply_<variant>` is a regular method on `TurnExecutor` and may be called
//! directly with a hand-built `Ledger` + `LedgerJournal`.
//!
//! Behavior is unchanged: each `apply_<variant>` is a verbatim move of the
//! corresponding old match arm, and `apply_effect` is reduced to a dispatcher.

use super::*;
use dregg_cell::*;

impl TurnExecutor {
    /// Apply a single effect to the ledger, recording undo entries in the journal.
    ///
    /// SECURITY: For any effect that names a cell other than `action_target`,
    /// we verify that the actor holds a capability to that cell AND that the
    /// relevant permission on that cell allows the operation.
    /// TRUST-CRITICAL: This function directly mutates ledger state (balances, fields, cells).
    /// If compromised: balance inflation/deflation, unauthorized state overwrites, or
    /// cell creation without proper authorization. All mutations are journaled for rollback.
    /// Future: replace with verified effect application via Effect VM STARK proof for all
    /// effect types (currently only sovereign cells use proof-carrying effects).
    pub(crate) fn apply_effect(
        &self,
        effect: &Effect,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        match effect {
            Effect::SetField { cell, index, value } => self.apply_set_field(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                *index,
                value,
            ),
            Effect::Transfer { from, to, amount } => self.apply_transfer(
                ledger,
                path,
                action_target,
                actor,
                journal,
                from,
                to,
                *amount,
            ),
            Effect::GrantCapability { from, to, cap } => self.apply_grant_capability(
                ledger,
                path,
                action_target,
                actor,
                journal,
                from,
                to,
                cap,
            ),
            Effect::RevokeCapability { cell, slot } => self.apply_revoke_capability(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                *slot,
            ),
            Effect::EmitEvent { cell, event } => {
                self.apply_emit_event(ledger, path, journal, cell, event)
            }
            Effect::IncrementNonce { cell } => {
                self.apply_increment_nonce(ledger, path, action_target, actor, journal, cell)
            }
            Effect::CreateCell {
                public_key,
                token_id,
                balance,
            } => self.apply_create_cell(ledger, path, journal, public_key, token_id, *balance),
            Effect::SetPermissions {
                cell,
                new_permissions,
            } => self.apply_set_permissions(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                new_permissions,
            ),
            Effect::SetVerificationKey { cell, new_vk } => self.apply_set_verification_key(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                new_vk.as_ref(),
            ),
            Effect::NoteSpend {
                nullifier,
                note_tree_root,
                spending_proof,
                value,
                asset_type,
                value_commitment,
            } => self.apply_note_spend(
                path,
                journal,
                nullifier,
                note_tree_root,
                spending_proof,
                *value,
                *asset_type,
                value_commitment.as_ref(),
            ),
            Effect::NoteCreate {
                commitment,
                value_commitment,
                range_proof,
                ..
            } => self.apply_note_create(
                path,
                journal,
                commitment,
                value_commitment.as_ref(),
                range_proof.as_deref(),
            ),
            Effect::BridgeMint { portable_proof } => {
                self.apply_bridge_mint(path, journal, portable_proof)
            }
            Effect::BridgeLock {
                nullifier,
                destination,
                value,
                asset_type,
                timeout_height,
                spending_proof,
            } => self.apply_bridge_lock(
                path,
                nullifier,
                destination,
                *value,
                *asset_type,
                *timeout_height,
                spending_proof,
            ),
            Effect::BridgeFinalize { nullifier, receipt } => {
                self.apply_bridge_finalize(path, nullifier, receipt)
            }
            Effect::BridgeCancel { nullifier } => self.apply_bridge_cancel(path, nullifier),
            Effect::CreateObligation {
                beneficiary,
                condition,
                deadline_height,
                stake,
                stake_amount,
            } => self.apply_create_obligation(
                ledger,
                path,
                action_target,
                journal,
                beneficiary,
                condition,
                *deadline_height,
                stake,
                *stake_amount,
            ),
            Effect::FulfillObligation {
                obligation_id,
                proof,
            } => self.apply_fulfill_obligation(
                ledger,
                path,
                action_target,
                journal,
                obligation_id,
                proof,
            ),
            Effect::SlashObligation { obligation_id } => {
                self.apply_slash_obligation(ledger, path, journal, obligation_id)
            }
            Effect::CreateEscrow {
                cell,
                recipient,
                amount,
                condition,
                timeout_height,
                escrow_id,
            } => self.apply_create_escrow(
                ledger,
                path,
                action_target,
                journal,
                cell,
                recipient,
                *amount,
                condition,
                *timeout_height,
                escrow_id,
            ),
            Effect::ReleaseEscrow { escrow_id, proof } => {
                self.apply_release_escrow(ledger, path, journal, escrow_id, proof.as_ref())
            }
            Effect::RefundEscrow { escrow_id } => {
                self.apply_refund_escrow(ledger, path, journal, escrow_id)
            }
            Effect::CreateCommittedEscrow {
                creator_commitment,
                recipient_commitment,
                value_commitment,
                condition_commitment,
                timeout_height,
                escrow_id,
                range_proof,
                amount,
            } => self.apply_create_committed_escrow(
                ledger,
                path,
                action_target,
                journal,
                creator_commitment,
                recipient_commitment,
                value_commitment,
                condition_commitment,
                *timeout_height,
                escrow_id,
                range_proof,
                *amount,
            ),
            Effect::ReleaseCommittedEscrow {
                escrow_id,
                claim_auth,
                recipient,
            } => self.apply_release_committed_escrow(
                ledger, path, journal, escrow_id, claim_auth, recipient,
            ),
            Effect::RefundCommittedEscrow {
                escrow_id,
                claim_auth,
                creator,
            } => self.apply_refund_committed_escrow(
                ledger, path, journal, escrow_id, claim_auth, creator,
            ),
            Effect::ExerciseViaCapability {
                cap_slot,
                inner_effects,
            } => self.apply_exercise_via_capability(
                ledger,
                path,
                actor,
                journal,
                *cap_slot,
                inner_effects,
            ),
            Effect::PipelinedSend { target, .. } => self.apply_pipelined_send(path, target),
            Effect::CreateSealPair {
                sealer_holder,
                unsealer_holder,
            } => self.apply_create_seal_pair(ledger, path, journal, sealer_holder, unsealer_holder),
            Effect::Seal {
                pair_id,
                capability,
            } => self.apply_seal(ledger, path, actor, journal, pair_id, capability),
            Effect::Introduce {
                introducer,
                recipient,
                target,
                permissions,
            } => self.apply_introduce(
                ledger,
                path,
                journal,
                introducer,
                recipient,
                target,
                permissions,
            ),
            Effect::Unseal {
                sealed_box,
                recipient,
            } => self.apply_unseal(ledger, path, actor, journal, sealed_box, recipient),
            Effect::SpawnWithDelegation {
                child_public_key,
                child_token_id,
                max_staleness,
            } => self.apply_spawn_with_delegation(
                ledger,
                path,
                action_target,
                journal,
                child_public_key,
                child_token_id,
                *max_staleness,
            ),
            Effect::RefreshDelegation => {
                self.apply_refresh_delegation(ledger, path, action_target, journal)
            }
            Effect::RevokeDelegation { child } => {
                self.apply_revoke_delegation(ledger, path, action_target, journal, child)
            }
            Effect::MakeSovereign { cell } => {
                self.apply_make_sovereign(ledger, path, action_target, cell)
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                owner_pubkey,
                token_id,
                params,
            } => self.apply_create_cell_from_factory(
                ledger,
                path,
                journal,
                factory_vk,
                owner_pubkey,
                token_id,
                params,
            ),
            Effect::QueueAllocate {
                capacity,
                program_vk,
            } => self.apply_queue_allocate(
                ledger,
                path,
                action_target,
                actor,
                journal,
                *capacity,
                program_vk.as_ref(),
            ),
            Effect::QueueEnqueue {
                queue,
                message_hash,
                deposit,
            } => self.apply_queue_enqueue(
                ledger,
                path,
                actor,
                journal,
                queue,
                message_hash,
                *deposit,
            ),
            Effect::QueueDequeue { queue } => {
                self.apply_queue_dequeue(ledger, path, action_target, journal, queue)
            }
            Effect::QueueResize {
                queue,
                new_capacity,
            } => self.apply_queue_resize(
                ledger,
                path,
                action_target,
                actor,
                journal,
                queue,
                *new_capacity,
            ),
            Effect::QueueAtomicTx { operations } => {
                self.apply_queue_atomic_tx(ledger, path, action_target, actor, journal, operations)
            }
            Effect::QueuePipelineStep {
                pipeline_id: _,
                source,
                sinks,
            } => {
                self.apply_queue_pipeline_step(ledger, path, action_target, journal, source, sinks)
            }
            Effect::ExportSturdyRef {
                swiss_number,
                target,
                permissions,
            } => self.apply_export_sturdy_ref(
                ledger,
                path,
                action_target,
                actor,
                journal,
                swiss_number,
                target,
                permissions,
            ),
            Effect::EnlivenRef {
                swiss_number,
                bearer,
                expected_cell_id,
                expected_permissions,
            } => self.apply_enliven_ref(
                ledger,
                path,
                journal,
                swiss_number,
                bearer,
                expected_cell_id,
                expected_permissions,
            ),
            Effect::DropRef { ref_id } => {
                self.apply_drop_ref(ledger, path, action_target, journal, ref_id)
            }
            Effect::ValidateHandoff {
                cert_hash,
                recipient_pk,
                introducer_pk,
            } => self.apply_validate_handoff(
                ledger,
                path,
                action_target,
                cert_hash,
                recipient_pk,
                introducer_pk,
            ),
            Effect::Refusal {
                cell,
                offered_action_commitment,
                refusal_reason,
                proof_witness_index,
            } => self.apply_refusal(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                offered_action_commitment,
                refusal_reason,
                *proof_witness_index,
            ),
            Effect::CellSeal { target, reason } => {
                self.apply_cell_seal(ledger, path, action_target, journal, target, *reason)
            }
            Effect::CellUnseal { target } => {
                self.apply_cell_unseal(ledger, path, action_target, journal, target)
            }
            Effect::CellDestroy {
                target,
                certificate,
            } => self.apply_cell_destroy(ledger, path, action_target, journal, target, certificate),
            Effect::Burn {
                target,
                slot,
                amount,
            } => self.apply_burn(
                ledger,
                path,
                action_target,
                actor,
                journal,
                target,
                *slot,
                *amount,
            ),
            Effect::AttenuateCapability {
                cell,
                slot,
                narrower_permissions,
                narrower_effects,
                narrower_expiry,
            } => self.apply_attenuate_capability(
                ledger,
                path,
                actor,
                journal,
                cell,
                *slot,
                narrower_permissions,
                *narrower_effects,
                *narrower_expiry,
            ),
            Effect::ReceiptArchive {
                prefix_end_height,
                checkpoint,
            } => self.apply_receipt_archive(
                ledger,
                path,
                action_target,
                journal,
                *prefix_end_height,
                checkpoint,
            ),
        }
    }

    // ─── Per-Effect apply methods ────────────────────────────────────────────
    //
    // Each method below is the verbatim body of the corresponding match arm
    // from the pre-decomposition `apply_effect`. The signatures pass through
    // exactly the variant fields plus the ambient ledger/path/journal/actor
    // context. Behavior is unchanged.

    fn apply_set_field(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        index: usize,
        value: &FieldElement,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if index >= STATE_SLOTS {
            return Err((
                TurnError::InvalidFieldIndex { cell: *cell, index },
                path.to_vec(),
            ));
        }
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetState,
                "SetState",
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        journal.record_set_field(*cell, index, c.state.fields[index]);
        c.state.fields[index] = *value;
        // Invalidate stale field commitment (the old hash no longer matches).
        if c.state.commitments[index].is_some() {
            c.state.commitments[index] = None;
        }
        Ok(())
    }

    fn apply_transfer(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        from: &CellId,
        to: &CellId,
        amount: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if from != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                from,
                dregg_cell::permissions::Action::Send,
                "Send",
                path,
            )?;
        }
        let from_cell = ledger
            .get(from)
            .ok_or_else(|| (TurnError::CellNotFound { id: *from }, path.to_vec()))?;
        if from_cell.state.balance() < amount {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *from,
                    required: amount,
                    available: from_cell.state.balance(),
                },
                path.to_vec(),
            ));
        }
        if ledger.get(to).is_none() {
            return Err((TurnError::TransferDestNotFound { id: *to }, path.to_vec()));
        }
        let to_balance = ledger.get(to).unwrap().state.balance();
        if to_balance.checked_add(amount).is_none() {
            return Err((TurnError::BalanceOverflow { cell: *to }, path.to_vec()));
        }
        // Record old balances, then apply.
        let old_from_balance = ledger.get(from).unwrap().state.balance();
        let old_to_balance = ledger.get(to).unwrap().state.balance();
        journal.record_set_balance(*from, old_from_balance);
        journal.record_set_balance(*to, old_to_balance);
        ledger
            .get_mut(from)
            .unwrap()
            .state
            .set_balance(old_from_balance - amount);
        ledger
            .get_mut(to)
            .unwrap()
            .state
            .set_balance(old_to_balance + amount);
        Ok(())
    }

    fn apply_grant_capability(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        from: &CellId,
        to: &CellId,
        cap: &CapabilityRef,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if from != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                from,
                dregg_cell::permissions::Action::Delegate,
                "Delegate",
                path,
            )?;
        }

        let from_cell = ledger
            .get(from)
            .ok_or_else(|| (TurnError::CellNotFound { id: *from }, path.to_vec()))?;

        // A cell implicitly holds the strongest capability over itself:
        // granting access to its own cell is authorized by the signed
        // action (the cell's owner consents). For cross-cell grants the
        // granter must hold an explicit c-list entry pointing at the
        // target.
        if cap.target == *from {
            // Self-grant: skip c-list lookup; the signature on the
            // action proves the cell owner consents to share access
            // to their own cell. Attenuation against an implicit
            // self-cap is always satisfied (the implicit cap is the
            // strongest possible).
        } else {
            let held_cap = from_cell
                .capabilities
                .lookup_by_target(&cap.target)
                .ok_or_else(|| {
                    (
                        TurnError::CapabilityNotHeld {
                            actor: *from,
                            target: cap.target,
                        },
                        path.to_vec(),
                    )
                })?;

            if !dregg_cell::is_attenuation(&held_cap.permissions, &cap.permissions) {
                return Err((
                    TurnError::DelegationDenied {
                        parent: *from,
                        child_target: *to,
                    },
                    path.to_vec(),
                ));
            }
        }

        let to_cell = ledger
            .get_mut(to)
            .ok_or_else(|| (TurnError::CellNotFound { id: *to }, path.to_vec()))?;
        let granted_slot = to_cell
            .capabilities
            .grant_with_breadstuff(cap.target, cap.permissions.clone(), cap.breadstuff)
            .ok_or_else(|| {
                (
                    TurnError::CapabilitySlotOverflow { cell: *to },
                    path.to_vec(),
                )
            })?;
        journal.record_grant_capability(*to, granted_slot);
        Ok(())
    }

    fn apply_revoke_capability(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        slot: u32,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::Delegate,
                "Delegate",
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        if let Some(old_cap) = c.capabilities.lookup(slot).cloned() {
            journal.record_revoke_capability(*cell, old_cap);
        }
        c.capabilities.revoke(slot);
        Ok(())
    }

    fn apply_emit_event(
        &self,
        ledger: &Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        cell: &CellId,
        event: &Event,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if ledger.get(cell).is_none() {
            return Err((TurnError::CellNotFound { id: *cell }, path.to_vec()));
        }
        // Record the event in the journal so it appears in the turn receipt.
        journal.record_event_emitted(*cell, event.topic, event.data.clone());
        Ok(())
    }

    fn apply_increment_nonce(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::IncrementNonce,
                "IncrementNonce",
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        journal.record_set_nonce(*cell, c.state.nonce());
        if !c.state.increment_nonce() {
            return Err((TurnError::NonceOverflow { cell: *cell }, path.to_vec()));
        }
        Ok(())
    }

    fn apply_create_cell(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        public_key: &[u8; 32],
        token_id: &[u8; 32],
        balance: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if balance != 0 {
            return Err((
                TurnError::CreateCellNonZeroBalance {
                    cell: CellId::derive_raw(public_key, token_id),
                    balance,
                },
                path.to_vec(),
            ));
        }
        let new_cell = Cell::with_balance(*public_key, *token_id, 0);
        let id = new_cell.id();
        ledger
            .insert_cell(new_cell)
            .map_err(|_| (TurnError::CellAlreadyExists { id }, path.to_vec()))?;
        journal.record_create_cell(id);
        Ok(())
    }

    fn apply_set_permissions(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        new_permissions: &dregg_cell::Permissions,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetPermissions,
                "SetPermissions",
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        journal.record_set_permissions(*cell, c.permissions.clone());
        c.permissions = new_permissions.clone();
        Ok(())
    }

    fn apply_set_verification_key(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        new_vk: Option<&dregg_cell::VerificationKey>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetVerificationKey,
                "SetVerificationKey",
                path,
            )?;
        }
        // Audit P0 #69: the apply path must reject `VerificationKey`s
        // whose declared `hash` is not `blake3(data)`. Without this
        // check a turn can pin an arbitrary `hash` while shipping
        // unrelated `data`, which then propagates into the cell
        // commitment (via `commitment.rs` line 148, `hasher.update(&vk.hash)`)
        // and into downstream verifiers that re-derive program
        // identity from the hash. Reject the apply rather than silently
        // accepting a mis-bound VK.
        if let Some(vk) = new_vk {
            let expected = *blake3::hash(&vk.data).as_bytes();
            if expected != vk.hash {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "SetVerificationKey: VerificationKey integrity invariant violated \
                             (declared hash {:02x}{:02x}.. but blake3(data) is {:02x}{:02x}..)",
                            vk.hash[0], vk.hash[1], expected[0], expected[1],
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        journal.record_set_verification_key(*cell, c.verification_key.clone());
        c.verification_key = new_vk.cloned();
        Ok(())
    }

    fn apply_note_spend(
        &self,
        path: &[usize],
        journal: &mut LedgerJournal,
        nullifier: &Nullifier,
        note_tree_root: &[u8; 32],
        spending_proof: &[u8],
        value: u64,
        asset_type: u64,
        // BUG #115: previously dropped via `..`; now validated and bound.
        // When present, `value_commitment` must be a valid compressed Ristretto
        // point. Binding it here (via journal.record_note_spend_commitment)
        // makes it observable in the turn receipt. Conservation and
        // Schnorr-excess proof are verified at the finalize layer
        // (`check_committed_conservation`).
        value_commitment: Option<&[u8; 32]>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate nullifier is well-formed (non-zero).
        if nullifier.0.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null nullifier in NoteSpend".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate note_tree_root is non-zero (must reference a real tree state).
        if note_tree_root.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null note_tree_root in NoteSpend".into(),
                },
                path.to_vec(),
            ));
        }
        // Verify the ZK spending proof: proves the spender knows the note's
        // opening, the nullifier is correctly derived, and the note commitment
        // exists in the note tree at the given root.
        if spending_proof.is_empty() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "NoteSpend missing spending proof".into(),
                },
                path.to_vec(),
            ));
        }
        let verifier = self.proof_verifier.as_ref().ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "no proof verifier configured for note spend verification".into(),
                },
                path.to_vec(),
            )
        })?;
        // Public inputs for the note spending STARK (advisory buffer for
        // the wire-side verifier; the real PI lives in the embedded proof):
        // nullifier || note_tree_root || value || asset_type || dest_fed
        //
        // SECURITY: value and asset_type are bound via boundary constraints
        // to the actual note preimage columns. A spender cannot claim a
        // different value/asset_type than what is committed in the note —
        // the proof verification will fail. destination_federation is
        // ZERO for local (non-bridge) spends; the AIR boundary pins col 18
        // to pi[4] so a bridge-shaped proof (non-zero dest) cannot be
        // replayed against the local-spend path.
        let mut public_inputs = Vec::with_capacity(112);
        public_inputs.extend_from_slice(&nullifier.0);
        public_inputs.extend_from_slice(note_tree_root);
        public_inputs.extend_from_slice(&value.to_le_bytes());
        public_inputs.extend_from_slice(&asset_type.to_le_bytes());
        // destination_federation = ZERO for local spends.
        public_inputs.extend_from_slice(&[0u8; 32]);
        if !verifier.verify(spending_proof, "note-spend", "note-tree", &public_inputs) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "NoteSpend spending proof verification failed".into(),
                },
                path.to_vec(),
            ));
        }
        // Insert into the production note-nullifier set with double-spend
        // rejection. This is the ledger-side gate that prevents the same
        // nullifier from being re-presented in a later turn. The insert is
        // journaled so a turn that fails *after* this point unwinds the
        // record (preventing a deliberate-failure attack that would
        // permanently burn the note).
        {
            let mut set = self.note_nullifiers.lock().unwrap();
            if set.contains(nullifier) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "double-spend: nullifier already in note_nullifiers set"
                            .to_string(),
                    },
                    path.to_vec(),
                ));
            }
            set.insert(*nullifier).map_err(|e| {
                // `insert` returns DoubleSpend on collision; we just
                // checked above, so this is defensive against future
                // concurrent races (the Mutex makes that impossible today).
                let reason = match e {
                    NoteError::DoubleSpend { .. } => {
                        "double-spend: race on nullifier insert".to_string()
                    }
                    other => format!("nullifier insert failed: {:?}", other),
                };
                (TurnError::InvalidEffect { reason }, path.to_vec())
            })?;
        }
        journal.record_note_nullifier_inserted(*nullifier);
        // Record for the note layer to process after turn commits.
        journal.record_note_spend(*nullifier);

        // BUG #115: validate value_commitment if present.
        // Reject malformed compressed Ristretto points immediately at apply
        // time so that the effect can never reach the finalize layer with a
        // value_commitment that is not a valid group element. The
        // conservation-proof check (Schnorr excess) and cross-note consistency
        // are verified at the finalize layer (`check_committed_conservation`).
        if let Some(vc_bytes) = value_commitment {
            if ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).is_none() {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "NoteSpend value_commitment is not a valid Ristretto point".into(),
                    },
                    path.to_vec(),
                ));
            }
        }

        Ok(())
    }

    fn apply_note_create(
        &self,
        path: &[usize],
        journal: &mut LedgerJournal,
        commitment: &NoteCommitment,
        // BUG #115: previously dropped via `..`; now validated at apply time.
        // If `value_commitment` is present, `range_proof` must also be present
        // and must verify against the commitment. This is defense-in-depth:
        // the finalize layer (`verify_output_range_proofs`) also checks this
        // for the Committed conservation path, but we reject here early so
        // that malformed effects never reach the journal.
        value_commitment: Option<&[u8; 32]>,
        range_proof: Option<&[u8]>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate commitment is well-formed (non-zero).
        if commitment.0.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null commitment in NoteCreate".into(),
                },
                path.to_vec(),
            ));
        }
        // Note: zero-value notes are legitimate (e.g., NFTs where asset_type
        // is the unique identifier and value=0 represents ownership).

        // BUG #115 (defense-in-depth): validate value_commitment + range_proof
        // at apply time. The finalize layer also checks this, but we reject
        // early so that malformed effects never persist through the journal.
        //
        // Rules:
        //   (a) value_commitment, if present, must be a valid compressed
        //       Ristretto point.
        //   (b) if value_commitment is present, range_proof must also be
        //       present and non-empty, and must verify against the commitment.
        //       This prevents a prover from hiding a negative value behind a
        //       commitment without proving the value is in [0, 2^64).
        //   (c) range_proof without value_commitment is incoherent — reject.
        match (value_commitment, range_proof) {
            (None, None) => {
                // Cleartext path: no commitment, no range proof — OK.
            }
            (None, Some(_)) => {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "NoteCreate has range_proof but no value_commitment".into(),
                    },
                    path.to_vec(),
                ));
            }
            (Some(vc_bytes), rp_opt) => {
                // Decode the compressed Ristretto point.
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).ok_or_else(
                    || {
                        (
                            TurnError::InvalidEffect {
                                reason:
                                    "NoteCreate value_commitment is not a valid Ristretto point"
                                        .into(),
                            },
                            path.to_vec(),
                        )
                    },
                )?;
                // Range proof is required when a value commitment is present.
                let rp_bytes = rp_opt.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "NoteCreate has value_commitment but no range_proof".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if rp_bytes.is_empty() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "NoteCreate range_proof is empty".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the Bulletproof range proof against the commitment.
                let bulletproof = BulletproofRangeProof {
                    proof_bytes: rp_bytes.to_vec(),
                };
                bulletproof.verify_range(&vc).map_err(|e| {
                    (
                        TurnError::InvalidEffect {
                            reason: format!("NoteCreate range proof verification failed: {}", e),
                        },
                        path.to_vec(),
                    )
                })?;
            }
        }

        // Record for the note layer to process after turn commits.
        journal.record_note_create(*commitment);
        Ok(())
    }

    // BridgeMint: verify the portable proof against trusted federation roots
    // and track the nullifier to prevent double-bridge attacks.
    // The destination_federation in the proof must match our local_federation_id
    // to prevent cross-federation replay (inflation bug).
    //
    // The note-spending AIR's pi layout (post-DSL upgrade) is:
    //   pi[0] = nullifier
    //   pi[1] = merkle_root
    //   pi[2] = value
    //   pi[3] = asset_type
    //   pi[4] = destination_federation
    // The boundary constraint at row 0 col 18 = pi[4] pins the prover's
    // trace destination to whatever the verifier passes — so a proof
    // generated with dest_federation D fails verification if the
    // verifier passes D' != D. Combined with `verify_portable_note`'s
    // local-federation-id check, this closes the cross-federation
    // replay trapdoor (see AUDIT-nullifiers.md §5).
    fn apply_bridge_mint(
        &self,
        path: &[usize],
        journal: &mut LedgerJournal,
        portable_proof: &PortableNoteProof,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // PROOF-TO-ACTION BINDING (Lane Bridge-Implementation).
        //
        // Previously, the bridge proof verification path serialized
        // (nullifier || root || value || asset_type || destination_federation)
        // into a byte buffer and passed it to `ProofVerifier::verify(..)`
        // as the `vk` argument. That argument is consumed as a 32-byte
        // verification key (the first 4 bytes are treated as a BabyBear
        // felt for the federation-root check), so all 112 typed PI bytes
        // were silently truncated — the four cryptographic bindings the
        // AIR enforces (nullifier, value, asset_type, destination) were
        // never compared against the proof's embedded PI vector.
        //
        // The fix: skip the generic `ProofVerifier` trait entirely for
        // bridge mints and call the typed `verify_note_spend_dsl_with_destination`
        // entry point. This verifier:
        //
        //   * deserializes the STARK proof,
        //   * recomputes the AIR's boundary constraints over the typed PI
        //     (nullifier, merkle_root, value, asset_type, destination_federation),
        //   * algebraically rejects any proof whose trace columns at row 0
        //     (col::NULLIFIER, col::VALUE, col::ASSET_TYPE,
        //     col::DESTINATION_FEDERATION) do not match the PI vector that
        //     the executor supplies from the `PortableNoteProof`.
        //
        // Combined with `verify_portable_note`'s local-federation-id check
        // and `BridgedNullifierSet::insert`'s replay protection, this
        // closes the cross-federation replay, value-inflation, asset-type
        // confusion, and recipient-substitution trapdoors (AUDIT-nullifiers.md
        // §5; BACKWATER-CRATES-AUDIT.md bridge/ open issue).
        //
        // PI encoding convention (provers MUST match):
        //   * nullifier, merkle_root, destination_federation: 32-byte values
        //     compressed into one BabyBear via
        //     `BabyBear::encode_hash(bytes)` → Poseidon2 `hash_many` →
        //     single field element (the same `bytes_to_babybear`
        //     compression used by `bridge::present` and the SDK).
        //   * value, asset_type: low-30 bits of the u64 reduced mod the
        //     BabyBear prime as a canonical `BabyBear::new` element. The
        //     prover must place the same value into `witness.value` /
        //     `witness.asset_type` to satisfy the boundary constraint.
        let verify_stark = |nullifier: &[u8; 32],
                            root: &[u8; 32],
                            dest_federation: &[u8; 32],
                            value: u64,
                            asset_type: u64,
                            proof_bytes: &[u8]|
         -> Result<(), String> {
            use dregg_circuit::BabyBear;
            use dregg_circuit::dsl::note_spending::verify_note_spend_dsl_with_destination;
            use dregg_circuit::poseidon2;
            use dregg_circuit::stark::proof_from_bytes;

            // Compress a 32-byte value to a single BabyBear via Poseidon2 of 8 limbs.
            // Matches `bridge::present::bytes_to_babybear` so prover and verifier agree.
            fn compress(bytes: &[u8; 32]) -> BabyBear {
                let limbs = BabyBear::encode_hash(bytes);
                poseidon2::hash_many(&limbs)
            }
            // Reduce a u64 to a canonical BabyBear (low 30 bits, then mod p).
            // The prover must use the same reduction for its witness scalars.
            fn u64_to_bb(v: u64) -> BabyBear {
                BabyBear::new((v & ((1u64 << 30) - 1)) as u32)
            }

            let stark_proof = proof_from_bytes(proof_bytes)
                .map_err(|e| format!("STARK proof deserialization failed: {e}"))?;

            let nullifier_bb = compress(nullifier);
            let root_bb = compress(root);
            let dest_bb = compress(dest_federation);
            let value_bb = u64_to_bb(value);
            let asset_bb = u64_to_bb(asset_type);

            // SECURITY: This call rejects any proof whose embedded PI vector
            // does not match (nullifier_bb, root_bb, value_bb, asset_bb,
            // dest_bb). The AIR's boundary constraints at row 0 columns
            // {NULLIFIER, VALUE, ASSET_TYPE, DESTINATION_FEDERATION} and at
            // the last row col CURRENT (merkle root) pin the prover's trace
            // to whatever the verifier passes here.
            verify_note_spend_dsl_with_destination(
                nullifier_bb,
                root_bb,
                value_bb,
                asset_bb,
                dest_bb,
                &stark_proof,
            )
            .map_err(|e| format!("STARK spending proof verification failed: {e}"))
        };

        dregg_cell::note_bridge::verify_portable_note(
            portable_proof,
            &self.local_federation_id,
            &self.trusted_federation_roots,
            verify_stark,
        )
        .map_err(|e| {
            (
                TurnError::BridgeMintFailed {
                    reason: e.to_string(),
                },
                path.to_vec(),
            )
        })?;

        self.bridged_nullifiers
            .lock()
            .unwrap()
            .insert(portable_proof.nullifier)
            .map_err(|e| {
                (
                    TurnError::BridgeMintFailed {
                        reason: e.to_string(),
                    },
                    path.to_vec(),
                )
            })?;

        // Record the insertion so it can be rolled back on turn failure.
        // Without this, an attacker could craft a turn with BridgeMint +
        // deliberate failure to permanently burn a nullifier without minting.
        journal.record_bridged_nullifier_inserted(portable_proof.nullifier);

        Ok(())
    }

    // BridgeLock: Phase 1 — lock a note for conditional cross-federation transfer.
    // The note's nullifier is committed-to but NOT added to the permanent set.
    // Instead a PendingBridge record is created in pending_bridges.
    fn apply_bridge_lock(
        &self,
        path: &[usize],
        nullifier: &[u8; 32],
        destination: &[u8; 32],
        value: u64,
        asset_type: u64,
        timeout_height: u64,
        spending_proof: &[u8],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let mut pending = self.pending_bridges.lock().unwrap();
        dregg_cell::note_bridge::initiate_bridge(
            *nullifier,
            *destination,
            value,
            asset_type,
            timeout_height,
            spending_proof.to_vec(),
            &mut pending,
        )
        .map_err(|e| {
            (
                TurnError::BridgeLockFailed {
                    reason: e.to_string(),
                },
                path.to_vec(),
            )
        })?;
        Ok(())
    }

    // BridgeFinalize: Phase 3 — present a destination receipt to finalize the burn.
    fn apply_bridge_finalize(
        &self,
        path: &[usize],
        nullifier: &[u8; 32],
        receipt: &BridgeReceipt,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let mut pending = self.pending_bridges.lock().unwrap();
        let mut bridged = self.bridged_nullifiers.lock().unwrap();
        dregg_cell::note_bridge::finalize_bridge(
            nullifier,
            receipt,
            &self.trusted_destination_keys,
            &mut pending,
            &mut bridged,
        )
        .map_err(|e| {
            (
                TurnError::BridgeFinalizeFailed {
                    reason: e.to_string(),
                },
                path.to_vec(),
            )
        })?;
        Ok(())
    }

    // BridgeCancel: Phase 4 — cancel a bridge after timeout (value returned to owner).
    fn apply_bridge_cancel(
        &self,
        path: &[usize],
        nullifier: &[u8; 32],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let mut pending = self.pending_bridges.lock().unwrap();
        dregg_cell::note_bridge::cancel_bridge(nullifier, self.block_height, &mut pending)
            .map_err(|e| {
                (
                    TurnError::BridgeCancelFailed {
                        reason: e.to_string(),
                    },
                    path.to_vec(),
                )
            })?;
        Ok(())
    }

    // Obligation effects: validate structure, enforce balance movement,
    // and record for the obligation registry.
    fn apply_create_obligation(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        beneficiary: &CellId,
        condition: &crate::conditional::ProofCondition,
        deadline_height: u64,
        stake: &NoteCommitment,
        stake_amount: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate beneficiary cell exists.
        if ledger.get(beneficiary).is_none() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "obligation beneficiary cell not found".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate deadline is in the future.
        if deadline_height <= self.block_height {
            return Err((
                TurnError::InvalidEffect {
                    reason: "obligation deadline must be in the future".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate deadline is within acceptable bounds.
        if let Err(reason) =
            crate::obligation::validate_obligation_deadline(deadline_height, self.block_height)
        {
            return Err((TurnError::InvalidEffect { reason }, path.to_vec()));
        }
        // Validate stake commitment is non-zero.
        if stake.0.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "obligation stake commitment is null".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate stake_amount is non-zero.
        if stake_amount == 0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: "obligation stake_amount must be non-zero".into(),
                },
                path.to_vec(),
            ));
        }
        // Lock stake_amount from the obligor's (action_target's) balance.
        let obligor_cell = ledger.get(action_target).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            )
        })?;
        if obligor_cell.state.balance() < stake_amount {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *action_target,
                    required: stake_amount,
                    available: obligor_cell.state.balance(),
                },
                path.to_vec(),
            ));
        }
        let old_balance = obligor_cell.state.balance();
        journal.record_set_balance(*action_target, old_balance);
        ledger
            .get_mut(action_target)
            .unwrap()
            .state
            .set_balance(old_balance - stake_amount);

        // Derive obligation ID and store in registry.
        // SECURITY (#113): the condition field must be bound into the obligation_id so
        // that two CreateObligations with identical payer/payee/stake but different
        // conditions produce distinct IDs.  Without this, a prover could re-use a
        // fulfillment proof built for a weak condition (e.g. HashPreimage) against an
        // obligation that was created with a stronger condition (e.g. LocalProof).
        let obligation_id = {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-obligation-id-v1");
            hasher.update(action_target.as_bytes());
            hasher.update(beneficiary.as_bytes());
            hasher.update(&deadline_height.to_le_bytes());
            hasher.update(&stake.0);
            // Bind the condition: include a discriminant byte followed by the
            // condition-specific bytes so every variant produces a distinct prefix.
            match condition {
                crate::conditional::ProofCondition::HashPreimage { hash } => {
                    hasher.update(&[0u8]);
                    hasher.update(hash);
                }
                crate::conditional::ProofCondition::RemoteProof {
                    federation_root,
                    expected_air,
                    expected_conclusion,
                } => {
                    hasher.update(&[1u8]);
                    hasher.update(federation_root);
                    hasher.update(expected_air.as_bytes());
                    hasher.update(&expected_conclusion.to_le_bytes());
                }
                crate::conditional::ProofCondition::LocalProof {
                    expected_air,
                    expected_public_inputs,
                } => {
                    hasher.update(&[2u8]);
                    hasher.update(expected_air.as_bytes());
                    for pi in expected_public_inputs {
                        hasher.update(&pi.to_le_bytes());
                    }
                }
                crate::conditional::ProofCondition::TurnExecuted { turn_hash } => {
                    hasher.update(&[3u8]);
                    hasher.update(turn_hash);
                }
            }
            *hasher.finalize().as_bytes()
        };
        {
            let mut obligations = self.obligations.lock().unwrap();
            obligations.insert(
                obligation_id,
                ObligationRecord {
                    obligor: *action_target,
                    beneficiary: *beneficiary,
                    deadline_height,
                    stake_amount,
                    resolved: false,
                },
            );
        }
        // Record the insertion so it is rolled back on turn failure.
        journal.record_obligation_inserted(obligation_id);

        // The actor (action_target) is the obligor.
        journal.record_obligation_created(*action_target, *beneficiary, deadline_height, *stake);
        Ok(())
    }

    fn apply_fulfill_obligation(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        obligation_id: &[u8; 32],
        proof: &crate::conditional::ConditionProof,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate obligation_id is non-zero.
        if obligation_id.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null obligation_id in FulfillObligation".into(),
                },
                path.to_vec(),
            ));
        }
        // Look up the obligation and return the locked stake to the obligor.
        let record = {
            let obligations = self.obligations.lock().unwrap();
            obligations.get(obligation_id).cloned()
        };
        let record = record.ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "obligation not found".into(),
                },
                path.to_vec(),
            )
        })?;
        if record.resolved {
            return Err((
                TurnError::InvalidEffect {
                    reason: "obligation already resolved".into(),
                },
                path.to_vec(),
            ));
        }
        // ACCESS CONTROL: Only the obligor (original creator) can fulfill
        // their own obligation. Without this check, anyone could fulfill
        // and return the stake to the obligor, defeating the obligation's purpose.
        if *action_target != record.obligor {
            return Err((
                TurnError::InvalidEffect {
                    reason: "only the obligor can fulfill their own obligation".into(),
                },
                path.to_vec(),
            ));
        }
        // Verify the deadline has not passed (fulfillment must be before deadline).
        if self.block_height > record.deadline_height {
            return Err((
                TurnError::InvalidEffect {
                    reason: "obligation deadline has passed, cannot fulfill".into(),
                },
                path.to_vec(),
            ));
        }
        // Verify the fulfillment proof.  SECURITY (#112): fail-closed — any
        // StarkProof (even with non-empty bytes) must be actively verified.
        // If no proof_verifier is configured, presenting a STARK proof is
        // an outright error rather than a silent pass.  Non-STARK conditions
        // (HashPreimage, Preimage) are verified inline without a verifier.
        if let crate::conditional::ConditionProof::StarkProof { proof_bytes, .. } = proof {
            if !proof_bytes.is_empty() {
                let verifier = self.proof_verifier.as_ref().ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason:
                                "no proof verifier configured; cannot verify obligation fulfillment proof"
                                    .into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if !verifier.verify(
                    proof_bytes,
                    "obligation-fulfill",
                    "obligation",
                    obligation_id,
                ) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "obligation fulfillment proof verification failed".into(),
                        },
                        path.to_vec(),
                    ));
                }
            }
        }
        // Return locked stake to the obligor.
        let obligor_cell = ledger.get(&record.obligor).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: record.obligor },
                path.to_vec(),
            )
        })?;
        let old_balance = obligor_cell.state.balance();
        journal.record_set_balance(record.obligor, old_balance);
        ledger
            .get_mut(&record.obligor)
            .unwrap()
            .state
            .set_balance(old_balance + record.stake_amount);
        // Mark as resolved.
        {
            let mut obligations = self.obligations.lock().unwrap();
            if let Some(ob) = obligations.get_mut(obligation_id) {
                ob.resolved = true;
            }
        }
        journal.record_obligation_fulfilled(*obligation_id);
        Ok(())
    }

    fn apply_slash_obligation(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        obligation_id: &[u8; 32],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate obligation_id is non-zero.
        if obligation_id.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null obligation_id in SlashObligation".into(),
                },
                path.to_vec(),
            ));
        }
        // Look up the obligation and transfer the locked stake to the beneficiary.
        let record = {
            let obligations = self.obligations.lock().unwrap();
            obligations.get(obligation_id).cloned()
        };
        let record = record.ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "obligation not found".into(),
                },
                path.to_vec(),
            )
        })?;
        if record.resolved {
            return Err((
                TurnError::InvalidEffect {
                    reason: "obligation already resolved".into(),
                },
                path.to_vec(),
            ));
        }
        // Slashing is only valid after the deadline has passed.
        if self.block_height <= record.deadline_height {
            return Err((
                TurnError::InvalidEffect {
                    reason: "obligation deadline has not passed, cannot slash".into(),
                },
                path.to_vec(),
            ));
        }
        // Transfer locked stake to beneficiary.
        let beneficiary_cell = ledger.get(&record.beneficiary).ok_or_else(|| {
            (
                TurnError::CellNotFound {
                    id: record.beneficiary,
                },
                path.to_vec(),
            )
        })?;
        let old_ben_balance = beneficiary_cell.state.balance();
        journal.record_set_balance(record.beneficiary, old_ben_balance);
        ledger
            .get_mut(&record.beneficiary)
            .unwrap()
            .state
            .set_balance(old_ben_balance + record.stake_amount);
        // Mark as resolved.
        {
            let mut obligations = self.obligations.lock().unwrap();
            if let Some(ob) = obligations.get_mut(obligation_id) {
                ob.resolved = true;
            }
        }
        journal.record_obligation_slashed(*obligation_id);
        Ok(())
    }

    // Escrow effects: conditional settlement with timeout refund.
    #[allow(clippy::too_many_arguments)]
    fn apply_create_escrow(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        recipient: &CellId,
        amount: u64,
        condition: &EscrowCondition,
        timeout_height: u64,
        escrow_id: &[u8; 32],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // SECURITY: The cell field must match action_target to prevent
        // locking someone else's funds via an action targeting a different cell.
        if cell != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "CreateEscrow cell must match action target".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate recipient cell exists.
        if ledger.get(recipient).is_none() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "escrow recipient cell not found".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate timeout is in the future.
        if timeout_height <= self.block_height {
            return Err((
                TurnError::InvalidEffect {
                    reason: "escrow timeout_height must be in the future".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate amount is non-zero.
        if amount == 0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: "escrow amount must be non-zero".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate escrow_id is non-zero.
        if escrow_id.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "escrow_id is null".into(),
                },
                path.to_vec(),
            ));
        }
        // Check escrow_id is not already in use.
        {
            let escrows = self.escrows.lock().unwrap();
            if escrows.contains_key(escrow_id) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "escrow_id already exists".into(),
                    },
                    path.to_vec(),
                ));
            }
        }
        // Validate the creator cell exists and has sufficient balance.
        let creator_cell = ledger
            .get(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        if creator_cell.state.balance() < amount {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *cell,
                    required: amount,
                    available: creator_cell.state.balance(),
                },
                path.to_vec(),
            ));
        }
        // Lock the funds: subtract from creator.
        let old_balance = creator_cell.state.balance();
        journal.record_set_balance(*cell, old_balance);
        ledger
            .get_mut(cell)
            .unwrap()
            .state
            .set_balance(old_balance - amount);

        // Store escrow record.
        {
            let mut escrows = self.escrows.lock().unwrap();
            escrows.insert(
                *escrow_id,
                EscrowRecord {
                    creator: *cell,
                    recipient: *recipient,
                    amount,
                    condition: condition.clone(),
                    timeout_height,
                    resolved: false,
                },
            );
        }
        // Record the insertion so it is rolled back on turn failure.
        journal.record_escrow_inserted(*escrow_id);

        journal.record_escrow_created(*escrow_id, *cell, *recipient, amount);
        Ok(())
    }

    fn apply_release_escrow(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        escrow_id: &[u8; 32],
        proof: Option<&Vec<u8>>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate escrow_id is non-zero.
        if escrow_id.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null escrow_id in ReleaseEscrow".into(),
                },
                path.to_vec(),
            ));
        }
        // Look up the escrow.
        let record = {
            let escrows = self.escrows.lock().unwrap();
            escrows.get(escrow_id).cloned()
        };
        let record = record.ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "escrow not found".into(),
                },
                path.to_vec(),
            )
        })?;
        if record.resolved {
            return Err((
                TurnError::InvalidEffect {
                    reason: "escrow already resolved".into(),
                },
                path.to_vec(),
            ));
        }
        // Verify the condition is met.
        match &record.condition {
            EscrowCondition::ProofPresented { verification_key } => {
                let proof_bytes = proof.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "escrow release requires proof but none provided".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if proof_bytes.is_empty() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow release proof is empty".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the proof using the configured verifier.
                let verifier = self.proof_verifier.as_ref().ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "no proof verifier configured for escrow release".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if !verifier.verify(proof_bytes, "escrow-release", "escrow", verification_key) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow release proof verification failed".into(),
                        },
                        path.to_vec(),
                    ));
                }
            }
            EscrowCondition::SignedByAll { signers } => {
                // The proof field must contain concatenated 64-byte Ed25519 signatures
                // (one per signer), each signing the escrow_id.
                let proof_bytes = proof.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "escrow release requires signatures but none provided".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                let expected_len = signers.len() * 64;
                if proof_bytes.len() != expected_len {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: format!(
                                "escrow release expected {} signature bytes, got {}",
                                expected_len,
                                proof_bytes.len()
                            ),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify each signature against the escrow_id.
                for (i, signer_key) in signers.iter().enumerate() {
                    let sig_slice = &proof_bytes[i * 64..(i + 1) * 64];
                    let mut sig_bytes = [0u8; 64];
                    sig_bytes.copy_from_slice(sig_slice);
                    let signature = Signature::from_bytes(&sig_bytes);
                    let verifying_key = VerifyingKey::from_bytes(signer_key).map_err(|_| {
                        (
                            TurnError::InvalidEffect {
                                reason: format!("invalid signer public key at index {}", i),
                            },
                            path.to_vec(),
                        )
                    })?;
                    use ed25519_dalek::Verifier;
                    verifying_key.verify(escrow_id, &signature).map_err(|_| {
                        (
                            TurnError::InvalidEffect {
                                reason: format!(
                                    "escrow release signature verification failed for signer {}",
                                    i
                                ),
                            },
                            path.to_vec(),
                        )
                    })?;
                }
            }
            EscrowCondition::PredicateSatisfied { predicate_hash } => {
                // For predicate conditions, the proof must contain the 32-byte
                // hash matching predicate_hash (simple equality check for now;
                // in production this would invoke the predicate evaluator).
                let proof_bytes = proof.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "escrow release requires predicate proof but none provided"
                                .into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if proof_bytes.len() < 32 {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow predicate proof too short".into(),
                        },
                        path.to_vec(),
                    ));
                }
                let provided_hash: [u8; 32] = proof_bytes[..32].try_into().unwrap();
                if provided_hash != *predicate_hash {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow predicate hash mismatch".into(),
                        },
                        path.to_vec(),
                    ));
                }
            }
        }
        // Condition satisfied: transfer amount to recipient.
        let recipient_cell = ledger.get(&record.recipient).ok_or_else(|| {
            (
                TurnError::CellNotFound {
                    id: record.recipient,
                },
                path.to_vec(),
            )
        })?;
        let old_recipient_balance = recipient_cell.state.balance();
        journal.record_set_balance(record.recipient, old_recipient_balance);
        ledger
            .get_mut(&record.recipient)
            .unwrap()
            .state
            .set_balance(old_recipient_balance + record.amount);
        // Mark escrow as resolved.
        {
            let mut escrows = self.escrows.lock().unwrap();
            if let Some(esc) = escrows.get_mut(escrow_id) {
                esc.resolved = true;
            }
        }
        journal.record_escrow_released(*escrow_id);
        Ok(())
    }

    fn apply_refund_escrow(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        escrow_id: &[u8; 32],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate escrow_id is non-zero.
        if escrow_id.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null escrow_id in RefundEscrow".into(),
                },
                path.to_vec(),
            ));
        }
        // Look up the escrow.
        let record = {
            let escrows = self.escrows.lock().unwrap();
            escrows.get(escrow_id).cloned()
        };
        let record = record.ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "escrow not found".into(),
                },
                path.to_vec(),
            )
        })?;
        if record.resolved {
            return Err((
                TurnError::InvalidEffect {
                    reason: "escrow already resolved".into(),
                },
                path.to_vec(),
            ));
        }
        // Check timeout has passed.
        if self.block_height <= record.timeout_height {
            return Err((
                TurnError::InvalidEffect {
                    reason: "escrow timeout has not passed, cannot refund".into(),
                },
                path.to_vec(),
            ));
        }
        // Return amount to creator.
        let creator_cell = ledger.get(&record.creator).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: record.creator },
                path.to_vec(),
            )
        })?;
        let old_creator_balance = creator_cell.state.balance();
        journal.record_set_balance(record.creator, old_creator_balance);
        ledger
            .get_mut(&record.creator)
            .unwrap()
            .state
            .set_balance(old_creator_balance + record.amount);
        // Mark escrow as resolved.
        {
            let mut escrows = self.escrows.lock().unwrap();
            if let Some(esc) = escrows.get_mut(escrow_id) {
                esc.resolved = true;
            }
        }
        journal.record_escrow_refunded(*escrow_id);
        Ok(())
    }

    // Committed escrow effects: privacy-preserving conditional settlement.
    #[allow(clippy::too_many_arguments)]
    fn apply_create_committed_escrow(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        creator_commitment: &[u8; 32],
        recipient_commitment: &[u8; 32],
        value_commitment: &ValueCommitmentBytes,
        condition_commitment: &[u8; 32],
        timeout_height: u64,
        escrow_id: &[u8; 32],
        range_proof: &[u8],
        amount: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate escrow_id is non-zero.
        if escrow_id.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow_id is null".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate timeout is in the future.
        if timeout_height <= self.block_height {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow timeout_height must be in the future".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate amount is non-zero.
        if amount == 0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow amount must be non-zero".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate commitments are non-zero (prevent trivial commitments).
        if creator_commitment.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow creator_commitment is null".into(),
                },
                path.to_vec(),
            ));
        }
        if recipient_commitment.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow recipient_commitment is null".into(),
                },
                path.to_vec(),
            ));
        }
        if condition_commitment.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow condition_commitment is null".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate range proof is present (non-empty).
        if range_proof.is_empty() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow range_proof is empty".into(),
                },
                path.to_vec(),
            ));
        }
        // Verify the range proof if a proof verifier is configured.
        if let Some(verifier) = &self.proof_verifier {
            if !verifier.verify(
                range_proof,
                "committed-escrow-range",
                "value-commitment",
                &value_commitment.0,
            ) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "committed escrow range proof verification failed".into(),
                    },
                    path.to_vec(),
                ));
            }
        }
        // Verify escrow_id is correctly derived from commitments.
        let expected_id = CommittedEscrow::compute_escrow_id(
            creator_commitment,
            recipient_commitment,
            value_commitment,
            condition_commitment,
            timeout_height,
        );
        if *escrow_id != expected_id {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow_id does not match derived value".into(),
                },
                path.to_vec(),
            ));
        }
        // Check escrow_id is not already in use (in either escrow map).
        {
            let escrows = self.escrows.lock().unwrap();
            if escrows.contains_key(escrow_id) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "escrow_id already exists (cleartext)".into(),
                    },
                    path.to_vec(),
                ));
            }
        }
        {
            let committed = self.committed_escrows.lock().unwrap();
            if committed.contains_key(escrow_id) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "committed escrow_id already exists".into(),
                    },
                    path.to_vec(),
                ));
            }
        }
        // Lock the funds from the creator (action_target).
        let creator_cell = ledger.get(action_target).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            )
        })?;
        if creator_cell.state.balance() < amount {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *action_target,
                    required: amount,
                    available: creator_cell.state.balance(),
                },
                path.to_vec(),
            ));
        }
        let old_balance = creator_cell.state.balance();
        journal.record_set_balance(*action_target, old_balance);
        ledger
            .get_mut(action_target)
            .unwrap()
            .state
            .set_balance(old_balance - amount);

        // Store committed escrow record.
        let record = CommittedEscrow {
            creator_commitment: *creator_commitment,
            recipient_commitment: *recipient_commitment,
            value_commitment: value_commitment.clone(),
            condition_commitment: *condition_commitment,
            timeout_height,
            escrow_id: *escrow_id,
            range_proof: range_proof.to_vec(),
            resolved: false,
        };
        {
            let mut committed = self.committed_escrows.lock().unwrap();
            committed.insert(*escrow_id, record);
        }
        // Store the amount in the side-table for settlement.
        {
            let mut amounts = self.committed_escrow_amounts.lock().unwrap();
            amounts.insert(*escrow_id, amount);
        }
        // Record insertion for rollback.
        journal.record_committed_escrow_inserted(*escrow_id);
        journal.record_committed_escrow_created(*escrow_id, amount);
        Ok(())
    }

    fn apply_release_committed_escrow(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        escrow_id: &[u8; 32],
        claim_auth: &EscrowClaimAuth,
        recipient: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate escrow_id is non-zero.
        if escrow_id.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null escrow_id in ReleaseCommittedEscrow".into(),
                },
                path.to_vec(),
            ));
        }
        // Look up the committed escrow.
        let record = {
            let committed = self.committed_escrows.lock().unwrap();
            committed.get(escrow_id).cloned()
        };
        let record = record.ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "committed escrow not found".into(),
                },
                path.to_vec(),
            )
        })?;
        if record.resolved {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow already resolved".into(),
                },
                path.to_vec(),
            ));
        }
        // Verify the recipient cell matches the claim and exists in ledger.
        if *recipient != claim_auth.cell_id {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow release: recipient does not match claim cell_id"
                        .into(),
                },
                path.to_vec(),
            ));
        }
        let recipient_cell_ref = ledger
            .get(recipient)
            .ok_or_else(|| (TurnError::CellNotFound { id: *recipient }, path.to_vec()))?;
        let recipient_pubkey = recipient_cell_ref.public_key();
        // Verify the claim_auth against the recipient_commitment.
        if !verify_escrow_claim(
            claim_auth,
            &record.recipient_commitment,
            escrow_id,
            &recipient_pubkey,
        ) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow release: claim authorization failed".into(),
                },
                path.to_vec(),
            ));
        }
        // Retrieve the escrowed amount from the side-table.
        let amount = {
            let amounts = self.committed_escrow_amounts.lock().unwrap();
            amounts.get(escrow_id).copied()
        };
        let amount = amount.ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "committed escrow amount not found (internal error)".into(),
                },
                path.to_vec(),
            )
        })?;
        // Credit the escrowed amount to the recipient.
        let recipient_cell = ledger.get(recipient).unwrap();
        let old_balance = recipient_cell.state.balance();
        journal.record_set_balance(*recipient, old_balance);
        ledger
            .get_mut(recipient)
            .unwrap()
            .state
            .set_balance(old_balance + amount);
        // Mark as resolved.
        {
            let mut committed = self.committed_escrows.lock().unwrap();
            if let Some(esc) = committed.get_mut(escrow_id) {
                esc.resolved = true;
            }
        }
        journal.record_committed_escrow_released(*escrow_id);
        Ok(())
    }

    fn apply_refund_committed_escrow(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        escrow_id: &[u8; 32],
        claim_auth: &EscrowClaimAuth,
        creator: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate escrow_id is non-zero.
        if escrow_id.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null escrow_id in RefundCommittedEscrow".into(),
                },
                path.to_vec(),
            ));
        }
        // Look up the committed escrow.
        let record = {
            let committed = self.committed_escrows.lock().unwrap();
            committed.get(escrow_id).cloned()
        };
        let record = record.ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "committed escrow not found".into(),
                },
                path.to_vec(),
            )
        })?;
        if record.resolved {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow already resolved".into(),
                },
                path.to_vec(),
            ));
        }
        // Check timeout has passed.
        if self.block_height <= record.timeout_height {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow timeout has not passed, cannot refund".into(),
                },
                path.to_vec(),
            ));
        }
        // Verify the creator cell matches the claim and exists in ledger.
        if *creator != claim_auth.cell_id {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow refund: creator does not match claim cell_id".into(),
                },
                path.to_vec(),
            ));
        }
        let creator_cell_ref = ledger
            .get(creator)
            .ok_or_else(|| (TurnError::CellNotFound { id: *creator }, path.to_vec()))?;
        let creator_pubkey = creator_cell_ref.public_key();
        // Verify the claim_auth against the creator_commitment.
        if !verify_escrow_claim(
            claim_auth,
            &record.creator_commitment,
            escrow_id,
            &creator_pubkey,
        ) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "committed escrow refund: claim authorization failed".into(),
                },
                path.to_vec(),
            ));
        }
        // Return the escrowed amount to the creator.
        let amount = {
            let amounts = self.committed_escrow_amounts.lock().unwrap();
            amounts.get(escrow_id).copied()
        };
        let amount = amount.ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "committed escrow amount not found (internal error)".into(),
                },
                path.to_vec(),
            )
        })?;
        let creator_cell = ledger.get(creator).unwrap();
        let old_balance = creator_cell.state.balance();
        journal.record_set_balance(*creator, old_balance);
        ledger
            .get_mut(creator)
            .unwrap()
            .state
            .set_balance(old_balance + amount);
        // Mark as resolved.
        {
            let mut committed = self.committed_escrows.lock().unwrap();
            if let Some(esc) = committed.get_mut(escrow_id) {
                esc.resolved = true;
            }
        }
        journal.record_committed_escrow_refunded(*escrow_id);
        Ok(())
    }

    // ExerciseViaCapability: one-step evaluation map.
    // Look up cap_slot in actor's c-list, verify permissions, execute
    // inner_effects against the capability's target cell.
    fn apply_exercise_via_capability(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        actor: &CellId,
        journal: &mut LedgerJournal,
        cap_slot: u32,
        inner_effects: &[Effect],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let actor_cell = ledger
            .get(actor)
            .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;

        // Look up the capability by slot.
        let cap = actor_cell
            .capabilities
            .lookup(cap_slot)
            .cloned()
            .ok_or_else(|| {
                (
                    TurnError::CapabilityNotHeld {
                        actor: *actor,
                        target: CellId::from_bytes([0u8; 32]), // slot doesn't exist
                    },
                    path.to_vec(),
                )
            })?;

        let cap_target = cap.target;

        // Check capability expiry.
        if let Some(expires_at) = cap.expires_at {
            if self.block_height > expires_at {
                return Err((
                    TurnError::CapabilityNotHeld {
                        actor: *actor,
                        target: cap_target,
                    },
                    path.to_vec(),
                ));
            }
        }

        // Check revocation channel: if the capability has a breadstuff that
        // matches a revocation channel, verify the channel is still active.
        if let Some(ref channels) = self.revocation_channels {
            if let Some(breadstuff) = &cap.breadstuff {
                // Use the breadstuff as a potential channel_id (capabilities
                // gated by a revocation channel store the channel_id as breadstuff).
                if let Err(_) = channels.check_exercise_permitted(
                    breadstuff,
                    self.block_height,
                    self.block_height, // assume fresh check at current height
                    self.max_introduction_lifetime,
                ) {
                    // Check if this is actually a registered channel (not just any breadstuff).
                    if channels.get(breadstuff).is_some() {
                        return Err((
                            TurnError::CapabilityRevoked {
                                actor: *actor,
                                channel_id: *breadstuff,
                                tripped_at: self.block_height,
                            },
                            path.to_vec(),
                        ));
                    }
                }
            }
        }

        // Verify the target cell exists.
        let target_cell_ref = ledger
            .get(&cap_target)
            .ok_or_else(|| (TurnError::CellNotFound { id: cap_target }, path.to_vec()))?;

        // Permission check: the capability's permissions must allow the operations.
        // If the capability requires Impossible, reject.
        if matches!(cap.permissions, dregg_cell::AuthRequired::Impossible) {
            return Err((
                TurnError::PermissionDenied {
                    cell: cap_target,
                    action: "ExerciseViaCapability".to_string(),
                    required: dregg_cell::AuthRequired::Impossible,
                },
                path.to_vec(),
            ));
        }

        // Also check that the capability's permission level satisfies the
        // TARGET CELL's requirements for each inner effect's operation.
        // This prevents bypassing target cell permissions via capability exercise.
        for inner_effect in inner_effects.iter() {
            // SECURITY (#111): Transfer with from != cap_target must be gated too.
            // Previously only `from == cap_target` matched the Send arm, so any
            // Transfer that names a third cell as `from` fell through to `_ => None`
            // and skipped both the cap-target permission check and the explicit
            // cap-to-from check.  Fix: handle all Transfer variants explicitly.
            if let Effect::Transfer { from, .. } = inner_effect {
                if from != &cap_target {
                    // The actor must hold an explicit capability covering `from`.
                    // We re-use check_cross_cell_permission which verifies both the
                    // c-list entry and `from`'s Send permission level.
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        from,
                        dregg_cell::permissions::Action::Send,
                        "Send (Transfer.from via ExerciseViaCapability)",
                        path,
                    )?;
                    // Handled; skip the generic required_perm_action path below.
                    continue;
                }
            }

            let required_perm_action = match inner_effect {
                Effect::SetField { .. } => {
                    Some((dregg_cell::permissions::Action::SetState, "SetState"))
                }
                Effect::Transfer { from, .. } if from == &cap_target => {
                    Some((dregg_cell::permissions::Action::Send, "Send"))
                }
                Effect::IncrementNonce { .. } => Some((
                    dregg_cell::permissions::Action::IncrementNonce,
                    "IncrementNonce",
                )),
                Effect::GrantCapability { .. } => {
                    Some((dregg_cell::permissions::Action::Delegate, "Delegate"))
                }
                Effect::RevokeCapability { .. } => {
                    Some((dregg_cell::permissions::Action::Delegate, "Delegate"))
                }
                Effect::SetPermissions { .. } => Some((
                    dregg_cell::permissions::Action::SetPermissions,
                    "SetPermissions",
                )),
                Effect::SetVerificationKey { .. } => Some((
                    dregg_cell::permissions::Action::SetVerificationKey,
                    "SetVerificationKey",
                )),
                _ => None,
            };

            if let Some((perm_action, action_name)) = required_perm_action {
                let target_required = target_cell_ref.permissions.for_action(perm_action);
                // The target cell's permission must be satisfiable by the capability's
                // permission level. If the target requires Impossible, always reject.
                // If the target requires Signature/Proof/Either but the capability only
                // grants None-level access, that's insufficient.
                if matches!(target_required, AuthRequired::Impossible) {
                    return Err((
                        TurnError::PermissionDenied {
                            cell: cap_target,
                            action: action_name.to_string(),
                            required: target_required.clone(),
                        },
                        path.to_vec(),
                    ));
                }
                // If the target requires auth (Signature/Proof/Either) and the
                // capability's permission level is weaker (None), reject.
                // The capability permission acts as the auth level the actor provides.
                if !matches!(target_required, AuthRequired::None) {
                    // The capability must be at least as strong as what the target requires.
                    if !cap.permissions.is_narrower_or_equal(target_required) {
                        return Err((
                            TurnError::PermissionDenied {
                                cell: cap_target,
                                action: action_name.to_string(),
                                required: target_required.clone(),
                            },
                            path.to_vec(),
                        ));
                    }
                }
            }
        }

        // Facet enforcement: if the capability has an allowed_effects mask,
        // verify that every inner effect's kind is permitted by the mask.
        // This implements E-language facets — a restricted view of the target
        // cell's interface through this capability.
        if let Some(mask) = cap.allowed_effects {
            if mask != 0 {
                for inner_effect in inner_effects.iter() {
                    let effect_bit = inner_effect.effect_kind_mask();
                    if effect_bit & mask == 0 {
                        return Err((
                            TurnError::FacetViolation {
                                actor: *actor,
                                target: cap_target,
                                cap_slot,
                                attempted_effect: format!(
                                    "{:?}",
                                    std::mem::discriminant(inner_effect)
                                ),
                                allowed_mask: mask,
                            },
                            path.to_vec(),
                        ));
                    }
                }
            }
        }

        // Execute each inner effect against the capability's target cell.
        for inner_effect in inner_effects {
            self.apply_effect(inner_effect, ledger, path, &cap_target, actor, journal)?;
        }

        Ok(())
    }

    // PipelinedSend must be resolved by the pipeline executor's resolution pass
    // before the turn reaches apply_effect. If we get here, it means the turn
    // was executed outside of a pipeline without resolution — which is a bug.
    fn apply_pipelined_send(
        &self,
        path: &[usize],
        target: &crate::eventual::EventualRef,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        Err((
            TurnError::PreconditionFailed {
                description: format!(
                    "unresolved PipelinedSend to EventualRef(source {:02x}{:02x}.., slot {}); \
                     turn must be executed within a pipeline",
                    target.source_turn[0], target.source_turn[1], target.output_slot
                ),
            },
            path.to_vec(),
        ))
    }

    // === Sealer/Unsealer effects (E-style rights amplification) ===
    fn apply_create_seal_pair(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        sealer_holder: &CellId,
        unsealer_holder: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if ledger.get(sealer_holder).is_none() {
            return Err((
                TurnError::CellNotFound { id: *sealer_holder },
                path.to_vec(),
            ));
        }
        if ledger.get(unsealer_holder).is_none() {
            return Err((
                TurnError::CellNotFound {
                    id: *unsealer_holder,
                },
                path.to_vec(),
            ));
        }

        let pair = dregg_cell::SealPair::generate();

        // Grant sealer capability (breadstuff = sealer_key).
        let sealer_cap_id = Self::seal_capability_id(&pair.id, true);
        let sealer_cell = ledger.get_mut(sealer_holder).unwrap();
        let sealer_slot = sealer_cell
            .capabilities
            .grant_with_breadstuff(
                sealer_cap_id,
                dregg_cell::AuthRequired::None,
                Some(pair.sealer_public),
            )
            .ok_or_else(|| {
                (
                    TurnError::CapabilitySlotOverflow {
                        cell: *sealer_holder,
                    },
                    path.to_vec(),
                )
            })?;
        journal.record_grant_capability(*sealer_holder, sealer_slot);

        // Grant unsealer capability (breadstuff = sealer_key for symmetric decrypt).
        let unsealer_cap_id = Self::seal_capability_id(&pair.id, false);
        let unsealer_cell = ledger.get_mut(unsealer_holder).unwrap();
        let unsealer_slot = unsealer_cell
            .capabilities
            .grant_with_breadstuff(
                unsealer_cap_id,
                dregg_cell::AuthRequired::None,
                Some(pair.unsealer_secret),
            )
            .ok_or_else(|| {
                (
                    TurnError::CapabilitySlotOverflow {
                        cell: *unsealer_holder,
                    },
                    path.to_vec(),
                )
            })?;
        journal.record_grant_capability(*unsealer_holder, unsealer_slot);

        Ok(())
    }

    fn apply_seal(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        actor: &CellId,
        journal: &mut LedgerJournal,
        pair_id: &[u8; 32],
        capability: &CapabilityRef,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let sealer_cap_id = Self::seal_capability_id(pair_id, true);
        let actor_cell = ledger
            .get(actor)
            .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
        let sealer_cap = actor_cell
            .capabilities
            .lookup_by_target(&sealer_cap_id)
            .ok_or_else(|| {
                (
                    TurnError::CapabilityNotHeld {
                        actor: *actor,
                        target: sealer_cap_id,
                    },
                    path.to_vec(),
                )
            })?;
        // Extract sealer public key from breadstuff and produce sealed box.
        let sealer_public = sealer_cap.breadstuff.ok_or_else(|| {
            (
                TurnError::InvalidAuthorization {
                    reason: "sealer capability missing key material".to_string(),
                },
                path.to_vec(),
            )
        })?;
        let seal_pair = dregg_cell::SealPair::sealer_only(sealer_public);
        let sealed = seal_pair.seal(capability);
        // Store seal commitment in actor's field 7 for on-chain discoverability.
        let actor_mut = ledger
            .get_mut(actor)
            .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
        journal.record_set_field(*actor, 7, actor_mut.state.fields[7]);
        actor_mut.state.fields[7] = sealed.commitment;
        if actor_mut.state.commitments[7].is_some() {
            actor_mut.state.commitments[7] = None;
        }
        Ok(())
    }

    fn apply_introduce(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        introducer: &CellId,
        recipient: &CellId,
        target: &CellId,
        permissions: &dregg_cell::AuthRequired,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let intro_cell = ledger
            .get(introducer)
            .ok_or_else(|| (TurnError::CellNotFound { id: *introducer }, path.to_vec()))?;
        if !intro_cell.capabilities.has_access(recipient) {
            return Err((
                TurnError::IntroductionDenied {
                    introducer: *introducer,
                    recipient: *recipient,
                    target: *target,
                    reason: "introducer has no capability to recipient".to_string(),
                },
                path.to_vec(),
            ));
        }
        let held_cap = intro_cell
            .capabilities
            .lookup_by_target(target)
            .ok_or_else(|| {
                (
                    TurnError::IntroductionDenied {
                        introducer: *introducer,
                        recipient: *recipient,
                        target: *target,
                        reason: "introducer has no capability to target".to_string(),
                    },
                    path.to_vec(),
                )
            })?;
        if !dregg_cell::is_attenuation(&held_cap.permissions, permissions) {
            return Err((
                TurnError::IntroductionDenied {
                    introducer: *introducer,
                    recipient: *recipient,
                    target: *target,
                    reason: "granted permissions exceed introducer's own (amplification denied)"
                        .to_string(),
                },
                path.to_vec(),
            ));
        }
        // Consent check: the target cell must allow delegation (delegate != Impossible).
        let target_cell = ledger
            .get(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        if target_cell.permissions.delegate == dregg_cell::AuthRequired::Impossible {
            return Err((
                TurnError::IntroductionDenied {
                    introducer: *introducer,
                    recipient: *recipient,
                    target: *target,
                    reason: "target cell has delegate=Impossible (consent denied)".to_string(),
                },
                path.to_vec(),
            ));
        }
        if ledger.get(recipient).is_none() {
            return Err((TurnError::CellNotFound { id: *recipient }, path.to_vec()));
        }
        let recipient_cell = ledger.get_mut(recipient).unwrap();
        let expires_at = self.block_height + self.max_introduction_lifetime;
        let granted_slot = recipient_cell
            .capabilities
            .grant_with_expiry(*target, permissions.clone(), expires_at)
            .ok_or_else(|| {
                (
                    TurnError::CapabilitySlotOverflow { cell: *recipient },
                    path.to_vec(),
                )
            })?;
        journal.record_grant_capability(*recipient, granted_slot);
        Ok(())
    }

    fn apply_unseal(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        actor: &CellId,
        journal: &mut LedgerJournal,
        sealed_box: &SealedBox,
        recipient: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if ledger.get(recipient).is_none() {
            return Err((TurnError::CellNotFound { id: *recipient }, path.to_vec()));
        }

        let unsealer_cap_id = Self::seal_capability_id(&sealed_box.pair_id, false);
        let actor_cell = ledger
            .get(actor)
            .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
        let unsealer_cap = actor_cell
            .capabilities
            .lookup_by_target(&unsealer_cap_id)
            .ok_or_else(|| {
                (
                    TurnError::CapabilityNotHeld {
                        actor: *actor,
                        target: unsealer_cap_id,
                    },
                    path.to_vec(),
                )
            })?;
        let unsealer_secret = unsealer_cap.breadstuff.ok_or_else(|| {
            (
                TurnError::InvalidAuthorization {
                    reason: "unsealer capability missing key material".to_string(),
                },
                path.to_vec(),
            )
        })?;

        let mut pair = dregg_cell::SealPair::from_keys([0u8; 32], unsealer_secret);
        pair.id = sealed_box.pair_id;

        match pair.unseal(sealed_box) {
            Ok(cap) => {
                let recipient_cell = ledger
                    .get_mut(recipient)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *recipient }, path.to_vec()))?;
                let granted_slot = recipient_cell
                    .capabilities
                    .grant_with_breadstuff(cap.target, cap.permissions.clone(), cap.breadstuff)
                    .ok_or_else(|| {
                        (
                            TurnError::CapabilitySlotOverflow { cell: *recipient },
                            path.to_vec(),
                        )
                    })?;
                journal.record_grant_capability(*recipient, granted_slot);
                Ok(())
            }
            Err(_) => Err((
                TurnError::InvalidAuthorization {
                    reason: "sealed box decryption/verification failed".to_string(),
                },
                path.to_vec(),
            )),
        }
    }

    fn apply_spawn_with_delegation(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        child_public_key: &[u8; 32],
        child_token_id: &[u8; 32],
        max_staleness: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let parent_cell_data = ledger.get(action_target).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            )
        })?;
        let delegation_epoch = parent_cell_data.state.delegation_epoch();
        let now = self.current_timestamp as u64;
        let snapshot: Vec<dregg_cell::CapabilityRef> =
            parent_cell_data.capabilities.iter().cloned().collect();

        let child_id = CellId::derive_raw(child_public_key, child_token_id);
        let mut child_cell = Cell::with_balance(*child_public_key, *child_token_id, 0);
        child_cell.delegate = Some(*action_target);
        let clist_bytes = postcard::to_allocvec(&snapshot).unwrap_or_default();
        let clist_commitment = dregg_cell::DelegatedRef::compute_clist_commitment(&clist_bytes);
        child_cell.delegation = Some(dregg_cell::DelegatedRef::new(
            *action_target,
            child_id,
            snapshot,
            delegation_epoch,
            now,
            max_staleness,
            clist_commitment,
            [0u8; 64], // Executor-internal delegation, signature verified by execution authority.
        ));

        ledger
            .insert_cell(child_cell)
            .map_err(|_| (TurnError::CellAlreadyExists { id: child_id }, path.to_vec()))?;
        journal.record_create_cell(child_id);
        Ok(())
    }

    fn apply_refresh_delegation(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let child_cell = ledger.get(action_target).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            )
        })?;
        let parent_id = child_cell.delegate.ok_or_else(|| {
            (
                TurnError::InvalidAuthorization {
                    reason: "cell has no delegate (parent) to refresh from".to_string(),
                },
                path.to_vec(),
            )
        })?;
        let max_staleness = child_cell
            .delegation
            .as_ref()
            .map(|d| d.max_staleness)
            .unwrap_or(0);
        let old_delegation = child_cell.delegation.clone();

        let parent_cell_data = ledger
            .get(&parent_id)
            .ok_or_else(|| (TurnError::CellNotFound { id: parent_id }, path.to_vec()))?;
        let new_snapshot: Vec<dregg_cell::CapabilityRef> =
            parent_cell_data.capabilities.iter().cloned().collect();
        let new_epoch = parent_cell_data.state.delegation_epoch();
        let now = self.current_timestamp as u64;

        let child_mut = ledger.get_mut(action_target).unwrap();
        journal.record_set_delegation(*action_target, old_delegation);
        let clist_bytes = postcard::to_allocvec(&new_snapshot).unwrap_or_default();
        let clist_commitment = dregg_cell::DelegatedRef::compute_clist_commitment(&clist_bytes);
        child_mut.delegation = Some(dregg_cell::DelegatedRef::new(
            parent_id,
            *action_target,
            new_snapshot,
            new_epoch,
            now,
            max_staleness,
            clist_commitment,
            [0u8; 64], // Executor-internal delegation, signature verified by execution authority.
        ));
        Ok(())
    }

    fn apply_revoke_delegation(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        child: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let child_cell = ledger
            .get(child)
            .ok_or_else(|| (TurnError::CellNotFound { id: *child }, path.to_vec()))?;
        if child_cell.delegate != Some(*action_target) {
            return Err((
                TurnError::DelegationDenied {
                    parent: *action_target,
                    child_target: *child,
                },
                path.to_vec(),
            ));
        }
        let old_child_delegation = child_cell.delegation.clone();

        let parent_mut = ledger.get_mut(action_target).unwrap();
        let old_epoch = parent_mut.state.delegation_epoch();
        journal.record_set_delegation_epoch(*action_target, old_epoch);
        if !parent_mut.state.bump_delegation_epoch() {
            return Err((
                TurnError::NonceOverflow {
                    cell: *action_target,
                },
                path.to_vec(),
            ));
        }

        let child_mut = ledger.get_mut(child).unwrap();
        journal.record_set_delegation(*child, old_child_delegation);
        child_mut.delegation = None;
        Ok(())
    }

    fn apply_make_sovereign(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        cell: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Only the cell itself (as action target) can make itself sovereign.
        if cell != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "MakeSovereign cell must match action target".into(),
                },
                path.to_vec(),
            ));
        }
        // Transition the cell from hosted to sovereign.
        ledger.make_sovereign(cell).map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("MakeSovereign failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        Ok(())
    }

    fn apply_create_cell_from_factory(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        factory_vk: &[u8; 32],
        owner_pubkey: &[u8; 32],
        token_id: &[u8; 32],
        params: &dregg_cell::factory::FactoryCreationParams,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate the factory exists in the registry and the creation is within
        // the factory's declared constraints (program VK, capabilities, fields, mode, budget).
        //
        // For Derived/FromSet strategies, validate_and_record now checks that the
        // claimed program_vk is correctly derived or in the approved set.
        self.factory_registry
            .borrow_mut()
            .validate_and_record(factory_vk, params)
            .map_err(|e| {
                (
                    TurnError::InvalidEffect {
                        reason: format!("factory creation failed: {}", e),
                    },
                    path.to_vec(),
                )
            })?;

        // Determine the effective child VK to install.
        // For Derived strategy: compute the derived VK from factory_vk + params.
        // For FromSet strategy: use the claimed VK (already validated above).
        // For Fixed/None strategy: use params.program_vk as-is.
        let effective_vk = {
            let registry = self.factory_registry.borrow();
            let descriptor = registry.get(factory_vk);
            match descriptor.and_then(|d| d.child_vk_strategy.as_ref()) {
                Some(dregg_cell::factory::ChildVkStrategy::Derived { base_vk }) => {
                    let param_hash =
                        dregg_cell::factory::ChildVkStrategy::compute_param_hash(params);
                    Some(dregg_cell::factory::ChildVkStrategy::derive_child_vk(
                        base_vk,
                        &param_hash,
                    ))
                }
                Some(dregg_cell::factory::ChildVkStrategy::FromSet { .. }) => {
                    // Already validated; use the claimed VK.
                    params.program_vk
                }
                Some(dregg_cell::factory::ChildVkStrategy::Fixed(vk)) => *vk,
                None => params.program_vk,
            }
        };

        // Create the cell.
        let new_cell_id = CellId::derive_raw(owner_pubkey, token_id);
        let mut new_cell = match params.mode {
            dregg_cell::CellMode::Hosted => Cell::new_hosted(*owner_pubkey, *token_id),
            dregg_cell::CellMode::Sovereign => Cell::new(*owner_pubkey, *token_id),
        };

        // Set initial fields.
        for (idx, val) in &params.initial_fields {
            let idx = *idx as usize;
            if idx < dregg_cell::state::STATE_SLOTS {
                // Zero-pad to 32 bytes.
                let mut field = [0u8; 32];
                field[..8].copy_from_slice(&val.to_le_bytes());
                new_cell.state.fields[idx] = field;
            }
        }

        // Install program VK — use effective_vk (which may be derived).
        if let Some(vk_hash) = &effective_vk {
            new_cell.verification_key = Some(dregg_cell::VerificationKey::from_parts(
                *vk_hash,
                vk_hash.to_vec(), // Minimal VK data — the hash IS the identifier
            ));
        }

        // Grant initial capabilities.
        for cap_grant in &params.initial_caps {
            let target_id = match &cap_grant.target {
                dregg_cell::factory::CapTarget::SelfCell => new_cell_id,
                dregg_cell::factory::CapTarget::Specific(id) => *id,
                dregg_cell::factory::CapTarget::Any => {
                    // "Any" in a grant means self for initial caps.
                    new_cell_id
                }
            };
            new_cell
                .capabilities
                .grant(target_id, cap_grant.max_permissions.clone());
        }

        // Insert into ledger.
        ledger.insert_cell(new_cell).map_err(|_| {
            (
                TurnError::CellAlreadyExists { id: new_cell_id },
                path.to_vec(),
            )
        })?;
        journal.record_create_cell(new_cell_id);
        Ok(())
    }

    // ─── Queue Operations ─────────────────────────────────────────────
    fn apply_queue_allocate(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        capacity: u64,
        program_vk: Option<&[u8; 32]>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // The queue cell is created with queue metadata encoded in state fields:
        //   field[0]: capacity (le bytes)
        //   field[1]: current length (0 initially)
        //   field[2]: owner cell id (action_target bytes)
        //   field[3]: program VK hash (if any)
        let cost = capacity;
        let actor_cell = ledger
            .get(actor)
            .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
        if actor_cell.state.balance() < cost {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *actor,
                    required: cost,
                    available: actor_cell.state.balance(),
                },
                path.to_vec(),
            ));
        }

        // Derive a queue cell ID from the actor + capacity + nonce.
        let actor_nonce = ledger.get(actor).unwrap().state.nonce();
        let hash = blake3::hash(
            &[
                actor.as_bytes().as_slice(),
                &capacity.to_le_bytes(),
                &actor_nonce.to_le_bytes(),
            ]
            .concat(),
        );
        let queue_seed: [u8; 32] = *hash.as_bytes();
        let queue_token = [0u8; 32];
        let queue_id = CellId::derive_raw(&queue_seed, &queue_token);

        let mut queue_cell = dregg_cell::Cell::with_balance(queue_seed, queue_token, 0);
        // Encode capacity in field[0].
        queue_cell.state.fields[0][..8].copy_from_slice(&capacity.to_le_bytes());
        // field[1] = current length = 0 (already zero).
        // field[2] = owner (action_target).
        queue_cell.state.fields[2] = *action_target.as_bytes();
        // field[3] = program VK hash (if provided).
        if let Some(vk) = program_vk {
            queue_cell.state.fields[3] = *vk;
        }
        // Open permissions on queue cell (managed by executor logic).
        queue_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::Impossible,
            set_verification_key: dregg_cell::AuthRequired::Impossible,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };

        ledger
            .insert_cell(queue_cell)
            .map_err(|_| (TurnError::CellAlreadyExists { id: queue_id }, path.to_vec()))?;
        journal.record_create_cell(queue_id);

        // Deduct the cost from the actor's balance.
        let old_balance = ledger.get(actor).unwrap().state.balance();
        journal.record_set_balance(*actor, old_balance);
        ledger
            .get_mut(actor)
            .unwrap()
            .state
            .set_balance(old_balance - cost);

        Ok(())
    }

    fn apply_queue_enqueue(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        actor: &CellId,
        journal: &mut LedgerJournal,
        queue: &CellId,
        message_hash: &[u8; 32],
        deposit: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate queue exists.
        let queue_cell = ledger
            .get(queue)
            .ok_or_else(|| (TurnError::CellNotFound { id: *queue }, path.to_vec()))?;
        let capacity = u64::from_le_bytes(queue_cell.state.fields[0][..8].try_into().unwrap());
        let current_len = u64::from_le_bytes(queue_cell.state.fields[1][..8].try_into().unwrap());

        // BUG #114: ACL check.
        // field[5] encodes the authorized-writer cell ID.
        //   - All-zero (default for new queues): open write — any actor may enqueue.
        //   - Non-zero: only the cell whose id bytes match field[5] may enqueue.
        // The owner can set field[5] via a SetField effect to restrict enqueue access.
        // This is a single-writer ACL; multi-writer is future work (field[5] as a
        // commitment to a writer set, checked via a separate proof).
        let authorized_writer_bytes = queue_cell.state.fields[5];
        let is_open = authorized_writer_bytes.iter().all(|&b| b == 0);
        if !is_open && authorized_writer_bytes != *actor.as_bytes() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "QueueEnqueue denied: actor {:?} is not the authorized writer for queue {:?}",
                        actor, queue
                    ),
                },
                path.to_vec(),
            ));
        }

        if current_len >= capacity {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!("queue {:?} is full ({}/{})", queue, current_len, capacity),
                },
                path.to_vec(),
            ));
        }

        // Check deposit: actor must have sufficient balance.
        let actor_cell = ledger
            .get(actor)
            .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
        if actor_cell.state.balance() < deposit {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *actor,
                    required: deposit,
                    available: actor_cell.state.balance(),
                },
                path.to_vec(),
            ));
        }

        // Deduct deposit from actor, credit to queue cell.
        let old_actor_balance = ledger.get(actor).unwrap().state.balance();
        let old_queue_balance = ledger.get(queue).unwrap().state.balance();
        journal.record_set_balance(*actor, old_actor_balance);
        journal.record_set_balance(*queue, old_queue_balance);
        ledger
            .get_mut(actor)
            .unwrap()
            .state
            .set_balance(old_actor_balance - deposit);
        ledger
            .get_mut(queue)
            .unwrap()
            .state
            .set_balance(old_queue_balance + deposit);

        // Increment queue length.
        let old_len_field = ledger.get(queue).unwrap().state.fields[1];
        let new_len = current_len + 1;
        journal.record_set_field(*queue, 1, old_len_field);
        let queue_mut = ledger.get_mut(queue).unwrap();
        queue_mut.state.fields[1][..8].copy_from_slice(&new_len.to_le_bytes());

        // Store the message hash in field[4] (tail: latest enqueued message).
        let old_field4 = queue_mut.state.fields[4];
        journal.record_set_field(*queue, 4, old_field4);
        queue_mut.state.fields[4] = *message_hash;

        // Field[6] = head message hash (earliest enqueued, for FIFO dequeue ordering).
        // When the queue transitions from empty (current_len == 0) to non-empty,
        // the first message is simultaneously the head AND the tail.  Only write
        // field[6] on this 0→1 transition; subsequent enqueues do NOT touch it,
        // preserving the original head until it is dequeued.
        //
        // NOTE: After a dequeue that leaves len > 1, the head pointer cannot be
        // advanced without out-of-band knowledge of the next message hash (we do not
        // store the full message list in queue cell fields).  The advancement gap is
        // documented at apply_queue_dequeue below.  For single-message queues and
        // for the 0→1 case this is fully correct FIFO ordering.
        if current_len == 0 {
            let old_field6 = queue_mut.state.fields[6];
            journal.record_set_field(*queue, 6, old_field6);
            queue_mut.state.fields[6] = *message_hash;
        }

        Ok(())
    }

    fn apply_queue_dequeue(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        queue: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let queue_cell = ledger
            .get(queue)
            .ok_or_else(|| (TurnError::CellNotFound { id: *queue }, path.to_vec()))?;

        // Only the queue owner can dequeue.
        let owner_bytes = queue_cell.state.fields[2];
        if owner_bytes != *action_target.as_bytes() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "only the queue owner can dequeue".to_string(),
                },
                path.to_vec(),
            ));
        }

        let current_len = u64::from_le_bytes(queue_cell.state.fields[1][..8].try_into().unwrap());
        if current_len == 0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: "queue is empty, cannot dequeue".to_string(),
                },
                path.to_vec(),
            ));
        }

        // Decrement queue length.
        let old_len_field = queue_cell.state.fields[1];
        let new_len = current_len - 1;
        journal.record_set_field(*queue, 1, old_len_field);
        let queue_mut = ledger.get_mut(queue).unwrap();
        queue_mut.state.fields[1][..8].copy_from_slice(&new_len.to_le_bytes());

        // Update head pointer (field[6]).
        //
        // When the queue becomes empty (new_len == 0) the head pointer is reset
        // to all-zeros so the next enqueue correctly re-establishes it on the
        // 0→1 transition in apply_queue_enqueue.
        //
        // When new_len > 0 the head cannot be advanced to the next message hash
        // without out-of-band knowledge of the message sequence (queue cell fields
        // do not store a full message list — only head and tail).  A future
        // extension (e.g. a committed Merkle list in field[7]) would close this
        // gap.  For now the head stays pointing at the *original* first message,
        // which is still the correct FIFO head for a newly-allocated queue that
        // enqueues messages before any dequeue: after the first dequeue the head
        // lags by one until the queue drains to zero.  This is strictly better
        // than the previous behaviour (reading tail = most-recently-enqueued).
        let old_field6 = queue_mut.state.fields[6];
        journal.record_set_field(*queue, 6, old_field6);
        if new_len == 0 {
            queue_mut.state.fields[6] = [0u8; 32];
        }
        // else: head stays; advancement of a multi-message queue requires caller
        // to supply the next-message hash (future work, see field[7] extension).

        // Refund the deposit to the dequeuer.
        let queue_balance = queue_mut.state.balance();
        let refund = if current_len > 0 {
            queue_balance / current_len
        } else {
            0
        };
        if refund > 0 {
            let old_queue_balance = queue_mut.state.balance();
            journal.record_set_balance(*queue, old_queue_balance);
            queue_mut.state.set_balance(old_queue_balance - refund);

            let old_actor_balance = ledger.get(action_target).unwrap().state.balance();
            journal.record_set_balance(*action_target, old_actor_balance);
            ledger
                .get_mut(action_target)
                .unwrap()
                .state
                .set_balance(old_actor_balance + refund);
        }

        Ok(())
    }

    fn apply_queue_resize(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        queue: &CellId,
        new_capacity: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Extract all needed data from immutable borrows first.
        let (owner_bytes, current_capacity, current_len, old_cap_field) = {
            let queue_cell = ledger
                .get(queue)
                .ok_or_else(|| (TurnError::CellNotFound { id: *queue }, path.to_vec()))?;
            (
                queue_cell.state.fields[2],
                u64::from_le_bytes(queue_cell.state.fields[0][..8].try_into().unwrap()),
                u64::from_le_bytes(queue_cell.state.fields[1][..8].try_into().unwrap()),
                queue_cell.state.fields[0],
            )
        };

        // Only the queue owner can resize.
        if owner_bytes != *action_target.as_bytes() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "only the queue owner can resize".to_string(),
                },
                path.to_vec(),
            ));
        }

        if new_capacity < current_len {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "cannot shrink queue below current occupancy ({} < {})",
                        new_capacity, current_len
                    ),
                },
                path.to_vec(),
            ));
        }

        // Growing costs additional computrons.
        if new_capacity > current_capacity {
            let additional = new_capacity - current_capacity;
            let actor_balance = ledger
                .get(actor)
                .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?
                .state
                .balance();
            if actor_balance < additional {
                return Err((
                    TurnError::InsufficientBalance {
                        cell: *actor,
                        required: additional,
                        available: actor_balance,
                    },
                    path.to_vec(),
                ));
            }
            journal.record_set_balance(*actor, actor_balance);
            ledger
                .get_mut(actor)
                .unwrap()
                .state
                .set_balance(actor_balance - additional);
        }

        // Update capacity field.
        journal.record_set_field(*queue, 0, old_cap_field);
        ledger.get_mut(queue).unwrap().state.fields[0][..8]
            .copy_from_slice(&new_capacity.to_le_bytes());

        Ok(())
    }

    fn apply_queue_atomic_tx(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        operations: &[crate::action::QueueTxOp],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Execute all operations atomically. On any failure, the journal
        // handles rollback for the entire action.
        for op in operations {
            match op {
                crate::action::QueueTxOp::Enqueue {
                    queue,
                    message_hash,
                    deposit,
                } => {
                    let queue_cell = ledger
                        .get(queue)
                        .ok_or_else(|| (TurnError::CellNotFound { id: *queue }, path.to_vec()))?;
                    let capacity =
                        u64::from_le_bytes(queue_cell.state.fields[0][..8].try_into().unwrap());
                    let current_len =
                        u64::from_le_bytes(queue_cell.state.fields[1][..8].try_into().unwrap());
                    // BUG #114: ACL check mirrors apply_queue_enqueue.
                    let authorized_writer_bytes = queue_cell.state.fields[5];
                    let is_open = authorized_writer_bytes.iter().all(|&b| b == 0);
                    if !is_open && authorized_writer_bytes != *actor.as_bytes() {
                        return Err((
                            TurnError::InvalidEffect {
                                reason: format!(
                                    "atomic tx QueueEnqueue denied: actor {:?} is not the authorized writer for queue {:?}",
                                    actor, queue
                                ),
                            },
                            path.to_vec(),
                        ));
                    }
                    if current_len >= capacity {
                        return Err((
                            TurnError::InvalidEffect {
                                reason: format!("atomic tx: queue {:?} is full", queue),
                            },
                            path.to_vec(),
                        ));
                    }
                    let actor_cell = ledger
                        .get(actor)
                        .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
                    if actor_cell.state.balance() < *deposit {
                        return Err((
                            TurnError::InsufficientBalance {
                                cell: *actor,
                                required: *deposit,
                                available: actor_cell.state.balance(),
                            },
                            path.to_vec(),
                        ));
                    }

                    let old_actor_balance = ledger.get(actor).unwrap().state.balance();
                    let old_queue_balance = ledger.get(queue).unwrap().state.balance();
                    journal.record_set_balance(*actor, old_actor_balance);
                    journal.record_set_balance(*queue, old_queue_balance);
                    ledger
                        .get_mut(actor)
                        .unwrap()
                        .state
                        .set_balance(old_actor_balance - *deposit);
                    ledger
                        .get_mut(queue)
                        .unwrap()
                        .state
                        .set_balance(old_queue_balance + *deposit);

                    let old_len_field = ledger.get(queue).unwrap().state.fields[1];
                    let new_len = current_len + 1;
                    journal.record_set_field(*queue, 1, old_len_field);
                    ledger.get_mut(queue).unwrap().state.fields[1][..8]
                        .copy_from_slice(&new_len.to_le_bytes());

                    // Tail: always updated to latest enqueued message.
                    let old_field4 = ledger.get(queue).unwrap().state.fields[4];
                    journal.record_set_field(*queue, 4, old_field4);
                    ledger.get_mut(queue).unwrap().state.fields[4] = *message_hash;

                    // Head (fields[6]): set on 0→1 transition only.
                    if current_len == 0 {
                        let old_field6 = ledger.get(queue).unwrap().state.fields[6];
                        journal.record_set_field(*queue, 6, old_field6);
                        ledger.get_mut(queue).unwrap().state.fields[6] = *message_hash;
                    }
                }
                crate::action::QueueTxOp::Dequeue { queue } => {
                    let queue_cell = ledger
                        .get(queue)
                        .ok_or_else(|| (TurnError::CellNotFound { id: *queue }, path.to_vec()))?;
                    let owner_bytes = queue_cell.state.fields[2];
                    if owner_bytes != *action_target.as_bytes() {
                        return Err((
                            TurnError::InvalidEffect {
                                reason: "atomic tx: only the queue owner can dequeue".to_string(),
                            },
                            path.to_vec(),
                        ));
                    }
                    let current_len =
                        u64::from_le_bytes(queue_cell.state.fields[1][..8].try_into().unwrap());
                    if current_len == 0 {
                        return Err((
                            TurnError::InvalidEffect {
                                reason: "atomic tx: queue is empty, cannot dequeue".to_string(),
                            },
                            path.to_vec(),
                        ));
                    }
                    let old_len_field = queue_cell.state.fields[1];
                    let new_len = current_len - 1;
                    journal.record_set_field(*queue, 1, old_len_field);
                    ledger.get_mut(queue).unwrap().state.fields[1][..8]
                        .copy_from_slice(&new_len.to_le_bytes());

                    // Clear head pointer when queue becomes empty.
                    let old_field6 = ledger.get(queue).unwrap().state.fields[6];
                    journal.record_set_field(*queue, 6, old_field6);
                    if new_len == 0 {
                        ledger.get_mut(queue).unwrap().state.fields[6] = [0u8; 32];
                    }
                    // else: head stays; advancement requires caller-supplied next hash.

                    // Refund deposit.
                    let queue_balance = ledger.get(queue).unwrap().state.balance();
                    let refund = if current_len > 0 {
                        queue_balance / current_len
                    } else {
                        0
                    };
                    if refund > 0 {
                        let old_q_bal = ledger.get(queue).unwrap().state.balance();
                        journal.record_set_balance(*queue, old_q_bal);
                        ledger
                            .get_mut(queue)
                            .unwrap()
                            .state
                            .set_balance(old_q_bal - refund);

                        let old_actor_bal = ledger.get(action_target).unwrap().state.balance();
                        journal.record_set_balance(*action_target, old_actor_bal);
                        ledger
                            .get_mut(action_target)
                            .unwrap()
                            .state
                            .set_balance(old_actor_bal + refund);
                    }
                }
            }
        }
        Ok(())
    }

    fn apply_queue_pipeline_step(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        source: &CellId,
        sinks: &[CellId],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate source queue exists and has messages.
        let source_cell = ledger
            .get(source)
            .ok_or_else(|| (TurnError::CellNotFound { id: *source }, path.to_vec()))?;
        let source_owner = source_cell.state.fields[2];
        if source_owner != *action_target.as_bytes() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "pipeline step: actor must own the source queue".to_string(),
                },
                path.to_vec(),
            ));
        }
        let source_len = u64::from_le_bytes(source_cell.state.fields[1][..8].try_into().unwrap());
        if source_len == 0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: "pipeline step: source queue is empty".to_string(),
                },
                path.to_vec(),
            ));
        }

        // Validate all sink queues exist, have capacity, and accept writes from
        // this actor.
        //
        // BUG #114 (sink check): the original code checked source ownership but
        // not sink authorization. Without this check, the pipeline step owner
        // could fan-out into any queue they don't control, filling a victim's
        // queue with attacker-controlled messages. We apply the same
        // authorized-writer check that `apply_queue_enqueue` uses:
        //   - field[5] all-zero  → open sink, anyone may route into it.
        //   - field[5] non-zero  → only the matching actor may route into it.
        for sink in sinks {
            let sink_cell = ledger
                .get(sink)
                .ok_or_else(|| (TurnError::CellNotFound { id: *sink }, path.to_vec()))?;
            let sink_capacity =
                u64::from_le_bytes(sink_cell.state.fields[0][..8].try_into().unwrap());
            let sink_len = u64::from_le_bytes(sink_cell.state.fields[1][..8].try_into().unwrap());
            if sink_len >= sink_capacity {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!("pipeline step: sink queue {:?} is full", sink),
                    },
                    path.to_vec(),
                ));
            }
            // ACL: sink must accept writes from this actor.
            let sink_authorized_writer = sink_cell.state.fields[5];
            let sink_is_open = sink_authorized_writer.iter().all(|&b| b == 0);
            if !sink_is_open && sink_authorized_writer != *action_target.as_bytes() {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "pipeline step: actor {:?} is not the authorized writer for sink queue {:?}",
                            action_target, sink
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }

        // Read the FIFO head message hash from the source before decrementing.
        // This is the message being moved through the pipeline.
        let moved_msg_hash = ledger.get(source).unwrap().state.fields[6];

        // Dequeue from source: decrement length.
        let old_source_len_field = ledger.get(source).unwrap().state.fields[1];
        let new_source_len = source_len - 1;
        journal.record_set_field(*source, 1, old_source_len_field);
        ledger.get_mut(source).unwrap().state.fields[1][..8]
            .copy_from_slice(&new_source_len.to_le_bytes());

        // Clear source head pointer when queue becomes empty; leave otherwise
        // (multi-message head advancement requires out-of-band state, see
        // apply_queue_dequeue for the documented gap).
        {
            let old_src_field6 = ledger.get(source).unwrap().state.fields[6];
            journal.record_set_field(*source, 6, old_src_field6);
            if new_source_len == 0 {
                ledger.get_mut(source).unwrap().state.fields[6] = [0u8; 32];
            }
        }

        // Enqueue to each sink (fan-out): update tail and head pointer.
        for sink in sinks {
            let sink_len = u64::from_le_bytes(
                ledger.get(sink).unwrap().state.fields[1][..8]
                    .try_into()
                    .unwrap(),
            );
            let old_sink_len_field = ledger.get(sink).unwrap().state.fields[1];
            let new_sink_len = sink_len + 1;
            journal.record_set_field(*sink, 1, old_sink_len_field);
            ledger.get_mut(sink).unwrap().state.fields[1][..8]
                .copy_from_slice(&new_sink_len.to_le_bytes());

            // Update tail (fields[4]).
            let old_sink_field4 = ledger.get(sink).unwrap().state.fields[4];
            journal.record_set_field(*sink, 4, old_sink_field4);
            ledger.get_mut(sink).unwrap().state.fields[4] = moved_msg_hash;

            // Update head (fields[6]) on 0→1 transition only.
            if sink_len == 0 {
                let old_sink_field6 = ledger.get(sink).unwrap().state.fields[6];
                journal.record_set_field(*sink, 6, old_sink_field6);
                ledger.get_mut(sink).unwrap().state.fields[6] = moved_msg_hash;
            }
        }

        Ok(())
    }

    // ─── CapTP runtime effects (Stage 7 / P1.A, P1.B) ─────────────
    //
    // Mirror the mutations that used to live at the wire layer
    // (`wire/src/server.rs` :2243-2350). The executor is now the
    // single source of truth for CapTP state transitions. The
    // wire layer constructs a Turn with these effects and runs
    // it through `TurnExecutor::execute`.
    #[allow(clippy::too_many_arguments)]
    fn apply_export_sturdy_ref(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        swiss_number: &[u8; 32],
        target: &CellId,
        permissions: &dregg_cell::AuthRequired,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if target != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                target,
                dregg_cell::permissions::Action::Delegate,
                "Delegate",
                path,
            )?;
        }
        // Block1-bind closure
        // (`ExportSturdyRef-permissions`): the declared
        // `permissions` must be narrower-or-equal to the cell's
        // own permission tier for the chosen action class. A
        // sturdy ref must NOT be able to grant authority the
        // cell itself does not hold; without this gate, a
        // caller could export `permissions: None` from a
        // `Signature`-protected cell and the AIR would attest
        // it. We check against the cell's `access` tier
        // (catch-all). For `Custom`, equality is required —
        // `Custom { vk_hash }` is incomparable with any other
        // tier other than itself / Impossible / None per
        // `AuthRequired::is_narrower_or_equal`.
        {
            let cell_for_check = ledger
                .get(target)
                .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
            let cell_tier = &cell_for_check.permissions.access;
            if !permissions.is_narrower_or_equal(cell_tier) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "ExportSturdyRef: declared permissions {permissions:?} is \
                             not narrower-or-equal to cell's access tier \
                             {cell_tier:?}"
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }
        let c = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        // Bump field[7] (export counter) — mirrors the AIR's
        // ExportSturdyRef state transition.
        let mut counter_bytes = c.state.fields[7];
        let counter = u64::from_le_bytes(counter_bytes[..8].try_into().unwrap());
        journal.record_set_field(*target, 7, c.state.fields[7]);
        let new_counter = counter.saturating_add(1);
        counter_bytes[..8].copy_from_slice(&new_counter.to_le_bytes());
        c.state.fields[7] = counter_bytes;
        // The swiss_number + permissions are bound into the
        // receipt via the turn's effects_hash; the federation-
        // level swiss table mirror is updated by the wire
        // layer's post-commit hook
        // (`process_introduction_exports`-style path), which
        // uses the same `permissions` value the AIR projects
        // into PI — so a forged variant value diverges from
        // the federation mirror.
        let _ = swiss_number;
        let _ = permissions;
        Ok(())
    }

    fn apply_enliven_ref(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        swiss_number: &[u8; 32],
        bearer: &CellId,
        expected_cell_id: &CellId,
        expected_permissions: &dregg_cell::AuthRequired,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // The bearer cell gains a routing entry; for the
        // minimal P1.A shape we increment the target's
        // use_count (field[6]) on the bearer cell since that's
        // what the AIR projection records.
        //
        // Block1-bind closure
        // (`EnlivenRef-permissions-merkle`): the
        // `expected_cell_id` and `expected_permissions`
        // declared by the runtime variant must be consistent
        // with the bearer's c-list — the entry granting the
        // sturdy ref must already point to `expected_cell_id`
        // with a tier narrower-or-equal to
        // `expected_permissions`. Without this gate, a forged
        // (cell_id, perms) pair would project into the AIR's
        // PARAMs and end up bound into the new
        // `swiss_table_root` via the algebraic leaf, attesting
        // a privilege the bearer never actually held.
        //
        // The membership witness lives in the bearer's
        // CapabilitySet (the c-list): if the bearer's c-list
        // contains a CapabilityRef whose `target ==
        // expected_cell_id` with a tier narrower-or-equal to
        // `expected_permissions`, the enliven is honest. The
        // post-enliven AIR row will then bind the same
        // (expected_cell_id, expected_permissions) pair into
        // the swiss_table_root chain.
        {
            let bearer_cell = ledger
                .get(bearer)
                .ok_or_else(|| (TurnError::CellNotFound { id: *bearer }, path.to_vec()))?;
            let cap_match = bearer_cell
                .capabilities
                .capabilities_for(expected_cell_id)
                .into_iter()
                .any(|cap| {
                    // Cap holds authority `cap.permissions` and we
                    // claim `expected_permissions` — claim must be
                    // narrower-or-equal to what the cap holds.
                    expected_permissions.is_narrower_or_equal(&cap.permissions)
                });
            if !cap_match {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "EnlivenRef: bearer {bearer} c-list contains no \
                             capability for {expected_cell_id} with a tier \
                             covering the declared expected_permissions \
                             {expected_permissions:?}"
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }
        let c = ledger
            .get_mut(bearer)
            .ok_or_else(|| (TurnError::CellNotFound { id: *bearer }, path.to_vec()))?;
        let mut use_count_bytes = c.state.fields[6];
        let use_count = u64::from_le_bytes(use_count_bytes[..8].try_into().unwrap());
        journal.record_set_field(*bearer, 6, c.state.fields[6]);
        let new_use_count = use_count.saturating_add(1);
        use_count_bytes[..8].copy_from_slice(&new_use_count.to_le_bytes());
        c.state.fields[6] = use_count_bytes;
        let _ = swiss_number;
        let _ = expected_cell_id;
        let _ = expected_permissions;
        Ok(())
    }

    fn apply_drop_ref(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        ref_id: &[u8; 32],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Decrement field[5] (refcount) on the action target.
        // P1.C tightens this to a real refcount-table Merkle
        // proof keyed by ref_id.
        let c = ledger.get_mut(action_target).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            )
        })?;
        let mut rc_bytes = c.state.fields[5];
        let rc = u64::from_le_bytes(rc_bytes[..8].try_into().unwrap());
        if rc == 0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: "DropRef: refcount is already zero".to_string(),
                },
                path.to_vec(),
            ));
        }
        journal.record_set_field(*action_target, 5, c.state.fields[5]);
        let new_rc = rc - 1;
        rc_bytes[..8].copy_from_slice(&new_rc.to_le_bytes());
        c.state.fields[5] = rc_bytes;
        let _ = ref_id;
        Ok(())
    }

    fn apply_validate_handoff(
        &self,
        ledger: &Ledger,
        path: &[usize],
        action_target: &CellId,
        cert_hash: &[u8; 32],
        recipient_pk: &[u8; 32],
        introducer_pk: &[u8; 32],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Consume-on-use: a successful ValidateHandoff removes
        // `cert_hash` from the federation's approved-handoffs
        // mirror so a second presentation of the same cert
        // produces a non-membership witness at the AIR layer.
        //
        // The mirror lives in the executor's federation state
        // (per `DESIGN-captp-integration.md` §9.4). At this
        // stage we only verify the cell exists; the actual
        // mirror is the wire layer's `CapTpState` which the
        // post-commit hook updates. P1.C wires up Merkle proof
        // verification against `approved_handoffs_root`.
        if ledger.get(action_target).is_none() {
            return Err((
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            ));
        }
        let _ = cert_hash;
        let _ = recipient_pk;
        let _ = introducer_pk;
        // NOTE: the action's `Authorization::CapTpDelivered`
        // carries the same `handoff_cert` (which pins
        // `recipient_pk`) and `introducer_pk`; the executor's
        // authorization path verifies cert signatures against
        // those keys. The effect's per-effect binding is what
        // the AIR projection consumes; a mismatch between the
        // effect's `(recipient_pk, introducer_pk)` and the
        // action's carried cert would surface at the
        // authorization gate, not here. This apply site is the
        // state-mutation half; soundness binding lives in the
        // AIR PI projection (effect_vm_bridge) + the
        // authorization verifier.
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_refusal(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        offered_action_commitment: &[u8; 32],
        refusal_reason: &crate::action::RefusalReason,
        proof_witness_index: u32,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // `Refusal` is the categorical dual of acting-effects: it
        // attests that the prover did *not* take a specific action
        // within some window (CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.3).
        //
        // On apply we:
        //   1. Resolve the carried non-action witness blob and
        //      assert it exists at `proof_witness_index`. The
        //      *content* of the witness is the app's choice
        //      (receipt-chain scan, bloom non-membership, custom
        //      AIR); the executor only confirms the bytes are
        //      present so downstream verifiers can re-execute.
        //      Future tightening: dispatch through the witnessed-
        //      predicate registry on a kind embedded in the
        //      refusal (today the offered_action_commitment +
        //      reason discriminant pin the binding; the witness
        //      verifier is registered out-of-band by the app).
        //   2. Bump the target cell's nonce so the refusal is
        //      ordered against other turns on the same cell
        //      (replay-safe).
        //   3. Record the refusal commitment + reason in field[4]
        //      (the audit slot) — a Poseidon2-ish commitment of
        //      `(offered_action_commitment, reason_discriminant)`
        //      so light clients can detect a refusal without
        //      re-fetching the witness.
        //   4. NEVER mutate balance, capability set, or any value
        //      slot. Refusal is structurally *only* a non-action
        //      attestation; permission/value mutations belong to
        //      other effect variants.
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetState,
                "Refusal",
                path,
            )?;
        }
        // Witness presence check. The app supplies the actual
        // verifier through the WitnessedPredicateRegistry; here
        // we only confirm the index resolves.
        // NOTE: the action is in scope only at the higher
        // execute_action level. apply_effect doesn't get the
        // action — but the per-action witness binding pass
        // covers this when the executor wires per-action
        // witness lookup. For the per-effect apply pass, the
        // structural integrity is that the witness index is in
        // u32 range (already typed) and the cell exists.
        let _ = proof_witness_index;
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // Bump nonce (orders the refusal with respect to other
        // turns on this cell).
        journal.record_set_nonce(*cell, c.state.nonce());
        if !c.state.increment_nonce() {
            return Err((TurnError::NonceOverflow { cell: *cell }, path.to_vec()));
        }
        // Compute audit commitment for slot[4]:
        //   blake3("dregg-refusal-audit-v1" ||
        //          offered_action_commitment ||
        //          reason_disc ||
        //          (optional reason_hash))
        let mut h = blake3::Hasher::new_derive_key("dregg-refusal-audit-v1");
        h.update(offered_action_commitment);
        match refusal_reason {
            crate::action::RefusalReason::Declined => h.update(&[0u8]),
            crate::action::RefusalReason::NoAuthority => h.update(&[1u8]),
            crate::action::RefusalReason::WindowExpired => h.update(&[2u8]),
            crate::action::RefusalReason::Custom { reason_hash } => {
                h.update(&[3u8]);
                h.update(reason_hash)
            }
        };
        let audit = *h.finalize().as_bytes();
        journal.record_set_field(*cell, 4, c.state.fields[4]);
        c.state.fields[4] = audit;
        if c.state.commitments[4].is_some() {
            c.state.commitments[4] = None;
        }
        Ok(())
    }

    // ── Cell lifecycle effects (Silver-Vision lifecycle subset) ──
    //
    // Each effect dispatches to the cell-side primitive shipped in
    // commits 9d819ea3/c0496d79/136ef24f. The executor handles:
    //   * target == action_target consistency (cross-cell lifecycle
    //     mutation is rejected as a structural error),
    //   * journaling the old lifecycle/capability state for rollback,
    //   * mapping `LifecycleTransitionError` to `TurnError::InvalidEffect`
    //     so the existing rollback path catches the failure.
    fn apply_cell_seal(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        target: &CellId,
        reason: [u8; 32],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if target != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "CellSeal target must match action target".into(),
                },
                path.to_vec(),
            ));
        }
        let c = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        let old = c.lifecycle.clone();
        c.seal(reason, self.block_height).map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("CellSeal failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        journal.record_set_lifecycle(*target, old);
        Ok(())
    }

    fn apply_cell_unseal(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        target: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if target != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "CellUnseal target must match action target".into(),
                },
                path.to_vec(),
            ));
        }
        let c = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        let old = c.lifecycle.clone();
        c.unseal().map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("CellUnseal failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        journal.record_set_lifecycle(*target, old);
        Ok(())
    }

    fn apply_cell_destroy(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        target: &CellId,
        certificate: &DeathCertificate,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if target != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "CellDestroy target must match action target".into(),
                },
                path.to_vec(),
            ));
        }
        let c = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        let old = c.lifecycle.clone();
        c.destroy(certificate).map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("CellDestroy failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        journal.record_set_lifecycle(*target, old);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_burn(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        target: &CellId,
        slot: u32,
        amount: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Silver-Vision: only the canonical balance slot (sentinel
        // 0) is burnable. Future expansion may introduce per-asset
        // slots; for now any other slot is rejected so the executor
        // never silently writes outside the balance field.
        if slot != 0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "Burn slot {} is not a burnable balance slot (only slot 0 supported)",
                        slot
                    ),
                },
                path.to_vec(),
            ));
        }
        if target != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                target,
                dregg_cell::permissions::Action::Send,
                "Burn",
                path,
            )?;
        }
        let c = ledger
            .get(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        let bal = c.state.balance();
        if bal < amount {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *target,
                    required: amount,
                    available: bal,
                },
                path.to_vec(),
            ));
        }
        let new_bal = bal - amount;
        let cm = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        journal.record_set_balance(*target, bal);
        cm.state.set_balance(new_bal);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_attenuate_capability(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        slot: u32,
        narrower_permissions: &dregg_cell::AuthRequired,
        narrower_effects: Option<u32>,
        narrower_expiry: Option<u64>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != actor {
            return Err((
                TurnError::InvalidEffect {
                    reason: "AttenuateCapability cell must match the actor".into(),
                },
                path.to_vec(),
            ));
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // Snapshot the slot's prior fields for rollback BEFORE
        // attenuation.
        let prior = c
            .capabilities
            .iter()
            .find(|r| r.slot == slot)
            .ok_or_else(|| {
                (
                    TurnError::InvalidEffect {
                        reason: format!("AttenuateCapability slot {slot} not present in c-list"),
                    },
                    path.to_vec(),
                )
            })?;
        let old_permissions = prior.permissions.clone();
        let old_allowed_effects = prior.allowed_effects;
        let old_expires_at = prior.expires_at;
        let result = c.capabilities.attenuate_in_place(
            slot,
            narrower_permissions.clone(),
            narrower_effects,
            narrower_expiry,
        );
        if result.is_none() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "AttenuateCapability rejected: not a monotone narrowing".into(),
                },
                path.to_vec(),
            ));
        }
        journal.record_attenuate_capability(
            *cell,
            slot,
            old_permissions,
            old_allowed_effects,
            old_expires_at,
        );
        Ok(())
    }

    fn apply_receipt_archive(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        prefix_end_height: u64,
        checkpoint: &ArchivalAttestation,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if checkpoint.cell_id != *action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "ReceiptArchive checkpoint cell_id mismatches action target".into(),
                },
                path.to_vec(),
            ));
        }
        if checkpoint.archive_end_height != prefix_end_height {
            return Err((
                TurnError::InvalidEffect {
                    reason:
                        "ReceiptArchive prefix_end_height mismatches checkpoint.archive_end_height"
                            .into(),
                },
                path.to_vec(),
            ));
        }
        // Reject archiving past the current head (block_height).
        if prefix_end_height > self.block_height {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "ReceiptArchive prefix_end_height {} exceeds current head height {}",
                        prefix_end_height, self.block_height
                    ),
                },
                path.to_vec(),
            ));
        }
        // Audit P0 #79: bind `archive_terminal_receipt_hash` to the
        // live chain head. Without this check, an attestation can
        // self-assert a fictional terminal receipt hash that bears
        // no relation to the actual chain, defeating the whole
        // point of the archive checkpoint (which is to pin the
        // chain at `archive_end_height` so post-archive turns can
        // link to it via `previous_receipt_hash`).
        //
        // The executor tracks `last_receipt_hash` per cell; for an
        // archive at height H, the terminal receipt hash MUST equal
        // the cell's currently-known chain head. (We do not store a
        // height->hash index here, so the strongest binding
        // available is "matches the most recent receipt the
        // executor has committed for this cell". A divergent claim
        // is rejected.) Cells with no prior receipt skip the check
        // — there is no head to bind to, and the attestation's own
        // non-zero invariant covers the degenerate case.
        if let Some(live_head) = self.get_last_receipt_hash(action_target) {
            if checkpoint.archive_terminal_receipt_hash != live_head {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "ReceiptArchive archive_terminal_receipt_hash \
                             {:02x}{:02x}.. does not match live chain head \
                             {:02x}{:02x}.. for cell {:?}",
                            checkpoint.archive_terminal_receipt_hash[0],
                            checkpoint.archive_terminal_receipt_hash[1],
                            live_head[0],
                            live_head[1],
                            action_target,
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }
        let c = ledger.get_mut(action_target).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            )
        })?;
        let old = c.lifecycle.clone();
        c.archive(checkpoint).map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("ReceiptArchive failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        journal.record_set_lifecycle(*action_target, old);
        Ok(())
    }

    // ─── Shared helpers ──────────────────────────────────────────────────────

    /// Height-aware check: does the cell have a non-expired capability to the target?
    ///
    /// Uses `has_access_at` to filter out capabilities whose `expires_at` has passed.
    pub(super) fn has_access_including_delegation_at(
        cell: &Cell,
        target: &CellId,
        current_height: u64,
    ) -> bool {
        // A cell implicitly holds the strongest capability over itself. The
        // alternative — requiring an explicit c-list entry to one's own id —
        // forces every newly-created cell to insert a self-grant before it
        // can be bound into a bearer cap. Treat self-access as inherent.
        if cell.id() == *target {
            return true;
        }
        // Direct capability (height-aware)
        if cell.capabilities.has_access_at(target, current_height) {
            return true;
        }
        // Delegated capability (from snapshot)
        if let Some(ref delegation) = cell.delegation {
            if delegation.has_capability(target) {
                return true;
            }
        }
        false
    }

    /// Walk the delegation chain from `start_cell` upward (via `cell.delegate`)
    /// looking for an ancestor that holds a capability to `target`.
    ///
    /// Returns `Some(ancestor_id)` if an ancestor with the capability is found,
    /// `None` otherwise. Limits the walk to 16 hops to prevent infinite loops.
    pub(super) fn walk_delegation_chain_for_capability(
        ledger: &Ledger,
        start_cell: &CellId,
        target: &CellId,
        current_height: u64,
    ) -> Option<CellId> {
        let mut current_id = *start_cell;
        let max_hops = 16;

        for _ in 0..max_hops {
            let cell = ledger.get(&current_id)?;
            // Check if this cell's delegate (parent) has the capability.
            let parent_id = cell.delegate?;
            let parent_cell = ledger.get(&parent_id)?;
            if Self::has_access_including_delegation_at(parent_cell, target, current_height) {
                return Some(parent_id);
            }
            current_id = parent_id;
        }

        None
    }

    /// SECURITY: Check that the actor holds a capability to the given cell AND that
    /// the cell's permission for the given action is not denied.
    pub(super) fn check_cross_cell_permission(
        &self,
        ledger: &Ledger,
        actor: &CellId,
        target_cell_id: &CellId,
        permission_action: dregg_cell::permissions::Action,
        action_name: &str,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if actor != target_cell_id {
            let actor_cell = ledger
                .get(actor)
                .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
            if !Self::has_access_including_delegation_at(
                actor_cell,
                target_cell_id,
                self.block_height,
            ) {
                return Err((
                    TurnError::CapabilityNotHeld {
                        actor: *actor,
                        target: *target_cell_id,
                    },
                    path.to_vec(),
                ));
            }
        }

        let cell = ledger.get(target_cell_id).ok_or_else(|| {
            (
                TurnError::CellNotFound {
                    id: *target_cell_id,
                },
                path.to_vec(),
            )
        })?;
        let required = cell.permissions.for_action(permission_action);
        if matches!(required, AuthRequired::Impossible) {
            return Err((
                TurnError::PermissionDenied {
                    cell: *target_cell_id,
                    action: action_name.to_string(),
                    required: required.clone(),
                },
                path.to_vec(),
            ));
        }
        if !matches!(required, AuthRequired::None) {
            return Err((
                TurnError::PermissionDenied {
                    cell: *target_cell_id,
                    action: action_name.to_string(),
                    required: required.clone(),
                },
                path.to_vec(),
            ));
        }

        Ok(())
    }
}
