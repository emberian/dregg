//! Call-forest tree walker: `execute_tree`, precondition checks, witnessed-clause dispatch.
//!
//! Extracted from `executor/mod.rs` (lines 3813-4627 of pre-decomposition file).

use super::*;

impl TurnExecutor {
    pub(crate) fn epoch_for_height(block_height: u64, epoch_duration: u64) -> u64 {
        block_height / epoch_duration.max(1)
    }

    fn state_constraint_context_count(
        &self,
        cell_id: &CellId,
        program: &dregg_cell::CellProgram,
        sender: Option<[u8; 32]>,
    ) -> u32 {
        let constraints = match program {
            dregg_cell::CellProgram::Predicate(constraints) => constraints,
            _ => return 0,
        };

        if let Some((max_per_epoch, epoch_duration)) = constraints.iter().find_map(|c| match c {
            dregg_cell::StateConstraint::RateLimit {
                max_per_epoch,
                epoch_duration,
            } => Some((*max_per_epoch, *epoch_duration)),
            _ => None,
        }) {
            let Some(sender) = sender else {
                return 0;
            };
            let epoch = Self::epoch_for_height(self.block_height, epoch_duration);
            return self
                .rate_limit_counters
                .lock()
                .unwrap()
                .get(&(*cell_id, sender, epoch))
                .copied()
                .unwrap_or(0)
                .min(max_per_epoch);
        }

        if let Some((slot_index, epoch_duration)) = constraints.iter().find_map(|c| match c {
            dregg_cell::StateConstraint::RateLimitBySum {
                slot_index,
                epoch_duration,
                ..
            } => Some((*slot_index, *epoch_duration)),
            _ => None,
        }) {
            let epoch = Self::epoch_for_height(self.block_height, epoch_duration);
            return self
                .rate_limit_sum_counters
                .lock()
                .unwrap()
                .get(&(*cell_id, slot_index, epoch))
                .copied()
                .unwrap_or(0)
                .min(u32::MAX as u64) as u32;
        }

        0
    }

    fn evaluate_cell_program_for_executor(
        program: &dregg_cell::CellProgram,
        new_state: &dregg_cell::CellState,
        old_state: Option<&dregg_cell::CellState>,
        ctx: &dregg_cell::EvalContext,
        meta: &dregg_cell::program::TransitionMeta,
        witnesses: &dregg_cell::program::WitnessBundle<'_>,
    ) -> Result<(), dregg_cell::ProgramError> {
        match program {
            dregg_cell::CellProgram::Predicate(constraints) => {
                for constraint in constraints {
                    if matches!(constraint, dregg_cell::StateConstraint::BoundDelta { .. }) {
                        continue;
                    }
                    dregg_cell::CellProgram::Predicate(vec![constraint.clone()]).evaluate_full(
                        new_state,
                        old_state,
                        Some(ctx),
                        meta,
                        witnesses,
                    )?;
                }
                Ok(())
            }
            _ => program.evaluate_full(new_state, old_state, Some(ctx), meta, witnesses),
        }
    }

    fn validate_bound_delta_program(
        &self,
        cell_id: &CellId,
        program: &dregg_cell::CellProgram,
        old_cell_states: &std::collections::HashMap<CellId, dregg_cell::CellState>,
        ledger: &Ledger,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let constraints = match program {
            dregg_cell::CellProgram::Predicate(constraints) => constraints,
            _ => return Ok(()),
        };
        for constraint in constraints {
            let dregg_cell::StateConstraint::BoundDelta {
                local_slot,
                peer_cell,
                peer_slot,
                delta_relation,
            } = constraint
            else {
                continue;
            };
            let Some(local_old) = old_cell_states.get(cell_id) else {
                return Err((
                    TurnError::ProgramViolation {
                        cell: *cell_id,
                        reason: "BoundDelta requires local old state".into(),
                    },
                    path.to_vec(),
                ));
            };
            let Some(local_new) = ledger.get(cell_id).map(|c| &c.state) else {
                return Err((TurnError::CellNotFound { id: *cell_id }, path.to_vec()));
            };
            let Some(peer_old) = old_cell_states.get(peer_cell) else {
                return Err((
                    TurnError::ProgramViolation {
                        cell: *cell_id,
                        reason: format!(
                            "BoundDelta peer {peer_cell} was not touched by this action"
                        ),
                    },
                    path.to_vec(),
                ));
            };
            let Some(peer_new) = ledger.get(peer_cell).map(|c| &c.state) else {
                return Err((TurnError::CellNotFound { id: *peer_cell }, path.to_vec()));
            };
            let matches = dregg_cell::program::bound_delta_pair_matches(
                local_old,
                local_new,
                *local_slot,
                peer_old,
                peer_new,
                *peer_slot,
                *delta_relation,
            )
            .map_err(|e| {
                (
                    TurnError::ProgramViolation {
                        cell: *cell_id,
                        reason: e.to_string(),
                    },
                    path.to_vec(),
                )
            })?;
            if !matches {
                return Err((
                    TurnError::ProgramViolation {
                        cell: *cell_id,
                        reason: format!(
                            "BoundDelta mismatch: local slot {local_slot} did not satisfy {delta_relation:?} against peer {peer_cell} slot {peer_slot}"
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }
        Ok(())
    }

    /// Execute a single tree node and its children recursively.
    ///
    /// Returns Ok(()) on success or Err((TurnError, path)) on failure.
    pub(super) fn execute_tree(
        &self,
        tree: &CallTree,
        ledger: &mut Ledger,
        parent_cell: &CellId,
        parent_delegation: DelegationMode,
        computrons_used: &mut u64,
        budget: u64,
        effects_hashes: &mut Vec<[u8; 32]>,
        path: Vec<usize>,
        journal: &mut LedgerJournal,
        excess: &mut i64,
        turn_nonce: u64,
        turn_agent: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let action = &tree.action;

        // Meter the action base cost.
        *computrons_used = computrons_used.saturating_add(self.costs.action_base);
        if *computrons_used > budget {
            return Err((
                TurnError::BudgetExceeded {
                    limit: budget,
                    used: *computrons_used,
                },
                path,
            ));
        }

        // Check target cell exists.
        // For sovereign cells without an injected witness, the cell is absent
        // from the hosted ledger table because Phase 1 only injects witnessed
        // sovereign cells (see `SOVEREIGN CELL WITNESS INJECTION` above). A
        // sovereign target with no witness must surface as the dedicated
        // `SovereignWitnessRequired` so callers can distinguish "you forgot
        // the witness" from "this cell does not exist." Otherwise, a future
        // refactor that hydrates cells lazily could silently regress this to
        // an acceptance path.
        if ledger.get(&action.target).is_none() {
            if ledger.is_sovereign(&action.target) {
                return Err((
                    TurnError::SovereignWitnessRequired {
                        cell: action.target,
                    },
                    path.clone(),
                ));
            }
            return Err((TurnError::CellNotFound { id: action.target }, path.clone()));
        }

        // Check capability: does the parent have access to the target?
        // The agent (top-level parent) implicitly has access to itself.
        // For other cells, the parent must hold a capability.
        // Bearer authorization bypasses this check: bearer caps carry their own
        // delegation proof that validates authority without requiring a c-list entry.
        let is_bearer_auth = matches!(&action.authorization, Authorization::Bearer(_));
        if &action.target != parent_cell && !is_bearer_auth {
            let parent = ledger
                .get(parent_cell)
                .ok_or_else(|| (TurnError::CellNotFound { id: *parent_cell }, path.clone()))?;

            let has_capability =
                Self::has_access_including_delegation_at(parent, &action.target, self.block_height);

            // Check delegation mode: if parent_delegation is None, child actions cannot
            // use the parent's capabilities to reach non-parent cells.
            if !has_capability {
                // TODO: DelegationMode::ParentsOwn and Inherit are not yet implemented.
                // Currently all modes fall through to direct capability check.
                // Use Effect::Introduce for explicit capability transfer between cells.
                match parent_delegation {
                    DelegationMode::None => {
                        return Err((
                            TurnError::CapabilityNotHeld {
                                actor: *parent_cell,
                                target: action.target,
                            },
                            path,
                        ));
                    }
                    DelegationMode::ParentsOwn | DelegationMode::Inherit => {
                        // ParentsOwn and Inherit are deprecated; behave like None.
                        return Err((
                            TurnError::CapabilityNotHeld {
                                actor: *parent_cell,
                                target: action.target,
                            },
                            path,
                        ));
                    }
                    DelegationMode::SnapshotRefresh => {
                        // Walk the delegation chain from parent_cell upward to find
                        // an ancestor that holds the capability to action.target.
                        // If found, create a DelegatedRef snapshot on the child cell,
                        // giving it a frozen view of the ancestor's capabilities.
                        let found_ancestor = Self::walk_delegation_chain_for_capability(
                            ledger,
                            parent_cell,
                            &action.target,
                            self.block_height,
                        );
                        if let Some(ancestor_id) = found_ancestor {
                            let ancestor = ledger.get(&ancestor_id).unwrap();
                            let snapshot: Vec<dregg_cell::CapabilityRef> =
                                ancestor.capabilities.iter().cloned().collect();
                            let delegation_epoch = ancestor.state.delegation_epoch();
                            let now = self.current_timestamp as u64;
                            let max_staleness = self.max_introduction_lifetime;

                            // Set up a DelegatedRef on the acting child cell so it can
                            // use the ancestor's capabilities for this and future actions.
                            let child_cell = ledger.get_mut(parent_cell).unwrap();
                            if child_cell.delegation.is_none() {
                                journal.record_set_delegation(*parent_cell, None);
                                let clist_bytes =
                                    postcard::to_allocvec(&snapshot).unwrap_or_default();
                                let clist_commitment =
                                    dregg_cell::DelegatedRef::compute_clist_commitment(
                                        &clist_bytes,
                                    );
                                child_cell.delegation = Some(dregg_cell::DelegatedRef::new(
                                    ancestor_id,
                                    *parent_cell,
                                    snapshot,
                                    delegation_epoch,
                                    now,
                                    max_staleness,
                                    clist_commitment,
                                    [0u8; 64], // Executor-internal delegation, signature verified by execution authority.
                                ));
                            }
                            // Re-check access now that the delegation snapshot is set.
                            let child_cell_ref = ledger.get(parent_cell).unwrap();
                            if !Self::has_access_including_delegation_at(
                                child_cell_ref,
                                &action.target,
                                self.block_height,
                            ) {
                                return Err((
                                    TurnError::CapabilityNotHeld {
                                        actor: *parent_cell,
                                        target: action.target,
                                    },
                                    path,
                                ));
                            }
                        } else {
                            return Err((
                                TurnError::CapabilityNotHeld {
                                    actor: *parent_cell,
                                    target: action.target,
                                },
                                path,
                            ));
                        }
                    }
                }
            }
        }

        // Re-fetch target_cell after potential delegation mutations above.
        let target_cell = ledger
            .get(&action.target)
            .ok_or_else(|| (TurnError::CellNotFound { id: action.target }, path.clone()))?;

        // Check preconditions (including witnessed clauses — Block 3.5).
        self.check_preconditions(action, target_cell, &path)?;

        // Verify authorization (including signature/proof verification).
        self.verify_authorization(action, target_cell, ledger, parent_cell, &path, turn_nonce)?;

        // Refusal-vs-mutation structural conflict guard.
        // `Effect::Refusal { cell, .. }` is the categorical
        // "evidence of non-action" (CROSS-CELL-CATEGORICAL-ANALYSIS.md
        // §3.3). It must NOT co-occur with any state-mutating effect
        // on the same cell within the same action — that collapses the
        // attest-non-action semantics into an ambiguous "did the prover
        // act or refuse?" Reject closed; downstream verifiers do not
        // have to silently pick an ordering.
        for (ref_idx, ref_eff) in action.effects.iter().enumerate() {
            if let Effect::Refusal { cell: ref_cell, .. } = ref_eff {
                for (other_idx, other) in action.effects.iter().enumerate() {
                    if ref_idx == other_idx {
                        continue;
                    }
                    let (conflicts, name): (bool, &'static str) = match other {
                        Effect::SetField { cell, .. } => (cell == ref_cell, "SetField"),
                        Effect::SetPermissions { cell, .. } => (cell == ref_cell, "SetPermissions"),
                        Effect::SetVerificationKey { cell, .. } => {
                            (cell == ref_cell, "SetVerificationKey")
                        }
                        Effect::Transfer { from, to, .. } => {
                            (from == ref_cell || to == ref_cell, "Transfer")
                        }
                        Effect::GrantCapability { from, to, .. } => {
                            (from == ref_cell || to == ref_cell, "GrantCapability")
                        }
                        Effect::RevokeCapability { cell, .. } => {
                            (cell == ref_cell, "RevokeCapability")
                        }
                        Effect::IncrementNonce { cell } => (cell == ref_cell, "IncrementNonce"),
                        // A second Refusal on the same cell is itself a
                        // structural conflict (two non-action attestations
                        // collapse into ambiguity about which is binding).
                        Effect::Refusal { cell, .. } => (cell == ref_cell, "Refusal"),
                        _ => (false, ""),
                    };
                    if conflicts {
                        return Err((
                            TurnError::RefusalConflictsWithMutation {
                                cell: *ref_cell,
                                conflicting_effect: name.to_string(),
                            },
                            path,
                        ));
                    }
                }
            }
        }

        // Meter authorization cost.
        let auth_cost = match &action.authorization {
            Authorization::Signature(_, _) => self.costs.signature_verify,
            Authorization::Proof { .. } => self.costs.proof_verify,
            Authorization::Breadstuff(_) => self.costs.signature_verify / 2, // cheaper
            Authorization::Bearer(_) => self.costs.signature_verify, // sig verification + delegation check
            Authorization::Unchecked => 0,
            // CapTpDelivered verifies introducer signature + sender signature: two ed25519 verifies.
            Authorization::CapTpDelivered { .. } => self.costs.signature_verify.saturating_mul(2),
            // Authorization::Custom: a witnessed-predicate dispatch
            // through the registry; meter as a proof verify.
            Authorization::Custom { .. } => self.costs.proof_verify,
            // OneOf: the cost is the cost of the chosen candidate.
            // We pessimistically charge the maximum candidate's cost so
            // a malicious chooser can't sneak a cheaper-than-actual
            // candidate through metering. The verifier still validates
            // only the indexed candidate.
            Authorization::OneOf { candidates, .. } => {
                fn cand_cost(costs: &ComputronCosts, a: &Authorization) -> u64 {
                    match a {
                        Authorization::Signature(_, _) => costs.signature_verify,
                        Authorization::Proof { .. } => costs.proof_verify,
                        Authorization::Breadstuff(_) => costs.signature_verify / 2,
                        Authorization::Bearer(_) => costs.signature_verify,
                        Authorization::Unchecked => 0,
                        Authorization::CapTpDelivered { .. } => {
                            costs.signature_verify.saturating_mul(2)
                        }
                        Authorization::Custom { .. } => costs.proof_verify,
                        Authorization::OneOf { candidates, .. } => candidates
                            .iter()
                            .map(|c| cand_cost(costs, c))
                            .max()
                            .unwrap_or(0),
                    }
                }
                candidates
                    .iter()
                    .map(|c| cand_cost(&self.costs, c))
                    .max()
                    .unwrap_or(0)
            }
        };
        *computrons_used = computrons_used.saturating_add(auth_cost);
        if *computrons_used > budget {
            return Err((
                TurnError::BudgetExceeded {
                    limit: budget,
                    used: *computrons_used,
                },
                path,
            ));
        }

        // Cav-Codex Block 1: snapshot the pre-effects state of EVERY cell
        // the action might touch (target cell + any cell named in an
        // effect or in an `ExerciseViaCapability`'s inner effects).
        // The cell-program evaluator at the bottom of this function
        // walks the touched-set and re-checks each cell's program
        // against its (old, new) pair — closing the "B was mutated
        // from action targeting A, but B's program was never checked"
        // gap codex flagged.
        let mut old_cell_states: std::collections::HashMap<CellId, dregg_cell::CellState> =
            std::collections::HashMap::new();
        for cell_id in Self::collect_touched_cells(action) {
            if let Some(c) = ledger.get(&cell_id) {
                old_cell_states.insert(cell_id, c.state.clone());
            }
        }
        // Always include the target cell (even if its state is None
        // pre-effects — i.e. the action creates it).
        if !old_cell_states.contains_key(&action.target) {
            if let Some(c) = ledger.get(&action.target) {
                old_cell_states.insert(action.target, c.state.clone());
            }
        }
        // Back-compat alias for code below that still references the
        // single old_target_state path.
        let old_target_state = old_cell_states.get(&action.target).cloned();

        // =====================================================================
        // PERMISSION UPDATE ORDERING (Fix 2):
        // Split effects into regular effects and permission-changing effects.
        // Regular effects are applied first, permission effects are applied LAST.
        // All permission checks use the ORIGINAL permissions (already verified above
        // in verify_authorization which ran before any effects were applied).
        // This prevents an action from SetPermissions -> exploit weakened perms.
        // =====================================================================
        let (regular_effects, permission_effects): (Vec<&Effect>, Vec<&Effect>) = action
            .effects
            .iter()
            .partition(|e| !e.is_permission_effect());

        // Apply effects, tracking which cells have fields set (for proved_state).
        let is_proof_auth = matches!(&action.authorization, Authorization::Proof { .. });
        let mut proof_field_sets: std::collections::HashMap<
            CellId,
            std::collections::HashSet<usize>,
        > = std::collections::HashMap::new();
        let mut non_proof_field_cells: std::collections::HashSet<CellId> =
            std::collections::HashSet::new();

        // Apply regular effects first.
        for effect in &regular_effects {
            let effect_cost = self.compute_effect_cost(effect);
            *computrons_used = computrons_used.saturating_add(effect_cost);
            if *computrons_used > budget {
                return Err((
                    TurnError::BudgetExceeded {
                        limit: budget,
                        used: *computrons_used,
                    },
                    path.clone(),
                ));
            }

            // Track SetField effects for proved_state logic.
            if let Effect::SetField { cell, index, .. } = effect {
                if is_proof_auth {
                    proof_field_sets.entry(*cell).or_default().insert(*index);
                } else {
                    non_proof_field_cells.insert(*cell);
                }
            }

            self.apply_effect(effect, ledger, &path, &action.target, parent_cell, journal)?;
            effects_hashes.push(effect.hash());
        }

        // Apply permission-changing effects LAST.
        for effect in &permission_effects {
            let effect_cost = self.compute_effect_cost(effect);
            *computrons_used = computrons_used.saturating_add(effect_cost);
            if *computrons_used > budget {
                return Err((
                    TurnError::BudgetExceeded {
                        limit: budget,
                        used: *computrons_used,
                    },
                    path.clone(),
                ));
            }

            self.apply_effect(effect, ledger, &path, &action.target, parent_cell, journal)?;
            effects_hashes.push(effect.hash());
        }

        // Update proved_state based on authorization type and fields touched.
        if is_proof_auth {
            // If ALL 8 fields were set by this proof-authorized action, proved_state = true.
            for (cell_id, indices) in &proof_field_sets {
                if indices.len() == STATE_SLOTS {
                    if let Some(c) = ledger.get_mut(cell_id) {
                        if !c.state.proved_state() {
                            journal.record_set_proved_state(*cell_id, c.state.proved_state());
                            c.state.set_proved_state(true);
                        }
                    }
                }
            }
        } else {
            // Non-proof authorization: if any field was modified, proved_state = false.
            for cell_id in &non_proof_field_cells {
                if let Some(c) = ledger.get_mut(cell_id) {
                    if c.state.proved_state() {
                        journal.record_set_proved_state(*cell_id, c.state.proved_state());
                        c.state.set_proved_state(false);
                    }
                }
            }
        }

        // Apply balance_change (Mina-style excess tracking).
        if let Some(delta) = action.balance_change {
            let target = ledger
                .get(&action.target)
                .ok_or_else(|| (TurnError::CellNotFound { id: action.target }, path.clone()))?;
            let current_balance = target.state.balance();

            // Check for underflow on withdrawal (negative delta).
            if delta < 0 {
                let abs_delta = delta.unsigned_abs();
                if current_balance < abs_delta {
                    return Err((
                        TurnError::BalanceChangeUnderflow {
                            cell: action.target,
                            current: current_balance,
                            delta,
                        },
                        path.clone(),
                    ));
                }
            } else {
                // Check for overflow on deposit (positive delta).
                let abs_delta = delta as u64;
                if current_balance.checked_add(abs_delta).is_none() {
                    return Err((
                        TurnError::BalanceOverflow {
                            cell: action.target,
                        },
                        path.clone(),
                    ));
                }
            }

            // Record old balance for rollback and apply the delta.
            let cell_mut = ledger.get_mut(&action.target).unwrap();
            journal.record_set_balance(action.target, cell_mut.state.balance());
            if delta < 0 {
                cell_mut
                    .state
                    .set_balance(cell_mut.state.balance() - delta.unsigned_abs());
            } else {
                cell_mut
                    .state
                    .set_balance(cell_mut.state.balance() + delta as u64);
            }

            // Update excess: withdrawal (negative delta) PRODUCES excess (adds to excess),
            // deposit (positive delta) CONSUMES excess (subtracts from excess).
            // excess += -delta
            *excess = excess.checked_sub(delta).ok_or_else(|| {
                (
                    TurnError::BalanceOverflow {
                        cell: action.target,
                    },
                    path.clone(),
                )
            })?;
        }

        // Cav-Codex Block 1+2: enforce cell program constraints on every
        // cell the action touched (not just the target). Multi-cell
        // mutations (Transfer, GrantCapability, SetField on a non-target
        // cell, ExerciseViaCapability inner effects) now re-check each
        // cell's program against its captured (old, new) pair.
        //
        // Cav-Codex Block 2: build a `WitnessBundle` from the action's
        // `witness_blobs` and the executor's
        // `WitnessedPredicateRegistry`, plus a fresh `TransitionMeta`
        // carrying the action's method symbol + effects-kind mask so
        // `CellProgram::Cases` programs can dispatch by op-shape.
        let parent_pk_opt: Option<[u8; 32]> = ledger.get(parent_cell).map(|p| *p.public_key());
        let effects_mask: u32 = action
            .effects
            .iter()
            .fold(0u32, |acc, e| acc | e.effect_kind_mask());
        let meta = dregg_cell::program::TransitionMeta::new(action.method, effects_mask);
        let witness_views: Vec<dregg_cell::program::WitnessBlobView<'_>> = action
            .witness_blobs
            .iter()
            .map(|wb| dregg_cell::program::WitnessBlobView {
                kind: match wb.kind {
                    crate::action::WitnessKind::Preimage32 => {
                        dregg_cell::program::WitnessKindTag::Preimage32
                    }
                    crate::action::WitnessKind::MerklePath => {
                        dregg_cell::program::WitnessKindTag::MerklePath
                    }
                    crate::action::WitnessKind::RateLimitCount => {
                        dregg_cell::program::WitnessKindTag::RateLimitCount
                    }
                    crate::action::WitnessKind::ProofBytes => {
                        dregg_cell::program::WitnessKindTag::ProofBytes
                    }
                    crate::action::WitnessKind::Cleartext => {
                        dregg_cell::program::WitnessKindTag::Cleartext
                    }
                },
                bytes: &wb.bytes,
            })
            .collect();
        let witnesses = dregg_cell::program::WitnessBundle {
            blobs: &witness_views,
            registry: self.witnessed_registry.as_ref(),
        };

        // Walk every cell whose program might fire on this action: the
        // target cell + any cell named in old_cell_states (the snapshot
        // map, which holds every cell touched by an effect).
        let mut to_check: Vec<CellId> = old_cell_states.keys().cloned().collect();
        // Also include any cell newly created during effects (no old
        // state but a fresh new state).
        if !to_check.contains(&action.target) {
            to_check.push(action.target);
        }

        for cell_id in &to_check {
            let Some(touched_cell) = ledger.get(cell_id) else {
                continue;
            };
            if touched_cell.program.is_none() {
                continue;
            }
            if touched_cell.program.requires_proof() {
                // Circuit programs: proof verification handles the
                // transition; skip the predicate evaluator.
                continue;
            }
            let old_state = old_cell_states.get(cell_id);
            // For RateLimit + SenderAuthorized variants, populate
            // ctx.sender_epoch_count from the executor's per-(cell,
            // sender) counter slot. Until a real counter slot lands
            // (deferred), leave at 0 and let the witness blob (a
            // RateLimitCount blob) supply the count.
            let sender_epoch_count =
                self.state_constraint_context_count(cell_id, &touched_cell.program, parent_pk_opt);
            let ctx = dregg_cell::EvalContext {
                block_height: self.block_height,
                timestamp: self.current_timestamp,
                current_epoch: self.block_height.saturating_div(1024),
                sender: parent_pk_opt,
                sender_epoch_count,
                revealed_preimage: None,
            };
            let result = Self::evaluate_cell_program_for_executor(
                &touched_cell.program,
                &touched_cell.state,
                old_state,
                &ctx,
                &meta,
                &witnesses,
            );
            if let Err(e) = result {
                return Err((
                    TurnError::ProgramViolation {
                        cell: *cell_id,
                        reason: e.to_string(),
                    },
                    path,
                ));
            }
            self.validate_bound_delta_program(
                cell_id,
                &touched_cell.program,
                &old_cell_states,
                ledger,
                &path,
            )?;
        }

        // Suppress unused warning on the legacy alias.
        let _ = old_target_state;

        // Per-action target-nonce bump for legacy (CellProgram::None) cells.
        //
        // When a cell has no program, the executor is responsible for
        // monotonically advancing its nonce on each successful action that
        // mutates its state. This mirrors Ethereum-style per-target sequence
        // numbers and is what `test_program_none_backward_compat` asserts.
        // Cells with a non-trivial CellProgram manage their own nonce via
        // explicit `Effect::IncrementNonce` (see `test_increment_nonce_effect`)
        // or via program constraints, so we only auto-bump when:
        //   1. The target is NOT the turn's agent (the agent gets its own
        //      per-turn nonce bump in phase 1 of `execute`; double-bumping
        //      would break the nonce-replay chain used by chained turns),
        //   2. The target cell exists post-effects,
        //   3. Its program is `CellProgram::None`,
        //   4. The action's effects actually changed target state (not a
        //      pure read), AND
        //   5. No explicit `Effect::IncrementNonce { cell: action.target }`
        //      was already applied this action (avoid double-bump).
        let target_is_turn_agent = &action.target == turn_agent;
        let explicit_target_nonce_bump = action
            .effects
            .iter()
            .any(|e| matches!(e, Effect::IncrementNonce { cell } if *cell == action.target));
        // Sovereign cells own their own state commitments and manage their
        // own nonce through proof-carrying or witness-signed transitions;
        // the hosted executor must not silently mutate them.
        let target_is_sovereign =
            ledger.is_sovereign(&action.target) || ledger.is_sovereign_registered(&action.target);
        if !target_is_turn_agent && !target_is_sovereign && !explicit_target_nonce_bump {
            let target_program_is_none = ledger
                .get(&action.target)
                .map(|c| c.program.is_none())
                .unwrap_or(false);
            // Did anything observably change for the target during this action?
            // Use the old_target_state snapshot captured before effects applied.
            let target_changed = match (
                old_cell_states.get(&action.target),
                ledger.get(&action.target),
            ) {
                (Some(old), Some(new)) => old != &new.state,
                // Newly created target — treat as a change.
                (None, Some(_)) => true,
                _ => false,
            };
            if target_program_is_none && target_changed {
                if let Some(c) = ledger.get_mut(&action.target) {
                    journal.record_set_nonce(action.target, c.state.nonce());
                    let _ = c.state.increment_nonce();
                }
            }
        }

        // Recurse into children.
        // NOTE: This resolution determines whether children can target *different* cells.
        // DelegationMode::None prevents cross-cell targeting (enforced below).
        // ParentsOwn and Inherit are deprecated — they behave identically to None.
        // Use Effect::Introduce or SnapshotRefresh for explicit capability delegation.
        let child_delegation = match action.may_delegate {
            DelegationMode::None => DelegationMode::None,
            DelegationMode::ParentsOwn => DelegationMode::None, // deprecated: same as None
            DelegationMode::Inherit => DelegationMode::None,    // deprecated: same as None
            DelegationMode::SnapshotRefresh => DelegationMode::SnapshotRefresh,
        };

        for (child_idx, child) in tree.children.iter().enumerate() {
            // Check delegation permission: None means children must target same cell as parent.
            if child_delegation == DelegationMode::None && child.action.target != action.target {
                return Err((
                    TurnError::DelegationDenied {
                        parent: action.target,
                        child_target: child.action.target,
                    },
                    {
                        let mut p = path.clone();
                        p.push(child_idx);
                        p
                    },
                ));
            }

            let mut child_path = path.clone();
            child_path.push(child_idx);

            self.execute_tree(
                child,
                ledger,
                &action.target, // current action's target becomes the parent for children
                child_delegation,
                computrons_used,
                budget,
                effects_hashes,
                child_path,
                journal,
                excess,
                turn_nonce,
                turn_agent,
            )?;
        }

        Ok(())
    }

    /// Check preconditions against the target cell's state.
    /// TRUST-CRITICAL: This function enforces temporal and state-based guards on actions.
    /// If compromised: expired turns could execute, balance thresholds could be bypassed,
    /// and block-height-locked actions could fire prematurely.
    /// Future: precondition evaluation will be proven inside the Effect VM circuit,
    /// allowing verifiers to confirm guards were checked without trusting the executor.
    pub(crate) fn check_preconditions(
        &self,
        action: &Action,
        target_cell: &Cell,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let preconditions = &action.preconditions;
        let sender_pk = match &action.authorization {
            Authorization::Signature(pk, _) => Some(*pk),
            Authorization::Bearer(bp) => match &bp.delegation_proof {
                crate::action::DelegationProofData::SignedDelegation { delegator_pk, .. } => {
                    Some(*delegator_pk)
                }
                _ => None,
            },
            Authorization::CapTpDelivered { sender_pk, .. } => Some(*sender_pk),
            _ => None,
        };
        let ctx = EvalContext {
            block_height: self.block_height,
            timestamp: self.current_timestamp,
            sender: sender_pk,
            ..Default::default()
        };

        preconditions
            .evaluate(&target_cell.state, &ctx)
            .map_err(|e| {
                (
                    TurnError::PreconditionFailed {
                        description: format!("{e:?}"),
                    },
                    path.to_vec(),
                )
            })?;

        // Cav-Codex Block 3.5: dispatch each `Preconditions::witnessed`
        // clause through the witnessed-predicate registry. Each clause
        // names a `WitnessedPredicateKind`, a commitment, an InputRef,
        // and a proof_witness_index naming the action's witness_blob.
        // Until this site existed, `Preconditions::witnessed` clauses
        // were dead code (CAVEAT-LAYER-COVERAGE.md §6.7).
        if !preconditions.witnessed.is_empty() {
            // Fail-closed gate: if the registry was disabled by an
            // explicit set_witnessed_registry(None)-style host
            // configuration, every witnessed clause rejects rather
            // than silently passing. dispatch_witnessed_clause
            // reproduces this check; the gate here makes the error
            // message specific to "no registry at all" vs "kind not
            // registered".
            if self.witnessed_registry.is_none() {
                return Err((
                    TurnError::PreconditionFailed {
                        description:
                            "witnessed precondition declared but executor has no witnessed_registry"
                                .into(),
                    },
                    path.to_vec(),
                ));
            }
            for wp in &preconditions.witnessed {
                self.dispatch_witnessed_clause(
                    wp,
                    action,
                    &target_cell.state,
                    sender_pk.as_ref(),
                    path,
                )?;
            }
        }
        Ok(())
    }

    /// Resolve a `WitnessedPredicate`'s `InputRef` against the current
    /// action / target-cell context and dispatch through
    /// `self.witnessed_registry`. Used by `Preconditions::witnessed`
    /// (Block 3.5 dispatch site) and (eventually) by
    /// `CapabilityCaveat::Witnessed`.
    ///
    /// On dispatch failure surfaces `TurnError::PreconditionFailed`
    /// with the verifier's diagnostic.
    pub(super) fn dispatch_witnessed_clause(
        &self,
        wp: &dregg_cell::WitnessedPredicate,
        action: &Action,
        target_state: &dregg_cell::CellState,
        sender_pk: Option<&[u8; 32]>,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let registry = match self.witnessed_registry.as_ref() {
            Some(r) => r,
            None => {
                return Err((
                    TurnError::PreconditionFailed {
                        description:
                            "witnessed clause requires executor.witnessed_registry to be set".into(),
                    },
                    path.to_vec(),
                ));
            }
        };
        let proof_blob = action
            .witness_blobs
            .get(wp.proof_witness_index)
            .ok_or_else(|| {
                (
                    TurnError::PreconditionFailed {
                        description: format!(
                            "witnessed clause references missing proof witness_index {}",
                            wp.proof_witness_index
                        ),
                    },
                    path.to_vec(),
                )
            })?;
        // Resolve the input ref.
        let input: PredicateInput<'_> = match &wp.input_ref {
            InputRef::Slot { index } => {
                let idx = *index as usize;
                if idx >= STATE_SLOTS {
                    return Err((
                        TurnError::PreconditionFailed {
                            description: format!(
                                "witnessed clause references out-of-range slot index {idx}"
                            ),
                        },
                        path.to_vec(),
                    ));
                }
                PredicateInput::Slot(&target_state.fields[idx])
            }
            InputRef::Witness { index } => {
                let b = action.witness_blobs.get(*index).ok_or_else(|| {
                    (
                        TurnError::PreconditionFailed {
                            description: format!(
                                "witnessed clause references missing input witness_index {index}"
                            ),
                        },
                        path.to_vec(),
                    )
                })?;
                PredicateInput::Bytes(&b.bytes)
            }
            InputRef::PublicInput { .. } => {
                return Err((
                    TurnError::PreconditionFailed {
                        description:
                            "witnessed clause InputRef::PublicInput is not resolvable at the precondition site"
                                .into(),
                    },
                    path.to_vec(),
                ));
            }
            InputRef::Sender => {
                let pk = sender_pk.ok_or_else(|| {
                    (
                        TurnError::PreconditionFailed {
                            description:
                                "witnessed clause requires a sender pubkey but action carries none"
                                    .into(),
                        },
                        path.to_vec(),
                    )
                })?;
                PredicateInput::Sender(pk)
            }
            InputRef::SigningMessage => {
                return Err((
                    TurnError::PreconditionFailed {
                        description:
                            "witnessed clause InputRef::SigningMessage is reserved for Authorization::Custom"
                                .into(),
                    },
                    path.to_vec(),
                ));
            }
        };
        registry.verify(wp, &input, &proof_blob.bytes).map_err(|e| {
            (
                TurnError::PreconditionFailed {
                    description: format!(
                        "witnessed clause {}: {}",
                        predicate_kind_name(wp.kind),
                        e
                    ),
                },
                path.to_vec(),
            )
        })
    }
}
