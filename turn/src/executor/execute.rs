//! Top-level turn execution: `execute()`, `wrap_witnessed`, `estimate_cost`, `validate_without_apply`.
//!
//! Extracted from `executor/mod.rs` (lines 2994-3812 of pre-decomposition file).

use super::*;

/// Common helper for fee share distribution (50% proposer / 30% treasury /
/// 20% fee well). Extracted to eliminate duplication between proof-carrying
/// sovereign fast path and normal forest path (excellence item from
/// conservation followup). Ensures consistent credit timing and logic for
/// post_state_hash / receipt / delta / AR consumers.
///
/// THE EPOCH §5 ("fees as moves"): the agent's full fee debit is matched by
/// credits — proposer share + treasury share + EVERYTHING ELSE (the 20%
/// remainder, integer-division dust, and any share whose recipient is
/// unconfigured or missing) moves to the FEE WELL when one is configured, so
/// the turn's total value delta is exactly zero (`reachable_total_zero`'s
/// hypotheses hold on the deployed chain, where genesis always configures
/// the well).
///
/// THE FEE LOOP (revolving fund): on devnet the fee well POINTS AT the faucet
/// cell (genesis-less backfill at `node/src/lib.rs`, and `fee_well: faucet_id`
/// in `node/src/genesis.rs`). So the `fee - delivered` credit here recirculates
/// straight back into the pool the faucet pays out of — closing the loop that
/// otherwise drained the faucet monotonically. NO fee is zeroed: the debit +
/// budget gate + faucet 1/min rate-limit remain the oversight leash.
///
/// With no fee well configured the undelivered remainder is burned — the legacy
/// pre-epoch semantics, kept only for well-less tests (every deployed boot mode
/// now configures the well, so this fallback is test-only).
fn distribute_fee_shares(
    ledger: &mut Ledger,
    proposer: Option<&CellId>,
    treasury: Option<&CellId>,
    fee_well: Option<&CellId>,
    fee: u64,
) {
    let proposer_share = fee / 2;
    // u128: `fee * 3` overflows u64 when fee > u64::MAX/3 (~6.15e18); in RELEASE
    // that wraps and mis-splits the fee. The 3/10 share is <= fee, so the cast
    // back to u64 is lossless.
    let treasury_share = ((fee as u128) * 3 / 10) as u64;
    let mut delivered: u64 = 0;
    if let Some(pid) = proposer {
        if let Some(p) = ledger.get_mut(pid) {
            if p.state.credit_balance(proposer_share) {
                delivered += proposer_share;
            }
        }
        // missing cell / overflow => share falls through to the fee well
    }
    if let Some(tid) = treasury {
        if let Some(t) = ledger.get_mut(tid) {
            if t.state.credit_balance(treasury_share) {
                delivered += treasury_share;
            }
        }
        // missing cell / overflow => share falls through to the fee well
    }
    // The move that closes the books: whatever was not delivered above goes
    // to the fee well (fee - delivered ≥ fee*2/10 by construction).
    if let Some(wid) = fee_well {
        if let Some(w) = ledger.get_mut(wid) {
            let _ = w.state.credit_balance(fee - delivered);
        }
    }
}

fn is_zero_hash(bytes: &[u8; 32]) -> bool {
    bytes.iter().all(|b| *b == 0)
}

/// Walk a call tree pre-order, collecting every `CellId` it references (action target + each
/// effect's referenced cells). Used to build the shadow's NODE-fed freeze-set (only referenced
/// cells can be named by a wire action, so only they can be frozen-checked). Mirrors the cell
/// collection in `lean_shadow::collect_tree_ids` (kept local to avoid widening that module's API).
fn collect_referenced_cells(
    tree: &crate::forest::CallTree,
    out: &mut std::collections::BTreeSet<CellId>,
) {
    use crate::action::Effect;
    out.insert(tree.action.target);
    for eff in &tree.action.effects {
        match eff {
            Effect::SetField { cell, .. }
            | Effect::IncrementNonce { cell }
            | Effect::SetPermissions { cell, .. }
            | Effect::SetVerificationKey { cell, .. }
            | Effect::EmitEvent { cell, .. }
            | Effect::MakeSovereign { cell }
            | Effect::Refusal { cell, .. }
            | Effect::RevokeCapability { cell, .. } => {
                out.insert(*cell);
            }
            Effect::Transfer { from, to, .. } => {
                out.insert(*from);
                out.insert(*to);
            }
            Effect::GrantCapability { from, to, cap } => {
                out.insert(*from);
                out.insert(*to);
                out.insert(cap.target);
            }
            Effect::RevokeDelegation { child } => {
                out.insert(*child);
            }
            Effect::CellSeal { target, .. }
            | Effect::CellUnseal { target }
            | Effect::CellDestroy { target, .. }
            | Effect::Burn { target, .. }
            // `Mint`'s recipient is an arbitrary PRE-EXISTING cell, exactly like `Burn`'s
            // holder — and `lean_shadow::effect_cells` assigns it a wire Nat
            // (`Effect::Mint { target } => vec![*target]`). Omitting it here made this
            // walker's stated mirror of `collect_tree_ids` FALSE and produced the unsafe
            // freeze under-report `ShadowHostCtx`'s host-obligation section names: a Mint
            // into a migration-FROZEN recipient reached the verified gate with that cell
            // absent from `frozen`, so the gate's frozen leg ADMITTED a turn the
            // true-facts gate REJECTS. Adding it can only ENLARGE the freeze set.
            | Effect::Mint { target, .. } => {
                out.insert(*target);
            }
            // Same mirror gap: `AttenuateCapability` narrows a slot the actor holds on
            // `cell`, and `effect_cells` registers it (`vec![*cell]`).
            Effect::AttenuateCapability { cell, .. } => {
                out.insert(*cell);
            }
            Effect::Introduce {
                introducer,
                recipient,
                target,
                ..
            } => {
                out.insert(*introducer);
                out.insert(*recipient);
                out.insert(*target);
            }
            // Effects whose write set is intrinsic (notes/queues/escrows/etc.) or self-targeted
            // reference no additional pre-existing cell beyond the action target collected above.
            //
            // ⚑ That justification is NOT true of every remaining arm, and saying so plainly is
            // the point: `SetProgram { cell }`, `RotatePqIdentity { cell }`, `Notify { from, to }`,
            // `Promise { cell }` and `ExerciseViaCapability`'s INNER effects all name pre-existing
            // cells this walker drops. They are safe TODAY only because `lean_shadow::effect_cells`
            // does not project them either, so such a turn is not comparable (`lean_verdict = None`)
            // and the gate never decides it — a GAP, not a check. Widening the marshaller to cover
            // any of them REQUIRES adding it here in the same change, or the freeze leg
            // under-reports and admits what the true-facts gate refuses.
            _ => {}
        }
    }
    for child in &tree.children {
        collect_referenced_cells(child, out);
    }
}

impl TurnExecutor {
    /// Snapshot the universal-map projection of the full executor state (the ledger +
    /// the executor-owned side tables) — THE EXECUTOR-STATE BRIDGE's pre/post surfaces
    /// (`crate::umem`; Lean twin `Dregg2/Exec/UniversalBridge.uproj`). Called only when
    /// [`TurnExecutor::umem_witness_enabled`] is set.
    fn umem_snapshot(&self, ledger: &Ledger) -> crate::umem::UProjection {
        crate::umem::project_executor_state(
            ledger,
            &self.note_nullifiers.lock().unwrap(),
            &self.bridged_nullifiers.lock().unwrap(),
            &self.factory_registry.borrow(),
        )
    }

    /// THE MID-FOREST YIELD POINT — checkpoint BETWEEN two effects of an in-flight turn.
    ///
    /// Called from the depth-first effect-application loop (`execute_tree`) right AFTER an
    /// effect appends to the journal. When [`Self::umem_yield_at`] names a journal-prefix
    /// length `k` and the live journal has just reached `k` entries (and nothing was
    /// captured yet), this snapshots `project_executor_state(ledger)` — the GENUINE
    /// mid-flight executor state, between two effects — into [`Self::last_umem_yield`].
    ///
    /// It is recursion-gated by [`Self::umem_witness_enabled`] (no work when the umem lane
    /// is off — the live proving path is untouched) and is an OBSERVATION only: it never
    /// changes the walk, never short-circuits, never emits a receipt. The turn still
    /// commits-or-rolls-back as a whole (the atomicity / receipt boundary stays whole-turn;
    /// the captured boundary is "this prefix, to be completed by the rest of THIS turn" —
    /// see `crate::continuation`). The FIRST crossing wins: a `>=` test with a once-guard
    /// (the `is_none` check) so a deeper recursion that pushes more entries does not clobber
    /// the boundary captured at exactly `k`.
    pub(crate) fn maybe_umem_yield(&self, ledger: &Ledger, journal: &LedgerJournal) {
        if !self
            .umem_witness_enabled
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            return;
        }
        let k = self
            .umem_yield_at
            .load(std::sync::atomic::Ordering::Relaxed);
        if k == u64::MAX || (journal.entries().len() as u64) < k {
            return;
        }
        let mut slot = self.last_umem_yield.lock().unwrap();
        if slot.is_none() {
            *slot = Some(self.umem_snapshot(ledger));
        }
    }

    /// Arm the mid-forest yield point at a journal-prefix length `k` (the boundary BETWEEN
    /// two effects at which the live forest walk snapshots executor state). Pass `None` to
    /// disarm. The yield only fires when [`Self::umem_witness_enabled`] is also set.
    pub fn set_umem_yield_at(&self, k: Option<u64>) {
        self.umem_yield_at
            .store(k.unwrap_or(u64::MAX), std::sync::atomic::Ordering::Relaxed);
    }

    /// Build a [`crate::continuation::Continuation`] from the most recent mid-forest yield.
    ///
    /// Pairs the live mid-flight snapshot ([`Self::last_umem_yield`], captured BETWEEN two
    /// effects by [`Self::maybe_umem_yield`]) with the committed whole-turn Blum trace
    /// ([`Self::last_umem_witness`]) and binds them via
    /// [`crate::continuation::Continuation::from_yield`]: the live boundary must equal a
    /// trace-prefix fold or capture is refused. Returns `None` when no yield fired, the umem
    /// witness is absent/errored, or the snapshot does not bind to the trace.
    pub fn capture_yielded_continuation(&self) -> Option<crate::continuation::Continuation> {
        let live = self.last_umem_yield.lock().unwrap().clone()?;
        let guard = self.last_umem_witness.lock().unwrap();
        let witness = guard.as_ref()?.as_ref().ok()?;
        crate::continuation::Continuation::from_yield(&witness.pre, &witness.ops, &live)
    }

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
    ///
    /// TRUST-CRITICAL: This function is the sole entry point for all ledger state mutations.
    /// If compromised: arbitrary state changes bypass authorization, preconditions, and fee metering.
    /// The federation's replicated execution ensures all members execute identically; divergence
    /// triggers consensus failure and halts the federation.
    ///
    /// Future: once Effect VM covers all effect types, every turn will carry a STARK proof,
    /// making this function a thin verify-and-commit wrapper (trustless).
    pub fn execute(&self, turn: &Turn, ledger: &mut Ledger) -> TurnResult {
        // Exact FNSP-v3 linearity: a committed token must be extracted before this executor can
        // begin another whole turn.  That makes any consumed token observed below attributable to
        // THIS execution, so every rejection can safely restore it to pending.
        {
            if let Err(error) = self.exact_fnsp_v3_admission_ready_for_execute() {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!("exact FNSP-v3 admission slot is not ready: {error}"),
                    },
                    at_action: vec![],
                };
            }
        }

        // The post-commit observer (the node's durable nullifier frontier). It is driven ONCE,
        // after the result is final — see the `obs.observe(..)` call below.
        //
        // ⚑ A pre-state capture stood here until 2026-07-30, building the NODE-fed admission ctx
        // (boundary-P1 bug 1) for a Lean↔Rust differential gated on `DREGG_LEAN_SHADOW=1`. That
        // variable was set by nothing, so the capture stored `None` on every deployed turn and the
        // differential never ran. The verified producer builds the SAME ctx itself
        // (`build_shadow_host_ctx`, called from `produce_via_lean`), which is where the bug-1 seam
        // actually lives and where it is exercised.
        let obs = self.shadow_observer.clone();

        // Factory quota is part of the same turn transaction as the newborn
        // cell. `CreateCellFromFactory` validates/records before all later
        // ledger checks have completed, so retain the exact pre-image until the
        // whole turn has committed.
        let factory_registry_checkpoint = Self::turn_mutates_factory_registry(turn)
            .then(|| self.factory_registry.borrow().clone());

        // Rate-limit debits are a candidate side-state transition until the Rust
        // execution has accepted. A rejected turn drops this value without ever
        // publishing it.
        let mut staged_rate_limits = super::execute_tree::StagedRateLimitState::default();
        let result = self.execute_without_shadow(turn, ledger, &mut staged_rate_limits);

        // Advance observer-owned CROSS-TURN state (the durable nullifier frontier). It does NOT
        // decide this turn — `result` is already final above.
        //
        // ⚑ THE VERIFIED DECISION IS NOT HERE. It is the authority inversion in
        // `dregg_exec_lean::lean_apply::produce_via_lean` (default-ON via `DREGG_LEAN_PRODUCER`),
        // which runs THIS function as its demoted Rust reference and then installs the verified
        // post-state and verdict over it. Two decisionless mechanisms that used to sit on this
        // line have been deleted rather than kept beside it: the `strict_veto_enabled`/`lean_vetoes`
        // pair (2026-07-28 — armed nowhere, dominated by the producer, and its rollback left the
        // agent's receipt-chain head advanced to a receipt that was never issued, so one vetoed
        // turn permanently bricked the agent), and the `DREGG_LEAN_SHADOW` differential
        // (2026-07-30 — the variable was set by nothing and the verdict was dropped by `let _ =`;
        // its cell-by-cell post-state comparison now decides `ProducerOutcome::divergence` on the
        // armed producer seam instead).
        obs.observe(turn, ledger, &result, self.block_height);

        if !result.is_committed() {
            let _ = self.restore_exact_fnsp_v3_admission_after_rejection();
        }
        if !result.is_committed() {
            if let Some(previous) = factory_registry_checkpoint {
                *self.factory_registry.borrow_mut() = previous;
            }
        }
        if result.is_committed() {
            staged_rate_limits.commit(self);
        }
        result
    }

    /// Build the HOST-fed admission context (boundary-P1 bug 1) from the executor's own state.
    /// Its ONE production caller is the verified producer (`lean_apply::produce_via_lean`); it is
    /// no longer built on the plain `execute` path, which used to build it for a differential
    /// gated on a variable nothing set.
    ///
    ///   * `block_height` — the chain clock (`self.block_height`);
    ///   * `frozen` — the cells frozen for migration (`self.cell_migrations`), the subset of
    ///     the turn's referenced cells that are frozen (a frozen agent / write-set
    ///     cell is what the verified `admissible` frozen leg rejects);
    ///   * `stored_head` — the agent's stored receipt-chain head (`self.get_last_receipt_hash`),
    ///     `None` = genesis; the verified ChainHead leg checks the turn's claimed
    ///     `prev` against it;
    ///   * `budget` — the Stingray silo budget slice (`self.budget_gate.remaining()`), the
    ///     verified Budget leg's `fee ≤ budget` bound.
    ///
    /// Build the NODE-fed shadow admission context from this executor's own state. Public so the
    /// node's PRODUCER MODE (`lean_apply::produce_via_lean`) can drive the verified Lean executor
    /// with EXACTLY the same admission context the Rust executor uses — the two producers must see
    /// the same clock / freeze-set / chain-head / budget, or the differential is meaningless.
    pub fn build_shadow_host_ctx(
        &self,
        turn: &Turn,
        ledger: &Ledger,
    ) -> crate::shadow::ShadowHostCtx {
        self.shadow_host_ctx(turn, ledger)
    }

    fn shadow_host_ctx(&self, turn: &Turn, ledger: &Ledger) -> crate::shadow::ShadowHostCtx {
        use std::collections::BTreeSet;

        // Collect the cells this turn references (agent + every action target + effect cell), then
        // keep only those the migration manager reports frozen. Only referenced cells can be named
        // by a wire action, so only they can be projected to wire Nats by the shadow.
        let mut referenced: BTreeSet<CellId> = BTreeSet::new();
        referenced.insert(turn.agent);
        for root in &turn.call_forest.roots {
            collect_referenced_cells(root, &mut referenced);
        }
        let frozen: Vec<CellId> = {
            let mgr = self.cell_migrations.lock().unwrap();
            referenced
                .into_iter()
                .filter(|c| {
                    // A referenced cell that is BOTH still in the ledger AND frozen is the
                    // admission-relevant case; an absent cell cannot be a write-set target.
                    let _ = ledger;
                    mgr.is_frozen(c)
                })
                .collect()
        };

        let stored_head = self.get_last_receipt_hash(&turn.agent);

        // The remaining silo budget slice the fee must fit. No gate ⇒ the diagnostic large slice
        // (the executor imposes no budget bound, so neither should the shadow).
        let budget = self
            .budget_gate
            .as_ref()
            .map(|g| g.lock().unwrap().slice.remaining())
            .unwrap_or(1_000_000_000);

        crate::shadow::ShadowHostCtx {
            block_height: self.block_height,
            frozen,
            stored_head,
            budget,
            intro_lifetime: self.max_introduction_lifetime,
            current_timestamp: self.current_timestamp as u64,
            federation_id: self.local_federation_id,
            // THE EPOCH §5 fee-distribution targets — the host policy `distribute_fee_shares`
            // applies (proposer fee/2, treasury fee*3/10, fee_well the remainder). The verified
            // kernel runs `distributeFee` against fixed PLACEHOLDER cells (`admCtxOfHost`'s
            // 0xF00/0xF01) + burns the residue, so the producer's reconstituted ledger carries no
            // real fee-well credit; threading the real targets lets the producer apply the IDENTICAL
            // distribution to the reconstituted ledger so a fee-bearing turn agrees on `.root()`.
            proposer_cell: self.proposer_cell,
            treasury_cell: self.treasury_cell,
            fee_well_cell: self.fee_well_cell,
        }
    }

    fn execute_without_shadow(
        &self,
        turn: &Turn,
        ledger: &mut Ledger,
        staged_rate_limits: &mut super::execute_tree::StagedRateLimitState,
    ) -> TurnResult {
        // MEASUREMENT-ONLY (`DREGG_TURN_PROFILE=1`): per-turn phase fences. When off,
        // `prof` is false and every `accum` below is skipped (no atomic writes).
        let prof = super::turn_profile::enabled();
        if prof {
            super::turn_profile::count_turn();
        }
        let _pt0 = super::turn_profile::Instant::now(); // `validate` phase start.

        // cap Phase C: a fresh turn starts with an empty consumed-capability
        // buffer (a prior REJECTED turn may have captured witnesses at its
        // auth sites before failing; they must not leak into this receipt).
        self.consumed_cap_witnesses
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clear();

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

        // Gate 3 — agent lifecycle (`cellLifecycleCanAuthor`). A TERMINAL agent
        // (Destroyed or Migrated) cannot author a turn. Mirrors the verified
        // `Dregg2.Exec.Admission.admissible` agent-lifecycle leg
        // (`cellLifecycleCanAuthor`, RecordKernel.lean), whose kernel-align fix
        // (`9e2c0e70`) admits the NON-terminal states (Live / Sealed / Archived)
        // — so a Sealed agent still self-unseals — and rejects ONLY the terminal
        // tombstones. Without this gate the executor admitted a Destroyed/Migrated
        // agent whose effects on a *non-terminal* target would then commit (the
        // per-effect liveness gate only guards the TARGET, never the actor): a
        // safe-direction divergence (Rust admits what the spec refuses). A
        // Migrated cell is an inert tombstone with no authoring path
        // (`cell/src/migration.rs`: the destination copy is the unique live home),
        // so refusing the full `is_terminal()` set has no legitimate-flow cost.
        if agent_cell.lifecycle.is_terminal() {
            return TurnResult::Rejected {
                reason: TurnError::AdmissionRefused {
                    reason: crate::AdmissionReason::DeadAgent,
                },
                at_action: vec![],
            };
        }

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
        // SIGNED balances (THE EPOCH §5): the agent is an ordinary cell, so
        // any negative reading or a balance below the fee refuses.
        if agent_cell.state.balance() < 0 || (agent_cell.state.balance() as u64) < turn.fee {
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
        //
        // GUARD: the write-set extraction (a forest walk + two Vec allocs +
        // sort/dedup) is only needed when SOME cell is frozen. In the common
        // no-migration case nothing is frozen, so skip the extraction entirely
        // (the per-effect `apply_effect` freeze checks remain as defence in
        // depth either way). Equivalent: with nothing frozen, every
        // `check_not_frozen` in the loop returns `Ok`.
        let any_frozen = self
            .cell_migrations
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .any_frozen();
        if any_frozen {
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

        // Compute the pre-state ANCHOR before any mutations — the AIR-bound chip
        // 8-felt commitment of the agent's cell (`crate::state_commit`), NOT the
        // trusted-Rust BLAKE3 `Ledger::root()` this used to stamp. See
        // `state_commit`'s module docs for the labeled residual.
        //
        // SYMBOLIC EXECUTION (`crate::collapse`): in WitnessMode::Symbolic the
        // per-turn witness is DEFERRED — we skip the anchor computation and
        // stamp the deferred sentinel instead. The state transition below still
        // applies in full; only the witness is deferred (recovered on demand by
        // `collapse`). EXCEPTION:
        // the proof-carrying sovereign path (`turn.execution_proof.is_some()`)
        // is itself an ADMISSION/witness gate — its STARK binds the committed
        // state commitment — so it always materializes the real root (a witness
        // gate is never deferred; only the classical-path witness is).
        let symbolic_defer = self.is_symbolic() && turn.execution_proof.is_none();
        if prof {
            super::turn_profile::accum(super::turn_profile::Phase::validate, _pt0);
        }
        let _pt_root = super::turn_profile::Instant::now();
        let pre_state_hash = if symbolic_defer {
            crate::collapse::DEFERRED_STATE_HASH
        } else {
            self.consensus_state_commitment(ledger, &turn.agent)
        };
        if prof {
            super::turn_profile::accum(super::turn_profile::Phase::pre_root, _pt_root);
        }

        // =====================================================================
        // PHASE 1: Commit fee + nonce (NEVER rolled back).
        // This prevents DoS via expensive-but-failing turns that never pay.
        // =====================================================================
        let _pt_p1 = super::turn_profile::Instant::now();
        {
            let agent = ledger.get_mut(&turn.agent).unwrap();
            // Ordinary debit (fee-coverage was checked above; a false return
            // here means a TOCTOU bug, so refuse loudly rather than going
            // negative).
            if !agent.state.debit_balance(turn.fee) {
                return TurnResult::Rejected {
                    reason: TurnError::InsufficientBalance {
                        cell: turn.agent,
                        required: turn.fee,
                        available: agent.state.balance(),
                    },
                    at_action: vec![],
                };
            }
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
                        self.fee_well_cell.as_ref(),
                        turn.fee,
                    );

                    // The AIR-bound post-state anchor (same function as the
                    // pre-state above, so `verify_receipt_chain`'s continuity
                    // check compares like with like).
                    let post_state_hash = self.consensus_state_commitment(ledger, &turn.agent);
                    // Compute the forest hash once; reuse for turn_hash + receipt field.
                    let forest_hash = turn.call_forest.compute_hash();
                    let turn_hash = turn.hash_with_forest(&forest_hash);

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
                        // cap Phase C: drain any consumed-capability witnesses
                        // captured before this proof-carrying early-commit.
                        consumed_capabilities: self.take_consumed_cap_witnesses(),
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
                    let mut fee_delivered: u64 = 0;
                    if let Some(proposer_id) = &self.proposer_cell {
                        let mut d = dregg_cell::CellStateDelta::empty();
                        d.balance_change = (turn.fee / 2) as i64;
                        fee_delivered += turn.fee / 2;
                        delta.updated.push((*proposer_id, d));
                    }
                    if let Some(treasury_id) = &self.treasury_cell {
                        let mut d = dregg_cell::CellStateDelta::empty();
                        // u128 to avoid the `turn.fee * 3` u64 wrap near the ceiling.
                        let treasury_share = ((turn.fee as u128) * 3 / 10) as u64;
                        d.balance_change = treasury_share as i64;
                        fee_delivered += treasury_share;
                        delta.updated.push((*treasury_id, d));
                    }
                    // THE EPOCH §5 ("fees as moves"): the remainder moves to
                    // the fee well, closing the delta to exactly zero.
                    if let Some(well_id) = &self.fee_well_cell {
                        let mut d = dregg_cell::CellStateDelta::empty();
                        d.balance_change = (turn.fee - fee_delivered) as i64;
                        delta.updated.push((*well_id, d));
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
            // 7a. Production sovereign witnesses must name a real post-state
            //     commitment. All-zero is a legacy placeholder, not an explicit
            //     no-op commitment. A no-op sovereign transition must still sign
            //     the real unchanged state commitment.
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
            // 7b. THE EFFECTS BINDING. `effects_hash` rides in the signing
            //     message (rule 5 above), so until this check existed it was a
            //     field the owner signed and NOTHING compared: a sovereign owner
            //     could sign `H(Transfer 10)` while the executor applied
            //     `Transfer 20`, and the turn committed. `EffectsHashMismatch`
            //     was defined, formatted, and handled — and constructed zero
            //     times.
            //
            //     `sovereign_effects_hash` is a pure function of the turn, so
            //     this runs HERE — with the other witness rules, BEFORE the
            //     forest mutates anything — rather than beside the
            //     post-execution `new_commitment` check. The two declarations
            //     are checked against two different things: this one against the
            //     turn's own effect sequence, `new_commitment` against the
            //     recomputed post-state (see `SOVEREIGN CELL POST-EXECUTION`).
            //
            //     The all-zero `effects_hash` sentinel that used to live here is
            //     GONE, and deliberately: the canonical hash absorbs a domain
            //     tag, the cell id and a length, so `[0u8; 32]` is not a value it
            //     can take — a witness authorizing no effects has an honest
            //     encoding. Special-casing one wrong value implies the others are
            //     fine, and that implication is exactly what this hole was made
            //     of. The zero placeholder is still refused; it is refused by the
            //     rule that binds, as `EffectsHashMismatch`.
            let expected_effects_hash = turn.sovereign_effects_hash(cell_id);
            if witness.effects_hash != expected_effects_hash {
                return TurnResult::Rejected {
                    reason: TurnError::EffectsHashMismatch {
                        cell: *cell_id,
                        expected: expected_effects_hash,
                        got: witness.effects_hash,
                    },
                    at_action: vec![],
                };
            }
            // 8. Optional STARK transition proof. The v1 hand-AIR witness-STARK verify is
            //    RETIRED; a sovereign witness carrying a v1 `transition_proof` fails closed on
            //    every build (the rotated proof-carrying turn is the sovereign attestation path).
            if let Some(proof_bytes) = &witness.transition_proof {
                // The v1 hand-AIR witness-STARK verify is RETIRED. A sovereign witness carrying a
                // v1 `transition_proof` cannot be verified here — fail closed (the rotated
                // proof-carrying turn is the sole sovereign attestation path).
                let _ = proof_bytes;
                return TurnResult::Rejected {
                    reason: TurnError::InvalidExecutionProof(
                        "sovereign witness carries a v1 transition_proof, which is no longer \
                         verified (use the rotated proof-carrying turn)"
                            .into(),
                    ),
                    at_action: vec![],
                };
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
        // THE EXECUTOR-STATE BRIDGE (recursion-gated, OFF by default): snapshot the
        // universal-map projection at the journal window's start so the committed
        // turn can be re-read as a Blum memory-op trace (`crate::umem::emit_trace`).
        let umem_pre = if self
            .umem_witness_enabled
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            // A fresh forest window: discard any mid-forest yield captured by a prior
            // turn so this turn's yield boundary (if `umem_yield_at` is set) is its own.
            *self.last_umem_yield.lock().unwrap() = None;
            Some(self.umem_snapshot(ledger))
        } else {
            None
        };

        let mut journal = LedgerJournal::with_capacity(16);
        let mut computrons_used: u64 = 0;
        let mut all_effects_hashes: Vec<[u8; 32]> = Vec::new();

        // COORDINATION EXEMPTION ("leash, not ledger") — opt-in via
        // `ComputronCosts::coordination_exempt`. An EmitEvent-only turn with no
        // `balance_change` anywhere in its forest (`Turn::is_coordination`) is
        // oversight traffic, so its CHARGE is waived: the tree walk meters with
        // an uncapped budget (so `computrons_used` stays the TRUE cost in the
        // receipt) and the admission comparison below charges 0. Economic turns
        // are untouched — any non-EmitEvent effect disqualifies the whole turn.
        let coordination_exempt = self.costs.coordination_exempt && turn.is_coordination();
        let metering_budget = if coordination_exempt {
            u64::MAX
        } else {
            turn.fee
        };
        let mut excess: i64 = 0; // Mina-style excess: must be zero at turn end.
        // Per-asset conservation accumulator: `(target-cell 32-byte asset id,
        // delta)` for every `balance_change`, grouped by the target's committed
        // `Cell::asset()`. The scalar `excess` only proves the deltas net to zero
        // ACROSS assets; this is checked per-asset at turn end so a cross-asset
        // teleport (mint X against burn self-issued Y) is REFUSED. The ID is
        // carried, not the ~31-bit fold, so the turn-end gate can still refuse two
        // DISTINCT currencies that share a class.
        let mut asset_deltas: Vec<([u8; 32], i64)> = Vec::new();

        // Everything from PHASE 1 start through here (incl. sovereign-witness /
        // binding-sweep gates, trivial for the classical forest path) is the
        // `phase1` accumulator; the forest walk below is the `forest` accumulator.
        if prof {
            super::turn_profile::accum(super::turn_profile::Phase::phase1, _pt_p1);
        }
        let _pt_forest = super::turn_profile::Instant::now();

        for (root_idx, root_tree) in turn.call_forest.roots.iter().enumerate() {
            let result = self.execute_tree(
                root_tree,
                ledger,
                &turn.agent,
                // Top-level: the turn agent is the root authority and owns its own
                // capabilities. `ParentsOwn` here is the ROOT marker — it is only ever
                // consulted by the root frame, where reaching the "no capability" arm
                // means the agent genuinely lacks a cap to a non-self target
                // (CapabilityNotHeld). It is NOT delegation: cross-cell child delegation
                // is gated separately (None/ParentsOwn→fail-closed, SnapshotRefresh
                // implemented) in execute_tree.
                DelegationMode::ParentsOwn,
                &mut computrons_used,
                metering_budget,
                &mut all_effects_hashes,
                vec![root_idx],
                &mut journal,
                &mut excess,
                &mut asset_deltas,
                turn.nonce,
                &turn.agent,
                // `created_by_turn`: the pre-execution turn INPUT hash. NOT the
                // post-execution receipt hash (which depends on the effects this
                // turn applies — circular). Folded into installed-cap provenance.
                turn.hash(),
                staged_rate_limits,
            );

            if let Err((error, path)) = result {
                // Rollback: replay journal in reverse to restore ledger.
                // Also removes any obligation/escrow/nullifier insertions from
                // the executor's in-memory maps (prevents phantom record attacks).
                journal.rollback(
                    ledger,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.note_commitments,
                    &self.note_revoked,
                    &self.note_shielded,
                    &self.reactive_registry,
                    &self.reactive_nullifiers,
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

        if prof {
            super::turn_profile::accum(super::turn_profile::Phase::forest, _pt_forest);
        }
        let _pt_post = super::turn_profile::Instant::now();

        // Check total cost against fee. A coordination-exempt turn CHARGES 0
        // (the class waiver) while `computrons_used` keeps the true metered
        // cost for the receipt — the leash stays observable, only the toll is
        // waived.
        let charged = if coordination_exempt {
            0
        } else {
            computrons_used
        };
        if charged > turn.fee {
            journal.rollback(
                ledger,
                &self.bridged_nullifiers,
                &self.note_nullifiers,
                &self.note_commitments,
                &self.note_revoked,
                &self.note_shielded,
                &self.reactive_registry,
                &self.reactive_nullifiers,
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
                &self.bridged_nullifiers,
                &self.note_nullifiers,
                &self.note_commitments,
                &self.note_revoked,
                &self.note_shielded,
                &self.reactive_registry,
                &self.reactive_nullifiers,
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
                &self.bridged_nullifiers,
                &self.note_nullifiers,
                &self.note_commitments,
                &self.note_revoked,
                &self.note_shielded,
                &self.reactive_registry,
                &self.reactive_nullifiers,
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

        // Check PER-ASSET conservation: the scalar `excess == 0` above only
        // proves the balance deltas sum to zero ACROSS asset classes — a +N on
        // cell(token X) against a −N on a self-issued cell(token Y) nets `excess`
        // to 0 yet mints X from worthless Y. Group every delta by its target
        // cell's committed asset class and require EACH asset's Σδ == 0
        // independently, through the SAME in-AIR-backed `BlockConservation`
        // collector the atomic path uses (`check_per_asset_conservation_by_asset`
        // — no second conservation implementation). A single-asset imbalance was
        // already caught by `excess != 0` above, so this fires only on the
        // cross-asset teleport that the scalar sum cannot see.
        //
        // ⚑ AND THE CLASS IS ONE ~31-BIT FELT. `check_per_asset_conservation_by_asset_id`
        // is handed the 32-BYTE ids and REFUSES the turn outright if two distinct
        // currencies fold to one class — a check that is impossible one line later,
        // and impossible for the Lean decider, which is handed the folded `u32`.
        if let Err(err) = Self::check_per_asset_conservation_by_asset_id(&asset_deltas) {
            journal.rollback(
                ledger,
                &self.bridged_nullifiers,
                &self.note_nullifiers,
                &self.note_commitments,
                &self.note_revoked,
                &self.note_shielded,
                &self.reactive_registry,
                &self.reactive_nullifiers,
            );
            for cell_id in &sovereign_cell_ids {
                ledger.remove(cell_id);
            }
            if let (Some(gate_cell), Some((digest, fee))) =
                (&self.budget_gate, &budget_debit_digest)
            {
                gate_cell.lock().unwrap().fast_unlock(*fee, digest);
            }
            let reason = match err {
                super::atomic::AtomicTurnError::PerAssetConservationViolation {
                    asset,
                    imbalance,
                } => TurnError::PerAssetConservationViolation { asset, imbalance },
                // FAIL CLOSED: no verified conservation gate was available to decide the
                // asset-inflation boundary. Surfaced as itself — NOT collapsed into a
                // conservation "violation", because the turn may well conserve; nothing
                // entitled to say so was installed. See `conservation_oracle`.
                super::atomic::AtomicTurnError::ConservationGateUnavailable => {
                    TurnError::ConservationGateUnavailable
                }
                // TWO DISTINCT CURRENCIES AT ONE ~31-BIT CLASS. Surfaced as
                // ITSELF, never collapsed into a conservation "violation": the
                // turn's arithmetic may be perfect; the PARTITION it would be
                // judged under merges two assets, so no verdict taken over it
                // means anything. See `fold_token_id_to_asset`.
                super::atomic::AtomicTurnError::AssetClassCollision {
                    first,
                    second,
                    class,
                } => TurnError::AssetClassCollision {
                    first,
                    second,
                    class,
                },
                // A ROW WHOSE MAGNITUDE THE FIELD CANNOT DENOTE. Surfaced as
                // ITSELF, never collapsed into a conservation "violation" (nor
                // into `ExcessNotZero`, which here would report `excess: 0` and
                // read as a contradiction): the turn's arithmetic may be exact —
                // what cannot happen is carrying the row to a decider. `|δ| = p`
                // used to encode to the field's ZERO and this turn COMMITTED —
                // `Action::balance_change` is an arbitrary `i64`, so THIS path is
                // the reachable producer. See `atomic::net_delta_mag_felt`.
                super::atomic::AtomicTurnError::NetDeltaNotRepresentable { asset, delta } => {
                    TurnError::NetDeltaNotRepresentable { asset, delta }
                }
                // `check_per_asset_conservation_by_asset_id` returns only those
                // four; any other variant is a contract break, surfaced as a
                // plain conservation failure.
                _ => TurnError::ExcessNotZero { excess },
            };
            return TurnResult::Rejected {
                reason,
                at_action: vec![],
            };
        }

        // =====================================================================
        // SOVEREIGN CELL POST-EXECUTION: Compute new commitments and remove
        // the temporarily-injected cells from the hosted store.
        // The federation stores only the updated 32-byte commitment.
        //
        // This block checks the witness's `new_commitment` — the POST-STATE
        // declaration, which needs execution to have happened. The witness's
        // OTHER declaration, `effects_hash`, is a pure function of the turn and
        // is checked as witness rule 7b above, before the forest runs
        // (`TurnError::EffectsHashMismatch`). Both declarations are checked;
        // they are checked at different points because they are claims about
        // different things.
        // =====================================================================
        for cell_id in &sovereign_cell_ids {
            let Some(cell) = ledger.get(cell_id) else {
                journal.rollback(
                    ledger,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.note_commitments,
                    &self.note_revoked,
                    &self.note_shielded,
                    &self.reactive_registry,
                    &self.reactive_nullifiers,
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
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.note_commitments,
                    &self.note_revoked,
                    &self.note_shielded,
                    &self.reactive_registry,
                    &self.reactive_nullifiers,
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

        // PI v3 committed-height column: every cell touched by this turn has its
        // `committed_height` advanced to the current chain height. This binds the
        // post-turn state commitment to a specific height, closing the temporal
        // gate's prover-chosen-height note. The update is journaled so rollback
        // (if this turn later fails at a downstream check) restores the old height.
        {
            use crate::journal::JournalEntry;
            let mut touched: std::collections::BTreeSet<CellId> = std::collections::BTreeSet::new();
            for entry in journal.entries() {
                let cell = match entry {
                    JournalEntry::SetField { cell, .. }
                    | JournalEntry::SetBalance { cell, .. }
                    | JournalEntry::SetNonce { cell, .. }
                    | JournalEntry::GrantCapability { cell, .. }
                    | JournalEntry::RevokeCapability { cell, .. }
                    | JournalEntry::CreateCell { cell }
                    | JournalEntry::SetProvedState { cell, .. }
                    | JournalEntry::SetPermissions { cell, .. }
                    | JournalEntry::SetVerificationKey { cell, .. }
                    | JournalEntry::SetDelegation { cell, .. }
                    | JournalEntry::SetDelegationEpoch { cell, .. }
                    | JournalEntry::SetCommittedHeight { cell, .. }
                    | JournalEntry::EventEmitted { cell, .. }
                    | JournalEntry::SetLifecycle { cell, .. }
                    | JournalEntry::AttenuateCapability { cell, .. } => Some(*cell),
                    _ => None,
                };
                if let Some(cell) = cell {
                    touched.insert(cell);
                }
            }
            for cell_id in touched {
                if let Some(c) = ledger.get_mut(&cell_id) {
                    let old_height = c.state.committed_height();
                    if old_height != self.block_height {
                        journal.record_set_committed_height(cell_id, old_height);
                        c.state.set_committed_height(self.block_height);
                    }
                }
            }
        }

        // THE EXECUTOR-STATE BRIDGE: the forest committed — snapshot the post
        // projection and re-read the journal as the turn's Blum write trace. The
        // window deliberately closes BEFORE Phase 3 fee distribution (the witness
        // covers the forest's effect semantics; fee/nonce legs are turn-level and
        // outside the journal, exactly as the journal itself scopes).
        if let Some(pre) = umem_pre {
            let post = self.umem_snapshot(ledger);
            let witness = crate::umem::emit_trace(&pre, &post, journal.entries());
            if let Err(e) = &witness {
                tracing::warn!("umem witness emission refused: {e}");
            }
            *self.last_umem_witness.lock().unwrap() = Some(witness);
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
            self.fee_well_cell.as_ref(),
            turn.fee,
        );

        // Phase 4: Compute receipt.
        //
        // SYMBOLIC EXECUTION: in WitnessMode::Symbolic this classical forest
        // path DEFERS the post-state witness — skip the anchor and stamp the
        // deferred sentinel. The state transition above already applied;
        // `collapse` re-runs this turn under Full to materialize the real
        // `post_state_hash`. (`symbolic_defer` was computed at the pre-state
        // above; the forest path is never proof-carrying, so it is simply
        // `self.is_symbolic()` here.)
        if prof {
            super::turn_profile::accum(super::turn_profile::Phase::post, _pt_post);
        }
        let _pt_postroot = super::turn_profile::Instant::now();
        let post_state_hash = if symbolic_defer {
            crate::collapse::DEFERRED_STATE_HASH
        } else {
            self.consensus_state_commitment(ledger, &turn.agent)
        };
        if prof {
            super::turn_profile::accum(super::turn_profile::Phase::post_root, _pt_postroot);
        }
        let _pt_receipt = super::turn_profile::Instant::now();
        let effects_hash = self.compute_effects_hash(&all_effects_hashes);

        // Compute the forest hash ONCE and reuse it for both the turn hash and
        // the receipt's `forest_hash` field — `turn.hash()` would otherwise walk
        // the whole call tree a SECOND time internally (the forest BLAKE3 walk is
        // the dominant ingredient of both). Byte-identical: `hash_with_forest`
        // takes exactly the value `turn.hash()` recomputes.
        let forest_hash = turn.call_forest.compute_hash();
        let turn_hash = turn.hash_with_forest(&forest_hash);

        // Build ledger delta from the journal, Phase 1 (fee + nonce), and Phase 3 (distribution).
        let delta = Self::compute_delta_from_journal_with_fee(
            &journal,
            ledger,
            &turn.agent,
            turn.fee,
            self.proposer_cell.as_ref(),
            self.treasury_cell.as_ref(),
            self.fee_well_cell.as_ref(),
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
            // cap Phase C: the capabilities CONSUMED to authorize this turn,
            // witnessed against the pre-state capability_root at the auth
            // sites. Empty for self-sovereign turns.
            consumed_capabilities: self.take_consumed_cap_witnesses(),
        };
        // R-4: sign the receipt over its canonical hash if the executor has
        // been configured with a signing key (`with_executor_signing_key`).
        receipt.executor_signature = self.maybe_sign_receipt(&receipt);

        // P0-3: record the new chain-head for this agent.
        self.record_receipt_hash(turn.agent, receipt.receipt_hash());

        // THE WRITE-SET (CORE-AUDIT.md finding 1): capture this turn's EXACT
        // mutated cells from the journal, so a durable consumer reconstructs
        // post-state from a COMPLETE change-set. The journal names every cell it
        // touched (incl. the cells an effect resolves at runtime — a burn's well,
        // a create's newborn, a factory birth — that a syntactic input-turn walk
        // misses). Overwrites the prior turn's set; read via `last_write_set()`.
        *self.last_write_set.lock().unwrap() = journal.touched_cells();

        if prof {
            super::turn_profile::accum(super::turn_profile::Phase::receipt, _pt_receipt);
        }

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
    ///
    /// A COORDINATION turn (`Turn::is_coordination`) estimates 0 when the
    /// executor opts into `ComputronCosts::coordination_exempt` — the
    /// admission-side mirror of the execution-path charge waiver, so
    /// `validate_without_apply` and fee-sizing clients agree that the class
    /// rides free ("leash, not ledger").
    pub fn estimate_cost(&self, turn: &Turn) -> u64 {
        if self.costs.coordination_exempt && turn.is_coordination() {
            return 0;
        }
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

        // Gate 3 — agent lifecycle (`cellLifecycleCanAuthor`). A TERMINAL agent
        // (Destroyed or Migrated) cannot author a turn. This mirrors the gate in
        // `execute_without_shadow` and the verified `Dregg2.Exec.Admission.admissible`
        // agent-lifecycle leg. Without it, `validate_without_apply` (the
        // admit-without-applying entry — pre-checks, mempool, fee estimation) admits
        // a Destroyed/Migrated agent the executor would then reject, a validate↔execute
        // divergence in the dangerous direction (validate accepts what apply refuses).
        if agent_cell.lifecycle.is_terminal() {
            return Err(TurnError::AdmissionRefused {
                reason: crate::AdmissionReason::DeadAgent,
            });
        }

        if agent_cell.state.nonce() != turn.nonce {
            return Err(TurnError::NonceReplay {
                expected: agent_cell.state.nonce(),
                got: turn.nonce,
            });
        }

        if agent_cell.state.balance() < 0 || (agent_cell.state.balance() as u64) < turn.fee {
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
}
