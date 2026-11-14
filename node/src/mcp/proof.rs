//! `mcp::proof` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

/// 32-byte-widening helper (effect-vm-hash-widen lane, 2026-05-28): the
/// EffectVM `GrantCapability.cap_entry` param is now `[BabyBear; 8]`. These
/// MCP construction sites carry a SCALAR cap-slot index (not a 32-byte hash),
/// so we anchor it in limb[0] — which drives the AIR's cap_root advance — and
/// leave the high limbs zero. This is byte-for-byte equivalent to the prior
/// single-felt binding, now in the widened 8-limb shape.
pub(super) fn grant_cap_entry_8(scalar: u32) -> [dregg_circuit::BabyBear; 8] {
    let mut a = [dregg_circuit::BabyBear::ZERO; 8];
    a[0] = dregg_circuit::BabyBear::new(scalar);
    a
}

// ⚑ DELETED 2026-07-28, with the two projectors it served (`project_effects_for_mcp`,
// `project_setfield_to_vm`) and the `setfield_value_lane_tooth` parity tests that pinned
// them: `setfield_value_lane`, the node-local `Effect::SetField` -> one-felt projection.
//
// Those projectors existed ONLY to feed `require_effect_vm_proof` / the retired v1
// standalone attestation, and with that gone they had no production caller — the tooth
// was pinning a TWIN of `dregg_sdk::AgentCipherclerk::try_convert_effects_to_vm` against
// the executor bridge. Deleting the twin is strictly stronger than testing that it agrees:
// the ONE producer the node now consults is the cipherclerk's, which is the same function
// the prove pool runs downstream (`turn_proving::prove_and_verify_finalized_turn`).
// `parse_effect_json`'s canonical-encoding test survives below — that surface is live.

/// Parse a JSON effect descriptor into a turn `Effect`.
///
/// Supports the subset needed for the two-AI handoff demo:
/// - `{ "type": "transfer", "from": "<hex>", "to": "<hex>", "amount": N }`
/// - `{ "type": "increment_nonce", "cell": "<hex>" }`
/// - `{ "type": "set_field", "cell": "<hex>", "index": N, "value": N }`
///
/// Returns a human-readable error string when the descriptor is malformed.
/// MCP-first: this is the canonical effect-parsing surface; the HTTP API
/// would derive from it if/when it gains an effects body.
pub(super) fn parse_effect_json(value: &Value) -> Result<dregg_turn::Effect, String> {
    let ty = value
        .get("type")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "effect missing 'type' field".to_string())?;

    let get_hex_32 = |obj: &Value, field: &str| -> Result<[u8; 32], String> {
        let s = obj
            .get(field)
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("effect.{ty} missing field '{field}'"))?;
        hex_decode(s).map_err(|_| format!("effect.{ty}.{field}: invalid hex (expected 64 chars)"))
    };

    match ty {
        "transfer" => {
            let from = get_hex_32(value, "from")?;
            let to = get_hex_32(value, "to")?;
            let amount = value
                .get("amount")
                .and_then(|v| v.as_u64())
                .ok_or_else(|| "effect.transfer missing 'amount'".to_string())?;
            Ok(dregg_turn::Effect::Transfer {
                from: dregg_cell::CellId(from),
                to: dregg_cell::CellId(to),
                amount,
            })
        }
        "increment_nonce" => {
            let cell = get_hex_32(value, "cell")?;
            Ok(dregg_turn::Effect::IncrementNonce {
                cell: dregg_cell::CellId(cell),
            })
        }
        "set_field" => {
            let cell = get_hex_32(value, "cell")?;
            let index = value
                .get("index")
                .and_then(|v| v.as_u64())
                .ok_or_else(|| "effect.set_field missing 'index'".to_string())?;
            let value_u64 = value
                .get("value")
                .and_then(|v| v.as_u64())
                .ok_or_else(|| "effect.set_field missing 'value'".to_string())?;
            // CANONICAL field encoding — `dregg_cell::field_from_u64` (the payload in
            // bytes 24..32, BIG-endian), the SAME lane `field_to_u64` reads and every
            // capacity gate evaluates over. This surface previously wrote
            // `value_bytes[..4] = (value as u32).to_le_bytes()`, an MCP-local dialect
            // that (a) silently dropped the high 32 bits of a u64 and (b) produced a
            // field element the cell evaluator reads back as ZERO (`field_to_u64` reads
            // bytes 24..32) and that `field_result_in_range` REFUSES outright (it
            // requires `value[..24] == 0`).
            Ok(dregg_turn::Effect::SetField {
                cell: dregg_cell::CellId(cell),
                index,
                value: dregg_cell::field_from_u64(value_u64),
            })
        }
        other => Err(format!(
            "unknown effect type '{other}' (supported: transfer, increment_nonce, set_field)"
        )),
    }
}

/// Build a CallForest with a single root action containing the given effects.
pub(super) fn build_forest_with_effects(
    target: CellId,
    effects: Vec<dregg_turn::Effect>,
) -> CallForest {
    let action = dregg_turn::Action {
        target,
        method: dregg_turn::action::symbol("execute"),
        args: vec![],
        authorization: dregg_turn::Authorization::Unchecked,
        preconditions: dregg_cell::Preconditions::default(),
        effects,
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);
    forest
}

/// Build a CallForest with a single root action authorized by an Ed25519
/// signature over the canonical action-signing message. The signature is
/// produced by `cipherclerk.sign_bytes` against `TurnExecutor::compute_signing_message`
/// in Full commitment mode using the executor's default federation id
/// (`[0u8; 32]`) — which matches `TurnExecutor::new(...).local_federation_id`.
///
/// `turn_nonce` must be the nonce the enclosing turn is submitted under
/// (`dregg-action-sig-v3` binds it into the signing message; callers here
/// stamp `turn.nonce = cclerk.receipt_chain_length()`).
pub(super) fn build_signed_forest(
    target: CellId,
    effects: Vec<dregg_turn::Effect>,
    cclerk: &dregg_sdk::AgentCipherclerk,
    federation_id: &[u8; 32],
    turn_nonce: u64,
) -> CallForest {
    let mut action = dregg_turn::Action {
        target,
        method: dregg_turn::action::symbol("execute"),
        args: vec![],
        authorization: dregg_turn::Authorization::Unchecked,
        preconditions: dregg_cell::Preconditions::default(),
        effects,
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    // Compute the canonical signing message and replace Unchecked with
    // Authorization::Signature so cells with `delegate: Signature` accept
    // the action.
    let msg = dregg_turn::TurnExecutor::compute_signing_message(&action, federation_id, turn_nonce);
    let sig = cclerk.sign_bytes(&msg);
    let mut r = [0u8; 32];
    let mut s = [0u8; 32];
    r.copy_from_slice(&sig.0[..32]);
    s.copy_from_slice(&sig.0[32..]);
    action.authorization = dregg_turn::Authorization::Signature(r, s);

    let mut forest = CallForest::new();
    forest.add_root(action);
    forest
}

#[derive(Debug)]
pub(super) struct EffectVmProofMaterial {
    pub(super) proof_hex: String,
    pub(super) public_inputs: Vec<u64>,
    pub(super) trace_rows: Vec<Vec<u32>>,
    pub(super) witness_hash_hex: String,
}

impl EffectVmProofMaterial {
    pub(super) fn into_parts(self) -> (String, Vec<u64>, Vec<Vec<u32>>, String) {
        (
            self.proof_hex,
            self.public_inputs,
            self.trace_rows,
            self.witness_hash_hex,
        )
    }
}

// ⚑ DELETED 2026-07-28: `witnessed_receipt_from_effect_material`. It returned `None`
// UNCONDITIONALLY (the v1 receipt-bound WR is retired) after computing a PI vector and
// a trace it then discarded, and its five callers all wrote `if let Some(w) = … {
// push_witnessed_receipt(w) }`. A function that cannot return `Some` is not a producer
// that happens to be off — it is a shape that makes a retired lane look live. The
// per-receipt attestation is the ROTATED finalized-turn proof the async prove pool
// produces; see [`attest_committed_turn`], which the five callers now use instead.

// ⚑ DELETED 2026-07-28: `require_pre_state`, the ACTOR-cell `(balance, nonce)` guard.
// Its message said it plainly — "refusing to execute without Effect VM pre-state" — and
// that tuple was an input to the retired v1 prover and to nothing else. A missing ACTOR
// cell is the EXECUTOR's question to answer (it rejects the turn, by variant), not an
// attestation precondition to refuse a commit on. At three of its four call sites it was
// already redundant with a check made earlier in the same function
// (`require_local_cell_for_commit` / the bilateral from+to ledger checks), so those
// refusals are unchanged and their tests still pin them.
//
// `require_local_cell_for_commit` and `require_effect_cells_for_commit` below are NOT
// this: they refuse to SYNTHESIZE a remote stub for a cell the turn will mutate, which is
// a statement about state, not about proving.

pub(super) fn require_local_cell_for_commit(
    ledger: &dregg_cell::Ledger,
    cell: &dregg_cell::CellId,
    label: &str,
) -> Result<(), McpToolResult> {
    if ledger.get(cell).is_some() {
        return Ok(());
    }
    Err(McpToolResult::json(&serde_json::json!({
        "activity_status": "rejected",
        "proof_status": "missing_pre_state",
        "committed": false,
        "exercised": false,
        "error": format!("{label}: cell {} is not in the local ledger; refusing to synthesize a remote stub for a turn that would mutate it", hex_encode(&cell.0)),
    })))
}

pub(super) fn require_effect_cells_for_commit(
    ledger: &dregg_cell::Ledger,
    effects: &[dregg_turn::Effect],
    label: &str,
) -> Result<(), McpToolResult> {
    for effect in effects {
        match effect {
            dregg_turn::Effect::Transfer { from, to, .. } => {
                require_local_cell_for_commit(ledger, from, label)?;
                require_local_cell_for_commit(ledger, to, label)?;
            }
            dregg_turn::Effect::GrantCapability { from, to, cap } => {
                require_local_cell_for_commit(ledger, from, label)?;
                require_local_cell_for_commit(ledger, to, label)?;
                require_local_cell_for_commit(ledger, &cap.target, label)?;
            }
            dregg_turn::Effect::SetField { cell, .. }
            | dregg_turn::Effect::IncrementNonce { cell }
            | dregg_turn::Effect::RevokeCapability { cell, .. }
            | dregg_turn::Effect::EmitEvent { cell, .. }
            | dregg_turn::Effect::SetPermissions { cell, .. }
            | dregg_turn::Effect::SetVerificationKey { cell, .. }
            | dregg_turn::Effect::Refusal { cell, .. } => {
                require_local_cell_for_commit(ledger, cell, label)?;
            }
            dregg_turn::Effect::Introduce {
                introducer,
                recipient,
                target,
                ..
            } => {
                require_local_cell_for_commit(ledger, introducer, label)?;
                require_local_cell_for_commit(ledger, recipient, label)?;
                require_local_cell_for_commit(ledger, target, label)?;
            }

            dregg_turn::Effect::CellSeal { target, .. }
            | dregg_turn::Effect::CellUnseal { target }
            | dregg_turn::Effect::CellDestroy { target, .. } => {
                require_local_cell_for_commit(ledger, target, label)?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// F-DOS-1 scoping note: this proves synchronously (the demo/CLI proof-return
/// contract — `effect_vm_proof_hex` is forwarded into the replay chain). Unlike
/// the public HTTP submit path (`api.rs`, which now revalidates inline + proves
/// async off the state-write lock), the MCP surface is **stdio-only, single-user
/// CLI** (`dregg-node mcp` reads JSON-RPC from stdin — see module docs + `main.rs`
/// `run_mcp`). There is no concurrent remote client to starve and no remote
/// attacker, so the F-DOS-1 vector (a submitted turn pins a worker under the
/// global lock while OTHER clients freeze) does not apply here. Converting this
/// to async would break the synchronous proof return the demos depend on, so the
/// proof stays inline — but it is NOT on a remote request path. The DoS fix lives
/// where the DoS lives: the HTTP submit/commit handlers.
// ⚑ DELETED 2026-07-28: `require_effect_vm_proof`. It called
// [`try_generate_effect_vm_proof`] — which returns `Err` UNCONDITIONALLY, with no `cfg`,
// because the v1 hand-AIR (`EffectVmAir`) standalone attestation is RETIRED — and turned
// the `Err` into an EARLY RETURN from the tool. It had no reachable `Ok`, so the five MCP
// tools that consulted it (`dregg_grant_capability`, `dregg_exercise_bearer_cap`,
// `dregg_exercise_handoff_cert`, and both sides of `dregg_bilateral_action`) could not
// commit AT ALL: every honest call came back `activity_status: "rejected"`, which reads
// like an authorization failure and is nothing of the kind.
//
// The refusal was never fail-closed safety, and `node/src/prove_pool.rs` settles it for
// the whole node: "Proofs are *additive attestation*, not a per-step soundness gate … the
// authoritative executor already validated the turn and committed the new state BEFORE
// this pool ever runs." A tool that refuses to commit because an ADDITIVE ATTESTATION
// cannot be produced is a dead tool. So the five tools now COMMIT and report the
// attestation truthfully — see [`attest_committed_turn`], which routes them at the SAME
// seam the HTTP submit path uses (`api::prepare_rotatable_turn` → the async prove pool,
// whose effect-vm leg proves through the LEAN-EMITTED ROTATED DESCRIPTOR; no AIR is
// authored on this path, and none may be).
//
// Making the helper return `Ok` instead would have laundered a MISSING attestation into a
// PRESENT one; the retirement is real and is reported as such.

/// The attestation disposition of a turn the MCP surface has ALREADY COMMITTED.
///
/// The executor is the soundness boundary; by the time one of these exists the state
/// transition is done and chained. This says only what became of the *attestation*, and
/// every value is a fact about a committed turn:
///
/// | `proof_status`            | means | HTTP twin ([`crate::state::ActivityProofStatus`]) |
/// |---|---|---|
/// | `attestation_pending`     | job ACCEPTED by the async prove pool; the WitnessedReceipt attaches when it lands | `proof_pending` |
/// | `attestation_unattested`  | there IS a transition to attest but no pool took it (none installed, or queue full) | `unattested` |
/// | `not_required`| own-cell event-only coordination; signature attestation, no validity proof | `not_required` |
/// | `attestation_unprovable`  | the CHECKED producer projection refuses this turn BY NAME (a verb with no AIR row, or a `SetField` key wider than the u32 index lane) | `proof_generation_failed` |
///
/// The `attestation_` prefix is deliberate: this surface used to answer `proved` (meaning
/// "standalone v1 material attached", a lane that has produced nothing since `384d0cd5a`)
/// and `v1_attestation_retired`, and no reader should confuse the two vocabularies.
#[derive(Debug)]
pub(super) struct CommittedAttestation {
    pub(super) proof_status: &'static str,
    detail: Option<String>,
}

impl CommittedAttestation {
    /// The `attestation` block every committed MCP tool response carries. It names the
    /// LEG so a caller can tell WHICH attestation it is waiting for — the rotated
    /// finalized-turn proof, not the retired standalone v1 material.
    pub(super) fn json(&self) -> serde_json::Value {
        serde_json::json!({
            "status": self.proof_status,
            "leg": "rotated-finalized-turn-proof (node/src/prove_pool.rs)",
            "detail": self.detail,
            "note": "The executor committed this turn; the attestation is ADDITIVE, and its \
                     absence is not a rejection. The retired lane is the standalone v1 \
                     EffectVmAir material — `effect_vm_proof_hex` and friends are gone from \
                     this response because that lane has no producer.",
        })
    }
}

/// Plan the committed turn's attestation. Runs UNDER the state-write lock (it reads the
/// actor cell), at the ONE seam the HTTP commit path uses — `api::prepare_rotatable_turn`
/// — so the MCP surface cannot drift into its own answer about what is attestable.
///
/// `before_cell` is the actor cell CLONED BEFORE `executor.execute` (the MCP paths arm no
/// per-turn restore-point journal, so there is no `pre_turn_touched_ledger` to read);
/// `after_cell` is the just-committed one.
pub(super) fn plan_attestation(
    turn: &Turn,
    before_cell: Option<&dregg_cell::Cell>,
    after_cell: Option<&dregg_cell::Cell>,
    receipt_hash: [u8; 32],
    turn_hash: &str,
    s: &crate::state::NodeStateInner,
) -> crate::api::HttpWitnessOutcome {
    match crate::api::prepare_turn_attestation(turn, before_cell, after_cell, receipt_hash, s) {
        Ok(outcome) => outcome,
        Err(err) => {
            tracing::warn!(
                turn_hash = %turn_hash,
                error = %err,
                "mcp: could not prepare the rotated attestation; the turn is committed and \
                 stays committed — only its attestation is missing"
            );
            crate::api::HttpWitnessOutcome::Unprovable(err)
        }
    }
}

/// Hand the planned attestation to the async prove pool and report WHAT ACTUALLY
/// HAPPENED. Must be called AFTER the state-write guard is dropped: the pool's
/// bookkeeping takes the write lock itself.
pub(super) async fn attest_committed_turn(
    state: &NodeState,
    planned: crate::api::HttpWitnessOutcome,
    receipt: dregg_turn::TurnReceipt,
    receipt_hash: [u8; 32],
    turn_hash: &str,
) -> CommittedAttestation {
    let unprovable_why = match &planned {
        crate::api::HttpWitnessOutcome::Unprovable(why) => Some(why.clone()),
        _ => None,
    };
    let (_status, pending) = planned.split(turn_hash);
    match pending {
        Some(rotatable) => {
            let enqueued = crate::api::enqueue_async_proof(
                state,
                rotatable,
                receipt,
                receipt_hash,
                turn_hash.to_string(),
            )
            .await;
            if enqueued {
                CommittedAttestation {
                    proof_status: "attestation_pending",
                    detail: None,
                }
            } else {
                CommittedAttestation {
                    proof_status: "attestation_unattested",
                    detail: Some(
                        "no async prove pool accepted the job (none installed in this \
                         process, or its bounded queue is full); the receipt is committed \
                         and unattested"
                            .to_string(),
                    ),
                }
            }
        }
        None => match unprovable_why {
            Some(why) => CommittedAttestation {
                proof_status: "attestation_unprovable",
                detail: Some(why),
            },
            None => CommittedAttestation {
                proof_status: "not_required",
                detail: Some(
                    "coordination-only turn: executor/committee attestation, not a validity proof"
                        .to_string(),
                ),
            },
        },
    }
}

/// The REJECTION VARIANT of a `TurnResult::Rejected`, derived from the enum itself.
///
/// `TurnError` is externally-tagged `Serialize`, so this is the Rust variant name and
/// nothing else — no hand-maintained table to drift, and no substring matching. A caller
/// (or a test) can tell `CapTpIntroducerKeyMismatch` from `BearerCapInvalidProof` from
/// `InsufficientBalance` without parsing prose.
///
/// ⚠ This exists because a `node/` test asserted a security property BY SUBSTRING —
/// `err.contains("rejected") || err.contains("introducer") || err.contains("invalid")` —
/// over a message that, at the time, came from the v1 retirement and never reached the
/// executor at all. Substrings cannot distinguish a forged key from a dead lane.
pub(super) fn rejection_variant(reason: &dregg_turn::TurnError) -> String {
    match serde_json::to_value(reason) {
        // Unit variants serialize as a bare string; data variants as `{Variant: {…}}`.
        Ok(serde_json::Value::String(name)) => name,
        Ok(serde_json::Value::Object(map)) => map
            .keys()
            .next()
            .cloned()
            .unwrap_or_else(|| "UnknownTurnError".to_string()),
        _ => "UnknownTurnError".to_string(),
    }
}

/// Generate an Effect VM STARK proof for a sequence of VM-domain effects.
///
/// Builds a fresh `CellState` from `(initial_balance, initial_nonce)`, runs the
/// effect VM trace generator, constructs the `EffectVmAir` sized to the effect
/// count, and produces a STARK proof. Returns the hex-encoded postcard-serialized
/// proof bytes, the public inputs converted to `u64` (BabyBear canonical
/// values fit in u32, so the JSON array is friendly to the independent verifier
/// which parses public inputs as u32), the trace as a `Vec<Vec<u32>>` for
/// scope-(2) WitnessedReceipt capture, and the BLAKE3 witness_hash of the
/// postcard-serialised `WitnessBundle::Inline` (hex-encoded) so demo scripts
/// can forward it verbatim into the on-disk replay chain.
///
/// Stage 7 / §C: returning the trace + witness_hash lets the MCP tool emit
/// scope-(2) WitnessedReceipts. The MCP layer ships these to the demo
/// scripts; the verifier-side `replay_chain` reconstructs `BabyBear` cells
/// via `BabyBear::new_canonical` and re-derives the witness_hash to check
/// the binding.
///
/// If `vm_effects` is empty, the checked helper returns an error.
///
/// ⚠ REMOVED: the `generate_effect_vm_proof` tuple wrapper that `unwrap`ed this by
/// `panic!`ing. Since the standalone v1 material was RETIRED,
/// [`try_generate_effect_vm_proof`] returns `Err` UNCONDITIONALLY — so that wrapper
/// turned every call of the four live starbridge MCP tools (`dregg_register_name`,
/// `dregg_publish_subscription`, `dregg_issue_credential`, `dregg_register_service`)
/// into a panic, AFTER the turn had already committed and gossiped, with no
/// `catch_unwind` anywhere on the stdio dispatch path. Callers now surface the refusal
/// as data.

pub(super) fn try_generate_effect_vm_proof(
    initial_balance: u64,
    initial_nonce: u64,
    vm_effects: &[dregg_circuit::effect_vm::Effect],
) -> Result<EffectVmProofMaterial, String> {
    if vm_effects.is_empty() {
        return Err("empty Effect VM projection".to_string());
    }

    // ⚑ DELETED 2026-07-28: this used to build the full effect-VM trace and PI vector,
    // write `PI[IS_AGENT_CELL] = 1` into it, and then discard all of it with
    // `let _ = (&trace, &public_inputs);` one line before the unconditional `Err` below.
    // Work whose only consumer is a discard is not a producer that happens to be off — it
    // is a shape that makes a retired lane look live to the next reader (and it carried a
    // long Issue-#72 comment justifying a PI write that bound nothing: the slot is PI 81
    // and a real rotated leg publishes 46-68 felts, so no shipped proof reaches the
    // offset). The retirement is the whole behaviour; nothing precedes it.
    let _ = (initial_balance, initial_nonce);

    // Issue #72: the verifier's `check_receipt_pi_binding` requires
    // `PI[IS_AGENT_CELL] == 1` for the v1 single-proof-per-WR shape (see
    // `verifier/src/lib.rs::check_receipt_pi_binding`). The trace generator
    // leaves this PI slot at zero because the AIR itself has no
    // constraint on IS_AGENT_CELL (it is an executor-asserted bundle tag
    // — the per-cell prover knows whether `cell_id == turn.agent`).
    //
    // For mcp-generated proofs the cell IS the agent by construction: this
    // path produces a *single* per-cell proof for the actor's own state
    // transition (grant/revoke/exercise of their own capability). So the
    // tag is always 1 here. Setting it explicitly mirrors what
    // `turn/src/executor/proof_verify.rs::populate_pi` does for the
    // executor-driven path and what `silver_helper.rs::cmd_make_recursive_witness`
    // does for the demo's witness fabrication path.
    //
    Err(
        "the standalone v1 effect-vm attestation (the `EffectVmAir` hand-AIR) is RETIRED \
         and has no producer; finalized turns prove ROTATED through the node commit pipeline"
            .to_string(),
    )
}

// =============================================================================
// JSON-RPC types
// =============================================================================

// ⚑ DELETED 2026-07-28: `schedule_projected_wr`. It projected the bilateral-schedule /
// turn-identity PI slots onto an `EffectVmProofMaterial` — the RETIRED standalone v1
// material, which `try_generate_effect_vm_proof` has never once produced. Its only caller
// was `dregg_bilateral_action`'s joint-aggregation block (`prove_aggregated_bundle` over
// two schedule-projected WRs), which therefore never ran: the tool refused several
// hundred lines earlier, on the same retirement. The per-cell v1 WR is the artifact that
// aggregator consumes and there is no producer for it; the live per-turn attestation is
// the ACTOR-cell rotated proof the async prove pool builds (see `attest_committed_turn`),
// which is not a two-sided bundle. The bilateral binding this tool still reports is the
// SCHEDULE (`ExpectedBilateral::counts_for`), which is derived from the committed turn and
// is real.

/// Ensure `cell_id` exists in the ledger. If missing, insert a default
/// hosted cell owned by the node's pubkey with zero balance. This lets
/// the executor find a cell to act on without forcing callers to
/// pre-register through a separate flow — the demo orchestrator can
/// just call the starbridge-app tools and the cells materialize on
/// first use.
///
/// Returns the (balance, nonce) pair the cell holds after the call
/// (used as the EffectVM `initial_balance`/`initial_nonce`).
pub(super) fn ensure_cell_in_ledger(
    cell_id: CellId,
    pk_bytes: [u8; 32],
    ledger: &mut dregg_cell::Ledger,
) -> (u64, u64) {
    if ledger.get(&cell_id).is_none() {
        // `Cell::with_balance` derives the cell id from
        // `(public_key, token_id)`, which only matches the agent's own
        // cell. For arbitrary caller-supplied cell ids (registry cells,
        // issuer cells, subscription cells, etc.) we use the
        // `remote_stub_with_id_pk_balance` constructor that records the
        // cell at the *specified* id while still attaching the node's
        // pubkey so signature-mode auth resolves correctly.
        let cell = dregg_cell::Cell::remote_stub_with_id_pk_balance(cell_id, pk_bytes, 0);
        // Best-effort: if insert fails we surface a zero state; the
        // executor will reject the turn downstream and the tool returns
        // the Rejected receipt.
        let _ = ledger.insert_cell(cell);
    }
    match ledger.get(&cell_id) {
        // THE EPOCH: balances are SIGNED (i64); the VM pre-state tuple is u64.
        // These are ORDINARY cells (non-negative) — checked conversion.
        Some(c) => (
            u64::try_from(c.state.balance()).unwrap_or(0),
            c.state.nonce(),
        ),
        None => (0, 0),
    }
}

/// **THE SURVIVING TOOTH — the MCP `set_field` JSON encoding.**
///
/// The four sibling tests here pinned the node-local `Effect::SetField` -> felt
/// PROJECTORS against the deployed executor bridge. Those projectors are DELETED (see
/// the tombstone at the top of this file): they fed the retired v1 attestation and
/// nothing else, so the node no longer carries a twin of
/// `AgentCipherclerk::try_convert_effects_to_vm` for them to disagree with.
///
/// What is still live, and still needs teeth, is `parse_effect_json`: the MCP JSON
/// surface must emit a field element the KERNEL can read back.
#[cfg(test)]
mod setfield_value_lane_tooth {
    use dregg_turn::Effect;

    /// The MCP JSON surface must produce a field element the KERNEL can read back.
    /// Pre-fix `{"value": 42}` became `2a000000…00`, which `field_to_u64` reads as 0.
    #[test]
    fn parse_effect_json_emits_the_canonical_field_encoding() {
        let cell_hex = "07".repeat(32);
        for v in [0u64, 42, u32::MAX as u64 + 1, u64::MAX] {
            let json = serde_json::json!({
                "type": "set_field",
                "cell": cell_hex,
                "index": 3,
                "value": v,
            });
            match super::parse_effect_json(&json).expect("set_field parses") {
                Effect::SetField { value, .. } => assert_eq!(
                    value,
                    dregg_cell::field_from_u64(v),
                    "MCP set_field must emit dregg_cell::field_from_u64({v})"
                ),
                other => panic!("expected SetField, got {other:?}"),
            }
        }
    }
}
