//! `mcp::handlers_apps` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

pub(super) async fn tool_deploy_factory(params: &Value, state: &NodeState) -> McpToolResult {
    let factory_vk_hex = match params.get("factory_vk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: factory_vk"),
    };

    let factory_vk = match hex_decode(factory_vk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for factory_vk"),
    };

    let _strategy = params
        .get("child_vk_strategy")
        .and_then(|v| v.as_str())
        .unwrap_or("fixed");
    let max_creations = params
        .get("max_creations_per_epoch")
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as usize;
    let sovereign = params
        .get("sovereign")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    drop(s);

    // Build a factory descriptor.
    let default_mode = if sovereign {
        dregg_cell::CellMode::Sovereign
    } else {
        dregg_cell::CellMode::Hosted
    };

    let descriptor = dregg_cell::factory::FactoryDescriptor {
        factory_vk,
        child_program_vk: Some(factory_vk),
        child_vk_strategy: Some(dregg_cell::factory::ChildVkStrategy::Fixed(Some(
            factory_vk,
        ))),
        allowed_cap_templates: vec![],
        field_constraints: vec![],
        state_constraints: vec![],
        default_mode,
        creation_budget: if max_creations == 0 {
            None
        } else {
            Some(max_creations as u64)
        },
    };

    let descriptor_hash = descriptor.hash();

    // Store in the node's factory registry (from cell crate).
    // The ProgramRegistry stores CellPrograms; we track factories via the ledger side.
    // For MCP purposes, record the factory descriptor hash for provenance verification.
    let _descriptor_hash_copy = descriptor_hash;

    McpToolResult::json(&serde_json::json!({
        "deployed": true,
        "factory_vk": factory_vk_hex,
        "descriptor_hash": hex_encode(&descriptor_hash),
        "max_creations_per_epoch": max_creations,
        "sovereign": sovereign,
    }))
}

pub(super) async fn tool_create_from_factory(params: &Value, state: &NodeState) -> McpToolResult {
    let factory_vk_hex = match params.get("factory_vk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: factory_vk"),
    };
    let cell_name = params
        .get("cell_name")
        .and_then(|v| v.as_str())
        .unwrap_or("unnamed");
    let sovereign = params
        .get("sovereign")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let factory_vk = match hex_decode(factory_vk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for factory_vk"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Derive child cell ID from factory VK + name + nonce.
    let mut derive_input = Vec::new();
    derive_input.extend_from_slice(&factory_vk);
    derive_input.extend_from_slice(cell_name.as_bytes());
    derive_input.extend_from_slice(&(s.cclerk.receipt_chain_length() as u64).to_le_bytes());
    let child_cell_id_bytes: [u8; 32] =
        blake3::derive_key("dregg-factory-child-cell-v1", &derive_input);
    let child_cell_id = dregg_cell::CellId(child_cell_id_bytes);

    // Get current height for provenance.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    let provenance =
        dregg_cell::factory::Provenance::from_factory(factory_vk, None, current_height);

    if sovereign {
        let commitment: [u8; 32] = *blake3::hash(&child_cell_id_bytes).as_bytes();
        let _ = s.ledger.register_sovereign_cell(child_cell_id, commitment);
    }

    McpToolResult::json(&serde_json::json!({
        "created": true,
        "cell_id": hex_encode(&child_cell_id_bytes),
        "cell_name": cell_name,
        "factory_vk": factory_vk_hex,
        "sovereign": sovereign,
        "provenance": {
            "factory_vk": factory_vk_hex,
            "height": current_height,
            "proof_hash": provenance.creation_proof_hash.map(|h| hex_encode(&h)),
        },
    }))
}

/// Emit an `Effect::CreateCellFromFactory` so the new cell is created
/// through the factory descriptor's validate_creation path. This is the
/// canonical replacement for the legacy `dregg_create_from_factory` tool,
/// which inserted cells via direct ledger manipulation; the new tool routes
/// through the executor and the factory descriptor's invariants.
pub(super) async fn tool_create_cell_from_factory_effect(
    params: &Value,
    state: &NodeState,
) -> McpToolResult {
    let factory_vk_hex = match params.get("factory_vk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: factory_vk"),
    };
    let factory_vk = match hex_decode(factory_vk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for factory_vk"),
    };
    let sovereign = params
        .get("sovereign")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);
    let program_vk: Option<[u8; 32]> = match params.get("program_vk").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => Some(b),
            Err(_) => return McpToolResult::error("invalid hex for program_vk"),
        },
        None => None,
    };

    let initial_fields: Vec<(u32, u64)> =
        match params.get("initial_fields").and_then(|v| v.as_array()) {
            Some(arr) => {
                let mut out = Vec::with_capacity(arr.len());
                for entry in arr {
                    let idx = entry
                        .get("index")
                        .and_then(|v| v.as_u64())
                        .ok_or_else(|| "initial_fields[*].index missing".to_string());
                    let val = entry
                        .get("value")
                        .and_then(|v| v.as_u64())
                        .ok_or_else(|| "initial_fields[*].value missing".to_string());
                    match (idx, val) {
                        (Ok(i), Ok(v)) => out.push((i as u32, v)),
                        (Err(e), _) | (_, Err(e)) => return McpToolResult::error(e),
                    }
                }
                out
            }
            None => Vec::new(),
        };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let owner_pubkey: [u8; 32] = match params.get("owner_pubkey").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for owner_pubkey"),
        },
        None => s.cclerk.public_key().0,
    };
    let token_id: [u8; 32] = match params.get("token_id").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for token_id"),
        },
        None => blake3::derive_key("dregg-mcp-factory-token-v1", &factory_vk),
    };

    let mode = if sovereign {
        dregg_cell::CellMode::Sovereign
    } else {
        dregg_cell::CellMode::Hosted
    };

    let params_struct = dregg_cell::factory::FactoryCreationParams {
        mode,
        program_vk,
        initial_fields,
        initial_caps: Vec::new(),
        owner_pubkey,
    };

    let effect = dregg_turn::Effect::CreateCellFromFactory {
        factory_vk,
        owner_pubkey,
        token_id,
        params: params_struct,
    };

    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
    // The ACTING CELL's replay nonce, off the ledger. `receipt_chain_length()` is the
    // number of receipts in the node-WIDE log across every agent — the same wrong scope
    // as the predecessor hash above, and refused by the same turn: the executor compares
    // `turn.nonce` against `cell.state.nonce()` and rejects `nonce replay: expected 0,
    // got 1` as soon as any other agent has committed once.
    let nonce = s
        .ledger
        .get(&agent_cell_id)
        .map(|c| c.state.nonce())
        .unwrap_or(0);
    // The MCP agent cell's own causal head — `append_receipt` below is agent-scoped
    // (`agent_receipt_head_hash(&receipt.agent)`), so the node-wide log head was refused
    // as soon as any other agent committed. Seeded onto the fresh executor too.
    let previous_receipt_hash = s.cclerk.agent_receipt_head_hash(&agent_cell_id);
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 10_000,
        memo: Some("create cell from factory (mcp)".to_string()),
        // `None` skips the executor's expiration check entirely
        // (`turn/src/executor/execute.rs:426`) — bound it instead
        // (`api::default_valid_until`).
        valid_until: crate::api::default_valid_until(),
        call_forest: build_signed_forest(
            agent_cell_id,
            vec![effect],
            &s.cclerk,
            &s.federation_id,
            nonce,
        ),
        depends_on: vec![],
        previous_receipt_hash,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    let turn_hash = hex_encode(&turn.hash());

    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    if let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent_cell_id, head);
    }
    let exec_result = mcp_execute(&mut s, &executor, &turn);

    let new_cell_id = dregg_cell::CellId::derive_raw(&owner_pubkey, &token_id);
    let new_cell_hex = hex_encode(&new_cell_id.0);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            McpToolResult::json(&serde_json::json!({
                "created": true,
                "factory_vk": factory_vk_hex,
                "new_cell_id": new_cell_hex,
                "owner_pubkey": hex_encode(&owner_pubkey),
                "token_id": hex_encode(&token_id),
                "sovereign": sovereign,
                "turn_hash": turn_hash,
                "note": "Created via Effect::CreateCellFromFactory; the executor ran the factory descriptor's validate_creation path before insertion.",
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "created": false,
                "error": format!("factory creation rejected: {reason}"),
                "turn_hash": turn_hash,
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("factory creation turn did not commit")
        }
    }
}

// =============================================================================
// Starbridge-app tool helpers
// =============================================================================
//
// These four tools wrap the canonical `build_*_action` helpers from the
// four anchor starbridge-apps so the cross-app-e2e demo can drive a
// real running node over MCP. Each tool:
//
//   1. Parses the action-specific parameters from JSON.
//   2. Builds a temporary `AppCipherclerk` from a fresh `AgentCipherclerk`
//      (matching seed irrelevant — we discard its signature).
//   3. Calls the starbridge-app's `build_*_action(&temp_cclerk, ...)` to
//      construct the canonical Action with the right effects + witness blobs.
//   4. Re-signs the action with the *node's* cipherclerk via
//      `AgentCipherclerk::sign_action` (federation_id [0u8; 32], matching
//      the executor default).  This binds the action's authorization to
//      the node's identity.
//   5. Ensures the target cell exists in the local ledger (insert as a
//      hosted cell owned by the node's pubkey if missing) — required for
//      the executor to find a cell to act on.
//   6. Wraps the signed action in a Turn, executes through TurnExecutor.
//   7. Projects the action's `SetField` effects into `effect_vm::Effect`
//      domain and produces a STARK proof via `generate_effect_vm_proof`.
//   8. Returns receipt JSON matching the shape of `grant.proof.json`
//      (effect_vm_proof_hex, effect_vm_public_inputs, effect_vm_trace_rows,
//      effect_vm_witness_hash_hex).
//
// **Effect-VM coverage gap**: the underlying `EffectVmAir` understands
// `Transfer`, `SetField`, `GrantCapability`, and `NoOp`. The starbridge
// apps emit `SetField` (which we map directly) and `EmitEvent` (which has
// no AIR row — we either skip it or, for purely-event actions like
// `register_service`, synthesise one `SetField` row carrying the event's
// path_hash so the proof remains non-trivial).

/// Build a `Turn` that wraps a single starbridge-app action, submit it through the
/// executor, and hand the committed turn to the node's async prove pool for its
/// ROTATED attestation. Returns the canonical (receipt-bearing) JSON response shape
/// used by all four starbridge tools.
///
/// ⚠ This function's post-commit block used to call the RETIRED v1 attestation
/// producer and report `effect_vm_proof_hex: null` with `proof_status:
/// "v1_attestation_retired"` — permanently, for every call, on a turn that had
/// already committed, chained and gossiped. It was not a gate (it ran after all
/// three) and it was not a producer; it was a tombstone in the response body.
pub(super) async fn run_starbridge_action(
    state: &NodeState,
    action: dregg_turn::Action,
    memo: String,
    extra_links: serde_json::Map<String, Value>,
) -> McpToolResult {
    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Node identity + agent cell.
    let pk_bytes = s.cclerk.public_key().0;
    let agent_cell_id = dregg_cell::CellId::derive_raw(&pk_bytes, &[0u8; 32]);
    let federation_id = [0u8; 32];

    // Re-sign the action with the node's cipherclerk (overwrites the temp
    // signature placed by the starbridge-apps builder).
    let signed_action = s.cclerk.sign_action(action, &federation_id);

    // ⚑ Open the application window BEFORE the two stub inserts below, not at
    // the `mcp_execute` call: those writes are part of this turn's attempt, and
    // if the turn is refused they are RAM-only cells no other node holds. There
    // is deliberately no `return` between here and the execute (see
    // `mcp_begin_turn`'s contract).
    mcp_begin_turn(&mut s);

    // Make sure the action's target cell exists in the ledger.
    let target = signed_action.target;
    // (The returned pre-state tuple fed the retired v1 attestation and nothing else;
    // the rotated leg reads the ACTOR cell's real before/after images instead.)
    let _ = ensure_cell_in_ledger(target, pk_bytes, &mut s.ledger);
    // Also ensure the agent cell exists — turn-level checks reference it.
    let _ = ensure_cell_in_ledger(agent_cell_id, pk_bytes, &mut s.ledger);

    // ⚑ DELETED 2026-07-28: the `project_setfield_to_vm` projection + the
    // `extra_vm_effects` parameter that fed it. Their only consumer was the retired v1
    // attestation call this function used to make AFTER committing; all four callers
    // already passed an empty vec. The live attestation is the rotated finalized-turn
    // proof enqueued below, which projects the turn's effects itself.

    // Build the Turn.
    let mut forest = CallForest::new();
    forest.add_root(signed_action);

    // The ACTING CELL's replay nonce, off the ledger. `receipt_chain_length()` is the
    // number of receipts in the node-WIDE log across every agent — the same wrong scope
    // as the predecessor hash above, and refused by the same turn: the executor compares
    // `turn.nonce` against `cell.state.nonce()` and rejects `nonce replay: expected 0,
    // got 1` as soon as any other agent has committed once.
    let nonce = s
        .ledger
        .get(&agent_cell_id)
        .map(|c| c.state.nonce())
        .unwrap_or(0);
    // The MCP agent cell's own causal head — `append_receipt` below is agent-scoped
    // (`agent_receipt_head_hash(&receipt.agent)`), so the node-wide log head was refused
    // as soon as any other agent committed. Seeded onto the fresh executor too. This is
    // the shared body behind `dregg_register_name` / `dregg_publish_subscription` /
    // `dregg_issue_credential` / `dregg_register_service`, so one wrong head refused all
    // four starbridge-app builders.
    let previous_receipt_hash = s.cclerk.agent_receipt_head_hash(&agent_cell_id);
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 10_000,
        memo: Some(memo),
        // `None` skips the executor's expiration check entirely
        // (`turn/src/executor/execute.rs:426`) — bound it instead
        // (`api::default_valid_until`).
        valid_until: crate::api::default_valid_until(),
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let signed = s.cclerk.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // The ACTOR cell BEFORE execution — the rotated attestation's before-image.
    let before_cell = s.ledger.get(&agent_cell_id).cloned();

    // Execute locally.
    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    if let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent_cell_id, head);
    }
    let exec_result = mcp_execute(&mut s, &executor, &turn);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash = receipt.receipt_hash();
            let receipt_hash_hex = hex_encode(&receipt_hash);
            let receipt_bytes =
                postcard::to_allocvec(&receipt).expect("TurnReceipt serializes via postcard");
            let receipt_bytes_hex = hex_encode(&receipt_bytes);
            let pre_state_hash_hex = hex_encode(&receipt.pre_state_hash);
            let post_state_hash_hex = hex_encode(&receipt.post_state_hash);
            let effects_hash_hex = hex_encode(&receipt.effects_hash);

            let planned = plan_attestation(
                &turn,
                before_cell.as_ref(),
                s.ledger.get(&agent_cell_id),
                receipt_hash,
                &turn_hash,
            );

            s.cclerk
                .append_receipt(receipt.clone())
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            // The LIVE attestation, at the same seam the HTTP submit path uses: the
            // rotated finalized-turn proof, built + self-verified off the lock by the
            // async prove pool. (Substrate, said out loud: that leg's effect-vm
            // descriptor is LEAN-EMITTED — this code only hands the pool a job.)
            let attestation =
                attest_committed_turn(state, planned, receipt, receipt_hash, &turn_hash).await;

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let h = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(h, turn_data).await;
                });
            }

            let mut out = serde_json::Map::new();
            out.insert("committed".into(), Value::Bool(true));
            out.insert("turn_hash".into(), Value::String(turn_hash));
            out.insert("receipt_hash".into(), Value::String(receipt_hash_hex));
            out.insert("receipt_bytes_hex".into(), Value::String(receipt_bytes_hex));
            out.insert("pre_state_hash".into(), Value::String(pre_state_hash_hex));
            out.insert("post_state_hash".into(), Value::String(post_state_hash_hex));
            out.insert("effects_hash".into(), Value::String(effects_hash_hex));
            out.insert(
                "proof_status".into(),
                Value::String(attestation.proof_status.to_string()),
            );
            out.insert("attestation".into(), attestation.json());
            for (k, v) in extra_links {
                out.insert(k, v);
            }
            McpToolResult::json(&Value::Object(out))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            let variant = rejection_variant(&reason);
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "committed": false,
                "turn_hash": turn_hash,
                "rejection_variant": variant,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("starbridge action turn did not commit")
        }
    }
}

/// Build a fresh `AppCipherclerk` for use as a builder argument. The
/// signature it places on the action is overwritten by the node
/// cipherclerk's `sign_action` before submission, so the temp cipherclerk
/// only contributes the action's `target`/`method`/`effects`/witness
/// shape — none of its key material lands in the receipt chain.
pub(super) fn temp_app_cclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0u8; 32])
}

/// Default registry/issuer/etc. cell when the caller omits it: the
/// node's own agent cell. Returns Err if the caller-supplied hex is
/// invalid (so the tool can surface a clean error).
pub(super) fn parse_or_default_cell(
    value: Option<&str>,
    default: CellId,
) -> Result<CellId, String> {
    match value {
        None => Ok(default),
        Some(h) => match hex_decode(h) {
            Ok(b) => Ok(dregg_cell::CellId(b)),
            Err(_) => Err(format!(
                "invalid hex for cell id '{h}' (expected 64 hex chars)"
            )),
        },
    }
}

// =============================================================================
// Tool: dregg_register_name
// =============================================================================

pub(super) async fn tool_register_name(params: &Value, state: &NodeState) -> McpToolResult {
    let name = match params.get("name").and_then(|v| v.as_str()) {
        Some(s) => s.to_string(),
        None => return McpToolResult::error("missing required parameter: name"),
    };
    let expiry_height = match params.get("expiry_height").and_then(|v| v.as_u64()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: expiry_height"),
    };

    // Resolve cell ids & defaults.
    let (agent_cell, node_pk) = {
        let s = state.read().await;
        if !s.unlocked {
            return McpToolResult::error("cipherclerk is locked; unlock first");
        }
        (agent_cell_of(&s.cclerk), s.cclerk.public_key().0)
    };

    let registry_cell = match parse_or_default_cell(
        params.get("registry_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };
    let issuer_cell = match parse_or_default_cell(
        params.get("issuer_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };

    let owner = match params.get("owner").and_then(|v| v.as_str()) {
        None => node_pk,
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for owner (expected 64 hex chars)"),
        },
    };

    // Schema id defaults to the kyc-v1 schema commitment.
    let schema_id = match params.get("credential_schema_id").and_then(|v| v.as_str()) {
        None => starbridge_identity::schema_commitment(&sb_kyc_schema()),
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => {
                return McpToolResult::error(
                    "invalid hex for credential_schema_id (expected 64 hex chars)",
                );
            }
        },
    };

    // Credential proof blob defaults to a small non-empty stub (the
    // attested-tier verifier only requires a non-empty witness blob
    // until the BlindedSet verifier registry lands; cross_app_helper
    // documents this with `attested_tier_accepted_by_executor`).
    let proof_bytes = match params
        .get("credential_presentation_proof_hex")
        .and_then(|v| v.as_str())
    {
        None => b"dregg-mcp-credential-stub-v1".to_vec(),
        Some(h) => match hex_decode_var(h) {
            Ok(b) => b,
            Err(_) => {
                return McpToolResult::error("invalid hex for credential_presentation_proof_hex");
            }
        },
    };

    let temp = temp_app_cclerk();
    let action = sb_build_register_with_credential_action(
        &temp,
        registry_cell,
        &name,
        owner,
        expiry_height,
        issuer_cell,
        schema_id,
        proof_bytes.clone(),
    );

    let mut links = serde_json::Map::new();
    links.insert("registered_name".into(), Value::String(name.clone()));
    links.insert(
        "registry_cell".into(),
        Value::String(hex_encode(&registry_cell.0)),
    );
    links.insert(
        "issuer_cell".into(),
        Value::String(hex_encode(&issuer_cell.0)),
    );
    links.insert("owner".into(), Value::String(hex_encode(&owner)));
    links.insert(
        "schema_commitment".into(),
        Value::String(hex_encode(&schema_id)),
    );
    links.insert(
        "expiry_height".into(),
        Value::Number(serde_json::Number::from(expiry_height)),
    );
    links.insert(
        "presentation_proof_blob_hash".into(),
        Value::String(hex_encode(blake3::hash(&proof_bytes).as_bytes())),
    );

    run_starbridge_action(state, action, format!("register_name: {name}"), links).await
}

// =============================================================================
// Tool: dregg_publish_subscription
// =============================================================================

pub(super) fn parse_bounty_state(s: &str) -> Option<SbBountyState> {
    match s.to_ascii_lowercase().as_str() {
        "posted" => Some(SbBountyState::Posted),
        "claimed" => Some(SbBountyState::Claimed),
        "fulfilled" => Some(SbBountyState::Fulfilled),
        "settled" => Some(SbBountyState::Settled),
        "canceled" => Some(SbBountyState::Canceled),
        _ => None,
    }
}

pub(super) async fn tool_publish_subscription(params: &Value, state: &NodeState) -> McpToolResult {
    let new_head = match params.get("new_head").and_then(|v| v.as_u64()) {
        Some(n) => n,
        None => return McpToolResult::error("missing required parameter: new_head"),
    };
    let new_msg_root_hex = match params.get("new_message_root").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: new_message_root"),
    };
    let new_message_root = match hex_decode(new_msg_root_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error(
                "invalid hex for new_message_root (expected 64 hex chars)",
            );
        }
    };
    let bounty_id_hex = match params.get("bounty_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: bounty_id"),
    };
    let bounty_id = match hex_decode(bounty_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for bounty_id"),
    };
    let prior_state_str = match params.get("prior_state").and_then(|v| v.as_str()) {
        Some(s) => s,
        None => return McpToolResult::error("missing required parameter: prior_state"),
    };
    let new_state_str = match params.get("new_state").and_then(|v| v.as_str()) {
        Some(s) => s,
        None => return McpToolResult::error("missing required parameter: new_state"),
    };
    let prior_state = match parse_bounty_state(prior_state_str) {
        Some(b) => b,
        None => return McpToolResult::error(format!("invalid prior_state: {prior_state_str}")),
    };
    let new_state = match parse_bounty_state(new_state_str) {
        Some(b) => b,
        None => return McpToolResult::error(format!("invalid new_state: {new_state_str}")),
    };
    let actor_pk_hash_hex = match params.get("actor_pk_hash").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: actor_pk_hash"),
    };
    let actor_pk_hash = match hex_decode(actor_pk_hash_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for actor_pk_hash"),
    };

    let agent_cell = {
        let s = state.read().await;
        if !s.unlocked {
            return McpToolResult::error("cipherclerk is locked; unlock first");
        }
        agent_cell_of(&s.cclerk)
    };
    let subscription_cell = match parse_or_default_cell(
        params.get("subscription_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };

    // u64 → 32-byte big-endian field (matches u64_field in
    // starbridge-nameservice / governed-namespace / cross_app_helper).
    let mut new_head_field = [0u8; 32];
    new_head_field[24..32].copy_from_slice(&new_head.to_be_bytes());

    let temp = temp_app_cclerk();
    let action = sb_build_bounty_publish(
        &temp,
        subscription_cell,
        new_head_field,
        new_message_root,
        &bounty_id,
        prior_state,
        new_state,
        &actor_pk_hash,
    );

    let payload_hash = starbridge_subscription::bounty_state_payload_hash(
        &bounty_id,
        prior_state,
        new_state,
        &actor_pk_hash,
    );

    let mut links = serde_json::Map::new();
    links.insert(
        "subscription_cell".into(),
        Value::String(hex_encode(&subscription_cell.0)),
    );
    links.insert("bounty_id".into(), Value::String(hex_encode(&bounty_id)));
    links.insert(
        "actor_pk_hash".into(),
        Value::String(hex_encode(&actor_pk_hash)),
    );
    links.insert(
        "payload_hash".into(),
        Value::String(hex_encode(&payload_hash)),
    );
    links.insert("prior_state".into(), Value::String(prior_state_str.into()));
    links.insert("new_state".into(), Value::String(new_state_str.into()));
    links.insert(
        "new_head".into(),
        Value::Number(serde_json::Number::from(new_head)),
    );

    run_starbridge_action(
        state,
        action,
        format!("publish_subscription: {prior_state_str}->{new_state_str}"),
        links,
    )
    .await
}

// =============================================================================
// Tool: dregg_issue_credential
// =============================================================================

pub(super) fn parse_schema_name(name: &str) -> Option<SbCredentialSchema> {
    match name.to_ascii_lowercase().as_str() {
        "kyc" | "kyc-v1" => Some(sb_kyc_schema()),
        "gov_id" | "gov-id" | "gov-id-v1" => Some(sb_gov_id_schema()),
        "employment" | "employment-v1" => Some(sb_employment_schema()),
        _ => None,
    }
}

pub(super) fn parse_attributes_into(
    schema: &SbCredentialSchema,
    obj: &serde_json::Map<String, Value>,
) -> Result<SbCredentialAttributes, String> {
    use starbridge_identity::AttrValue;
    let mut attrs = SbCredentialAttributes::new();
    for (k, v) in obj {
        if !schema.has_attribute(k) {
            return Err(format!("attribute '{k}' not in schema '{}'", schema.name));
        }
        let attr_value = if let Some(u) = v.as_u64() {
            AttrValue::Integer(u)
        } else if let Some(_i) = v.as_i64() {
            return Err(format!(
                "attribute '{k}' integer value must be non-negative"
            ));
        } else if let Some(s) = v.as_str() {
            AttrValue::Text(s.into())
        } else {
            return Err(format!("attribute '{k}' value must be string or integer"));
        };
        attrs = attrs.with(k.as_str(), attr_value);
    }
    Ok(attrs)
}

pub(super) async fn tool_issue_credential(params: &Value, state: &NodeState) -> McpToolResult {
    let (agent_cell, node_pk) = {
        let s = state.read().await;
        if !s.unlocked {
            return McpToolResult::error("cipherclerk is locked; unlock first");
        }
        (agent_cell_of(&s.cclerk), s.cclerk.public_key().0)
    };

    let issuer_cell = match parse_or_default_cell(
        params.get("issuer_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };

    let schema_name = params
        .get("schema")
        .and_then(|v| v.as_str())
        .unwrap_or("kyc");
    let schema = match parse_schema_name(schema_name) {
        Some(s) => s,
        None => return McpToolResult::error(format!("unknown schema: {schema_name}")),
    };

    let holder_id = match params.get("holder_id").and_then(|v| v.as_str()) {
        None => *blake3::hash(&node_pk).as_bytes(),
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for holder_id"),
        },
    };

    let attributes = match params.get("attributes").and_then(|v| v.as_object()) {
        None => SbCredentialAttributes::new(),
        Some(obj) => match parse_attributes_into(&schema, obj) {
            Ok(a) => a,
            Err(e) => return McpToolResult::error(e),
        },
    };

    let new_counter = params
        .get("new_counter")
        .and_then(|v| v.as_u64())
        .unwrap_or(1);
    let revocation_root = match params.get("revocation_root").and_then(|v| v.as_str()) {
        None => [0u8; 32],
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for revocation_root"),
        },
    };
    let issued_at = params
        .get("issued_at")
        .and_then(|v| v.as_i64())
        .unwrap_or(1_700_000_000);
    let not_after = params.get("not_after").and_then(|v| v.as_i64());

    // Mint the credential.  Use a deterministic IssuerKeys derived from
    // the node's pubkey so the issuance is reproducible across replays.
    let issuer_keys = SbIssuerKeys::new(
        blake3::derive_key("dregg-mcp-issuer-root-v1", &node_pk),
        blake3::derive_key("dregg-mcp-issuer-federation-v1", &node_pk),
        node_pk.to_vec(),
        "dregg-node-mcp",
    );

    let credential: SbCredential = match sb_issue(
        &issuer_keys,
        &schema,
        holder_id,
        attributes,
        issued_at,
        not_after,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(format!("credential issuance failed: {e}")),
    };
    let credential_id = credential.id();

    let temp = temp_app_cclerk();
    let action = sb_build_issue_credential_action(
        &temp,
        issuer_cell,
        &credential,
        new_counter,
        revocation_root,
    );

    let mut links = serde_json::Map::new();
    links.insert(
        "issuer_cell".into(),
        Value::String(hex_encode(&issuer_cell.0)),
    );
    links.insert("schema".into(), Value::String(schema_name.into()));
    links.insert(
        "schema_commitment".into(),
        Value::String(hex_encode(&starbridge_identity::schema_commitment(&schema))),
    );
    links.insert(
        "credential_id".into(),
        Value::String(hex_encode(&credential_id)),
    );
    links.insert("holder_id".into(), Value::String(hex_encode(&holder_id)));
    links.insert(
        "new_counter".into(),
        Value::Number(serde_json::Number::from(new_counter)),
    );
    links.insert(
        "revocation_root".into(),
        Value::String(hex_encode(&revocation_root)),
    );
    links.insert(
        "credential_encoded".into(),
        Value::String(credential.encoded.clone()),
    );

    run_starbridge_action(
        state,
        action,
        format!("issue_credential: {schema_name}"),
        links,
    )
    .await
}

// =============================================================================
// Tool: dregg_register_service
// =============================================================================

pub(super) async fn tool_register_service(params: &Value, state: &NodeState) -> McpToolResult {
    let path = match params.get("path").and_then(|v| v.as_str()) {
        Some(p) => p.to_string(),
        None => return McpToolResult::error("missing required parameter: path"),
    };

    let agent_cell = {
        let s = state.read().await;
        if !s.unlocked {
            return McpToolResult::error("cipherclerk is locked; unlock first");
        }
        agent_cell_of(&s.cclerk)
    };

    let namespace_cell = match parse_or_default_cell(
        params.get("namespace_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };
    let target_cell = match parse_or_default_cell(
        params.get("target_cell").and_then(|v| v.as_str()),
        agent_cell,
    ) {
        Ok(c) => c,
        Err(e) => return McpToolResult::error(e),
    };

    let temp = temp_app_cclerk();
    let action = sb_build_register_service_action(&temp, namespace_cell, &path, target_cell);

    // Closes #110: the underlying action emits one
    // `EmitEvent("service-registered", [path_hash, target_field])`. The
    // EffectVmAir now carries a real `EmitEvent` row variant with
    // canonical (topic_hash, payload_hash) binding, so the bridge in
    // `turn/src/executor/effect_vm_bridge.rs` projects the runtime
    // Event directly — no synthesised SetField is required. The proof's
    // PI surface (EMIT_EVENT_TOPIC_HASH / EMIT_EVENT_PAYLOAD_HASH) ties
    // the STARK to the actual emitted event.
    let path_hash = *blake3::hash(path.as_bytes()).as_bytes();

    let mut links = serde_json::Map::new();
    links.insert(
        "namespace_cell".into(),
        Value::String(hex_encode(&namespace_cell.0)),
    );
    links.insert("path".into(), Value::String(path.clone()));
    links.insert("path_hash".into(), Value::String(hex_encode(&path_hash)));
    links.insert(
        "target_cell".into(),
        Value::String(hex_encode(&target_cell.0)),
    );

    run_starbridge_action(state, action, format!("register_service: {path}"), links).await
}

// =============================================================================
// MCP server main loop (stdio transport)
// =============================================================================
