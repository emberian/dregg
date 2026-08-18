//! `mcp::handlers_delegate` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

pub(super) async fn tool_grant_capability(params: &Value, state: &NodeState) -> McpToolResult {
    let to_agent_hex = match params.get("to_agent").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_agent"),
    };
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let permissions = match params.get("permissions").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: permissions"),
    };

    let to_agent_bytes = match hex_decode(to_agent_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to_agent (expected 64 hex chars)"),
    };
    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error("invalid hex for target_cell (expected 64 hex chars)");
        }
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Build a turn with Effect::GrantCapability.
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
    let to_cell_id = dregg_cell::CellId(to_agent_bytes);
    let target_cell_id = dregg_cell::CellId(target_cell_bytes);

    // Parse permissions string into AuthRequired level.
    let perm_level = match permissions {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permission type: '{}'. Valid: none, signature, proof, either",
                other
            ));
        }
    };

    let cap = dregg_cell::CapabilityRef {
        target: target_cell_id,
        slot: 0,
        permissions: perm_level,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
        provenance: dregg_cell::derivation::cap_provenance(
            &(target_cell_id),
            (0),
            &dregg_cell::derivation::mint_provenance(),
            &[0u8; 32],
        ),
    };
    let effect = dregg_turn::Effect::GrantCapability {
        from: agent_cell_id,
        to: to_cell_id,
        cap,
    };
    if let Err(result) = require_effect_cells_for_commit(
        &s.ledger,
        std::slice::from_ref(&effect),
        "grant capability",
    ) {
        return result;
    }

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
        // Cover the executor's computron metering for an Action-base + one
        // GrantCapability effect (~100 + 50 computrons by default; round up).
        fee: 10_000,
        memo: Some(format!("grant capability: {permissions}")),
        // `None` skips the executor's expiration check entirely
        // (`turn/src/executor/execute.rs:426`) — bound it instead
        // (`api::default_valid_until`).
        valid_until: crate::api::default_valid_until(),
        // Use a signed action so the cell's `delegate: Signature` permission
        // accepts it. (Hosted-cell grants require the cell owner's signature.)
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

    let signed = s.cclerk.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // The ACTOR cell as it stands BEFORE execution — the rotated attestation's
    // before-image (`api::prepare_rotatable_turn`). One cell, cloned; the MCP paths
    // arm no per-turn restore-point journal, so this is the whole pre-state the
    // attestation needs.
    let before_cell = s.ledger.get(&agent_cell_id).cloned();

    // Execute locally. ⚑ THE COMMIT IS NOT GATED ON AN ATTESTATION. This used to call
    // `require_effect_vm_proof` HERE, before executing, and return its refusal — and
    // that helper had no reachable `Ok`, so this tool could not commit at all.
    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    if let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent_cell_id, head);
    }
    let exec_result = mcp_execute(&mut s, &executor, &turn);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash = receipt.receipt_hash();
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

            let attestation =
                attest_committed_turn(state, planned, receipt, receipt_hash, &turn_hash).await;

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "activity_status": "committed",
                "proof_status": attestation.proof_status,
                "attestation": attestation.json(),
                "granted": true,
                "to_agent": to_agent_hex,
                "target_cell": target_cell_hex,
                "permissions": permissions,
                "turn_hash": turn_hash,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            let variant = rejection_variant(&reason);
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "rejection_variant": variant,
                "granted": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "granted": false,
                "error": "grant capability turn did not commit",
            }))
        }
    }
}

pub(super) async fn tool_revoke_capability(params: &Value, state: &NodeState) -> McpToolResult {
    let cap_slot = match params.get("cap_slot").and_then(|v| v.as_u64()) {
        Some(s) => s as u32,
        None => return McpToolResult::error("missing required parameter: cap_slot"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Build a turn with Effect::RevokeCapability targeting the agent's own cell.
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);

    let effect = dregg_turn::Effect::RevokeCapability {
        cell: agent_cell_id,
        slot: cap_slot,
    };

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
        fee: 0,
        memo: Some(format!("revoke capability slot {cap_slot}")),
        // `None` skips the executor's expiration check entirely
        // (`turn/src/executor/execute.rs:426`) — bound it instead
        // (`api::default_valid_until`).
        valid_until: crate::api::default_valid_until(),
        call_forest: build_forest_with_effects(agent_cell_id, vec![effect]),
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

    // Execute locally.
    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    if let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent_cell_id, head);
    }
    let exec_result = mcp_execute(&mut s, &executor, &turn);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "revoked": true,
                "cap_slot": cap_slot,
                "turn_hash": turn_hash,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "revoked": false,
                "cap_slot": cap_slot,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("revoke capability turn did not commit")
        }
    }
}

pub(super) async fn tool_delegate(params: &Value, state: &NodeState) -> McpToolResult {
    let capability = match params.get("capability").and_then(|v| v.as_u64()) {
        Some(c) => c as usize,
        None => return McpToolResult::error("missing required parameter: capability"),
    };
    let to_agent_hex = match params.get("to_agent").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_agent"),
    };

    let to_agent_bytes = match hex_decode(to_agent_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to_agent (expected 64 hex chars)"),
    };

    // Parse optional restrictions into an Attenuation.
    let restrictions: Attenuation = params
        .get("restrictions")
        .and_then(|v| serde_json::from_value(v.clone()).ok())
        .unwrap_or_default();

    let max_staleness = params
        .get("max_staleness")
        .and_then(|v| v.as_u64())
        .unwrap_or(1000);

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let tokens = s.cclerk.tokens();
    if capability >= tokens.len() {
        return McpToolResult::error(format!(
            "capability slot {} out of range (have {} tokens)",
            capability,
            tokens.len()
        ));
    }

    // Perform the token-level delegation (attenuate + produce DelegatedToken).
    let token = tokens[capability].clone();
    let to_pubkey = PublicKey(to_agent_bytes);
    let delegated = match s.cclerk.delegate(&token, &to_pubkey, &restrictions) {
        Ok(d) => d,
        Err(e) => return McpToolResult::error(format!("delegation failed: {e}")),
    };

    // Build a turn with Effect::GrantCapability to record the delegation on-ledger.
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
    let to_cell_id = dregg_cell::CellId(to_agent_bytes);

    let cap = dregg_cell::CapabilityRef {
        target: agent_cell_id,
        slot: capability as u32,
        permissions: dregg_cell::AuthRequired::Signature,
        breadstuff: None,
        expires_at: restrictions.not_after.map(|t| t as u64),
        allowed_effects: None,
        stored_epoch: None,
        provenance: dregg_cell::derivation::cap_provenance(
            &(agent_cell_id),
            (capability as u32),
            &dregg_cell::derivation::mint_provenance(),
            &[0u8; 32],
        ),
    };

    let effect = dregg_turn::Effect::GrantCapability {
        from: agent_cell_id,
        to: to_cell_id,
        cap,
    };

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
        fee: 0,
        memo: Some(format!(
            "delegate capability slot {} to {}",
            capability, to_agent_hex
        )),
        // `None` skips the executor's expiration check entirely
        // (`turn/src/executor/execute.rs:426`) — bound it instead
        // (`api::default_valid_until`).
        valid_until: crate::api::default_valid_until(),
        call_forest: build_forest_with_effects(agent_cell_id, vec![effect]),
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

    // Execute locally.
    let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    if let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent_cell_id, head);
    }
    let exec_result = mcp_execute(&mut s, &executor, &turn);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "delegated": true,
                "from_token": delegated.id,
                "to_agent": to_agent_hex,
                "turn_hash": turn_hash,
                "max_staleness": max_staleness,
                "token_bytes": delegated.token_bytes,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "delegated": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("delegation turn did not commit")
        }
    }
}

pub(super) async fn tool_create_bearer_cap(params: &Value, state: &NodeState) -> McpToolResult {
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let permissions_str = match params.get("permissions").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: permissions"),
    };
    let expires_at = match params.get("expires_at").and_then(|v| v.as_u64()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: expires_at"),
    };
    let bearer_pk_hex = match params.get("bearer_pk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: bearer_pk"),
    };

    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for target_cell"),
    };
    let bearer_pk_bytes = match hex_decode(bearer_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for bearer_pk"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let perm_level = match permissions_str {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permission type: '{}'. Valid: none, signature, proof, either",
                other
            ));
        }
    };

    // F-P1-8: bind `perm_level` into the signed message. Prior code computed
    // `perm_level` but discarded it (the variable was named `_perm_level`), so
    // the resulting signature did not commit to which permission level was
    // delegated — a downstream exerciser could claim any permission level.
    let perm_tag: u8 = match perm_level {
        dregg_cell::AuthRequired::None => 0,
        dregg_cell::AuthRequired::Signature => 1,
        dregg_cell::AuthRequired::Proof => 2,
        dregg_cell::AuthRequired::Either => 3,
        // Future-proof: any other variant is rejected with a tag the verifier
        // will not accept.
        _ => 0xff,
    };

    // Sign the bearer cap delegation chain using the SAME canonical message
    // format the executor's verify_bearer_cap recomputes via
    // TurnExecutor::compute_bearer_delegation_message — domain-separated,
    // federation-bound, with the perm-byte after the perm-AuthRequired
    // mapping (not the perm_tag from this tool's local lookup). Without
    // this match, every exercise turn fails with "delegation signature
    // verification failed" even though the signing key is correct.
    let target_cell_arr: [u8; 32] = target_cell_bytes.try_into().expect("32-byte cell id");
    let bearer_pk_arr: [u8; 32] = bearer_pk_bytes.try_into().expect("32-byte bearer pk");
    let perm_auth_required = match perm_tag {
        0 => dregg_cell::AuthRequired::None,
        1 => dregg_cell::AuthRequired::Signature,
        2 => dregg_cell::AuthRequired::Proof,
        3 => dregg_cell::AuthRequired::Either,
        _ => dregg_cell::AuthRequired::Impossible,
    };
    let federation_id = s.federation_id;
    let msg = dregg_turn::TurnExecutor::compute_bearer_delegation_message(
        &dregg_cell::CellId(target_cell_arr),
        &perm_auth_required,
        &bearer_pk_arr,
        expires_at,
        &federation_id,
    );
    let signing_key = s.cclerk.gossip_signing_key();
    let signature = dregg_types::sign(&signing_key, &msg);

    let bearer_cap_id = blake3::hash(&signature.0);

    McpToolResult::json(&serde_json::json!({
        "created": true,
        "bearer_cap_id": hex_encode(bearer_cap_id.as_bytes()),
        "target_cell": target_cell_hex,
        "bearer_pk": bearer_pk_hex,
        "permissions": permissions_str,
        "expires_at": expires_at,
        "delegation_chain": hex_encode(&signature.0),
        "note": "Bearer cap created. Share the delegation_chain with the bearer to exercise."
    }))
}

pub(super) async fn tool_exercise_bearer_cap(params: &Value, state: &NodeState) -> McpToolResult {
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let method = match params.get("method").and_then(|v| v.as_str()) {
        Some(m) => m,
        None => return McpToolResult::error("missing required parameter: method"),
    };
    let delegation_chain_hex = match params.get("delegation_chain").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: delegation_chain"),
    };
    let bearer_pk_hex = match params.get("bearer_pk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: bearer_pk"),
    };
    let expires_at = match params.get("expires_at").and_then(|v| v.as_u64()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: expires_at"),
    };
    // F-P1-8: accept caller-supplied permissions. Default to Signature for
    // backward compat. The signed delegation message commits to this tag in
    // `tool_create_bearer_cap`, so a downstream verifier checks the binding.
    let permissions_str = params
        .get("permissions")
        .and_then(|v| v.as_str())
        .unwrap_or("signature");
    let permissions = match permissions_str {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permission type: '{}'. Valid: none, signature, proof, either",
                other
            ));
        }
    };

    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for target_cell"),
    };
    let bearer_pk_bytes = match hex_decode(bearer_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for bearer_pk"),
    };
    let delegation_chain_bytes = match hex_decode_var(delegation_chain_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for delegation_chain"),
    };

    // Parse optional effects array. The brief specifies the bearer-cap turn
    // should be able to carry effects so the bearer can actually act through
    // the delegation. Empty / missing falls back to the prior empty-effects
    // behavior so existing callers aren't broken.
    let parsed_effects: Vec<dregg_turn::Effect> =
        match params.get("effects").and_then(|v| v.as_array()) {
            Some(arr) => {
                let mut out = Vec::with_capacity(arr.len());
                for ev in arr {
                    match parse_effect_json(ev) {
                        Ok(e) => out.push(e),
                        Err(msg) => return McpToolResult::error(format!("invalid effect: {msg}")),
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
    let federation_id = s.federation_id;

    // Check expiry against current height.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    if current_height > expires_at {
        return McpToolResult::json(&serde_json::json!({
            "exercised": false,
            "error": format!("bearer cap expired: current_height={current_height}, expires_at={expires_at}"),
        }));
    }

    // Build a turn using Bearer authorization.
    let target_cell_id = dregg_cell::CellId(target_cell_bytes);
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);

    // The delegator_pk is the introducer (the cell owner who signed the
    // bearer cap), NOT this node's cipherclerk. Accept it as a parameter; fall
    // back to this cipherclerk's pk for the (rare) self-delegation case.
    // (Parsed early so the stub-insertion below can pair the delegator's pk
    // with the target cell stub — without that pairing, the executor's
    // bearer-cap verify walks the ledger by pk and finds nothing.)
    let delegator_pk: [u8; 32] = match params.get("delegator_pk").and_then(|v| v.as_str()) {
        Some(hex) => match hex_decode(hex) {
            Ok(b) => b,
            Err(_) => {
                return McpToolResult::error(
                    "invalid hex for delegator_pk (expected 64 hex chars)",
                );
            }
        },
        None => s.cclerk.public_key().0,
    };

    if let Err(result) =
        require_local_cell_for_commit(&s.ledger, &target_cell_id, "bearer cap exercise target")
    {
        return result;
    }
    if let Err(result) =
        require_effect_cells_for_commit(&s.ledger, &parsed_effects, "bearer cap exercise")
    {
        return result;
    }

    // Construct the delegation proof data. Use the first 32 bytes as delegator_pk,
    // the full bytes as the signature, and the bearer_pk from params.
    let mut sig_array = [0u8; 64];
    let copy_len = delegation_chain_bytes.len().min(64);
    sig_array[..copy_len].copy_from_slice(&delegation_chain_bytes[..copy_len]);

    let bearer_proof = dregg_turn::BearerCapProof {
        target: target_cell_id,
        // F-P1-8: use the caller-supplied permission level (or Signature default).
        permissions,
        delegation_proof: dregg_turn::DelegationProofData::SignedDelegation {
            delegator_pk,
            signature: sig_array,
            bearer_pk: bearer_pk_bytes,
        },
        expires_at,
        revocation_channel: None,
        allowed_effects: None,
    };

    let action = dregg_turn::Action {
        target: target_cell_id,
        method: dregg_turn::action::symbol(method),
        args: vec![],
        authorization: dregg_turn::Authorization::Bearer(bearer_proof),
        preconditions: dregg_cell::Preconditions::default(),
        effects: parsed_effects.clone(),
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

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
        // Cover Action-base + per-effect cost for the parsed effects.
        fee: 10_000,
        memo: Some(format!("bearer cap exercise: {method}")),
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

    let turn_hash = hex_encode(&turn.hash());

    // The ACTOR cell BEFORE execution — the rotated attestation's before-image. The
    // "agent" view is the one the bearer operates as on this node (the exerciser of
    // the cap).
    let before_cell = s.ledger.get(&agent_cell_id).cloned();

    // Execute locally. ⚑ THE COMMIT IS NOT GATED ON AN ATTESTATION: this used to call
    // `require_effect_vm_proof` first and return its refusal, and that helper has no
    // reachable `Ok` — so an honest bearer-cap exercise carrying ANY effect could not
    // commit, while one carrying NO effects sailed through (the `vm_effects.is_empty()`
    // arm). The gate fired on exactly the calls that did something.
    let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    executor.set_local_federation_id(federation_id);
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());
    if let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent_cell_id, head);
    }
    let exec_result = mcp_execute(&mut s, &executor, &turn);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash = receipt.receipt_hash();
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
            drop(s);

            let attestation =
                attest_committed_turn(state, planned, receipt, receipt_hash, &turn_hash).await;

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            McpToolResult::json(&serde_json::json!({
                "activity_status": "committed",
                "proof_status": attestation.proof_status,
                "attestation": attestation.json(),
                "exercised": true,
                "target_cell": target_cell_hex,
                "method": method,
                "turn_hash": turn_hash,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            let variant = rejection_variant(&reason);
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "rejection_variant": variant,
                "exercised": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "exercised": false,
                "error": "bearer cap turn did not commit",
            }))
        }
    }
}

// =============================================================================
// Factory tools
// =============================================================================

/// Propose a live membership change on the RUNNING node — the MCP twin of
/// `POST /epoch/propose-transition`.
///
/// ⚑ THIS TOOL USED TO AUTHOR NOTHING AND SAY IT HAD. It built a
/// `MembershipProposal` into `_proposal`, discarded it, BLAKE3'd
/// `(action, participant)` into a `proposal_id` naming an object that did not
/// exist, and answered `"proposed": true` with the note "Proposal submitted.
/// Requires quorum votes from current participants to take effect." No block
/// was authored, nothing was broadcast, no committee ever saw it, and the
/// caller had a hex id to poll for a proposal that was never made.
///
/// It now calls the same `BlocklaceHandle::propose_membership` the HTTP route
/// does, and returns the REAL authored block id. Every way that call can fail —
/// no consensus handle, a candidate with no published ML-DSA-65 key (which
/// would author a wedge), an F2 durable-persist rollback — comes back as an
/// error carrying ITS OWN diagnosis. A refusal must never render as the
/// expected verdict.
///
/// `reason` is gone rather than ignored: `MembershipAction` carries the node id
/// and the PQ key and has no justification field, so an accepted-and-dropped
/// free-text argument is a promise the chain does not keep.
pub(super) async fn tool_propose_membership(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let add = match action {
        "join" => true,
        "leave" => false,
        other => {
            return McpToolResult::error(format!(
                "invalid action: '{other}'. Use 'join' or 'leave'"
            ));
        }
    };
    let participant_hex = match params.get("participant").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: participant"),
    };
    // A short key was silently accepted before, because nothing downstream ever
    // used the bytes.
    let participant: [u8; 32] = match hex_decode(participant_hex)
        .ok()
        .and_then(|b| <[u8; 32]>::try_from(b.as_slice()).ok())
    {
        Some(k) => k,
        None => {
            return McpToolResult::error(
                "invalid participant: expected exactly 64 hex chars (a 32-byte ed25519 public key)",
            );
        }
    };

    {
        let s = state.read().await;
        if !s.unlocked {
            return McpToolResult::error("cipherclerk is locked; unlock first");
        }
        if !s.federation_configured {
            return McpToolResult::error(
                "federation not configured; cannot propose membership changes",
            );
        }
    }

    // Dropped before `propose_membership`, which takes the state lock itself.
    let Some(blocklace) = state.blocklace().await else {
        return McpToolResult::error(
            "node is not running blocklace consensus (no committee to reconfigure) — nothing was \
             proposed",
        );
    };

    match blocklace.propose_membership(state, participant, add).await {
        Ok(block_id) => {
            let (committee_size, threshold) = {
                let c = blocklace.constitution.read().await;
                (c.current.participant_count(), c.threshold())
            };
            McpToolResult::json(&serde_json::json!({
                "proposed": true,
                // The id of the block that was actually authored, self-voted,
                // persisted and disseminated — not a hash of the arguments.
                "proposal_block": hex_encode(&block_id.0),
                "action": action,
                "participant": participant_hex,
                "committee_size": committee_size,
                "threshold": threshold,
                "note": "Proposal authored and disseminated. Proposing is not authority: it \
                         APPLIES only once a quorum of the CURRENT committee ratifies it through \
                         finality."
            }))
        }
        Err(reason) => McpToolResult::error(format!(
            "membership proposal REFUSED — nothing was authored or broadcast: {reason}"
        )),
    }
}

// =============================================================================
// Shared Resource tools
// =============================================================================

/// Exercise a CapTP HandoffCertificate via `Authorization::CapTpDelivered`.
///
/// Unlike `tool_captp_deliver` (which generates a fresh cert entirely in-process),
/// this tool models the *recipient* exercising a cert they received from a third-party
/// introducer. The caller supplies introducer identity (sk or pk), optional downstream
/// effects, and optionally a pre-built cert hash (if omitted we BLAKE3 the serialised
/// cert). The `Authorization::CapTpDelivered` carries the cert; the executor verifies
/// the introducer signature + the recipient's delivery signature. A STARK proof is
/// generated over the downstream effects (or a NoOp if none) so the receipt chain
/// carries verifiable provenance.
pub(super) async fn tool_exercise_handoff_cert(params: &Value, state: &NodeState) -> McpToolResult {
    // ── Parse required inputs ────────────────────────────────────────────────
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for target_cell"),
    };

    // ── Permissions ──────────────────────────────────────────────────────────
    let permissions_str = params
        .get("permissions")
        .and_then(|v| v.as_str())
        .unwrap_or("signature");
    let permissions = match permissions_str {
        "none" | "None" => dregg_cell::AuthRequired::None,
        "signature" | "Signature" => dregg_cell::AuthRequired::Signature,
        "proof" | "Proof" => dregg_cell::AuthRequired::Proof,
        "either" | "Either" => dregg_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permissions: '{other}' (none|signature|proof|either)"
            ));
        }
    };

    // ── Swiss number ─────────────────────────────────────────────────────────
    let swiss: [u8; 32] = match params.get("swiss").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for swiss"),
        },
        None => {
            let mut s = [0u8; 32];
            if getrandom::fill(&mut s).is_err() {
                return McpToolResult::error("failed to generate swiss");
            }
            s
        }
    };

    // ── Expiry ───────────────────────────────────────────────────────────────
    let expires_at = params.get("expires_at").and_then(|v| v.as_u64());

    // ── Target federation ────────────────────────────────────────────────────
    let target_federation_bytes: [u8; 32] =
        match params.get("target_federation").and_then(|v| v.as_str()) {
            Some(h) => match hex_decode(h) {
                Ok(b) => b,
                Err(_) => return McpToolResult::error("invalid hex for target_federation"),
            },
            None => [0u8; 32],
        };
    let target_federation = dregg_types::FederationId(target_federation_bytes);

    // ── Introducer key ───────────────────────────────────────────────────────
    // If introducer_sk is supplied, derive pk from it (testing path).
    // Otherwise, if introducer_pk is supplied, use it directly and construct
    // a cert using a fresh ephemeral signing key whose pk matches (not possible
    // without the sk — so we must require either sk or accept an ephemeral key
    // when only pk is given, and the sig won't verify against that pk).
    // Simplest contract: if sk supplied → use it; else generate fresh ephemeral.
    let introducer_sk = match params.get("introducer_sk").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => dregg_types::SigningKey::from_bytes(&b),
            Err(_) => return McpToolResult::error("invalid hex for introducer_sk"),
        },
        None => {
            // Caller may supply an explicit introducer_pk for the non-sk path;
            // we cannot create a valid cert in that case (we don't hold the sk).
            // Generate an ephemeral key so the cert's signature is consistent —
            // test adversarial paths via mismatched introducer_pk below.
            let mut seed = [0u8; 32];
            if getrandom::fill(&mut seed).is_err() {
                return McpToolResult::error("failed to generate introducer seed");
            }
            dregg_types::SigningKey::from_bytes(&seed)
        }
    };
    let introducer_pk_bytes: [u8; 32] = *introducer_sk.public_key().as_bytes();

    // Allow caller to override the introducer_pk that ends up on the Action
    // (distinct from the cert's introducer field). Used only in adversarial
    // tests — the executor rejects when the override does not match the cert's
    // `introducer.0`, with `TurnError::CapTpIntroducerKeyMismatch`.
    //
    // ⚠ This sentence was FALSE until 2026-07-28. It named a comparison
    // `verify_captp_delivered` did not perform: the executor verified the cert's
    // signature under whatever pk the Action carried and never asked whether that key
    // WAS `cert.introducer`. An override therefore failed only when the SIGNATURE
    // failed — so a presenter holding the introducer sk could name any federation at all
    // and be attributed to it. The binding now exists (`authorize.rs` step 3b).
    // When absent, use the sk-derived pk (honest path).
    let action_introducer_pk_bytes: [u8; 32] =
        match params.get("introducer_pk").and_then(|v| v.as_str()) {
            Some(h) => match hex_decode(h) {
                Ok(b) => b,
                Err(_) => return McpToolResult::error("invalid hex for introducer_pk"),
            },
            None => introducer_pk_bytes,
        };

    // ── Introducer federation ────────────────────────────────────────────────
    // The canonical convention (captp/src/handoff.rs `setup_introducer`) is
    // `FederationId(pk.0)` — the federation id IS the introducer's raw Ed25519
    // public key bytes. The executor's `verify_captp_delivered` step 3b enforces
    // `action.introducer_pk == cert.introducer.0` (and `dregg_captp::validate_handoff`
    // step 1b enforces the same on the cross-vat path), so we must pass the raw pk
    // as the default federation, not its hash.
    let introducer_federation_bytes: [u8; 32] =
        match params.get("introducer_federation").and_then(|v| v.as_str()) {
            Some(h) => match hex_decode(h) {
                Ok(b) => b,
                Err(_) => return McpToolResult::error("invalid hex for introducer_federation"),
            },
            None => introducer_pk_bytes, // FederationId = raw pk bytes (canonical convention)
        };
    let introducer_federation = dregg_types::FederationId(introducer_federation_bytes);

    // ── Optional downstream effects ──────────────────────────────────────────
    let downstream_effects: Vec<dregg_turn::Effect> =
        match params.get("effects").and_then(|v| v.as_array()) {
            Some(arr) => {
                let mut out = Vec::with_capacity(arr.len());
                for ev in arr {
                    match parse_effect_json(ev) {
                        Ok(e) => out.push(e),
                        Err(msg) => return McpToolResult::error(format!("invalid effect: {msg}")),
                    }
                }
                out
            }
            None => Vec::new(),
        };

    // ── Acquire state ────────────────────────────────────────────────────────
    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let recipient_pk: [u8; 32] = match params.get("recipient_pk").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for recipient_pk"),
        },
        None => s.cclerk.public_key().0,
    };
    let target_cell_id = dregg_cell::CellId(target_cell_bytes);
    let target_cell_captp = dregg_types::CellId(target_cell_bytes);

    // ── Create HandoffCertificate ─────────────────────────────────────────────
    let cert = dregg_captp::HandoffCertificate::create(
        &introducer_sk,
        introducer_federation,
        target_federation,
        target_cell_captp,
        recipient_pk,
        permissions,
        None,
        expires_at,
        None,
        swiss,
    );

    // Derive cert_hash: BLAKE3 over the serialised cert bytes (mirrors
    // wire/src/server.rs line 3060: `blake3::hash(&presentation_bytes).into()`).
    let cert_bytes = cert.to_bytes();
    let cert_hash: [u8; 32] = blake3::hash(&cert_bytes).into();
    let cert_nonce_hex = hex_encode(&cert.nonce);

    // VERB-LOCKSTEP: the ValidateHandoff kernel verb is gone (caps-in-slots /
    // R7 epoch-at-retrieval is the stored-authority story). The CapTpDelivered
    // AUTHORIZATION carries the cert + delivery signature; the turn carries the
    // downstream effects directly.
    let all_effects = downstream_effects.clone();

    // ── Sender signature (recipient signs the canonical delivery message) ─────
    let agent_cell_id = target_cell_id;
    // The ACTING CELL's replay nonce, off the ledger. `receipt_chain_length()` is the
    // number of receipts in the node-WIDE log across every agent — the same wrong scope
    // as the predecessor hash above, and refused by the same turn: the executor compares
    // `turn.nonce` against `cell.state.nonce()` and rejects `nonce replay: expected 0,
    // got 1` as soon as any other agent has committed once.
    let turn_nonce = s
        .ledger
        .get(&agent_cell_id)
        .map(|c| c.state.nonce())
        .unwrap_or(0);
    let federation_id = s.federation_id;
    let signing_msg = dregg_turn::Authorization::captp_delivered_signing_message_for_federation(
        &federation_id,
        &cert.nonce,
        &agent_cell_id,
        &target_cell_id,
        turn_nonce,
        &all_effects,
    );
    let recipient_signature = dregg_types::sign(&s.cclerk.gossip_signing_key(), &signing_msg);

    if s.ledger.get(&target_cell_id).is_none() {
        return McpToolResult::json(&serde_json::json!({
            "activity_status": "rejected",
            "proof_status": "missing_pre_state",
            "exercised": false,
            "target_cell": target_cell_hex,
            "error": format!("handoff cert exercise: target cell {} is not in the local ledger; refusing to synthesize a stub for a turn that would mutate it", target_cell_hex),
        }));
    }
    if let Err(result) = require_effect_cells_for_commit(
        &s.ledger,
        &downstream_effects,
        "handoff cert exercise downstream effect",
    ) {
        return result;
    }

    // ── The ACTOR cell before execution (the rotated attestation's before-image) ──
    let before_cell = s.ledger.get(&agent_cell_id).cloned();

    // ── Build and execute the Turn ────────────────────────────────────────────
    // ⚑ THE COMMIT IS NOT GATED ON AN ATTESTATION. `require_effect_vm_proof` stood
    // here and refused unconditionally, so `dregg_exercise_handoff_cert` returned
    // `exercised: false` for EVERY call — including the honest one — and the
    // executor's CapTp authorization checks were never reached at all. A `node/`
    // test read that refusal as proof that a FORGED introducer key was rejected.
    let action = dregg_turn::Action {
        target: target_cell_id,
        method: dregg_turn::action::symbol("captp.route"),
        args: vec![],
        authorization: dregg_turn::Authorization::CapTpDelivered {
            handoff_cert: cert,
            introducer_pk: action_introducer_pk_bytes,
            sender_pk: recipient_pk,
            sender_signature: recipient_signature.0,
        },
        preconditions: dregg_cell::Preconditions::default(),
        effects: all_effects.clone(),
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: dregg_turn::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

    // Here the turn's agent is the HANDOFF TARGET cell (`agent_cell_id = target_cell_id`
    // above), not the node operator, so the wide log head and this agent's causal head
    // are different questions with different answers. `append_receipt` asks the second.
    // Seeded onto the fresh executor too.
    let previous_receipt_hash = s.cclerk.agent_receipt_head_hash(&agent_cell_id);
    let turn = Turn {
        agent: agent_cell_id,
        nonce: turn_nonce,
        fee: 10_000,
        memo: Some("captp.handoff-cert-exercise (mcp)".to_string()),
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
    let turn_hash = hex_encode(&turn.hash());

    let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
    executor.set_local_federation_id(federation_id);
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());
    if let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent_cell_id, head);
    }
    let exec_result = mcp_execute(&mut s, &executor, &turn);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash = receipt.receipt_hash();
            let planned = plan_attestation(
                &turn,
                before_cell.as_ref(),
                s.ledger.get(&agent_cell_id),
                receipt_hash,
                &turn_hash,
            );
            s.cclerk
                .append_receipt(receipt.clone())
                .expect("local executor and cclerk chains must agree");
            drop(s);

            let attestation =
                attest_committed_turn(state, planned, receipt, receipt_hash, &turn_hash).await;

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            McpToolResult::json(&serde_json::json!({
                "activity_status": "committed",
                "proof_status": attestation.proof_status,
                "attestation": attestation.json(),
                "exercised": true,
                "target_cell": target_cell_hex,
                "turn_hash": turn_hash,
                "cert_nonce": cert_nonce_hex,
                "handoff_certificate_hex": hex_encode(&cert_bytes),
                "cert_hash": hex_encode(&cert_hash),
                "introducer_pk": hex_encode(&introducer_pk_bytes),
                "introducer_federation": hex_encode(&introducer_federation_bytes),
                "target_federation": hex_encode(&target_federation_bytes),
                "recipient_pk": hex_encode(&recipient_pk),
                "permissions": permissions_str,
                "swiss": hex_encode(&swiss),
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            let variant = rejection_variant(&reason);
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "rejection_variant": variant,
                "exercised": false,
                "error": format!("handoff cert exercise rejected: {reason}"),
                "turn_hash": turn_hash,
                "cert_nonce": cert_nonce_hex,
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "activity_status": "rejected",
                "proof_status": "not_committed",
                "exercised": false,
                "error": "handoff cert exercise did not commit",
            }))
        }
    }
}

// =============================================================================
// Sovereign witness signing (reshaped per soundness-sweep redesign)
// =============================================================================
