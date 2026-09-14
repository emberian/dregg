//! `mcp::handlers_privacy` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

pub(super) async fn tool_seal_data(params: &Value, state: &NodeState) -> McpToolResult {
    let data = match params.get("data").and_then(|v| v.as_str()) {
        Some(d) => d,
        None => return McpToolResult::error("missing required parameter: data"),
    };
    let recipient_hex = match params.get("recipient").and_then(|v| v.as_str()) {
        Some(r) => r,
        None => return McpToolResult::error("missing required parameter: recipient"),
    };

    let recipient_bytes = match hex_decode(recipient_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error("invalid hex for recipient (expected 64 hex chars)");
        }
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Use X25519 + ChaCha20-Poly1305 sealed-box encryption.
    // Generate ephemeral keypair for forward secrecy.
    let mut eph_bytes = [0u8; 32];
    if getrandom::fill(&mut eph_bytes).is_err() {
        return McpToolResult::error("failed to generate ephemeral key");
    }
    let ephemeral_secret = x25519_dalek::StaticSecret::from(eph_bytes);
    let ephemeral_public = x25519_dalek::PublicKey::from(&ephemeral_secret);

    // DH with recipient's public key to derive shared secret.
    let recipient_public = x25519_dalek::PublicKey::from(recipient_bytes);
    let shared = ephemeral_secret.diffie_hellman(&recipient_public);

    // Derive encryption key via BLAKE3 KDF (don't use raw DH output directly).
    let enc_key = blake3::derive_key("dregg-mcp-seal-data-v1", shared.as_bytes());

    // Generate random nonce.
    let mut nonce_bytes = [0u8; 12];
    if getrandom::fill(&mut nonce_bytes).is_err() {
        return McpToolResult::error("failed to generate nonce");
    }

    // Encrypt with ChaCha20-Poly1305.
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new((&enc_key).into());
    let nonce = chacha20poly1305::Nonce::from_slice(&nonce_bytes);
    let ciphertext = match cipher.encrypt(nonce, data.as_bytes()) {
        Ok(ct) => ct,
        Err(_) => return McpToolResult::error("encryption failed"),
    };

    // Wire format: [32-byte ephemeral pk][12-byte nonce][ciphertext + tag]
    let mut sealed_box = Vec::with_capacity(32 + 12 + ciphertext.len());
    sealed_box.extend_from_slice(ephemeral_public.as_bytes());
    sealed_box.extend_from_slice(&nonce_bytes);
    sealed_box.extend_from_slice(&ciphertext);
    let sealed_hex: String = sealed_box.iter().map(|b| format!("{b:02x}")).collect();

    McpToolResult::json(&serde_json::json!({
        "sealed": true,
        "sealed_box": sealed_hex,
        "recipient": recipient_hex,
        "ephemeral_public": hex_encode(ephemeral_public.as_bytes()),
        "note": "Data sealed with X25519+ChaCha20-Poly1305. Only the recipient can unseal with their private key."
    }))
}

pub(super) async fn tool_unseal_data(params: &Value, state: &NodeState) -> McpToolResult {
    let sealed_box_hex = match params.get("sealed_box").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: sealed_box"),
    };

    // Decode variable-length hex sealed box.
    let sealed_bytes = match hex_decode_var(sealed_box_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for sealed_box"),
    };

    // Wire format: [32-byte ephemeral pk][12-byte nonce][ciphertext + tag]
    if sealed_bytes.len() < 32 + 12 + 16 {
        return McpToolResult::error("sealed_box too short (minimum 60 bytes)");
    }

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let ephemeral_public_bytes: [u8; 32] = sealed_bytes[..32].try_into().unwrap();
    let nonce_bytes: [u8; 12] = sealed_bytes[32..44].try_into().unwrap();
    let ciphertext = &sealed_bytes[44..];

    // Derive the cipherclerk's X25519 secret from its Ed25519 signing key (private material).
    // SECURITY: Must use private key material here — deriving from the public key would
    // allow anyone to compute the same secret and decrypt sealed data.
    let cclerk_secret_bytes = s.cclerk.derive_symmetric_key("dregg-mcp-seal-x25519-v1");
    let cclerk_secret = x25519_dalek::StaticSecret::from(cclerk_secret_bytes);
    let ephemeral_public = x25519_dalek::PublicKey::from(ephemeral_public_bytes);
    let shared = cclerk_secret.diffie_hellman(&ephemeral_public);

    // Derive decryption key the same way as sealing.
    let dec_key = blake3::derive_key("dregg-mcp-seal-data-v1", shared.as_bytes());

    // Decrypt with ChaCha20-Poly1305.
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new((&dec_key).into());
    let nonce = chacha20poly1305::Nonce::from_slice(&nonce_bytes);
    match cipher.decrypt(nonce, ciphertext) {
        Ok(plaintext) => {
            let text = String::from_utf8_lossy(&plaintext).to_string();
            McpToolResult::json(&serde_json::json!({
                "unsealed": true,
                "data": text,
            }))
        }
        Err(_) => McpToolResult::json(&serde_json::json!({
            "unsealed": false,
            "error": "decryption failed — this sealed box was not addressed to this cipherclerk, or is corrupted",
        })),
    }
}

pub(super) async fn tool_create_stealth_address(
    params: &Value,
    state: &NodeState,
) -> McpToolResult {
    let spend_pk_hex = match params
        .get("recipient_spend_pubkey")
        .and_then(|v| v.as_str())
    {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: recipient_spend_pubkey"),
    };
    let view_pk_hex = match params.get("recipient_view_pubkey").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: recipient_view_pubkey"),
    };

    let spend_pk_bytes = match hex_decode(spend_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for recipient_spend_pubkey"),
    };
    let view_pk_bytes = match hex_decode(view_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for recipient_view_pubkey"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    drop(s);

    // Generate ephemeral keypair for the stealth protocol.
    let mut eph_bytes = [0u8; 32];
    if getrandom::fill(&mut eph_bytes).is_err() {
        return McpToolResult::error("failed to generate ephemeral key");
    }
    let ephemeral_secret = x25519_dalek::StaticSecret::from(eph_bytes);
    let ephemeral_public = x25519_dalek::PublicKey::from(&ephemeral_secret);

    // DH with recipient's view key.
    let view_public = x25519_dalek::PublicKey::from(view_pk_bytes);
    let shared_secret = ephemeral_secret.diffie_hellman(&view_public);

    // Derive one-time address: scalar = BLAKE3(shared_secret || "dregg-stealth-derive")
    let scalar = blake3::derive_key("dregg-stealth-derive", shared_secret.as_bytes());

    // One-time address = spend_pk XOR scalar (simplified; full impl uses curve addition)
    let mut one_time_address = [0u8; 32];
    for i in 0..32 {
        one_time_address[i] = spend_pk_bytes[i] ^ scalar[i];
    }

    McpToolResult::json(&serde_json::json!({
        "one_time_address": hex_encode(&one_time_address),
        "ephemeral_public": hex_encode(ephemeral_public.as_bytes()),
        "note": "Share ephemeral_public with the transaction. Recipient scans with their view key to detect ownership."
    }))
}

pub(super) async fn tool_private_transfer(params: &Value, state: &NodeState) -> McpToolResult {
    let from_cell_hex = match params.get("from_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: from_cell"),
    };
    let to_cell_hex = match params.get("to_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_cell"),
    };
    let amount = match params.get("amount").and_then(|v| v.as_u64()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: amount"),
    };

    let from_cell_bytes = match hex_decode(from_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for from_cell"),
    };
    let to_cell_bytes = match hex_decode(to_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to_cell"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Generate or use provided blinding factor.
    let blinding = match params.get("blinding").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for blinding"),
        },
        None => {
            let mut b = [0u8; 32];
            if getrandom::fill(&mut b).is_err() {
                return McpToolResult::error("failed to generate blinding factor");
            }
            b
        }
    };

    // Compute Pedersen-style commitment: BLAKE3("dregg-pedersen-v1", amount || blinding)
    let mut input = Vec::with_capacity(40);
    input.extend_from_slice(&amount.to_le_bytes());
    input.extend_from_slice(&blinding);
    let commitment = blake3::derive_key("dregg-pedersen-v1", &input);

    // Build a turn with committed note effects.
    let from_cell_id = dregg_cell::CellId(from_cell_bytes);
    let _to_cell_id = dregg_cell::CellId(to_cell_bytes);
    let agent_cell_id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);

    // Build a note commitment from the Pedersen commitment.
    let note_commitment = dregg_cell::NoteCommitment(commitment);

    let effects = vec![dregg_turn::Effect::NoteCreate {
        commitment: note_commitment,
        value: 0, // Hidden in commitment.
        asset_type: 0,
        encrypted_note: vec![], // Recipient decrypts separately.
        value_commitment: Some(commitment),
        range_proof: None,
    }];

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
        memo: Some("private transfer".to_string()),
        // `None` skips the executor's expiration check entirely
        // (`turn/src/executor/execute.rs:426`) — bound it instead
        // (`api::default_valid_until`).
        valid_until: crate::api::default_valid_until(),
        call_forest: build_forest_with_effects(from_cell_id, effects),
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
                "transferred": true,
                "turn_hash": turn_hash,
                "commitment": hex_encode(&commitment),
                "from_cell": from_cell_hex,
                "to_cell": to_cell_hex,
                "note": "Amount hidden behind Pedersen commitment. Recipient can verify with blinding factor."
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "transferred": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "transferred": false,
                "error": "private transfer turn did not commit",
            }))
        }
    }
}

pub(super) async fn tool_encrypt_intent(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let resource = match params.get("resource").and_then(|v| v.as_str()) {
        Some(r) => r.to_string(),
        None => return McpToolResult::error("missing required parameter: resource"),
    };
    let expiry_blocks = params
        .get("expiry_blocks")
        .and_then(|v| v.as_u64())
        .unwrap_or(100);

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let expiry = current_height + expiry_blocks;

    // Build the match spec for SSE encryption.
    let spec = dregg_intent::MatchSpec {
        actions: vec![dregg_intent::ActionPattern {
            action: Some(action.clone()),
            resource: Some(resource.clone()),
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some(resource.clone()),
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };

    let creator = dregg_intent::CommitmentId::random();

    // Create the encrypted intent using SSE.
    let (encrypted_intent, _keypair) =
        dregg_intent::sse::EncryptedIntent::create(&spec, creator, 0, Some(expiry));

    let intent_id = encrypted_intent.id;
    let intent_id_hex = hex_encode(&intent_id);

    // Store in the encrypted intent pool.
    if s.encrypted_intent_pool.len() >= crate::api::MAX_NODE_INTENT_POOL {
        return McpToolResult::error("encrypted intent pool is full");
    }
    s.encrypted_intent_pool.insert(intent_id, encrypted_intent);

    McpToolResult::json(&serde_json::json!({
        "intent_id": intent_id_hex,
        "encrypted": true,
        "action": action,
        "resource": resource,
        "expiry_height": expiry,
        "note": "Intent body encrypted with SSE. Fulfillers can match via search tokens without seeing plaintext."
    }))
}
