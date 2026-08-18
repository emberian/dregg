//! `mcp::handlers_verify` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

pub(super) async fn tool_peer_exchange(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let peer_cell_id_hex = match params.get("peer_cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: peer_cell_id"),
    };
    let new_commitment_hex = match params.get("new_commitment").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: new_commitment"),
    };

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };
    let peer_cell_id_bytes = match hex_decode(peer_cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for peer_cell_id"),
    };
    let new_commitment = match hex_decode(new_commitment_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for new_commitment"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);
    let peer_cell_id = dregg_cell::CellId(peer_cell_id_bytes);

    // Create a peer exchange instance and generate a state transition.
    let signing_key = s.cclerk.gossip_signing_key().to_bytes();
    let mut exchange = dregg_cell_crypto::PeerExchange::new(cell_id, signing_key);
    exchange.register_peer(peer_cell_id, [0u8; 32]); // PLACEHOLDER peer commitment — see below.

    // Use a zero old_commitment (first exchange) and a zero effects_hash.
    let old_commitment = [0u8; 32];
    let effects_hash = *blake3::hash(b"peer-exchange").as_bytes();

    let transition = exchange.create_transition(old_commitment, new_commitment, effects_hash);
    let transition_hash = blake3::hash(&postcard::to_stdvec(&transition).unwrap_or_default());

    // ⚑ MEASURED 2026-07-30. This returned `"exchanged": true` — a key that CANNOT be false,
    // because nothing above it can fail. NO PEER IS CONTACTED. The peer is registered with a
    // placeholder zero commitment, `old_commitment` is hardcoded zero, `effects_hash` is a
    // constant, and no proof of any kind is produced — while `tools_def` advertised
    // "producing a STARK proof of the transition". An agent plans from `tools/list` and then
    // reads a boolean that reads as a completed exchange.
    //
    // The success word is GONE, and the key with it, so a caller testing `exchanged === true`
    // gets `undefined` rather than a weaker string. What the call actually does is reported:
    // it BUILDS AND SIGNS a local transition object. That is a real artifact and it is worth
    // returning; it is not an exchange and it is not a proof.
    McpToolResult::json(&serde_json::json!({
        "built_local_transition": true,
        "peer_contacted": false,
        "proof": serde_json::Value::Null,
        "cell_id": cell_id_hex,
        "peer_cell_id": peer_cell_id_hex,
        "new_commitment": new_commitment_hex,
        "transition_hash": hex_encode(transition_hash.as_bytes()),
        "sequence": transition.sequence,
        "scope": "This node built and signed a local peer-exchange transition object. It did \
                  NOT contact the peer, did not receive anything from it, registered the peer \
                  under a PLACEHOLDER zero commitment, and produced NO proof. Nothing here is \
                  evidence that an exchange occurred.",
    }))
}

/// **THE ANCHOR A VERIFICATION CLAIM IS EARNED AGAINST.**
///
/// `dregg_compress_history` used to fold the node's retained turns, recompute the VK
/// fingerprint *of the fold it had just produced*, verify against THAT, and report
/// `"verification": "valid"`. Tooth 1 — the VK pin, the entire point of which is that the
/// anchor is configuration the verifier held BEFOREHAND — compared a value with itself and
/// **could not fail**. Every caller of the tool was told a proof verified against an anchor
/// that came from the thing under test.
///
/// A tooth that compares a value with itself is worse than no tooth, so there is no longer a
/// code path that produces one: the anchor is a REQUIRED caller parameter, and the tool
/// refuses before folding anything without it. There is no "self-anchor" flag to set, no
/// default to fall through to, and the tool never derives the value it checks against.
pub(super) fn required_config_anchor(params: &Value) -> Result<[u8; 32], String> {
    let Some(hex) = params.get("vk_anchor").and_then(|v| v.as_str()) else {
        return Err(
            "missing required parameter: vk_anchor (the 64-hex root-circuit VK fingerprint \
             your configuration pins). This tool will not verify against an anchor it \
             computed itself: the anchor IS the trust input, and one recomputed from the \
             fold under test makes the VK pin compare a value with itself, which cannot \
             fail. Obtain it the way a light client does — from the genesis/checkpoint \
             configuration for this circuit shape, or once from an honest setup fold you \
             ran yourself (`produce_history_envelope`) and then held fixed. Passing back a \
             value this node minted in the same breath is the self-anchoring this refusal \
             exists to prevent."
                .to_string(),
        );
    };
    let hex = hex.trim().strip_prefix("0x").unwrap_or(hex.trim());
    if hex.len() != 64 {
        return Err(format!(
            "vk_anchor must be 64 hex chars (32 bytes), got {}. A fat-fingered anchor is a \
             clear error, never a silent zero-fill.",
            hex.len()
        ));
    }
    hex_decode(hex).map_err(|_| "vk_anchor is not valid hex".to_string())
}

/// Assemble the tool's JSON report. Split out from the handler so the ONE rule that matters
/// is checkable without a node, a ledger, or an hour of recursive proving:
///
/// > the `verification` key exists **only** when a caller-supplied anchor was checked.
///
/// `anchored_verify_held` is the outcome of `verify_whole_chain_proof_bytes` against
/// [`required_config_anchor`]'s value — never against a locally recomputed fingerprint.
/// `node/tests/mcp_verification_claims_are_earned.rs` is the permanent control.
pub(super) fn compress_history_report(
    mut fold: serde_json::Map<String, Value>,
    cell_id_hex: &str,
    anchored_verify_held: bool,
) -> Value {
    fold.insert("compressed".into(), serde_json::json!(true));
    fold.insert("cell_id".into(), serde_json::json!(cell_id_hex));
    if anchored_verify_held {
        // Stated ONLY here, and only when the byte envelope re-verified through the
        // light-client teeth against the CALLER'S anchor. This is the light-client check:
        // the anchor was configuration the caller held, not a value this node minted.
        fold.insert("verification".into(), serde_json::json!("valid"));
        fold.insert(
            "anchor_source".into(),
            serde_json::json!("caller-supplied config anchor"),
        );
    }
    Value::Object(fold)
}

pub(super) async fn tool_compress_history(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let turn_count = params.get("turn_count").and_then(|v| v.as_u64());

    // FIRST, before any work: the anchor. Refusing here rather than after the fold means a
    // caller cannot discover the tool's own fingerprint and hand it straight back.
    let config_anchor = match required_config_anchor(params) {
        Ok(a) => a,
        Err(e) => return McpToolResult::error(e),
    };

    let _cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // The REAL receipt chain, oldest → newest. Select the most recent `turn_count`
    // receipts but KEEP chain order — the whole-chain fold's temporal tooth
    // (`new_root[i] == old_root[i+1]`) binds the finalized order.
    let chain = s.cclerk.receipt_chain();
    let limit = turn_count.map(|c| c as usize).unwrap_or(chain.len());
    let start = chain.len().saturating_sub(limit);
    let window = &chain[start..];
    if window.is_empty() {
        return McpToolResult::error("no turns to compress in receipt chain");
    }

    // Load the RETAINED wrap-input `FinalizedTurn` for every turn in the window —
    // minted at commit time from the turn's REAL execution context and anchor-tied
    // to the served FullTurnProof (`blocklace_sync::execute_finalized_turn`).
    // FAIL CLOSED on any gap: synthetic data is never substituted.
    let window_len = window.len();
    let mut retained: Vec<(String, Vec<u8>)> = Vec::with_capacity(window_len);
    let mut missing: Vec<String> = Vec::new();
    for receipt in window {
        let hash_hex = hex_encode(&receipt.turn_hash);
        let key = crate::turn_proving::finalized_turn_config_key(&hash_hex);
        match s.store.get_config(&key) {
            Ok(Some(bytes)) => retained.push((hash_hex, bytes)),
            Ok(None) => missing.push(hash_hex),
            Err(e) => {
                return McpToolResult::error(format!(
                    "config store read failed for turn {hash_hex}: {e}"
                ));
            }
        }
    }
    drop(s);

    if !missing.is_empty() {
        return McpToolResult::error(format!(
            "real IVC compression requires retained finalized turns; {} of {} requested turns \
             have no retained wrap-input FinalizedTurn (they predate retention, were committed \
             without full-turn proving enabled, or failed the fail-closed anchor tie at commit \
             time). First missing turn hashes: [{}]. Nothing was proven — a fabricated stand-in \
             is never substituted.",
            missing.len(),
            window_len,
            missing
                .iter()
                .take(8)
                .cloned()
                .collect::<Vec<_>>()
                .join(", "),
        ));
    }
    if retained.len() < 2 {
        return McpToolResult::error(
            "real IVC compression folds a CHAIN: at least 2 retained finalized turns are \
             required (the whole-chain recursion has no 1-turn fold)",
        );
    }

    // Decode each retained envelope back into the wrap-input `FinalizedTurn`
    // (descriptor rebuilt fail-closed from its committed WIDE-registry row).
    let mut turns = Vec::with_capacity(retained.len());
    for (hash_hex, bytes) in &retained {
        match crate::turn_proving::decode_retained_finalized_turn(bytes) {
            Ok(t) => turns.push(t),
            Err(e) => {
                return McpToolResult::error(format!(
                    "retained finalized turn {hash_hex} failed to decode: {e} (fail-closed; \
                     nothing proven)"
                ));
            }
        }
    }

    // THE REAL FOLD: `prove_turn_chain_recursive` host-admits every leg (each
    // rotated proof re-verified standalone, selector-bound), re-proves each leaf
    // in-circuit, and folds the tree to ONE root; then the byte envelope is
    // verified with `verify_whole_chain_proof_bytes` — the SAME three teeth a
    // light client runs, against the CALLER'S CONFIG ANCHOR.
    //
    // ⚑ THE ANCHOR IS `config_anchor`, NOT `proof.root_vk_fingerprint()`. It used to be
    // the latter: the fold's own recomputed fingerprint, checked against itself, so tooth
    // 1 could not fail and "valid" meant only "this node's fold is internally consistent"
    // while reading as "an independent party verified this history". Passing the caller's
    // value here is what makes the VK pin able to REFUSE — a fold of a different circuit
    // shape, or a node whose recursion tower has moved, now returns a mismatch instead of
    // a green tick. Heavy: run off the async core.
    let turn_total = turns.len();
    let folded = tokio::task::spawn_blocking(move || -> Result<serde_json::Value, String> {
        use dregg_circuit_prove::ivc_turn_chain::RecursionVk;
        let proof = dregg_circuit_prove::ivc_turn_chain::prove_turn_chain_recursive(&turns)
            .map_err(|e| format!("whole-chain fold failed: {e:?}"))?;
        let bytes = proof.to_bytes();
        let anchor = RecursionVk(config_anchor);
        dregg_circuit_prove::ivc_turn_chain::verify_whole_chain_proof_bytes(&bytes, &anchor)
            .map_err(|e| {
                format!(
                    "whole-chain proof did NOT verify against your configured vk_anchor: {e:?}. \
                     Nothing is reported valid. A VK-fingerprint mismatch means this node's \
                     recursion tower folds a DIFFERENT circuit shape than your anchor pins — \
                     which is precisely the refusal the anchor exists to produce, and which \
                     the retired self-anchored path could never reach."
                )
            })?;
        Ok(serde_json::json!({
            "turns_compressed": proof.num_turns,
            "proof_size_bytes": bytes.len(),
            "genesis_root": proof.genesis_root.iter().map(|f| f.as_u32()).collect::<Vec<_>>(),
            "final_root": proof.final_root.iter().map(|f| f.as_u32()).collect::<Vec<_>>(),
            "chain_digest": proof.chain_digest.iter().map(|f| f.as_u32()).collect::<Vec<_>>(),
        }))
    })
    .await;

    match folded {
        // The verify HELD against the caller's anchor — the only path on which this tool
        // has ever been entitled to the word "valid". `compress_history_report` is the one
        // place the key is written, and it writes it only when told the anchored verify
        // held (see `node/tests/mcp_verification_claims_are_earned.rs`).
        Ok(Ok(summary)) => {
            let map = match summary {
                Value::Object(m) => m,
                other => {
                    return McpToolResult::error(format!(
                        "internal: fold summary was not an object ({other})"
                    ));
                }
            };
            McpToolResult::json(&compress_history_report(map, cell_id_hex, true))
        }
        Ok(Err(e)) => McpToolResult::error(format!(
            "IVC compression failed for {turn_total} retained turns (fail-closed): {e}"
        )),
        Err(e) => McpToolResult::error(format!("IVC compression task did not complete: {e}")),
    }
}

// =============================================================================
// Bearer Capability tools
// =============================================================================

pub(super) async fn tool_prove_sovereign_turn(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let effects_val = match params.get("effects").and_then(|v| v.as_array()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: effects"),
    };
    let pre_state_hex = match params.get("pre_state_hash").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: pre_state_hash"),
    };

    let _cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };
    let _pre_state_bytes = match hex_decode(pre_state_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for pre_state_hash"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    // Parse effects into the Effect VM representation.
    let mut vm_effects = Vec::new();
    for effect_val in effects_val {
        let effect_type = effect_val
            .get("type")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown");
        let amount = effect_val
            .get("amount")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);

        let effect = match effect_type {
            "credit" => dregg_circuit::effect_vm::Effect::Transfer {
                amount,
                direction: 0, // 0 = incoming (credit)
            },
            "debit" => dregg_circuit::effect_vm::Effect::Transfer {
                amount,
                direction: 1, // 1 = outgoing (debit)
            },
            "set_field" => dregg_circuit::effect_vm::Effect::SetField {
                field_idx: 0,
                value: dregg_circuit::BabyBear::new(amount as u32),
            },
            "grant_cap" => dregg_circuit::effect_vm::Effect::GrantCapability {
                cap_entry: grant_cap_entry_8(amount as u32),
                phase_b: None,
            },
            other => {
                return McpToolResult::error(format!("unknown effect type: '{other}'"));
            }
        };
        vm_effects.push(effect);
    }

    if vm_effects.is_empty() {
        return McpToolResult::error("effects array cannot be empty");
    }

    // Generate the Effect VM trace and STARK proof.
    let initial_state = dregg_circuit::effect_vm::CellState::new(1000, 0); // Placeholder initial state.
    let (trace, public_inputs) =
        dregg_circuit::effect_vm::generate_effect_vm_trace(&initial_state, &vm_effects);

    // The v1 hand-AIR (`EffectVmAir`) standalone effect-VM prove is RETIRED; this demo
    // tool reports the standalone v1 proof is unavailable (finalized turns prove rotated
    // through the node commit pipeline).
    let _ = (&trace, &public_inputs, &cell_id_hex);
    McpToolResult::json(&serde_json::json!({
        "proved": false,
        "cell_id": cell_id_hex,
        "effect_count": vm_effects.len(),
        "error": "standalone v1 effect-vm proof is retired; finalized turns prove rotated \
                  through the node commit pipeline",
    }))
}

pub(super) async fn tool_verify_sovereign_proof(
    params: &Value,
    state: &NodeState,
) -> McpToolResult {
    let proof_hex = match params.get("proof_hex").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: proof_hex"),
    };
    let public_inputs_val = match params.get("public_inputs").and_then(|v| v.as_array()) {
        Some(pi) => pi,
        None => return McpToolResult::error("missing required parameter: public_inputs"),
    };

    let proof_bytes = match hex_decode_var(proof_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for proof_hex"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    drop(s);

    // Parse public inputs as BabyBear field elements.
    let public_inputs: Vec<dregg_circuit::BabyBear> = public_inputs_val
        .iter()
        .filter_map(|v| v.as_u64().map(|n| dregg_circuit::BabyBear::new(n as u32)))
        .collect();

    // The v1 hand-AIR (`EffectVmAir`) standalone effect-VM `StarkProof` verify is RETIRED and
    // the v1 wire format is gone. Descriptor-IR2 proofs verify through
    // `dregg_circuit::descriptor_ir2::verify_vm_descriptor2`, which must anchor against the
    // emitted descriptor — not available from this raw-bytes demo surface (no descriptor is
    // supplied) — so this tool reports v1 verification is unavailable and rejects (fail-closed).
    let _ = &proof_bytes;
    McpToolResult::json(&serde_json::json!({
        "valid": false,
        "error": "v1 effect-vm STARK verification is retired; descriptor-IR2 proofs verify \
                  through verify_vm_descriptor2 (which needs the descriptor to anchor against)",
        "public_inputs_count": public_inputs.len(),
        "proof_bytes_len": proof_bytes.len(),
    }))
}

// =============================================================================
// Privacy tools
// =============================================================================

pub(super) async fn tool_prove_predicate(params: &Value, state: &NodeState) -> McpToolResult {
    let predicate_type_str = match params.get("predicate_type").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: predicate_type"),
    };
    let attribute = match params.get("attribute").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: attribute"),
    };
    let private_value = match params.get("private_value").and_then(|v| v.as_u64()) {
        Some(v) => v as u32,
        None => return McpToolResult::error("missing required parameter: private_value"),
    };
    let state_root_u32 = match params.get("state_root").and_then(|v| v.as_u64()) {
        Some(r) => r as u32,
        None => return McpToolResult::error("missing required parameter: state_root"),
    };
    let threshold = params
        .get("threshold")
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as u32;

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }
    drop(s);

    // The fact identity the predicate speaks about: the attribute is the predicate symbol, the
    // compared value is `terms[0]`. EVERY descriptor in the family is WELDED and BLINDED — the
    // witness builders compute the fact commitment FROM the value, the fact identity and a private
    // blinding factor (`hash_4_to_1([hash_fact(sym, [value, ..]), state_root, blinding, 0])`), so the
    // predicate proof binds to the committed fact in-circuit and stays unlinkable across showings.
    let state_root = dregg_circuit::BabyBear::new(state_root_u32);
    let attr_sym = dregg_circuit::BabyBear::new(
        blake3::hash(attribute.as_bytes()).as_bytes()[0] as u32
            | ((blake3::hash(attribute.as_bytes()).as_bytes()[1] as u32) << 8),
    );
    let fact = dregg_circuit::predicate_arith_witness::FactBinding {
        predicate_sym: attr_sym,
        term1: dregg_circuit::BabyBear::ZERO,
        term2: dregg_circuit::BabyBear::ZERO,
        state_root,
    };
    // A FRESH blinding factor for THIS proof. The commitment is `hash_4_to_1([fact_hash, state_root,
    // blinding, 0])`, so two proofs about the same attribute emit different commitments and cannot be
    // correlated; the weld still binds each to the value compared.
    let mut blinding_bytes = [0u8; 8];
    if getrandom::fill(&mut blinding_bytes).is_err() {
        return McpToolResult::error(
            "OS randomness unavailable; refusing to emit an unblinded proof",
        );
    }
    let blinding = dregg_circuit::predicate_arith_witness::Blinding(
        dregg_circuit::BabyBear::from_u64(u64::from_le_bytes(blinding_bytes)),
    );
    // The commitment the welded builders reproduce in-circuit for this value + blinding.
    let fact_commitment = fact.commitment_of(
        dregg_circuit::BabyBear::from_u64(private_value as u64),
        blinding,
    );

    // The retired hand-AIR `prove_predicate` is replaced by the descriptor prover: each comparison
    // operator maps to an emitted, byte-pinned IR-v2 descriptor (dispatched by `descriptor_by_name`)
    // proven through `prove_vm_descriptor2`. The witness builders live in circuit's
    // `predicate_arith_witness` (`≥`) and `predicate_comparison_witness` (`≤`/`>`/`<`/`≠`). The
    // descriptor's in-circuit range/nonzero tooth is the judge — an unsatisfiable comparison makes the
    // witness build or the prove fail, matching the old `Option::None` "predicate does not hold".
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use dregg_circuit::predicate_arith_witness::{PREDICATE_ARITH_NAME, predicate_arith_witness};
    use dregg_circuit::predicate_comparison_witness::{
        PREDICATE_ARITH_GT_NAME, PREDICATE_ARITH_LE_NAME, PREDICATE_ARITH_LT_NAME,
        PREDICATE_ARITH_NEQ_NAME, predicate_gt_witness, predicate_le_witness, predicate_lt_witness,
        predicate_neq_witness,
    };

    const HEIGHT: usize = 4; // trace height (power of two ≥ 2) — the emit-gate goldens' choice.
    let value = private_value as u64;
    let thr = threshold as u64;
    let (air_name, built) = match predicate_type_str {
        "gte" => (
            PREDICATE_ARITH_NAME,
            predicate_arith_witness(value, thr, fact, blinding, HEIGHT),
        ),
        "lte" => (
            PREDICATE_ARITH_LE_NAME,
            predicate_le_witness(value, thr, fact, blinding, HEIGHT),
        ),
        "gt" => (
            PREDICATE_ARITH_GT_NAME,
            predicate_gt_witness(value, thr, fact, blinding, HEIGHT),
        ),
        "lt" => (
            PREDICATE_ARITH_LT_NAME,
            predicate_lt_witness(value, thr, fact, blinding, HEIGHT),
        ),
        "neq" => (
            PREDICATE_ARITH_NEQ_NAME,
            predicate_neq_witness(value, thr, fact, blinding, HEIGHT),
        ),
        other => {
            return McpToolResult::error(format!(
                "unknown predicate_type: '{other}'. Valid: gte, lte, gt, lt, neq"
            ));
        }
    };

    // Resolve the emitted descriptor — fail-closed on a miss (never a silent accept).
    let descriptor = match dregg_circuit::descriptor_by_name::descriptor_by_name(air_name) {
        Some(d) => d,
        None => {
            return McpToolResult::error(format!(
                "no emitted descriptor for predicate_type '{predicate_type_str}' (air '{air_name}')"
            ));
        }
    };

    // A witness-build refusal already means the comparison is unsatisfiable at this shape.
    let (trace, public_inputs) = match built {
        Ok(tw) => tw,
        Err(_) => {
            return McpToolResult::json(&serde_json::json!({
                "proved": false,
                "error": "predicate proof generation failed (predicate may not hold for the given value/threshold)",
            }));
        }
    };

    // Prove then verify through the descriptor prover. A prove/verify refusal = the in-circuit
    // range/nonzero tooth rejected the witness (predicate does not hold) — fail-closed to proved:false.
    match prove_vm_descriptor2(
        &descriptor,
        &trace,
        &public_inputs,
        &MemBoundaryWitness::default(),
        &[],
    ) {
        Ok(proof) if verify_vm_descriptor2(&descriptor, &proof, &public_inputs).is_ok() => {
            let proof_bytes = postcard::to_stdvec(&proof).unwrap_or_default();
            McpToolResult::json(&serde_json::json!({
                "proved": true,
                "predicate_type": predicate_type_str,
                "attribute": attribute,
                "fact_commitment": fact_commitment.as_u32(),
                "state_root": state_root_u32,
                "threshold": threshold,
                "descriptor": air_name,
                "proof_hash": hex_encode(blake3::hash(&proof_bytes).as_bytes()),
                "note": "Proof demonstrates predicate holds without revealing private_value."
            }))
        }
        _ => McpToolResult::json(&serde_json::json!({
            "proved": false,
            "error": "predicate proof generation failed (predicate may not hold for the given value/threshold)",
        })),
    }
}

// =============================================================================
// Proof Composition tool
// =============================================================================

/// **RETIRED, FAIL-CLOSED.** The old body verified NOTHING: it hex-decoded the
/// inputs, BLAKE3-hashed them, and answered `composed: true` / `valid` for every
/// mode unconditionally — a checksum masquerading as proof composition. No real
/// composition engine exists to wire to (the multi-step composite was deleted in
/// the stark-kill), so this tool now refuses honestly instead of claiming
/// validity. Real whole-chain folding lives in `dregg_compress_history`
/// (`ivc_turn_chain::prove_turn_chain_recursive`).
pub(super) async fn tool_compose_proofs(params: &Value, _state: &NodeState) -> McpToolResult {
    let mode = params
        .get("mode")
        .and_then(|v| v.as_str())
        .unwrap_or("<unspecified>");
    McpToolResult::error(format!(
        "proof composition is RETIRED (fail-closed): no real composition engine exists — the \
         former implementation only hashed the supplied bytes and reported '{mode}' composition \
         as valid without verifying anything. Nothing was composed or verified. For a real \
         constant-size proof over a turn history, use dregg_compress_history (the whole-chain \
         recursive fold)."
    ))
}

// =============================================================================
// Blocklace tools
// =============================================================================

/// Build a `SovereignCellWitness` for a sovereign cell currently in the
/// local ledger, signed with the node cipherclerk's Ed25519 key.
///
/// The canonical signing message includes (cell_id, old_commitment,
/// new_commitment, effects_hash, timestamp, sequence) — see
/// `SovereignCellWitness::signing_message`. Per the soundness-sweep
/// redesign the executor verifies the signature against the cell's
/// `public_key()` with `verify_strict`, enforces a monotonic per-cell
/// `sequence`, and (when `attach_proof` is set) verifies the optional
/// STARK `transition_proof` through the EffectVmAir path.
pub(super) async fn tool_sign_sovereign_witness(
    params: &Value,
    state: &NodeState,
) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    // THE EFFECTS the witness authorizes. This used to be an `effects_hash`
    // CALLER PARAMETER defaulting to `[0u8; 32]` — a caller-supplied binding,
    // which is to say no binding at all: the caller chose the digest AND the
    // effects independently, and nothing ever compared them. The tool now takes
    // the effects, builds the turn they belong to, and DERIVES the digest
    // through `Turn::sovereign_effects_hash` — the one function the executor's
    // witness rule 7b recomputes.
    let effects_json = match params.get("effects").and_then(|v| v.as_array()) {
        Some(a) => a,
        None => {
            return McpToolResult::error(
                "missing required parameter: effects (array of effect descriptors). The \
                 `effects_hash` parameter is GONE: a witness binds the effects it authorizes, \
                 and a caller-chosen hash binds nothing.",
            );
        }
    };
    let mut effects: Vec<dregg_turn::Effect> = Vec::with_capacity(effects_json.len());
    for e in effects_json {
        match super::proof::parse_effect_json(e) {
            Ok(effect) => effects.push(effect),
            Err(msg) => return McpToolResult::error(msg),
        }
    }
    let attach_proof = params
        .get("attach_proof")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);
    let vm_effect_amount = params
        .get("vm_effect_amount")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("cipherclerk is locked; unlock first");
    }

    let cell = match s.ledger.get(&cell_id) {
        Some(c) => c.clone(),
        None => {
            return McpToolResult::error(format!(
                "cell {} not found in local ledger; create it before signing a witness",
                cell_id_hex
            ));
        }
    };

    let old_commitment: [u8; 32] = match s.ledger.get_sovereign_commitment(&cell_id) {
        Some(c) => *c,
        None => cell.state_commitment(),
    };

    let sequence = s.ledger.last_sovereign_witness_sequence(&cell_id) + 1;

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let new_commitment: [u8; 32] = match params.get("new_commitment").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for new_commitment"),
        },
        // FAIL CLOSED. The old default here was
        // `derive_key("dregg-mcp-witness-new-commit-v1")(cell_id ‖ old ‖ effects_hash ‖ seq)`
        // — a fabricated digest that is not the post-state commitment of
        // anything, so the executor's post-execution check
        // (`SovereignCommitmentMismatch`) refused every witness this tool
        // produced without an explicit `new_commitment`. This node does not
        // execute the effects to learn the post-state, so it says so instead of
        // inventing a value.
        None => {
            return McpToolResult::error(
                "missing required parameter: new_commitment (hex-encoded 32-byte post-state \
                 commitment). This tool does not execute the effects, so it cannot derive the \
                 post-state; a fabricated commitment is refused by the executor \
                 (SovereignCommitmentMismatch).",
            );
        }
    };

    // The turn this witness is FOR. The witness's `effects_hash` is a property of
    // a specific turn, so the tool builds that turn here and hands it back with
    // the witness — a witness detached from its turn is not submittable and its
    // digest is not checkable.
    let mut witnessed_turn = dregg_turn::Turn {
        agent: cell_id,
        nonce: 0,
        call_forest: super::proof::build_forest_with_effects(cell_id, effects),
        fee: 0,
        memo: None,
        // This is the exact turn the tool tells the caller to submit
        // (`witnessed_turn_postcard_hex`, below) — `None` would skip the executor's
        // expiration check entirely (`turn/src/executor/execute.rs:426`) on it.
        valid_until: crate::api::default_valid_until(),
        previous_receipt_hash: None,
        depends_on: Vec::new(),
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
    let effects_hash: [u8; 32] = witnessed_turn.sovereign_effects_hash(&cell_id);

    let signing_msg = dregg_turn::SovereignCellWitness::signing_message(
        &cell_id,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        timestamp,
        sequence,
    );
    let sig = dregg_types::sign(&s.cclerk.gossip_signing_key(), &signing_msg);

    let transition_proof_hex = if attach_proof {
        let vm_effects = vec![dregg_circuit::effect_vm::Effect::Transfer {
            amount: vm_effect_amount,
            direction: 1,
        }];
        // The standalone v1 material is RETIRED, so this always refuses. It must NOT
        // panic (this runs inside the stdio dispatch loop, which has no `catch_unwind` —
        // a panic here kills the whole `dregg-node mcp` server), and it must NOT silently
        // hand back a proof-less witness to a caller who explicitly asked for
        // `attach_proof`: refuse by name instead.
        //
        // ⚑ THIS REFUSAL IS CORRECT, and it is NOT the class of refusal the five commit
        // tools carried (2026-07-28). Those refused to COMMIT because an ADDITIVE
        // attestation could not be minted; this one refuses to MINT AN ARTIFACT THE
        // EXECUTOR ITSELF REJECTS. `turn/src/executor/execute.rs` (step 8 of sovereign
        // witness verification) fails a turn CLOSED with `InvalidExecutionProof` the
        // moment a witness carries a v1 `transition_proof`. Handing one back would build
        // a witness whose only effect is to make every turn it is attached to
        // unsubmittable — so the tool refuses the REQUEST, by name, and a caller who
        // omits `attach_proof` gets a witness that works.
        match try_generate_effect_vm_proof(
            u64::try_from(cell.state.balance()).unwrap_or(0),
            cell.state.nonce(),
            &vm_effects,
        ) {
            Ok(material) => material.into_parts().0,
            Err(e) => {
                return McpToolResult::error(format!(
                    "attach_proof was requested but no transition proof can be produced: {e}. \
                     A v1 transition_proof is refused by the executor itself \
                     (TurnError::InvalidExecutionProof, execute.rs sovereign-witness step 8), \
                     so attaching one would make this witness unsubmittable. Re-issue without \
                     `attach_proof`; the sovereign attestation path is the rotated \
                     proof-carrying turn."
                ));
            }
        }
    } else {
        String::new()
    };
    let transition_proof_field: serde_json::Value = if transition_proof_hex.is_empty() {
        serde_json::Value::Null
    } else {
        serde_json::Value::String(transition_proof_hex.clone())
    };

    let transition_proof_bytes: Option<Vec<u8>> = if transition_proof_hex.is_empty() {
        None
    } else {
        hex_decode_var(&transition_proof_hex).ok()
    };
    let witness = dregg_turn::SovereignCellWitness {
        cell_id,
        old_commitment,
        new_commitment,
        effects_hash,
        timestamp,
        sequence,
        signature: sig.0,
        cell_state: cell.clone(),
        transition_proof: transition_proof_bytes,
    };
    let witness_postcard = postcard::to_stdvec(&witness).unwrap_or_default();
    let signer_pk_hex = hex_encode(cell.public_key());
    // Hand back the WITNESSED TURN, not just the witness: `effects_hash` is a
    // property of this turn and of no other, so submitting the witness against a
    // different effect set is now a rejection (`EffectsHashMismatch`), not a
    // silent substitution.
    witnessed_turn.sovereign_witnesses.insert(cell_id, witness);
    let turn_postcard = postcard::to_stdvec(&witnessed_turn).unwrap_or_default();
    drop(s);

    McpToolResult::json(&serde_json::json!({
        "signed": true,
        "cell_id": cell_id_hex,
        "old_commitment": hex_encode(&old_commitment),
        "new_commitment": hex_encode(&new_commitment),
        "effects_hash": hex_encode(&effects_hash),
        "timestamp": timestamp,
        "sequence": sequence,
        "signature": hex_encode(&sig.0),
        "signer_pubkey": signer_pk_hex,
        "transition_proof_hex": transition_proof_field,
        "witness_postcard_hex": hex_encode(&witness_postcard),
        "witnessed_turn_postcard_hex": hex_encode(&turn_postcard),
        "note": "Submit `witnessed_turn_postcard_hex` — the witness is already attached at Turn::sovereign_witnesses[cell_id]. The witness's effects_hash is the canonical `Turn::sovereign_effects_hash` of THAT turn; attaching it to a turn with any other effect set is rejected with EffectsHashMismatch.",
    }))
}

// =============================================================================
// γ.2 bilateral binding receipts
// =============================================================================
