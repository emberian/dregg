let wasm_bindgen = (function(exports) {
    let script_src;
    if (typeof document !== 'undefined' && document.currentScript !== null) {
        script_src = new URL(document.currentScript.src, location.href).toString();
    }

    /**
     * Advance the block height for timeout simulation.
     * @param {number} handle
     * @param {bigint} blocks
     * @returns {any}
     */
    function advance_height(handle, blocks) {
        const ret = wasm.advance_height(handle, blocks);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.advance_height = advance_height;

    /**
     * Attenuate an existing held token by narrowing its actions/resource.
     * @param {number} handle
     * @param {number} agent_index
     * @param {number} token_index
     * @param {string} restrict_actions_json
     * @param {string} restrict_resource
     * @returns {any}
     */
    function agent_attenuate(handle, agent_index, token_index, restrict_actions_json, restrict_resource) {
        const ptr0 = passStringToWasm0(restrict_actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(restrict_resource, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.agent_attenuate(handle, agent_index, token_index, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.agent_attenuate = agent_attenuate;

    /**
     * Mint a token for an agent (for intent matching).
     * `actions_json` is a JSON array of strings like `["read", "write"]`.
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} resource
     * @param {string} actions_json
     * @param {bigint} expiry
     * @returns {any}
     */
    function agent_mint_token(handle, agent_index, resource, actions_json, expiry) {
        const ptr0 = passStringToWasm0(resource, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.agent_mint_token(handle, agent_index, ptr0, len0, ptr1, len1, expiry);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.agent_mint_token = agent_mint_token;

    /**
     * Attempt time-travel rewind on the sim runtime (STARBRIDGE-FOLLOWUP-03
     * on blocked §5.10 + Q4).
     *
     * For target <= current: returns Ok(()) only for exact current (no-op) or
     * Err explaining the pending snapshot format dependency.
     * For target > current: explicit forward-only error.
     *
     * Provides the JS-callable surface + error shape for `<dregg-...>`
     * scrubber / cursor UI to target. `caps.timeTravel` should stay false
     * in surfaces until real impl lands. See runtime.rs docs and plan §5.10.
     *
     * Thin + safe (no proving stack, delegates to stub).
     * @param {number} handle
     * @param {bigint} target_height
     * @returns {any}
     */
    function attempt_time_travel(handle, target_height) {
        const ret = wasm.attempt_time_travel(handle, target_height);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.attempt_time_travel = attempt_time_travel;

    /**
     * Attenuate a macaroon token with service/action restrictions.
     *
     * `actions` is a comma-separated list of action strings (e.g. "read,write").
     * `expires_secs` is seconds from now (0 means no expiry caveat).
     *
     * Returns JSON: { "token": "<em2_...>", "caveats_added": N }
     * @param {string} token_str
     * @param {Uint8Array} root_key
     * @param {string} service
     * @param {string} actions
     * @param {bigint} expires_secs
     * @returns {any}
     */
    function attenuate_token(token_str, root_key, service, actions, expires_secs) {
        const ptr0 = passStringToWasm0(token_str, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(root_key, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(service, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(actions, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.attenuate_token(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, expires_secs);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.attenuate_token = attenuate_token;

    /**
     * Compute a BLAKE3 hash of an arbitrary string, returning the hex digest.
     *
     * This is exposed so the extension can produce BLAKE3 hashes without pulling
     * in a full JS implementation.
     * @param {string} input
     * @returns {string}
     */
    function blake3_hash(input) {
        let deferred2_0;
        let deferred2_1;
        try {
            const ptr0 = passStringToWasm0(input, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.blake3_hash(ptr0, len0);
            deferred2_0 = ret[0];
            deferred2_1 = ret[1];
            return getStringFromWasm0(ret[0], ret[1]);
        } finally {
            wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
        }
    }
    exports.blake3_hash = blake3_hash;

    /**
     * Build a committed (private) transfer turn.
     *
     * Takes a JSON params object and returns the turn bytes + turn_id.
     * @param {string} params_json
     * @returns {any}
     */
    function build_committed_turn(params_json) {
        const ptr0 = passStringToWasm0(params_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.build_committed_turn(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.build_committed_turn = build_committed_turn;

    /**
     * Build a faceted capability mask.
     *
     * `allowed_effects_json`: JSON array of effect names to permit.
     * Valid names: "set_field", "transfer", "grant_capability", "revoke_capability",
     *             "emit_event", "increment_nonce", "create_cell", "set_permissions",
     *             "set_verification_key"
     *
     * Returns JSON: { mask: u32, description: string[] }
     * @param {string} allowed_effects_json
     * @returns {any}
     */
    function build_facet_mask(allowed_effects_json) {
        const ptr0 = passStringToWasm0(allowed_effects_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.build_facet_mask(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.build_facet_mask = build_facet_mask;

    /**
     * Build and sign a canonical turn from a JSON spec, using `AgentCipherclerk` as
     * the canonical signing path.
     *
     * The cipherclerk is constructed from `sender_privkey` (32-byte Ed25519 seed
     * carried by the extension background) using `AgentCipherclerk::from_key_bytes`,
     * and the turn is built via `AgentCipherclerk::make_action` + `AgentCipherclerk::make_turn_for`.
     * The action records one `Effect::IncrementNonce` (a no-op state advancement)
     * with a custom `method` field derived from `turnSpec.action` — it carries the
     * semantic intent without requiring ledger state for the extension's broadcast path.
     *
     * JSON input:
     * ```json
     * {
     *   "sender_pubkey": [32 bytes as number[]],
     *   "sender_privkey": [32 bytes as number[]],
     *   "action": "transfer",
     *   "resource": "docs/*",
     *   "amount": 0,
     *   "recipient": null,
     *   "metadata": null,
     *   "timestamp": 1716000000
     * }
     * ```
     *
     * Returns JSON: `{ "turn_id": "<hex>", "turn_bytes": <Uint8Array> }`.
     * `turn_bytes` is the postcard-serialized `Turn` that the node's
     * `/turns/submit` endpoint expects.
     * @param {string} spec_json
     * @returns {any}
     */
    function build_turn(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.build_turn(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.build_turn = build_turn;

    /**
     * Check if a stealth announcement is addressed to us.
     *
     * Performs the DH check: shared = X25519(view_privkey, ephemeral_pubkey),
     * then derives expected one-time pubkey and compares.
     *
     * Returns JSON: { is_ours: bool, one_time_privkey: Vec<u8> | null }
     * @param {Uint8Array} view_privkey
     * @param {Uint8Array} spend_pubkey
     * @param {Uint8Array} ephemeral_pubkey
     * @param {Uint8Array} one_time_pubkey
     * @returns {any}
     */
    function check_stealth_ownership(view_privkey, spend_pubkey, ephemeral_pubkey, one_time_pubkey) {
        const ptr0 = passArray8ToWasm0(view_privkey, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(spend_pubkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passArray8ToWasm0(ephemeral_pubkey, wasm.__wbindgen_malloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passArray8ToWasm0(one_time_pubkey, wasm.__wbindgen_malloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.check_stealth_ownership(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.check_stealth_ownership = check_stealth_ownership;

    /**
     * Build and sign a canonical `Effect::CreateCellFromFactory` turn from a
     * JSON spec, using `AgentCipherclerk::create_from_factory` as the canonical
     * constructor-transparency path.
     *
     * This replaces the standalone `create_from_factory` derivation function
     * for the extension's `window.dregg.createFromFactory` path. The previous
     * shape only computed `(child_vk, param_hash)` deterministically — useful
     * for client-side preview, but it never actually minted a cell. The
     * canonical path is: build a real signed turn, submit it via
     * `/turns/submit`, and let the node's `TurnExecutor` mint the cell with
     * real provenance tracking.
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes as number[]],
     *   "factory_vk_hex": "<64 hex chars>",
     *   "owner_pubkey_hex": "<64 hex chars>",
     *   "token_id_hex": "<64 hex chars>",
     *   "mode": "Hosted" | "Sovereign",
     *   "program_vk_hex": "<optional 64 hex chars>",
     *   "initial_fields": [[field_index, value], ...],
     *   "initial_balance": 0
     * }
     * ```
     *
     * Returns JSON: `{ "turn_id": "<hex>", "turn_bytes": <Uint8Array>,
     * "child_vk": "<hex>", "param_hash": "<hex>", "factory_vk": "<hex>" }`.
     *
     * `turn_bytes` is the postcard-serialized `Turn` that the node's
     * `/turns/submit` endpoint accepts. `child_vk` / `param_hash` are
     * surfaced so the caller can immediately compute the new cell's identity
     * without round-tripping through the node.
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_create_from_factory(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_create_from_factory(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_create_from_factory = cipherclerk_create_from_factory;

    /**
     * Build a cipherclerk-signed [`Turn`] carrying a single named action.
     *
     * Routes through `AgentCipherclerk::make_action(target, method, effects,
     * federation_id)` + `AgentCipherclerk::make_turn_for(domain, action)` so
     * the action's `authorization` field is a real Ed25519 signature
     * over the canonical action bytes, bound to the federation_id.
     *
     * The action's `method` carries the semantic name
     * (e.g. `"propose_routes"`, `"vote_on_proposal"`); the request payload
     * is carried in the [`Turn::memo`] field as a JSON string. The
     * federation can dispatch by `method` and decode the memo to recover
     * the proposal / vote payload. The action's effects are a single
     * `IncrementNonce` (no ledger mutation in the action itself — the
     * federation drives any state change from the memo'd payload).
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes],
     *   "method": "propose_routes",
     *   "memo_json": "<arbitrary JSON string for the action body>",
     *   "federation_id_hex": "<optional 64 hex chars>"
     * }
     * ```
     *
     * Returns JSON: `{ turn_id, turn_bytes, agent_cell_id, method }`.
     * `turn_bytes` is the postcard-serialized signed `Turn` for the node's
     * `/turns/submit` endpoint.
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_make_action_turn(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_make_action_turn(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_make_action_turn = cipherclerk_make_action_turn;

    /**
     * Build a peer-exchange `PeerStateTransition` signed by the cipherclerk's
     * Ed25519 key via `AgentCipherclerk::peer_exchange(domain)`. This replaces
     * the prior `peer_exchange_with_proof` shape (which only emitted
     * canonical-looking hex blobs but did not sign with the cipherclerk).
     *
     * The transition carries:
     *   - `cell_id`        = `cclerk.cell_id("default")`
     *   - `old_commitment` = blake3-derived from (sender, receiver)
     *   - `new_commitment` = blake3-derived from (old, amount, receiver)
     *   - `effects_hash`   = blake3 of postcard(`Effect::Transfer{..}`)
     *   - `sequence`       = 1 (each call constructs a fresh PeerExchange
     *                          session — wasm has no persistent session)
     *   - `timestamp`      = caller-supplied (wasm has no `SystemTime::now()`)
     *   - `signature`      = Ed25519 over the canonical message
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes as number[]],
     *   "receiver_cell_hex": "<64 hex>",
     *   "amount": <u64>,
     *   "timestamp": <i64 unix-seconds>
     * }
     * ```
     *
     * Returns JSON: `{ exchange_id, proof_commitment, sender_cell,
     * receiver_cell, transition_bytes, amount }`. `transition_bytes` is
     * the postcard-encoded `PeerStateTransition` — the wire format peers
     * exchange directly. `exchange_id` / `proof_commitment` are retained
     * for shape compatibility with the legacy binding so existing
     * page-side callers don't break.
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_peer_exchange(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_peer_exchange(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_peer_exchange = cipherclerk_peer_exchange;

    /**
     * Build an `EncryptedIntent` via the canonical SDK path
     * (`AgentCipherclerk::post_encrypted_intent`). The cipherclerk's Ed25519 identity
     * is the source of the `commitment_id` field; the intent body is sealed
     * with a fresh ephemeral keypair (per `EncryptedIntent::create`).
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes as number[]],
     *   "match_spec": { ... canonical MatchSpec JSON ... },
     *   "kind": "Need" | "Offer" | "Query",
     *   "expiry": null | <unix-seconds>
     * }
     * ```
     *
     * `match_spec` is parsed via the canonical `dregg_intent::MatchSpec`
     * serde shape, so the field names are exactly those of the Rust type.
     * The extension already coerces its inbound MatchSpec to this shape
     * for `dregg:postIntent` / `compute_intent_id`, so the same payload
     * flows through here.
     *
     * Returns JSON: `{ intent_id: <hex>, encrypted_intent_bytes: Uint8Array,
     * expiry: u64|null }`. `encrypted_intent_bytes` is the postcard-serialized
     * `EncryptedIntent`, ready for gossip propagation or for the extension
     * to forward to `/intents/encrypted` (or equivalent transport).
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_post_encrypted_intent(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_post_encrypted_intent(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_post_encrypted_intent = cipherclerk_post_encrypted_intent;

    /**
     * Build a private-transfer turn via the canonical SDK path
     * (`AgentCipherclerk::private_transfer`). The turn carries a Pedersen value
     * commitment (amount hidden) addressed to a freshly-derived stealth
     * one-time pubkey for the recipient meta-address.
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes as number[]],
     *   "amount": <u64>,
     *   "asset_type": <u64>,
     *   "recipient_meta": {
     *     "spend_pubkey": [32 bytes as number[]],
     *     "view_pubkey":  [32 bytes as number[]]
     *   }
     * }
     * ```
     *
     * Returns JSON: `{ turn_id: <hex>, turn_bytes: Uint8Array,
     * agent_cell_id: <hex> }`. `turn_bytes` is the postcard-serialized
     * `Turn` ready for `/turns/submit`.
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_private_transfer(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_private_transfer(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_private_transfer = cipherclerk_private_transfer;

    /**
     * DFA compile/eval stub. In full: delegates to dregg_dfa::compiler + air.
     * For inspector <dregg-dfa> + relay/pubsub. Returns placeholder shape today.
     * @param {string} _pattern_json
     * @returns {any}
     */
    function compile_dfa(_pattern_json) {
        const ptr0 = passStringToWasm0(_pattern_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.compile_dfa(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.compile_dfa = compile_dfa;

    /**
     * Compose multiple proofs using AND/OR/Chain/Aggregate strategies.
     *
     * `proofs_json`: JSON array of proof objects { proof_json, public_inputs }
     * `mode`: "and" | "or" | "chain" | "aggregate"
     *
     * Returns JSON: { composed_proof, mode, input_count, valid }
     * @param {string} proofs_json
     * @param {string} mode
     * @returns {any}
     */
    function compose_proofs(proofs_json, mode) {
        const ptr0 = passStringToWasm0(proofs_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(mode, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.compose_proofs(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.compose_proofs = compose_proofs;

    /**
     * Compute a canonical intent ID exactly as the Rust intent engine does.
     *
     * Takes a JSON object with: kind, actions, resource_pattern, constraints, expiry, creator.
     * Returns the hex-encoded 32-byte BLAKE3 intent ID using postcard serialization,
     * identical to `Intent::compute_id()` in the `dregg-intent` crate.
     *
     * JSON schema:
     * ```json
     * {
     *   "kind": "Need" | "Offer" | "Query",
     *   "actions": [{"action": "read", "resource": "docs/*"}, ...],
     *   "constraints": [{"AppId": "x"}, {"Service": "y"}, ...],
     *   "min_budget": null | 1000,
     *   "resource_pattern": null | "docs/*",
     *   "compound": null | [{ "actions": [...], ... }],
     *   "expiry": 1716000000,
     *   "creator": [170, 170, ...] (32 bytes),
     *   "stake_commitment": null | [1, 2, 3, ...] (32 bytes)
     * }
     * ```
     * @param {string} intent_json
     * @returns {string}
     */
    function compute_intent_id(intent_json) {
        let deferred3_0;
        let deferred3_1;
        try {
            const ptr0 = passStringToWasm0(intent_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.compute_intent_id(ptr0, len0);
            var ptr2 = ret[0];
            var len2 = ret[1];
            if (ret[3]) {
                ptr2 = 0; len2 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred3_0 = ptr2;
            deferred3_1 = len2;
            return getStringFromWasm0(ptr2, len2);
        } finally {
            wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
        }
    }
    exports.compute_intent_id = compute_intent_id;

    /**
     * Compute a Merkle root from a list of leaf strings.
     *
     * Returns JSON: { "root_hex": "...", "num_leaves": N, "tree_depth": D }
     * @param {string} leaves_json
     * @returns {any}
     */
    function compute_merkle_root(leaves_json) {
        const ptr0 = passStringToWasm0(leaves_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.compute_merkle_root(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.compute_merkle_root = compute_merkle_root;

    /**
     * Create an agent (cipherclerk + cell) in the runtime.
     * Returns the agent index (handle).
     *
     * Genesis (agent 0) is birth-by-fiat: the ledger inserts the root cell
     * directly because no signer exists yet. Subsequent agents are minted
     * via `Effect::CreateCellFromFactory` against the runtime's default
     * test-cipherclerk factory — the canonical constructor-transparency path.
     * To mint from a specific factory, use
     * [`create_agent_with_factory`] / [`deploy_factory_descriptor`].
     * @param {number} handle
     * @param {string} name
     * @param {bigint} initial_balance
     * @returns {any}
     */
    function create_agent(handle, name, initial_balance) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.create_agent(handle, ptr0, len0, initial_balance);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_agent = create_agent;

    /**
     * Create an agent whose cell is minted from a specific factory VK
     * (instead of the runtime's default test-cipherclerk factory).
     *
     * The factory must have been deployed via
     * [`deploy_factory_descriptor`]. The new cell carries a `Provenance`
     * record pointing at this factory, so a downstream `verify_provenance`
     * against the named factory set will return true.
     *
     * Genesis (the first agent in the runtime) cannot be born from a
     * factory — no signer exists yet. This binding always returns an error
     * for agent index 0; create the genesis agent via [`create_agent`]
     * first, then mint subsequent agents from your factory.
     * @param {number} handle
     * @param {string} name
     * @param {bigint} initial_balance
     * @param {string} factory_vk_hex
     * @returns {any}
     */
    function create_agent_with_factory(handle, name, initial_balance, factory_vk_hex) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(factory_vk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.create_agent_with_factory(handle, ptr0, len0, initial_balance, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_agent_with_factory = create_agent_with_factory;

    /**
     * Create a bearer capability proof.
     *
     * P1 audit fix: the previous version produced
     * `BLAKE3("dregg-bearer-cap-v1", delegator_pubkey || target || action || expiry)`,
     * which used **public** material only — anyone could forge a "bearer token"
     * by recomputing the same hash. This was not a bearer capability; it was a
     * content-addressable label.
     *
     * The new bearer cap is an Ed25519 signature by the delegator over a binding
     * hash over `(delegator_pubkey, target_cell, action, expiry)`. Only the
     * delegator can issue (they hold the signing key); anyone with the delegator
     * pubkey can verify.
     *
     * `delegator_signing_key_hex`: 32-byte Ed25519 secret seed (held in
     *   `Zeroizing`; do not pass material you don't control).
     * `target_cell_hex`: 32-byte hex ID of the cell being targeted.
     * `action_name`: the action to authorize (e.g., "transfer", "read").
     * `expiry`: Unix timestamp after which the cap expires (0 = no expiry).
     *
     * Returns JSON: `{ bearer_token_hex (64-byte Ed25519 sig), delegator_pubkey_hex,
     * binding_hex, target_cell, action, expiry }`
     * @param {string} delegator_signing_key_hex
     * @param {string} target_cell_hex
     * @param {string} action_name
     * @param {bigint} expiry
     * @returns {any}
     */
    function create_bearer_cap(delegator_signing_key_hex, target_cell_hex, action_name, expiry) {
        const ptr0 = passStringToWasm0(delegator_signing_key_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(target_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(action_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.create_bearer_cap(ptr0, len0, ptr1, len1, ptr2, len2, expiry);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_bearer_cap = create_bearer_cap;

    /**
     * Create a *real* `BearerCapProof` (SignedDelegation variant) usable in
     * canonical turns / `Authorization::Bearer`.
     *
     * Extended (FOLLOWUP-14 inspector cluster): supports optional revocation_channel
     * and allowed_effects facet mask for full capability model integration with
     * <dregg-revocation-channel> and facet attenuation. Empty rev hex or mask=0 means absent.
     *
     * Returns JSON-serialized BearerCapProof (matches the shape already
     * surfaced in AuthorizationView and TurnReceipt actions).
     * @param {string} delegator_signing_key_hex
     * @param {string} target_cell_hex
     * @param {string} permissions
     * @param {string} bearer_pubkey_hex
     * @param {bigint} expires_at
     * @param {string} federation_id_hex
     * @param {string} revocation_channel_hex
     * @param {number} allowed_effects_mask
     * @returns {any}
     */
    function create_bearer_cap_proof(delegator_signing_key_hex, target_cell_hex, permissions, bearer_pubkey_hex, expires_at, federation_id_hex, revocation_channel_hex, allowed_effects_mask) {
        const ptr0 = passStringToWasm0(delegator_signing_key_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(target_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(permissions, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(bearer_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ptr4 = passStringToWasm0(federation_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len4 = WASM_VECTOR_LEN;
        const ptr5 = passStringToWasm0(revocation_channel_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len5 = WASM_VECTOR_LEN;
        const ret = wasm.create_bearer_cap_proof(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, expires_at, ptr4, len4, ptr5, len5, allowed_effects_mask);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_bearer_cap_proof = create_bearer_cap_proof;

    /**
     * Create a cell in the runtime via a real `Effect::CreateCell` turn issued
     * by the genesis agent (agent 0). Requires at least one agent to exist as
     * the signer — if there are none, returns an error.
     *
     * `owner_pk` is a 32-byte public key (hex string).
     * Returns JSON with the cell_id.
     * @param {number} handle
     * @param {string} owner_pk_hex
     * @param {bigint} initial_balance
     * @returns {any}
     */
    function create_cell(handle, owner_pk_hex, initial_balance) {
        const ptr0 = passStringToWasm0(owner_pk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.create_cell(handle, ptr0, len0, initial_balance);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_cell = create_cell;

    /**
     * Create a federation with `num_nodes` real federation nodes. Each node has
     * a freshly generated Ed25519 keypair and an empty `RevocationTree`. The
     * federation index is its handle for subsequent calls.
     * @param {number} handle
     * @param {string} name
     * @param {number} num_nodes
     * @returns {any}
     */
    function create_federation(handle, name, num_nodes) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.create_federation(handle, ptr0, len0, num_nodes);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_federation = create_federation;

    /**
     * Create a cell from a factory descriptor.
     *
     * Validates the creation parameters against the factory constraints and
     * returns the derived child cell VK hash.
     *
     * `factory_descriptor_json`: JSON representation of the factory descriptor
     * `params_json`: JSON of creation parameters (initial_balance, field_inits)
     *
     * Returns JSON: { child_vk, param_hash, factory_vk }
     * @param {string} factory_vk_hex
     * @param {string} owner_pubkey_hex
     * @param {bigint} _initial_balance
     * @returns {any}
     */
    function create_from_factory(factory_vk_hex, owner_pubkey_hex, _initial_balance) {
        const ptr0 = passStringToWasm0(factory_vk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(owner_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.create_from_factory(ptr0, len0, ptr1, len1, _initial_balance);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_from_factory = create_from_factory;

    /**
     * Create an intent.
     *
     * `kind`: "Need", "Offer", or "Query"
     * `actions_json`: `[{"action": "read", "resource": "docs/*"}, ...]`
     * `constraints_json`: `[{"AppId": "x"}, {"Service": "y"}, ...]`
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} kind
     * @param {string} actions_json
     * @param {string} constraints_json
     * @param {string} resource_pattern
     * @param {bigint} expiry
     * @returns {any}
     */
    function create_intent(handle, agent_index, kind, actions_json, constraints_json, resource_pattern, expiry) {
        const ptr0 = passStringToWasm0(kind, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(constraints_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(resource_pattern, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.create_intent(handle, agent_index, ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, expiry);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_intent = create_intent;

    /**
     * Create a note commitment for an agent.
     * @param {number} handle
     * @param {number} agent_index
     * @param {bigint} value
     * @param {bigint} asset_type
     * @returns {any}
     */
    function create_note(handle, agent_index, value, asset_type) {
        const ret = wasm.create_note(handle, agent_index, value, asset_type);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_note = create_note;

    /**
     * Sign a state-transition for the named agent's exchange session and
     * return the postcard-encoded `PeerStateTransition` bytes. Bytes — not
     * JSON — because the whole point is a compact signed blob that can be
     * base64-encoded for paste UX.
     * @param {number} handle
     * @param {number} agent_idx
     * @param {string} old_commit_hex
     * @param {string} new_commit_hex
     * @param {string} effects_hash_hex
     * @returns {Uint8Array}
     */
    function create_peer_transition(handle, agent_idx, old_commit_hex, new_commit_hex, effects_hash_hex) {
        const ptr0 = passStringToWasm0(old_commit_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(new_commit_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(effects_hash_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.create_peer_transition(handle, agent_idx, ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[3]) {
            throw takeFromExternrefTable0(ret[2]);
        }
        var v4 = getArrayU8FromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
        return v4;
    }
    exports.create_peer_transition = create_peer_transition;

    /**
     * Create a revocation channel for an agent.
     * @param {number} handle
     * @param {number} revoker_agent
     * @returns {any}
     */
    function create_revocation_channel(handle, revoker_agent) {
        const ret = wasm.create_revocation_channel(handle, revoker_agent);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_revocation_channel = create_revocation_channel;

    /**
     * Create a new DreggRuntime and return its handle.
     * @returns {number}
     */
    function create_runtime() {
        const ret = wasm.create_runtime();
        return ret >>> 0;
    }
    exports.create_runtime = create_runtime;

    /**
     * Create a one-time stealth address for a recipient.
     *
     * Implements the stealth address protocol using X25519 DH:
     * 1. Generate ephemeral X25519 keypair
     * 2. Compute shared_secret = X25519(ephemeral_priv, recipient_view_pubkey)
     * 3. Derive scalar = BLAKE3(shared_secret, "dregg-stealth-derive")
     * 4. one_time_pubkey = H(scalar || spend_pubkey) (simplified for WASM)
     *
     * Returns JSON: { one_time_pubkey, ephemeral_pubkey }
     * @param {Uint8Array} recipient_spend_pubkey
     * @param {Uint8Array} recipient_view_pubkey
     * @returns {any}
     */
    function create_stealth_address(recipient_spend_pubkey, recipient_view_pubkey) {
        const ptr0 = passArray8ToWasm0(recipient_spend_pubkey, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(recipient_view_pubkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.create_stealth_address(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_stealth_address = create_stealth_address;

    /**
     * Create a Pedersen-style value commitment.
     *
     * Uses BLAKE3-based commitment: C = H(value || blinding).
     * Returns JSON: { commitment: Vec<u8>, blinding: Vec<u8> }
     * @param {bigint} amount
     * @param {Uint8Array} blinding
     * @returns {any}
     */
    function create_value_commitment(amount, blinding) {
        const ptr0 = passArray8ToWasm0(blinding, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.create_value_commitment(amount, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_value_commitment = create_value_commitment;

    /**
     * Postcard-decode a `PeerStateTransition` and return its fields as a
     * structured JS object. The transition_bytes are the raw postcard bytes
     * returned by `create_peer_transition`.
     *
     * Returns `{ cell_id, old_commitment, new_commitment, effects_hash,
     *   timestamp, sequence, signature, has_transition_proof }`.
     * Full proof bytes are NOT included by default (too large for render);
     * `has_transition_proof: bool` tells the inspector whether one is
     * attached.
     * @param {Uint8Array} bytes
     * @returns {any}
     */
    function decode_peer_transition(bytes) {
        const ptr0 = passArray8ToWasm0(bytes, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.decode_peer_transition(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.decode_peer_transition = decode_peer_transition;

    /**
     * Return the VK of the runtime's default test-cipherclerk factory — the
     * factory used by `create_agent` / `create_cell` when no explicit
     * factory is named.
     *
     * Exposed so the JS layer can pre-register the wasm-runtime factory
     * set with `verifyProvenance` (or display the wasm-runtime's
     * constructor-transparency anchor in the inspector UI).
     * @param {number} handle
     * @returns {any}
     */
    function default_factory_vk(handle) {
        const ret = wasm.default_factory_vk(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.default_factory_vk = default_factory_vk;

    /**
     * Create a token state, attenuate it, and return the fold chain info.
     *
     * `facts_json`: array of strings like "predicate:term1:term2"
     * `remove_json`: array of strings (facts to remove in attenuation)
     *
     * Returns JSON with old_root, new_root, verification status.
     * @param {string} facts_json
     * @param {string} remove_json
     * @returns {any}
     */
    function demonstrate_fold(facts_json, remove_json) {
        const ptr0 = passStringToWasm0(facts_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(remove_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.demonstrate_fold(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.demonstrate_fold = demonstrate_fold;

    /**
     * Deploy a factory descriptor into the runtime, returning the
     * `factory_vk` that addresses it. The factory_vk can then be passed to
     * [`create_agent_with_factory`] (or to JS-side `createFromFactory`)
     * to mint cells from this factory.
     *
     * `descriptor_json` is a serde-serialized `FactoryDescriptor`. Apps
     * that ship their own factories can call this at boot to register them
     * alongside the runtime's default test-cipherclerk factory.
     * @param {number} handle
     * @param {string} descriptor_json
     * @returns {any}
     */
    function deploy_factory_descriptor(handle, descriptor_json) {
        const ptr0 = passStringToWasm0(descriptor_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.deploy_factory_descriptor(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.deploy_factory_descriptor = deploy_factory_descriptor;

    /**
     * Derive an Ed25519 keypair from a BIP39 mnemonic using the dregg BLAKE3 derivation path.
     *
     * This uses the same BLAKE3-based derivation as `dregg-sdk`'s `mnemonic_to_seed` +
     * `derive_keypair`. The Ed25519 public key is computed in-WASM via ed25519-dalek.
     *
     * Returns an object `{ public_key: Vec<u8>(32), secret_key: Vec<u8>(32) }`.
     *
     * # Arguments
     * * `mnemonic` - A 24-word BIP39 mnemonic string.
     * * `passphrase` - Optional passphrase (use empty string for none).
     *
     * # Errors
     * Returns an error if the mnemonic is invalid.
     *
     * # Security
     * Intermediate seed material is wrapped in `Zeroizing` to scrub linear-memory
     * residues on drop. The returned secret/public key bytes are necessarily
     * copied into a JS object by `serde_wasm_bindgen`; callers in background
     * workers should overwrite or drop those buffers when done.
     * @param {string} mnemonic
     * @param {string} passphrase
     * @returns {any}
     */
    function derive_keypair_from_mnemonic(mnemonic, passphrase) {
        const ptr0 = passStringToWasm0(mnemonic, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(passphrase, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.derive_keypair_from_mnemonic(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.derive_keypair_from_mnemonic = derive_keypair_from_mnemonic;

    /**
     * Derive stealth keys from a mnemonic + passphrase.
     *
     * Returns JSON: { spend_pubkey, spend_privkey, view_pubkey, view_privkey }
     * All keys are 32-byte arrays. The public keys are BLAKE3 derivations of the
     * private keys (matching the SDK's deterministic derivation). The extension uses
     * these with its own Ed25519/X25519 library for the full DH protocol.
     * @param {string} mnemonic
     * @param {string} passphrase
     * @returns {any}
     */
    function derive_stealth_keys(mnemonic, passphrase) {
        const ptr0 = passStringToWasm0(mnemonic, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(passphrase, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.derive_stealth_keys(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.derive_stealth_keys = derive_stealth_keys;

    /**
     * Alias matching the extension's expected export name.
     * @param {Uint8Array} recipient_spend_pubkey
     * @param {Uint8Array} recipient_view_pubkey
     * @returns {any}
     */
    function derive_stealth_one_time_address(recipient_spend_pubkey, recipient_view_pubkey) {
        const ptr0 = passArray8ToWasm0(recipient_spend_pubkey, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(recipient_view_pubkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.derive_stealth_one_time_address(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.derive_stealth_one_time_address = derive_stealth_one_time_address;

    /**
     * Destroy a runtime, freeing its resources. Returns true if the handle was valid.
     * @param {number} handle
     * @returns {boolean}
     */
    function destroy_runtime(handle) {
        const ret = wasm.destroy_runtime(handle);
        return ret !== 0;
    }
    exports.destroy_runtime = destroy_runtime;

    /**
     * Evaluate a Datalog authorization request against facts and rules.
     *
     * `facts_json`: array of { "predicate": "name", "terms": ["const1", "const2"] }
     * `request_json`: { "app_id": "...", "action": "...", "service": "..." }
     *
     * Returns the full derivation trace as JSON.
     * @param {string} facts_json
     * @param {string} request_json
     * @returns {any}
     */
    function evaluate_datalog(facts_json, request_json) {
        const ptr0 = passStringToWasm0(facts_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(request_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.evaluate_datalog(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.evaluate_datalog = evaluate_datalog;

    /**
     * Build and execute a turn for an agent.
     *
     * `actions_json` is a JSON array of action descriptors:
     * ```json
     * [
     *   { "type": "transfer", "to": "<cell_id_hex>", "amount": 100 },
     *   { "type": "set_field", "cell": "<cell_id_hex>", "index": 0, "value_hex": "..." },
     *   { "type": "increment_nonce", "cell": "<cell_id_hex>" }
     * ]
     * ```
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} actions_json
     * @param {bigint} fee
     * @returns {any}
     */
    function execute_turn(handle, agent_index, actions_json, fee) {
        const ptr0 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.execute_turn(handle, agent_index, ptr0, len0, fee);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.execute_turn = execute_turn;

    /**
     * Execute a turn step-by-step and return the execution trace.
     * Same input format as `execute_turn` but returns detailed trace info.
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} actions_json
     * @param {bigint} fee
     * @returns {any}
     */
    function execute_turn_step_by_step(handle, agent_index, actions_json, fee) {
        const ptr0 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.execute_turn_step_by_step(handle, agent_index, ptr0, len0, fee);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.execute_turn_step_by_step = execute_turn_step_by_step;

    /**
     * Export runtime snapshot stub (STARBRIDGE-FOLLOWUP-03 on blocked §5.9).
     *
     * Returns pretty JSON with current state summary + explicit note that
     * this is a v0 placeholder pending the canonical WitnessedReceipt stream
     * format (Houyhnhnm + plan §8 Q4). Unblocks JS/inspector prep for
     * snapshot-and-replay / time-travel without requiring the human cargo
     * session for proving changes. Matches the Rust surface added to
     * DreggRuntime::export_runtime_snapshot_stub.
     *
     * Safe thin binding (delegates only; no new crypto, no circuit).
     * @param {number} handle
     * @returns {string}
     */
    function export_runtime_snapshot_stub(handle) {
        let deferred2_0;
        let deferred2_1;
        try {
            const ret = wasm.export_runtime_snapshot_stub(handle);
            var ptr1 = ret[0];
            var len1 = ret[1];
            if (ret[3]) {
                ptr1 = 0; len1 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred2_0 = ptr1;
            deferred2_1 = len1;
            return getStringFromWasm0(ptr1, len1);
        } finally {
            wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
        }
    }
    exports.export_runtime_snapshot_stub = export_runtime_snapshot_stub;

    /**
     * Run the full garbled circuit comparison protocol (both parties in-process for demo).
     *
     * Proves `prover_value >= verifier_threshold` without the prover learning the threshold
     * (garbled circuit approach). Both parties are simulated in-process for the playground.
     *
     * Returns JSON with: result (pass/fail), proof_size, garbling_time_ms
     * @param {number} prover_value
     * @param {number} verifier_threshold
     * @returns {any}
     */
    function garbled_compare(prover_value, verifier_threshold) {
        const ret = wasm.garbled_compare(prover_value, verifier_threshold);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.garbled_compare = garbled_compare;

    /**
     * Demo/playground only. Uses simplified linear AIR (field-addition parent
     * computation), not cryptographically sound for production. Generates a STARK
     * proof for a Merkle membership claim using `MerkleStarkAir`.
     *
     * `leaf_value` is a u32 field element, `depth` controls the Merkle tree depth (2-8).
     *
     * Returns JSON with proof bytes, generation time, proof size, etc.
     * @param {number} leaf_value
     * @param {number} depth
     * @returns {any}
     */
    function generate_demo_stark_proof(leaf_value, depth) {
        const ret = wasm.generate_demo_stark_proof(leaf_value, depth);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.generate_demo_stark_proof = generate_demo_stark_proof;

    /**
     * Generate a predicate proof for a private attribute.
     *
     * Proves a comparison statement about `private_value` vs `threshold` without
     * revealing the private value. The proof is bound to a fact commitment derived
     * from the attribute key and a state root.
     *
     * `predicate_type`: "gte", "lte", "gt", "lt", "neq"
     * `private_value`: The secret value (u32 field element)
     * `threshold`: The public comparison target (u32 field element)
     * `attribute_key`: String key used to derive the fact hash
     * `state_root`: A u32 field element representing the token state root
     *
     * Returns JSON with proof data, or an error if the predicate is not satisfiable.
     * @param {string} predicate_type
     * @param {number} private_value
     * @param {number} threshold
     * @param {string} attribute_key
     * @param {number} state_root
     * @returns {any}
     */
    function generate_predicate_proof(predicate_type, private_value, threshold, attribute_key, state_root) {
        const ptr0 = passStringToWasm0(predicate_type, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(attribute_key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.generate_predicate_proof(ptr0, len0, private_value, threshold, ptr1, len1, state_root);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.generate_predicate_proof = generate_predicate_proof;

    /**
     * Generate a range proof for a committed value.
     *
     * Returns JSON: { proof: Vec<u8>, proof_size_bytes: usize }
     * @param {bigint} amount
     * @param {Uint8Array} blinding
     * @param {Uint8Array} _commitment
     * @returns {any}
     */
    function generate_range_proof(amount, blinding, _commitment) {
        const ptr0 = passArray8ToWasm0(blinding, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(_commitment, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.generate_range_proof(amount, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.generate_range_proof = generate_range_proof;

    /**
     * Generate a random 32-byte root key and return it as hex.
     * @returns {any}
     */
    function generate_root_key() {
        const ret = wasm.generate_root_key();
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.generate_root_key = generate_root_key;

    /**
     * Generate searchable symmetric encryption (SSE) tokens from keywords.
     *
     * Returns a flat byte array: N tokens of 32 bytes each.
     * @param {string} keywords_json
     * @returns {Uint8Array}
     */
    function generate_sse_tokens(keywords_json) {
        const ptr0 = passStringToWasm0(keywords_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.generate_sse_tokens(ptr0, len0);
        if (ret[3]) {
            throw takeFromExternrefTable0(ret[2]);
        }
        var v2 = getArrayU8FromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
        return v2;
    }
    exports.generate_sse_tokens = generate_sse_tokens;

    /**
     * Get all cells in the ledger.
     * @param {number} handle
     * @returns {any}
     */
    function get_all_cells(handle) {
        const ret = wasm.get_all_cells(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_all_cells = get_all_cells;

    /**
     * Get the capability tree (CDT) for an agent's cell.
     * @param {number} handle
     * @param {number} agent_index
     * @returns {any}
     */
    function get_capability_tree(handle, agent_index) {
        const ret = wasm.get_capability_tree(handle, agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_capability_tree = get_capability_tree;

    /**
     * Get the state of a cell.
     *
     * Refactor 6: adds `program: CellProgramView` surfacing the full slot-caveat
     * tree so JS inspectors can render a complete picture of the cell's program
     * semantics. Existing fields are byte-equivalent to the prior shape.
     * @param {number} handle
     * @param {string} cell_id_hex
     * @returns {any}
     */
    function get_cell_state(handle, cell_id_hex) {
        const ptr0 = passStringToWasm0(cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.get_cell_state(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_cell_state = get_cell_state;

    /**
     * Read the current canonical state-commitment of a cell — what the agent
     * signs over when emitting a `PeerStateTransition`. Returns `null` if the
     * cell isn't in the ledger.
     * @param {number} handle
     * @param {string} cell_id_hex
     * @returns {any}
     */
    function get_cell_state_commitment(handle, cell_id_hex) {
        const ptr0 = passStringToWasm0(cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.get_cell_state_commitment(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_cell_state_commitment = get_cell_state_commitment;

    /**
     * Get the delegation graph (all capabilities across all cells).
     * @param {number} handle
     * @returns {any}
     */
    function get_delegation_graph(handle) {
        const ret = wasm.get_delegation_graph(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_delegation_graph = get_delegation_graph;

    /**
     * Get a finalized block by height (1-indexed; height 1 = first finalized
     * block). Returns `null` if the height has not been finalized.
     * @param {number} handle
     * @param {number} fed_index
     * @param {bigint} height
     * @returns {any}
     */
    function get_federation_block(handle, fed_index, height) {
        const ret = wasm.get_federation_block(handle, fed_index, height);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_federation_block = get_federation_block;

    /**
     * Get a snapshot of federation state — node count, finalized history depth,
     * latest attested root, etc. All values derived from the canonical
     * `Federation` committee + local consensus state.
     * @param {number} handle
     * @param {number} fed_index
     * @returns {any}
     */
    function get_federation_state(handle, fed_index) {
        const ret = wasm.get_federation_state(handle, fed_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_federation_state = get_federation_state;

    /**
     * Get the Merkle tree visualization data (for SVG rendering).
     * @param {number} handle
     * @returns {any}
     */
    function get_merkle_tree_viz(handle) {
        const ret = wasm.get_merkle_tree_viz(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_merkle_tree_viz = get_merkle_tree_viz;

    /**
     * List notes (commitments) for an agent. Returns array of {commitment, value, asset_type, spent}.
     * Stub for now (always []); real tracking of held notes across create/spend awaits
     * SimAgent.held_notes field + updates in runtime.rs (Wave 3 note inspector + §5.1 gaps).
     * @param {number} handle
     * @param {number} agent_index
     * @returns {any}
     */
    function get_notes(handle, agent_index) {
        const ret = wasm.get_notes(handle, agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_notes = get_notes;

    /**
     * Convenience: get the agent's PeerExchange public key. Useful for the
     * paste-UX where one side needs to share the verifying key with the
     * other up-front.
     * @param {number} handle
     * @param {number} agent_idx
     * @returns {any}
     */
    function get_peer_pubkey(handle, agent_idx) {
        const ret = wasm.get_peer_pubkey(handle, agent_idx);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_peer_pubkey = get_peer_pubkey;

    /**
     * Read the agent's current view of a peer cell — commitment, sequence,
     * timestamp. Returns `null` if the peer has not been registered.
     * @param {number} handle
     * @param {number} agent_idx
     * @param {string} peer_cell_id_hex
     * @returns {any}
     */
    function get_peer_view(handle, agent_idx, peer_cell_id_hex) {
        const ptr0 = passStringToWasm0(peer_cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.get_peer_view(handle, agent_idx, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_peer_view = get_peer_view;

    /**
     * List pending conditional turns in the runtime (for <dregg-conditional-turn>).
     * Uses the real PendingConditional vec from runtime; condition simplified to string tag.
     * @param {number} handle
     * @returns {any}
     */
    function get_pending_conditionals(handle) {
        const ret = wasm.get_pending_conditionals(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_pending_conditionals = get_pending_conditionals;

    /**
     * Get the receipt chain for the runtime.
     *
     * Refactor 3: adds `actions: Vec<ActionView>` per receipt, each with
     * `target_cell`, `method`, `effects`, and `authorization` (6-variant tagged union).
     * Refactor 7: adds `proof_view: Option<ProofView>` per receipt for γ.2 bilateral
     * PI rendering by `<dregg-proof>`.
     * Existing fields are byte-equivalent to the prior shape.
     * @param {number} handle
     * @returns {any}
     */
    function get_receipt_chain(handle) {
        const ret = wasm.get_receipt_chain(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_receipt_chain = get_receipt_chain;

    /**
     * Return the current dregg-observability event log as the Studio wire JSON
     * (schema with "schema_version", "events": [{kind, envelope, payload}, ...]).
     * This is the source for the signal-cached getter in runtime-in-memory.js
     * and the <dregg-activity> live feed inspector (Task #30).
     *
     * The log contains TurnLifecycle (at minimum; full 7 variants when deeper
     * executor hooks land) plus any future Authorization etc. events.
     * @param {number} handle
     * @returns {any}
     */
    function get_trace_events_json(handle) {
        const ret = wasm.get_trace_events_json(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_trace_events_json = get_trace_events_json;

    /**
     * Return trace steps for the committed turn identified by `turn_hash_hex`.
     * If the turn is not found in the receipt chain, returns `null`.
     *
     * Each step: `{ action_path: number[], target_cell: string, method: string,
     *   effects: string[], computrons_used: number, result: string }`.
     * @param {number} handle
     * @param {string} turn_hash_hex
     * @returns {any}
     */
    function get_turn_trace(handle, turn_hash_hex) {
        const ptr0 = passStringToWasm0(turn_hash_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.get_turn_trace(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_turn_trace = get_turn_trace;

    /**
     * Grant a capability from one agent to another.
     * @param {number} handle
     * @param {number} from_agent
     * @param {number} to_agent
     * @param {string} target_cell_hex
     * @param {string} permission
     * @returns {any}
     */
    function grant_capability(handle, from_agent, to_agent, target_cell_hex, permission) {
        const ptr0 = passStringToWasm0(target_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(permission, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.grant_capability(handle, from_agent, to_agent, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.grant_capability = grant_capability;

    /**
     * Check if a revocation channel is active.
     * @param {number} handle
     * @param {string} channel_id_hex
     * @returns {any}
     */
    function is_channel_active(handle, channel_id_hex) {
        const ptr0 = passStringToWasm0(channel_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.is_channel_active(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.is_channel_active = is_channel_active;

    /**
     * Stub for factory descriptor listing (deploy already exists; this closes the read path for <dregg-factory-descriptor>).
     * Returns the Vks + basic metadata of deployed factories in the executor.
     * @param {number} handle
     * @returns {any}
     */
    function list_deployed_factories(handle) {
        const ret = wasm.list_deployed_factories(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_deployed_factories = list_deployed_factories;

    /**
     * List all finalized block headers for a federation. Each entry is a
     * compact summary; call `get_federation_block(fed_idx, height)` for the
     * full view. Returns an empty list if nothing has been finalized.
     * @param {number} handle
     * @param {number} fed_index
     * @returns {any}
     */
    function list_federation_blocks(handle, fed_index) {
        const ret = wasm.list_federation_blocks(handle, fed_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_federation_blocks = list_federation_blocks;

    /**
     * List the KnownFederations registry (wasm/sim surface for §5.7).
     * Returns the SimFederations the runtime knows (analog to node
     * KnownFederations for the federation-list inspector).
     * @param {number} handle
     * @returns {any}
     */
    function list_known_federations(handle) {
        const ret = wasm.list_known_federations(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_known_federations = list_known_federations;

    /**
     * List all peer cell ids the agent has registered (hex strings).
     * @param {number} handle
     * @param {number} agent_idx
     * @returns {any}
     */
    function list_peers(handle, agent_idx) {
        const ret = wasm.list_peers(handle, agent_idx);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_peers = list_peers;

    /**
     * List all known revocation channels (ids + active state). Now uses real
     * RevocationChannelSet::iter() (the TODO is resolved; inspector cluster A).
     * Enables <dregg-revocation-channel> list + URI views with live state.
     * @param {number} handle
     * @returns {any}
     */
    function list_revocation_channels(handle) {
        const ret = wasm.list_revocation_channels(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_revocation_channels = list_revocation_channels;

    /**
     * Create the make_sovereign effect payload.
     *
     * Returns the BLAKE3 commitment of the cell state that the federation will store.
     * @param {string} cell_id_hex
     * @param {bigint} current_balance
     * @returns {any}
     */
    function make_cell_sovereign(cell_id_hex, current_balance) {
        const ptr0 = passStringToWasm0(cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.make_cell_sovereign(ptr0, len0, current_balance);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.make_cell_sovereign = make_cell_sovereign;

    /**
     * Match an intent against an agent's held tokens.
     * @param {number} handle
     * @param {number} intent_index
     * @param {number} agent_index
     * @returns {any}
     */
    function match_intent_for_agent(handle, intent_index, agent_index) {
        const ret = wasm.match_intent_for_agent(handle, intent_index, agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.match_intent_for_agent = match_intent_for_agent;

    /**
     * Generate a Merkle membership proof for a specific leaf.
     *
     * Returns JSON with the proof path and verification result.
     * @param {string} leaves_json
     * @param {string} target_leaf
     * @returns {any}
     */
    function merkle_membership_proof(leaves_json, target_leaf) {
        const ptr0 = passStringToWasm0(leaves_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(target_leaf, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.merkle_membership_proof(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.merkle_membership_proof = merkle_membership_proof;

    /**
     * Generate a non-membership proof for a leaf NOT in the set.
     * @param {string} leaves_json
     * @param {string} absent_leaf
     * @returns {any}
     */
    function merkle_non_membership_proof(leaves_json, absent_leaf) {
        const ptr0 = passStringToWasm0(leaves_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(absent_leaf, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.merkle_non_membership_proof(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.merkle_non_membership_proof = merkle_non_membership_proof;

    /**
     * Mint a new root macaroon token.
     *
     * Returns JSON: { "token": "<em2_...>", "key_hex": "<hex>" }
     * @param {Uint8Array} root_key
     * @param {string} location
     * @returns {any}
     */
    function mint_token(root_key, location) {
        const ptr0 = passArray8ToWasm0(root_key, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(location, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.mint_token(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.mint_token = mint_token;

    /**
     * Prepare a peer exchange with STARK proof.
     *
     * This generates the proof payload that accompanies a direct peer-to-peer
     * state exchange between two sovereign cell owners.
     *
     * Returns JSON: { exchange_id, proof_commitment, sender_cell, receiver_cell }
     * @param {string} sender_cell_hex
     * @param {string} receiver_cell_hex
     * @param {bigint} amount
     * @returns {any}
     */
    function peer_exchange_with_proof(sender_cell_hex, receiver_cell_hex, amount) {
        const ptr0 = passStringToWasm0(sender_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(receiver_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.peer_exchange_with_proof(ptr0, len0, ptr1, len1, amount);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.peer_exchange_with_proof = peer_exchange_with_proof;

    /**
     * Submit a batch of revocation events from node 0 and immediately drive
     * a consensus round. `events_json` is a JSON array of token-id strings;
     * each becomes a `RevocationEvent` signed by node 0's signing key.
     *
     * Behavioral note vs. the deleted SimFederation: real `run_consensus_round`
     * requires the leader's `pending_events` to be non-empty AND a quorum of
     * online nodes (n - floor(n/3)) to vote — proposing with no events or with
     * too few online nodes will return `block_hash: null`.
     * @param {number} handle
     * @param {number} fed_index
     * @param {string} events_json
     * @returns {any}
     */
    function propose_block(handle, fed_index, events_json) {
        const ptr0 = passStringToWasm0(events_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.propose_block(handle, fed_index, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.propose_block = propose_block;

    /**
     * Generate a blinded ring membership proof for an agent in a set.
     *
     * Proves that an agent (identified by `agent_id_hex`) is a member of the ring
     * defined by `ring_members_json` (a JSON array of hex-encoded 32-byte IDs)
     * without revealing which specific member they are.
     *
     * `agent_id_hex`: hex-encoded 32-byte agent identity
     * `ring_members_json`: JSON array of hex-encoded 32-byte member identities
     *
     * Returns JSON with: blinded_leaf, presentation_tag, set_root, ring_size, proof_size
     * @param {string} agent_id_hex
     * @param {string} ring_members_json
     * @returns {any}
     */
    function prove_anonymous_membership(agent_id_hex, ring_members_json) {
        const ptr0 = passStringToWasm0(agent_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(ring_members_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.prove_anonymous_membership(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.prove_anonymous_membership = prove_anonymous_membership;

    /**
     * Prove that a private value meets a committed threshold (value >= threshold)
     * without revealing either value to third parties.
     *
     * `value`: the prover's private attribute value (u32 field element)
     * `threshold`: the verifier's threshold (u32 field element)
     * `blinding`: randomness for the threshold commitment (u32 field element)
     *
     * Returns JSON with: proof bytes, threshold_commitment, fact_commitment, verified status.
     * Returns error if the predicate is not satisfiable (value < threshold).
     * @param {number} value
     * @param {number} threshold
     * @param {number} blinding
     * @returns {any}
     */
    function prove_committed_threshold(value, threshold, blinding) {
        const ret = wasm.prove_committed_threshold(value, threshold, blinding);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.prove_committed_threshold = prove_committed_threshold;

    /**
     * Register (or record) a federation in the runtime's known set (sim).
     * committee_pubkeys_json: array of hex pubkeys (minimal: derives n).
     * Unblocks extension `registerFederation` + list in plan §4.3/§5.7.
     * @param {number} handle
     * @param {string} name
     * @param {string} committee_pubkeys_json
     * @returns {any}
     */
    function register_federation(handle, name, committee_pubkeys_json) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(committee_pubkeys_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.register_federation(handle, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.register_federation = register_federation;

    /**
     * Register a peer cell on the named agent's exchange session, anchoring it
     * to an initial commitment that the two parties agreed on out-of-band.
     * Must be called before `verify_peer_transition` will accept transitions
     * from that peer.
     * @param {number} handle
     * @param {number} agent_idx
     * @param {string} peer_cell_id_hex
     * @param {string} peer_pubkey_hex
     * @param {string} initial_commitment_hex
     * @returns {any}
     */
    function register_peer(handle, agent_idx, peer_cell_id_hex, peer_pubkey_hex, initial_commitment_hex) {
        const ptr0 = passStringToWasm0(peer_cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(peer_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(initial_commitment_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.register_peer(handle, agent_idx, ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.register_peer = register_peer;

    /**
     * Revoke a capability by slot.
     * @param {number} handle
     * @param {number} agent_index
     * @param {number} slot
     * @returns {any}
     */
    function revoke_capability(handle, agent_index, slot) {
        const ret = wasm.revoke_capability(handle, agent_index, slot);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.revoke_capability = revoke_capability;

    /**
     * Scan a batch of stealth announcements for notes addressed to us.
     *
     * `announcements_json`: JSON array of { ephemeral_pubkey: number[], view_tag: number }
     * Returns JSON array of indices that belong to us.
     * @param {Uint8Array} view_privkey
     * @param {Uint8Array} spend_pubkey
     * @param {string} announcements_json
     * @returns {any}
     */
    function scan_stealth_announcements(view_privkey, spend_pubkey, announcements_json) {
        const ptr0 = passArray8ToWasm0(view_privkey, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(spend_pubkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(announcements_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.scan_stealth_announcements(ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.scan_stealth_announcements = scan_stealth_announcements;

    /**
     * Generate a Schnorr keypair from a random seed.
     *
     * Returns JSON: { "secret_key": [8 u32 elements], "public_key": { "x": [8], "y": [8] } }
     * @returns {any}
     */
    function schnorr_keygen() {
        const ret = wasm.schnorr_keygen();
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.schnorr_keygen = schnorr_keygen;

    /**
     * Sign a message with a Schnorr secret key.
     *
     * `secret_key_json`: JSON with { "secret_key": [32 bytes] }
     * `message`: the message string to sign
     *
     * Returns JSON with signature { "r_x": [8], "r_y": [8], "s": [8] }
     * @param {string} secret_key_json
     * @param {string} message
     * @returns {any}
     */
    function schnorr_sign(secret_key_json, message) {
        const ptr0 = passStringToWasm0(secret_key_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(message, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.schnorr_sign(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.schnorr_sign = schnorr_sign;

    /**
     * Verify a Schnorr signature.
     *
     * `public_key_json`: JSON with { "public_key_x": [8 u32], "public_key_y": [8 u32] }
     * `message`: the message string
     * `signature_json`: JSON with { "r_x": [8 u32], "r_y": [8 u32], "s": [32 bytes] }
     *
     * Returns bool: true if signature is valid.
     * @param {string} public_key_json
     * @param {string} message
     * @param {string} signature_json
     * @returns {boolean}
     */
    function schnorr_verify(public_key_json, message, signature_json) {
        const ptr0 = passStringToWasm0(public_key_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(message, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(signature_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.schnorr_verify(ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return ret[0] !== 0;
    }
    exports.schnorr_verify = schnorr_verify;

    /**
     * Seal (encrypt) an intent body for a recipient.
     *
     * A 32-byte recipient X25519 public key is **required**. The previous
     * "broadcast mode" path derived the recipient key as a deterministic BLAKE3
     * of the plaintext, which provided no confidentiality (identical plaintexts
     * produced identical ciphertexts and anyone who could guess the plaintext
     * could decrypt it). That mode has been removed.
     *
     * To send a publicly-decryptable envelope, generate a fresh ephemeral
     * X25519 keypair, encrypt to its public key, and publish the corresponding
     * private key out-of-band (or alongside the ciphertext with a clear
     * "broadcast" label).
     *
     * Returns JSON: { ciphertext, ephemeral_pubkey }
     * @param {string} plaintext_json
     * @param {Uint8Array | null} [recipient_pubkey]
     * @returns {any}
     */
    function seal_intent_body(plaintext_json, recipient_pubkey) {
        const ptr0 = passStringToWasm0(plaintext_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        var ptr1 = isLikeNone(recipient_pubkey) ? 0 : passArray8ToWasm0(recipient_pubkey, wasm.__wbindgen_malloc);
        var len1 = WASM_VECTOR_LEN;
        const ret = wasm.seal_intent_body(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.seal_intent_body = seal_intent_body;

    /**
     * Sign an arbitrary message with a 32-byte Ed25519 secret-key seed.
     *
     * Returns the 64-byte Ed25519 signature. The extension background uses this
     * to sign turn JSON when `build_turn` is unavailable (e.g., a turn type that
     * doesn't map to a canonical Effect). For canonical turn construction use
     * `build_turn` instead — it routes through `AgentCipherclerk` directly.
     *
     * `secret_key` must be exactly 32 bytes (the seed, not the full 64-byte
     * expanded key). `message` may be any length.
     *
     * Returns a `Uint8Array` of 64 signature bytes.
     * @param {Uint8Array} secret_key
     * @param {Uint8Array} message
     * @returns {Uint8Array}
     */
    function sign_message(secret_key, message) {
        const ptr0 = passArray8ToWasm0(secret_key, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(message, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.sign_message(ptr0, len0, ptr1, len1);
        if (ret[3]) {
            throw takeFromExternrefTable0(ret[2]);
        }
        var v3 = getArrayU8FromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
        return v3;
    }
    exports.sign_message = sign_message;

    /**
     * Drive a single consensus round on the federation without submitting new
     * events (events already in `pending_events` will be picked up). Returns
     * the finalized block summary or null if the round did not finalize.
     * @param {number} handle
     * @param {number} fed_index
     * @returns {any}
     */
    function simulate_consensus_round(handle, fed_index) {
        const ret = wasm.simulate_consensus_round(handle, fed_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.simulate_consensus_round = simulate_consensus_round;

    /**
     * Spend a note (reveal its nullifier).
     * @param {number} handle
     * @param {number} agent_index
     * @param {bigint} value
     * @param {bigint} asset_type
     * @returns {any}
     */
    function spend_note(handle, agent_index, value, asset_type) {
        const ret = wasm.spend_note(handle, agent_index, value, asset_type);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.spend_note = spend_note;

    /**
     * Submit a conditional turn (executes only when condition is proven).
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} actions_json
     * @param {bigint} fee
     * @param {string} condition_json
     * @param {bigint} timeout_blocks
     * @returns {any}
     */
    function submit_conditional(handle, agent_index, actions_json, fee, condition_json, timeout_blocks) {
        const ptr0 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(condition_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.submit_conditional(handle, agent_index, ptr0, len0, fee, ptr1, len1, timeout_blocks);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.submit_conditional = submit_conditional;

    /**
     * Demo/playground only. Tamper with a demo STARK proof by flipping bits in
     * the first query's trace values.
     *
     * Returns the tampered proof JSON.
     * @param {string} proof_json
     * @returns {string}
     */
    function tamper_demo_stark_proof(proof_json) {
        let deferred3_0;
        let deferred3_1;
        try {
            const ptr0 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.tamper_demo_stark_proof(ptr0, len0);
            var ptr2 = ret[0];
            var len2 = ret[1];
            if (ret[3]) {
                ptr2 = 0; len2 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred3_0 = ptr2;
            deferred3_1 = len2;
            return getStringFromWasm0(ptr2, len2);
        } finally {
            wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
        }
    }
    exports.tamper_demo_stark_proof = tamper_demo_stark_proof;

    /**
     * Trip a revocation channel.
     * @param {number} handle
     * @param {number} revoker_agent
     * @param {string} channel_id_hex
     * @returns {any}
     */
    function trip_revocation_channel(handle, revoker_agent, channel_id_hex) {
        const ptr0 = passStringToWasm0(channel_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.trip_revocation_channel(handle, revoker_agent, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.trip_revocation_channel = trip_revocation_channel;

    /**
     * Unseal (decrypt) an encrypted intent body.
     *
     * `ciphertext` and `ephemeral_pubkey` are byte arrays.
     * `privkey` is the 32-byte secret key.
     *
     * Returns the plaintext JSON string.
     * @param {Uint8Array} ciphertext
     * @param {Uint8Array} ephemeral_pubkey
     * @param {Uint8Array} privkey
     * @returns {string}
     */
    function unseal_intent_body(ciphertext, ephemeral_pubkey, privkey) {
        let deferred5_0;
        let deferred5_1;
        try {
            const ptr0 = passArray8ToWasm0(ciphertext, wasm.__wbindgen_malloc);
            const len0 = WASM_VECTOR_LEN;
            const ptr1 = passArray8ToWasm0(ephemeral_pubkey, wasm.__wbindgen_malloc);
            const len1 = WASM_VECTOR_LEN;
            const ptr2 = passArray8ToWasm0(privkey, wasm.__wbindgen_malloc);
            const len2 = WASM_VECTOR_LEN;
            const ret = wasm.unseal_intent_body(ptr0, len0, ptr1, len1, ptr2, len2);
            var ptr4 = ret[0];
            var len4 = ret[1];
            if (ret[3]) {
                ptr4 = 0; len4 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred5_0 = ptr4;
            deferred5_1 = len4;
            return getStringFromWasm0(ptr4, len4);
        } finally {
            wasm.__wbindgen_free(deferred5_0, deferred5_1, 1);
        }
    }
    exports.unseal_intent_body = unseal_intent_body;

    /**
     * Verify a bearer capability proof.
     *
     * Decodes the 64-byte Ed25519 signature from `bearer_token_hex`, recomputes
     * the binding from the claimed parameters, and checks the signature against
     * `delegator_pubkey_hex`.
     *
     * Returns JSON: `{ valid: bool, signature_valid: bool, expired: bool }`
     * @param {string} bearer_token_hex
     * @param {string} delegator_pubkey_hex
     * @param {string} target_cell_hex
     * @param {string} action_name
     * @param {bigint} expiry
     * @param {bigint} current_time
     * @returns {any}
     */
    function verify_bearer_cap(bearer_token_hex, delegator_pubkey_hex, target_cell_hex, action_name, expiry, current_time) {
        const ptr0 = passStringToWasm0(bearer_token_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(delegator_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(target_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(action_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.verify_bearer_cap(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, expiry, current_time);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_bearer_cap = verify_bearer_cap;

    /**
     * Sig-only verification of a real BearerCapProof (SignedDelegation path).
     * Does *not* perform the full executor cap-lookup / revocation / amplification
     * checks (those require a Ledger snapshot); this is the cryptographic piece
     * for inspector paste-and-verify UX. Accepts the canonical JSON shape of
     * BearerCapProof (or a minimal subset for the sig fields).
     * Returns { signature_valid, expired, valid_for_sig }.
     * @param {string} proof_json
     * @param {bigint} current_time
     * @param {string} federation_id_hex
     * @returns {any}
     */
    function verify_bearer_cap_proof_sig(proof_json, current_time, federation_id_hex) {
        const ptr0 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(federation_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_bearer_cap_proof_sig(ptr0, len0, current_time, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_bearer_cap_proof_sig = verify_bearer_cap_proof_sig;

    /**
     * Verify a committed threshold proof given the public commitments.
     *
     * `threshold_commitment`: the Poseidon2(threshold, blinding) value
     * `fact_commitment`: the binding to token state
     * `proof_json`: serialized STARK proof (from prove_committed_threshold)
     *
     * Returns JSON: { "valid": bool, "verification_time_ms": f64 }
     * @param {string} proof_json
     * @param {number} threshold_commitment
     * @param {number} fact_commitment
     * @returns {any}
     */
    function verify_committed_threshold(proof_json, threshold_commitment, fact_commitment) {
        const ptr0 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.verify_committed_threshold(ptr0, len0, threshold_commitment, fact_commitment);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_committed_threshold = verify_committed_threshold;

    /**
     * Verify a conservation proof (sum of inputs == sum of outputs).
     *
     * `input_commitments_json`: JSON array of hex-encoded 32-byte commitments
     * `output_commitments_json`: same format
     * `excess_signature_hex`: the Schnorr excess signature binding inputs to outputs
     *
     * Returns JSON: { valid: bool }
     * @param {string} input_commitments_json
     * @param {string} output_commitments_json
     * @returns {any}
     */
    function verify_conservation_proof(input_commitments_json, output_commitments_json) {
        const ptr0 = passStringToWasm0(input_commitments_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(output_commitments_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_conservation_proof(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_conservation_proof = verify_conservation_proof;

    /**
     * Demo/playground only. Uses simplified linear AIR, not cryptographically
     * sound for production. Verifies a previously generated demo STARK proof.
     *
     * Returns JSON: { "valid": bool, "error": null | "..." }
     * @param {string} proof_json
     * @returns {any}
     */
    function verify_demo_stark_proof(proof_json) {
        const ptr0 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.verify_demo_stark_proof(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_demo_stark_proof = verify_demo_stark_proof;

    /**
     * Postcard-decode a peer transition's bytes and verify it against the
     * named agent's exchange session. On success returns the updated
     * `PeerCellView` shape (with hex-encoded commitment + sequence +
     * last-updated). On rejection returns a `JsError` whose message includes
     * the typed variant name (e.g. `"InvalidSignature: invalid Ed25519
     * signature"`) so the UI can switch on the code.
     * @param {number} handle
     * @param {number} agent_idx
     * @param {Uint8Array} transition_bytes
     * @param {string} peer_pubkey_hex
     * @returns {any}
     */
    function verify_peer_transition(handle, agent_idx, transition_bytes, peer_pubkey_hex) {
        const ptr0 = passArray8ToWasm0(transition_bytes, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(peer_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_peer_transition(handle, agent_idx, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_peer_transition = verify_peer_transition;

    /**
     * Verify a predicate proof.
     *
     * `proof_json`: The serialized proof (from generate_predicate_proof).
     * `threshold`: The expected threshold.
     * `fact_commitment`: The expected fact commitment (from generate_predicate_proof output).
     *
     * Returns JSON: { "valid": bool, "error": null | "..." }
     * @param {string} proof_json
     * @param {number} threshold
     * @param {number} fact_commitment
     * @returns {any}
     */
    function verify_predicate_proof(proof_json, threshold, fact_commitment) {
        const ptr0 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.verify_predicate_proof(ptr0, len0, threshold, fact_commitment);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_predicate_proof = verify_predicate_proof;

    /**
     * Verify the provenance of a cell — check if it was created by a known factory.
     *
     * `cell_vk_hex`: the cell's verification key hash
     * `factory_vks_json`: JSON array of hex-encoded factory VK hashes
     *
     * Returns JSON: { from_factory: bool, factory_vk: string | null }
     * @param {string} cell_vk_hex
     * @param {string} factory_vks_json
     * @returns {any}
     */
    function verify_provenance(cell_vk_hex, factory_vks_json) {
        const ptr0 = passStringToWasm0(cell_vk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(factory_vks_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_provenance(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_provenance = verify_provenance;

    /**
     * Verify a macaroon token against a request.
     *
     * Returns JSON: { "allowed": bool, "policy": "...", "error": null | "..." }
     * @param {string} token_str
     * @param {Uint8Array} root_key
     * @param {string} app_id
     * @param {string} action
     * @returns {any}
     */
    function verify_token(token_str, root_key, app_id, action) {
        const ptr0 = passStringToWasm0(token_str, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(root_key, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(app_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(action, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.verify_token(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_token = verify_token;
    function __wbg_get_imports() {
        const import0 = {
            __proto__: null,
            __wbg_Error_bce6d499ff0a4aff: function(arg0, arg1) {
                const ret = Error(getStringFromWasm0(arg0, arg1));
                return ret;
            },
            __wbg_Number_b7972a139bfbfdf0: function(arg0) {
                const ret = Number(arg0);
                return ret;
            },
            __wbg_String_8564e559799eccda: function(arg0, arg1) {
                const ret = String(arg1);
                const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
                const len1 = WASM_VECTOR_LEN;
                getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
                getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
            },
            __wbg___wbindgen_is_function_5cd60d5cf78b4eef: function(arg0) {
                const ret = typeof(arg0) === 'function';
                return ret;
            },
            __wbg___wbindgen_is_object_b4593df85baada48: function(arg0) {
                const val = arg0;
                const ret = typeof(val) === 'object' && val !== null;
                return ret;
            },
            __wbg___wbindgen_is_string_dde0fd9020db4434: function(arg0) {
                const ret = typeof(arg0) === 'string';
                return ret;
            },
            __wbg___wbindgen_is_undefined_35bb9f4c7fd651d5: function(arg0) {
                const ret = arg0 === undefined;
                return ret;
            },
            __wbg___wbindgen_throw_9c31b086c2b26051: function(arg0, arg1) {
                throw new Error(getStringFromWasm0(arg0, arg1));
            },
            __wbg_call_dfde26266607c996: function() { return handleError(function (arg0, arg1, arg2) {
                const ret = arg0.call(arg1, arg2);
                return ret;
            }, arguments); },
            __wbg_crypto_38df2bab126b63dc: function(arg0) {
                const ret = arg0.crypto;
                return ret;
            },
            __wbg_getRandomValues_3f44b700395062e5: function() { return handleError(function (arg0, arg1) {
                globalThis.crypto.getRandomValues(getArrayU8FromWasm0(arg0, arg1));
            }, arguments); },
            __wbg_getRandomValues_c44a50d8cfdaebeb: function() { return handleError(function (arg0, arg1) {
                arg0.getRandomValues(arg1);
            }, arguments); },
            __wbg_instanceof_Window_faa5cf994f49cca7: function(arg0) {
                let result;
                try {
                    result = arg0 instanceof Window;
                } catch (_) {
                    result = false;
                }
                const ret = result;
                return ret;
            },
            __wbg_length_56fcd3e2b7e0299d: function(arg0) {
                const ret = arg0.length;
                return ret;
            },
            __wbg_msCrypto_bd5a034af96bcba6: function(arg0) {
                const ret = arg0.msCrypto;
                return ret;
            },
            __wbg_new_02d162bc6cf02f60: function() {
                const ret = new Object();
                return ret;
            },
            __wbg_new_070df68d66325372: function() {
                const ret = new Map();
                return ret;
            },
            __wbg_new_310879b66b6e95e1: function() {
                const ret = new Array();
                return ret;
            },
            __wbg_new_with_length_99887c91eae4abab: function(arg0) {
                const ret = new Uint8Array(arg0 >>> 0);
                return ret;
            },
            __wbg_node_84ea875411254db1: function(arg0) {
                const ret = arg0.node;
                return ret;
            },
            __wbg_now_3cd905700d21a70b: function(arg0) {
                const ret = arg0.now();
                return ret;
            },
            __wbg_now_81363d44c96dd239: function() {
                const ret = Date.now();
                return ret;
            },
            __wbg_performance_ddd4e7eeef6254f3: function(arg0) {
                const ret = arg0.performance;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_process_44c7a14e11e9f69e: function(arg0) {
                const ret = arg0.process;
                return ret;
            },
            __wbg_prototypesetcall_5f9bdc8d75e07276: function(arg0, arg1, arg2) {
                Uint8Array.prototype.set.call(getArrayU8FromWasm0(arg0, arg1), arg2);
            },
            __wbg_randomFillSync_6c25eac9869eb53c: function() { return handleError(function (arg0, arg1) {
                arg0.randomFillSync(arg1);
            }, arguments); },
            __wbg_require_b4edbdcf3e2a1ef0: function() { return handleError(function () {
                const ret = module.require;
                return ret;
            }, arguments); },
            __wbg_set_6be42768c690e380: function(arg0, arg1, arg2) {
                arg0[arg1] = arg2;
            },
            __wbg_set_78ea6a19f4818587: function(arg0, arg1, arg2) {
                arg0[arg1 >>> 0] = arg2;
            },
            __wbg_set_facb7a5914e0fa39: function(arg0, arg1, arg2) {
                const ret = arg0.set(arg1, arg2);
                return ret;
            },
            __wbg_static_accessor_GLOBAL_THIS_02344c9b09eb08a9: function() {
                const ret = typeof globalThis === 'undefined' ? null : globalThis;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_static_accessor_GLOBAL_ac6d4ac874d5cd54: function() {
                const ret = typeof global === 'undefined' ? null : global;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_static_accessor_SELF_9b2406c23aeb2023: function() {
                const ret = typeof self === 'undefined' ? null : self;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_static_accessor_WINDOW_b34d2126934e16ba: function() {
                const ret = typeof window === 'undefined' ? null : window;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_subarray_7c6a0da8f3b4a1ba: function(arg0, arg1, arg2) {
                const ret = arg0.subarray(arg1 >>> 0, arg2 >>> 0);
                return ret;
            },
            __wbg_versions_276b2795b1c6a219: function(arg0) {
                const ret = arg0.versions;
                return ret;
            },
            __wbindgen_cast_0000000000000001: function(arg0) {
                // Cast intrinsic for `F64 -> Externref`.
                const ret = arg0;
                return ret;
            },
            __wbindgen_cast_0000000000000002: function(arg0) {
                // Cast intrinsic for `I64 -> Externref`.
                const ret = arg0;
                return ret;
            },
            __wbindgen_cast_0000000000000003: function(arg0, arg1) {
                // Cast intrinsic for `Ref(Slice(U8)) -> NamedExternref("Uint8Array")`.
                const ret = getArrayU8FromWasm0(arg0, arg1);
                return ret;
            },
            __wbindgen_cast_0000000000000004: function(arg0, arg1) {
                // Cast intrinsic for `Ref(String) -> Externref`.
                const ret = getStringFromWasm0(arg0, arg1);
                return ret;
            },
            __wbindgen_cast_0000000000000005: function(arg0) {
                // Cast intrinsic for `U64 -> Externref`.
                const ret = BigInt.asUintN(64, arg0);
                return ret;
            },
            __wbindgen_init_externref_table: function() {
                const table = wasm.__wbindgen_externrefs;
                const offset = table.grow(4);
                table.set(0, undefined);
                table.set(offset + 0, undefined);
                table.set(offset + 1, null);
                table.set(offset + 2, true);
                table.set(offset + 3, false);
            },
        };
        return {
            __proto__: null,
            "./dregg_wasm_bg.js": import0,
        };
    }

    function addToExternrefTable0(obj) {
        const idx = wasm.__externref_table_alloc();
        wasm.__wbindgen_externrefs.set(idx, obj);
        return idx;
    }

    function getArrayU8FromWasm0(ptr, len) {
        ptr = ptr >>> 0;
        return getUint8ArrayMemory0().subarray(ptr / 1, ptr / 1 + len);
    }

    let cachedDataViewMemory0 = null;
    function getDataViewMemory0() {
        if (cachedDataViewMemory0 === null || cachedDataViewMemory0.buffer.detached === true || (cachedDataViewMemory0.buffer.detached === undefined && cachedDataViewMemory0.buffer !== wasm.memory.buffer)) {
            cachedDataViewMemory0 = new DataView(wasm.memory.buffer);
        }
        return cachedDataViewMemory0;
    }

    function getStringFromWasm0(ptr, len) {
        return decodeText(ptr >>> 0, len);
    }

    let cachedUint8ArrayMemory0 = null;
    function getUint8ArrayMemory0() {
        if (cachedUint8ArrayMemory0 === null || cachedUint8ArrayMemory0.byteLength === 0) {
            cachedUint8ArrayMemory0 = new Uint8Array(wasm.memory.buffer);
        }
        return cachedUint8ArrayMemory0;
    }

    function handleError(f, args) {
        try {
            return f.apply(this, args);
        } catch (e) {
            const idx = addToExternrefTable0(e);
            wasm.__wbindgen_exn_store(idx);
        }
    }

    function isLikeNone(x) {
        return x === undefined || x === null;
    }

    function passArray8ToWasm0(arg, malloc) {
        const ptr = malloc(arg.length * 1, 1) >>> 0;
        getUint8ArrayMemory0().set(arg, ptr / 1);
        WASM_VECTOR_LEN = arg.length;
        return ptr;
    }

    function passStringToWasm0(arg, malloc, realloc) {
        if (realloc === undefined) {
            const buf = cachedTextEncoder.encode(arg);
            const ptr = malloc(buf.length, 1) >>> 0;
            getUint8ArrayMemory0().subarray(ptr, ptr + buf.length).set(buf);
            WASM_VECTOR_LEN = buf.length;
            return ptr;
        }

        let len = arg.length;
        let ptr = malloc(len, 1) >>> 0;

        const mem = getUint8ArrayMemory0();

        let offset = 0;

        for (; offset < len; offset++) {
            const code = arg.charCodeAt(offset);
            if (code > 0x7F) break;
            mem[ptr + offset] = code;
        }
        if (offset !== len) {
            if (offset !== 0) {
                arg = arg.slice(offset);
            }
            ptr = realloc(ptr, len, len = offset + arg.length * 3, 1) >>> 0;
            const view = getUint8ArrayMemory0().subarray(ptr + offset, ptr + len);
            const ret = cachedTextEncoder.encodeInto(arg, view);

            offset += ret.written;
            ptr = realloc(ptr, len, offset, 1) >>> 0;
        }

        WASM_VECTOR_LEN = offset;
        return ptr;
    }

    function takeFromExternrefTable0(idx) {
        const value = wasm.__wbindgen_externrefs.get(idx);
        wasm.__externref_table_dealloc(idx);
        return value;
    }

    let cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });
    cachedTextDecoder.decode();
    function decodeText(ptr, len) {
        return cachedTextDecoder.decode(getUint8ArrayMemory0().subarray(ptr, ptr + len));
    }

    const cachedTextEncoder = new TextEncoder();

    if (!('encodeInto' in cachedTextEncoder)) {
        cachedTextEncoder.encodeInto = function (arg, view) {
            const buf = cachedTextEncoder.encode(arg);
            view.set(buf);
            return {
                read: arg.length,
                written: buf.length
            };
        };
    }

    let WASM_VECTOR_LEN = 0;

    let wasmModule, wasmInstance, wasm;
    function __wbg_finalize_init(instance, module) {
        wasmInstance = instance;
        wasm = instance.exports;
        wasmModule = module;
        cachedDataViewMemory0 = null;
        cachedUint8ArrayMemory0 = null;
        wasm.__wbindgen_start();
        return wasm;
    }

    async function __wbg_load(module, imports) {
        if (typeof Response === 'function' && module instanceof Response) {
            if (typeof WebAssembly.instantiateStreaming === 'function') {
                try {
                    return await WebAssembly.instantiateStreaming(module, imports);
                } catch (e) {
                    const validResponse = module.ok && expectedResponseType(module.type);

                    if (validResponse && module.headers.get('Content-Type') !== 'application/wasm') {
                        console.warn("`WebAssembly.instantiateStreaming` failed because your server does not serve Wasm with `application/wasm` MIME type. Falling back to `WebAssembly.instantiate` which is slower. Original error:\n", e);

                    } else { throw e; }
                }
            }

            const bytes = await module.arrayBuffer();
            return await WebAssembly.instantiate(bytes, imports);
        } else {
            const instance = await WebAssembly.instantiate(module, imports);

            if (instance instanceof WebAssembly.Instance) {
                return { instance, module };
            } else {
                return instance;
            }
        }

        function expectedResponseType(type) {
            switch (type) {
                case 'basic': case 'cors': case 'default': return true;
            }
            return false;
        }
    }

    function initSync(module) {
        if (wasm !== undefined) return wasm;


        if (module !== undefined) {
            if (Object.getPrototypeOf(module) === Object.prototype) {
                ({module} = module)
            } else {
                console.warn('using deprecated parameters for `initSync()`; pass a single object instead')
            }
        }

        const imports = __wbg_get_imports();
        if (!(module instanceof WebAssembly.Module)) {
            module = new WebAssembly.Module(module);
        }
        const instance = new WebAssembly.Instance(module, imports);
        return __wbg_finalize_init(instance, module);
    }

    async function __wbg_init(module_or_path) {
        if (wasm !== undefined) return wasm;


        if (module_or_path !== undefined) {
            if (Object.getPrototypeOf(module_or_path) === Object.prototype) {
                ({module_or_path} = module_or_path)
            } else {
                console.warn('using deprecated parameters for the initialization function; pass a single object instead')
            }
        }


        const imports = __wbg_get_imports();

        if (typeof module_or_path === 'string' || (typeof Request === 'function' && module_or_path instanceof Request) || (typeof URL === 'function' && module_or_path instanceof URL)) {
            module_or_path = fetch(module_or_path);
        }

        const { instance, module } = await __wbg_load(await module_or_path, imports);

        return __wbg_finalize_init(instance, module);
    }

    return Object.assign(__wbg_init, { initSync }, exports);
})({ __proto__: null });
