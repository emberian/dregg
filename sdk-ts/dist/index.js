"use strict";
var __defProp = Object.defineProperty;
var __getOwnPropDesc = Object.getOwnPropertyDescriptor;
var __getOwnPropNames = Object.getOwnPropertyNames;
var __hasOwnProp = Object.prototype.hasOwnProperty;
var __export = (target, all) => {
  for (var name in all)
    __defProp(target, name, { get: all[name], enumerable: true });
};
var __copyProps = (to, from, except, desc) => {
  if (from && typeof from === "object" || typeof from === "function") {
    for (let key of __getOwnPropNames(from))
      if (!__hasOwnProp.call(to, key) && key !== except)
        __defProp(to, key, { get: () => from[key], enumerable: !(desc = __getOwnPropDesc(from, key)) || desc.enumerable });
  }
  return to;
};
var __toCommonJS = (mod) => __copyProps(__defProp({}, "__esModule", { value: true }), mod);

// src/index.ts
var index_exports = {};
__export(index_exports, {
  AgentCipherclerk: () => AgentCipherclerk,
  MerkleTree: () => MerkleTree,
  PredicateEvaluator: () => PredicateEvaluator,
  ProofEngine: () => ProofEngine,
  PyanaClient: () => PyanaClient,
  PyanaRuntime: () => PyanaRuntime,
  TokenOps: () => TokenOps
});
module.exports = __toCommonJS(index_exports);

// src/cipherclerk.ts
var AgentCipherclerk = class _AgentCipherclerk {
  constructor(wasm, rootKey) {
    this.wasm = wasm;
    this.rootKey = rootKey;
  }
  /**
   * Create a new AgentCipherclerk with a randomly generated root key.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @returns A new AgentCipherclerk instance with a fresh root key.
   */
  static async create(wasm) {
    const keyResult = wasm.generate_root_key();
    const rootKey = new Uint8Array(keyResult.key_bytes);
    return new _AgentCipherclerk(wasm, rootKey);
  }
  /**
   * Create an AgentCipherclerk from an existing root key.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @param rootKey - A 32-byte root key (Uint8Array or hex string).
   * @returns A new AgentCipherclerk instance using the provided key.
   * @throws Error if the key is not exactly 32 bytes.
   */
  static fromKey(wasm, rootKey) {
    const keyBytes = typeof rootKey === "string" ? hexToBytes(rootKey) : rootKey;
    if (keyBytes.length !== 32) {
      throw new Error(
        `Root key must be exactly 32 bytes, got ${keyBytes.length}`
      );
    }
    return new _AgentCipherclerk(wasm, keyBytes);
  }
  /**
   * Get the root key as a hex string.
   */
  get keyHex() {
    return bytesToHex(this.rootKey);
  }
  /**
   * Get the raw root key bytes.
   */
  get keyBytes() {
    return new Uint8Array(this.rootKey);
  }
  /**
   * Mint a new root token for the given service/location.
   *
   * This creates an unrestricted token that can later be attenuated.
   *
   * @param location - The service name or location identifier.
   * @returns The minted token result with the encoded token string.
   * @throws Error if the WASM call fails.
   */
  async mint(location) {
    try {
      return this.wasm.mint_token(this.rootKey, location);
    } catch (e) {
      throw new Error(`Failed to mint token: ${extractError(e)}`);
    }
  }
  /**
   * Attenuate (restrict) an existing token with additional caveats.
   *
   * Attenuation is monotonic: you can only further restrict a token,
   * never broaden its permissions.
   *
   * @param tokenStr - The encoded token string to attenuate.
   * @param options - Restriction options (service, actions, expiry).
   * @returns The attenuated token result.
   * @throws Error if the token is invalid or the WASM call fails.
   */
  async attenuate(tokenStr, options = {}) {
    const service = options.service ?? "";
    const actions = options.actions ?? "";
    const expiresSecs = options.expiresSecs ?? 0;
    try {
      return this.wasm.attenuate_token(
        tokenStr,
        this.rootKey,
        service,
        actions,
        BigInt(expiresSecs)
      );
    } catch (e) {
      throw new Error(`Failed to attenuate token: ${extractError(e)}`);
    }
  }
  /**
   * Verify a token against a specific request.
   *
   * Checks all caveats (service, action, expiry) and returns whether
   * the token grants access.
   *
   * @param tokenStr - The encoded token string to verify.
   * @param options - The request to verify against.
   * @returns Verification result with allowed/denied status.
   * @throws Error if the token is malformed or the WASM call fails.
   */
  async verify(tokenStr, options = {}) {
    const appId = options.appId ?? "";
    const action = options.action ?? "";
    try {
      return this.wasm.verify_token(
        tokenStr,
        this.rootKey,
        appId,
        action
      );
    } catch (e) {
      throw new Error(`Failed to verify token: ${extractError(e)}`);
    }
  }
};
function hexToBytes(hex) {
  if (hex.length % 2 !== 0) {
    throw new Error("Hex string must have even length");
  }
  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < bytes.length; i++) {
    bytes[i] = parseInt(hex.substring(i * 2, i * 2 + 2), 16);
  }
  return bytes;
}
function bytesToHex(bytes) {
  return Array.from(bytes).map((b) => b.toString(16).padStart(2, "0")).join("");
}
function extractError(e) {
  if (e instanceof Error) return e.message;
  return String(e);
}

// src/token.ts
var TokenOps = class {
  constructor(wasm) {
    this.wasm = wasm;
  }
  /**
   * Demonstrate a fold operation: create a token state, then attenuate it
   * by removing facts, showing the Merkle root transition.
   *
   * This models the core pyana attenuation primitive where tokens can only
   * monotonically lose capabilities (facts are removed, never added).
   *
   * @param options - The facts and removal list.
   * @returns Fold result with old/new roots and verification status.
   * @throws Error if the WASM call fails.
   */
  async demonstrateFold(options) {
    const factsJson = JSON.stringify(options.facts);
    const removeJson = JSON.stringify(options.removeFacts);
    try {
      return this.wasm.demonstrate_fold(factsJson, removeJson);
    } catch (e) {
      throw new Error(`Failed to demonstrate fold: ${extractError2(e)}`);
    }
  }
  /**
   * Compute a BLAKE3 hash of an arbitrary string.
   *
   * Returns the 64-character hex digest. Uses the same BLAKE3 implementation
   * as the Rust backend for consistency.
   *
   * @param input - The string to hash.
   * @returns 64-character hex-encoded BLAKE3 digest.
   */
  blake3Hash(input) {
    return this.wasm.blake3_hash(input);
  }
  /**
   * Compute the canonical intent ID using the same algorithm as the Rust
   * intent engine (postcard serialization + BLAKE3 domain-separated hash).
   *
   * This produces a deterministic 32-byte ID that matches `Intent::compute_id()`
   * in the `pyana-intent` crate.
   *
   * @param input - The intent specification.
   * @returns 64-character hex-encoded intent ID.
   * @throws Error if the intent is malformed or serialization fails.
   */
  async computeIntentId(input) {
    const json = JSON.stringify(input);
    try {
      return this.wasm.compute_intent_id(json);
    } catch (e) {
      throw new Error(`Failed to compute intent ID: ${extractError2(e)}`);
    }
  }
  /**
   * Derive a keypair from a BIP39 mnemonic using pyana's BLAKE3 derivation path.
   *
   * Returns 64 bytes: first 32 are the secret key seed, last 32 are reserved
   * for the public key (computed externally with Ed25519).
   *
   * @param mnemonic - A 24-word BIP39 mnemonic.
   * @param passphrase - Optional passphrase (empty string for none).
   * @returns 64-byte Uint8Array with the derived key material.
   * @throws Error if the mnemonic is invalid.
   */
  async deriveKeypairFromMnemonic(mnemonic, passphrase = "") {
    try {
      return new Uint8Array(
        this.wasm.derive_keypair_from_mnemonic(mnemonic, passphrase)
      );
    } catch (e) {
      throw new Error(`Failed to derive keypair: ${extractError2(e)}`);
    }
  }
};
function extractError2(e) {
  if (e instanceof Error) return e.message;
  return String(e);
}

// src/proof.ts
var ProofEngine = class {
  constructor(wasm) {
    this.wasm = wasm;
  }
  // ==========================================================================
  // STARK Proofs
  // ==========================================================================
  /**
   * Generate a STARK proof for a Merkle membership claim.
   *
   * Creates a proof that a leaf value is part of a Merkle tree of the
   * specified depth. The proof uses FRI-based polynomial commitments.
   *
   * @param leafValue - The leaf value (u32 field element).
   * @param depth - Merkle tree depth (2-8, will be clamped).
   * @returns The proof result with serialized proof and metrics.
   * @throws Error if proof generation fails.
   */
  async generateStarkProof(leafValue, depth) {
    try {
      return this.wasm.generate_demo_stark_proof(
        leafValue,
        depth
      );
    } catch (e) {
      throw new Error(`Failed to generate STARK proof: ${extractError3(e)}`);
    }
  }
  /**
   * Verify a previously generated STARK proof.
   *
   * @param proofJson - The serialized proof JSON string.
   * @returns Verification result with valid/invalid status.
   * @throws Error if the proof JSON is malformed.
   */
  async verifyStarkProof(proofJson) {
    try {
      return this.wasm.verify_demo_stark_proof(proofJson);
    } catch (e) {
      throw new Error(`Failed to verify STARK proof: ${extractError3(e)}`);
    }
  }
  /**
   * Tamper with a STARK proof by flipping bits. Useful for testing that
   * verification correctly rejects corrupted proofs.
   *
   * @param proofJson - The original proof JSON.
   * @returns The tampered proof JSON.
   * @throws Error if the proof is malformed.
   */
  async tamperStarkProof(proofJson) {
    try {
      return this.wasm.tamper_demo_stark_proof(proofJson);
    } catch (e) {
      throw new Error(`Failed to tamper proof: ${extractError3(e)}`);
    }
  }
  // ==========================================================================
  // Predicate Proofs
  // ==========================================================================
  /**
   * Options for generating a predicate proof.
   */
  /**
   * Generate a predicate proof for a private attribute.
   *
   * Proves a comparison (e.g., age >= 18) about a private value without
   * revealing the value itself. The proof is bound to a fact commitment
   * derived from the attribute key and state root.
   *
   * @param options - The predicate parameters.
   * @returns The predicate proof result.
   * @throws Error if the predicate is not satisfiable.
   */
  async generatePredicateProof(options) {
    try {
      return this.wasm.generate_predicate_proof(
        options.predicateType,
        options.privateValue,
        options.threshold,
        options.attributeKey,
        options.stateRoot
      );
    } catch (e) {
      throw new Error(`Failed to generate predicate proof: ${extractError3(e)}`);
    }
  }
  /**
   * Verify a predicate proof.
   *
   * @param proofJson - The serialized predicate proof.
   * @param threshold - The expected threshold value.
   * @param factCommitment - The expected fact commitment.
   * @returns Whether the proof is valid.
   * @throws Error if the proof is malformed.
   */
  async verifyPredicateProof(proofJson, threshold, factCommitment) {
    try {
      return this.wasm.verify_predicate_proof(
        proofJson,
        threshold,
        factCommitment
      );
    } catch (e) {
      throw new Error(`Failed to verify predicate proof: ${extractError3(e)}`);
    }
  }
  // ==========================================================================
  // Committed Threshold Proofs
  // ==========================================================================
  /**
   * Prove that a private value meets a committed threshold (value >= threshold)
   * without revealing either value to third parties.
   *
   * The threshold is hidden behind a Poseidon2 commitment, so the verifier
   * only learns that the check passed, not what the threshold was.
   *
   * @param value - The prover's private attribute value.
   * @param threshold - The verifier's threshold.
   * @param blinding - Randomness for the threshold commitment.
   * @returns The committed threshold proof result.
   * @throws Error if the predicate is not satisfiable (value < threshold).
   */
  async proveCommittedThreshold(value, threshold, blinding) {
    try {
      return this.wasm.prove_committed_threshold(
        value,
        threshold,
        blinding
      );
    } catch (e) {
      throw new Error(
        `Failed to prove committed threshold: ${extractError3(e)}`
      );
    }
  }
  /**
   * Verify a committed threshold proof given the public commitments.
   *
   * @param proofJson - Serialized STARK proof.
   * @param thresholdCommitment - The Poseidon2(threshold, blinding) value.
   * @param factCommitment - The binding to token state.
   * @returns Whether the proof is valid.
   * @throws Error if the proof is malformed.
   */
  async verifyCommittedThreshold(proofJson, thresholdCommitment, factCommitment) {
    try {
      return this.wasm.verify_committed_threshold(
        proofJson,
        thresholdCommitment,
        factCommitment
      );
    } catch (e) {
      throw new Error(
        `Failed to verify committed threshold: ${extractError3(e)}`
      );
    }
  }
  // ==========================================================================
  // Garbled Circuit Comparison
  // ==========================================================================
  /**
   * Run the garbled circuit comparison protocol (both parties simulated in-process).
   *
   * Proves `proverValue >= verifierThreshold` without the prover learning
   * the threshold. This uses a garbled circuit approach where the verifier
   * garbles a comparison circuit and the prover evaluates it.
   *
   * @param proverValue - The prover's private value.
   * @param verifierThreshold - The verifier's private threshold.
   * @returns The comparison result with pass/fail status and proof.
   */
  async garbledCompare(proverValue, verifierThreshold) {
    try {
      return this.wasm.garbled_compare(
        proverValue,
        verifierThreshold
      );
    } catch (e) {
      throw new Error(`Failed to run garbled comparison: ${extractError3(e)}`);
    }
  }
  // ==========================================================================
  // Anonymous Membership
  // ==========================================================================
  /**
   * Generate a blinded ring membership proof.
   *
   * Proves that an agent is a member of a ring (set of identities) without
   * revealing which specific member they are. Uses Poseidon2 blinding for
   * unlinkability across sessions.
   *
   * @param agentIdHex - Hex-encoded 32-byte agent identity.
   * @param ringMembers - Array of hex-encoded 32-byte member identities.
   * @returns The anonymous membership proof result.
   * @throws Error if the agent is not in the ring or inputs are malformed.
   */
  async proveAnonymousMembership(agentIdHex, ringMembers) {
    const ringJson = JSON.stringify(ringMembers);
    try {
      return this.wasm.prove_anonymous_membership(
        agentIdHex,
        ringJson
      );
    } catch (e) {
      throw new Error(
        `Failed to prove anonymous membership: ${extractError3(e)}`
      );
    }
  }
  // ==========================================================================
  // Schnorr Signatures
  // ==========================================================================
  /**
   * Generate a Schnorr keypair on the BabyBear^8 curve.
   *
   * @returns A keypair with secret key bytes and public key coordinates.
   */
  async schnorrKeygen() {
    try {
      const result = this.wasm.schnorr_keygen();
      return {
        secret_key: new Uint8Array(result.secret_key),
        public_key_x: result.public_key_x,
        public_key_y: result.public_key_y
      };
    } catch (e) {
      throw new Error(`Failed to generate Schnorr keypair: ${extractError3(e)}`);
    }
  }
  /**
   * Sign a message with a Schnorr secret key.
   *
   * @param secretKey - The 32-byte secret key.
   * @param message - The message string to sign.
   * @returns The Schnorr signature.
   * @throws Error if the key is invalid.
   */
  async schnorrSign(secretKey, message) {
    const keyJson = JSON.stringify({
      secret_key: Array.from(secretKey)
    });
    try {
      const result = this.wasm.schnorr_sign(keyJson, message);
      return {
        r_x: result.r_x,
        r_y: result.r_y,
        s: new Uint8Array(result.s)
      };
    } catch (e) {
      throw new Error(`Failed to sign message: ${extractError3(e)}`);
    }
  }
  /**
   * Verify a Schnorr signature.
   *
   * @param publicKeyX - BabyBear8 x-coordinate (8 u32 elements).
   * @param publicKeyY - BabyBear8 y-coordinate (8 u32 elements).
   * @param message - The message that was signed.
   * @param signature - The signature to verify.
   * @returns Whether the signature is valid.
   * @throws Error if inputs are malformed.
   */
  async schnorrVerify(publicKeyX, publicKeyY, message, signature) {
    const pkJson = JSON.stringify({
      public_key_x: publicKeyX,
      public_key_y: publicKeyY
    });
    const sigJson = JSON.stringify({
      r_x: signature.r_x,
      r_y: signature.r_y,
      s: Array.from(signature.s)
    });
    try {
      return this.wasm.schnorr_verify(
        pkJson,
        message,
        sigJson
      );
    } catch (e) {
      throw new Error(`Failed to verify signature: ${extractError3(e)}`);
    }
  }
};
function extractError3(e) {
  if (e instanceof Error) return e.message;
  return String(e);
}

// src/merkle.ts
var MerkleTree = class {
  constructor(wasm) {
    this.wasm = wasm;
  }
  /**
   * Compute the Merkle root of a set of leaf strings.
   *
   * Each leaf is hashed as a unary fact with predicate "leaf" and the
   * string as the term, matching the FactSet representation.
   *
   * @param leaves - Array of leaf strings.
   * @returns The root hash and leaf count.
   * @throws Error if the input is invalid.
   */
  async computeRoot(leaves) {
    const leavesJson = JSON.stringify(leaves);
    try {
      return this.wasm.compute_merkle_root(leavesJson);
    } catch (e) {
      throw new Error(`Failed to compute Merkle root: ${extractError4(e)}`);
    }
  }
  /**
   * Generate a Merkle membership proof for a specific leaf.
   *
   * Proves that `targetLeaf` is a member of the set defined by `leaves`.
   * The proof consists of sibling hashes along the path from the leaf to the root.
   *
   * @param leaves - All leaves in the tree.
   * @param targetLeaf - The leaf to prove membership for.
   * @returns Membership proof result with the root and verification status.
   * @throws Error if the WASM call fails.
   */
  async proveMembership(leaves, targetLeaf) {
    const leavesJson = JSON.stringify(leaves);
    try {
      return this.wasm.merkle_membership_proof(
        leavesJson,
        targetLeaf
      );
    } catch (e) {
      throw new Error(
        `Failed to generate membership proof: ${extractError4(e)}`
      );
    }
  }
  /**
   * Generate a Merkle non-membership proof for a leaf NOT in the set.
   *
   * Proves that `absentLeaf` is NOT a member of the set. This is used
   * for revocation checks and negative authorization.
   *
   * @param leaves - All leaves in the tree.
   * @param absentLeaf - The leaf to prove absence for.
   * @returns Non-membership proof result.
   * @throws Error if the WASM call fails.
   */
  async proveNonMembership(leaves, absentLeaf) {
    const leavesJson = JSON.stringify(leaves);
    try {
      return this.wasm.merkle_non_membership_proof(
        leavesJson,
        absentLeaf
      );
    } catch (e) {
      throw new Error(
        `Failed to generate non-membership proof: ${extractError4(e)}`
      );
    }
  }
};
function extractError4(e) {
  if (e instanceof Error) return e.message;
  return String(e);
}

// src/predicates.ts
var PredicateEvaluator = class {
  constructor(wasm) {
    this.wasm = wasm;
  }
  /**
   * Evaluate a Datalog authorization request against a set of facts.
   *
   * Uses the standard pyana policy rules to derive an allow/deny conclusion.
   * The derivation trace is returned for debugging and auditability.
   *
   * @param facts - The facts representing the current authorization state.
   * @param request - The authorization request to evaluate.
   * @returns The evaluation result with conclusion and derivation trace.
   * @throws Error if the facts or request are malformed.
   */
  async evaluate(facts, request) {
    const factsJson = JSON.stringify(facts);
    const requestJson = JSON.stringify(request);
    try {
      return this.wasm.evaluate_datalog(
        factsJson,
        requestJson
      );
    } catch (e) {
      throw new Error(`Failed to evaluate Datalog: ${extractError5(e)}`);
    }
  }
  /**
   * Check if a specific action is allowed given a set of facts.
   *
   * Convenience method that wraps `evaluate()` and returns a boolean.
   *
   * @param facts - The authorization facts.
   * @param action - The action to check.
   * @param service - The service context (optional).
   * @param appId - The application ID (optional).
   * @returns True if the action is allowed.
   */
  async isAllowed(facts, action, service, appId) {
    const request = { action };
    if (service) request.service = service;
    if (appId) request.app_id = appId;
    const result = await this.evaluate(facts, request);
    return result.conclusion === "allow";
  }
  /**
   * Build a set of facts from a simplified permission map.
   *
   * Converts a record of `{ role: actions[] }` into Datalog facts
   * suitable for the standard policy engine.
   *
   * @param permissions - A map of role names to allowed actions.
   * @param userRole - The user's role.
   * @param userId - The user's ID.
   * @returns An array of DatalogFact objects.
   *
   * @example
   * ```ts
   * const facts = evaluator.buildFacts(
   *   { admin: ["read", "write", "delete"], viewer: ["read"] },
   *   "admin",
   *   "alice"
   * );
   * ```
   */
  buildFacts(permissions, userRole, userId) {
    const facts = [];
    facts.push({ predicate: "member", terms: [userId, userRole] });
    for (const [role, actions] of Object.entries(permissions)) {
      for (const action of actions) {
        facts.push({ predicate: "permission", terms: [role, action] });
      }
    }
    return facts;
  }
};
function extractError5(e) {
  if (e instanceof Error) return e.message;
  return String(e);
}

// src/runtime.ts
var PyanaRuntime = class {
  constructor(wasm) {
    this.destroyed = false;
    this.wasm = wasm;
    this.handle = wasm.create_runtime();
  }
  /**
   * Destroy this runtime, freeing all associated resources.
   * After calling this, the runtime instance cannot be used.
   */
  destroy() {
    if (!this.destroyed) {
      this.wasm.destroy_runtime(this.handle);
      this.destroyed = true;
    }
  }
  assertAlive() {
    if (this.destroyed) {
      throw new Error("Runtime has been destroyed");
    }
  }
  // ==========================================================================
  // Agent Management
  // ==========================================================================
  /**
   * Create an agent (cclerk + cell) in the runtime.
   *
   * The agent gets a deterministic keypair derived from their name,
   * a cell in the ledger with the specified balance, and a commitment ID
   * for intent matching.
   *
   * @param name - Display name for the agent.
   * @param initialBalance - Starting balance for the agent's cell.
   * @returns Agent info with index, cell ID, and public key.
   */
  async createAgent(name, initialBalance) {
    this.assertAlive();
    try {
      return this.wasm.create_agent(
        this.handle,
        name,
        BigInt(initialBalance)
      );
    } catch (e) {
      throw new Error(`Failed to create agent: ${extractError6(e)}`);
    }
  }
  /**
   * Mint a token for an agent (for intent matching).
   *
   * @param agentIndex - The agent's index.
   * @param resource - Resource pattern (e.g., "docs/*").
   * @param actions - Allowed actions (e.g., ["read", "write"]).
   * @param expiry - Expiry timestamp (0 for no expiry).
   * @returns The minted token info.
   */
  async mintToken(agentIndex, resource, actions, expiry = 0) {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    try {
      return this.wasm.agent_mint_token(
        this.handle,
        agentIndex,
        resource,
        actionsJson,
        BigInt(expiry)
      );
    } catch (e) {
      throw new Error(`Failed to mint token: ${extractError6(e)}`);
    }
  }
  /**
   * Attenuate an existing held token by narrowing its actions/resource.
   *
   * @param agentIndex - The agent's index.
   * @param tokenIndex - Index of the token to attenuate.
   * @param restrictActions - Actions to keep (empty = keep all).
   * @param restrictResource - New resource pattern (empty = keep original).
   * @returns The attenuated token info.
   */
  async attenuateToken(agentIndex, tokenIndex, restrictActions = [], restrictResource = "") {
    this.assertAlive();
    const actionsJson = JSON.stringify(restrictActions);
    try {
      return this.wasm.agent_attenuate(
        this.handle,
        agentIndex,
        tokenIndex,
        actionsJson,
        restrictResource
      );
    } catch (e) {
      throw new Error(`Failed to attenuate token: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Cell Operations
  // ==========================================================================
  /**
   * Get the full state of a cell.
   *
   * @param cellIdHex - Hex-encoded cell ID.
   * @returns The cell's state including balance, nonce, fields, and permissions.
   */
  async getCellState(cellIdHex) {
    this.assertAlive();
    try {
      return this.wasm.get_cell_state(
        this.handle,
        cellIdHex
      );
    } catch (e) {
      throw new Error(`Failed to get cell state: ${extractError6(e)}`);
    }
  }
  /**
   * Get all cells in the ledger.
   *
   * @returns Array of cell summaries.
   */
  async getAllCells() {
    this.assertAlive();
    try {
      return this.wasm.get_all_cells(this.handle);
    } catch (e) {
      throw new Error(`Failed to get cells: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Turn Execution
  // ==========================================================================
  /**
   * Build and execute a turn (transaction) for an agent.
   *
   * A turn consists of one or more actions (transfers, field sets, etc.)
   * that are atomically committed or rejected.
   *
   * @param agentIndex - The agent executing the turn.
   * @param actions - Array of actions to execute.
   * @param fee - Fee to pay for the turn (in computrons).
   * @returns The turn result with status and receipt.
   */
  async executeTurn(agentIndex, actions, fee = 0) {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    try {
      return this.wasm.execute_turn(
        this.handle,
        agentIndex,
        actionsJson,
        BigInt(fee)
      );
    } catch (e) {
      throw new Error(`Failed to execute turn: ${extractError6(e)}`);
    }
  }
  /**
   * Execute a turn with step-by-step tracing for debugging.
   *
   * Same as `executeTurn` but returns detailed trace information
   * about each step of execution.
   *
   * @param agentIndex - The agent executing the turn.
   * @param actions - Array of actions to execute.
   * @param fee - Fee to pay.
   * @returns Detailed trace with per-step results.
   */
  async executeTurnStepByStep(agentIndex, actions, fee = 0) {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    try {
      return this.wasm.execute_turn_step_by_step(
        this.handle,
        agentIndex,
        actionsJson,
        BigInt(fee)
      );
    } catch (e) {
      throw new Error(`Failed to execute turn (traced): ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Capabilities
  // ==========================================================================
  /**
   * Grant a capability from one agent to another.
   *
   * @param fromAgent - Index of the granting agent.
   * @param toAgent - Index of the receiving agent.
   * @param permission - Permission level to grant.
   * @param targetCellHex - Target cell (empty = from agent's cell).
   * @returns The grant result with slot number.
   */
  async grantCapability(fromAgent, toAgent, permission, targetCellHex = "") {
    this.assertAlive();
    try {
      return this.wasm.grant_capability(
        this.handle,
        fromAgent,
        toAgent,
        targetCellHex,
        permission
      );
    } catch (e) {
      throw new Error(`Failed to grant capability: ${extractError6(e)}`);
    }
  }
  /**
   * Revoke a capability by slot index.
   *
   * @param agentIndex - The agent whose capability to revoke.
   * @param slot - The capability slot number.
   * @returns Whether the revocation succeeded.
   */
  async revokeCapability(agentIndex, slot) {
    this.assertAlive();
    try {
      return this.wasm.revoke_capability(
        this.handle,
        agentIndex,
        slot
      );
    } catch (e) {
      throw new Error(`Failed to revoke capability: ${extractError6(e)}`);
    }
  }
  /**
   * Get the Capability Delegation Tree (CDT) for an agent.
   *
   * @param agentIndex - The agent's index.
   * @returns The CDT view with all capabilities.
   */
  async getCapabilityTree(agentIndex) {
    this.assertAlive();
    try {
      return this.wasm.get_capability_tree(
        this.handle,
        agentIndex
      );
    } catch (e) {
      throw new Error(`Failed to get capability tree: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Notes (Privacy-Preserving Values)
  // ==========================================================================
  /**
   * Create a note commitment for an agent.
   *
   * Notes are privacy-preserving value stores. The commitment hides
   * the value while allowing later spending with nullifier reveal.
   *
   * @param agentIndex - The agent creating the note.
   * @param value - The note's value.
   * @param assetType - The asset type identifier.
   * @returns The note commitment.
   */
  async createNote(agentIndex, value, assetType) {
    this.assertAlive();
    try {
      return this.wasm.create_note(
        this.handle,
        agentIndex,
        BigInt(value),
        BigInt(assetType)
      );
    } catch (e) {
      throw new Error(`Failed to create note: ${extractError6(e)}`);
    }
  }
  /**
   * Spend a note by revealing its nullifier.
   *
   * Double-spending is prevented by the nullifier set.
   *
   * @param agentIndex - The agent spending the note.
   * @param value - The note's value.
   * @param assetType - The asset type.
   * @returns The nullifier and spend status.
   * @throws Error if the note was already spent (double-spend).
   */
  async spendNote(agentIndex, value, assetType) {
    this.assertAlive();
    try {
      return this.wasm.spend_note(
        this.handle,
        agentIndex,
        BigInt(value),
        BigInt(assetType)
      );
    } catch (e) {
      throw new Error(`Failed to spend note: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Federation
  // ==========================================================================
  /**
   * Create a simulated federation with the specified number of nodes.
   *
   * @param name - Federation name.
   * @param numNodes - Number of validator nodes.
   * @returns Federation info with index.
   */
  async createFederation(name, numNodes) {
    this.assertAlive();
    try {
      return this.wasm.create_federation(
        this.handle,
        name,
        numNodes
      );
    } catch (e) {
      throw new Error(`Failed to create federation: ${extractError6(e)}`);
    }
  }
  /**
   * Propose a block of events to a federation.
   *
   * @param fedIndex - Federation index.
   * @param events - Array of event data strings.
   * @returns The block hash and new height.
   */
  async proposeBlock(fedIndex, events) {
    this.assertAlive();
    const eventsJson = JSON.stringify(events);
    try {
      return this.wasm.propose_block(
        this.handle,
        fedIndex,
        eventsJson
      );
    } catch (e) {
      throw new Error(`Failed to propose block: ${extractError6(e)}`);
    }
  }
  /**
   * Get the current state of a federation.
   *
   * @param fedIndex - Federation index.
   * @returns The federation state.
   */
  async getFederationState(fedIndex) {
    this.assertAlive();
    try {
      return this.wasm.get_federation_state(
        this.handle,
        fedIndex
      );
    } catch (e) {
      throw new Error(`Failed to get federation state: ${extractError6(e)}`);
    }
  }
  /**
   * Simulate a consensus round (all nodes vote and finalize).
   *
   * @param fedIndex - Federation index.
   * @returns The consensus round result.
   */
  async simulateConsensusRound(fedIndex) {
    this.assertAlive();
    try {
      return this.wasm.simulate_consensus_round(
        this.handle,
        fedIndex
      );
    } catch (e) {
      throw new Error(`Failed to simulate consensus: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Intents
  // ==========================================================================
  /**
   * Create an intent (Need, Offer, or Query).
   *
   * @param agentIndex - The creating agent's index.
   * @param kind - Intent kind: "Need", "Offer", or "Query".
   * @param actions - Action patterns to match.
   * @param constraints - Constraint specifications.
   * @param resourcePattern - Optional resource pattern.
   * @param expiry - Expiry timestamp.
   * @returns The intent info with ID and index.
   */
  async createIntent(agentIndex, kind, actions, constraints = [], resourcePattern = "", expiry = 0) {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    const constraintsJson = JSON.stringify(constraints);
    try {
      return this.wasm.create_intent(
        this.handle,
        agentIndex,
        kind,
        actionsJson,
        constraintsJson,
        resourcePattern,
        BigInt(expiry)
      );
    } catch (e) {
      throw new Error(`Failed to create intent: ${extractError6(e)}`);
    }
  }
  /**
   * Match an intent against an agent's held tokens.
   *
   * @param intentIndex - Index of the intent to match.
   * @param agentIndex - Index of the agent to match against.
   * @returns The match result.
   */
  async matchIntent(intentIndex, agentIndex) {
    this.assertAlive();
    try {
      return this.wasm.match_intent_for_agent(
        this.handle,
        intentIndex,
        agentIndex
      );
    } catch (e) {
      throw new Error(`Failed to match intent: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Conditional Turns
  // ==========================================================================
  /**
   * Submit a conditional turn that executes only when a condition is proven.
   *
   * @param agentIndex - The agent submitting the conditional.
   * @param actions - Actions to execute if condition is met.
   * @param fee - Fee to pay.
   * @param condition - The proof condition that must be satisfied.
   * @param timeoutBlocks - Number of blocks before timeout.
   * @returns The conditional turn ID and timeout height.
   */
  async submitConditional(agentIndex, actions, fee, condition, timeoutBlocks) {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    const conditionJson = JSON.stringify(condition);
    try {
      return this.wasm.submit_conditional(
        this.handle,
        agentIndex,
        actionsJson,
        BigInt(fee),
        conditionJson,
        BigInt(timeoutBlocks)
      );
    } catch (e) {
      throw new Error(`Failed to submit conditional: ${extractError6(e)}`);
    }
  }
  /**
   * Advance the block height (for timeout simulation).
   *
   * @param blocks - Number of blocks to advance.
   * @returns The new height and timestamp.
   */
  async advanceHeight(blocks) {
    this.assertAlive();
    try {
      return this.wasm.advance_height(
        this.handle,
        BigInt(blocks)
      );
    } catch (e) {
      throw new Error(`Failed to advance height: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Revocation Channels
  // ==========================================================================
  /**
   * Create a revocation channel for an agent.
   *
   * Revocation channels allow an agent to instantly invalidate
   * all capabilities delegated through that channel.
   *
   * @param revokerAgent - The agent who can trigger revocation.
   * @returns The channel ID.
   */
  async createRevocationChannel(revokerAgent) {
    this.assertAlive();
    try {
      return this.wasm.create_revocation_channel(
        this.handle,
        revokerAgent
      );
    } catch (e) {
      throw new Error(`Failed to create revocation channel: ${extractError6(e)}`);
    }
  }
  /**
   * Trip (activate) a revocation channel, invalidating all associated capabilities.
   *
   * @param revokerAgent - The agent triggering revocation.
   * @param channelIdHex - Hex-encoded channel ID.
   * @returns Whether the trip succeeded.
   */
  async tripRevocationChannel(revokerAgent, channelIdHex) {
    this.assertAlive();
    try {
      return this.wasm.trip_revocation_channel(
        this.handle,
        revokerAgent,
        channelIdHex
      );
    } catch (e) {
      throw new Error(`Failed to trip channel: ${extractError6(e)}`);
    }
  }
  /**
   * Check if a revocation channel is still active (not tripped).
   *
   * @param channelIdHex - Hex-encoded channel ID.
   * @returns Active status.
   */
  async isChannelActive(channelIdHex) {
    this.assertAlive();
    try {
      return this.wasm.is_channel_active(
        this.handle,
        channelIdHex
      );
    } catch (e) {
      throw new Error(`Failed to check channel: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Visualization Helpers
  // ==========================================================================
  /**
   * Get the Merkle tree visualization data for the ledger.
   *
   * @returns Tree visualization info (root, leaf count, type).
   */
  async getMerkleTreeViz() {
    this.assertAlive();
    try {
      return this.wasm.get_merkle_tree_viz(this.handle);
    } catch (e) {
      throw new Error(`Failed to get tree viz: ${extractError6(e)}`);
    }
  }
  /**
   * Get the full receipt chain (all committed turn receipts).
   *
   * @returns Array of receipt entries in order.
   */
  async getReceiptChain() {
    this.assertAlive();
    try {
      return this.wasm.get_receipt_chain(
        this.handle
      );
    } catch (e) {
      throw new Error(`Failed to get receipt chain: ${extractError6(e)}`);
    }
  }
  /**
   * Get the delegation graph (all capability edges across all cells).
   *
   * Useful for visualizing the authorization topology.
   *
   * @returns Graph with nodes and edges.
   */
  async getDelegationGraph() {
    this.assertAlive();
    try {
      return this.wasm.get_delegation_graph(
        this.handle
      );
    } catch (e) {
      throw new Error(`Failed to get delegation graph: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Cell creation (non-agent paths)
  // ==========================================================================
  /**
   * Create a cell in the runtime via a real `Effect::CreateCell` turn issued
   * by the genesis agent (agent 0).
   *
   * @param ownerPkHex - 32-byte owner public key as a hex string.
   * @param initialBalance - Starting balance.
   * @returns The new cell ID.
   */
  async createCell(ownerPkHex, initialBalance) {
    this.assertAlive();
    try {
      return this.wasm.create_cell(
        this.handle,
        ownerPkHex,
        BigInt(initialBalance)
      );
    } catch (e) {
      throw new Error(`Failed to create cell: ${extractError6(e)}`);
    }
  }
  /**
   * Create an agent whose cell is minted from a specific factory VK.
   *
   * The factory must have been deployed via `deployFactoryDescriptor`.
   *
   * @param name - Display name for the agent.
   * @param initialBalance - Starting balance.
   * @param factoryVkHex - Hex-encoded factory VK.
   * @returns Agent info.
   */
  async createAgentWithFactory(name, initialBalance, factoryVkHex) {
    this.assertAlive();
    try {
      return this.wasm.create_agent_with_factory(
        this.handle,
        name,
        BigInt(initialBalance),
        factoryVkHex
      );
    } catch (e) {
      throw new Error(`Failed to create agent with factory: ${extractError6(e)}`);
    }
  }
  /**
   * Deploy a factory descriptor into the runtime, returning the factory VK.
   *
   * @param descriptorJson - Serde-serialized `FactoryDescriptor` JSON.
   * @returns The factory VK that addresses the deployed descriptor.
   */
  async deployFactoryDescriptor(descriptorJson) {
    this.assertAlive();
    try {
      return this.wasm.deploy_factory_descriptor(
        this.handle,
        descriptorJson
      );
    } catch (e) {
      throw new Error(`Failed to deploy factory descriptor: ${extractError6(e)}`);
    }
  }
  /**
   * Get the VK of the runtime's default test-cipherclerk factory.
   *
   * Useful for pre-registering the wasm-runtime factory set with
   * `verify_provenance` or displaying the constructor-transparency anchor.
   *
   * @returns The default factory VK.
   */
  async defaultFactoryVk() {
    this.assertAlive();
    try {
      return this.wasm.default_factory_vk(
        this.handle
      );
    } catch (e) {
      throw new Error(`Failed to get default factory VK: ${extractError6(e)}`);
    }
  }
  /**
   * Read the current canonical state-commitment of a cell.
   *
   * Returns `null` in the `commitment` field if the cell isn't in the ledger.
   *
   * @param cellIdHex - Hex-encoded cell ID.
   * @returns The current state commitment.
   */
  async getCellStateCommitment(cellIdHex) {
    this.assertAlive();
    try {
      return this.wasm.get_cell_state_commitment(
        this.handle,
        cellIdHex
      );
    } catch (e) {
      throw new Error(`Failed to get cell state commitment: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Turn trace
  // ==========================================================================
  /**
   * Return execution trace steps for a committed turn.
   *
   * @param turnHashHex - Hex-encoded turn hash (from a `TurnResultView`).
   * @returns Array of trace steps, or `null` if the turn is not in the receipt chain.
   */
  async getTurnTrace(turnHashHex) {
    this.assertAlive();
    try {
      return this.wasm.get_turn_trace(
        this.handle,
        turnHashHex
      );
    } catch (e) {
      throw new Error(`Failed to get turn trace: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Peer exchange
  // ==========================================================================
  /**
   * Register a peer cell on the named agent's exchange session.
   *
   * Must be called before `verifyPeerTransition` will accept transitions
   * from that peer.
   *
   * @param agentIdx - Agent whose session to register the peer on.
   * @param peerCellIdHex - Hex-encoded peer cell ID.
   * @param peerPubkeyHex - Hex-encoded peer Ed25519 verifying key.
   * @param initialCommitmentHex - Hex-encoded initial commitment agreed out-of-band.
   * @returns The registered peer cell view.
   */
  async registerPeer(agentIdx, peerCellIdHex, peerPubkeyHex, initialCommitmentHex) {
    this.assertAlive();
    try {
      return this.wasm.register_peer(
        this.handle,
        agentIdx,
        peerCellIdHex,
        peerPubkeyHex,
        initialCommitmentHex
      );
    } catch (e) {
      throw new Error(`Failed to register peer: ${extractError6(e)}`);
    }
  }
  /**
   * Get the agent's PeerExchange public key.
   *
   * @param agentIdx - Agent index.
   * @returns The agent's peer pubkey as a hex string.
   */
  async getPeerPubkey(agentIdx) {
    this.assertAlive();
    try {
      return this.wasm.get_peer_pubkey(
        this.handle,
        agentIdx
      );
    } catch (e) {
      throw new Error(`Failed to get peer pubkey: ${extractError6(e)}`);
    }
  }
  /**
   * Read the agent's current view of a registered peer cell.
   *
   * @param agentIdx - Agent index.
   * @param peerCellIdHex - Hex-encoded peer cell ID.
   * @returns The peer cell view, or `null` if not registered.
   */
  async getPeerView(agentIdx, peerCellIdHex) {
    this.assertAlive();
    try {
      return this.wasm.get_peer_view(
        this.handle,
        agentIdx,
        peerCellIdHex
      );
    } catch (e) {
      throw new Error(`Failed to get peer view: ${extractError6(e)}`);
    }
  }
  /**
   * List all peer cell IDs the agent has registered.
   *
   * @param agentIdx - Agent index.
   * @returns Array of hex-encoded peer cell IDs.
   */
  async listPeers(agentIdx) {
    this.assertAlive();
    try {
      return this.wasm.list_peers(
        this.handle,
        agentIdx
      );
    } catch (e) {
      throw new Error(`Failed to list peers: ${extractError6(e)}`);
    }
  }
  /**
   * Sign a state-transition for the named agent's exchange session.
   *
   * Returns raw postcard-encoded `PeerStateTransition` bytes — not JSON —
   * because the whole point is a compact signed blob for paste UX.
   *
   * @param agentIdx - Agent index.
   * @param oldCommitHex - Hex-encoded old commitment.
   * @param newCommitHex - Hex-encoded new commitment.
   * @param effectsHashHex - Hex-encoded effects bundle hash.
   * @returns Postcard-encoded transition bytes.
   */
  async createPeerTransition(agentIdx, oldCommitHex, newCommitHex, effectsHashHex) {
    this.assertAlive();
    try {
      return this.wasm.create_peer_transition(
        this.handle,
        agentIdx,
        oldCommitHex,
        newCommitHex,
        effectsHashHex
      );
    } catch (e) {
      throw new Error(`Failed to create peer transition: ${extractError6(e)}`);
    }
  }
  /**
   * Decode a `PeerStateTransition` blob into structured fields.
   *
   * @param bytes - Postcard-encoded transition bytes (from `createPeerTransition`).
   * @returns Decoded transition fields.
   */
  async decodePeerTransition(bytes) {
    this.assertAlive();
    try {
      return this.wasm.decode_peer_transition(
        bytes
      );
    } catch (e) {
      throw new Error(`Failed to decode peer transition: ${extractError6(e)}`);
    }
  }
  /**
   * Verify a peer transition against the agent's registered session.
   *
   * On success returns the updated `PeerCellView`. On failure throws with
   * the typed variant name (e.g. `"InvalidSignature: invalid Ed25519 signature"`)
   * so callers can switch on the error code.
   *
   * @param agentIdx - Agent index whose session is checked.
   * @param transitionBytes - Postcard-encoded transition bytes.
   * @param peerPubkeyHex - Hex-encoded peer verifying key.
   * @returns Updated peer cell view.
   */
  async verifyPeerTransition(agentIdx, transitionBytes, peerPubkeyHex) {
    this.assertAlive();
    try {
      return this.wasm.verify_peer_transition(
        this.handle,
        agentIdx,
        transitionBytes,
        peerPubkeyHex
      );
    } catch (e) {
      throw new Error(`Failed to verify peer transition: ${extractError6(e)}`);
    }
  }
  // ==========================================================================
  // Federation block history
  // ==========================================================================
  /**
   * Get a finalized block by height (1-indexed).
   *
   * @param fedIndex - Federation index.
   * @param height - Block height (1 = first finalized block).
   * @returns The full block view, or `null` if not yet finalized.
   */
  async getFederationBlock(fedIndex, height) {
    this.assertAlive();
    try {
      return this.wasm.get_federation_block(
        this.handle,
        fedIndex,
        BigInt(height)
      );
    } catch (e) {
      throw new Error(`Failed to get federation block: ${extractError6(e)}`);
    }
  }
  /**
   * List all finalized block headers for a federation.
   *
   * Call `getFederationBlock(fedIndex, height)` for full block contents.
   *
   * @param fedIndex - Federation index.
   * @returns Array of compact block headers (empty if nothing finalized yet).
   */
  async listFederationBlocks(fedIndex) {
    this.assertAlive();
    try {
      return this.wasm.list_federation_blocks(
        this.handle,
        fedIndex
      );
    } catch (e) {
      throw new Error(`Failed to list federation blocks: ${extractError6(e)}`);
    }
  }
};
function extractError6(e) {
  if (e instanceof Error) return e.message;
  return String(e);
}

// src/index.ts
var PyanaClient = class _PyanaClient {
  /**
   * Create a new PyanaClient. Prefer using `PyanaClient.init()` which
   * handles async cclerk creation.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @param cclerk - A pre-created AgentCipherclerk instance.
   */
  constructor(wasm, cclerk) {
    this.wasm = wasm;
    this.cclerk = cclerk;
    this.token = new TokenOps(wasm);
    this.proof = new ProofEngine(wasm);
    this.merkle = new MerkleTree(wasm);
    this.predicates = new PredicateEvaluator(wasm);
  }
  /**
   * Initialize a PyanaClient with a fresh random cclerk.
   *
   * This is the recommended way to create a client instance.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @returns A fully initialized PyanaClient.
   */
  static async init(wasm) {
    const cclerk = await AgentCipherclerk.create(wasm);
    return new _PyanaClient(wasm, cclerk);
  }
  /**
   * Initialize a PyanaClient with an existing root key.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @param rootKey - A 32-byte root key (Uint8Array or hex string).
   * @returns A PyanaClient using the provided key.
   */
  static fromKey(wasm, rootKey) {
    const cclerk = AgentCipherclerk.fromKey(wasm, rootKey);
    return new _PyanaClient(wasm, cclerk);
  }
  /**
   * Create a new PyanaRuntime for full distributed system simulation.
   *
   * The runtime provides agents, cells, turns, federations, intents,
   * notes, capabilities, and revocation channels -- all running in WASM.
   *
   * @returns A new PyanaRuntime instance.
   */
  createRuntime() {
    return new PyanaRuntime(this.wasm);
  }
};
// Annotate the CommonJS export names for ESM import in node:
0 && (module.exports = {
  AgentCipherclerk,
  MerkleTree,
  PredicateEvaluator,
  ProofEngine,
  PyanaClient,
  PyanaRuntime,
  TokenOps
});
