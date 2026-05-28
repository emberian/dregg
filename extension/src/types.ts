/**
 * Shared type definitions for the Dragon's Egg extension message protocol.
 *
 * These types ensure end-to-end type safety between page.ts <-> content.ts <-> background.ts.
 * Where possible, types are imported from/aligned with the ts-sdk definitions.
 */

// ---------------------------------------------------------------------------
// Re-export compatible types from ts-sdk conceptual model
// (The extension bundles independently, so we define locally rather than
//  importing from ts-sdk to avoid circular build deps.)
// ---------------------------------------------------------------------------

/** 64-character hex string identifying a cell. */
export type CellId = string;

/** Hex string identifying a turn. */
export type TurnId = string;

/** Operating mode of a cell. */
export type CellMode = "federated" | "sovereign";

/** Kind of intent. */
export type IntentKind = "need" | "offer" | "query";

/** Stealth meta-address (public-facing identifier for receiving private payments). */
export interface StealthMetaAddress {
  spendPubkey: number[];
  viewPubkey: number[];
}

/** Node connection configuration. */
export interface NodeConfig {
  nodeUrl: string;
  wssUrl: string;
  wsUrl: string;
  devnetKey: string;
}

// ---------------------------------------------------------------------------
// Intent / Match types
// ---------------------------------------------------------------------------

/** A constraint on an intent match. */
export interface IntentConstraint {
  type: string;
  value: string | number;
}

/** Specification for matching intents. */
export interface MatchSpec {
  actions?: Array<{ action: string; resource?: string }>;
  resourcePattern?: string;
  constraints?: IntentConstraint[];
  minBudget?: number;
  creator?: string;
  proofOfStake?: string;
}

/** An intent broadcast to the network. */
export interface Intent {
  id: string;
  kind: IntentKind;
  matcher: MatchSpec;
  expiry: number;
  createdAt: number;
  encrypted?: boolean;
}

// ---------------------------------------------------------------------------
// Token / Capability types
// ---------------------------------------------------------------------------

/** A capability token held in the cipherclerk. */
export interface CapabilityToken {
  id: string;
  actions: string[];
  resource: string;
  expiry: number | null;
  issuer: string | null;
  provisioned: number;
  appId?: string;
  service?: string;
  userId?: string;
  email?: string;
  org?: string;
  organization?: string;
  balance?: number;
  amount?: number;
  reputation?: number;
  score?: number;
  level?: number;
  depth?: number;
  delegationDepth?: number;
  budget?: number;
  attributes?: Record<string, unknown>;
  meta?: Record<string, unknown>;
}

// ---------------------------------------------------------------------------
// Message Protocol — discriminated union for all extension messages
// ---------------------------------------------------------------------------

/** All message types in the extension protocol. */
export type MessageType =
  // Core cipherclerk operations
  | "dregg:authorize"
  | "dregg:isConnected"
  | "dregg:canAuthorize"
  | "dregg:provision"
  | "dregg:subscribe"
  // Popup-only cipherclerk operations
  | "dregg:getState"
  | "dregg:lock"
  | "dregg:unlock"
  | "dregg:getCapabilities"
  | "dregg:revoke"
  | "dregg:setPassphrase"
  | "dregg:getMnemonic"
  | "dregg:recover"
  // Intent operations
  | "dregg:postIntent"
  | "dregg:offerCapability"
  | "dregg:listIntents"
  | "dregg:fulfillIntent"
  | "dregg:getFulfillableIntents"
  // Privacy operations
  | "dregg:getStealthAddress"
  | "dregg:postEncryptedIntent"
  | "dregg:privateTransfer"
  | "dregg:getPrivacyState"
  | "dregg:setCommittedTransferMode"
  | "dregg:getStealthNotes"
  // Bearer capabilities
  | "dregg:createBearerCap"
  | "dregg:verifyBearerCap"
  // Factory operations
  | "dregg:createFromFactory"
  | "dregg:verifyProvenance"
  // Sovereign cell operations
  | "dregg:makeCellSovereign"
  | "dregg:peerExchange"
  // Proof composition
  | "dregg:composeProofs"
  // Turn submission
  | "dregg:signTurn"
  | "dregg:queryBalance"
  // Node configuration
  | "dregg:getNodeConfig"
  | "dregg:setNodeConfig"
  // CapTP operations
  | "dregg:shareCapability"
  | "dregg:acceptCapability"
  | "dregg:createHandoff"
  | "dregg:getLiveRefs"
  | "dregg:dropLiveRef"
  // Directory operations
  | "dregg:mountService"
  | "dregg:discoverServices"
  | "dregg:resolvePath"
  // Storage operations
  | "dregg:storageWrite"
  | "dregg:storageRead"
  | "dregg:storageQuota"
  // Federation operations
  | "dregg:federationStatus"
  | "dregg:proposeRoutes"
  | "dregg:voteOnProposal"
  // Discovery
  | "dregg:getFederation"
  | "dregg:refreshDiscovery"
  // Origin permission
  | "dregg:requestOriginPermission"
  | "dregg:originPermissionDecision"
  | "dregg:getOriginPermissions"
  | "dregg:revokeOriginPermission"
  | "dregg:getDisclosurePrefs"
  | "dregg:clearDisclosurePref"
  // Turn v3 (pre-built postcard bytes)
  | "dregg:signTurnV3"
  // Durable offline outbox
  | "dregg:listOutbox"
  | "dregg:flushOutbox"
  | "dregg:dropOutboxEntry"
  // Federation registry
  | "dregg:registerFederation"
  | "dregg:listKnownFederations"
  // CapTP delivered authorization
  | "dregg:createCapTpDeliveredAuth"
  | "dregg:getReceiptWitnesses"
  | "dregg:getActivityFeed"  // Phase 1 debugger: activity feed for <dregg-activity>
  // Internal decision messages
  | "dregg:provisionDecision"
  | "dregg:intentConfirmation"
  | "dregg:disclosureDecision"
  // Popup-to-background: fetch the display payload registered when the popup was opened.
  | "dregg:getPendingDecision";

// ---------------------------------------------------------------------------
// Known federation types
// ---------------------------------------------------------------------------

/** A federation registered in the local KnownFederations registry. */
export interface KnownFederation {
  federationId: string;
  name: string;
  committeePubkeys: string[];
  registeredAt: number;
}

/** Canonical witnessed-receipt artifact payload from `/api/receipts/{hash}/witnesses`. */
export interface ReceiptWitnessArtifacts {
  receipt_hash: string;
  witness_count: number;
  artifact_format: "DWR1" | "legacy-json" | string;
  witness_artifacts: string[];
  witnessed_receipts?: unknown[];
}

// ---------------------------------------------------------------------------
// Authorization types
// ---------------------------------------------------------------------------

/** Request for authorization. */
export interface AuthorizeRequest {
  action: string;
  resource: string;
  mode?: "trusted" | "selective" | "private";
  requestedDisclosure?: Array<{ key: string }>;
  forceDisclosurePicker?: boolean;
  /** Internal: set by the disclosure picker flow. */
  _disclosedFacts?: string[] | null;
  _predicateFacts?: PredicateFact[] | null;
  _skipDisclosure?: boolean;
}

/** A predicate fact for zero-knowledge range proofs. */
export interface PredicateFact {
  key: string;
  predicateType: "gte" | "lte" | "gt" | "lt" | "neq";
  threshold: number;
}

/** Result of an authorization check. */
export interface AuthorizeResult {
  allowed: boolean;
  proof?: number[];
  facts?: string[];
  mode?: string;
  disclosedFacts?: string[];
  predicateProofs?: PredicateProofResult[];
  error?: string;
}

/** Result of a predicate proof generation. */
export interface PredicateProofResult {
  key: string;
  predicateType: string;
  threshold: number;
  proof: string | null;
  factCommitment?: string;
  verified?: boolean;
  proofSizeBytes?: number;
  error?: string;
}

// ---------------------------------------------------------------------------
// Cipherclerk state types
// ---------------------------------------------------------------------------

/** Public cipherclerk state (returned to popup). */
export interface CipherclerkState {
  locked: boolean;
  tokenCount: number;
  chainLength: number;
  hasMnemonic: boolean;
  mnemonicShown: boolean;
  hasPassphrase: boolean;
  needsPassphraseSetup: boolean;
  hasStealthKeys: boolean;
  stealthNotesCount: number;
}

/** Internal full cipherclerk state (in-memory). */
export interface InternalCipherclerkState {
  locked: boolean;
  publicKey: number[];
  secretKey: number[] | null;
  tokens: CapabilityToken[];
  receiptChain: string[];
  log: LogEntry[];
  hasMnemonic: boolean;
  mnemonicShown: boolean;
  needsPassphraseSetup: boolean;
  stealthMeta: StealthMetaAddress | null;
  stealthPrivate: StealthPrivateKeys | null;
  stealthNotes: StealthNote[];
}


/** Stealth private keys (stored encrypted at rest). */
export interface StealthPrivateKeys {
  spendPrivkey: number[];
  viewPrivkey: number[];
}

/** A stealth note matched to our cipherclerk. */
export interface StealthNote {
  noteId: string;
  amount: number | null;
  assetType: string;
  oneTimePrivkey: number[] | null;
  ephemeralPubkey: number[];
  memo: string | null;
  receivedAt: number;
}

/** A log entry for cipherclerk activity. */
export interface LogEntry {
  action: string;
  resource: string;
  allowed: boolean;
  timestamp: number;
  mode: string;
  turnId?: string;
  amount?: number;
  intentId?: string;
  tokenId?: string;
  disclosedFacts?: string[] | null;
  predicateFacts?: PredicateFact[] | null;
  recipientStealthMeta?: StealthMetaAddress;
}

// ---------------------------------------------------------------------------
// Turn types
// ---------------------------------------------------------------------------

/** Specification for building a turn. */
export interface TurnSpec {
  action: string;
  resource?: string;
  amount?: number;
  recipient?: string;
  metadata?: Record<string, unknown>;
}

/** Result of signing and submitting a turn. */
export interface SignTurnResult {
  turnId?: string;
  submitted: boolean;
  queued?: boolean;
  outboxId?: string;
  error?: string;
  nodeResult?: Record<string, unknown>;
}

export type OutboxStatus = "pending" | "submitting" | "submitted" | "failed";

/** Durable signed submission waiting for a node to accept it. */
export interface OutboxEntry {
  id: string;
  kind: "turn" | "encrypted_intent";
  label: string;
  endpoint: string;
  method: "POST";
  body: string;
  headers?: Record<string, string>;
  nodeUrl: string;
  turnId?: string;
  createdAt: number;
  updatedAt: number;
  attempts: number;
  nextAttemptAt: number;
  status: OutboxStatus;
  lastError?: string;
  metadata?: Record<string, unknown>;
}

// ---------------------------------------------------------------------------
// CapTP types (extension-specific)
// ---------------------------------------------------------------------------

/** A live reference held by the extension. */
export interface ExtensionLiveRef {
  refId: string;
  cellId: string;
  uri: string;
  nodeId: string;
  permissions: string;
  tabId: number | null;
  createdAt: number;
  capId: string | null;
}

// ---------------------------------------------------------------------------
// Federation / Discovery types
// ---------------------------------------------------------------------------

/** A node in the federation discovery response. */
export interface FederationNode {
  nodeId: string;
  ticket: string;
  lastSeen: number;
  role: string;
}

/** Federation state as tracked by the extension. */
export interface FederationState {
  nodes: FederationNode[];
  intentService: { nodeId: string; ticket: string; lastSeen: number } | null;
  lastUpdated: string | null;
  commit?: string;
  fetchError: string | null;
}

// ---------------------------------------------------------------------------
// Origin permission types
// ---------------------------------------------------------------------------

/** An origin permission entry in the allowlist. */
export interface OriginPermission {
  methods: string[];
  expires: number;
}

/** Origin permission display entry for the popup. */
export interface OriginPermissionDisplay {
  origin: string;
  methods: string[];
  expires: number;
  expiresIn: number | null;
}

// ---------------------------------------------------------------------------
// Disclosure picker types
// ---------------------------------------------------------------------------

/** A fact that can be disclosed from a token. */
export interface DisclosableFact {
  key: string;
  value: string | number;
  category: "permissions" | "identity" | "temporal" | "resource";
}

/** Decision from the disclosure picker popup. */
export interface DisclosureDecision {
  authorized: boolean;
  level?: "full" | "selective" | "private";
  disclosedFacts?: string[];
  remember?: boolean;
  facts?: Array<{
    index: number;
    disclosure: "reveal" | "predicate" | "hide";
    predicateType?: string;
    threshold?: number;
  }>;
}

// ---------------------------------------------------------------------------
// Storage types (extension-specific)
// ---------------------------------------------------------------------------

/** Storage quota as returned to the popup. */
export interface StorageQuotaResult {
  bytesStored: number;
  bytesLimit: number;
  computronsUsed: number;
  computronsRemaining: number;
  objectCount: number;
  error?: string;
}

// ---------------------------------------------------------------------------
// Node HTTP response wrapper
// ---------------------------------------------------------------------------

/** Result of a node HTTP request. */
export interface NodeRequestResult<T = unknown> {
  ok: boolean;
  data?: T;
  error?: string;
  status?: number;
}

// ---------------------------------------------------------------------------
// Encrypted state (at-rest format)
// ---------------------------------------------------------------------------

/** Encrypted data envelope (AES-256-GCM via PBKDF2). */
export interface EncryptedEnvelope {
  salt: number[];
  iv: number[];
  ciphertext: number[];
  /** Unencrypted public key (for UI display while locked). */
  publicKey?: number[];
  hasMnemonic?: boolean;
  needsPassphraseSetup?: boolean;
}

// ---------------------------------------------------------------------------
// WASM module interface
// ---------------------------------------------------------------------------

/**
 * Interface for the dregg WASM module exports.
 * Only the functions actually called from JS are typed here.
 */
export interface DreggWasm {
  // Mnemonic / key derivation
  generate_mnemonic(): string;
  validate_mnemonic(mnemonic: string): boolean;
  derive_keypair_from_mnemonic(
    mnemonic: string,
    passphrase: string,
    path: string,
  ): { public_key: Uint8Array; secret_key: Uint8Array };

  // Authorization / proofs
  evaluate_datalog(facts: string, request: string): { conclusion: string; steps: Array<{ rule_id: string; derived_predicate_hex: string }> };
  generate_demo_stark_proof(hash: number, depth: number): { proof_json: string };
  verify_token(payload: string, rootKey: string, appId: string, action: string): boolean;
  compute_merkle_root(leaves: string): string;
  generate_predicate_proof(
    predicateType: string,
    privateValue: number,
    threshold: number,
    key: string,
    stateRoot: number,
  ): { proof_json: string; fact_commitment: string; verified: boolean; proof_size_bytes: number };

  // Hashing
  blake3_hash(input: string): string;

  // Turn building / signing
  build_turn(params: string): { turn_id: string; turn_bytes: Uint8Array; signature?: Uint8Array };
  sign_message(privkey: Uint8Array, message: Uint8Array): Uint8Array;
  /**
   * Sign a pre-built postcard-encoded Turn via the canonical v3 path
   * (`AgentCipherclerk::sign_action`). Replaces every Unchecked action's
   * authorization with a real Ed25519 signature; re-encodes to postcard bytes.
   */
  sign_turn_v3(
    turnBytes: Uint8Array,
    senderPrivkey: Uint8Array,
    federationId: Uint8Array,
  ): {
    turn_id: string;
    /** Signed turn, postcard-encoded. */
    turn_bytes: Uint8Array;
    /** Signed turn, JSON-encoded (round-trippable; postcard Turn is not — see wasm doc). */
    turn_bytes_json: Uint8Array;
    /** Encoding the INPUT was decoded as: "postcard" | "json". */
    encoding: string;
    signer_pubkey: string;
  };
  /**
   * Build a canonical `Authorization::CapTpDelivered` envelope (postcard bytes).
   * `handoffCertB58` is the compact `dregg-handoff:<base58>` or bare base58 of
   * the cert; the three key/sig args are hex.
   */
  create_captp_delivered_auth(
    handoffCertB58: string,
    introducerPkHex: string,
    senderPkHex: string,
    senderSigHex: string,
  ): { auth_bytes: Uint8Array; recipient_pk: string; introducer_federation: string };

  // Bearer capabilities
  create_bearer_cap(delegatorKeyHex: string, targetCellHex: string, action: string, expiry: number): { bearerTokenHex: string; targetCell: string; action: string };
  verify_bearer_cap(tokenHex: string, delegatorKeyHex: string, targetCellHex: string, action: string, expiry: number, currentTime: number): { valid: boolean; expired: boolean };

  // Factory operations
  /**
   * Deterministic preview: hash-derives `(child_vk, param_hash)` from
   * `(factory_vk, owner_pubkey)` without minting a cell. Useful for
   * client-side display before submission. Does NOT produce a signed
   * turn; use `cipherclerk_create_from_factory` for that.
   */
  create_from_factory(factoryVkHex: string, ownerPubkeyHex: string, initialBalance: number): { childVk: string; paramHash: string; factoryVk: string };
  /**
   * Canonical mint path: build and sign a real
   * `Effect::CreateCellFromFactory` turn via `AgentCipherclerk::create_from_factory`.
   * The returned `turn_bytes` is the postcard-encoded Turn ready for
   * `/turns/submit`. Also surfaces `child_vk` / `param_hash` so the
   * caller can display the new cell's identity without waiting on the
   * node round-trip.
   */
  cipherclerk_create_from_factory(specJson: string): {
    turn_id: string;
    turn_bytes: Uint8Array;
    agent_cell_id: string;
    child_vk: string;
    param_hash: string;
    factory_vk: string;
  };
  verify_provenance(cellVkHex: string, knownFactoryVks: string): { fromFactory: boolean; factoryVk: string | null };

  // Sovereign cells
  make_cell_sovereign(cellIdHex: string, balance: number): { cellId: string; stateCommitment: string; mode: string };
  peer_exchange_with_proof(senderCellHex: string, receiverCellHex: string, amount: number): { exchangeId: string; proofCommitment: string };

  // Proof composition
  compose_proofs(proofsJson: string, mode: string): { composedProof: string; mode: string; inputCount: number; valid: boolean };

  // Intent ID
  compute_intent_id(intentJson: string): string;

  // Stealth addresses
  derive_stealth_keys(mnemonic: string, passphrase: string): {
    spend_pubkey: Uint8Array;
    spend_privkey: Uint8Array;
    view_pubkey: Uint8Array;
    view_privkey: Uint8Array;
  };
  check_stealth_ownership(
    viewPrivkey: Uint8Array,
    spendPubkey: Uint8Array,
    ephemeralPubkey: Uint8Array,
    oneTimePubkey: Uint8Array,
  ): { is_ours: boolean; one_time_privkey: Uint8Array | null };
  derive_stealth_one_time_address(
    spendPubkey: Uint8Array,
    viewPubkey: Uint8Array,
  ): { one_time_pubkey: Uint8Array; ephemeral_pubkey: Uint8Array; ephemeral_privkey: Uint8Array };

  // Private transfers
  create_value_commitment(amount: number, blinding: Uint8Array): { commitment: Uint8Array; blinding: Uint8Array };
  generate_range_proof(amount: number, blinding: Uint8Array, commitment: Uint8Array): { proof: Uint8Array; proof_size_bytes: number };
  build_committed_turn(params: string): { turn_id: string; turn_bytes: Uint8Array };

  // Encrypted intents
  generate_sse_tokens(keywords: string[]): Uint8Array[];
  seal_intent_body(plaintextJson: string, recipientPubkey: Uint8Array | null): {
    ciphertext: Uint8Array;
    ephemeral_pubkey: Uint8Array;
    nonce: Uint8Array;
  };
  /**
   * Canonical encrypted-intent post path. Routes through
   * `AgentCipherclerk::post_encrypted_intent` in the SDK so the resulting
   * `EncryptedIntent`'s `commitment_id` is bound to the cipherclerk's
   * Ed25519 public key. Returns the postcard-encoded `EncryptedIntent`
   * bytes alongside the content-addressed intent id (hex) and the
   * (optional) expiry that was set.
   */
  cipherclerk_post_encrypted_intent(specJson: string): {
    intent_id: string;
    encrypted_intent_bytes: Uint8Array;
    encrypted_intent_json: string;
    expiry: number | null;
    encrypted: boolean;
  };
  /**
   * Canonical private-transfer turn-builder. Routes through
   * `AgentCipherclerk::private_transfer` in the SDK — Pedersen value
   * commitment + stealth one-time-address recipient — and returns the
   * postcard-encoded `Turn` ready for `/turns/submit`.
   */
  cipherclerk_private_transfer(specJson: string): {
    turn_id: string;
    turn_bytes: Uint8Array;
    agent_cell_id: string;
  };
  /**
   * Canonical cipherclerk-signed peer exchange. Routes through
   * `AgentCipherclerk::peer_exchange("default")` so the resulting
   * `PeerStateTransition` is signed by the cipherclerk's Ed25519 identity.
   * `transition_bytes` is the postcard-encoded transition for direct
   * peer-to-peer exchange; the legacy `exchange_id` / `proof_commitment`
   * hex fields are retained for UI display parity.
   */
  cipherclerk_peer_exchange(specJson: string): {
    exchange_id: string;
    proof_commitment: string;
    sender_cell: string;
    receiver_cell: string;
    transition_bytes: Uint8Array;
    amount: number;
  };
  /**
   * Canonical cipherclerk-signed action-turn builder for federation-routed
   * actions like `propose_routes` / `vote_on_proposal`. Routes through
   * `AgentCipherclerk::make_action` + `AgentCipherclerk::make_turn_for`, so the
   * action's `authorization` is an Ed25519 signature bound to the
   * federation_id. The arbitrary action payload travels in the turn's
   * `memo` field as a JSON string.
   */
  cipherclerk_make_action_turn(specJson: string): {
    turn_id: string;
    turn_bytes: Uint8Array;
    agent_cell_id: string;
    method: string;
  };
}

// ---------------------------------------------------------------------------
// Page-to-content message envelope
// ---------------------------------------------------------------------------

/** Message envelope sent from page.ts to content.ts via CustomEvent. */
export interface PageRequestMessage {
  type: MessageType;
  id: string;
  [key: string]: unknown;
}

/** Response message sent from content.ts back to page.ts via CustomEvent. */
export interface PageResponseMessage {
  id: string;
  result?: unknown;
  error?: string;
}

/** Event notification forwarded from background to page. */
export interface EventNotification {
  eventName: string;
  payload: unknown;
}
