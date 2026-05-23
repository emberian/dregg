/**
 * Shared type definitions for the Pyana extension message protocol.
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

/** A capability token held in the wallet. */
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
  // Core wallet operations
  | "pyana:authorize"
  | "pyana:isConnected"
  | "pyana:canAuthorize"
  | "pyana:provision"
  | "pyana:subscribe"
  // Popup-only wallet operations
  | "pyana:getState"
  | "pyana:lock"
  | "pyana:unlock"
  | "pyana:getCapabilities"
  | "pyana:revoke"
  | "pyana:setPassphrase"
  | "pyana:getMnemonic"
  | "pyana:recover"
  // Intent operations
  | "pyana:postIntent"
  | "pyana:offerCapability"
  | "pyana:listIntents"
  | "pyana:fulfillIntent"
  | "pyana:getFulfillableIntents"
  // Privacy operations
  | "pyana:getStealthAddress"
  | "pyana:postEncryptedIntent"
  | "pyana:privateTransfer"
  | "pyana:getPrivacyState"
  | "pyana:setCommittedTransferMode"
  | "pyana:getStealthNotes"
  // Bearer capabilities
  | "pyana:createBearerCap"
  | "pyana:verifyBearerCap"
  // Factory operations
  | "pyana:createFromFactory"
  | "pyana:verifyProvenance"
  // Sovereign cell operations
  | "pyana:makeCellSovereign"
  | "pyana:peerExchange"
  // Proof composition
  | "pyana:composeProofs"
  // Turn submission
  | "pyana:signTurn"
  | "pyana:queryBalance"
  // Node configuration
  | "pyana:getNodeConfig"
  | "pyana:setNodeConfig"
  // CapTP operations
  | "pyana:shareCapability"
  | "pyana:acceptCapability"
  | "pyana:createHandoff"
  | "pyana:getLiveRefs"
  | "pyana:dropLiveRef"
  // Directory operations
  | "pyana:mountService"
  | "pyana:discoverServices"
  | "pyana:resolvePath"
  // Storage operations
  | "pyana:storageWrite"
  | "pyana:storageRead"
  | "pyana:storageQuota"
  // Federation operations
  | "pyana:federationStatus"
  | "pyana:proposeRoutes"
  | "pyana:voteOnProposal"
  // Discovery
  | "pyana:getFederation"
  | "pyana:refreshDiscovery"
  // Origin permission
  | "pyana:requestOriginPermission"
  | "pyana:originPermissionDecision"
  | "pyana:getOriginPermissions"
  | "pyana:revokeOriginPermission"
  | "pyana:getDisclosurePrefs"
  | "pyana:clearDisclosurePref"
  // Queue operations
  | "pyana:queueAllocate"
  | "pyana:queueEnqueue"
  | "pyana:queueDequeue"
  | "pyana:queueAtomicTx"
  | "pyana:queueStatus"
  // Internal decision messages
  | "pyana:provisionDecision"
  | "pyana:intentConfirmation"
  | "pyana:disclosureDecision";

// ---------------------------------------------------------------------------
// Queue types
// ---------------------------------------------------------------------------

/** An operation within an atomic queue transaction. */
export type QueueTxOp =
  | { type: "enqueue"; queue: string; messageHash: string; deposit: number }
  | { type: "dequeue"; queue: string };

/** Status of a queue cell. */
export interface QueueStatus {
  queueId: string;
  occupancy: number;
  capacity: number;
  owner: string;
  programVk?: string;
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
// Wallet state types
// ---------------------------------------------------------------------------

/** Public wallet state (returned to popup). */
export interface WalletState {
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

/** Internal full wallet state (in-memory). */
export interface InternalWalletState {
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

/** A stealth note matched to our wallet. */
export interface StealthNote {
  noteId: string;
  amount: number | null;
  assetType: string;
  oneTimePrivkey: number[] | null;
  ephemeralPubkey: number[];
  memo: string | null;
  receivedAt: number;
}

/** A log entry for wallet activity. */
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
  error?: string;
  nodeResult?: Record<string, unknown>;
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
 * Interface for the pyana WASM module exports.
 * Only the functions actually called from JS are typed here.
 */
export interface PyanaWasm {
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

  // Bearer capabilities
  create_bearer_cap(delegatorKeyHex: string, targetCellHex: string, action: string, expiry: number): { bearerTokenHex: string; targetCell: string; action: string };
  verify_bearer_cap(tokenHex: string, delegatorKeyHex: string, targetCellHex: string, action: string, expiry: number, currentTime: number): { valid: boolean; expired: boolean };

  // Factory operations
  create_from_factory(factoryVkHex: string, ownerPubkeyHex: string, initialBalance: number): { childVk: string; paramHash: string; factoryVk: string };
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
