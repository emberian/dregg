// ============================================================================
// Core type definitions for the pyana TypeScript SDK.
// These map directly to the JSON structures returned by pyana-wasm exports.
// ============================================================================

/** Result of minting a new root macaroon token. */
export interface MintResult {
  /** The encoded token string (em2_ prefix). */
  token: string;
  /** The location/service this token was minted for. */
  location: string;
  /** Token format identifier. */
  format: string;
}

/** Result of generating a random root key. */
export interface KeyResult {
  /** Hex-encoded 32-byte key. */
  key_hex: string;
  /** Raw key bytes. */
  key_bytes: Uint8Array;
}

/** Result of attenuating a token. */
export interface AttenuateResult {
  /** The new attenuated token string. */
  token: string;
  /** Service the token was restricted to. */
  service: string;
  /** Comma-separated actions. */
  actions: string;
  /** Expiry in seconds (0 = no expiry). */
  expires_secs: number;
}

/** Result of verifying a token against a request. */
export interface VerifyResult {
  /** Whether the token grants access. */
  allowed: boolean;
  /** The matched policy rule (if allowed). */
  policy: string | null;
  /** Error message (if denied). */
  error: string | null;
}

/** Result of generating a STARK proof. */
export interface StarkProofResult {
  /** Serialized proof JSON. */
  proof_json: string;
  /** Size of the proof in bytes. */
  proof_size_bytes: number;
  /** Time to generate in milliseconds. */
  generation_time_ms: number;
  /** Number of trace rows. */
  trace_rows: number;
  /** Input leaf value. */
  leaf_value: number;
  /** Computed root value. */
  root_value: number;
  /** Number of FRI queries. */
  num_queries: number;
  /** Number of FRI layers. */
  fri_layers: number;
}

/** Result of verifying a STARK proof. */
export interface StarkVerifyResult {
  /** Whether the proof is valid. */
  valid: boolean;
  /** Error message if invalid. */
  error: string | null;
  /** Time to verify in milliseconds. */
  verification_time_ms: number;
}

/** Result of generating a predicate proof. */
export interface PredicateProofResult {
  /** Serialized proof JSON. */
  proof_json: string;
  /** Size of the proof in bytes. */
  proof_size_bytes: number;
  /** Time to generate in milliseconds. */
  generation_time_ms: number;
  /** The predicate type used. */
  predicate_type: string;
  /** The public threshold. */
  threshold: number;
  /** The fact commitment binding this proof to state. */
  fact_commitment: number;
  /** Whether the proof self-verified. */
  verified: boolean;
}

/** Result of verifying a predicate proof. */
export interface PredicateVerifyResult {
  /** Whether the proof is valid. */
  valid: boolean;
}

/** Supported predicate comparison operators. */
export type PredicateType = "gte" | "lte" | "gt" | "lt" | "neq";

/** Result of computing a Merkle root. */
export interface MerkleRootResult {
  /** Hex-encoded Merkle root. */
  root_hex: string;
  /** Number of leaves in the tree. */
  num_leaves: number;
}

/** Result of a Merkle membership proof. */
export interface MembershipProofResult {
  /** Hex-encoded Merkle root. */
  root_hex: string;
  /** The leaf that was proven. */
  leaf: string;
  /** Whether the leaf is a member of the set. */
  is_member: boolean;
  /** Length of the proof path (number of siblings). */
  proof_path_len: number;
}

/** Result of a Merkle non-membership proof. */
export interface NonMembershipProofResult {
  /** Hex-encoded Merkle root. */
  root_hex: string;
  /** The leaf proven absent. */
  leaf: string;
  /** Whether absence was proven. */
  proven_absent: boolean;
}

/** Result of a Datalog evaluation. */
export interface DatalogResult {
  /** "allow" or "deny". */
  conclusion: "allow" | "deny";
  /** The policy rule ID that matched (if allow). */
  policy_rule_id: number | null;
  /** Number of derivation steps. */
  num_derivation_steps: number;
  /** Detailed derivation steps. */
  steps: DatalogStep[];
}

/** A single Datalog derivation step. */
export interface DatalogStep {
  /** Rule ID that fired. */
  rule_id: number;
  /** Hex of the derived predicate. */
  derived_predicate_hex: string;
  /** Number of variable bindings. */
  num_bindings: number;
}

/** A Datalog fact for input. */
export interface DatalogFact {
  /** The predicate name. */
  predicate: string;
  /** The constant terms. */
  terms: string[];
}

/** A Datalog authorization request. */
export interface DatalogRequest {
  app_id?: string;
  service?: string;
  action?: string;
  features?: string[];
  user_id?: string;
  now?: number;
}

/** Result of demonstrating a fold (attenuation chain). */
export interface FoldResult {
  /** Old state root (hex). */
  old_root_hex: string;
  /** New state root after attenuation (hex). */
  new_root_hex: string;
  /** Whether the fold was verified. */
  verified: boolean;
  /** Total facts before attenuation. */
  total_facts: number;
  /** Number of facts removed. */
  removed_facts: number;
  /** Facts remaining after attenuation. */
  remaining_facts: number;
}

/** Result of a committed threshold proof. */
export interface CommittedThresholdResult {
  /** Poseidon2 commitment to the threshold. */
  threshold_commitment: number;
  /** Fact commitment binding to token state. */
  fact_commitment: number;
  /** Proof size in bytes. */
  proof_size_bytes: number;
  /** Generation time in milliseconds. */
  generation_time_ms: number;
  /** Whether the proof self-verified. */
  verified: boolean;
}

/** Result of verifying a committed threshold proof. */
export interface CommittedThresholdVerifyResult {
  /** Whether the proof is valid. */
  valid: boolean;
  /** Verification time in milliseconds. */
  verification_time_ms: number;
}

/** Result of Schnorr key generation. */
export interface SchnorrKeypair {
  /** 32-byte secret key seed. */
  secret_key: Uint8Array;
  /** BabyBear8 x-coordinate of public key (8 u32 elements). */
  public_key_x: number[];
  /** BabyBear8 y-coordinate of public key (8 u32 elements). */
  public_key_y: number[];
}

/** A Schnorr signature. */
export interface SchnorrSignature {
  /** BabyBear8 x-coordinate of R point. */
  r_x: number[];
  /** BabyBear8 y-coordinate of R point. */
  r_y: number[];
  /** Scalar s as 32 bytes. */
  s: Uint8Array;
}

/** Result of a garbled circuit comparison. */
export interface GarbledCompareResult {
  /** "pass" or "fail". */
  result: "pass" | "fail";
  /** The prover's value. */
  prover_value: number;
  /** The verifier's threshold. */
  verifier_threshold: number;
  /** Raw output bit. */
  output_bit: boolean;
  /** Proof size in bytes. */
  proof_size_bytes: number;
  /** Whether the proof verified. */
  proof_verified: boolean;
  /** Time to garble in milliseconds. */
  garbling_time_ms: number;
  /** Total protocol time in milliseconds. */
  total_time_ms: number;
  /** Number of gates in the garbled circuit. */
  num_gates: number;
}

/** Result of anonymous ring membership proof. */
export interface AnonymousMembershipResult {
  /** Blinded leaf value (u32 field element). */
  blinded_leaf: number;
  /** One-time presentation tag. */
  presentation_tag: number;
  /** Merkle root of the agent set. */
  set_root: number;
  /** Number of members in the ring. */
  ring_size: number;
  /** Estimated proof size in bytes. */
  proof_size_bytes: number;
  /** Generation time in milliseconds. */
  generation_time_ms: number;
}

/** Intent ID computation input. */
export interface IntentIdInput {
  kind: "Need" | "Offer" | "Query";
  actions?: Array<{ action?: string; resource?: string }>;
  constraints?: Array<IntentConstraint>;
  min_budget?: number;
  resource_pattern?: string;
  compound?: Array<{
    actions?: Array<{ action?: string; resource?: string }>;
    constraints?: Array<IntentConstraint>;
    min_budget?: number;
    resource_pattern?: string;
  }>;
  expiry: number;
  creator?: number[];
  stake_commitment?: number[];
}

/** A constraint in an intent. */
export interface IntentConstraint {
  AppId?: string;
  Service?: string;
  UserId?: string;
  NotExpiredAt?: number;
  Feature?: string;
  OAuthProvider?: string;
  predicate?: string;
  value?: string;
}

// ============================================================================
// Runtime types (from bindings.rs)
// ============================================================================

/** Result of creating an agent in the runtime. */
export interface AgentInfo {
  /** Index of the agent (used as handle). */
  agent_index: number;
  /** Display name. */
  name: string;
  /** Hex-encoded cell ID. */
  cell_id: string;
  /** Hex-encoded public key. */
  public_key: string;
}

// CellState is defined below with the enriched program field (Refactor 6).

/** Permission levels for a cell. */
export interface CellPermissions {
  send: string;
  receive: string;
  set_state: string;
  set_permissions: string;
  delegate: string;
  access: string;
}

/** Summary of a cell for listing. */
export interface CellSummary {
  cell_id: string;
  balance: number;
  nonce: number;
  num_capabilities: number;
}

/** Result of executing a turn. */
export interface TurnResultView {
  status: "committed" | "rejected" | "expired" | "pending";
  turn_hash: string | null;
  computrons_used: number | null;
  pre_state_hash: string | null;
  post_state_hash: string | null;
  error: string | null;
  at_action: number[] | null;
}

/** An action to execute in a turn. */
export type TurnAction =
  | { type: "transfer"; to: string; amount: number; from?: string }
  | { type: "set_field"; index: number; value_hex: string; cell?: string }
  | { type: "increment_nonce"; cell?: string };

/** Result of creating a federation. */
export interface FederationInfo {
  fed_index: number;
  name: string;
  num_nodes: number;
}

/** Federation state. */
export interface FederationState {
  name: string;
  height: number;
  num_nodes: number;
  num_events: number;
  num_finalized_roots: number;
  latest_root: string | null;
}

/** Result of proposing a block. */
export interface BlockResult {
  block_hash: string;
  height: number;
}

/** Result of a consensus round. */
export interface ConsensusRoundResult {
  height: number;
  root: string;
  votes: number;
  quorum_reached: boolean;
}

/** Result of creating an intent in the runtime. */
export interface IntentInfo {
  intent_id: string;
  intent_index: number;
}

/** Result of matching an intent. */
export interface IntentMatchResult {
  matched: boolean;
  kind: "matched" | "compound_matched" | "no_match" | "expired" | "wrong_kind";
  token_index: number | null;
  token_indices: number[] | null;
}

/** Result of minting a token in the runtime. */
export interface RuntimeMintResult {
  token_index: number;
  token_id: string;
}

/** Result of attenuating a token in the runtime. */
export interface RuntimeAttenuateResult {
  new_token_index: number;
  token_id: string;
}

/** Capability entry in a CDT. */
export interface CapabilityEntry {
  slot: number;
  target: string;
  permissions: string;
  has_breadstuff: boolean;
}

/** Capability Delegation Tree view. */
export interface CDTView {
  cell_id: string;
  agent_name: string;
  capabilities: CapabilityEntry[];
}

/** A note commitment result. */
export interface NoteResult {
  commitment: string;
  value: number;
  asset_type: number;
}

/** Result of spending a note. */
export interface SpendResult {
  nullifier: string;
  spent: boolean;
}

/** Result of granting a capability. */
export interface GrantResult {
  slot: number;
  target_cell: string;
  to_agent_cell: string;
}

/** Revocation channel result. */
export interface ChannelResult {
  channel_id: string;
}

/** Result of tripping a revocation channel. */
export interface TripResult {
  tripped: boolean;
  channel_id: string;
}

/** Channel active status. */
export interface ChannelActiveResult {
  channel_id: string;
  active: boolean;
}

/** Result of a conditional turn submission. */
export interface ConditionalResult {
  conditional_id: string;
  timeout_height: number;
}

/** Proof condition for conditional turns. */
export type ProofCondition =
  | { type: "hash_preimage"; hash: string }
  | { type: "turn_executed"; turn_hash: string }
  | { type: "remote_proof"; federation_root: string };

/** Delegation graph for visualization. */
export interface DelegationGraph {
  nodes: Array<{ cell_id: string; agent_name: string | null }>;
  edges: Array<{ from: string; to: string; slot: number; permissions: string }>;
}

// ReceiptEntry is defined below with enriched actions/proof_view fields (Refactors 3 & 7).

/** Merkle tree visualization data. */
export interface TreeViz {
  root_hex: string;
  num_leaves: number;
  tree_type: string;
}

/** Height/timestamp after advancing. */
export interface HeightResult {
  height: number;
  timestamp: number;
}

/** Permission level for capability grants. */
export type AuthRequired = "None" | "Signature" | "Proof" | "Either" | "Impossible";

// ============================================================================
// Enriched receipt / action / proof view types (Refactors 3 & 7)
// ============================================================================

/**
 * Authorization proof attached to a single action inside a receipt.
 * Tagged union that covers all six variants the runtime can emit.
 */
export type ActionAuthorization =
  | { kind: "None" }
  | { kind: "Ed25519"; pubkey_hex: string; signature_hex: string }
  | { kind: "BearerToken"; token_hex: string }
  | { kind: "CapabilitySlot"; slot: number }
  | { kind: "Delegation"; delegator_hex: string; slot: number }
  | { kind: "FederationQuorum"; fed_index: number; block_hash: string };

/** View of a single action inside a receipt (Refactor 3). */
export interface ActionView {
  /** Path through nested sub-actions (empty = top-level). */
  action_path: number[];
  /** Hex-encoded target cell. */
  target_cell: string;
  /** Named method / effect type. */
  method: string;
  /** Human-readable effect descriptions. */
  effects: string[];
  /** Authorization proof attached to this action. */
  authorization: ActionAuthorization;
}

/**
 * Proof view attached to a receipt for bilateral PI rendering (Refactor 7).
 * `null` when the turn carried no ZK proof.
 */
export interface ProofView {
  /** Proof backend identifier ("stark" | "plonky3" | "kimchi" | "mock"). */
  backend: string;
  /** Serialized proof JSON (may be large). */
  proof_json: string;
  /** Public inputs as hex-encoded field elements. */
  public_inputs: string[];
  /** Proof size in bytes. */
  proof_size_bytes: number;
  /** Whether the proof was already verified at receipt time. */
  verified: boolean;
}

/** Receipt chain entry with enriched action list and optional proof view. */
export interface ReceiptEntry {
  turn_hash: string;
  pre_state_hash: string;
  post_state_hash: string;
  timestamp: number;
  computrons_used: number;
  action_count: number;
  /** Per-action details (Refactor 3). */
  actions: ActionView[];
  /** Attached ZK proof, if any (Refactor 7). */
  proof_view: ProofView | null;
}

// ============================================================================
// Cell program view (Refactor 6)
// ============================================================================

/** A single slot in the cell's slot-caveat tree. */
export interface SlotView {
  /** Slot index. */
  index: number;
  /** Caveat predicate name. */
  predicate: string;
  /** Caveat terms (serialized). */
  terms: string[];
}

/**
 * Full program semantics view for a cell (Refactor 6).
 * Surfaced so JS inspectors can render the complete slot-caveat tree.
 */
export interface CellProgramView {
  /** Verification key hash (hex). */
  vk_hash: string;
  /** Ordered list of active slots. */
  slots: SlotView[];
  /** Whether the cell has a sovereign program attached. */
  has_sovereign_program: boolean;
  /** Factory VK that minted this cell, if any. */
  factory_vk: string | null;
}

/** Cell state view with enriched program field (Refactor 6). */
export interface CellState {
  cell_id: string;
  public_key: string;
  balance: number;
  nonce: number;
  fields: string[];
  num_capabilities: number;
  permissions: CellPermissions;
  proved_state: boolean;
  delegation_epoch: number;
  /** Full slot-caveat program semantics (Refactor 6). */
  program: CellProgramView;
}

// ============================================================================
// Peer exchange types
// ============================================================================

/** Decoded fields of a PeerStateTransition. */
export interface PeerTransitionView {
  /** Hex-encoded cell ID of the transition author. */
  cell_id: string;
  /** Hex-encoded old commitment. */
  old_commitment: string;
  /** Hex-encoded new commitment. */
  new_commitment: string;
  /** Hex-encoded hash of the effects bundle. */
  effects_hash: string;
  /** Unix timestamp (seconds). */
  timestamp: number;
  /** Monotonic sequence number. */
  sequence: number;
  /** Hex-encoded Ed25519 signature. */
  signature: string;
  /** Whether a full transition proof blob is attached. */
  has_transition_proof: boolean;
}

/** Current view of a registered peer cell. */
export interface PeerCellView {
  /** Hex-encoded cell ID. */
  cell_id: string;
  /** Hex-encoded current commitment. */
  commitment: string;
  /** Last accepted sequence number. */
  sequence: number;
  /** Unix timestamp of last update. */
  last_updated: number;
}

// ============================================================================
// Turn trace (get_turn_trace)
// ============================================================================

/** A single step in a turn's execution trace. */
export interface TurnTraceStep {
  /** Path through nested sub-actions. */
  action_path: number[];
  /** Hex-encoded target cell. */
  target_cell: string;
  /** Method name. */
  method: string;
  /** Effect descriptions applied at this step. */
  effects: string[];
  /** Computrons consumed at this step. */
  computrons_used: number;
  /** Step result: "ok" or an error message. */
  result: string;
}

// ============================================================================
// Factory / cell creation
// ============================================================================

/** Result of deploying a factory descriptor. */
export interface FactoryDeployResult {
  /** Hex-encoded factory verification key. */
  factory_vk: string;
}

/** Result of creating a cell (not via an agent). */
export interface CellCreateResult {
  /** Hex-encoded cell ID. */
  cell_id: string;
}

/** Result of getting the default factory VK. */
export interface DefaultFactoryVkResult {
  /** Hex-encoded factory VK. */
  factory_vk: string;
}

/** Result of getting the cell state commitment. */
export interface CellStateCommitmentResult {
  /** Hex-encoded current commitment, or null if not in ledger. */
  commitment: string | null;
}

// ============================================================================
// Federation block types
// ============================================================================

/** Compact header for a finalized federation block. */
export interface FederationBlockHeader {
  /** Block height (1-indexed). */
  height: number;
  /** Hex-encoded block hash. */
  block_hash: string;
  /** Number of events in the block. */
  event_count: number;
  /** Hex-encoded attested state root. */
  state_root: string;
  /** Unix timestamp. */
  timestamp: number;
}

/** Full finalized block view. */
export interface FederationBlock {
  /** Block height (1-indexed). */
  height: number;
  /** Hex-encoded block hash. */
  block_hash: string;
  /** Revocation event token IDs. */
  events: string[];
  /** Hex-encoded attested state root. */
  state_root: string;
  /** Unix timestamp. */
  timestamp: number;
  /** Number of votes that finalized this block. */
  vote_count: number;
}
