// ---------------------------------------------------------------------------
// Core Identifiers
// ---------------------------------------------------------------------------

/** 64-character hex string identifying a cell. */
export type CellId = string;

/** 64-character hex string identifying a block. */
export type BlockId = string;

/** Hex string identifying a turn. */
export type TurnId = string;

// ---------------------------------------------------------------------------
// Cell Types
// ---------------------------------------------------------------------------

/** Operating mode of a cell. */
export type CellMode = "federated" | "sovereign";

/** Full state of a cell as returned by the node. */
export interface CellState {
  id: CellId;
  owner: string;
  balance: number;
  mode: CellMode;
  stateCommitment?: string;
  nonce: number;
  createdAt: number;
  lastTurnId?: TurnId;
  factoryVk?: string;
}

/** Parameters for creating a new cell. */
export interface CreateCellParams {
  ownerPubkeyHex: string;
  initialBalance?: number;
  factoryVkHex?: string;
}

// ---------------------------------------------------------------------------
// Turn Types
// ---------------------------------------------------------------------------

/**
 * A loosely-typed effect (legacy representation).
 * @deprecated Use the discriminated union `Effect` from `./effects.js` for new code.
 */
export interface LegacyEffect {
  type: string;
  target?: CellId;
  amount?: number;
  data?: Record<string, unknown>;
}

/** A turn: the atomic unit of state transition in Pyana. */
export interface Turn {
  action: string;
  resource?: string;
  amount?: number;
  recipient?: string;
  metadata?: Record<string, unknown>;
  effects?: LegacyEffect[];
}

/** Finality level of a turn receipt. */
export type Finality = "pending" | "soft" | "final";

/** Receipt returned after a turn is accepted by the network. */
export interface TurnReceipt {
  turnId: TurnId;
  submitted: boolean;
  finality?: Finality;
  blockId?: BlockId;
  nodeResult?: Record<string, unknown>;
  error?: string;
}

// ---------------------------------------------------------------------------
// Block Types
// ---------------------------------------------------------------------------

/** Finality level for a block. */
export type FinalityLevel = "proposed" | "committed" | "finalized";

/** A block in the Pyana ledger. */
export interface Block {
  id: BlockId;
  height: number;
  parentId: BlockId;
  merkleRoot: string;
  timestamp: number;
  turnCount: number;
  finality: FinalityLevel;
}

// ---------------------------------------------------------------------------
// Proof Types
// ---------------------------------------------------------------------------

/** Which proof backend produced this proof. */
export type ProofBackend = "stark" | "plonky3" | "kimchi" | "halo2";

/** A STARK proof (serialized). */
export interface StarkProof {
  proofJson: string;
  publicInputs?: number[];
  backend: ProofBackend;
  sizeBytes?: number;
}

/** Bearer capability proof. */
export interface BearerCapProof {
  bearerTokenHex: string;
  targetCell: CellId;
  action: string;
  expiry: number;
  delegatorKeyHex: string;
}

/** Data for a delegation proof (bearer cap creation result). */
export interface DelegationProofData {
  bearerTokenHex: string;
  targetCell: CellId;
  action: string;
}

/** Pedersen value commitment (for private transfers). */
export interface ValueCommitment {
  commitment: number[];
  blinding?: number[];
}

/** Conservation proof (proves inputs = outputs without revealing amounts). */
export interface ConservationProof {
  proof: string;
  inputCommitments: ValueCommitment[];
  outputCommitments: ValueCommitment[];
  valid: boolean;
}

// ---------------------------------------------------------------------------
// Intent Types
// ---------------------------------------------------------------------------

/** Kind of intent. */
export type IntentKind = "need" | "offer" | "query";

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

/** Result of an intent fulfillment. */
export interface Fulfillment {
  fulfilled: boolean;
  intentId: string;
  tokenId?: string;
  nodeResult?: Record<string, unknown>;
  error?: string;
}

// ---------------------------------------------------------------------------
// Gallery / AMM Types
// ---------------------------------------------------------------------------

/** An artwork listing in the gallery. */
export interface Artwork {
  id: string;
  title: string;
  artist: string;
  imageUrl?: string;
  currentBid?: string;
  auctionEndTime?: number;
  owner: string;
}

/** Parameters for an AMM swap. */
export interface SwapParams {
  tokenIn: string;
  tokenOut: string;
  amountIn: number;
  slippageBps?: number;
}

/** Result of an AMM swap. */
export interface SwapResult {
  amountOut: number;
  executedPrice: number;
  turnId: TurnId;
  poolState?: Record<string, unknown>;
}

// ---------------------------------------------------------------------------
// Stealth / Privacy Types
// ---------------------------------------------------------------------------

/** Stealth meta-address (public-facing identifier for receiving private payments). */
export interface StealthMetaAddress {
  spendPubkey: number[];
  viewPubkey: number[];
}

/** Parameters for a private transfer. */
export interface PrivateTransferParams {
  amount: number;
  assetType: string;
  recipientStealthMeta: StealthMetaAddress;
}

/** Result of a private transfer. */
export interface PrivateTransferResult {
  success: boolean;
  turnId?: TurnId;
  commitment?: number[];
  ephemeralPubkey?: number[];
  rangeProofSize?: number;
  submitted?: boolean;
  error?: string;
}

// ---------------------------------------------------------------------------
// Node Configuration
// ---------------------------------------------------------------------------

/** Node connection configuration. */
export interface NodeConfig {
  nodeUrl: string;
  wssUrl?: string;
  wsUrl?: string;
  devnetKey?: string;
}
