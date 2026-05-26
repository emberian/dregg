/**
 * PyanaRuntime: Full distributed system simulation wrapper.
 *
 * Provides a high-level API over the WASM runtime bindings for simulating
 * agents, cells, turns, federations, intents, notes, capabilities, and
 * revocation channels.
 */

import type {
  AgentInfo,
  CellState,
  CellSummary,
  TurnResultView,
  TurnAction,
  FederationInfo,
  FederationState,
  BlockResult,
  ConsensusRoundResult,
  IntentInfo,
  IntentMatchResult,
  RuntimeMintResult,
  RuntimeAttenuateResult,
  CDTView,
  NoteResult,
  SpendResult,
  GrantResult,
  ChannelResult,
  TripResult,
  ChannelActiveResult,
  ConditionalResult,
  ProofCondition,
  DelegationGraph,
  ReceiptEntry,
  TreeViz,
  HeightResult,
  AuthRequired,
  PeerTransitionView,
  PeerCellView,
  TurnTraceStep,
  FactoryDeployResult,
  CellCreateResult,
  DefaultFactoryVkResult,
  CellStateCommitmentResult,
  FederationBlock,
  FederationBlockHeader,
} from "./types";

/**
 * PyanaRuntime wraps the WASM runtime simulation, managing a handle to
 * the underlying runtime instance and providing type-safe methods for
 * all distributed system operations.
 *
 * Each runtime maintains its own isolated state: ledger, agents, federations,
 * intents, etc. Multiple runtimes can coexist.
 *
 * @example
 * ```ts
 * import { PyanaRuntime } from "@pyana/sdk";
 *
 * const runtime = new PyanaRuntime(wasm);
 *
 * // Create agents
 * const alice = await runtime.createAgent("alice", 1000);
 * const bob = await runtime.createAgent("bob", 500);
 *
 * // Execute a transfer
 * const result = await runtime.executeTurn(alice.agent_index, [
 *   { type: "transfer", to: bob.cell_id, amount: 100 },
 * ]);
 * console.log(result.status); // "committed"
 *
 * // Clean up
 * runtime.destroy();
 * ```
 */
export class PyanaRuntime {
  private wasm: typeof import("pyana-wasm");
  private handle: number;
  private destroyed = false;

  constructor(wasm: typeof import("pyana-wasm")) {
    this.wasm = wasm;
    this.handle = (wasm as any).create_runtime() as number;
  }

  /**
   * Destroy this runtime, freeing all associated resources.
   * After calling this, the runtime instance cannot be used.
   */
  destroy(): void {
    if (!this.destroyed) {
      (this.wasm as any).destroy_runtime(this.handle);
      this.destroyed = true;
    }
  }

  private assertAlive(): void {
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
  async createAgent(name: string, initialBalance: number): Promise<AgentInfo> {
    this.assertAlive();
    try {
      return (this.wasm as any).create_agent(
        this.handle,
        name,
        BigInt(initialBalance)
      ) as AgentInfo;
    } catch (e) {
      throw new Error(`Failed to create agent: ${extractError(e)}`);
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
  async mintToken(
    agentIndex: number,
    resource: string,
    actions: string[],
    expiry: number = 0
  ): Promise<RuntimeMintResult> {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    try {
      return (this.wasm as any).agent_mint_token(
        this.handle,
        agentIndex,
        resource,
        actionsJson,
        BigInt(expiry)
      ) as RuntimeMintResult;
    } catch (e) {
      throw new Error(`Failed to mint token: ${extractError(e)}`);
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
  async attenuateToken(
    agentIndex: number,
    tokenIndex: number,
    restrictActions: string[] = [],
    restrictResource: string = ""
  ): Promise<RuntimeAttenuateResult> {
    this.assertAlive();
    const actionsJson = JSON.stringify(restrictActions);
    try {
      return (this.wasm as any).agent_attenuate(
        this.handle,
        agentIndex,
        tokenIndex,
        actionsJson,
        restrictResource
      ) as RuntimeAttenuateResult;
    } catch (e) {
      throw new Error(`Failed to attenuate token: ${extractError(e)}`);
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
  async getCellState(cellIdHex: string): Promise<CellState> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_cell_state(
        this.handle,
        cellIdHex
      ) as CellState;
    } catch (e) {
      throw new Error(`Failed to get cell state: ${extractError(e)}`);
    }
  }

  /**
   * Get all cells in the ledger.
   *
   * @returns Array of cell summaries.
   */
  async getAllCells(): Promise<CellSummary[]> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_all_cells(this.handle) as CellSummary[];
    } catch (e) {
      throw new Error(`Failed to get cells: ${extractError(e)}`);
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
  async executeTurn(
    agentIndex: number,
    actions: TurnAction[],
    fee: number = 0
  ): Promise<TurnResultView> {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    try {
      return (this.wasm as any).execute_turn(
        this.handle,
        agentIndex,
        actionsJson,
        BigInt(fee)
      ) as TurnResultView;
    } catch (e) {
      throw new Error(`Failed to execute turn: ${extractError(e)}`);
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
  async executeTurnStepByStep(
    agentIndex: number,
    actions: TurnAction[],
    fee: number = 0
  ): Promise<any> {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    try {
      return (this.wasm as any).execute_turn_step_by_step(
        this.handle,
        agentIndex,
        actionsJson,
        BigInt(fee)
      );
    } catch (e) {
      throw new Error(`Failed to execute turn (traced): ${extractError(e)}`);
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
  async grantCapability(
    fromAgent: number,
    toAgent: number,
    permission: AuthRequired,
    targetCellHex: string = ""
  ): Promise<GrantResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).grant_capability(
        this.handle,
        fromAgent,
        toAgent,
        targetCellHex,
        permission
      ) as GrantResult;
    } catch (e) {
      throw new Error(`Failed to grant capability: ${extractError(e)}`);
    }
  }

  /**
   * Revoke a capability by slot index.
   *
   * @param agentIndex - The agent whose capability to revoke.
   * @param slot - The capability slot number.
   * @returns Whether the revocation succeeded.
   */
  async revokeCapability(
    agentIndex: number,
    slot: number
  ): Promise<{ revoked: boolean; slot: number }> {
    this.assertAlive();
    try {
      return (this.wasm as any).revoke_capability(
        this.handle,
        agentIndex,
        slot
      ) as { revoked: boolean; slot: number };
    } catch (e) {
      throw new Error(`Failed to revoke capability: ${extractError(e)}`);
    }
  }

  /**
   * Get the Capability Delegation Tree (CDT) for an agent.
   *
   * @param agentIndex - The agent's index.
   * @returns The CDT view with all capabilities.
   */
  async getCapabilityTree(agentIndex: number): Promise<CDTView> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_capability_tree(
        this.handle,
        agentIndex
      ) as CDTView;
    } catch (e) {
      throw new Error(`Failed to get capability tree: ${extractError(e)}`);
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
  async createNote(
    agentIndex: number,
    value: number,
    assetType: number
  ): Promise<NoteResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).create_note(
        this.handle,
        agentIndex,
        BigInt(value),
        BigInt(assetType)
      ) as NoteResult;
    } catch (e) {
      throw new Error(`Failed to create note: ${extractError(e)}`);
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
  async spendNote(
    agentIndex: number,
    value: number,
    assetType: number
  ): Promise<SpendResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).spend_note(
        this.handle,
        agentIndex,
        BigInt(value),
        BigInt(assetType)
      ) as SpendResult;
    } catch (e) {
      throw new Error(`Failed to spend note: ${extractError(e)}`);
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
  async createFederation(
    name: string,
    numNodes: number
  ): Promise<FederationInfo> {
    this.assertAlive();
    try {
      return (this.wasm as any).create_federation(
        this.handle,
        name,
        numNodes
      ) as FederationInfo;
    } catch (e) {
      throw new Error(`Failed to create federation: ${extractError(e)}`);
    }
  }

  /**
   * Propose a block of events to a federation.
   *
   * @param fedIndex - Federation index.
   * @param events - Array of event data strings.
   * @returns The block hash and new height.
   */
  async proposeBlock(fedIndex: number, events: string[]): Promise<BlockResult> {
    this.assertAlive();
    const eventsJson = JSON.stringify(events);
    try {
      return (this.wasm as any).propose_block(
        this.handle,
        fedIndex,
        eventsJson
      ) as BlockResult;
    } catch (e) {
      throw new Error(`Failed to propose block: ${extractError(e)}`);
    }
  }

  /**
   * Get the current state of a federation.
   *
   * @param fedIndex - Federation index.
   * @returns The federation state.
   */
  async getFederationState(fedIndex: number): Promise<FederationState> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_federation_state(
        this.handle,
        fedIndex
      ) as FederationState;
    } catch (e) {
      throw new Error(`Failed to get federation state: ${extractError(e)}`);
    }
  }

  /**
   * Simulate a consensus round (all nodes vote and finalize).
   *
   * @param fedIndex - Federation index.
   * @returns The consensus round result.
   */
  async simulateConsensusRound(
    fedIndex: number
  ): Promise<ConsensusRoundResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).simulate_consensus_round(
        this.handle,
        fedIndex
      ) as ConsensusRoundResult;
    } catch (e) {
      throw new Error(`Failed to simulate consensus: ${extractError(e)}`);
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
  async createIntent(
    agentIndex: number,
    kind: "Need" | "Offer" | "Query",
    actions: Array<{ action?: string; resource?: string }>,
    constraints: Array<Record<string, string | number>> = [],
    resourcePattern: string = "",
    expiry: number = 0
  ): Promise<IntentInfo> {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    const constraintsJson = JSON.stringify(constraints);
    try {
      return (this.wasm as any).create_intent(
        this.handle,
        agentIndex,
        kind,
        actionsJson,
        constraintsJson,
        resourcePattern,
        BigInt(expiry)
      ) as IntentInfo;
    } catch (e) {
      throw new Error(`Failed to create intent: ${extractError(e)}`);
    }
  }

  /**
   * Match an intent against an agent's held tokens.
   *
   * @param intentIndex - Index of the intent to match.
   * @param agentIndex - Index of the agent to match against.
   * @returns The match result.
   */
  async matchIntent(
    intentIndex: number,
    agentIndex: number
  ): Promise<IntentMatchResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).match_intent_for_agent(
        this.handle,
        intentIndex,
        agentIndex
      ) as IntentMatchResult;
    } catch (e) {
      throw new Error(`Failed to match intent: ${extractError(e)}`);
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
  async submitConditional(
    agentIndex: number,
    actions: TurnAction[],
    fee: number,
    condition: ProofCondition,
    timeoutBlocks: number
  ): Promise<ConditionalResult> {
    this.assertAlive();
    const actionsJson = JSON.stringify(actions);
    const conditionJson = JSON.stringify(condition);
    try {
      return (this.wasm as any).submit_conditional(
        this.handle,
        agentIndex,
        actionsJson,
        BigInt(fee),
        conditionJson,
        BigInt(timeoutBlocks)
      ) as ConditionalResult;
    } catch (e) {
      throw new Error(`Failed to submit conditional: ${extractError(e)}`);
    }
  }

  /**
   * Advance the block height (for timeout simulation).
   *
   * @param blocks - Number of blocks to advance.
   * @returns The new height and timestamp.
   */
  async advanceHeight(blocks: number): Promise<HeightResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).advance_height(
        this.handle,
        BigInt(blocks)
      ) as HeightResult;
    } catch (e) {
      throw new Error(`Failed to advance height: ${extractError(e)}`);
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
  async createRevocationChannel(
    revokerAgent: number
  ): Promise<ChannelResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).create_revocation_channel(
        this.handle,
        revokerAgent
      ) as ChannelResult;
    } catch (e) {
      throw new Error(`Failed to create revocation channel: ${extractError(e)}`);
    }
  }

  /**
   * Trip (activate) a revocation channel, invalidating all associated capabilities.
   *
   * @param revokerAgent - The agent triggering revocation.
   * @param channelIdHex - Hex-encoded channel ID.
   * @returns Whether the trip succeeded.
   */
  async tripRevocationChannel(
    revokerAgent: number,
    channelIdHex: string
  ): Promise<TripResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).trip_revocation_channel(
        this.handle,
        revokerAgent,
        channelIdHex
      ) as TripResult;
    } catch (e) {
      throw new Error(`Failed to trip channel: ${extractError(e)}`);
    }
  }

  /**
   * Check if a revocation channel is still active (not tripped).
   *
   * @param channelIdHex - Hex-encoded channel ID.
   * @returns Active status.
   */
  async isChannelActive(channelIdHex: string): Promise<ChannelActiveResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).is_channel_active(
        this.handle,
        channelIdHex
      ) as ChannelActiveResult;
    } catch (e) {
      throw new Error(`Failed to check channel: ${extractError(e)}`);
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
  async getMerkleTreeViz(): Promise<TreeViz> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_merkle_tree_viz(this.handle) as TreeViz;
    } catch (e) {
      throw new Error(`Failed to get tree viz: ${extractError(e)}`);
    }
  }

  /**
   * Get the full receipt chain (all committed turn receipts).
   *
   * @returns Array of receipt entries in order.
   */
  async getReceiptChain(): Promise<ReceiptEntry[]> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_receipt_chain(
        this.handle
      ) as ReceiptEntry[];
    } catch (e) {
      throw new Error(`Failed to get receipt chain: ${extractError(e)}`);
    }
  }

  /**
   * Get the delegation graph (all capability edges across all cells).
   *
   * Useful for visualizing the authorization topology.
   *
   * @returns Graph with nodes and edges.
   */
  async getDelegationGraph(): Promise<DelegationGraph> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_delegation_graph(
        this.handle
      ) as DelegationGraph;
    } catch (e) {
      throw new Error(`Failed to get delegation graph: ${extractError(e)}`);
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
  async createCell(
    ownerPkHex: string,
    initialBalance: number
  ): Promise<CellCreateResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).create_cell(
        this.handle,
        ownerPkHex,
        BigInt(initialBalance)
      ) as CellCreateResult;
    } catch (e) {
      throw new Error(`Failed to create cell: ${extractError(e)}`);
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
  async createAgentWithFactory(
    name: string,
    initialBalance: number,
    factoryVkHex: string
  ): Promise<AgentInfo> {
    this.assertAlive();
    try {
      return (this.wasm as any).create_agent_with_factory(
        this.handle,
        name,
        BigInt(initialBalance),
        factoryVkHex
      ) as AgentInfo;
    } catch (e) {
      throw new Error(`Failed to create agent with factory: ${extractError(e)}`);
    }
  }

  /**
   * Deploy a factory descriptor into the runtime, returning the factory VK.
   *
   * @param descriptorJson - Serde-serialized `FactoryDescriptor` JSON.
   * @returns The factory VK that addresses the deployed descriptor.
   */
  async deployFactoryDescriptor(
    descriptorJson: string
  ): Promise<FactoryDeployResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).deploy_factory_descriptor(
        this.handle,
        descriptorJson
      ) as FactoryDeployResult;
    } catch (e) {
      throw new Error(`Failed to deploy factory descriptor: ${extractError(e)}`);
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
  async defaultFactoryVk(): Promise<DefaultFactoryVkResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).default_factory_vk(
        this.handle
      ) as DefaultFactoryVkResult;
    } catch (e) {
      throw new Error(`Failed to get default factory VK: ${extractError(e)}`);
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
  async getCellStateCommitment(
    cellIdHex: string
  ): Promise<CellStateCommitmentResult> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_cell_state_commitment(
        this.handle,
        cellIdHex
      ) as CellStateCommitmentResult;
    } catch (e) {
      throw new Error(`Failed to get cell state commitment: ${extractError(e)}`);
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
  async getTurnTrace(
    turnHashHex: string
  ): Promise<TurnTraceStep[] | null> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_turn_trace(
        this.handle,
        turnHashHex
      ) as TurnTraceStep[] | null;
    } catch (e) {
      throw new Error(`Failed to get turn trace: ${extractError(e)}`);
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
  async registerPeer(
    agentIdx: number,
    peerCellIdHex: string,
    peerPubkeyHex: string,
    initialCommitmentHex: string
  ): Promise<PeerCellView> {
    this.assertAlive();
    try {
      return (this.wasm as any).register_peer(
        this.handle,
        agentIdx,
        peerCellIdHex,
        peerPubkeyHex,
        initialCommitmentHex
      ) as PeerCellView;
    } catch (e) {
      throw new Error(`Failed to register peer: ${extractError(e)}`);
    }
  }

  /**
   * Get the agent's PeerExchange public key.
   *
   * @param agentIdx - Agent index.
   * @returns The agent's peer pubkey as a hex string.
   */
  async getPeerPubkey(agentIdx: number): Promise<{ pubkey_hex: string }> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_peer_pubkey(
        this.handle,
        agentIdx
      ) as { pubkey_hex: string };
    } catch (e) {
      throw new Error(`Failed to get peer pubkey: ${extractError(e)}`);
    }
  }

  /**
   * Read the agent's current view of a registered peer cell.
   *
   * @param agentIdx - Agent index.
   * @param peerCellIdHex - Hex-encoded peer cell ID.
   * @returns The peer cell view, or `null` if not registered.
   */
  async getPeerView(
    agentIdx: number,
    peerCellIdHex: string
  ): Promise<PeerCellView | null> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_peer_view(
        this.handle,
        agentIdx,
        peerCellIdHex
      ) as PeerCellView | null;
    } catch (e) {
      throw new Error(`Failed to get peer view: ${extractError(e)}`);
    }
  }

  /**
   * List all peer cell IDs the agent has registered.
   *
   * @param agentIdx - Agent index.
   * @returns Array of hex-encoded peer cell IDs.
   */
  async listPeers(agentIdx: number): Promise<string[]> {
    this.assertAlive();
    try {
      return (this.wasm as any).list_peers(
        this.handle,
        agentIdx
      ) as string[];
    } catch (e) {
      throw new Error(`Failed to list peers: ${extractError(e)}`);
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
  async createPeerTransition(
    agentIdx: number,
    oldCommitHex: string,
    newCommitHex: string,
    effectsHashHex: string
  ): Promise<Uint8Array> {
    this.assertAlive();
    try {
      return (this.wasm as any).create_peer_transition(
        this.handle,
        agentIdx,
        oldCommitHex,
        newCommitHex,
        effectsHashHex
      ) as Uint8Array;
    } catch (e) {
      throw new Error(`Failed to create peer transition: ${extractError(e)}`);
    }
  }

  /**
   * Decode a `PeerStateTransition` blob into structured fields.
   *
   * @param bytes - Postcard-encoded transition bytes (from `createPeerTransition`).
   * @returns Decoded transition fields.
   */
  async decodePeerTransition(bytes: Uint8Array): Promise<PeerTransitionView> {
    this.assertAlive();
    try {
      return (this.wasm as any).decode_peer_transition(
        bytes
      ) as PeerTransitionView;
    } catch (e) {
      throw new Error(`Failed to decode peer transition: ${extractError(e)}`);
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
  async verifyPeerTransition(
    agentIdx: number,
    transitionBytes: Uint8Array,
    peerPubkeyHex: string
  ): Promise<PeerCellView> {
    this.assertAlive();
    try {
      return (this.wasm as any).verify_peer_transition(
        this.handle,
        agentIdx,
        transitionBytes,
        peerPubkeyHex
      ) as PeerCellView;
    } catch (e) {
      throw new Error(`Failed to verify peer transition: ${extractError(e)}`);
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
  async getFederationBlock(
    fedIndex: number,
    height: number
  ): Promise<FederationBlock | null> {
    this.assertAlive();
    try {
      return (this.wasm as any).get_federation_block(
        this.handle,
        fedIndex,
        BigInt(height)
      ) as FederationBlock | null;
    } catch (e) {
      throw new Error(`Failed to get federation block: ${extractError(e)}`);
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
  async listFederationBlocks(
    fedIndex: number
  ): Promise<FederationBlockHeader[]> {
    this.assertAlive();
    try {
      return (this.wasm as any).list_federation_blocks(
        this.handle,
        fedIndex
      ) as FederationBlockHeader[];
    } catch (e) {
      throw new Error(`Failed to list federation blocks: ${extractError(e)}`);
    }
  }
}

function extractError(e: unknown): string {
  if (e instanceof Error) return e.message;
  return String(e);
}
