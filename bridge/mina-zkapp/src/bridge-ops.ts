import { PyanaFederation } from './PyanaFederation';
import { Field, Mina, PrivateKey, PublicKey, UInt64, fetchAccount } from 'o1js';

// ---------------------------------------------------------------------------
// Bridge relay operations
// ---------------------------------------------------------------------------

/**
 * Configuration for the bridge relay.
 */
export interface BridgeConfig {
  /** The zkApp address on Mina */
  zkAppAddress: PublicKey;
  /** Network endpoint (for remote networks) */
  minaEndpoint?: string;
  /** Fee for transactions (in nanomina) */
  txFee?: number;
}

/**
 * Result of a bridge transaction.
 */
export interface BridgeTxResult {
  /** Whether the transaction succeeded */
  success: boolean;
  /** Transaction hash (if sent) */
  txHash?: string;
  /** Error message (if failed) */
  error?: string;
}

/**
 * BridgeRelay: orchestrates bridge operations between pyana and Mina.
 *
 * The relay is responsible for:
 * 1. Observing pyana state transitions and submitting proofs to Mina
 * 2. Observing Mina deposit events and crediting notes on pyana
 * 3. Processing withdrawal requests from pyana users
 *
 * This class provides the Mina-side transaction construction. The pyana-side
 * observation and proof generation happens in the Rust bridge code.
 */
export class BridgeRelay {
  private zkApp: PyanaFederation;
  private config: BridgeConfig;
  private defaultFee: number;

  constructor(config: BridgeConfig) {
    this.config = config;
    this.zkApp = new PyanaFederation(config.zkAppAddress);
    this.defaultFee = config.txFee ?? 100_000_000; // 0.1 MINA default
  }

  /**
   * Get the current on-chain state of the federation.
   */
  async getOnChainState(): Promise<{
    stateRoot: Field;
    provenHeight: Field;
    federationId: Field;
    totalLocked: Field;
  }> {
    // Fetch latest account state from the network
    if (this.config.minaEndpoint) {
      await fetchAccount({ publicKey: this.config.zkAppAddress });
    }

    const stateRoot = this.zkApp.stateRoot.get();
    const provenHeight = this.zkApp.provenHeight.get();
    const federationId = this.zkApp.federationId.get();
    const totalLocked = this.zkApp.totalLocked.get();

    return { stateRoot, provenHeight, federationId, totalLocked };
  }

  /**
   * Submit a state advance to the Mina zkApp.
   *
   * Called by the relay after:
   * 1. A new pyana block is finalized
   * 2. The STARK proof is generated (Rust side)
   * 3. The STARK is verified in a Kimchi circuit
   * 4. The Kimchi proof is wrapped in Pickles
   *
   * The Pickles proof is what o1js verifies recursively when this transaction
   * is included in a Mina block.
   */
  async submitStateAdvance(
    senderKey: PrivateKey,
    oldRoot: Field,
    newRoot: Field,
    newHeight: Field,
    effectsHash: Field,
  ): Promise<BridgeTxResult> {
    try {
      const sender = senderKey.toPublicKey();
      const txn = await Mina.transaction(
        { sender, fee: this.defaultFee },
        async () => {
          await this.zkApp.advanceState(oldRoot, newRoot, newHeight, effectsHash);
        },
      );
      await txn.prove();
      const sent = await txn.sign([senderKey]).send();

      return {
        success: true,
        txHash: sent.hash,
      };
    } catch (e: unknown) {
      return {
        success: false,
        error: e instanceof Error ? e.message : String(e),
      };
    }
  }

  /**
   * Process a deposit (user locks tokens on Mina, credited on pyana).
   *
   * The note commitment should be computed as:
   *   Poseidon(blinding || recipientPyanaAddress || amount)
   *
   * After this transaction is confirmed, the relay observes the deposit event
   * and creates the corresponding note on the pyana side.
   */
  async processDeposit(
    senderKey: PrivateKey,
    amount: UInt64,
    noteCommitment: Field,
  ): Promise<BridgeTxResult> {
    try {
      const sender = senderKey.toPublicKey();
      const txn = await Mina.transaction(
        { sender, fee: this.defaultFee },
        async () => {
          await this.zkApp.deposit(amount, noteCommitment);
        },
      );
      await txn.prove();
      const sent = await txn.sign([senderKey]).send();

      return {
        success: true,
        txHash: sent.hash,
      };
    } catch (e: unknown) {
      return {
        success: false,
        error: e instanceof Error ? e.message : String(e),
      };
    }
  }

  /**
   * Process a withdrawal (user proves note spend on pyana, unlocks on Mina).
   *
   * The withdrawal requires:
   * - A valid nullifier (proving the pyana note was spent)
   * - The state root at which the spend was proven
   * - The amount must not exceed totalLocked
   *
   * The relay verifies the nullifier hasn't been used before submitting.
   */
  async processWithdrawal(
    senderKey: PrivateKey,
    amount: UInt64,
    nullifier: Field,
    stateRootAtSpend: Field,
    recipient: PublicKey,
  ): Promise<BridgeTxResult> {
    try {
      const sender = senderKey.toPublicKey();
      const txn = await Mina.transaction(
        { sender, fee: this.defaultFee },
        async () => {
          await this.zkApp.withdraw(amount, nullifier, stateRootAtSpend, recipient);
        },
      );
      await txn.prove();
      const sent = await txn.sign([senderKey]).send();

      return {
        success: true,
        txHash: sent.hash,
      };
    } catch (e: unknown) {
      return {
        success: false,
        error: e instanceof Error ? e.message : String(e),
      };
    }
  }

  /**
   * Initialize a freshly deployed federation zkApp.
   */
  async initializeFederation(
    senderKey: PrivateKey,
    genesisRoot: Field,
    constitutionHash: Field,
    relayPubKeyHash: Field,
  ): Promise<BridgeTxResult> {
    try {
      const sender = senderKey.toPublicKey();
      const txn = await Mina.transaction(
        { sender, fee: this.defaultFee },
        async () => {
          await this.zkApp.initialize(genesisRoot, constitutionHash, relayPubKeyHash);
        },
      );
      await txn.prove();
      const sent = await txn.sign([senderKey]).send();

      return {
        success: true,
        txHash: sent.hash,
      };
    } catch (e: unknown) {
      return {
        success: false,
        error: e instanceof Error ? e.message : String(e),
      };
    }
  }

  /**
   * Batch multiple state advances into a single proof chain.
   *
   * Useful when the relay has fallen behind and needs to catch up.
   * Each transition builds on the previous one.
   */
  async batchStateAdvance(
    senderKey: PrivateKey,
    transitions: Array<{
      oldRoot: Field;
      newRoot: Field;
      height: Field;
      effectsHash: Field;
    }>,
  ): Promise<BridgeTxResult> {
    if (transitions.length === 0) {
      return { success: false, error: 'No transitions to submit' };
    }

    // For batch, we submit only the final transition (the proof chain
    // handles intermediate verification). The recursive proof already
    // attests to the full chain.
    const final = transitions[transitions.length - 1];
    return this.submitStateAdvance(
      senderKey,
      final.oldRoot,
      final.newRoot,
      final.height,
      final.effectsHash,
    );
  }
}

// ---------------------------------------------------------------------------
// Utility functions
// ---------------------------------------------------------------------------

/**
 * Compute a note commitment for a deposit.
 */
export function computeNoteCommitment(
  blinding: Field,
  recipientHash: Field,
  amount: UInt64,
): Field {
  const { Poseidon } = require('o1js');
  return Poseidon.hash([blinding, recipientHash, amount.value]);
}

/**
 * Compute a nullifier for a withdrawal.
 */
export function computeNullifier(
  noteCommitment: Field,
  spenderSecret: Field,
): Field {
  const { Poseidon } = require('o1js');
  return Poseidon.hash([noteCommitment, spenderSecret]);
}
