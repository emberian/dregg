import { Field, Struct, UInt64, PublicKey, Poseidon, UInt32, Bool } from 'o1js';

// ---------------------------------------------------------------------------
// Core state types
// ---------------------------------------------------------------------------

/**
 * A pyana state root commitment. This is the Poseidon hash of the entire
 * federation's cell state tree at a given height.
 */
export class StateRoot extends Struct({
  /** The Poseidon2 hash committing to the cell state tree */
  root: Field,
  /** The block height at which this root was proven */
  height: Field,
}) {
  static genesis(): StateRoot {
    return new StateRoot({ root: Field(0), height: Field(0) });
  }

  hash(): Field {
    return Poseidon.hash([this.root, this.height]);
  }
}

// ---------------------------------------------------------------------------
// State transition types
// ---------------------------------------------------------------------------

/**
 * Represents a proven state transition from oldRoot to newRoot.
 * The effectsHash commits to the set of effects (cell mutations) that occurred.
 */
export class StateTransition extends Struct({
  oldRoot: Field,
  newRoot: Field,
  height: Field,
  effectsHash: Field,
}) {
  hash(): Field {
    return Poseidon.hash([
      this.oldRoot,
      this.newRoot,
      this.height,
      this.effectsHash,
    ]);
  }
}

// ---------------------------------------------------------------------------
// Merkle membership types
// ---------------------------------------------------------------------------

/** The depth of the cell state Merkle tree */
export const TREE_DEPTH = 32;

/**
 * A single Merkle witness node: the sibling hash and whether the path goes left.
 */
export class MerkleNode extends Struct({
  sibling: Field,
  isLeft: Bool,
}) {}

/**
 * A Merkle proof (witness) for a cell's inclusion in the state tree.
 * Uses a fixed depth of TREE_DEPTH.
 */
export class CellMerkleWitness extends Struct({
  /** Path from leaf to root. Index 0 is the leaf level. */
  path: Provable.Array(Field, TREE_DEPTH),
  /** Whether the cell is on the left at each level */
  isLeft: Provable.Array(Bool, TREE_DEPTH),
}) {
  /**
   * Compute the root given a leaf value.
   */
  computeRoot(leaf: Field): Field {
    let current = leaf;
    for (let i = 0; i < TREE_DEPTH; i++) {
      const left = Provable.if(this.isLeft[i], current, this.path[i]);
      const right = Provable.if(this.isLeft[i], this.path[i], current);
      current = Poseidon.hash([left, right]);
    }
    return current;
  }
}

// ---------------------------------------------------------------------------
// Bridge operation types
// ---------------------------------------------------------------------------

/**
 * A deposit note: locks tokens on Mina, to be credited on the pyana side.
 */
export class DepositNote extends Struct({
  /** Amount of MINA locked */
  amount: UInt64,
  /** Commitment to the pyana note (blinding + recipient + amount) */
  noteCommitment: Field,
  /** Mina block height at deposit time */
  minaHeight: UInt32,
}) {
  hash(): Field {
    return Poseidon.hash([
      this.amount.value,
      this.noteCommitment,
      this.minaHeight.value,
    ]);
  }
}

/**
 * A withdrawal proof: proves a note was spent on pyana, unlocks tokens on Mina.
 */
export class WithdrawalProof extends Struct({
  /** Amount to unlock */
  amount: UInt64,
  /** Nullifier proving the note was spent (prevents double-withdrawal) */
  nullifier: Field,
  /** The pyana state root at the time of spend */
  stateRootAtSpend: Field,
  /** Recipient on Mina */
  recipient: PublicKey,
}) {
  hash(): Field {
    return Poseidon.hash([
      this.amount.value,
      this.nullifier,
      this.stateRootAtSpend,
      ...this.recipient.toFields(),
    ]);
  }
}

// ---------------------------------------------------------------------------
// Capability types
// ---------------------------------------------------------------------------

/**
 * A capability attestation: proves that a principal holds a capability on pyana.
 * Used for bridging authorization tokens to Mina-native contracts.
 */
export class CapabilityAttestation extends Struct({
  /** Hash of the capability (resource + action + constraints) */
  capabilityHash: Field,
  /** The principal who holds it */
  holder: PublicKey,
  /** State root at which the capability was proven valid */
  provenAtRoot: Field,
  /** Expiry height (0 = no expiry) */
  expiryHeight: Field,
}) {
  hash(): Field {
    return Poseidon.hash([
      this.capabilityHash,
      ...this.holder.toFields(),
      this.provenAtRoot,
      this.expiryHeight,
    ]);
  }
}

// ---------------------------------------------------------------------------
// Event types
// ---------------------------------------------------------------------------

/**
 * Events emitted by the zkApp for relay observation.
 */
export class DepositEvent extends Struct({
  amount: UInt64,
  noteCommitment: Field,
}) {}

export class WithdrawalEvent extends Struct({
  amount: UInt64,
  nullifier: Field,
  recipient: PublicKey,
}) {}

export class StateAdvanceEvent extends Struct({
  oldRoot: Field,
  newRoot: Field,
  newHeight: Field,
}) {}

// We need this import for Provable.Array usage
import { Provable } from 'o1js';
