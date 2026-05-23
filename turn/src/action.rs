//! Action types: the building blocks of a call forest.
//!
//! An Action is a single operation in the call forest, analogous to Mina's AccountUpdate.
//! Each action targets a cell, specifies a method, carries authorization, declares
//! preconditions, and produces effects.

use pyana_cell::note_bridge::{BridgeReceipt, PortableNoteProof};
use pyana_cell::state::FieldElement;
use pyana_cell::{CapabilityRef, CellId, NoteCommitment, Nullifier, Preconditions, SealedBox};
#[allow(unused_imports)]
use pyana_cell::{ValueCommitment, ValueCommitmentBytes};
use serde::{Deserialize, Serialize};

use crate::conditional::{ConditionProof, ProofCondition};
use crate::escrow::{EscrowClaimAuth, EscrowCondition};

/// How much of the turn an action's signer commits to.
///
/// This controls what goes into the signing message:
/// - `Full`: signs over the entire turn hash (maximum binding, current default)
/// - `Partial`: signs over only this action's content + its position in the forest,
///   allowing composability where signers don't need to see other actions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CommitmentMode {
    /// Sign over the entire turn hash (current behavior — maximum binding).
    Full,
    /// Sign over only this action's hash + its position in the forest.
    /// Allows composability: signer doesn't need to see other actions.
    Partial,
}

impl Default for CommitmentMode {
    fn default() -> Self {
        CommitmentMode::Full
    }
}

/// A Symbol is a BLAKE3-hashed method or topic name, stored as a field element.
pub type Symbol = FieldElement;

/// Compute a symbol from a string name.
pub fn symbol(name: &str) -> Symbol {
    *blake3::hash(name.as_bytes()).as_bytes()
}

/// A single operation in the call forest.
///
/// Analogous to Mina's AccountUpdate: targets a cell, performs a method,
/// requires authorization, checks preconditions, and produces effects.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Action {
    /// Which cell is being acted upon.
    pub target: CellId,
    /// What operation (method name hashed to symbol).
    pub method: Symbol,
    /// Arguments to the operation.
    pub args: Vec<FieldElement>,
    /// How this action is authorized.
    pub authorization: Authorization,
    /// What must be true before this action can execute.
    pub preconditions: Preconditions,
    /// What changes result from this action.
    pub effects: Vec<Effect>,
    /// Can children use parent's capabilities?
    pub may_delegate: DelegationMode,
    /// How much of the turn this action's signer commits to.
    /// Full = signs over entire turn hash (default, maximum binding).
    /// Partial = signs over only this action + position (enables multi-party composition).
    #[serde(default)]
    pub commitment_mode: CommitmentMode,
    /// Signed balance modification (Mina-style).
    ///
    /// When set, this applies a signed delta to the target cell's balance:
    /// - Negative values withdraw (produce excess available to other actions)
    /// - Positive values deposit (consume excess from other actions)
    ///
    /// At turn end, the sum of all balance_change deltas must be zero (conservation law).
    /// This enables composable patterns like DEX fills without explicit Transfer pairing.
    #[serde(default)]
    pub balance_change: Option<i64>,
}

/// How an action is authorized.
///
/// Maps to the authorization models in Mina: signature, proof, or none.
/// Adds `Breadstuff` for capability token authorization.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Authorization {
    /// Ed25519 signature over the action hash (stored as two 32-byte halves).
    Signature([u8; 32], [u8; 32]),
    /// Zero-knowledge proof bytes with the bound (action, resource) pair.
    ///
    /// The `bound_action` and `bound_resource` fields record what the prover
    /// committed to at proving time (from `AuthRequest.action` and
    /// `app_id.or(service)`). The verifier recomputes the binding from these
    /// strings and checks it against the proof's public inputs.
    Proof {
        proof_bytes: Vec<u8>,
        bound_action: String,
        bound_resource: String,
    },
    /// Capability token hash (breadstuff authorization).
    Breadstuff([u8; 32]),
    /// No authorization provided (only valid if the cell's permissions allow it).
    ///
    /// Named `Unchecked` rather than `None` to make it grep-able and ensure
    /// code review flags its usage. Previously called `None`.
    #[serde(alias = "None")]
    Unchecked,
}

impl Authorization {
    /// Map this authorization to the corresponding AuthKind for permission checking.
    /// Returns None for Authorization::Unchecked and Authorization::Breadstuff (handled separately).
    pub fn to_auth_kind(&self) -> Option<pyana_cell::AuthKind> {
        match self {
            Authorization::Signature(_, _) => Some(pyana_cell::AuthKind::Signature),
            Authorization::Proof { .. } => Some(pyana_cell::AuthKind::Proof),
            Authorization::Breadstuff(_) => None,
            Authorization::Unchecked => None,
        }
    }

    /// Create a Signature authorization from a 64-byte signature.
    pub fn from_sig_bytes(bytes: [u8; 64]) -> Self {
        let mut r = [0u8; 32];
        let mut s = [0u8; 32];
        r.copy_from_slice(&bytes[..32]);
        s.copy_from_slice(&bytes[32..]);
        Authorization::Signature(r, s)
    }
}

/// Delegation mode for child cells. Currently only `None` is enforced;
/// `ParentsOwn` and `Inherit` are planned but not yet implemented in the executor.
/// Use three-party introduction (Effect::Introduce) for explicit capability delegation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DelegationMode {
    /// Children cannot use parent's capabilities.
    None,
    /// Children can use capabilities that the parent owns.
    /// NOTE: Not yet differentiated from `None` in capability-chain walking.
    /// The executor rejects missing capabilities identically for all modes.
    ParentsOwn,
    /// Children inherit parent's delegation mode transitively.
    /// NOTE: Not yet differentiated from `None` in capability-chain walking.
    /// The executor rejects missing capabilities identically for all modes.
    Inherit,
    /// Snapshot+refresh: child inherits parent's capabilities as a point-in-time
    /// snapshot. Child can act using the snapshot offline. Refresh to pick up new
    /// capabilities. Revocation is eventual (bounded by max_staleness).
    SnapshotRefresh,
}

/// An effect produced by an action — what changes in the ledger.
///
/// Analogous to Mina's balance_change + state updates, but generalized for
/// the cell model.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Effect {
    /// Set a state field on a cell.
    SetField {
        cell: CellId,
        index: usize,
        value: FieldElement,
    },
    /// Transfer computrons between cells.
    Transfer {
        from: CellId,
        to: CellId,
        amount: u64,
    },
    /// Grant a capability from one cell to another.
    GrantCapability {
        from: CellId,
        to: CellId,
        cap: CapabilityRef,
    },
    /// Revoke a capability from a cell.
    RevokeCapability { cell: CellId, slot: u32 },
    /// Emit an event from a cell (does not modify state, but is part of the receipt).
    EmitEvent { cell: CellId, event: Event },
    /// Increment a cell's nonce by 1.
    IncrementNonce { cell: CellId },
    /// Create a new cell in the ledger.
    CreateCell {
        public_key: [u8; 32],
        token_id: [u8; 32],
        balance: u64,
    },
    /// Update the permissions on a cell.
    ///
    /// SECURITY: This effect is always applied LAST within an action, after all
    /// other effects. Permission checks for all effects use the ORIGINAL permissions
    /// (snapshotted before any effects in this action run). This prevents an action
    /// from weakening permissions and then exploiting the weakened permissions in
    /// subsequent effects within the same action.
    SetPermissions {
        cell: CellId,
        new_permissions: pyana_cell::Permissions,
    },
    /// Update the verification key on a cell.
    ///
    /// SECURITY: Like SetPermissions, this is applied LAST within an action.
    SetVerificationKey {
        cell: CellId,
        new_vk: Option<pyana_cell::VerificationKey>,
    },
    /// Spend (consume) a note by revealing its nullifier.
    /// The proof must demonstrate: the nullifier corresponds to a valid note
    /// in the note tree, and the spender has authority.
    NoteSpend {
        nullifier: Nullifier,
        /// Root of the note tree at the time of proof generation.
        note_tree_root: [u8; 32],
        /// The value being released (for conservation tracking).
        value: u64,
        /// The asset type of the note being spent.
        asset_type: u64,
        /// The STARK spending proof (serialized). Proves:
        /// 1. The spender knows the note's opening (preimage of the commitment)
        /// 2. The nullifier is correctly derived from the note's secret data
        /// 3. The note commitment exists in the note tree (Merkle membership against the root)
        spending_proof: Vec<u8>,
        /// Optional Pedersen value commitment (compressed Ristretto point, 32 bytes).
        /// When present, the executor uses the committed conservation path instead
        /// of cleartext value comparison. All notes in a turn must either all have
        /// commitments or all lack them (mixed is rejected).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        value_commitment: Option<[u8; 32]>,
    },
    /// Create a new note (add commitment to note tree).
    NoteCreate {
        commitment: NoteCommitment,
        /// The value being locked in this note (for conservation tracking).
        value: u64,
        /// The asset type of the note being created.
        asset_type: u64,
        /// Encrypted note content (only recipient can decrypt).
        encrypted_note: Vec<u8>,
        /// Optional Pedersen value commitment (compressed Ristretto point, 32 bytes).
        /// When present, the executor uses the committed conservation path.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        value_commitment: Option<[u8; 32]>,
        /// Optional range proof attesting the committed value is in [0, 2^64).
        /// Required when value_commitment is present to prevent hidden inflation.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        range_proof: Option<Vec<u8>>,
    },
    /// Create a new sealer/unsealer pair for partition-tolerant capability transfer.
    CreateSealPair {
        /// Cell that will hold the sealer capability.
        sealer_holder: CellId,
        /// Cell that will hold the unsealer capability.
        unsealer_holder: CellId,
    },
    /// Seal a capability into an opaque box.
    Seal {
        /// The pair to seal with.
        pair_id: [u8; 32],
        /// The capability to seal.
        capability: CapabilityRef,
    },
    /// Unseal a box, recovering the original capability.
    Unseal {
        /// The sealed box to open.
        sealed_box: SealedBox,
        /// The cell that should receive the unsealed capability.
        recipient: CellId,
    },
    /// Spawn a child cell with snapshot+refresh delegation.
    /// The child inherits the actor's current c-list as a snapshot.
    SpawnWithDelegation {
        /// Public key of the new child cell.
        child_public_key: [u8; 32],
        /// Token domain of the new child cell.
        child_token_id: [u8; 32],
        /// Maximum acceptable staleness (seconds) for the delegation snapshot.
        max_staleness: u64,
    },
    /// Child refreshes its delegation snapshot from its parent.
    /// The actor must be the child cell (self-refresh).
    RefreshDelegation,
    /// Parent revokes delegation to a child by bumping its own epoch.
    /// The child's snapshot becomes stale relative to the new epoch.
    RevokeDelegation {
        /// The child cell whose delegation is being revoked.
        child: CellId,
    },
    /// Bridge a note from another federation by presenting a portable spending proof.
    ///
    /// When processed:
    /// 1. Verify the portable note proof against trusted federation roots.
    /// 2. Check the nullifier hasn't already been bridged (prevent double-bridge).
    /// 3. Create a new note commitment in the local note tree.
    /// 4. Credit the value to the receiving cell.
    BridgeMint {
        /// The portable proof carrying the STARK spending proof from the source federation.
        portable_proof: PortableNoteProof,
    },
    /// Phase 1: Lock a note for cross-federation bridge transfer.
    ///
    /// Instead of immediately burning the note, this creates a conditional lock.
    /// The note cannot be spent or re-locked until the bridge is finalized or cancelled.
    /// If the destination federation is offline or refuses, the note can be recovered
    /// after the timeout.
    BridgeLock {
        /// The nullifier of the note being locked.
        nullifier: [u8; 32],
        /// The destination federation's identity.
        destination: [u8; 32],
        /// The value being bridged.
        value: u64,
        /// The asset type being bridged.
        asset_type: u64,
        /// Block height at which this lock expires (can be cancelled after).
        timeout_height: u64,
        /// The serialized spending proof for destination to verify.
        spending_proof: Vec<u8>,
    },
    /// Phase 3: Finalize a bridge by presenting a valid receipt from the destination.
    ///
    /// The receipt proves the destination federation minted the value. On success,
    /// the note's nullifier becomes permanently spent.
    BridgeFinalize {
        /// The nullifier of the pending bridge to finalize.
        nullifier: [u8; 32],
        /// The signed receipt from the destination federation.
        receipt: BridgeReceipt,
    },
    /// Phase 4: Cancel a bridge after the timeout has expired.
    ///
    /// If the bridge was not finalized before the timeout height, the note is
    /// unlocked and returned to the owner. Prevents value-trapping when the
    /// destination federation is offline or refuses the bridge.
    BridgeCancel {
        /// The nullifier of the pending bridge to cancel.
        nullifier: [u8; 32],
    },
    /// Pipelined send: dispatch an action to the result of a pending turn.
    /// Three-party introduction.
    Introduce {
        introducer: CellId,
        recipient: CellId,
        target: CellId,
        permissions: pyana_cell::AuthRequired,
    },
    PipelinedSend {
        /// The eventual target — resolved during pipeline execution.
        target: crate::eventual::EventualRef,
        /// The action to send to the resolved target.
        action: Box<Action>,
    },
    /// Create a bonded proof obligation: the actor commits to delivering a proof
    /// satisfying `condition` before `deadline_height`, with `stake` locked as bond.
    /// If the proof is not delivered, the stake is slashed to the beneficiary.
    CreateObligation {
        /// Who benefits (receives stake on failure, or whose ConditionalTurn resolves).
        beneficiary: CellId,
        /// What must be proven.
        condition: ProofCondition,
        /// Federation height deadline.
        deadline_height: u64,
        /// Note commitment representing the locked stake.
        stake: NoteCommitment,
        /// Numeric amount to lock from the obligor's cell balance as bond.
        /// This is subtracted on creation, returned on fulfillment, or transferred
        /// to the beneficiary on slash.
        stake_amount: u64,
    },
    /// Fulfill a proof obligation by presenting the required proof.
    /// On success, the locked stake is returned to the obligor.
    FulfillObligation {
        /// ID of the obligation being fulfilled.
        obligation_id: [u8; 32],
        /// The proof satisfying the obligation's condition.
        proof: ConditionProof,
    },
    /// Slash an expired obligation: transfer the locked stake to the beneficiary.
    /// Only valid after the obligation's deadline has passed without fulfillment.
    SlashObligation {
        /// ID of the obligation to slash.
        obligation_id: [u8; 32],
    },
    /// Create a conditional escrow: lock value from the sender, release to recipient
    /// if `condition` is met, else allow refund after `timeout_height`.
    CreateEscrow {
        /// The escrow creator (funds source).
        cell: CellId,
        /// Who gets the funds if condition is met.
        recipient: CellId,
        /// Amount to lock in escrow.
        amount: u64,
        /// What must be satisfied for release.
        condition: EscrowCondition,
        /// Block height after which refund is allowed.
        timeout_height: u64,
        /// Unique identifier for this escrow.
        escrow_id: [u8; 32],
    },
    /// Release an escrow by satisfying its condition.
    /// Transfers the escrowed amount to the recipient.
    ReleaseEscrow {
        /// ID of the escrow to release.
        escrow_id: [u8; 32],
        /// Proof satisfying the condition (if condition requires one).
        proof: Option<Vec<u8>>,
    },
    /// Refund an escrow after its timeout has passed.
    /// Returns the escrowed amount to the original creator.
    RefundEscrow {
        /// ID of the escrow to refund.
        escrow_id: [u8; 32],
    },
    /// Create a privacy-preserving committed escrow.
    ///
    /// All party identities and the value are hidden behind cryptographic commitments.
    /// The range proof must demonstrate the committed value is in `[0, 2^64)`.
    /// The value commitment encodes the actual locked amount (verified via range proof),
    /// and the corresponding cleartext amount is deducted from the creator's balance.
    CreateCommittedEscrow {
        /// Commitment to the creator's identity (BLAKE3 of CellId + blinding).
        creator_commitment: [u8; 32],
        /// Commitment to the recipient's identity (BLAKE3 of CellId + blinding).
        recipient_commitment: [u8; 32],
        /// Pedersen commitment to the escrowed value (compressed Ristretto).
        value_commitment: ValueCommitmentBytes,
        /// Commitment to the escrow condition (BLAKE3 of condition + nonce).
        condition_commitment: [u8; 32],
        /// Block height after which refund is allowed (public for enforcement).
        timeout_height: u64,
        /// Deterministic escrow ID (derived from commitments).
        escrow_id: [u8; 32],
        /// Range proof showing the committed value is in [0, 2^64).
        range_proof: Vec<u8>,
        /// The actual amount to lock (must match the value commitment opening).
        /// This is needed to deduct from the creator's balance; the commitment
        /// binds this value cryptographically via the range proof.
        amount: u64,
    },
    /// Release a committed escrow by proving recipient identity.
    ///
    /// The claimer proves they are the recipient by revealing the opening of the
    /// recipient_commitment and signing the escrow_id. In the initial implementation
    /// this is a signed statement; a future version will accept a ZK presentation
    /// proof bound to the escrow_id.
    ReleaseCommittedEscrow {
        /// ID of the committed escrow to release.
        escrow_id: [u8; 32],
        /// Authorization proving the claimer is the committed recipient.
        claim_auth: EscrowClaimAuth,
        /// The recipient CellId to credit (must match the claim_auth opening).
        recipient: CellId,
    },
    /// Refund a committed escrow after timeout by proving creator identity.
    ///
    /// The creator proves their identity by revealing the opening of the
    /// creator_commitment and signing the escrow_id.
    RefundCommittedEscrow {
        /// ID of the committed escrow to refund.
        escrow_id: [u8; 32],
        /// Authorization proving the claimer is the committed creator.
        claim_auth: EscrowClaimAuth,
        /// The creator CellId to credit (must match the claim_auth opening).
        creator: CellId,
    },
    /// Exercise a capability from the actor's c-list in one atomic step.
    ///
    /// This is the categorical "evaluation map" (eval: B^A x A -> B): look up a
    /// capability by slot, verify permissions, and execute inner effects against
    /// the capability's target cell. Combines c-list lookup + sub-action into a
    /// single effect, eliminating the two-step lookup-then-submit pattern.
    ExerciseViaCapability {
        /// Which slot in the actor's c-list to exercise.
        cap_slot: u32,
        /// The effects to perform on the target cell (resolved from the capability).
        inner_effects: Vec<Effect>,
    },
}

/// An event emitted by an action.
///
/// Events are logged in the receipt but do not modify ledger state.
/// They are indexed by topic for off-chain consumption.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Event {
    /// The topic of this event (hashed method/event name).
    pub topic: Symbol,
    /// Arbitrary data fields.
    pub data: Vec<FieldElement>,
}

impl Action {
    /// Compute the BLAKE3 hash of this action (for Merkle tree inclusion).
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Domain separation: prevents type confusion with other hash preimages.
        hasher.update(b"pyana-action-v2:");
        hasher.update(self.target.as_bytes());
        hasher.update(&self.method);
        for arg in &self.args {
            hasher.update(arg);
        }
        // Hash authorization discriminant + data.
        match &self.authorization {
            Authorization::Signature(r, s) => {
                hasher.update(&[0u8]);
                hasher.update(r);
                hasher.update(s);
            }
            Authorization::Proof {
                proof_bytes,
                bound_action,
                bound_resource,
            } => {
                hasher.update(&[1u8]);
                hasher.update(proof_bytes);
                hasher.update(bound_action.as_bytes());
                hasher.update(bound_resource.as_bytes());
            }
            Authorization::Breadstuff(token) => {
                hasher.update(&[2u8]);
                hasher.update(token);
            }
            Authorization::Unchecked => {
                hasher.update(&[3u8]);
            }
        }
        // Hash delegation mode.
        hasher.update(&[self.may_delegate as u8]);
        // Hash commitment mode.
        hasher.update(&[self.commitment_mode as u8]);
        // Hash balance_change.
        if let Some(delta) = self.balance_change {
            hasher.update(&[1u8]); // discriminant: Some
            hasher.update(&delta.to_le_bytes());
        } else {
            hasher.update(&[0u8]); // discriminant: None
        }
        // Hash effects.
        for effect in &self.effects {
            hasher.update(&effect.hash());
        }
        // Hash preconditions to prevent downgrade attacks where an attacker removes
        // preconditions (e.g., minimum balance guards) from a signed action.
        let preconds_bytes = postcard::to_allocvec(&self.preconditions).unwrap_or_default();
        hasher.update(&preconds_bytes);
        *hasher.finalize().as_bytes()
    }
}

impl Effect {
    /// Compute the BLAKE3 hash of this effect.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        match self {
            Effect::SetField { cell, index, value } => {
                hasher.update(&[0u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&(*index as u64).to_le_bytes());
                hasher.update(value);
            }
            Effect::Transfer { from, to, amount } => {
                hasher.update(&[1u8]);
                hasher.update(from.as_bytes());
                hasher.update(to.as_bytes());
                hasher.update(&amount.to_le_bytes());
            }
            Effect::GrantCapability { from, to, cap } => {
                hasher.update(&[2u8]);
                hasher.update(from.as_bytes());
                hasher.update(to.as_bytes());
                hasher.update(cap.target.as_bytes());
                hasher.update(&cap.slot.to_le_bytes());
            }
            Effect::RevokeCapability { cell, slot } => {
                hasher.update(&[3u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&slot.to_le_bytes());
            }
            Effect::EmitEvent { cell, event } => {
                hasher.update(&[4u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&event.topic);
                for d in &event.data {
                    hasher.update(d);
                }
            }
            Effect::IncrementNonce { cell } => {
                hasher.update(&[5u8]);
                hasher.update(cell.as_bytes());
            }
            Effect::CreateCell {
                public_key,
                token_id,
                balance,
            } => {
                hasher.update(&[6u8]);
                hasher.update(public_key);
                hasher.update(token_id);
                hasher.update(&balance.to_le_bytes());
            }
            Effect::SetPermissions {
                cell,
                new_permissions,
            } => {
                hasher.update(&[7u8]);
                hasher.update(cell.as_bytes());
                // Hash each permission field's discriminant.
                let perms = [
                    &new_permissions.send,
                    &new_permissions.receive,
                    &new_permissions.set_state,
                    &new_permissions.set_permissions,
                    &new_permissions.set_verification_key,
                    &new_permissions.increment_nonce,
                    &new_permissions.delegate,
                    &new_permissions.access,
                ];
                for p in perms {
                    let disc = match p {
                        pyana_cell::AuthRequired::None => 0u8,
                        pyana_cell::AuthRequired::Signature => 1u8,
                        pyana_cell::AuthRequired::Proof => 2u8,
                        pyana_cell::AuthRequired::Either => 3u8,
                        pyana_cell::AuthRequired::Impossible => 4u8,
                    };
                    hasher.update(&[disc]);
                }
            }
            Effect::SetVerificationKey { cell, new_vk } => {
                hasher.update(&[8u8]);
                hasher.update(cell.as_bytes());
                if let Some(vk) = new_vk {
                    hasher.update(&[1u8]);
                    hasher.update(&vk.data);
                } else {
                    hasher.update(&[0u8]);
                }
            }
            Effect::NoteSpend {
                nullifier,
                note_tree_root,
                value,
                asset_type,
                spending_proof,
                value_commitment,
            } => {
                hasher.update(&[9u8]);
                hasher.update(&nullifier.0);
                hasher.update(note_tree_root);
                hasher.update(&value.to_le_bytes());
                hasher.update(&asset_type.to_le_bytes());
                hasher.update(spending_proof);
                match value_commitment {
                    Some(vc) => {
                        hasher.update(&[1u8]);
                        hasher.update(vc);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
            }
            Effect::NoteCreate {
                commitment,
                value,
                asset_type,
                encrypted_note,
                value_commitment,
                range_proof,
            } => {
                hasher.update(&[10u8]);
                hasher.update(&commitment.0);
                hasher.update(&value.to_le_bytes());
                hasher.update(&asset_type.to_le_bytes());
                hasher.update(&(encrypted_note.len() as u64).to_le_bytes());
                hasher.update(encrypted_note);
                match value_commitment {
                    Some(vc) => {
                        hasher.update(&[1u8]);
                        hasher.update(vc);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
                match range_proof {
                    Some(rp) => {
                        hasher.update(&[1u8]);
                        hasher.update(&(rp.len() as u64).to_le_bytes());
                        hasher.update(rp);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
            }
            Effect::CreateSealPair {
                sealer_holder,
                unsealer_holder,
            } => {
                hasher.update(&[13u8]);
                hasher.update(sealer_holder.as_bytes());
                hasher.update(unsealer_holder.as_bytes());
            }
            Effect::Seal {
                pair_id,
                capability,
            } => {
                hasher.update(&[14u8]);
                hasher.update(pair_id);
                hasher.update(capability.target.as_bytes());
                hasher.update(&capability.slot.to_le_bytes());
            }
            Effect::Unseal {
                sealed_box,
                recipient,
            } => {
                hasher.update(&[15u8]);
                hasher.update(&sealed_box.pair_id);
                hasher.update(&sealed_box.ephemeral_public);
                hasher.update(&sealed_box.commitment);
                hasher.update(&sealed_box.nonce);
                hasher.update(recipient.as_bytes());
            }
            Effect::BridgeMint { portable_proof } => {
                hasher.update(&[21u8]);
                hasher.update(&portable_proof.nullifier);
                hasher.update(&portable_proof.destination_commitment.0);
                hasher.update(&portable_proof.value.to_le_bytes());
                hasher.update(&portable_proof.asset_type.to_le_bytes());
                hasher.update(&portable_proof.source_root.merkle_root);
                hasher.update(&portable_proof.source_root.height.to_le_bytes());
            }
            Effect::BridgeLock {
                nullifier,
                destination,
                value,
                asset_type,
                timeout_height,
                spending_proof,
            } => {
                hasher.update(&[26u8]);
                hasher.update(nullifier);
                hasher.update(destination);
                hasher.update(&value.to_le_bytes());
                hasher.update(&asset_type.to_le_bytes());
                hasher.update(&timeout_height.to_le_bytes());
                hasher.update(&(spending_proof.len() as u64).to_le_bytes());
                hasher.update(spending_proof);
            }
            Effect::BridgeFinalize { nullifier, receipt } => {
                hasher.update(&[27u8]);
                hasher.update(nullifier);
                hasher.update(&receipt.nullifier);
                hasher.update(&receipt.destination_federation);
                hasher.update(&receipt.mint_height.to_le_bytes());
                hasher.update(&receipt.signature);
            }
            Effect::BridgeCancel { nullifier } => {
                hasher.update(&[28u8]);
                hasher.update(nullifier);
            }
            Effect::Introduce {
                introducer,
                recipient,
                target,
                permissions,
            } => {
                hasher.update(&[17u8]);
                hasher.update(introducer.as_bytes());
                hasher.update(recipient.as_bytes());
                hasher.update(target.as_bytes());
                hasher.update(&[match permissions {
                    pyana_cell::AuthRequired::None => 0u8,
                    pyana_cell::AuthRequired::Signature => 1u8,
                    pyana_cell::AuthRequired::Proof => 2u8,
                    pyana_cell::AuthRequired::Either => 3u8,
                    pyana_cell::AuthRequired::Impossible => 4u8,
                }]);
            }
            Effect::PipelinedSend { target, action } => {
                hasher.update(&[16u8]);
                hasher.update(&target.source_turn);
                hasher.update(&target.output_slot.to_le_bytes());
                hasher.update(&action.hash());
            }
            Effect::CreateObligation {
                beneficiary,
                condition,
                deadline_height,
                stake,
                stake_amount,
            } => {
                hasher.update(&[22u8]);
                hasher.update(beneficiary.as_bytes());
                hasher.update(&deadline_height.to_le_bytes());
                hasher.update(&stake.0);
                hasher.update(&stake_amount.to_le_bytes());
                // Include condition discriminant.
                match condition {
                    ProofCondition::HashPreimage { hash } => {
                        hasher.update(&[0u8]);
                        hasher.update(hash);
                    }
                    ProofCondition::RemoteProof {
                        federation_root,
                        expected_air,
                        expected_conclusion,
                    } => {
                        hasher.update(&[1u8]);
                        hasher.update(federation_root);
                        hasher.update(expected_air.as_bytes());
                        hasher.update(&expected_conclusion.to_le_bytes());
                    }
                    ProofCondition::LocalProof {
                        expected_air,
                        expected_public_inputs,
                    } => {
                        hasher.update(&[2u8]);
                        hasher.update(expected_air.as_bytes());
                        for pi in expected_public_inputs {
                            hasher.update(&pi.to_le_bytes());
                        }
                    }
                    ProofCondition::TurnExecuted { turn_hash } => {
                        hasher.update(&[3u8]);
                        hasher.update(turn_hash);
                    }
                }
            }
            Effect::FulfillObligation {
                obligation_id,
                proof,
            } => {
                hasher.update(&[23u8]);
                hasher.update(obligation_id);
                match proof {
                    ConditionProof::Preimage(preimage) => {
                        hasher.update(&[0u8]);
                        hasher.update(preimage);
                    }
                    ConditionProof::StarkProof {
                        proof_bytes,
                        federation_root,
                        public_outputs,
                        air_name,
                    } => {
                        hasher.update(&[1u8]);
                        hasher.update(&(proof_bytes.len() as u64).to_le_bytes());
                        hasher.update(proof_bytes);
                        hasher.update(federation_root);
                        for po in public_outputs {
                            hasher.update(&po.to_le_bytes());
                        }
                        hasher.update(air_name.as_bytes());
                    }
                    ConditionProof::Receipt(receipt) => {
                        hasher.update(&[2u8]);
                        hasher.update(&receipt.turn_hash);
                    }
                }
            }
            Effect::SlashObligation { obligation_id } => {
                hasher.update(&[24u8]);
                hasher.update(obligation_id);
            }
            Effect::CreateEscrow {
                cell,
                recipient,
                amount,
                condition,
                timeout_height,
                escrow_id,
            } => {
                hasher.update(&[29u8]);
                hasher.update(cell.as_bytes());
                hasher.update(recipient.as_bytes());
                hasher.update(&amount.to_le_bytes());
                hasher.update(&timeout_height.to_le_bytes());
                hasher.update(escrow_id);
                match condition {
                    EscrowCondition::ProofPresented { verification_key } => {
                        hasher.update(&[0u8]);
                        hasher.update(verification_key);
                    }
                    EscrowCondition::SignedByAll { signers } => {
                        hasher.update(&[1u8]);
                        for signer in signers {
                            hasher.update(signer);
                        }
                    }
                    EscrowCondition::PredicateSatisfied { predicate_hash } => {
                        hasher.update(&[2u8]);
                        hasher.update(predicate_hash);
                    }
                }
            }
            Effect::ReleaseEscrow { escrow_id, proof } => {
                hasher.update(&[30u8]);
                hasher.update(escrow_id);
                if let Some(p) = proof {
                    hasher.update(&[1u8]);
                    hasher.update(&(p.len() as u64).to_le_bytes());
                    hasher.update(p);
                } else {
                    hasher.update(&[0u8]);
                }
            }
            Effect::RefundEscrow { escrow_id } => {
                hasher.update(&[31u8]);
                hasher.update(escrow_id);
            }
            Effect::CreateCommittedEscrow {
                creator_commitment,
                recipient_commitment,
                value_commitment,
                condition_commitment,
                timeout_height,
                escrow_id,
                range_proof,
                amount,
            } => {
                hasher.update(&[32u8]);
                hasher.update(creator_commitment);
                hasher.update(recipient_commitment);
                hasher.update(&value_commitment.0);
                hasher.update(condition_commitment);
                hasher.update(&timeout_height.to_le_bytes());
                hasher.update(escrow_id);
                hasher.update(&(range_proof.len() as u64).to_le_bytes());
                hasher.update(range_proof);
                hasher.update(&amount.to_le_bytes());
            }
            Effect::ReleaseCommittedEscrow {
                escrow_id,
                claim_auth,
                recipient,
            } => {
                hasher.update(&[33u8]);
                hasher.update(escrow_id);
                hasher.update(&claim_auth.public_key);
                hasher.update(&claim_auth.blinding);
                hasher.update(&claim_auth.signature);
                hasher.update(recipient.as_bytes());
            }
            Effect::RefundCommittedEscrow {
                escrow_id,
                claim_auth,
                creator,
            } => {
                hasher.update(&[34u8]);
                hasher.update(escrow_id);
                hasher.update(&claim_auth.public_key);
                hasher.update(&claim_auth.blinding);
                hasher.update(&claim_auth.signature);
                hasher.update(creator.as_bytes());
            }
            Effect::SpawnWithDelegation {
                child_public_key,
                child_token_id,
                max_staleness,
            } => {
                hasher.update(&[18u8]);
                hasher.update(child_public_key);
                hasher.update(child_token_id);
                hasher.update(&max_staleness.to_le_bytes());
            }
            Effect::RefreshDelegation => {
                hasher.update(&[19u8]);
            }
            Effect::RevokeDelegation { child } => {
                hasher.update(&[20u8]);
                hasher.update(child.as_bytes());
            }
            Effect::ExerciseViaCapability {
                cap_slot,
                inner_effects,
            } => {
                hasher.update(&[25u8]);
                hasher.update(&cap_slot.to_le_bytes());
                for inner in inner_effects {
                    hasher.update(&inner.hash());
                }
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Return the number of bytes of data in this effect (for cost estimation).
    pub fn data_bytes(&self) -> usize {
        match self {
            Effect::SetField { .. } => 32 + 8 + 32, // cell + index + value
            Effect::Transfer { .. } => 32 + 32 + 8,
            Effect::GrantCapability { .. } => 32 + 32 + 36,
            Effect::RevokeCapability { .. } => 32 + 4,
            Effect::EmitEvent { event, .. } => 32 + 32 + event.data.len() * 32,
            Effect::IncrementNonce { .. } => 32,
            Effect::CreateCell { .. } => 32 + 32 + 8,
            Effect::SetPermissions { .. } => 32 + 8 * 1, // cell + 8 permission fields
            Effect::SetVerificationKey { new_vk, .. } => {
                32 + new_vk.as_ref().map_or(1, |vk| 1 + vk.data.len())
            }
            Effect::NoteSpend { spending_proof, value_commitment, .. } => {
                32 + 32 + 8 + 8 + spending_proof.len() + value_commitment.map_or(0, |_| 32) // nullifier + root + value + asset_type + proof + opt commitment
            }
            Effect::NoteCreate { encrypted_note, value_commitment, range_proof, .. } => {
                32 + 8 + 8 + encrypted_note.len() + value_commitment.map_or(0, |_| 32) + range_proof.as_ref().map_or(0, |rp| rp.len()) // commitment + value + asset_type + ciphertext + opt vc + opt rp
            }
            Effect::CreateSealPair { .. } => 32 + 32,
            Effect::Seal { .. } => 32 + 32 + 4,
            Effect::Unseal { sealed_box, .. } => {
                32 + 32 + 32 + sealed_box.ciphertext.len() + 32 + 32
            }
            Effect::BridgeMint { portable_proof } => {
                32 + 32 + 8 + 8 + portable_proof.spending_proof.len() // nullifier + commitment + value + asset + proof
            }
            Effect::BridgeLock { spending_proof, .. } => {
                32 + 32 + 8 + 8 + 8 + spending_proof.len() // nullifier + dest + value + asset + timeout + proof
            }
            Effect::BridgeFinalize { .. } => {
                32 + 32 + 32 + 8 + 64 // nullifier + receipt(nullifier + dest + height + sig)
            }
            Effect::BridgeCancel { .. } => 32, // nullifier
            Effect::PipelinedSend { .. } => 32 + 4 + 32,
            Effect::Introduce { .. } => 97,
            Effect::SpawnWithDelegation { .. } => 32 + 32 + 8,
            Effect::RefreshDelegation => 0,
            Effect::RevokeDelegation { .. } => 32,
            Effect::CreateObligation { stake, .. } => {
                32 + 32 + 8 + stake.0.len() + 8 // beneficiary + condition + deadline + stake + stake_amount
            }
            Effect::FulfillObligation { proof, .. } => {
                32 + match proof {
                    ConditionProof::Preimage(_) => 32,
                    ConditionProof::StarkProof { proof_bytes, .. } => proof_bytes.len() + 32 + 32,
                    ConditionProof::Receipt(_) => 32,
                }
            }
            Effect::SlashObligation { .. } => 32,
            Effect::CreateEscrow { condition, .. } => {
                32 + 32
                    + 8
                    + 8
                    + 32
                    + match condition {
                        EscrowCondition::ProofPresented { .. } => 32,
                        EscrowCondition::SignedByAll { signers } => signers.len() * 32,
                        EscrowCondition::PredicateSatisfied { .. } => 32,
                    }
            }
            Effect::ReleaseEscrow { proof, .. } => 32 + proof.as_ref().map_or(0, |p| p.len()),
            Effect::RefundEscrow { .. } => 32,
            Effect::CreateCommittedEscrow { range_proof, .. } => {
                32 + 32 + 32 + 32 + 8 + 32 + range_proof.len() + 8
                // creator_comm + recipient_comm + value_comm + condition_comm + timeout + escrow_id + range_proof + amount
            }
            Effect::ReleaseCommittedEscrow { .. } => {
                32 + 32 + 32 + 64 + 32 // escrow_id + pubkey + blinding + signature + recipient
            }
            Effect::RefundCommittedEscrow { .. } => {
                32 + 32 + 32 + 64 + 32 // escrow_id + pubkey + blinding + signature + creator
            }
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                4 + inner_effects.iter().map(|e| e.data_bytes()).sum::<usize>()
            }
        }
    }

    /// Returns true if this effect is a permission-changing effect.
    ///
    /// Permission-changing effects (SetPermissions, SetVerificationKey) are always
    /// applied LAST within an action to prevent an action from weakening permissions
    /// and exploiting the weakened state in subsequent effects.
    pub fn is_permission_effect(&self) -> bool {
        matches!(
            self,
            Effect::SetPermissions { .. } | Effect::SetVerificationKey { .. }
        )
    }
}

impl Event {
    /// Create a new event.
    pub fn new(topic: Symbol, data: Vec<FieldElement>) -> Self {
        Self { topic, data }
    }
}
