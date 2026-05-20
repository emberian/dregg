//! TurnComposer: multi-party turn composition for atomic swaps and DEX fills.
//!
//! Enables independent parties to sign their own actions with `CommitmentMode::Partial`,
//! then a composer (e.g., a DEX matcher) assembles them into a complete `Turn`.
//!
//! # Design
//!
//! In Mina, `use_full_commitment = false` lets a party sign their AccountUpdate
//! without seeing the rest of the transaction. Pyana's `CommitmentMode::Partial`
//! provides the same capability: the signer commits to their action's content
//! and position, but not to what other actions exist in the turn.
//!
//! # Example: Atomic Swap
//!
//! ```text
//! Alice signs: "withdraw 100 USDC from my cell" (partial commitment)
//! Bob signs:   "withdraw 1 ETH from my cell" (partial commitment)
//! Matcher:     composes both + adds deposit actions → single atomic turn
//! ```

use ed25519_dalek::{Signature, VerifyingKey, Verifier};
use pyana_cell::CellId;

use crate::action::{Action, CommitmentMode};
use crate::executor::TurnExecutor;
use crate::forest::CallForest;
use crate::turn::Turn;

/// Errors that can occur during turn composition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComposeError {
    /// A fragment contains an action with Full commitment mode.
    /// Fragments must use Partial commitment for composability.
    FullCommitmentInFragment { fragment_index: usize, action_index: usize },

    /// Signature verification failed for a fragment's action.
    InvalidSignature {
        fragment_index: usize,
        action_index: usize,
        reason: String,
    },

    /// The number of signatures doesn't match the number of actions in a fragment.
    SignatureCountMismatch {
        fragment_index: usize,
        actions: usize,
        signatures: usize,
    },

    /// The composed turn has non-zero excess (balance_change deltas don't sum to zero).
    ExcessImbalance { total_excess: i64 },

    /// No fragments were added to compose.
    EmptyComposition,

    /// A fragment action is missing authorization.
    MissingAuthorization { fragment_index: usize, action_index: usize },
}

impl core::fmt::Display for ComposeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ComposeError::FullCommitmentInFragment { fragment_index, action_index } => {
                write!(
                    f,
                    "fragment {fragment_index}, action {action_index}: \
                     must use CommitmentMode::Partial for composability"
                )
            }
            ComposeError::InvalidSignature { fragment_index, action_index, reason } => {
                write!(
                    f,
                    "fragment {fragment_index}, action {action_index}: \
                     signature verification failed: {reason}"
                )
            }
            ComposeError::SignatureCountMismatch { fragment_index, actions, signatures } => {
                write!(
                    f,
                    "fragment {fragment_index}: {actions} actions but {signatures} signatures"
                )
            }
            ComposeError::ExcessImbalance { total_excess } => {
                write!(f, "balance_change excess is non-zero: {total_excess}")
            }
            ComposeError::EmptyComposition => {
                write!(f, "no fragments to compose")
            }
            ComposeError::MissingAuthorization { fragment_index, action_index } => {
                write!(
                    f,
                    "fragment {fragment_index}, action {action_index}: missing authorization"
                )
            }
        }
    }
}

impl std::error::Error for ComposeError {}

/// A signed fragment is one party's contribution to a composed turn.
///
/// Each fragment contains one or more actions (all with `CommitmentMode::Partial`)
/// and corresponding signatures. The actions already have their `authorization`
/// field populated with the signature.
#[derive(Clone, Debug)]
pub struct SignedFragment {
    /// The actions this party contributes (must all be CommitmentMode::Partial).
    pub actions: Vec<Action>,
    /// Ed25519 signatures for each action (one per action, in order).
    /// Each signature is over `compute_partial_signing_message(action, position, forest_root)`.
    pub signatures: Vec<[u8; 64]>,
    /// The public key that signed these actions (for pre-verification).
    pub signer: [u8; 32],
}

/// Composes independently-signed actions into a single atomic turn.
///
/// The composer is used by a third party (e.g., DEX matcher, relay, sequencer)
/// to assemble fragments from multiple signers into one Turn that executes atomically.
pub struct TurnComposer {
    /// The agent cell that will pay the fee and own the turn.
    fee_payer: CellId,
    /// The fee for the composed turn.
    fee: u64,
    /// The agent's nonce for replay protection.
    nonce: u64,
    /// Collected fragments from various parties.
    fragments: Vec<SignedFragment>,
    /// Additional actions added by the composer (e.g., settlement/deposit actions).
    /// These use Full commitment mode and are signed by the fee payer.
    settlement_actions: Vec<Action>,
    /// Optional memo.
    memo: Option<String>,
    /// Optional expiration.
    valid_until: Option<i64>,
}

impl TurnComposer {
    /// Create a new composer for the given fee payer.
    pub fn new(fee_payer: CellId, fee: u64, nonce: u64) -> Self {
        TurnComposer {
            fee_payer,
            fee,
            nonce,
            fragments: Vec::new(),
            settlement_actions: Vec::new(),
            memo: None,
            valid_until: None,
        }
    }

    /// Set an optional memo for the composed turn.
    pub fn set_memo(&mut self, memo: impl Into<String>) -> &mut Self {
        self.memo = Some(memo.into());
        self
    }

    /// Set an optional expiration for the composed turn.
    pub fn set_valid_until(&mut self, ts: i64) -> &mut Self {
        self.valid_until = Some(ts);
        self
    }

    /// Add a signed fragment from one party.
    ///
    /// Validates that all actions in the fragment use `CommitmentMode::Partial`
    /// and that the signature count matches the action count.
    pub fn add_fragment(&mut self, fragment: SignedFragment) -> Result<(), ComposeError> {
        let frag_idx = self.fragments.len();

        // Validate signature count.
        if fragment.actions.len() != fragment.signatures.len() {
            return Err(ComposeError::SignatureCountMismatch {
                fragment_index: frag_idx,
                actions: fragment.actions.len(),
                signatures: fragment.signatures.len(),
            });
        }

        // Validate all actions use Partial commitment.
        for (action_idx, action) in fragment.actions.iter().enumerate() {
            if action.commitment_mode != CommitmentMode::Partial {
                return Err(ComposeError::FullCommitmentInFragment {
                    fragment_index: frag_idx,
                    action_index: action_idx,
                });
            }
        }

        self.fragments.push(fragment);
        Ok(())
    }

    /// Add a settlement action (added by the composer, not a fragment signer).
    ///
    /// Settlement actions are used to complete swaps, e.g., deposit actions
    /// that credit one party with what the other party withdrew.
    pub fn add_settlement_action(&mut self, action: Action) -> &mut Self {
        self.settlement_actions.push(action);
        self
    }

    /// Compose all fragments into a final Turn.
    ///
    /// This method:
    /// 1. Validates all fragment signatures against partial commitment messages.
    /// 2. Checks that the total `balance_change` excess sums to zero.
    /// 3. Assembles a CallForest with all actions (fragments first, then settlements).
    /// 4. Returns the complete Turn ready for executor application.
    pub fn compose(self) -> Result<Turn, ComposeError> {
        if self.fragments.is_empty() && self.settlement_actions.is_empty() {
            return Err(ComposeError::EmptyComposition);
        }

        // Phase 1: Collect all actions and compute their positions.
        let mut all_actions: Vec<Action> = Vec::new();

        // Fragment actions first.
        for fragment in &self.fragments {
            all_actions.extend(fragment.actions.iter().cloned());
        }

        // Settlement actions after.
        all_actions.extend(self.settlement_actions.iter().cloned());

        // Phase 2: Build the forest so we can compute its root hash.
        let mut forest = CallForest::new();
        for action in &all_actions {
            forest.add_root(action.clone());
        }
        let forest_root_hash = forest.hash();

        // Phase 3: Verify fragment signatures against partial commitment messages.
        let mut position = 0usize;
        for (frag_idx, fragment) in self.fragments.iter().enumerate() {
            for (action_idx, action) in fragment.actions.iter().enumerate() {
                let signing_message = TurnExecutor::compute_partial_signing_message(
                    action,
                    position,
                    &forest_root_hash,
                );

                // Verify the signature.
                let sig_bytes = fragment.signatures[action_idx];
                let signature = Signature::from_bytes(&sig_bytes);

                let verifying_key = VerifyingKey::from_bytes(&fragment.signer).map_err(|_| {
                    ComposeError::InvalidSignature {
                        fragment_index: frag_idx,
                        action_index: action_idx,
                        reason: "invalid public key".to_string(),
                    }
                })?;

                verifying_key.verify(&signing_message, &signature).map_err(|_| {
                    ComposeError::InvalidSignature {
                        fragment_index: frag_idx,
                        action_index: action_idx,
                        reason: "Ed25519 signature verification failed".to_string(),
                    }
                })?;

                position += 1;
            }
        }

        // Phase 4: Check balance_change conservation (excess must sum to zero).
        let total_excess: i64 = all_actions
            .iter()
            .filter_map(|a| a.balance_change)
            .sum();

        if total_excess != 0 {
            return Err(ComposeError::ExcessImbalance { total_excess });
        }

        // Phase 5: Assemble the Turn.
        let turn = Turn {
            agent: self.fee_payer,
            nonce: self.nonce,
            call_forest: forest,
            fee: self.fee,
            memo: self.memo,
            valid_until: self.valid_until,
        };

        Ok(turn)
    }
}
