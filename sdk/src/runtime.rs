//! Agent runtime: high-level orchestration of wallet, ledger, and execution.
//!
//! The [`AgentRuntime`] ties together:
//! - An agent wallet (identity + tokens)
//! - A local ledger (cell state)
//! - A turn executor (atomic execution)
//!
//! It provides the highest-level API for agent operations: execute effects,
//! spawn sub-agents with attenuated capabilities, and manage the local cell.

use std::sync::{Arc, Mutex, RwLock};

use pyana_cell::{Cell, CellId, Ledger};
use pyana_token::{Attenuation, AuthToken};
use pyana_turn::{
    Action, Authorization, BudgetGate, BudgetSlice, CallForest, ComputronCosts, DelegationMode,
    Effect, Turn, TurnExecutor, TurnReceipt, TurnResult, action::symbol,
};
use pyana_types::PublicKey;

use crate::cipherclerk::{AgentCipherclerk, HeldToken};
use crate::error::SdkError;

/// The agent runtime: orchestrates wallet, ledger, and execution.
///
/// This is the top-level coordination layer for an agent. It manages:
/// - The agent's cell in the local ledger
/// - Turn construction and execution
/// - Sub-agent spawning with attenuated capabilities
///
/// The wallet is held behind an `Arc<RwLock<...>>` so that the runtime can
/// append receipts after successful turn execution (mutating the receipt chain
/// and IVC state), while still allowing shared read access for signing and
/// token operations.
///
/// # Example
///
/// ```no_run
/// use pyana_sdk::{AgentCipherclerk, AgentRuntime, Effect};
/// use pyana_types::CellId;
/// use std::sync::{Arc, RwLock};
///
/// let wallet = Arc::new(RwLock::new(AgentCipherclerk::new()));
/// let runtime = AgentRuntime::new(wallet, "my-domain");
///
/// // Execute effects against the local ledger
/// let receipt = runtime.execute(vec![
///     Effect::IncrementNonce { cell: runtime.cell_id() },
/// ]).unwrap();
/// ```
pub struct AgentRuntime {
    /// The agent's wallet (read-write lock for receipt chain mutation).
    cipherclerk: Arc<RwLock<AgentCipherclerk>>,
    /// The agent's cell ID in the local domain.
    cell_id: CellId,
    /// The domain this runtime operates in.
    domain: String,
    /// The local ledger (shared, thread-safe).
    ledger: Arc<Mutex<Ledger>>,
    /// The turn executor.
    executor: TurnExecutor,
    /// Current nonce for the agent's cell (tracks submitted turns).
    nonce: Mutex<u64>,
}

impl AgentRuntime {
    /// Create a new agent runtime with simplified ownership.
    ///
    /// This is a convenience constructor that wraps the wallet in `Arc<RwLock<...>>`
    /// internally, so callers don't need to manage the synchronization primitives
    /// themselves.
    ///
    /// # Arguments
    ///
    /// * `wallet` - The agent's wallet (moved into the runtime).
    /// * `domain` - The domain this agent operates in (e.g., "compute", "storage").
    ///
    /// # Example
    ///
    /// ```no_run
    /// use pyana_sdk::{AgentCipherclerk, AgentRuntime};
    ///
    /// let wallet = AgentCipherclerk::new();
    /// let runtime = AgentRuntime::new_simple(wallet, "my-domain");
    /// ```
    pub fn new_simple(cipherclerk: AgentCipherclerk, domain: &str) -> Self {
        Self::new(Arc::new(RwLock::new(cipherclerk)), domain)
    }

    /// Create a new agent runtime.
    ///
    /// Initializes the local ledger with the agent's cell (funded with a default
    /// balance for local execution). The domain determines the agent's cell ID.
    ///
    /// # Arguments
    ///
    /// * `wallet` - Shared read-write reference to the agent's wallet.
    /// * `domain` - The domain this agent operates in (e.g., "compute", "storage").
    pub fn new(cipherclerk: Arc<RwLock<AgentCipherclerk>>, domain: &str) -> Self {
        let cell_id;
        let public_key;
        {
            // Recover from poisoned lock rather than cascading panics.
            // A poisoned RwLock means a writer panicked while holding the lock;
            // we accept the potentially-inconsistent state as preferable to
            // bringing down the entire runtime.
            let w = cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            cell_id = w.cell_id(domain);
            public_key = w.public_key();
        }
        let mut ledger = Ledger::new();

        // Create the agent's cell with a generous initial balance for local use.
        let agent_cell = Cell::with_balance(
            public_key.0,
            *blake3::hash(domain.as_bytes()).as_bytes(),
            1_000_000, // 1M computrons initial balance
        );
        ledger
            .insert_cell(agent_cell)
            .expect("fresh ledger, no conflict");

        let executor = TurnExecutor::new(ComputronCosts::default_costs());

        AgentRuntime {
            cipherclerk,
            cell_id,
            domain: domain.to_string(),
            ledger: Arc::new(Mutex::new(ledger)),
            executor,
            nonce: Mutex::new(0),
        }
    }

    /// Create a runtime with a pre-existing ledger.
    ///
    /// Use this when the ledger is shared with other components or has been
    /// restored from persistent storage.
    pub fn with_ledger(
        cipherclerk: Arc<RwLock<AgentCipherclerk>>,
        domain: &str,
        ledger: Arc<Mutex<Ledger>>,
    ) -> Self {
        let cell_id = cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .cell_id(domain);
        let executor = TurnExecutor::new(ComputronCosts::default_costs());

        AgentRuntime {
            cipherclerk,
            cell_id,
            domain: domain.to_string(),
            ledger,
            executor,
            nonce: Mutex::new(0),
        }
    }

    /// Get the agent's cell ID.
    pub fn cell_id(&self) -> CellId {
        self.cell_id
    }

    /// Get the domain this runtime operates in.
    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// Get a reference to the ledger.
    pub fn ledger(&self) -> &Arc<Mutex<Ledger>> {
        &self.ledger
    }

    /// Get the agent's current nonce.
    pub fn nonce(&self) -> u64 {
        *self.nonce.lock().unwrap()
    }

    /// Get a reference to the cipherclerk (behind RwLock).
    ///
    /// Callers should use `.read().unwrap_or_else(|e| e.into_inner())` for read
    /// access or `.write().unwrap_or_else(|e| e.into_inner())` for mutation
    /// (e.g., enabling IVC, minting tokens).
    pub fn cipherclerk(&self) -> &Arc<RwLock<AgentCipherclerk>> {
        &self.cipherclerk
    }

    /// Legacy alias for [`Self::cipherclerk`].
    #[doc(hidden)]
    pub fn wallet(&self) -> &Arc<RwLock<AgentCipherclerk>> {
        self.cipherclerk()
    }

    /// Attach a budget gate (Stingray bounded counter) to this runtime's executor.
    ///
    /// When set, each turn execution will check the silo's local budget slice
    /// before proceeding. If the slice cannot cover the turn fee, the turn is
    /// rejected with `TurnError::BudgetExhausted`.
    ///
    /// Call this when the agent's current silo has provided a budget slice via
    /// the StingrayCounter (pyana_coord::StingrayCounter).
    pub fn set_budget_gate(&mut self, silo_id: u32, slice: BudgetSlice) {
        self.executor
            .set_budget_gate(BudgetGate::new(silo_id, slice));
    }

    /// Execute a list of effects against the local ledger.
    ///
    /// Wraps the effects into a turn, signs it, and executes it atomically.
    /// On success, the ledger is updated and a receipt is returned.
    ///
    /// # Arguments
    ///
    /// * `effects` - The effects to execute (state changes, transfers, etc.)
    ///
    /// # Returns
    ///
    /// A [`TurnReceipt`] proving the turn was committed, or an error if
    /// execution was rejected.
    pub fn execute(&self, effects: Vec<Effect>) -> Result<TurnReceipt, SdkError> {
        // LOCK ORDER: ledger → nonce → wallet (canonical order to prevent deadlock).
        // We acquire ledger first, then nonce, then wallet for signing/receipts.

        // Build the action without authorization first to compute the signing message.
        let action_unsigned = Action {
            target: self.cell_id,
            method: symbol("execute"),
            args: Vec::new(),
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        // Compute the signing message and sign with the wallet's key (read lock).
        // We sign before acquiring the ledger lock since signing is pure.
        let message = TurnExecutor::compute_signing_message(
            &action_unsigned,
            &self.executor.local_federation_id,
        );
        let sig = self
            .cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .sign_bytes(&message);

        // Rebuild the action with the signature attached.
        let action_signed = Action {
            authorization: Authorization::from_sig_bytes(sig.0),
            ..action_unsigned
        };

        // Construct the turn manually with the signed action.
        let mut forest = CallForest::new();
        forest.add_root(action_signed);

        // Acquire ledger lock first (canonical order: ledger → nonce → wallet).
        let mut ledger = self.ledger.lock().unwrap();

        let nonce = {
            let mut n = self.nonce.lock().unwrap();
            let current = *n;
            *n += 1;
            current
        };

        // Bind this turn to the receipt chain: read the latest receipt hash from the wallet.
        let previous_receipt_hash = self
            .cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .receipt_head()
            .map(|r| r.receipt_hash());

        let turn = Turn {
            agent: self.cell_id,
            nonce,
            call_forest: forest,
            fee: 10_000,
            memo: None,
            valid_until: None,
            previous_receipt_hash,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
        };

        // Execute against the local ledger.
        let result = self.executor.execute(&turn, &mut ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // Release ledger lock before taking wallet write lock.
                drop(ledger);
                // Append the receipt to the wallet's chain (write lock).
                self.cipherclerk
                    .write()
                    .unwrap_or_else(|e| e.into_inner())
                    .append_receipt(receipt.clone());
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Execute a pre-built turn against the local ledger.
    ///
    /// Use this when you need full control over the turn structure (multiple
    /// root actions, child actions, custom authorization, etc.)
    pub fn execute_turn(&self, turn: &Turn) -> Result<TurnReceipt, SdkError> {
        // LOCK ORDER: ledger → nonce → wallet (canonical order to prevent deadlock).
        let mut ledger = self.ledger.lock().unwrap();
        let result = self.executor.execute(turn, &mut ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // Advance our nonce to match (nonce lock after ledger = canonical order).
                {
                    let mut n = self.nonce.lock().unwrap();
                    if turn.nonce >= *n {
                        *n = turn.nonce + 1;
                    }
                }
                // Release ledger lock before taking wallet write lock.
                drop(ledger);
                // Append the receipt to the wallet's chain (write lock).
                self.cipherclerk
                    .write()
                    .unwrap_or_else(|e| e.into_inner())
                    .append_receipt(receipt.clone());
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Spawn a sub-agent with attenuated capabilities.
    ///
    /// Creates a new agent (fresh wallet + cell) with capabilities derived from
    /// this agent's tokens, narrowed by the given restrictions. The sub-agent
    /// operates on the same ledger but with reduced authority.
    ///
    /// # Arguments
    ///
    /// * `restrictions` - Restrictions to apply to the delegated token.
    /// * `token` - The parent token to delegate from.
    ///
    /// # Returns
    ///
    /// A [`SubAgent`] with its own wallet and attenuated token.
    pub fn spawn_sub_agent(
        &self,
        restrictions: &Attenuation,
        token: &HeldToken,
    ) -> Result<SubAgent, SdkError> {
        // Create a new wallet for the sub-agent.
        let mut sub_cclerk = AgentCipherclerk::new();
        let sub_pk = sub_cclerk.public_key();

        // Attenuate the token for the sub-agent.
        let decoded = token.decode()?;
        let attenuated_boxed = decoded.attenuate(restrictions)?;
        let encoded = attenuated_boxed.to_encoded()?;

        let token_id = format!("sub:{}:{}", token.id(), sub_pk.short_hex());
        let delegated_label = format!("delegated:{}", token.service());

        // SECURITY: The sub-agent receives an attenuated token with zeroed root_key.
        // It cannot mint new root tokens or bypass the attenuation chain.
        // However, it carries the derived issuer_key for ZK proof generation.
        // The issuer_key is always the derived proof key (never the raw root key).
        let issuer_key = *token.issuer_key();
        let delegated_token = HeldToken::new_attenuated(
            delegated_label.clone(),
            token.service().to_string(),
            encoded.clone(),
            token_id.clone(),
            issuer_key,
        );

        // Pass through the issuer_key as the proof_key for the sub-agent's delegation.
        // Since issuer_key is already a one-way derivation (never the raw root key),
        // it's safe to transmit to the sub-agent.
        let proof_key = if issuer_key != [0u8; 32] {
            Some(issuer_key)
        } else {
            None
        };

        // Local (in-process) sub-agent spawning. We use the typed `LocalDelegation`
        // path so this code can never accidentally normalize an externally-sourced
        // unsigned token. The local envelope is still signature-bound (under a
        // distinct domain tag), and the receiver verifies it against the parent
        // wallet's public key.
        let parent_pubkey = {
            let parent = self.cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            parent.public_key()
        };
        let local = {
            let parent = self.cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            parent.make_local_delegation(
                encoded,
                token.service().to_string(),
                delegated_label,
                token_id,
                sub_pk,
                restrictions.clone(),
                proof_key,
                None, // no pre-generated membership proof in this path
                None, // no caveat_chain_hash; sub-agent operates on local state
            )
        };
        sub_cclerk.receive_local_delegation(local, &parent_pubkey)?;

        // Create the sub-agent's cell in the ledger.
        let sub_cell_id = sub_cclerk.cell_id(&self.domain);
        {
            let mut ledger = self.ledger.lock().unwrap();
            let sub_cell = Cell::with_balance(
                sub_pk.0,
                *blake3::hash(self.domain.as_bytes()).as_bytes(),
                100_000, // 100k computrons for sub-agent
            );
            // Ignore error if cell already exists (idempotent).
            let _ = ledger.insert_cell(sub_cell);
        }

        Ok(SubAgent {
            cipherclerk: Arc::new(sub_cclerk),
            cell_id: sub_cell_id,
            token: delegated_token,
            parent: self
                .cipherclerk
                .read()
                .unwrap_or_else(|e| e.into_inner())
                .public_key(),
            domain: self.domain.clone(),
            federation_id: self.executor.local_federation_id,
            ledger: self.ledger.clone(),
            nonce: Mutex::new(0),
            last_receipt_hash: Mutex::new(None),
        })
    }
}

impl std::fmt::Debug for AgentRuntime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AgentRuntime")
            .field("cell_id", &self.cell_id)
            .field("domain", &self.domain)
            .field("nonce", &self.nonce())
            .finish()
    }
}

/// A sub-agent spawned by a parent runtime with attenuated capabilities.
///
/// Sub-agents have their own identity and wallet but operate on the same ledger
/// as their parent. Their token is strictly less powerful than the parent's.
///
/// Each sub-agent maintains its own receipt chain binding: every turn it executes
/// includes `previous_receipt_hash` linking to its last committed receipt. This
/// prevents reordering and replay of sub-agent turns.
// AUDIT[P2]: `SubAgent` exposes `pub wallet: Arc<AgentCipherclerk>` and `pub token:
// HeldToken`. The `HeldToken` itself is now sealed-value (P0 fix), so its
// authority-affecting fields cannot be tampered with. But `pub federation_id:
// [u8; 32]` IS writable by an external caller holding a `&mut SubAgent`. This
// federation_id is used as the signing-message domain separator for turn
// signatures (see `SubAgent::execute`). An attacker who can mutate
// `federation_id` post-construct could cause the sub-agent to sign turns
// against the wrong federation, leading to cross-federation replay vectors.
// Severity P2: requires existing `&mut SubAgent` access, which is itself a
// privileged hold. Recommended fix: make all SubAgent fields private with
// read-only accessors (`pub fn federation_id(&self) -> [u8; 32]`).
#[derive(Debug)]
pub struct SubAgent {
    // P1-1, P1-2 (AUDIT-wallet.md / AUDIT-sdk-rest.md): every field is now
    // `pub(crate)` so external callers can no longer rewrite `federation_id`
    // (the signing-message domain separator) or swap `wallet` / `token`
    // post-construct. Access from outside the crate is via the read-only
    // accessor methods below.
    /// The sub-agent's cipherclerk.
    pub(crate) cipherclerk: Arc<AgentCipherclerk>,
    /// The sub-agent's cell ID.
    pub(crate) cell_id: CellId,
    /// The attenuated token this sub-agent holds.
    pub(crate) token: HeldToken,
    /// The parent agent's public key.
    pub(crate) parent: PublicKey,
    /// The domain this sub-agent operates in.
    pub(crate) domain: String,
    /// The federation/group ID inherited from the parent runtime.
    ///
    /// In the unified lace model, this is equivalent to a `GroupId` (the
    /// reference group this agent belongs to). Used for signing messages
    /// with the correct group context. The field name is preserved for
    /// backward compatibility; semantically it is a group identifier.
    pub(crate) federation_id: [u8; 32],
    /// Shared ledger with the parent.
    ledger: Arc<Mutex<Ledger>>,
    /// Nonce counter for turn submission (incremented on each execute call).
    nonce: Mutex<u64>,
    /// The hash of the last committed receipt for this sub-agent.
    /// Used to bind each new turn to its predecessor, preventing reordering
    /// and replay of sub-agent turns.
    last_receipt_hash: Mutex<Option<[u8; 32]>>,
}

impl SubAgent {
    /// Get the sub-agent's public key.
    pub fn public_key(&self) -> PublicKey {
        self.cipherclerk.public_key()
    }

    /// Read-only access to the sub-agent's cipherclerk.
    pub fn cipherclerk(&self) -> &Arc<AgentCipherclerk> {
        &self.cipherclerk
    }

    /// Legacy alias for [`Self::cipherclerk`].
    #[doc(hidden)]
    pub fn wallet(&self) -> &Arc<AgentCipherclerk> {
        self.cipherclerk()
    }

    /// Get the sub-agent's cell ID.
    pub fn cell_id(&self) -> CellId {
        self.cell_id
    }

    /// Get a reference to the sub-agent's held token.
    pub fn token(&self) -> &HeldToken {
        &self.token
    }

    /// Get the parent agent's public key.
    pub fn parent(&self) -> PublicKey {
        self.parent
    }

    /// Get the domain this sub-agent operates in.
    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// Get the federation (group) id this sub-agent inherited.
    pub fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    /// Check whether the sub-agent's token authorizes a request.
    ///
    /// P1-4: previously delegated to [`AgentCipherclerk::verify_token`], which
    /// requires the token's `root_key` to be set (HMAC verification). Sub-agent
    /// tokens are delegated and carry a zeroed `root_key`, so `verify_token`
    /// always returned `false` — the method had no useful semantics.
    ///
    /// This implementation runs the Datalog evaluator on the structural
    /// caveat set (the same evaluator used by trusted-mode authorization),
    /// returning `true` if the request is `Allow`ed by the token's caveats and
    /// `false` for `Deny` / `Inconclusive` / parse failure. The durable
    /// binding is re-verified first so a post-receive tampering returns
    /// `false`.
    pub fn can_authorize(&self, request: &pyana_token::AuthRequest) -> bool {
        if self.token.reverify_delegation_binding().is_err() {
            return false;
        }
        match self
            .cipherclerk
            .authorize(&self.token, request, crate::VerificationMode::Trusted)
        {
            Ok(crate::AuthorizationPresentation::Trusted { trace, .. }) => {
                matches!(trace.conclusion, pyana_trace::Conclusion::Allow { .. })
            }
            // Any other presentation kind shouldn't occur from Trusted mode;
            // be conservative.
            Ok(_) => false,
            Err(_) => false,
        }
    }

    /// Execute effects on the shared ledger using this sub-agent's cell.
    ///
    /// Each turn is bound to this sub-agent's receipt chain via `previous_receipt_hash`,
    /// which prevents reordering and replay of sub-agent turns. The binding is updated
    /// after each successful commit.
    pub fn execute(&self, effects: Vec<Effect>) -> Result<TurnReceipt, SdkError> {
        let executor = TurnExecutor::new(ComputronCosts::default_costs());

        let nonce = {
            let mut n = self.nonce.lock().unwrap();
            let current = *n;
            *n += 1;
            current
        };

        // Read the current receipt chain head for binding.
        let previous_receipt_hash = *self.last_receipt_hash.lock().unwrap();

        // Build unsigned action to compute signing message.
        let action_unsigned = Action {
            target: self.cell_id,
            method: symbol("execute"),
            args: Vec::new(),
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        // Sign with the sub-agent's wallet using the parent's federation_id
        // for correct domain separation.
        let message = TurnExecutor::compute_signing_message(&action_unsigned, &self.federation_id);
        let sig = self.cipherclerk.sign_bytes(&message);

        let action_signed = Action {
            authorization: Authorization::from_sig_bytes(sig.0),
            ..action_unsigned
        };

        let mut forest = CallForest::new();
        forest.add_root(action_signed);

        let turn = Turn {
            agent: self.cell_id,
            nonce,
            call_forest: forest,
            fee: 5_000,
            memo: None,
            valid_until: None,
            previous_receipt_hash,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
        };

        let mut ledger = self.ledger.lock().unwrap();
        let result = executor.execute(&turn, &mut ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // SECURITY: Update the receipt chain binding so the next turn
                // is linked to this one, preventing reordering and replay.
                *self.last_receipt_hash.lock().unwrap() = Some(receipt.receipt_hash());
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Get the sub-agent's current nonce.
    pub fn nonce(&self) -> u64 {
        *self.nonce.lock().unwrap()
    }
}
