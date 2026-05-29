use serde::{Deserialize, Serialize};

use crate::capability::CapabilitySet;
use crate::delegation::DelegatedRef;
use crate::id::CellId;
use crate::lifecycle::{CellLifecycle, LifecycleTransitionError};
use crate::permissions::Permissions;
use crate::program::CellProgram;
use crate::state::CellState;

/// Whether a cell's full state is stored by the federation or only a commitment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CellMode {
    /// Federation stores full cell state (current behavior).
    Hosted,
    /// Federation stores only a 32-byte state commitment.
    /// The agent must provide cell state in each turn.
    Sovereign,
}

impl Default for CellMode {
    fn default() -> Self {
        CellMode::Sovereign
    }
}

/// A verification key associated with a cell's proof circuit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationKey {
    /// Hash of the verification key for cheap comparison.
    pub hash: [u8; 32],
    /// Serialized verification key data (opaque blob).
    pub data: Vec<u8>,
}

impl VerificationKey {
    /// Create a new verification key from raw data, computing its BLAKE3 hash.
    ///
    /// **Deprecated.** This constructor uses a plain `blake3(data)` hash, which
    /// is *not* a `canonical_vk_v2` hash (domain key `"dregg-vk-v2"`). Any VK
    /// built here is internally consistent but not interoperable with a validator
    /// that re-derives the expected VK hash via `canonical_vk_v2` from the four
    /// canonical components. Use [`VerificationKey::from_components`] for all
    /// production VK construction where the circuit/AIR/verifier/proving-system
    /// identity components are available. Opaque-fixture uses (tests, demos) may
    /// continue to call `new` — the deprecation warning is expected and acceptable
    /// for those sites. Do **not** suppress the warning with `#[allow(deprecated)]`
    /// unless the call site is genuinely opaque-fixture only.
    ///
    /// See `docs-old/VK-NEW-CALLER-AUDIT.md` §2 Option A for the full rationale.
    #[deprecated(
        note = "use from_components for canonical vk_v2 hashing; see VK-NEW-CALLER-AUDIT"
    )]
    pub fn new(data: Vec<u8>) -> Self {
        let hash = *blake3::hash(&data).as_bytes();
        VerificationKey { hash, data }
    }

    /// Create a verification key from the four canonical VK v2 components,
    /// computing the hash via [`crate::vk_v2::canonical_vk_v2`].
    ///
    /// This is the correct constructor for any production code path that has the
    /// cell-program / AIR / verifier / proving-system identity components in hand:
    ///
    /// - `components.program_bytes` — canonical postcard(CellProgram), DSL AST,
    ///   or opaque app-provided bytes encoding the executable spec.
    /// - `components.air_fingerprint` — 32-byte hash of the AIR descriptor.
    /// - `components.verifier_fingerprint` — which verifier implementation runs
    ///   the circuit (source-hash / wasm-hash / compiled-VK-hash variant).
    /// - `components.proving_system_id` — Plonky3BabyBearFri, KimchiPasta,
    ///   Sp1V6, or Custom.
    ///
    /// The resulting `hash` field is a `blake3_keyed("dregg-vk-v2", …)` digest —
    /// the same value that a validator re-derives independently. The `data` field
    /// stores `program_bytes` so the program spec is recoverable for
    /// cross-checking (AIR/verifier/proving-system identity is conveyed
    /// out-of-band via `VkComponents`; see `vk_v2.rs` for the full boundary
    /// contract).
    ///
    /// # Example
    ///
    /// ```
    /// use dregg_cell::VerificationKey;
    /// use dregg_cell::vk_v2::{VkComponents, VerifierFingerprint, ProvingSystemId};
    ///
    /// let program_bytes = b"my-cell-program-postcard-bytes";
    /// let vk = VerificationKey::from_components(&VkComponents {
    ///     program_bytes,
    ///     air_fingerprint: [0x11; 32],
    ///     verifier_fingerprint: VerifierFingerprint::SourceHash([0x22; 32]),
    ///     proving_system_id: ProvingSystemId::Plonky3BabyBearFri {
    ///         p3_rev: "82cfad73",
    ///     },
    /// });
    /// // vk.hash is canonical_vk_v2(components), not blake3(program_bytes).
    /// ```
    pub fn from_components(components: &crate::vk_v2::VkComponents<'_>) -> Self {
        let hash = crate::vk_v2::canonical_vk_v2(components);
        // Store the program bytes so the executable spec is recoverable for
        // cross-checking. The AIR/verifier/proving-system fields are conveyed
        // out-of-band via VkComponents and are NOT embedded in `data`.
        let data = components.program_bytes.to_vec();
        VerificationKey { hash, data }
    }

    /// Create a verification key with a pre-computed hash (e.g., from
    /// deserialization).
    ///
    /// **Audit P0 #69:** this constructor does *not* validate the
    /// `hash == blake3(data)` invariant. It exists for the
    /// deserialization fast-path where the producer has already paid
    /// the hash and we want to avoid recomputing it. Untrusted-input
    /// call sites (the `SetVerificationKey` apply, wire decoders,
    /// federation gossip ingest) MUST use [`Self::from_parts_checked`]
    /// instead — otherwise an attacker can pin an arbitrary `hash` and
    /// defeat the layered-VK design (the cell commitment binds the
    /// `hash`, but downstream verifiers expect that `hash` to be the
    /// commitment of `data`).
    pub fn from_parts(hash: [u8; 32], data: Vec<u8>) -> Self {
        VerificationKey { hash, data }
    }

    /// Create a verification key with a pre-computed hash, validating
    /// the integrity invariant `hash == blake3(data)`.
    ///
    /// Returns `Err(VerificationKeyIntegrityError)` if the supplied hash
    /// does not match the BLAKE3 commitment of the supplied data. This
    /// is the correct constructor for any code path that consumes a
    /// `VerificationKey` from outside trust boundaries (a turn body, a
    /// federation broadcast, a deserialized snapshot) — see audit P0 #69.
    pub fn from_parts_checked(
        hash: [u8; 32],
        data: Vec<u8>,
    ) -> Result<Self, VerificationKeyIntegrityError> {
        let expected = *blake3::hash(&data).as_bytes();
        if expected != hash {
            return Err(VerificationKeyIntegrityError {
                expected,
                got: hash,
            });
        }
        Ok(VerificationKey { hash, data })
    }
}

/// Returned when a [`VerificationKey`]'s declared `hash` does not match
/// `blake3(data)`. See [`VerificationKey::from_parts_checked`] and audit
/// P0 #69.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerificationKeyIntegrityError {
    /// Hash the validator computed from the supplied `data`.
    pub expected: [u8; 32],
    /// Hash the caller declared.
    pub got: [u8; 32],
}

impl std::fmt::Display for VerificationKeyIntegrityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "VerificationKey hash mismatch: declared {:02x}{:02x}{:02x}{:02x}.. \
             but blake3(data) is {:02x}{:02x}{:02x}{:02x}..",
            self.got[0],
            self.got[1],
            self.got[2],
            self.got[3],
            self.expected[0],
            self.expected[1],
            self.expected[2],
            self.expected[3],
        )
    }
}

impl std::error::Error for VerificationKeyIntegrityError {}

/// A Cell is an isolated agent execution context.
/// This is the agent-model analog of a Mina zkApp account.
///
/// Audit P0-1 sealing: the identity-bearing fields `id`, `public_key`, and
/// `token_id` are `pub(crate)` rather than `pub` — external code must use the
/// accessors [`Cell::id`], [`Cell::public_key`], [`Cell::token_id`] for reads
/// and go through `Ledger::update_with` for mutations. This preserves the
/// content-address invariant `id == derive_raw(public_key, token_id)` (P2-3).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cell {
    /// Content-addressed identity: BLAKE3(public_key || token_id).
    ///
    /// `pub(crate)`: external code must read via `Cell::id()` and cannot mutate
    /// without going through `Ledger::update_with` (which re-checks integrity).
    pub(crate) id: CellId,
    /// The cell's public key (Ed25519). See `id` for sealing rationale.
    pub(crate) public_key: [u8; 32],
    /// Mutable state: 8 fields + nonce + balance.
    pub state: CellState,
    /// Authorization requirements for each action type.
    pub permissions: Permissions,
    /// Optional verification key for ZK proof validation.
    pub verification_key: Option<VerificationKey>,
    /// Optional parent/supervisor cell. Planned for delegation chain walking
    /// (child inherits parent's capabilities). Not yet enforced by the executor.
    pub delegate: Option<CellId>,
    /// Rich delegation snapshot: point-in-time copy of the parent's c-list.
    /// Used for snapshot+refresh E-style delegation. The child acts using this
    /// snapshot; acceptors check freshness via `max_staleness`.
    pub delegation: Option<DelegatedRef>,
    /// Which token domain this cell belongs to. See `id` for sealing rationale.
    pub(crate) token_id: [u8; 32],
    /// The c-list: what other cells this cell can reference.
    pub capabilities: CapabilitySet,
    /// The cell's program: defines valid state transitions.
    /// If `CellProgram::None`, any authorized state change is valid (backward compat).
    pub program: CellProgram,
    /// Whether this cell is hosted (federation stores full state) or sovereign
    /// (federation stores only a 32-byte commitment). Defaults to Hosted for
    /// backward compatibility with existing serialized cells.
    #[serde(default)]
    pub mode: CellMode,
    /// Canonical lifecycle state of the cell. Per
    /// `PROTOCOL-CATEGORICAL-ANALYSIS.md §1`, this enumerates the
    /// structural states a cell can inhabit (Live, Sealed, Migrated,
    /// Destroyed, Archived). Defaults to [`CellLifecycle::Live`].
    ///
    /// `#[serde(default)]`: existing serialized cells deserialize to
    /// `Live`, preserving backward compatibility while making the
    /// lifecycle explicit going forward.
    #[serde(default)]
    pub lifecycle: CellLifecycle,
}

/// Configuration for creating a new cell.
///
/// Allows choosing mode, initial balance, permissions, and program at creation time.
#[derive(Clone, Debug)]
pub struct CellConfig {
    /// Whether the cell is hosted or sovereign.
    pub mode: CellMode,
    /// Initial balance (computrons).
    pub balance: u64,
    /// Permissions (defaults to Permissions::default() if None).
    pub permissions: Option<Permissions>,
    /// Cell program (defaults to CellProgram::None if None).
    pub program: Option<CellProgram>,
    /// Verification key (optional).
    pub verification_key: Option<VerificationKey>,
}

impl Default for CellConfig {
    fn default() -> Self {
        CellConfig {
            mode: CellMode::Sovereign,
            balance: 0,
            permissions: None,
            program: None,
            verification_key: None,
        }
    }
}

impl CellConfig {
    /// Create a config for a hosted cell.
    pub fn hosted() -> Self {
        CellConfig {
            mode: CellMode::Hosted,
            ..Default::default()
        }
    }

    /// Create a config for a sovereign cell.
    pub fn sovereign() -> Self {
        CellConfig {
            mode: CellMode::Sovereign,
            ..Default::default()
        }
    }

    /// Set the initial balance.
    pub fn with_balance(mut self, balance: u64) -> Self {
        self.balance = balance;
        self
    }

    /// Set the permissions.
    pub fn with_permissions(mut self, permissions: Permissions) -> Self {
        self.permissions = Some(permissions);
        self
    }

    /// Set the cell program.
    pub fn with_program(mut self, program: CellProgram) -> Self {
        self.program = Some(program);
        self
    }

    /// Set the verification key.
    pub fn with_verification_key(mut self, vk: VerificationKey) -> Self {
        self.verification_key = Some(vk);
        self
    }
}

impl Cell {
    /// Create a new cell with default permissions and the given public key and token domain.
    ///
    /// Defaults to `CellMode::Sovereign` (Phase 4). Use `Cell::new_hosted()` for
    /// explicit hosted creation.
    pub fn new(public_key: [u8; 32], token_id: [u8; 32]) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Sovereign,
            lifecycle: CellLifecycle::Live,
        }
    }

    /// Create a new hosted cell explicitly.
    ///
    /// This is the pre-Phase-4 behavior where the federation stores full cell state.
    pub fn new_hosted(public_key: [u8; 32], token_id: [u8; 32]) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
        }
    }

    /// Create a new cell with a specific initial balance.
    ///
    /// Remains hosted for backward compatibility with existing tests.
    pub fn with_balance(public_key: [u8; 32], token_id: [u8; 32], balance: u64) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            state: CellState::new(balance),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
        }
    }

    /// Create a placeholder cell for a remote peer using their pre-derived
    /// cell id directly, without re-deriving from a (pk, token_id) pair.
    ///
    /// # When to use
    ///
    /// Inter-node operations (cross-federation grants, peer introductions,
    /// gossip of a remote cell's c-list entry) sometimes need a landing site
    /// for a remote cell whose canonical state lives on another node. The
    /// remote node has the real `(pk, token_id)`; the local node only sees
    /// the resulting content-addressed `CellId`. Calling `with_balance` would
    /// re-derive from a placeholder pk and produce a *different* id; calling
    /// this constructor preserves the id chosen by the remote node.
    ///
    /// # Soundness
    ///
    /// The returned cell breaks the invariant `id == derive_raw(public_key,
    /// token_id)` (the stub's public_key is zeros). This is acceptable because:
    ///
    /// 1. The stub cannot sign — its pk is zero — so no local authorization
    ///    path will accept a Signature(r, s) against it.
    /// 2. The stub's id is consistent with what the remote node would emit,
    ///    so cross-node gossip remains coherent.
    /// 3. The integrity invariant `verify_id_integrity()` will fail on this
    ///    stub, which is intentional: callers that need a canonical cell
    ///    must use `Ledger::update_with` and verify integrity there.
    ///
    /// In short: this is the escape hatch for "we know the id but not the
    /// pre-image." Use sparingly.
    pub fn remote_stub_with_id(id: CellId) -> Self {
        Self::remote_stub_with_id_and_balance(id, 0)
    }

    /// Like [`Cell::remote_stub_with_id`] but with an initial balance set on
    /// the placeholder. Use this when the local node knows the remote cell
    /// should have at least a certain balance for a turn to commit (for
    /// example, when a bearer-cap holder needs to issue a Transfer from a
    /// remote cell whose canonical balance lives on another node — without
    /// the local balance, the Transfer would hit InsufficientBalance even
    /// though it would succeed on the canonical node).
    pub fn remote_stub_with_id_and_balance(id: CellId, balance: u64) -> Self {
        Self::remote_stub_with_id_pk_balance(id, [0u8; 32], balance)
    }

    /// Like [`Cell::remote_stub_with_id_and_balance`] but also lets the
    /// caller specify the remote cell's public key. Required when the
    /// executor walks the local ledger to find the *delegator* of a bearer
    /// cap by pk: a zero-pk stub wouldn't match, so the bearer-cap proof
    /// would be rejected as if the delegator weren't present.
    pub fn remote_stub_with_id_pk_balance(id: CellId, public_key: [u8; 32], balance: u64) -> Self {
        Cell {
            id,
            public_key,
            state: CellState::new(balance),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id: [0u8; 32],
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
        }
    }

    /// Create a new cell from a configuration.
    pub fn from_config(public_key: [u8; 32], token_id: [u8; 32], config: CellConfig) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            state: CellState::new(config.balance),
            permissions: config.permissions.unwrap_or_default(),
            verification_key: config.verification_key,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: config.program.unwrap_or(CellProgram::None),
            mode: config.mode,
            lifecycle: CellLifecycle::Live,
        }
    }

    /// Read accessor for the content-addressed cell ID. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly — the following must
    /// not compile:
    /// ```compile_fail
    /// # use dregg_cell::Cell;
    /// let mut cell = Cell::new([0u8; 32], [0u8; 32]);
    /// cell.id = dregg_cell::CellId::derive_raw(&[1u8; 32], &[2u8; 32]);
    /// ```
    #[inline]
    pub fn id(&self) -> CellId {
        self.id
    }

    /// Read accessor for the cell's Ed25519 public key. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::Cell;
    /// let mut cell = Cell::new([0u8; 32], [0u8; 32]);
    /// cell.public_key = [1u8; 32];
    /// ```
    #[inline]
    pub fn public_key(&self) -> &[u8; 32] {
        &self.public_key
    }

    /// Read accessor for the cell's token-domain ID. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::Cell;
    /// let mut cell = Cell::new([0u8; 32], [0u8; 32]);
    /// cell.token_id = [1u8; 32];
    /// ```
    #[inline]
    pub fn token_id(&self) -> &[u8; 32] {
        &self.token_id
    }

    /// Compute the canonical commitment to this cell's current state.
    ///
    /// This is a thin wrapper around
    /// [`crate::commitment::compute_canonical_state_commitment`], the single
    /// source of truth for "what bytes commit to this cell." `Ledger::hash_cell`
    /// is also routed through the same function so the sovereign-witness check
    /// (which uses `state_commitment`) and the federation Merkle leaf (which
    /// uses `hash_cell`) agree byte-for-byte. See `cell/src/commitment.rs` for
    /// the full hash shape and the audit context (P0-2).
    pub fn state_commitment(&self) -> [u8; 32] {
        crate::commitment::compute_canonical_state_commitment(self)
    }

    /// Verify that `self.id` matches `derive_raw(public_key, token_id)`.
    ///
    /// Audit P2-3: the `id` field is content-addressed at construction but
    /// nothing in the type system maintains the invariant after construction.
    /// Authoritative call sites (sovereign-witness ingest, peer-exchange ingest,
    /// post-deserialization) should call this and reject cells that fail.
    pub fn verify_id_integrity(&self) -> bool {
        self.id == CellId::derive_raw(&self.public_key, &self.token_id)
    }

    /// Seal this cell: transition `lifecycle` to [`CellLifecycle::Sealed`].
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4`. Sealing is *reversible*
    /// quiescence — the cell rejects new effects but state and history
    /// are preserved. Use [`Cell::unseal`] to return to
    /// [`CellLifecycle::Live`]. Sealing is the prelude to destruction;
    /// it clarifies what destruction is not.
    ///
    /// # Errors
    ///
    /// Returns `Err(LifecycleTransitionError::Terminal)` if the cell is
    /// already in a terminal state (Destroyed or Migrated). Returns
    /// `Err(LifecycleTransitionError::AlreadySealed)` if the cell is
    /// already sealed (sealing is idempotent in effect but explicit so
    /// callers don't silently overwrite the original `reason_hash` /
    /// `sealed_at`).
    pub fn seal(
        &mut self,
        reason_hash: [u8; 32],
        sealed_at: u64,
    ) -> Result<(), LifecycleTransitionError> {
        match &self.lifecycle {
            CellLifecycle::Live | CellLifecycle::Archived { .. } => {
                self.lifecycle = CellLifecycle::Sealed {
                    reason_hash,
                    sealed_at,
                };
                Ok(())
            }
            CellLifecycle::Sealed { .. } => Err(LifecycleTransitionError::AlreadySealed),
            CellLifecycle::Destroyed { .. } | CellLifecycle::Migrated { .. } => {
                Err(LifecycleTransitionError::Terminal)
            }
        }
    }

    /// Reverse a seal: transition `lifecycle` from [`CellLifecycle::Sealed`]
    /// back to [`CellLifecycle::Live`].
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4`. The reversibility of
    /// seal/unseal is precisely what distinguishes sealing from
    /// destruction.
    ///
    /// # Errors
    ///
    /// Returns `Err(LifecycleTransitionError::NotSealed)` if the cell is
    /// not currently in [`CellLifecycle::Sealed`].
    pub fn unseal(&mut self) -> Result<(), LifecycleTransitionError> {
        if matches!(self.lifecycle, CellLifecycle::Sealed { .. }) {
            self.lifecycle = CellLifecycle::Live;
            Ok(())
        } else {
            Err(LifecycleTransitionError::NotSealed)
        }
    }

    /// Permanently retire this cell: transition `lifecycle` to
    /// [`CellLifecycle::Destroyed`] and bind a [`DeathCertificate`] hash
    /// into the final state.
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4`. Destruction is
    /// *permanent* — once a cell is Destroyed it cannot transition to
    /// any other lifecycle state. Descendants / observers can present
    /// the cell's final state-commitment alongside the
    /// `DeathCertificate` to prove "this cell is permanently retired"
    /// rather than inferring from absence.
    ///
    /// # Errors
    ///
    /// Returns `Err(LifecycleTransitionError::Terminal)` if the cell is
    /// already in a terminal state.
    pub fn destroy(
        &mut self,
        certificate: &crate::lifecycle::DeathCertificate,
    ) -> Result<(), LifecycleTransitionError> {
        if self.lifecycle.is_terminal() {
            return Err(LifecycleTransitionError::Terminal);
        }
        if certificate.cell_id != self.id {
            return Err(LifecycleTransitionError::CertificateMismatch);
        }
        self.lifecycle = CellLifecycle::Destroyed {
            death_certificate_hash: certificate.certificate_hash(),
            destroyed_at: certificate.destroyed_at_height,
        };
        Ok(())
    }

    /// Mark this cell's receipt-chain prefix as archived. Lifecycle
    /// transitions to [`CellLifecycle::Archived`] (or stays Archived
    /// with the newer checkpoint).
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §4.2`. Archival does NOT
    /// disable the cell — `lifecycle.accepts_effects()` remains true.
    /// What changes: verifiers reconstructing the chain prior to
    /// `archived_through` consult the off-chain blob referenced by
    /// `checkpoint_hash`; chain links above the cutover walk the live
    /// tail.
    ///
    /// # Errors
    ///
    /// Returns `Err(LifecycleTransitionError::Terminal)` if the cell is
    /// in a terminal state, `Err(LifecycleTransitionError::SealedCannotArchive)`
    /// if it is sealed (unseal first if you really mean to archive a
    /// sealed cell's history), and
    /// `Err(LifecycleTransitionError::CertificateMismatch)` if the
    /// attestation does not bind to this cell.
    pub fn archive(
        &mut self,
        attestation: &crate::lifecycle::ArchivalAttestation,
    ) -> Result<(), LifecycleTransitionError> {
        if self.lifecycle.is_terminal() {
            return Err(LifecycleTransitionError::Terminal);
        }
        if self.lifecycle.is_sealed() {
            return Err(LifecycleTransitionError::SealedCannotArchive);
        }
        if attestation.cell_id != self.id {
            return Err(LifecycleTransitionError::CertificateMismatch);
        }
        attestation
            .validate()
            .map_err(LifecycleTransitionError::InvalidAttestation)?;
        // Monotonicity: an earlier archival cutover cannot replace a
        // later one (archived_through is monotone).
        if let CellLifecycle::Archived {
            archived_through, ..
        } = &self.lifecycle
        {
            if attestation.archive_end_height <= *archived_through {
                return Err(LifecycleTransitionError::ArchiveNotMonotone);
            }
        }
        self.lifecycle = CellLifecycle::Archived {
            checkpoint_hash: attestation.checkpoint_hash(),
            archived_through: attestation.archive_end_height,
        };
        Ok(())
    }

    /// Whether this cell currently accepts new effects.
    ///
    /// Shortcut for `self.lifecycle.accepts_effects()`. The executor
    /// consults this before applying any state-mutating effect; effects
    /// targeting a non-accepting cell are rejected with a structural
    /// "cell is sealed / destroyed / migrated" error.
    pub fn accepts_effects(&self) -> bool {
        self.lifecycle.accepts_effects()
    }

    /// Create a child cell delegated to this cell.
    pub fn spawn_child(&self, child_public_key: [u8; 32], child_token_id: [u8; 32]) -> Cell {
        let id = CellId::derive_raw(&child_public_key, &child_token_id);
        Cell {
            id,
            public_key: child_public_key,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: Some(self.id),
            delegation: None,
            token_id: child_token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
        }
    }

    /// Create a child cell with snapshot+refresh delegation from this cell.
    ///
    /// The child inherits a point-in-time snapshot of the parent's c-list.
    /// The snapshot epoch and refresh timestamp are set by the caller.
    ///
    /// Audit P1-5: This constructor produces a `DelegatedRef` with a
    /// placeholder all-zero signature, which `verify_parent_signature` will
    /// reject. To prevent external code from minting forged delegations by
    /// calling this and then skipping verification, the function is now
    /// `pub(crate)` — only the cell crate (and downstream callers that
    /// re-export it deliberately) can invoke it. External orchestration
    /// should go through a signature-required constructor or
    /// `DelegatedRef::new` with a real signature.
    #[cfg(test)]
    pub(crate) fn spawn_child_with_delegation(
        &self,
        child_public_key: [u8; 32],
        child_token_id: [u8; 32],
        delegation_epoch: u64,
        refreshed_at: u64,
        max_staleness: u64,
    ) -> Cell {
        let id = CellId::derive_raw(&child_public_key, &child_token_id);
        let snapshot: Vec<crate::capability::CapabilityRef> =
            self.capabilities.iter().cloned().collect();
        Cell {
            id,
            public_key: child_public_key,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: Some(self.id),
            delegation: Some({
                let clist_bytes = postcard::to_allocvec(&snapshot).unwrap_or_default();
                let clist_commitment = DelegatedRef::compute_clist_commitment(&clist_bytes);
                DelegatedRef::new(
                    self.id,
                    id,
                    snapshot,
                    delegation_epoch,
                    refreshed_at,
                    max_staleness,
                    clist_commitment,
                    [0u8; 64], // Placeholder signature — spawn_child is a privileged internal op.
                )
            }),
            token_id: child_token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
        }
    }
}

#[cfg(test)]
mod lifecycle_transition_tests {
    //! Adversarial tests for the Cell lifecycle transition primitives.
    //!
    //! Per PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4: seal/unseal must be
    //! exactly inverse; destroy is terminal; the certificate must bind
    //! to the cell being retired; archive must be monotone.
    use super::*;
    use crate::lifecycle::{ArchivalAttestation, DeathCertificate, DeathReason};

    fn fresh(b: u8) -> Cell {
        let mut k = [0u8; 32];
        k[0] = b;
        Cell::new(k, [0u8; 32])
    }

    #[test]
    fn seal_then_unseal_round_trips() {
        let mut c = fresh(1);
        assert!(c.accepts_effects());
        c.seal([9u8; 32], 100).unwrap();
        assert!(!c.accepts_effects());
        assert!(c.lifecycle.is_sealed());
        c.unseal().unwrap();
        assert!(c.accepts_effects());
        assert!(matches!(c.lifecycle, CellLifecycle::Live));
    }

    #[test]
    fn second_seal_rejected() {
        let mut c = fresh(1);
        c.seal([9u8; 32], 100).unwrap();
        let err = c.seal([7u8; 32], 200).unwrap_err();
        assert_eq!(err, LifecycleTransitionError::AlreadySealed);
        // Original seal data must be preserved.
        if let CellLifecycle::Sealed {
            reason_hash,
            sealed_at,
        } = c.lifecycle
        {
            assert_eq!(reason_hash, [9u8; 32]);
            assert_eq!(sealed_at, 100);
        } else {
            panic!("expected Sealed");
        }
    }

    #[test]
    fn unseal_on_live_cell_rejected() {
        let mut c = fresh(1);
        let err = c.unseal().unwrap_err();
        assert_eq!(err, LifecycleTransitionError::NotSealed);
    }

    #[test]
    fn destroy_is_terminal() {
        let mut c = fresh(1);
        let dc = DeathCertificate {
            cell_id: c.id(),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: c.state_commitment(),
            destroyed_at_height: 42,
            reason: DeathReason::Voluntary,
        };
        c.destroy(&dc).unwrap();
        assert!(c.lifecycle.is_destroyed());
        assert!(c.lifecycle.is_terminal());
        assert!(!c.accepts_effects());

        // No further transition is allowed.
        assert_eq!(
            c.seal([0u8; 32], 1).unwrap_err(),
            LifecycleTransitionError::Terminal
        );
        assert_eq!(c.unseal().unwrap_err(), LifecycleTransitionError::NotSealed);
        assert_eq!(
            c.destroy(&dc).unwrap_err(),
            LifecycleTransitionError::Terminal
        );
    }

    #[test]
    fn destroy_rejects_certificate_for_other_cell() {
        let mut c = fresh(1);
        let other = fresh(2);
        let dc = DeathCertificate {
            cell_id: other.id(),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: other.state_commitment(),
            destroyed_at_height: 42,
            reason: DeathReason::Voluntary,
        };
        let err = c.destroy(&dc).unwrap_err();
        assert_eq!(err, LifecycleTransitionError::CertificateMismatch);
        assert!(matches!(c.lifecycle, CellLifecycle::Live));
    }

    #[test]
    fn destroy_from_sealed_is_allowed() {
        // Sealing-as-prelude-to-destruction is the documented usage.
        let mut c = fresh(1);
        c.seal([9u8; 32], 100).unwrap();
        let dc = DeathCertificate {
            cell_id: c.id(),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: c.state_commitment(),
            destroyed_at_height: 200,
            reason: DeathReason::Forced,
        };
        c.destroy(&dc).unwrap();
        assert!(c.lifecycle.is_destroyed());
    }

    #[test]
    fn archive_succeeds_and_cell_still_accepts() {
        let mut c = fresh(1);
        let a = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        c.archive(&a).unwrap();
        assert!(c.accepts_effects(), "archived cells still accept effects");
        if let CellLifecycle::Archived {
            archived_through, ..
        } = c.lifecycle
        {
            assert_eq!(archived_through, 100);
        } else {
            panic!("expected Archived");
        }
    }

    #[test]
    fn archive_must_be_monotone() {
        let mut c = fresh(1);
        let a1 = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        let a2_older = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 50, // older
            archive_blob_hash: [4u8; 32],
            archive_terminal_commitment: [5u8; 32],
            archive_terminal_receipt_hash: [6u8; 32],
        };
        let a3_newer = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 101,
            archive_end_height: 200,
            archive_blob_hash: [7u8; 32],
            archive_terminal_commitment: [8u8; 32],
            archive_terminal_receipt_hash: [9u8; 32],
        };

        c.archive(&a1).unwrap();
        assert_eq!(
            c.archive(&a2_older).unwrap_err(),
            LifecycleTransitionError::ArchiveNotMonotone
        );
        c.archive(&a3_newer).unwrap(); // monotone advance OK
        if let CellLifecycle::Archived {
            archived_through, ..
        } = c.lifecycle
        {
            assert_eq!(archived_through, 200);
        }
    }

    #[test]
    fn archive_rejects_other_cell_attestation() {
        let mut c = fresh(1);
        let other = fresh(2);
        let a = ArchivalAttestation {
            cell_id: other.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        assert_eq!(
            c.archive(&a).unwrap_err(),
            LifecycleTransitionError::CertificateMismatch
        );
    }

    #[test]
    fn sealed_cells_cannot_be_archived() {
        let mut c = fresh(1);
        c.seal([1u8; 32], 50).unwrap();
        let a = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        assert_eq!(
            c.archive(&a).unwrap_err(),
            LifecycleTransitionError::SealedCannotArchive
        );
    }

    #[test]
    fn terminal_cells_reject_archive() {
        let mut c = fresh(1);
        let dc = DeathCertificate {
            cell_id: c.id(),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: c.state_commitment(),
            destroyed_at_height: 42,
            reason: DeathReason::Voluntary,
        };
        c.destroy(&dc).unwrap();
        let a = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        assert_eq!(
            c.archive(&a).unwrap_err(),
            LifecycleTransitionError::Terminal
        );
    }

    /// State-commitment difference: sealing produces a *different*
    /// commitment than the original Live cell. This is what binds the
    /// lifecycle transition into the chain.
    #[test]
    fn lifecycle_transition_changes_state_commitment() {
        let mut c = fresh(1);
        let live_commit = c.state_commitment();
        c.seal([5u8; 32], 100).unwrap();
        let sealed_commit = c.state_commitment();
        assert_ne!(live_commit, sealed_commit);
        c.unseal().unwrap();
        let unsealed_commit = c.state_commitment();
        // Round-trip: unsealed cell agrees with original Live commit.
        assert_eq!(live_commit, unsealed_commit);
    }
}
