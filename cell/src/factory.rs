//! EROS-style Object Factories for pyana.
//!
//! A Factory is a CellProgram that constrains what new cells it can create.
//! The factory's [`FactoryDescriptor`] IS the constructor transparency — anyone
//! can inspect exactly what capabilities the factory grants to its creations,
//! what programs it installs, and what initial state it sets.
//!
//! Factories work in all modes (sovereign, hosted, federated): same VK, same
//! circuit, different verification venue.

use serde::{Deserialize, Serialize};

use crate::cell::CellMode;
use crate::id::CellId;
use crate::permissions::AuthRequired;
use crate::program::CellProgram;
use crate::vk_v2::{ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2};

/// Compute the **program-bytes layer** of a cell-program VK hash.
///
/// Per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1 (v1) this *was* the full VK
/// identifier; per §v2 it is the program-bytes component of a four-
/// component vk_hash. The legacy v1 encoding survives as this
/// function's return value and is fed into [`canonical_program_vk_v2`]
/// alongside the AIR fingerprint, verifier fingerprint, and proving-
/// system identifier to produce the layered hash.
///
/// **Use [`canonical_program_vk_v2`] for new VK identifiers.** Callers
/// that produce a `child_program_vk` slot, a custom-predicate vk_hash,
/// or a custom-effect vk_hash should always go through the v2 path,
/// passing this function's output as the `program_bytes` component.
/// This function is retained for content-addressed identity within
/// cell-internal data structures where AIR / verifier / proving-system
/// identity is not relevant (e.g., the program-text hash inside a
/// factory descriptor's content hash).
///
/// # Determinism
///
/// `postcard::to_allocvec` is deterministic given a stable `Serialize`
/// impl. `CellProgram` and its constituent types (`StateConstraint`,
/// `TransitionCase`, `WitnessedPredicate`, …) derive `Serialize` via
/// `serde`, so the encoding is determined by the variant layout in
/// source.
///
/// # Boundary contract
///
/// - Cleartext-inside:  VK author + validators (they hold the program).
/// - Commitment-inside: receipt observers (see vk_hash but not program).
/// - Acceptance-inside: post-recursion validators (acceptance bit only).
/// - Out-of-band:       everyone else.
/// Enforced by: BLAKE3 keyed-hash binding canonical bytes to vk_hash.
/// Failure mode if violated: re-execution disagrees with executor's
/// claimed acceptance bit; soundness failure.
pub fn canonical_program_vk(program: &CellProgram) -> [u8; 32] {
    let serialized = postcard::to_allocvec(program)
        .expect("CellProgram postcard serialization is infallible for v1 encoding");
    let mut hasher = blake3::Hasher::new_derive_key("pyana-cellprogram-vk-v1");
    hasher.update(&(serialized.len() as u64).to_le_bytes());
    hasher.update(&serialized);
    *hasher.finalize().as_bytes()
}

/// Canonically serialize a `CellProgram` to its postcard bytes — the
/// `program_bytes` component of [`canonical_program_vk_v2`].
///
/// Exposed so v2 callers in higher layers (`pyana-app-framework` and
/// app crates that depend on both `pyana-cell` and `pyana-circuit`)
/// can feed the program directly into a [`VkComponents`] without
/// re-encoding.
pub fn canonical_program_bytes(program: &CellProgram) -> Vec<u8> {
    postcard::to_allocvec(program)
        .expect("CellProgram postcard serialization is infallible for v1 encoding")
}

/// Compute the canonical **layered** (v2) VK hash for a `CellProgram`.
///
/// Per `VK-AS-RE-EXECUTION-RECIPE.md` §v2, a vk_hash commits to four
/// components, not one:
///
/// 1. The program's canonical postcard bytes (the spec).
/// 2. The AIR-shape fingerprint (which AIR runs the spec). Computed by
///    `pyana_circuit::air_descriptor::fingerprint(&AIR_DESCRIPTOR)`.
/// 3. The verifier-impl fingerprint (which code/wasm/compiled-VK
///    runs the verifier).
/// 4. The proving-system identifier (Plonky3-FRI, Kimchi, SP1, …).
///
/// This function performs the postcard serialization of `program` and
/// hands the result, plus the caller-supplied components, to
/// [`canonical_vk_v2`].
///
/// # Migration from v1
///
/// v1 callers (`canonical_program_vk(program)`) committed only to
/// component 1. Their vk_hashes are *not* equivalent to v2 vk_hashes
/// computed over the same program — domain separation under the v2
/// domain string `"pyana-vk-v2"` ensures the two never collide.
/// Greenfield migration: starbridge-apps and other VK authors bump all
/// their vk_hash constants to v2 in one move; receivers (factory
/// registries, custom-predicate / custom-effect registries) accept the
/// new hashes uniformly.
pub fn canonical_program_vk_v2(
    program: &CellProgram,
    air_fingerprint: [u8; 32],
    verifier_fingerprint: VerifierFingerprint,
    proving_system_id: ProvingSystemId,
) -> [u8; 32] {
    let program_bytes = canonical_program_bytes(program);
    canonical_vk_v2(&VkComponents {
        program_bytes: &program_bytes,
        air_fingerprint,
        verifier_fingerprint,
        proving_system_id,
    })
}

/// Strategy for determining the child cell's program VK at creation time.
///
/// This enables "computable child VK" — factories that derive the child's program
/// based on creation parameters rather than having a single fixed VK.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChildVkStrategy {
    /// Fixed VK — all children get the same program (legacy behavior).
    Fixed(Option<[u8; 32]>),
    /// Derived VK — child VK is computed from factory VK + creation parameters.
    /// The derivation is: `child_vk = Poseidon2(factory_vk || param_hash)`
    /// where `param_hash = Poseidon2(all_creation_params)`.
    Derived {
        /// The base VK from which children are derived (typically the factory's own VK).
        base_vk: [u8; 32],
    },
    /// Registry lookup — child VK is chosen from a set of approved VKs.
    /// Verification uses Merkle membership: `child_vk in approved_vks`.
    FromSet {
        /// The set of approved child VKs (order-independent Merkle tree).
        approved_vks: Vec<[u8; 32]>,
    },
}

impl ChildVkStrategy {
    /// Compute the BLAKE3 hash of this strategy for descriptor hashing.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-child-vk-strategy-v1");
        match self {
            ChildVkStrategy::Fixed(None) => {
                hasher.update(&[0u8]);
            }
            ChildVkStrategy::Fixed(Some(vk)) => {
                hasher.update(&[1u8]);
                hasher.update(vk);
            }
            ChildVkStrategy::Derived { base_vk } => {
                hasher.update(&[2u8]);
                hasher.update(base_vk);
            }
            ChildVkStrategy::FromSet { approved_vks } => {
                hasher.update(&[3u8]);
                hasher.update(&(approved_vks.len() as u64).to_le_bytes());
                for vk in approved_vks {
                    hasher.update(vk);
                }
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Derive a child VK from creation parameters (for `Derived` strategy).
    ///
    /// Uses BLAKE3 keyed derivation: `child_vk = BLAKE3("pyana-derived-child-vk" || factory_vk || param_hash)`.
    /// This is the off-circuit computation; the circuit version uses Poseidon2 over BabyBear elements.
    pub fn derive_child_vk(factory_vk: &[u8; 32], param_hash: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-derived-child-vk-v1");
        hasher.update(factory_vk);
        hasher.update(param_hash);
        *hasher.finalize().as_bytes()
    }

    /// Compute the param_hash for a set of creation parameters.
    ///
    /// `param_hash = BLAKE3("pyana-factory-params" || mode || fields || caps_hash)`.
    pub fn compute_param_hash(params: &FactoryCreationParams) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-factory-params-v1");
        let mode_byte = match params.mode {
            CellMode::Hosted => 0u8,
            CellMode::Sovereign => 1u8,
        };
        hasher.update(&[mode_byte]);
        hasher.update(&(params.initial_fields.len() as u64).to_le_bytes());
        for (idx, val) in &params.initial_fields {
            hasher.update(&idx.to_le_bytes());
            hasher.update(&val.to_le_bytes());
        }
        hasher.update(&(params.initial_caps.len() as u64).to_le_bytes());
        for cap in &params.initial_caps {
            let target_byte = match &cap.target {
                CapTarget::SelfCell => 0u8,
                CapTarget::Specific(_) => 1u8,
                CapTarget::Any => 2u8,
            };
            hasher.update(&[target_byte]);
            let perm_byte = match &cap.max_permissions {
                AuthRequired::None => 0u8,
                AuthRequired::Signature => 1u8,
                AuthRequired::Proof => 2u8,
                AuthRequired::Either => 3u8,
                AuthRequired::Impossible => 4u8,
                AuthRequired::Custom { .. } => 5u8,
            };
            hasher.update(&[perm_byte]);
            // For Custom auth, mix in the vk_hash so two factories that
            // differ only in app-defined auth mode produce distinct
            // param_hashes (and thus distinct derived child VKs).
            if let AuthRequired::Custom { vk_hash } = &cap.max_permissions {
                hasher.update(vk_hash);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Check if a given child VK is in the approved set.
    pub fn is_in_approved_set(approved_vks: &[[u8; 32]], child_vk: &[u8; 32]) -> bool {
        approved_vks.contains(child_vk)
    }

    /// Validate a claimed child VK against this strategy and the given creation params.
    ///
    /// Returns `Ok(())` if the claimed VK is valid for this strategy, otherwise an error.
    pub fn validate_child_vk(
        &self,
        claimed_vk: &Option<[u8; 32]>,
        params: &FactoryCreationParams,
    ) -> Result<(), FactoryError> {
        match self {
            ChildVkStrategy::Fixed(expected) => {
                if claimed_vk != expected {
                    return Err(FactoryError::ProgramMismatch {
                        expected: *expected,
                        got: *claimed_vk,
                    });
                }
                Ok(())
            }
            ChildVkStrategy::Derived { base_vk } => {
                let param_hash = Self::compute_param_hash(params);
                let expected_vk = Self::derive_child_vk(base_vk, &param_hash);
                match claimed_vk {
                    Some(vk) if *vk == expected_vk => Ok(()),
                    _ => Err(FactoryError::DerivedVkMismatch {
                        expected: expected_vk,
                        got: *claimed_vk,
                    }),
                }
            }
            ChildVkStrategy::FromSet { approved_vks } => match claimed_vk {
                Some(vk) if Self::is_in_approved_set(approved_vks, vk) => Ok(()),
                _ => Err(FactoryError::VkNotInApprovedSet {
                    claimed: *claimed_vk,
                    set_size: approved_vks.len(),
                }),
            },
        }
    }
}

/// A factory descriptor: metadata about what a factory creates.
///
/// This is inspectable by anyone without running the circuit. It describes the
/// complete "constructor contract" — what the factory is allowed to produce.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactoryDescriptor {
    /// The factory's own program VK hash (identifies the factory).
    pub factory_vk: [u8; 32],
    /// What program (if any) is installed on created cells (legacy fixed VK).
    pub child_program_vk: Option<[u8; 32]>,
    /// Strategy for determining child VK at creation time.
    ///
    /// If `None`, uses legacy behavior (`child_program_vk` must match exactly).
    /// If `Some`, this strategy overrides `child_program_vk` for validation.
    pub child_vk_strategy: Option<ChildVkStrategy>,
    /// Maximum capabilities the factory can grant to created cells.
    pub allowed_cap_templates: Vec<CapTemplate>,
    /// Initial field constraints (which fields are set at creation, value ranges).
    /// **Creation-time only** — these run once when `validate_creation` is
    /// called against the constructor parameters. They do not govern subsequent
    /// state transitions; for that, use [`state_constraints`] (slot caveats).
    pub field_constraints: Vec<FieldConstraint>,
    /// **Perpetual** slot caveats baked into the child cell's `CellProgram`.
    ///
    /// Per `SLOT-CAVEATS-DESIGN.md` (Lane G), these are the
    /// `StateConstraint` set installed on every cell produced by this
    /// factory. They are evaluated by the executor on *every*
    /// state-modifying turn (not just creation), giving lifetime
    /// invariants like `WriteOnce`, `Monotonic`, `FieldDelta`, etc.
    ///
    /// Defaults to empty so existing factory descriptors keep validating
    /// unchanged. Apps that want lifetime invariants bake them in here at
    /// the same time the factory's `field_constraints` are declared.
    #[serde(default)]
    pub state_constraints: Vec<crate::program::StateConstraint>,
    /// Whether created cells are sovereign or hosted.
    pub default_mode: CellMode,
    /// Resource budget: max cells this factory can create per epoch.
    pub creation_budget: Option<u64>,
}

impl FactoryDescriptor {
    /// Compute the BLAKE3 hash of this descriptor (content-addressed identity).
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-factory-descriptor-v1");
        hasher.update(&self.factory_vk);
        match &self.child_program_vk {
            Some(vk) => {
                hasher.update(&[1u8]);
                hasher.update(vk);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        // Include child_vk_strategy in hash.
        match &self.child_vk_strategy {
            Some(strategy) => {
                hasher.update(&[1u8]);
                hasher.update(&strategy.hash());
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        hasher.update(&(self.allowed_cap_templates.len() as u64).to_le_bytes());
        for tmpl in &self.allowed_cap_templates {
            hasher.update(&tmpl.hash());
        }
        hasher.update(&(self.field_constraints.len() as u64).to_le_bytes());
        for fc in &self.field_constraints {
            hasher.update(&fc.hash());
        }
        // Slot caveats (StateConstraint set) are part of the constructor
        // transparency: a child cell carries them on `program`, and the
        // descriptor's hash binds the factory to the same set so anyone
        // can audit what invariants new cells inherit.
        let constraints_encoded =
            postcard::to_allocvec(&self.state_constraints).unwrap_or_default();
        hasher.update(&(constraints_encoded.len() as u64).to_le_bytes());
        hasher.update(&constraints_encoded);
        let mode_byte = match self.default_mode {
            CellMode::Hosted => 0u8,
            CellMode::Sovereign => 1u8,
        };
        hasher.update(&[mode_byte]);
        match self.creation_budget {
            Some(b) => {
                hasher.update(&[1u8]);
                hasher.update(&b.to_le_bytes());
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Validate that a proposed creation is within this descriptor's constraints.
    ///
    /// Returns `Ok(())` if all constraints pass, or an error describing the violation.
    pub fn validate_creation(&self, params: &FactoryCreationParams) -> Result<(), FactoryError> {
        // Check child program VK using strategy if present, else legacy check.
        match &self.child_vk_strategy {
            Some(strategy) => {
                strategy.validate_child_vk(&params.program_vk, params)?;
            }
            None => {
                // Legacy behavior: exact match on child_program_vk.
                if self.child_program_vk != params.program_vk {
                    return Err(FactoryError::ProgramMismatch {
                        expected: self.child_program_vk,
                        got: params.program_vk,
                    });
                }
            }
        }

        // Check mode.
        if self.default_mode != params.mode {
            return Err(FactoryError::ModeMismatch {
                expected: self.default_mode.clone(),
                got: params.mode.clone(),
            });
        }

        // Check capabilities are within templates.
        for (i, cap) in params.initial_caps.iter().enumerate() {
            if !self.cap_within_templates(cap) {
                return Err(FactoryError::CapabilityOutsideTemplate { cap_index: i });
            }
        }

        // Check field constraints.
        for constraint in &self.field_constraints {
            constraint.check(&params.initial_fields)?;
        }

        Ok(())
    }

    /// Validate that this descriptor's `child_program_vk` is the
    /// canonical VK hash of the supplied `CellProgram` per the
    /// re-execution-recipe contract (`VK-AS-RE-EXECUTION-RECIPE.md` §2.1).
    ///
    /// Used by validators with both a `FactoryDescriptor` and the
    /// canonical `CellProgram` text in hand to confirm the descriptor's
    /// claimed VK actually binds to the program. Returns
    /// `Ok(())` when `self.child_program_vk == Some(canonical_program_vk(program))`,
    /// or a `FactoryError::ProgramMismatch` describing the disagreement.
    ///
    /// Sovereign factories that install `child_program_vk = None`
    /// (no program; transitions governed by the cell-owner's witness)
    /// reject this check — there is no program to canonicalize.
    /// Callers that want to permit `None` should not invoke this method.
    pub fn validate_child_vk_canonical(&self, program: &CellProgram) -> Result<(), FactoryError> {
        let expected = canonical_program_vk(program);
        match self.child_program_vk {
            Some(got) if got == expected => Ok(()),
            other => Err(FactoryError::ProgramMismatch {
                expected: Some(expected),
                got: other,
            }),
        }
    }

    /// Check that a capability grant is within at least one template.
    fn cap_within_templates(&self, cap: &CapGrant) -> bool {
        self.allowed_cap_templates.iter().any(|tmpl| {
            // Target must match.
            let target_ok = match &tmpl.target {
                CapTarget::Any => true,
                CapTarget::SelfCell => cap.target == CapTarget::SelfCell,
                CapTarget::Specific(id) => cap.target == CapTarget::Specific(*id),
            };
            // Permissions must be no broader than template.
            let perm_ok = cap
                .max_permissions
                .is_narrower_or_equal(&tmpl.max_permissions);
            // Attenuatable only if template allows it.
            let atten_ok = !cap.attenuatable || tmpl.attenuatable;
            target_ok && perm_ok && atten_ok
        })
    }
}

/// A capability template: what the factory is allowed to grant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapTemplate {
    /// Who the capability targets.
    pub target: CapTarget,
    /// Maximum permissions the factory can grant.
    pub max_permissions: AuthRequired,
    /// Whether created cells can further delegate this capability.
    pub attenuatable: bool,
}

impl CapTemplate {
    /// Compute a hash of this template for descriptor hashing.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-cap-template:");
        match &self.target {
            CapTarget::SelfCell => {
                hasher.update(&[0u8]);
            }
            CapTarget::Specific(id) => {
                hasher.update(&[1u8]);
                hasher.update(id.as_bytes());
            }
            CapTarget::Any => {
                hasher.update(&[2u8]);
            }
        }
        let perm_byte = match &self.max_permissions {
            AuthRequired::None => 0u8,
            AuthRequired::Signature => 1u8,
            AuthRequired::Proof => 2u8,
            AuthRequired::Either => 3u8,
            AuthRequired::Impossible => 4u8,
            AuthRequired::Custom { .. } => 5u8,
        };
        hasher.update(&[perm_byte]);
        // For Custom permissions, include the vk_hash in the template hash
        // so that templates differing only in their app-defined auth mode
        // do not collide.
        if let AuthRequired::Custom { vk_hash } = &self.max_permissions {
            hasher.update(vk_hash);
        }
        hasher.update(&[self.attenuatable as u8]);
        *hasher.finalize().as_bytes()
    }
}

/// The target of a capability template.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CapTarget {
    /// The created cell itself (self-reference).
    SelfCell,
    /// A specific cell ID.
    Specific(CellId),
    /// Any cell (unrestricted targeting).
    Any,
}

/// A constraint on initial field values.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldConstraint {
    /// A specific field must equal a specific value.
    Equality { field_index: u32, value: u64 },
    /// A specific field must be within a range.
    Range {
        field_index: u32,
        min: u64,
        max: u64,
    },
    /// A specific field must be set (non-zero).
    NonZero { field_index: u32 },
}

impl FieldConstraint {
    /// Compute a hash of this constraint for descriptor hashing.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-field-constraint:");
        match self {
            FieldConstraint::Equality { field_index, value } => {
                hasher.update(&[0u8]);
                hasher.update(&field_index.to_le_bytes());
                hasher.update(&value.to_le_bytes());
            }
            FieldConstraint::Range {
                field_index,
                min,
                max,
            } => {
                hasher.update(&[1u8]);
                hasher.update(&field_index.to_le_bytes());
                hasher.update(&min.to_le_bytes());
                hasher.update(&max.to_le_bytes());
            }
            FieldConstraint::NonZero { field_index } => {
                hasher.update(&[2u8]);
                hasher.update(&field_index.to_le_bytes());
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Check that the initial fields satisfy this constraint.
    fn check(&self, fields: &[(u32, u64)]) -> Result<(), FactoryError> {
        match self {
            FieldConstraint::Equality { field_index, value } => {
                let actual = fields
                    .iter()
                    .find(|(idx, _)| idx == field_index)
                    .map(|(_, v)| *v)
                    .unwrap_or(0);
                if actual != *value {
                    return Err(FactoryError::FieldConstraintViolation {
                        field_index: *field_index,
                        reason: format!("expected {}, got {}", value, actual),
                    });
                }
            }
            FieldConstraint::Range {
                field_index,
                min,
                max,
            } => {
                let actual = fields
                    .iter()
                    .find(|(idx, _)| idx == field_index)
                    .map(|(_, v)| *v)
                    .unwrap_or(0);
                if actual < *min || actual > *max {
                    return Err(FactoryError::FieldConstraintViolation {
                        field_index: *field_index,
                        reason: format!("value {} outside range [{}, {}]", actual, min, max),
                    });
                }
            }
            FieldConstraint::NonZero { field_index } => {
                let actual = fields
                    .iter()
                    .find(|(idx, _)| idx == field_index)
                    .map(|(_, v)| *v)
                    .unwrap_or(0);
                if actual == 0 {
                    return Err(FactoryError::FieldConstraintViolation {
                        field_index: *field_index,
                        reason: "field must be non-zero".to_string(),
                    });
                }
            }
        }
        Ok(())
    }
}

/// A capability grant request in a factory creation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapGrant {
    /// The target of the capability.
    pub target: CapTarget,
    /// What permissions this grants.
    pub max_permissions: AuthRequired,
    /// Whether the created cell can further delegate.
    pub attenuatable: bool,
}

/// Parameters for creating a cell from a factory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactoryCreationParams {
    /// The mode of the created cell.
    pub mode: CellMode,
    /// Program VK hash to install on the created cell.
    pub program_vk: Option<[u8; 32]>,
    /// Initial field values (field_index, value).
    pub initial_fields: Vec<(u32, u64)>,
    /// Capabilities to grant to the created cell.
    pub initial_caps: Vec<CapGrant>,
    /// Owner public key for the created cell.
    pub owner_pubkey: [u8; 32],
}

/// Provenance record stored on cells, tracking their creation history.
///
/// This allows anyone to verify who created a cell and under what constraints.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Provenance {
    /// Which factory created this cell (factory VK hash), if any.
    pub created_by_factory: Option<[u8; 32]>,
    /// Hash of the creation STARK proof (for verification).
    pub creation_proof_hash: Option<[u8; 32]>,
    /// The block height at which the cell was created.
    pub creation_height: u64,
    /// If the child VK was derived, the param_hash used in derivation.
    /// Third parties can verify: `cell.program_vk == derive(factory_vk, param_hash)`.
    pub derivation_param_hash: Option<[u8; 32]>,
}

impl Provenance {
    /// Create a provenance for a cell not created by a factory.
    pub fn genesis(height: u64) -> Self {
        Provenance {
            created_by_factory: None,
            creation_proof_hash: None,
            creation_height: height,
            derivation_param_hash: None,
        }
    }

    /// Create a provenance for a factory-created cell.
    pub fn from_factory(factory_vk: [u8; 32], proof_hash: Option<[u8; 32]>, height: u64) -> Self {
        Provenance {
            created_by_factory: Some(factory_vk),
            creation_proof_hash: proof_hash,
            creation_height: height,
            derivation_param_hash: None,
        }
    }

    /// Create a provenance for a factory-created cell with a derived VK.
    pub fn from_factory_derived(
        factory_vk: [u8; 32],
        proof_hash: Option<[u8; 32]>,
        height: u64,
        param_hash: [u8; 32],
    ) -> Self {
        Provenance {
            created_by_factory: Some(factory_vk),
            creation_proof_hash: proof_hash,
            creation_height: height,
            derivation_param_hash: Some(param_hash),
        }
    }

    /// Verify that a cell's program VK was correctly derived from the factory.
    ///
    /// Returns `true` if the derivation is valid, `false` if it cannot be verified
    /// (e.g., no derivation_param_hash, or no factory VK).
    pub fn verify_derivation(&self, cell_program_vk: &[u8; 32]) -> bool {
        match (self.created_by_factory, self.derivation_param_hash) {
            (Some(factory_vk), Some(param_hash)) => {
                let expected = ChildVkStrategy::derive_child_vk(&factory_vk, &param_hash);
                expected == *cell_program_vk
            }
            _ => false,
        }
    }
}

/// Errors from factory validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FactoryError {
    /// The child program VK doesn't match the factory's descriptor.
    ProgramMismatch {
        expected: Option<[u8; 32]>,
        got: Option<[u8; 32]>,
    },
    /// The cell mode doesn't match the factory's descriptor.
    ModeMismatch { expected: CellMode, got: CellMode },
    /// A capability grant is outside the factory's allowed templates.
    CapabilityOutsideTemplate { cap_index: usize },
    /// A field constraint is violated.
    FieldConstraintViolation { field_index: u32, reason: String },
    /// The factory has exceeded its creation budget for this epoch.
    BudgetExceeded { limit: u64, used: u64 },
    /// The factory VK doesn't match the claimed descriptor.
    FactoryVkMismatch { expected: [u8; 32], got: [u8; 32] },
    /// The derived child VK doesn't match the expected derivation.
    DerivedVkMismatch {
        expected: [u8; 32],
        got: Option<[u8; 32]>,
    },
    /// The claimed child VK is not in the factory's approved set.
    VkNotInApprovedSet {
        claimed: Option<[u8; 32]>,
        set_size: usize,
    },
}

impl std::fmt::Display for FactoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FactoryError::ProgramMismatch { expected, got } => {
                write!(
                    f,
                    "child program VK mismatch: expected {:?}, got {:?}",
                    expected, got
                )
            }
            FactoryError::ModeMismatch { expected, got } => {
                write!(
                    f,
                    "cell mode mismatch: expected {:?}, got {:?}",
                    expected, got
                )
            }
            FactoryError::CapabilityOutsideTemplate { cap_index } => {
                write!(
                    f,
                    "capability at index {} outside factory template",
                    cap_index
                )
            }
            FactoryError::FieldConstraintViolation {
                field_index,
                reason,
            } => {
                write!(f, "field {} constraint violated: {}", field_index, reason)
            }
            FactoryError::BudgetExceeded { limit, used } => {
                write!(f, "factory budget exceeded: limit={}, used={}", limit, used)
            }
            FactoryError::FactoryVkMismatch { expected, got } => {
                write!(
                    f,
                    "factory VK mismatch: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    expected[0], expected[1], got[0], got[1]
                )
            }
            FactoryError::DerivedVkMismatch { expected, got } => {
                write!(
                    f,
                    "derived child VK mismatch: expected {:02x}{:02x}..., got {:?}",
                    expected[0],
                    expected[1],
                    got.map(|g| format!("{:02x}{:02x}...", g[0], g[1]))
                )
            }
            FactoryError::VkNotInApprovedSet { claimed, set_size } => {
                write!(
                    f,
                    "child VK {:?} not in approved set of {} VKs",
                    claimed.map(|c| format!("{:02x}{:02x}...", c[0], c[1])),
                    set_size
                )
            }
        }
    }
}

impl std::error::Error for FactoryError {}

/// A factory registry: tracks deployed factories and their creation counts per epoch.
#[derive(Clone, Debug, Default)]
pub struct FactoryRegistry {
    /// Deployed factory descriptors, keyed by factory VK hash.
    pub descriptors: std::collections::HashMap<[u8; 32], FactoryDescriptor>,
    /// Creation counts per epoch: (factory_vk, epoch) -> count.
    pub creation_counts: std::collections::HashMap<([u8; 32], u64), u64>,
    /// Current epoch number.
    pub current_epoch: u64,
}

impl FactoryRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Deploy a factory, registering its descriptor.
    ///
    /// Returns the factory VK hash as an identifier.
    pub fn deploy(&mut self, descriptor: FactoryDescriptor) -> [u8; 32] {
        let vk = descriptor.factory_vk;
        self.descriptors.insert(vk, descriptor);
        vk
    }

    /// Get a factory descriptor by VK hash.
    pub fn get(&self, factory_vk: &[u8; 32]) -> Option<&FactoryDescriptor> {
        self.descriptors.get(factory_vk)
    }

    /// Record a creation and check budget.
    ///
    /// Returns `Ok(())` if within budget, or an error if exceeded.
    pub fn record_creation(&mut self, factory_vk: &[u8; 32]) -> Result<(), FactoryError> {
        let descriptor =
            self.descriptors
                .get(factory_vk)
                .ok_or(FactoryError::FactoryVkMismatch {
                    expected: *factory_vk,
                    got: [0u8; 32],
                })?;

        if let Some(budget) = descriptor.creation_budget {
            let key = (*factory_vk, self.current_epoch);
            let count = self.creation_counts.entry(key).or_insert(0);
            if *count >= budget {
                return Err(FactoryError::BudgetExceeded {
                    limit: budget,
                    used: *count,
                });
            }
            *count += 1;
        }

        Ok(())
    }

    /// Advance to a new epoch (resets creation counters for previous epochs).
    pub fn advance_epoch(&mut self) {
        self.current_epoch += 1;
        // Retain only current epoch counts.
        let current = self.current_epoch;
        self.creation_counts
            .retain(|(_, epoch), _| *epoch == current);
    }

    /// Validate a creation against the factory descriptor and budget.
    pub fn validate_and_record(
        &mut self,
        factory_vk: &[u8; 32],
        params: &FactoryCreationParams,
    ) -> Result<(), FactoryError> {
        // Get descriptor (clone to avoid borrow conflict).
        let descriptor =
            self.descriptors
                .get(factory_vk)
                .cloned()
                .ok_or(FactoryError::FactoryVkMismatch {
                    expected: *factory_vk,
                    got: [0u8; 32],
                })?;

        // Validate creation params against descriptor.
        descriptor.validate_creation(params)?;

        // Check and record budget.
        self.record_creation(factory_vk)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_factory_vk() -> [u8; 32] {
        *blake3::hash(b"test-factory").as_bytes()
    }

    fn test_child_vk() -> [u8; 32] {
        *blake3::hash(b"test-child-program").as_bytes()
    }

    fn worker_factory_descriptor() -> FactoryDescriptor {
        let coordinator_id = CellId::derive_raw(&[1u8; 32], &[0u8; 32]);
        FactoryDescriptor {
            factory_vk: test_factory_vk(),
            child_program_vk: Some(test_child_vk()),
            child_vk_strategy: None,
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::Specific(coordinator_id),
                max_permissions: AuthRequired::None,
                attenuatable: false,
            }],
            field_constraints: vec![
                FieldConstraint::Equality {
                    field_index: 0,
                    value: 42,
                },
                FieldConstraint::Range {
                    field_index: 1,
                    min: 1,
                    max: 100,
                },
            ],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: Some(10),
        }
    }

    #[test]
    fn test_deploy_factory() {
        let mut registry = FactoryRegistry::new();
        let desc = worker_factory_descriptor();
        let vk = registry.deploy(desc.clone());
        assert_eq!(vk, test_factory_vk());
        assert_eq!(registry.get(&vk), Some(&desc));
    }

    #[test]
    fn test_valid_creation() {
        let desc = worker_factory_descriptor();
        let coordinator_id = CellId::derive_raw(&[1u8; 32], &[0u8; 32]);
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![CapGrant {
                target: CapTarget::Specific(coordinator_id),
                max_permissions: AuthRequired::None,
                attenuatable: false,
            }],
            owner_pubkey: [2u8; 32],
        };
        assert!(desc.validate_creation(&params).is_ok());
    }

    #[test]
    fn test_program_mismatch() {
        let desc = worker_factory_descriptor();
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None, // Wrong: factory requires Some
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(err, FactoryError::ProgramMismatch { .. }));
    }

    #[test]
    fn test_mode_mismatch() {
        let desc = worker_factory_descriptor();
        let params = FactoryCreationParams {
            mode: CellMode::Sovereign, // Wrong: factory specifies Hosted
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(err, FactoryError::ModeMismatch { .. }));
    }

    #[test]
    fn test_capability_outside_template() {
        let desc = worker_factory_descriptor();
        let rogue_cell = CellId::derive_raw(&[99u8; 32], &[0u8; 32]);
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![CapGrant {
                target: CapTarget::Specific(rogue_cell), // Not in template
                max_permissions: AuthRequired::None,
                attenuatable: false,
            }],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(
            err,
            FactoryError::CapabilityOutsideTemplate { .. }
        ));
    }

    #[test]
    fn test_field_equality_constraint_violated() {
        let desc = worker_factory_descriptor();
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 99), (1, 50)], // field 0 must be 42
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(err, FactoryError::FieldConstraintViolation { .. }));
    }

    #[test]
    fn test_field_range_constraint_violated() {
        let desc = worker_factory_descriptor();
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 200)], // field 1 range is [1, 100]
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(err, FactoryError::FieldConstraintViolation { .. }));
    }

    #[test]
    fn test_budget_enforcement() {
        let mut registry = FactoryRegistry::new();
        let desc = worker_factory_descriptor(); // budget = 10
        let vk = registry.deploy(desc);

        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };

        // Should succeed 10 times.
        for _ in 0..10 {
            assert!(registry.validate_and_record(&vk, &params).is_ok());
        }

        // 11th should fail.
        let err = registry.validate_and_record(&vk, &params).unwrap_err();
        assert!(matches!(
            err,
            FactoryError::BudgetExceeded { limit: 10, .. }
        ));
    }

    #[test]
    fn test_budget_resets_on_epoch_advance() {
        let mut registry = FactoryRegistry::new();
        let desc = worker_factory_descriptor();
        let vk = registry.deploy(desc);

        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };

        // Use up budget.
        for _ in 0..10 {
            registry.validate_and_record(&vk, &params).unwrap();
        }
        assert!(registry.validate_and_record(&vk, &params).is_err());

        // Advance epoch.
        registry.advance_epoch();

        // Should succeed again.
        assert!(registry.validate_and_record(&vk, &params).is_ok());
    }

    #[test]
    fn test_provenance_creation() {
        let prov = Provenance::from_factory(test_factory_vk(), Some([0xAB; 32]), 100);
        assert_eq!(prov.created_by_factory, Some(test_factory_vk()));
        assert_eq!(prov.creation_proof_hash, Some([0xAB; 32]));
        assert_eq!(prov.creation_height, 100);
    }

    #[test]
    fn test_provenance_genesis() {
        let prov = Provenance::genesis(0);
        assert_eq!(prov.created_by_factory, None);
        assert_eq!(prov.creation_proof_hash, None);
        assert_eq!(prov.creation_height, 0);
    }

    #[test]
    fn test_descriptor_hash_deterministic() {
        let desc = worker_factory_descriptor();
        let h1 = desc.hash();
        let h2 = desc.hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_descriptor_hash_changes_with_content() {
        let desc1 = worker_factory_descriptor();
        let mut desc2 = worker_factory_descriptor();
        desc2.creation_budget = Some(20);
        assert_ne!(desc1.hash(), desc2.hash());
    }

    #[test]
    fn test_sovereign_factory() {
        let desc = FactoryDescriptor {
            factory_vk: test_factory_vk(),
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            }],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Sovereign,
            creation_budget: None,
        };

        let params = FactoryCreationParams {
            mode: CellMode::Sovereign,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![CapGrant {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            }],
            owner_pubkey: [3u8; 32],
        };

        assert!(desc.validate_creation(&params).is_ok());
    }

    #[test]
    fn test_any_target_template_allows_any_specific() {
        let desc = FactoryDescriptor {
            factory_vk: test_factory_vk(),
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::Any,
                max_permissions: AuthRequired::None,
                attenuatable: true,
            }],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: None,
        };

        let random_cell = CellId::derive_raw(&[77u8; 32], &[0u8; 32]);
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![CapGrant {
                target: CapTarget::Specific(random_cell),
                max_permissions: AuthRequired::None,
                attenuatable: true,
            }],
            owner_pubkey: [4u8; 32],
        };

        assert!(desc.validate_creation(&params).is_ok());
    }

    // =========================================================================
    // Computable child VK tests
    // =========================================================================

    #[test]
    fn test_derived_vk_strategy_creates_correct_vk() {
        let factory_vk = test_factory_vk();
        let desc = FactoryDescriptor {
            factory_vk,
            child_program_vk: None,
            child_vk_strategy: Some(ChildVkStrategy::Derived {
                base_vk: factory_vk,
            }),
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: None,
        };

        // Compute what the derived VK should be for these params.
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None, // Will be overwritten with derived VK
            initial_fields: vec![(0, 100), (1, 200)],
            initial_caps: vec![],
            owner_pubkey: [5u8; 32],
        };
        let param_hash = ChildVkStrategy::compute_param_hash(&params);
        let derived_vk = ChildVkStrategy::derive_child_vk(&factory_vk, &param_hash);

        // Creation with correct derived VK succeeds.
        let params_with_vk = FactoryCreationParams {
            program_vk: Some(derived_vk),
            ..params.clone()
        };
        assert!(desc.validate_creation(&params_with_vk).is_ok());

        // Creation with wrong VK fails.
        let wrong_params = FactoryCreationParams {
            program_vk: Some([0xAA; 32]),
            ..params
        };
        let err = desc.validate_creation(&wrong_params).unwrap_err();
        assert!(matches!(err, FactoryError::DerivedVkMismatch { .. }));
    }

    #[test]
    fn test_derived_vk_different_params_different_vk() {
        let factory_vk = test_factory_vk();

        let params_a = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![(0, 1)], // token A
            initial_caps: vec![],
            owner_pubkey: [5u8; 32],
        };
        let params_b = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![(0, 2)], // token B
            initial_caps: vec![],
            owner_pubkey: [5u8; 32],
        };

        let hash_a = ChildVkStrategy::compute_param_hash(&params_a);
        let hash_b = ChildVkStrategy::compute_param_hash(&params_b);
        let vk_a = ChildVkStrategy::derive_child_vk(&factory_vk, &hash_a);
        let vk_b = ChildVkStrategy::derive_child_vk(&factory_vk, &hash_b);

        // Different params must produce different VKs.
        assert_ne!(vk_a, vk_b);
    }

    #[test]
    fn test_from_set_strategy_allows_approved_vk() {
        let factory_vk = test_factory_vk();
        let vk_admin = *blake3::hash(b"admin-program").as_bytes();
        let vk_reader = *blake3::hash(b"reader-program").as_bytes();
        let vk_writer = *blake3::hash(b"writer-program").as_bytes();

        let desc = FactoryDescriptor {
            factory_vk,
            child_program_vk: None,
            child_vk_strategy: Some(ChildVkStrategy::FromSet {
                approved_vks: vec![vk_admin, vk_reader, vk_writer],
            }),
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: None,
        };

        // Creating with an approved VK succeeds.
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(vk_reader),
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: [6u8; 32],
        };
        assert!(desc.validate_creation(&params).is_ok());

        // Creating with an unapproved VK fails.
        let bad_params = FactoryCreationParams {
            program_vk: Some(*blake3::hash(b"rogue-program").as_bytes()),
            ..params
        };
        let err = desc.validate_creation(&bad_params).unwrap_err();
        assert!(matches!(err, FactoryError::VkNotInApprovedSet { .. }));
    }

    #[test]
    fn test_from_set_rejects_none_vk() {
        let factory_vk = test_factory_vk();
        let vk_admin = *blake3::hash(b"admin-program").as_bytes();

        let desc = FactoryDescriptor {
            factory_vk,
            child_program_vk: None,
            child_vk_strategy: Some(ChildVkStrategy::FromSet {
                approved_vks: vec![vk_admin],
            }),
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: None,
        };

        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None, // Not in the set
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: [7u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(err, FactoryError::VkNotInApprovedSet { .. }));
    }

    #[test]
    fn test_provenance_derivation_verification() {
        let factory_vk = test_factory_vk();

        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![(0, 42)],
            initial_caps: vec![],
            owner_pubkey: [8u8; 32],
        };
        let param_hash = ChildVkStrategy::compute_param_hash(&params);
        let derived_vk = ChildVkStrategy::derive_child_vk(&factory_vk, &param_hash);

        let prov = Provenance::from_factory_derived(factory_vk, None, 50, param_hash);
        assert!(prov.verify_derivation(&derived_vk));
        assert!(!prov.verify_derivation(&[0xBB; 32])); // wrong VK
    }

    #[test]
    fn test_child_vk_strategy_hash_deterministic() {
        let s1 = ChildVkStrategy::Derived {
            base_vk: test_factory_vk(),
        };
        let s2 = ChildVkStrategy::Derived {
            base_vk: test_factory_vk(),
        };
        assert_eq!(s1.hash(), s2.hash());
    }

    #[test]
    fn test_child_vk_strategy_hash_differs_between_variants() {
        let fixed = ChildVkStrategy::Fixed(Some(test_child_vk()));
        let derived = ChildVkStrategy::Derived {
            base_vk: test_factory_vk(),
        };
        let from_set = ChildVkStrategy::FromSet {
            approved_vks: vec![test_child_vk()],
        };
        assert_ne!(fixed.hash(), derived.hash());
        assert_ne!(derived.hash(), from_set.hash());
        assert_ne!(fixed.hash(), from_set.hash());
    }

    #[test]
    fn test_descriptor_hash_changes_with_strategy() {
        let mut desc = worker_factory_descriptor();
        let h1 = desc.hash();
        desc.child_vk_strategy = Some(ChildVkStrategy::Derived {
            base_vk: test_factory_vk(),
        });
        let h2 = desc.hash();
        assert_ne!(h1, h2);
    }

    // =========================================================================
    // Canonical program VK tests (VK-AS-RE-EXECUTION-RECIPE.md §2.1)
    // =========================================================================

    fn canonical_test_program() -> CellProgram {
        use crate::program::{StateConstraint, TransitionCase, TransitionGuard};
        CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::WriteOnce { index: 2 },
                StateConstraint::Monotonic { index: 4 },
            ],
        }])
    }

    #[test]
    fn canonical_program_vk_is_deterministic() {
        let p = canonical_test_program();
        let h1 = canonical_program_vk(&p);
        let h2 = canonical_program_vk(&p);
        assert_eq!(h1, h2, "canonical VK must be deterministic");
    }

    #[test]
    fn canonical_program_vk_changes_with_program_shape() {
        use crate::program::{StateConstraint, TransitionCase, TransitionGuard};
        let p1 = canonical_test_program();
        // Same shape but with one additional constraint — must hash differently.
        let p2 = CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::WriteOnce { index: 2 },
                StateConstraint::Monotonic { index: 4 },
                StateConstraint::Immutable { index: 5 },
            ],
        }]);
        assert_ne!(canonical_program_vk(&p1), canonical_program_vk(&p2));
    }

    #[test]
    fn canonical_program_vk_changes_with_constraint_index() {
        use crate::program::{StateConstraint, TransitionCase, TransitionGuard};
        let p1 = CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![StateConstraint::WriteOnce { index: 2 }],
        }]);
        // Same shape, different index value — must hash differently.
        let p2 = CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![StateConstraint::WriteOnce { index: 3 }],
        }]);
        assert_ne!(canonical_program_vk(&p1), canonical_program_vk(&p2));
    }

    #[test]
    fn canonical_program_vk_none_program_has_stable_hash() {
        // Even the trivial program has a stable canonical VK — apps that
        // pin child_program_vk to `canonical_program_vk(&CellProgram::None)`
        // get a real cryptographic identifier, not a placeholder.
        let p = CellProgram::None;
        let h = canonical_program_vk(&p);
        // Non-zero (BLAKE3 of any input is non-zero w.h.p.).
        assert_ne!(h, [0u8; 32]);
        // Deterministic.
        assert_eq!(h, canonical_program_vk(&CellProgram::None));
    }

    #[test]
    fn canonical_program_vk_distinguishes_none_from_empty_cases() {
        // `CellProgram::None` and `CellProgram::Cases(vec![])` are
        // semantically very different (the second default-denies every
        // transition); their canonical VKs must differ.
        let none_vk = canonical_program_vk(&CellProgram::None);
        let empty_cases_vk = canonical_program_vk(&CellProgram::Cases(vec![]));
        assert_ne!(none_vk, empty_cases_vk);
    }

    #[test]
    fn validate_child_vk_canonical_accepts_canonical_program() {
        let program = canonical_test_program();
        let vk = canonical_program_vk(&program);
        let desc = FactoryDescriptor {
            factory_vk: test_factory_vk(),
            child_program_vk: Some(vk),
            child_vk_strategy: None,
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: None,
        };
        desc.validate_child_vk_canonical(&program)
            .expect("descriptor's VK must validate against its canonical program");
    }

    #[test]
    fn validate_child_vk_canonical_rejects_mismatched_program() {
        use crate::program::{StateConstraint, TransitionCase, TransitionGuard};
        let program = canonical_test_program();
        let vk = canonical_program_vk(&program);
        let desc = FactoryDescriptor {
            factory_vk: test_factory_vk(),
            child_program_vk: Some(vk),
            child_vk_strategy: None,
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: None,
        };
        // A different program — the descriptor's VK should not bind to it.
        let other = CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![StateConstraint::Immutable { index: 7 }],
        }]);
        let err = desc
            .validate_child_vk_canonical(&other)
            .expect_err("mismatched program must be rejected");
        assert!(matches!(err, FactoryError::ProgramMismatch { .. }));
    }

    #[test]
    fn validate_child_vk_canonical_rejects_none_child_vk() {
        let program = canonical_test_program();
        let desc = FactoryDescriptor {
            factory_vk: test_factory_vk(),
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Sovereign,
            creation_budget: None,
        };
        let err = desc
            .validate_child_vk_canonical(&program)
            .expect_err("descriptor with None child_program_vk cannot validate any program");
        assert!(matches!(
            err,
            FactoryError::ProgramMismatch {
                got: None,
                expected: Some(_)
            }
        ));
    }
}
