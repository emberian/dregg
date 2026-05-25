//! Custom-effect verifier registry — vk_hash → (canonical bytes,
//! verifier) for [`pyana_circuit::effect_vm::Effect::Custom`].
//!
//! Mirrors the [`WitnessedPredicateRegistry`](crate::predicate::WitnessedPredicateRegistry)
//! shape: the executor holds an instance, looks up entries by the
//! 32-byte `vk_hash`, and dispatches the proof to the registered
//! verifier. Designed so that *every place pyana names a custom
//! verifier by hash* (slot-caveat `Custom`, `WitnessedPredicateKind::Custom`,
//! `Effect::Custom`, `FactoryDescriptor.child_program_vk`) shares the
//! same registration + dispatch + audit surface.
//!
//! Per `VK-AS-RE-EXECUTION-RECIPE.md` §2.4 + §3, a `vk_hash` is a
//! BLAKE3 keyed hash of *canonical executable bytes* — the bytes
//! the validator re-executes against the proof's witness to confirm
//! acceptance. The registry stores those canonical bytes alongside
//! the live verifier handle:
//!
//! - Validators can re-derive `vk_hash = canonical_predicate_vk(&bytes)`
//!   to confirm registry honesty.
//! - Auditors can pull bytes from the registry for offline
//!   re-execution.
//! - The executor's hot path uses the verifier handle to dispatch
//!   without re-deserializing.
//!
//! ## Why a separate registry from `WitnessedPredicateRegistry`?
//!
//! Slot caveats / preconditions / authorization predicates all hand
//! the verifier a *predicate input* (slot value, witness bytes, signing
//! message, sender pk). `Effect::Custom`'s domain-specific proofs are
//! AIR-shaped — they verify against `(public_inputs, proof_bytes)`
//! pairs where `public_inputs` is a vector of field elements
//! (`BabyBear`-encoded) produced by the executor's `effect_vm` lowering.
//! The verifier signatures differ enough to warrant their own trait,
//! but the registry plumbing is identical.
//!
//! ## v1 scope
//!
//! Same as the witnessed-predicate registry's v1: ship the
//! registration surface + a stub verifier (accepts non-empty proof
//! bytes, rejects empty) so the executor's dispatch can be exercised
//! without pulling in the heavyweight circuit. Production wiring
//! registers `pyana_circuit::dsl::circuit::CellProgram` verifiers via
//! [`CustomEffectRegistry::register`].
//!
//! ## Boundary contract
//!
//! Per `BOUNDARIES.md §5.2`:
//!
//! - Cleartext-inside:  VK author (writes the canonical bytes) +
//!                      validators (re-execute the bytes pre-recursion).
//! - Commitment-inside: receipt observers (see vk_hash + acceptance bit).
//! - Acceptance-inside: post-recursion validators (proof + verifying key).
//! - Out-of-band:       everyone outside the validator + observer
//!                      populations.
//! Enforced by: BLAKE3 keyed-hash binding canonical bytes to vk_hash;
//! the executor refuses registrations whose canonical bytes don't
//! match the registration key.
//! Failure mode if violated: validator's re-execution disagrees with
//! executor's claimed acceptance bit (soundness failure → consensus).

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::predicate::canonical_predicate_vk;

/// Errors a [`CustomEffectVerifier`] can produce.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CustomEffectError {
    /// The verifier rejected the proof.
    Rejected {
        vk_hash: [u8; 32],
        name: &'static str,
        reason: String,
    },
    /// No verifier is registered for this vk_hash.
    VkHashNotRegistered { vk_hash: [u8; 32] },
    /// The canonical bytes registered under `vk_hash` don't hash to
    /// `vk_hash` — a registration was attempted with mismatched bytes.
    /// This is a registration-time error, not a verification-time
    /// one, but we surface it through the registry so callers see a
    /// consistent error surface.
    CanonicalBindingMismatch {
        claimed_vk_hash: [u8; 32],
        computed_vk_hash: [u8; 32],
    },
    /// The action did not carry the expected proof bytes.
    ProofMissing { vk_hash: [u8; 32] },
}

impl core::fmt::Display for CustomEffectError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Rejected {
                vk_hash,
                name,
                reason,
            } => write!(
                f,
                "custom-effect {name} ({:02x}{:02x}...) rejected: {reason}",
                vk_hash[0], vk_hash[1]
            ),
            Self::VkHashNotRegistered { vk_hash } => write!(
                f,
                "no custom-effect verifier registered for vk_hash {:02x}{:02x}...",
                vk_hash[0], vk_hash[1]
            ),
            Self::CanonicalBindingMismatch {
                claimed_vk_hash,
                computed_vk_hash,
            } => write!(
                f,
                "canonical bytes do not hash to claimed vk_hash: \
                 claimed {:02x}{:02x}..., computed {:02x}{:02x}...",
                claimed_vk_hash[0], claimed_vk_hash[1], computed_vk_hash[0], computed_vk_hash[1],
            ),
            Self::ProofMissing { vk_hash } => write!(
                f,
                "custom-effect proof missing for vk_hash {:02x}{:02x}...",
                vk_hash[0], vk_hash[1]
            ),
        }
    }
}

impl std::error::Error for CustomEffectError {}

/// A registered verifier for an [`Effect::Custom`] vk_hash.
///
/// The trait is object-safe so the registry can hold
/// `Arc<dyn CustomEffectVerifier>` and dispatch by vk_hash at runtime.
/// Implementations live wherever the underlying program lives —
/// `pyana_circuit::dsl::circuit::CellProgram` for DSL-authored
/// programs, app-side crates for app-defined verifiers.
pub trait CustomEffectVerifier: Send + Sync {
    /// Human-readable name for diagnostics.
    fn name(&self) -> &'static str;

    /// The vk_hash this verifier handles. Must equal the registry key.
    fn vk_hash(&self) -> [u8; 32];

    /// Verify a custom-effect proof.
    ///
    /// `public_inputs` is the executor-computed PI vector for the
    /// Effect VM AIR slot; `proof_bytes` is the serialized STARK (or
    /// app-specific) proof carried by the action.
    ///
    /// Returns `Ok(())` on accept; `CustomEffectError::Rejected` on
    /// algebraic reject.
    fn verify(&self, public_inputs: &[u8], proof_bytes: &[u8]) -> Result<(), CustomEffectError>;
}

/// The registry resolving `Effect::Custom` vk_hashes to their
/// verifiers + canonical bytes.
///
/// Mirrors [`WitnessedPredicateRegistry`](crate::predicate::WitnessedPredicateRegistry)'s
/// shape, keyed on the 32-byte vk_hash. Unlike the witnessed-predicate
/// registry, there's no built-in / custom distinction — every entry
/// is keyed on the same kind of hash (a `canonical_predicate_vk`
/// of the verifier's authoring bytes).
///
/// The registry is **not** a singleton — each executor instance can
/// hold its own (a host that wants to refuse a custom effect simply
/// doesn't register it).
#[derive(Default, Clone)]
pub struct CustomEffectRegistry {
    entries: BTreeMap<[u8; 32], Entry>,
}

#[derive(Clone)]
struct Entry {
    /// Canonical bytes whose BLAKE3-keyed hash is the registration key.
    canonical_bytes: Vec<u8>,
    /// Live verifier handle (the dispatch target).
    verifier: Arc<dyn CustomEffectVerifier>,
}

impl std::fmt::Debug for CustomEffectRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CustomEffectRegistry")
            .field("entries_count", &self.entries.len())
            .finish()
    }
}

impl CustomEffectRegistry {
    /// Construct an empty registry.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Register a verifier under its canonical bytes.
    ///
    /// The vk_hash is derived from `canonical_bytes` via
    /// [`canonical_predicate_vk`]; the verifier's
    /// [`vk_hash()`](CustomEffectVerifier::vk_hash) must match. Both
    /// the canonical bytes and the verifier handle are stored.
    ///
    /// Returns the computed `vk_hash` on success.
    pub fn register(
        &mut self,
        canonical_bytes: Vec<u8>,
        verifier: Arc<dyn CustomEffectVerifier>,
    ) -> Result<[u8; 32], CustomEffectError> {
        let computed = canonical_predicate_vk(&canonical_bytes);
        let claimed = verifier.vk_hash();
        if computed != claimed {
            return Err(CustomEffectError::CanonicalBindingMismatch {
                claimed_vk_hash: claimed,
                computed_vk_hash: computed,
            });
        }
        self.entries.insert(
            computed,
            Entry {
                canonical_bytes,
                verifier,
            },
        );
        Ok(computed)
    }

    /// Register a verifier under a *pre-computed* vk_hash without
    /// canonical bytes. Useful for verifiers whose canonical bytes
    /// are stored externally (the program registry already, etc.).
    ///
    /// **Soundness note:** without canonical bytes, validators cannot
    /// re-execute. Use this only when canonical bytes live in a
    /// parallel registry that's queryable on dispute.
    pub fn register_without_bytes(&mut self, verifier: Arc<dyn CustomEffectVerifier>) -> [u8; 32] {
        let vk_hash = verifier.vk_hash();
        self.entries.insert(
            vk_hash,
            Entry {
                canonical_bytes: Vec::new(),
                verifier,
            },
        );
        vk_hash
    }

    /// Look up a verifier by vk_hash. Returns `None` if not registered.
    pub fn get(&self, vk_hash: &[u8; 32]) -> Option<Arc<dyn CustomEffectVerifier>> {
        self.entries.get(vk_hash).map(|e| e.verifier.clone())
    }

    /// Look up the canonical bytes for a vk_hash. Returns `None` if
    /// not registered or if registered via
    /// [`register_without_bytes`](Self::register_without_bytes).
    pub fn canonical_bytes(&self, vk_hash: &[u8; 32]) -> Option<&[u8]> {
        self.entries
            .get(vk_hash)
            .map(|e| e.canonical_bytes.as_slice())
            .filter(|b| !b.is_empty())
    }

    /// Check if a vk_hash is registered.
    pub fn contains(&self, vk_hash: &[u8; 32]) -> bool {
        self.entries.contains_key(vk_hash)
    }

    /// Number of registered entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Verify a custom-effect proof against the verifier registered
    /// under `vk_hash`. Returns `Ok(())` on accept;
    /// `VkHashNotRegistered` if no entry exists; the verifier's
    /// own [`Rejected`](CustomEffectError::Rejected) on algebraic
    /// reject.
    pub fn verify(
        &self,
        vk_hash: &[u8; 32],
        public_inputs: &[u8],
        proof_bytes: &[u8],
    ) -> Result<(), CustomEffectError> {
        if proof_bytes.is_empty() {
            return Err(CustomEffectError::ProofMissing { vk_hash: *vk_hash });
        }
        let verifier = self
            .get(vk_hash)
            .ok_or(CustomEffectError::VkHashNotRegistered { vk_hash: *vk_hash })?;
        verifier.verify(public_inputs, proof_bytes)
    }
}

// ─────────────────────────────────────────────────────────────────────
// Stub verifier (development / tests)
// ─────────────────────────────────────────────────────────────────────

/// A stub verifier for development / unit tests. Accepts non-empty
/// proof bytes; rejects empty ones. Does NOT perform real
/// cryptographic verification.
///
/// Production callers MUST replace stubs with real verifiers before
/// evaluating any custom effect. The presence of a stub is a
/// deliberate fail-safe-but-loud signal: dispatch plumbing works,
/// soundness is the real verifier's job.
pub struct StubCustomEffectVerifier {
    vk_hash: [u8; 32],
    name: &'static str,
}

impl StubCustomEffectVerifier {
    /// Construct a stub verifier with the given vk_hash and name.
    pub fn new(vk_hash: [u8; 32], name: &'static str) -> Self {
        Self { vk_hash, name }
    }
}

impl CustomEffectVerifier for StubCustomEffectVerifier {
    fn name(&self) -> &'static str {
        self.name
    }

    fn vk_hash(&self) -> [u8; 32] {
        self.vk_hash
    }

    fn verify(&self, _public_inputs: &[u8], proof_bytes: &[u8]) -> Result<(), CustomEffectError> {
        if proof_bytes.is_empty() {
            return Err(CustomEffectError::Rejected {
                vk_hash: self.vk_hash,
                name: self.name,
                reason: "stub verifier requires non-empty proof bytes".into(),
            });
        }
        Ok(())
    }
}

// ─────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn registry_with_one_entry() -> (CustomEffectRegistry, [u8; 32], Vec<u8>) {
        let bytes = b"stub-cell-program-v1".to_vec();
        let vk_hash = canonical_predicate_vk(&bytes);
        let verifier = Arc::new(StubCustomEffectVerifier::new(vk_hash, "stub-program"));
        let mut reg = CustomEffectRegistry::empty();
        reg.register(bytes.clone(), verifier).expect("register");
        (reg, vk_hash, bytes)
    }

    #[test]
    fn register_and_verify_round_trips() {
        let (reg, vk_hash, _) = registry_with_one_entry();
        reg.verify(&vk_hash, b"pi", b"proof").expect("accept");
    }

    #[test]
    fn unknown_vk_hash_yields_not_registered() {
        let reg = CustomEffectRegistry::empty();
        let err = reg.verify(&[7u8; 32], b"pi", b"proof").unwrap_err();
        assert!(matches!(err, CustomEffectError::VkHashNotRegistered { .. }));
    }

    #[test]
    fn empty_proof_bytes_rejected() {
        let (reg, vk_hash, _) = registry_with_one_entry();
        let err = reg.verify(&vk_hash, b"pi", b"").unwrap_err();
        assert!(matches!(err, CustomEffectError::ProofMissing { .. }));
    }

    #[test]
    fn canonical_binding_mismatch_rejected_at_registration_time() {
        // Build a verifier claiming vk_hash X, register with canonical
        // bytes whose hash is Y != X.
        let bogus_vk = [0xFFu8; 32];
        let verifier = Arc::new(StubCustomEffectVerifier::new(bogus_vk, "bogus"));
        let bytes = b"different-bytes".to_vec();
        let mut reg = CustomEffectRegistry::empty();
        let err = reg.register(bytes, verifier).unwrap_err();
        match err {
            CustomEffectError::CanonicalBindingMismatch {
                claimed_vk_hash,
                computed_vk_hash,
            } => {
                assert_eq!(claimed_vk_hash, bogus_vk);
                assert_ne!(claimed_vk_hash, computed_vk_hash);
            }
            other => panic!("expected CanonicalBindingMismatch, got: {other:?}"),
        }
    }

    #[test]
    fn canonical_bytes_retrievable_after_register() {
        let (reg, vk_hash, bytes) = registry_with_one_entry();
        assert_eq!(reg.canonical_bytes(&vk_hash), Some(bytes.as_slice()));
    }

    #[test]
    fn canonical_bytes_none_for_register_without_bytes() {
        let mut reg = CustomEffectRegistry::empty();
        let vk = [0x42u8; 32];
        let verifier = Arc::new(StubCustomEffectVerifier::new(vk, "no-bytes"));
        let returned = reg.register_without_bytes(verifier);
        assert_eq!(returned, vk);
        assert!(reg.contains(&vk));
        // No canonical bytes were stored.
        assert!(reg.canonical_bytes(&vk).is_none());
    }

    #[test]
    fn tampered_verifier_proof_bytes_rejected_via_kind_verifier() {
        // Register a verifier that *checks* its proof bytes (parses a
        // length-prefixed header). Tampered proof bytes get rejected
        // through the registered verifier path.
        struct LenCheck {
            vk: [u8; 32],
        }
        impl CustomEffectVerifier for LenCheck {
            fn name(&self) -> &'static str {
                "len-check"
            }
            fn vk_hash(&self) -> [u8; 32] {
                self.vk
            }
            fn verify(&self, _pi: &[u8], proof_bytes: &[u8]) -> Result<(), CustomEffectError> {
                if proof_bytes.len() < 4 {
                    return Err(CustomEffectError::Rejected {
                        vk_hash: self.vk,
                        name: "len-check",
                        reason: "proof bytes shorter than 4-byte header".into(),
                    });
                }
                let claimed_len = u32::from_le_bytes([
                    proof_bytes[0],
                    proof_bytes[1],
                    proof_bytes[2],
                    proof_bytes[3],
                ]) as usize;
                if claimed_len + 4 != proof_bytes.len() {
                    return Err(CustomEffectError::Rejected {
                        vk_hash: self.vk,
                        name: "len-check",
                        reason: format!(
                            "header claims {claimed_len} bytes but proof has {} after header",
                            proof_bytes.len() - 4
                        ),
                    });
                }
                Ok(())
            }
        }

        let bytes = b"len-check-program".to_vec();
        let vk = canonical_predicate_vk(&bytes);
        let verifier = Arc::new(LenCheck { vk });
        let mut reg = CustomEffectRegistry::empty();
        reg.register(bytes, verifier).unwrap();

        // Honest proof: 3 bytes of payload after the length prefix.
        let mut honest = (3u32).to_le_bytes().to_vec();
        honest.extend_from_slice(&[0xAA, 0xBB, 0xCC]);
        reg.verify(&vk, b"pi", &honest).expect("honest accepted");

        // Tampered: flip a byte in the length header so it no longer
        // matches the payload size.
        let mut tampered = honest.clone();
        tampered[0] ^= 0x01;
        let err = reg.verify(&vk, b"pi", &tampered).unwrap_err();
        assert!(matches!(err, CustomEffectError::Rejected { .. }));
    }
}
