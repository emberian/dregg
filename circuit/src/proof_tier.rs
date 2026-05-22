//! Proof tier markers — prevents scaffold/test proofs from satisfying production verifiers.
//!
//! The codebase has multiple proof backends (custom STARK, Kimchi native, Mina/Pickles,
//! SP1, Binius, constraint prover, structural stubs). All produce bytes that look like
//! "proofs," but only a subset provide real cryptographic soundness guarantees.
//!
//! This module introduces:
//! - [`ProofTier`]: an enum marking whether a proof is production-grade, experimental,
//!   or structural-only.
//! - [`CryptographicProof`]: a marker trait that proof types implement to declare their tier.
//! - [`VerifiedProof`]: a wrapper returned by verification functions that carries the tier.
//!
//! Production code paths check the tier at the verification boundary to reject structural
//! stubs that would otherwise pass type-checking.

use std::fmt;

/// Proof tiers — prevents scaffold proofs from satisfying production verifiers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProofTier {
    /// Real cryptographic proof with full soundness guarantees.
    /// Only produced by: custom STARK (with ext-field composition), Kimchi native, Pickles.
    Production,
    /// Proof from a backend that is in development. May have known weaknesses.
    /// Produced by: custom STARK (base-field only), Poseidon STARK.
    Experimental,
    /// Structural validation only — no cryptographic guarantees.
    /// Produced by: SP1 stub (no feature), Binius stub (no feature), constraint prover.
    Structural,
}

impl fmt::Display for ProofTier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofTier::Production => write!(f, "Production"),
            ProofTier::Experimental => write!(f, "Experimental"),
            ProofTier::Structural => write!(f, "Structural"),
        }
    }
}

/// Marker trait for proofs that declare their cryptographic strength tier.
///
/// Backends implement this on their proof types so that verification boundaries
/// can reject non-production proofs without needing to know which specific backend
/// produced them.
pub trait CryptographicProof {
    /// Returns the tier of this proof.
    fn tier(&self) -> ProofTier;
}

/// A verified proof that carries its tier information.
///
/// Returned by verification functions. Production code paths inspect the tier
/// to reject structural or experimental proofs.
#[derive(Clone, Debug)]
pub struct VerifiedProof {
    /// The tier of the backend that produced this proof.
    tier: ProofTier,
    /// The backend name (for diagnostics).
    backend: &'static str,
    /// The federation root the proof was verified against (if applicable).
    pub federation_root: Option<[u8; 32]>,
}

impl VerifiedProof {
    /// Create a new verified proof with the given tier and backend name.
    pub fn new(tier: ProofTier, backend: &'static str) -> Self {
        Self {
            tier,
            backend,
            federation_root: None,
        }
    }

    /// Create a verified proof with federation root binding.
    pub fn with_federation_root(tier: ProofTier, backend: &'static str, root: [u8; 32]) -> Self {
        Self {
            tier,
            backend,
            federation_root: Some(root),
        }
    }

    /// Returns the tier of this verified proof.
    pub fn tier(&self) -> ProofTier {
        self.tier
    }

    /// Returns the backend name that produced this proof.
    pub fn backend(&self) -> &'static str {
        self.backend
    }

    /// Returns true if this proof is production-grade.
    pub fn is_production(&self) -> bool {
        self.tier == ProofTier::Production
    }

    /// Returns true if this proof is at least experimental (not structural).
    pub fn is_cryptographic(&self) -> bool {
        matches!(self.tier, ProofTier::Production | ProofTier::Experimental)
    }
}

impl CryptographicProof for VerifiedProof {
    fn tier(&self) -> ProofTier {
        self.tier
    }
}

// ============================================================================
// Tier assignments for each backend
// ============================================================================

/// Returns the proof tier for the custom STARK backend.
///
/// The custom STARK uses extension-field (BabyBear^4) composition for 124-bit
/// security on constraint combination, making it production-grade.
pub fn stark_tier() -> ProofTier {
    ProofTier::Production
}

/// Returns the proof tier for the Kimchi native backend.
///
/// Kimchi over Pasta curves provides IPA-based polynomial commitments with
/// full soundness. Production-grade.
pub fn kimchi_native_tier() -> ProofTier {
    ProofTier::Production
}

/// Returns the proof tier for the Poseidon STARK backend.
///
/// The Poseidon STARK is production-grade (uses the same ext-field STARK as the
/// primary backend, with Poseidon2 AIR constraints).
pub fn poseidon_stark_tier() -> ProofTier {
    ProofTier::Production
}

/// Returns the proof tier for the SP1 backend.
///
/// With the `sp1` feature enabled, SP1 produces real STARK proofs via the zkVM.
/// Without the feature, it produces structural stubs only.
pub fn sp1_tier() -> ProofTier {
    if cfg!(feature = "sp1") {
        ProofTier::Experimental
    } else {
        ProofTier::Structural
    }
}

/// Returns the proof tier for the Binius backend.
///
/// With the `binius` feature enabled, Binius produces real proofs over binary towers.
/// Without the feature, it produces structural stubs only.
pub fn binius_tier() -> ProofTier {
    if cfg!(feature = "binius") {
        ProofTier::Experimental
    } else {
        ProofTier::Structural
    }
}

/// Returns the proof tier for the constraint prover (mock prover).
///
/// The constraint prover validates AIR constraints directly on the execution trace
/// without generating cryptographic proofs. Always structural.
pub fn constraint_prover_tier() -> ProofTier {
    ProofTier::Structural
}

/// Returns the proof tier for the Plonky3 backend.
///
/// Plonky3 is a battle-tested proving system. Production-grade when available.
pub fn plonky3_tier() -> ProofTier {
    ProofTier::Production
}

// ============================================================================
// Backend name constants
// ============================================================================

/// Backend name for the custom STARK prover.
pub const STARK_BACKEND: &str = "custom-stark";
/// Backend name for Kimchi native.
pub const KIMCHI_BACKEND: &str = "kimchi-native";
/// Backend name for the Poseidon STARK.
pub const POSEIDON_STARK_BACKEND: &str = "poseidon-stark";
/// Backend name for SP1 zkVM.
pub const SP1_BACKEND: &str = "sp1";
/// Backend name for Binius binary towers.
pub const BINIUS_BACKEND: &str = "binius";
/// Backend name for the constraint prover.
pub const CONSTRAINT_PROVER_BACKEND: &str = "constraint-prover";
/// Backend name for Plonky3.
pub const PLONKY3_BACKEND: &str = "plonky3";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tier_display() {
        assert_eq!(ProofTier::Production.to_string(), "Production");
        assert_eq!(ProofTier::Experimental.to_string(), "Experimental");
        assert_eq!(ProofTier::Structural.to_string(), "Structural");
    }

    #[test]
    fn verified_proof_production() {
        let vp = VerifiedProof::new(ProofTier::Production, STARK_BACKEND);
        assert!(vp.is_production());
        assert!(vp.is_cryptographic());
        assert_eq!(vp.backend(), "custom-stark");
    }

    #[test]
    fn verified_proof_structural_rejected() {
        let vp = VerifiedProof::new(ProofTier::Structural, CONSTRAINT_PROVER_BACKEND);
        assert!(!vp.is_production());
        assert!(!vp.is_cryptographic());
    }

    #[test]
    fn verified_proof_experimental_is_cryptographic_but_not_production() {
        let vp = VerifiedProof::new(ProofTier::Experimental, SP1_BACKEND);
        assert!(!vp.is_production());
        assert!(vp.is_cryptographic());
    }

    #[test]
    fn stark_is_production() {
        assert_eq!(stark_tier(), ProofTier::Production);
    }

    #[test]
    fn constraint_prover_is_structural() {
        assert_eq!(constraint_prover_tier(), ProofTier::Structural);
    }
}
