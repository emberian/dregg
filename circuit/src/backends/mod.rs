//! Alternative proof backends for pyana circuits.
//!
//! While the primary STARK backend (`crate::stark`) uses BabyBear + FRI,
//! these backends provide alternative proof systems with different tradeoffs:
//!
//! - **Binius** (binary field towers): Operates natively over GF(2) tower extensions,
//!   producing very small proofs for hash-intensive circuits. Uses Groestl-256 (AES-based)
//!   which is native to the binary tower. Post-quantum secure. Expected ~1-4 KiB proofs
//!   for Merkle membership. Always compiled (stub mode without feature flag).
//!
//! - **Halo2** (Plonkish arithmetization): Produces smaller proofs (~1-5 KiB),
//!   uses elliptic curve pairings (Pasta curves / BN254). Better for on-chain
//!   verification where proof size matters.
//!
//! - **Nova** (folding-based IVC): Provides true incrementally verifiable
//!   computation via folding. Each additional fold step is O(1) work for the
//!   verifier, and the final proof is constant-size regardless of chain length.
//!   This directly solves the "linear proof growth" problem in attenuation chains.
//!
//! - **Mina/Kimchi** (Plonk variant over Pasta curves with IPA): Produces ~1-2 KiB
//!   proofs via Kimchi (a Plonk variant with custom gates) + Pickles (recursive
//!   proof composition over the Pasta cycle of curves). This is the same proof
//!   system that compresses the entire Mina blockchain into a single constant-size
//!   proof. NOT post-quantum secure, but provides true recursion via IPA over
//!   the Pallas/Vesta cycle.

#[cfg(feature = "halo2")]
pub mod halo2;

#[cfg(feature = "nova")]
pub mod nova;

#[cfg(feature = "mina")]
pub mod mina;

/// Binius backend: binary field tower proof system using Groestl-256 hashing.
///
/// Always compiled (stub mode without the `binius` feature flag). When the `binius`
/// feature is enabled, provides full proof generation and verification using the
/// Binius binary tower library from IrreducibleOSS.
///
/// The stub mode validates circuit logic and produces structurally-correct proofs
/// that demonstrate the expected API and proof sizes.
pub mod binius;

/// Unified trait for proof backends.
///
/// Implementors provide both membership proofs (leaf in tree) and fold-step
/// proofs (IVC accumulation of attenuation steps).
pub trait ProofBackend: Send + Sync {
    /// The proof type produced by this backend.
    type Proof: serde::Serialize + for<'de> serde::Deserialize<'de>;

    /// Prove that `leaf` is a member of a Merkle tree with given `root`,
    /// where `siblings` contains the sibling hashes at each level.
    ///
    /// Each element in `siblings` is a vector of sibling hashes at that level
    /// (for a 4-ary tree, each level has 3 siblings).
    fn prove_membership(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        root: &[u8; 32],
    ) -> Result<Self::Proof, String>;

    /// Verify a membership proof against a given root.
    fn verify_membership(proof: &Self::Proof, root: &[u8; 32]) -> Result<bool, String>;

    /// Prove a single fold step: transition from `old_root` to `new_root`
    /// by removing the specified facts (whose hashes are in `removals`).
    ///
    /// This is the building block for IVC: each fold step removes capabilities
    /// from the token's fact set.
    fn prove_fold_step(
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        removals: &[[u8; 32]],
    ) -> Result<Self::Proof, String>;

    /// Verify a fold proof.
    fn verify_fold(proof: &Self::Proof) -> Result<bool, String>;

    /// Get the serialized size of a proof in bytes.
    fn proof_size(proof: &Self::Proof) -> usize;

    /// The human-readable name of this backend.
    fn backend_name() -> &'static str;
}
