//! Homomorphic value commitments (Pedersen commitments over Ristretto).
//!
//! # Construction
//!
//! A Pedersen commitment hides an amount `v` with blinding factor `r`:
//!
//! ```text
//! commit(v, r) = v * V + r * R
//! ```
//!
//! where `V` and `R` are independent generators of the Ristretto group with
//! unknown discrete log relation (derived via hash-to-point).
//!
//! # Properties
//!
//! - **Hiding**: without knowing `r`, the commitment reveals nothing about `v`.
//! - **Binding**: given `commit(v, r)`, the committer cannot open to `(v', r')` with `v' != v`
//!   (under the discrete log assumption).
//! - **Homomorphic**: `commit(a, r1) + commit(b, r2) = commit(a+b, r1+r2)`.
//!   This lets the executor verify conservation without learning individual amounts.
//!
//! # Conservation proof
//!
//! If `sum(input_commitments) - sum(output_commitments) = excess`, then the values
//! balance iff `excess` is a commitment to zero: `excess = 0*V + r_excess*R`.
//!
//! A Schnorr signature proving knowledge of `r_excess` (the "excess blinding factor")
//! ensures the transactor actually knows the values balance — no inflation is possible.
//!
//! # Range proofs (interface only)
//!
//! To prevent negative values (which would allow hidden inflation), each commitment
//! must be accompanied by a range proof showing `v in [0, 2^64)`. Two strategies:
//!
//! - **Bulletproofs**: native to the Ristretto group, logarithmic proof size, aggregatable.
//!   Use the `bulletproofs` crate (same curve). Pros: small proofs (~700 bytes for 64-bit).
//!   Cons: verification is somewhat slow; not STARK-native.
//!
//! - **STARK-based decomposition**: Prove `v = sum(b_i * 2^i)` for `b_i in {0,1}` inside
//!   the existing Plonky3 STARK. Pros: free to batch with other STARK proofs; STARK-native.
//!   Cons: larger proof; requires embedding the Ristretto scalar field relationship.
//!
//! The recommended path: use Bulletproofs for the standalone privacy layer, and migrate
//! to STARK-based decomposition once the circuit integration is mature.
//!
//! # Executor integration (planned, NOT yet implemented)
//!
//! The executor currently enforces conservation in cleartext:
//! ```text
//! sum(input_values) == sum(output_values)  [per asset type]
//! ```
//!
//! With value commitments, this becomes:
//! ```text
//! sum(input_commitments) - sum(output_commitments) == excess_commitment
//! AND verify_schnorr(excess_commitment, excess_signature)
//! ```
//!
//! The executor never learns the actual amounts — it only verifies the algebraic
//! relation and the binding signature. The `NoteSpend` and `NoteCreate` effects
//! would carry `ValueCommitment` instead of (or alongside) cleartext `value` fields.
//!
//! Per-asset-type conservation requires asset-type-specific generators:
//! `V_asset = hash_to_point("dregg-value-generator", asset_type_bytes)`.
//! This prevents cross-asset conservation attacks (committing to asset A on one side
//! and asset B on the other).

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use serde::{Deserialize, Serialize};
use std::ops::{Add, Neg, Sub};

// ─── Generators ───────────────────────────────────────────────────────────────

/// Derive a Ristretto generator from a domain-separation tag.
///
/// Uses BLAKE3 in XOF mode to produce 64 uniform bytes, then maps to Ristretto
/// via `from_uniform_bytes` (Elligator2 map — guaranteed to produce a valid point
/// with no cofactor issues).
fn hash_to_generator(domain: &[u8]) -> RistrettoPoint {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-pedersen generator v1");
    hasher.update(domain);
    let mut xof = hasher.finalize_xof();
    let mut uniform = [0u8; 64];
    xof.fill(&mut uniform);
    RistrettoPoint::from_uniform_bytes(&uniform)
}

/// Value generator `V`: the base point for the committed amount.
/// `V = hash_to_point("dregg-value-generator")`.
pub fn value_generator() -> RistrettoPoint {
    hash_to_generator(b"dregg-value-generator")
}

/// Randomness generator `R`: the base point for the blinding factor.
/// `R = hash_to_point("dregg-randomness-generator")`.
///
/// The discrete log relationship between V and R is unknown by construction
/// (random oracle model on BLAKE3).
pub fn randomness_generator() -> RistrettoPoint {
    hash_to_generator(b"dregg-randomness-generator")
}

/// Asset-type-specific value generator: `V_asset = hash_to_point("dregg-value-generator", asset_type_le_bytes)`.
///
/// Using different generators per asset type prevents cross-asset conservation attacks.
/// An attacker cannot forge `commit(v, r) on V_a == commit(v', r') on V_b` because
/// the discrete log between V_a and V_b is unknown.
pub fn asset_value_generator(asset_type: u64) -> RistrettoPoint {
    let mut domain = b"dregg-value-generator:".to_vec();
    domain.extend_from_slice(&asset_type.to_le_bytes());
    hash_to_generator(&domain)
}

// ─── ValueCommitment ──────────────────────────────────────────────────────────

/// A Pedersen commitment to a value: `commitment = v * V + r * R`.
///
/// Stored in compressed form (32 bytes) for serialization; decompressed for arithmetic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueCommitment {
    /// The commitment point (v*V + r*R).
    pub point: RistrettoPoint,
}

/// Serializable form of a ValueCommitment (32-byte compressed Ristretto encoding).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValueCommitmentBytes(pub [u8; 32]);

impl ValueCommitment {
    /// Create a commitment to `value` with blinding factor `blinding`.
    ///
    /// Uses the default (non-asset-specific) generators.
    /// For multi-asset scenarios, use `commit_with_asset`.
    pub fn commit(value: u64, blinding: &Scalar) -> Self {
        let v = Scalar::from(value);
        let point = v * value_generator() + blinding * randomness_generator();
        Self { point }
    }

    /// Create a commitment using an asset-type-specific value generator.
    ///
    /// ```text
    /// commitment = value * V_asset + blinding * R
    /// ```
    ///
    /// Different asset types use different V generators, preventing cross-asset attacks.
    pub fn commit_with_asset(value: u64, blinding: &Scalar, asset_type: u64) -> Self {
        let v = Scalar::from(value);
        let point = v * asset_value_generator(asset_type) + blinding * randomness_generator();
        Self { point }
    }

    /// Commitment to zero with a given blinding factor: `0*V + r*R = r*R`.
    pub fn commit_zero(blinding: &Scalar) -> Self {
        let point = blinding * randomness_generator();
        Self { point }
    }

    /// The identity commitment (point at infinity). Useful as the neutral element
    /// when summing commitments.
    pub fn identity() -> Self {
        Self {
            point: RistrettoPoint::identity(),
        }
    }

    /// Compress to 32 bytes for serialization/storage.
    pub fn to_bytes(&self) -> ValueCommitmentBytes {
        ValueCommitmentBytes(self.point.compress().to_bytes())
    }

    /// Decompress from 32 bytes. Returns None if the bytes are not a valid Ristretto point.
    pub fn from_bytes(bytes: &ValueCommitmentBytes) -> Option<Self> {
        let compressed = CompressedRistretto::from_slice(&bytes.0).ok()?;
        compressed.decompress().map(|point| Self { point })
    }
}

// ─── Byte-friendly helpers (for FFI / wasm marshalling) ──────────────────────
//
// These keep the curve25519-dalek `Scalar`/`RistrettoPoint` work inside the
// `cell` crate so that callers (e.g. the wasm bindings) only ever marshal
// `[u8; 32]` arrays across the FFI boundary and never need a direct
// curve25519-dalek dependency.

/// Interpret 32 little-endian bytes as a Ristretto `Scalar` (reduced mod the
/// group order). Always succeeds — non-canonical encodings are reduced rather
/// than rejected, which is exactly what we want for a freshly-generated random
/// blinding factor handed in as raw bytes.
pub fn scalar_from_blinding_bytes(blinding: &[u8; 32]) -> Scalar {
    Scalar::from_bytes_mod_order(*blinding)
}

/// Create a Pedersen value commitment from a value and 32 raw blinding bytes,
/// returning the 32-byte compressed Ristretto encoding.
///
/// `commit_bytes(value, blinding) = (value * V + scalar(blinding) * R).compress()`
///
/// This is the byte-in / byte-out form of [`ValueCommitment::commit`]: the
/// blinding bytes are reduced mod the group order via
/// [`scalar_from_blinding_bytes`] and the resulting point is returned in the
/// canonical 32-byte compressed Ristretto encoding (the same bytes
/// [`ValueCommitment::to_bytes`] produces).
pub fn commit_bytes(value: u64, blinding: &[u8; 32]) -> [u8; 32] {
    let scalar = scalar_from_blinding_bytes(blinding);
    ValueCommitment::commit(value, &scalar).to_bytes().0
}

/// Result of [`prove_conservation_bytes`]: all fields are 32-byte compressed
/// Ristretto / scalar encodings, ready to hand across an FFI boundary as hex.
#[derive(Clone, Debug)]
pub struct ConservationProofBytes {
    /// Compressed Ristretto encoding of each input value commitment, in order.
    pub input_commitments: Vec<[u8; 32]>,
    /// Compressed Ristretto encoding of each output value commitment, in order.
    pub output_commitments: Vec<[u8; 32]>,
    /// The canonical Schnorr conservation proof (excess / nonce / response).
    pub proof: ConservationProof,
}

/// Build value commitments for a balanced transaction and produce the canonical
/// Schnorr conservation proof — all in terms of raw bytes.
///
/// Each input/output is `(value, blinding_bytes)`. The excess blinding factor
/// is computed internally as `Σ input_blindings − Σ output_blindings`, so the
/// caller does not need to touch a `Scalar`. The returned commitments and proof
/// are exactly what [`verify_conservation`] (and the wasm
/// `verify_conservation_proof` binding) consume.
///
/// This is the prove-side counterpart to the byte-in verifier: it lets a wasm
/// caller produce a real generate→verify roundtrip without depending on
/// curve25519-dalek directly.
pub fn prove_conservation_bytes(
    inputs: &[(u64, [u8; 32])],
    outputs: &[(u64, [u8; 32])],
    message: &[u8],
) -> ConservationProofBytes {
    let input_commitments: Vec<ValueCommitment> = inputs
        .iter()
        .map(|(v, b)| ValueCommitment::commit(*v, &scalar_from_blinding_bytes(b)))
        .collect();
    let output_commitments: Vec<ValueCommitment> = outputs
        .iter()
        .map(|(v, b)| ValueCommitment::commit(*v, &scalar_from_blinding_bytes(b)))
        .collect();

    // excess_blinding = Σ input_blindings − Σ output_blindings.
    let sum_in = inputs
        .iter()
        .fold(Scalar::ZERO, |acc, (_, b)| acc + scalar_from_blinding_bytes(b));
    let sum_out = outputs
        .iter()
        .fold(Scalar::ZERO, |acc, (_, b)| acc + scalar_from_blinding_bytes(b));
    let excess_blinding = sum_in - sum_out;

    let proof = prove_conservation(
        &input_commitments,
        &output_commitments,
        &excess_blinding,
        message,
    );

    ConservationProofBytes {
        input_commitments: input_commitments.iter().map(|c| c.to_bytes().0).collect(),
        output_commitments: output_commitments.iter().map(|c| c.to_bytes().0).collect(),
        proof,
    }
}

impl Add for ValueCommitment {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self {
            point: self.point + rhs.point,
        }
    }
}

impl<'a> Add<&'a ValueCommitment> for &'a ValueCommitment {
    type Output = ValueCommitment;
    fn add(self, rhs: &'a ValueCommitment) -> ValueCommitment {
        ValueCommitment {
            point: self.point + rhs.point,
        }
    }
}

impl Sub for ValueCommitment {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self {
            point: self.point - rhs.point,
        }
    }
}

impl<'a> Sub<&'a ValueCommitment> for &'a ValueCommitment {
    type Output = ValueCommitment;
    fn sub(self, rhs: &'a ValueCommitment) -> ValueCommitment {
        ValueCommitment {
            point: self.point - rhs.point,
        }
    }
}

impl Neg for ValueCommitment {
    type Output = Self;
    fn neg(self) -> Self {
        Self { point: -self.point }
    }
}

// ─── CommittedNote ────────────────────────────────────────────────────────────

/// A note whose value is hidden behind a Pedersen commitment.
///
/// This is the privacy-preserving analog of `Note` from `note.rs`. The amount
/// is replaced by a `ValueCommitment`, so the executor and other observers
/// cannot see how much is being transferred.
///
/// The holder retains the opening (value, blinding) as private witness data.
#[derive(Clone, Debug)]
pub struct CommittedNote {
    /// Asset type identifier (still public — asset type privacy requires additional work).
    pub asset_type: u64,
    /// Pedersen commitment hiding the amount: `value * V_asset + blinding * R`.
    pub value_commitment: ValueCommitment,
    /// Note commitment: `H(owner || value_commitment || asset_type || creation_nonce || rcm)`.
    /// This is what goes into the note tree.
    pub note_commitment: [u8; 32],
}

/// The private opening data that the note holder retains.
/// This is NEVER published — only used to construct proofs.
#[derive(Clone, Debug)]
pub struct CommittedNoteOpening {
    /// The plaintext amount.
    pub value: u64,
    /// The blinding factor used in the value commitment.
    pub blinding: Scalar,
    /// The owner's public key.
    pub owner: [u8; 32],
    /// Asset type identifier.
    pub asset_type: u64,
    /// Randomness for the note commitment (analogous to `Note::randomness`).
    pub note_randomness: [u8; 32],
    /// Creation nonce (analogous to `Note::creation_nonce`).
    pub creation_nonce: [u8; 32],
}

impl CommittedNote {
    /// Create a committed note from its opening data.
    ///
    /// Computes the value commitment and note commitment from the private opening.
    pub fn from_opening(opening: &CommittedNoteOpening) -> Self {
        let value_commitment = ValueCommitment::commit_with_asset(
            opening.value,
            &opening.blinding,
            opening.asset_type,
        );
        let note_commitment = Self::compute_note_commitment(
            &opening.owner,
            &value_commitment,
            opening.asset_type,
            &opening.creation_nonce,
            &opening.note_randomness,
        );
        Self {
            asset_type: opening.asset_type,
            value_commitment,
            note_commitment,
        }
    }

    /// Compute the note commitment hash.
    ///
    /// ```text
    /// H("dregg-committed-note v1", owner || value_commitment_bytes || asset_type_le || creation_nonce || rcm)
    /// ```
    fn compute_note_commitment(
        owner: &[u8; 32],
        value_commitment: &ValueCommitment,
        asset_type: u64,
        creation_nonce: &[u8; 32],
        note_randomness: &[u8; 32],
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-committed-note v1");
        hasher.update(owner);
        hasher.update(&value_commitment.to_bytes().0);
        hasher.update(&asset_type.to_le_bytes());
        hasher.update(creation_nonce);
        hasher.update(note_randomness);
        *hasher.finalize().as_bytes()
    }
}

impl CommittedNoteOpening {
    /// Create a new opening with all required data.
    pub fn new(
        owner: [u8; 32],
        value: u64,
        asset_type: u64,
        blinding: Scalar,
        note_randomness: [u8; 32],
        creation_nonce: [u8; 32],
    ) -> Self {
        Self {
            value,
            blinding,
            owner,
            asset_type,
            note_randomness,
            creation_nonce,
        }
    }
}

// ─── Conservation Proof ───────────────────────────────────────────────────────

/// A proof that inputs and outputs conserve value (no inflation/deflation).
///
/// The proof is a Schnorr signature proving knowledge of the excess blinding factor:
/// ```text
/// excess_point = sum(input_commitments) - sum(output_commitments)
///              = (sum_v_in - sum_v_out) * V + (sum_r_in - sum_r_out) * R
/// ```
///
/// If values balance (`sum_v_in == sum_v_out`), then:
/// ```text
/// excess_point = 0 * V + r_excess * R = r_excess * R
/// ```
///
/// The Schnorr signature proves the signer knows `r_excess` with respect to
/// generator `R`, which implies `excess_point` has no `V`-component (i.e., values balance).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConservationProof {
    /// The excess point (compressed): sum(inputs) - sum(outputs).
    pub excess_commitment: [u8; 32],
    /// Schnorr signature: nonce commitment `k*R` (compressed).
    pub nonce_commitment: [u8; 32],
    /// Schnorr signature: response scalar `s = k + e * r_excess`.
    pub response: [u8; 32],
}

/// Compute the Schnorr challenge for the conservation proof.
///
/// ```text
/// e = H("dregg-conservation-challenge v1", R_nonce || excess_point || message)
/// ```
fn schnorr_challenge(
    nonce_point: &RistrettoPoint,
    excess_point: &RistrettoPoint,
    message: &[u8],
) -> Scalar {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-conservation-challenge v1");
    hasher.update(&nonce_point.compress().to_bytes());
    hasher.update(&excess_point.compress().to_bytes());
    hasher.update(message);
    let hash = hasher.finalize();
    // Reduce hash to scalar (interpret 32 bytes as little-endian integer mod l).
    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(hash.as_bytes());
    Scalar::from_bytes_mod_order_wide(&wide)
}

/// Prove that value is conserved across a transaction.
///
/// # Arguments
///
/// - `input_commitments`: value commitments from spent notes
/// - `output_commitments`: value commitments from created notes
/// - `excess_blinding`: `sum(input_blindings) - sum(output_blindings)` — the prover
///   must know this value (it's derived from the transaction's private data)
/// - `message`: optional binding context (e.g., transaction hash) to prevent replay
///
/// # Panics
///
/// Panics if `getrandom` fails (should not happen on supported platforms).
pub fn prove_conservation(
    input_commitments: &[ValueCommitment],
    output_commitments: &[ValueCommitment],
    excess_blinding: &Scalar,
    message: &[u8],
) -> ConservationProof {
    // Compute excess point: sum(inputs) - sum(outputs).
    let sum_inputs = input_commitments
        .iter()
        .fold(RistrettoPoint::identity(), |acc, c| acc + c.point);
    let sum_outputs = output_commitments
        .iter()
        .fold(RistrettoPoint::identity(), |acc, c| acc + c.point);
    let excess_point = sum_inputs - sum_outputs;

    // Generate random nonce for Schnorr signature.
    let mut nonce_bytes = [0u8; 64];
    getrandom::fill(&mut nonce_bytes).expect("getrandom failed");
    let k = Scalar::from_bytes_mod_order_wide(&nonce_bytes);

    // Nonce commitment: k * R.
    let r_gen = randomness_generator();
    let nonce_point = k * r_gen;

    // Challenge.
    let e = schnorr_challenge(&nonce_point, &excess_point, message);

    // Response: s = k + e * r_excess.
    let s = k + e * excess_blinding;

    ConservationProof {
        excess_commitment: excess_point.compress().to_bytes(),
        nonce_commitment: nonce_point.compress().to_bytes(),
        response: s.to_bytes(),
    }
}

/// Verify a conservation proof.
///
/// Checks:
/// 1. The excess point matches `sum(input_commitments) - sum(output_commitments)`
/// 2. The Schnorr signature is valid (proving the excess is a commitment to zero value)
///
/// # Returns
///
/// `Ok(())` if conservation is proven, `Err(ConservationError)` otherwise.
pub fn verify_conservation(
    input_commitments: &[ValueCommitment],
    output_commitments: &[ValueCommitment],
    proof: &ConservationProof,
    message: &[u8],
) -> Result<(), ConservationError> {
    // Recompute excess point.
    let sum_inputs = input_commitments
        .iter()
        .fold(RistrettoPoint::identity(), |acc, c| acc + c.point);
    let sum_outputs = output_commitments
        .iter()
        .fold(RistrettoPoint::identity(), |acc, c| acc + c.point);
    let expected_excess = sum_inputs - sum_outputs;

    // Decompress excess from proof.
    let excess_compressed = CompressedRistretto::from_slice(&proof.excess_commitment)
        .map_err(|_| ConservationError::InvalidExcessPoint)?;
    let excess_point = excess_compressed
        .decompress()
        .ok_or(ConservationError::InvalidExcessPoint)?;

    // Verify excess matches recomputed value.
    if excess_point != expected_excess {
        return Err(ConservationError::ExcessMismatch);
    }

    // Decompress nonce commitment.
    let nonce_compressed = CompressedRistretto::from_slice(&proof.nonce_commitment)
        .map_err(|_| ConservationError::InvalidNoncePoint)?;
    let nonce_point = nonce_compressed
        .decompress()
        .ok_or(ConservationError::InvalidNoncePoint)?;

    // Recompute challenge.
    let e = schnorr_challenge(&nonce_point, &excess_point, message);

    // Verify: s * R == nonce_point + e * excess_point.
    let s_ct = Scalar::from_canonical_bytes(proof.response);
    let s: Scalar = if s_ct.is_some().into() {
        s_ct.unwrap()
    } else {
        return Err(ConservationError::InvalidResponse);
    };

    let r_gen = randomness_generator();
    let lhs = s * r_gen;
    let rhs = nonce_point + e * excess_point;

    if lhs == rhs {
        Ok(())
    } else {
        Err(ConservationError::SignatureInvalid)
    }
}

/// Errors from conservation proof verification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConservationError {
    /// The excess commitment bytes are not a valid Ristretto point.
    InvalidExcessPoint,
    /// The excess point does not match the recomputed sum(inputs) - sum(outputs).
    ExcessMismatch,
    /// The nonce commitment bytes are not a valid Ristretto point.
    InvalidNoncePoint,
    /// The response scalar is not canonical (not in [0, l)).
    InvalidResponse,
    /// The Schnorr signature does not verify — values do NOT balance.
    SignatureInvalid,
}

impl core::fmt::Display for ConservationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidExcessPoint => write!(f, "invalid excess commitment point"),
            Self::ExcessMismatch => {
                write!(f, "excess point does not match commitment sum difference")
            }
            Self::InvalidNoncePoint => write!(f, "invalid nonce commitment point"),
            Self::InvalidResponse => write!(f, "response scalar is not canonical"),
            Self::SignatureInvalid => {
                write!(f, "conservation signature invalid: values do not balance")
            }
        }
    }
}

impl std::error::Error for ConservationError {}

// ─── Range proofs (Bulletproofs) ─────────────────────────────────────────────

/// A range proof attesting that a committed value is in `[0, 2^64)`.
///
/// This is an interface trait. The concrete implementation (`BulletproofRangeProof`)
/// uses the `bulletproofs` crate (dalek ecosystem, native to Ristretto).
///
/// Future backends (e.g., STARK-based bit decomposition) can also implement this trait.
pub trait RangeProofTrait: Sized {
    /// Prove that the value committed in `commitment` is in [0, 2^64).
    ///
    /// The prover needs the opening (value, blinding) to construct the proof.
    fn prove(value: u64, blinding: &Scalar, commitment: &ValueCommitment) -> Self;

    /// Verify that the committed value is in [0, 2^64).
    fn verify(&self, commitment: &ValueCommitment) -> Result<(), RangeProofError>;

    /// Batch-verify multiple range proofs (amortized cost).
    fn batch_verify(
        proofs: &[Self],
        commitments: &[ValueCommitment],
    ) -> Result<(), RangeProofError>;
}

/// Errors from range proof verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RangeProofError {
    /// The proof is malformed.
    Malformed,
    /// The proof does not verify — the value may be negative or >= 2^64.
    VerificationFailed,
    /// Batch length mismatch between proofs and commitments.
    LengthMismatch,
}

impl core::fmt::Display for RangeProofError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Malformed => write!(f, "range proof is malformed"),
            Self::VerificationFailed => write!(f, "range proof verification failed"),
            Self::LengthMismatch => write!(
                f,
                "batch verify: proofs and commitments have different lengths"
            ),
        }
    }
}

impl std::error::Error for RangeProofError {}

// ─── Bulletproof range proof implementation ──────────────────────────────────

use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;

/// Pedersen generators configured to match our value commitment scheme.
///
/// Bulletproofs needs `PedersenGens { B: value_generator, B_blinding: randomness_generator }`
/// so that the commitment `v*B + r*B_blinding` matches our `ValueCommitment::commit`.
fn pedersen_gens() -> PedersenGens {
    PedersenGens {
        B: value_generator(),
        B_blinding: randomness_generator(),
    }
}

/// Bulletproof generators for 64-bit range proofs (single value).
///
/// These are expensive to construct, so callers doing many proofs may want to
/// cache this. For the trait implementation we construct on each call (correctness
/// over performance — this is not on the hot path for transaction validation in
/// production; batch APIs amortize the cost).
fn bulletproof_gens() -> BulletproofGens {
    BulletproofGens::new(64, 1)
}

/// Concrete range proof using the Bulletproofs protocol (logarithmic size, ~672 bytes for 64-bit).
///
/// Wraps a serialized `bulletproofs::RangeProof` so the struct is `Clone + Serialize + Deserialize`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BulletproofRangeProof {
    /// Serialized bulletproof bytes (variable length, typically ~672 bytes for 64-bit).
    pub proof_bytes: Vec<u8>,
}

impl BulletproofRangeProof {
    /// Create a fresh Fiat-Shamir transcript for range proof domain separation.
    fn transcript() -> Transcript {
        Transcript::new(b"dregg-range-proof v1")
    }

    /// Prove that `value` is in `[0, 2^64)` given the blinding factor.
    ///
    /// Returns the range proof. The caller should have already constructed
    /// `commitment = ValueCommitment::commit(value, blinding)`.
    pub fn prove_range(value: u64, blinding: &Scalar) -> Self {
        let bp_gens = bulletproof_gens();
        let pc_gens = pedersen_gens();
        let mut transcript = Self::transcript();

        let (proof, _committed_value) = bulletproofs::RangeProof::prove_single(
            &bp_gens,
            &pc_gens,
            &mut transcript,
            value,
            blinding,
            64,
        )
        .expect("range proof creation should not fail for valid 64-bit value");

        Self {
            proof_bytes: proof.to_bytes(),
        }
    }

    /// Verify that the commitment contains a value in `[0, 2^64)`.
    pub fn verify_range(&self, commitment: &ValueCommitment) -> Result<(), RangeProofError> {
        let bp_gens = bulletproof_gens();
        let pc_gens = pedersen_gens();
        let mut transcript = Self::transcript();

        let proof = bulletproofs::RangeProof::from_bytes(&self.proof_bytes)
            .map_err(|_| RangeProofError::Malformed)?;

        let compressed = commitment.point.compress();
        proof
            .verify_single(&bp_gens, &pc_gens, &mut transcript, &compressed, 64)
            .map_err(|_| RangeProofError::VerificationFailed)
    }
}

impl RangeProofTrait for BulletproofRangeProof {
    fn prove(value: u64, blinding: &Scalar, _commitment: &ValueCommitment) -> Self {
        Self::prove_range(value, blinding)
    }

    fn verify(&self, commitment: &ValueCommitment) -> Result<(), RangeProofError> {
        self.verify_range(commitment)
    }

    fn batch_verify(
        proofs: &[Self],
        commitments: &[ValueCommitment],
    ) -> Result<(), RangeProofError> {
        if proofs.len() != commitments.len() {
            return Err(RangeProofError::LengthMismatch);
        }
        // Bulletproofs batch verification: verify each individually.
        // (The bulletproofs crate supports batch verification via verify_multiple,
        // but that requires all proofs to be aggregated together at proof time.
        // For independently-created proofs, we verify each one.)
        for (proof, commitment) in proofs.iter().zip(commitments.iter()) {
            proof.verify(commitment)?;
        }
        Ok(())
    }
}

// ─── Conservation proof with range proofs ────────────────────────────────────

/// A full conservation proof that includes:
/// 1. A Schnorr excess signature proving inputs and outputs balance.
/// 2. Range proofs for each output commitment, preventing negative values.
///
/// Without range proofs, a malicious transactor could commit to a negative value
/// (wrapping in the scalar field) on one output and inflate another output,
/// while still satisfying the conservation equation. Range proofs close this attack
/// by ensuring every output value is in `[0, 2^64)`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FullConservationProof {
    /// The Schnorr-based conservation proof (excess signature).
    pub conservation: ConservationProof,
    /// One range proof per output commitment, in the same order as `output_commitments`.
    pub output_range_proofs: Vec<BulletproofRangeProof>,
}

/// Prove conservation with range proofs for all outputs.
///
/// # Arguments
///
/// - `input_commitments`: value commitments from spent notes
/// - `output_commitments`: value commitments from created notes
/// - `output_values`: plaintext values for each output (needed to construct range proofs)
/// - `output_blindings`: blinding factors for each output commitment
/// - `excess_blinding`: `sum(input_blindings) - sum(output_blindings)`
/// - `message`: binding context (e.g., transaction hash)
///
/// # Panics
///
/// Panics if `output_values.len() != output_commitments.len()` or
/// `output_blindings.len() != output_commitments.len()`.
pub fn prove_conservation_with_range(
    input_commitments: &[ValueCommitment],
    output_commitments: &[ValueCommitment],
    output_values: &[u64],
    output_blindings: &[Scalar],
    excess_blinding: &Scalar,
    message: &[u8],
) -> FullConservationProof {
    assert_eq!(output_values.len(), output_commitments.len());
    assert_eq!(output_blindings.len(), output_commitments.len());

    let conservation = prove_conservation(
        input_commitments,
        output_commitments,
        excess_blinding,
        message,
    );

    let output_range_proofs = output_values
        .iter()
        .zip(output_blindings.iter())
        .map(|(&value, blinding)| BulletproofRangeProof::prove_range(value, blinding))
        .collect();

    FullConservationProof {
        conservation,
        output_range_proofs,
    }
}

/// Verify a full conservation proof (Schnorr excess + output range proofs).
///
/// Checks:
/// 1. The Schnorr excess signature is valid (values balance).
/// 2. Every output commitment has a valid range proof (no negative values).
///
/// # Returns
///
/// `Ok(())` if conservation is proven and all outputs are in range.
/// `Err(FullConservationError)` otherwise.
pub fn verify_conservation_with_range(
    input_commitments: &[ValueCommitment],
    output_commitments: &[ValueCommitment],
    proof: &FullConservationProof,
    message: &[u8],
) -> Result<(), FullConservationError> {
    // Step 1: Verify the Schnorr conservation proof.
    verify_conservation(
        input_commitments,
        output_commitments,
        &proof.conservation,
        message,
    )
    .map_err(FullConservationError::Conservation)?;

    // Step 2: Verify range proofs for each output.
    if proof.output_range_proofs.len() != output_commitments.len() {
        return Err(FullConservationError::RangeProofCountMismatch {
            expected: output_commitments.len(),
            got: proof.output_range_proofs.len(),
        });
    }

    for (i, (range_proof, commitment)) in proof
        .output_range_proofs
        .iter()
        .zip(output_commitments.iter())
        .enumerate()
    {
        range_proof.verify_range(commitment).map_err(|e| {
            FullConservationError::RangeProofFailed {
                output_index: i,
                source: e,
            }
        })?;
    }

    Ok(())
}

/// Errors from full conservation proof verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FullConservationError {
    /// The Schnorr conservation proof failed.
    Conservation(ConservationError),
    /// Wrong number of range proofs relative to output commitments.
    RangeProofCountMismatch { expected: usize, got: usize },
    /// A specific output's range proof failed verification.
    RangeProofFailed {
        output_index: usize,
        source: RangeProofError,
    },
}

impl core::fmt::Display for FullConservationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Conservation(e) => write!(f, "conservation proof failed: {}", e),
            Self::RangeProofCountMismatch { expected, got } => {
                write!(
                    f,
                    "range proof count mismatch: expected {} but got {}",
                    expected, got
                )
            }
            Self::RangeProofFailed {
                output_index,
                source,
            } => {
                write!(
                    f,
                    "range proof failed for output {}: {}",
                    output_index, source
                )
            }
        }
    }
}

impl std::error::Error for FullConservationError {}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;

    /// Helper: deterministic scalar from a seed byte.
    fn test_scalar(seed: u8) -> Scalar {
        let mut bytes = [0u8; 64];
        bytes[0] = seed;
        bytes[1] = seed.wrapping_mul(37);
        Scalar::from_bytes_mod_order_wide(&bytes)
    }

    #[test]
    fn generators_are_distinct() {
        let v = value_generator();
        let r = randomness_generator();
        assert_ne!(v, r);
        // Neither should be the standard basepoint (extremely unlikely, but check).
        assert_ne!(v, RISTRETTO_BASEPOINT_POINT);
        assert_ne!(r, RISTRETTO_BASEPOINT_POINT);
    }

    #[test]
    fn generators_are_deterministic() {
        assert_eq!(value_generator(), value_generator());
        assert_eq!(randomness_generator(), randomness_generator());
    }

    #[test]
    fn asset_generators_differ_by_type() {
        let g1 = asset_value_generator(1);
        let g2 = asset_value_generator(2);
        assert_ne!(g1, g2);
        // Same asset type always produces same generator.
        assert_eq!(asset_value_generator(42), asset_value_generator(42));
    }

    #[test]
    fn commitment_hiding() {
        // Same value with different blinding produces different commitments.
        let r1 = test_scalar(1);
        let r2 = test_scalar(2);
        let c1 = ValueCommitment::commit(100, &r1);
        let c2 = ValueCommitment::commit(100, &r2);
        assert_ne!(c1.point, c2.point);
    }

    #[test]
    fn commitment_binding() {
        // Different values with same blinding produce different commitments.
        let r = test_scalar(1);
        let c1 = ValueCommitment::commit(100, &r);
        let c2 = ValueCommitment::commit(200, &r);
        assert_ne!(c1.point, c2.point);
    }

    #[test]
    fn commitment_homomorphic_addition() {
        let r1 = test_scalar(1);
        let r2 = test_scalar(2);

        let c1 = ValueCommitment::commit(300, &r1);
        let c2 = ValueCommitment::commit(500, &r2);

        // c1 + c2 should equal commit(300+500, r1+r2).
        let sum = &c1 + &c2;
        let expected = ValueCommitment::commit(800, &(r1 + r2));
        assert_eq!(sum.point, expected.point);
    }

    #[test]
    fn commitment_homomorphic_subtraction() {
        let r1 = test_scalar(3);
        let r2 = test_scalar(4);

        let c1 = ValueCommitment::commit(1000, &r1);
        let c2 = ValueCommitment::commit(400, &r2);

        // c1 - c2 should equal commit(600, r1-r2).
        let diff = &c1 - &c2;
        let expected = ValueCommitment::commit(600, &(r1 - r2));
        assert_eq!(diff.point, expected.point);
    }

    #[test]
    fn commitment_zero_value() {
        let r = test_scalar(5);
        let c = ValueCommitment::commit_zero(&r);
        let expected = ValueCommitment::commit(0, &r);
        assert_eq!(c.point, expected.point);
    }

    #[test]
    fn commitment_serialization_roundtrip() {
        let r = test_scalar(6);
        let c = ValueCommitment::commit(42, &r);
        let bytes = c.to_bytes();
        let recovered = ValueCommitment::from_bytes(&bytes).expect("decompression failed");
        assert_eq!(c.point, recovered.point);
    }

    #[test]
    fn commitment_invalid_bytes_rejected() {
        // All-zero is not a valid compressed Ristretto point (except identity).
        // Actually the identity IS all-zeros in compressed form. Use something invalid:
        let bad_bytes = ValueCommitmentBytes([0xFF; 32]);
        assert!(ValueCommitment::from_bytes(&bad_bytes).is_none());
    }

    #[test]
    fn conservation_proof_valid_transaction() {
        // Transaction: 2 inputs (300, 500) -> 2 outputs (450, 350).
        // Total: 800 = 800. Conservation holds.
        let r_in1 = test_scalar(10);
        let r_in2 = test_scalar(11);
        let r_out1 = test_scalar(12);
        let r_out2 = test_scalar(13);

        let inputs = vec![
            ValueCommitment::commit(300, &r_in1),
            ValueCommitment::commit(500, &r_in2),
        ];
        let outputs = vec![
            ValueCommitment::commit(450, &r_out1),
            ValueCommitment::commit(350, &r_out2),
        ];

        // Excess blinding = sum(input_r) - sum(output_r).
        let excess_blinding = (r_in1 + r_in2) - (r_out1 + r_out2);

        let proof = prove_conservation(&inputs, &outputs, &excess_blinding, b"test-tx-1");

        assert!(verify_conservation(&inputs, &outputs, &proof, b"test-tx-1").is_ok());
    }

    #[test]
    fn conservation_proof_invalid_blinding_rejected() {
        // Use wrong excess blinding — signature should fail.
        let r_in = test_scalar(20);
        let r_out = test_scalar(21);

        let inputs = vec![ValueCommitment::commit(100, &r_in)];
        let outputs = vec![ValueCommitment::commit(100, &r_out)];

        // Correct excess would be r_in - r_out, but we use a wrong value.
        let wrong_excess = test_scalar(99);

        let proof = prove_conservation(&inputs, &outputs, &wrong_excess, b"test-tx-2");

        assert_eq!(
            verify_conservation(&inputs, &outputs, &proof, b"test-tx-2"),
            Err(ConservationError::SignatureInvalid)
        );
    }

    #[test]
    fn conservation_proof_imbalanced_values_rejected() {
        // Inputs: 100. Outputs: 200. Values don't balance.
        // Even if we somehow produce a "proof", verification should fail
        // because the excess point has a V-component.
        let r_in = test_scalar(30);
        let r_out = test_scalar(31);

        let inputs = vec![ValueCommitment::commit(100, &r_in)];
        let outputs = vec![ValueCommitment::commit(200, &r_out)];

        // The "honest" excess blinding for the blinding factors:
        let blinding_diff = r_in - r_out;

        // This proof will fail because excess = -100*V + blinding_diff*R,
        // and the Schnorr signature proves knowledge of blinding_diff w.r.t. R,
        // but excess != blinding_diff * R (it has a V component).
        let proof = prove_conservation(&inputs, &outputs, &blinding_diff, b"test-tx-3");

        assert_eq!(
            verify_conservation(&inputs, &outputs, &proof, b"test-tx-3"),
            Err(ConservationError::SignatureInvalid)
        );
    }

    #[test]
    fn conservation_proof_wrong_message_rejected() {
        // Correct proof but verified with wrong message — should fail.
        let r_in = test_scalar(40);
        let r_out = test_scalar(41);

        let inputs = vec![ValueCommitment::commit(500, &r_in)];
        let outputs = vec![ValueCommitment::commit(500, &r_out)];

        let excess = r_in - r_out;
        let proof = prove_conservation(&inputs, &outputs, &excess, b"correct-msg");

        assert_eq!(
            verify_conservation(&inputs, &outputs, &proof, b"wrong-msg"),
            Err(ConservationError::SignatureInvalid)
        );
    }

    #[test]
    fn conservation_proof_multi_asset() {
        // Test with asset-specific generators.
        let asset_a = 1u64;
        let asset_b = 2u64;

        let r1 = test_scalar(50);
        let r2 = test_scalar(51);
        let r3 = test_scalar(52);
        let r4 = test_scalar(53);

        // Asset A: input 100, output 100.
        let inputs_a = vec![ValueCommitment::commit_with_asset(100, &r1, asset_a)];
        let outputs_a = vec![ValueCommitment::commit_with_asset(100, &r2, asset_a)];
        let excess_a = r1 - r2;

        // Asset B: input 200, output 200.
        let inputs_b = vec![ValueCommitment::commit_with_asset(200, &r3, asset_b)];
        let outputs_b = vec![ValueCommitment::commit_with_asset(200, &r4, asset_b)];
        let excess_b = r3 - r4;

        // Each asset type is checked independently.
        let proof_a = prove_conservation(&inputs_a, &outputs_a, &excess_a, b"multi-asset");
        let proof_b = prove_conservation(&inputs_b, &outputs_b, &excess_b, b"multi-asset");

        assert!(verify_conservation(&inputs_a, &outputs_a, &proof_a, b"multi-asset").is_ok());
        assert!(verify_conservation(&inputs_b, &outputs_b, &proof_b, b"multi-asset").is_ok());
    }

    #[test]
    fn conservation_proof_empty_transaction() {
        // Edge case: no inputs, no outputs. Trivially balanced.
        let excess = Scalar::ZERO;
        let proof = prove_conservation(&[], &[], &excess, b"empty");
        assert!(verify_conservation(&[], &[], &proof, b"empty").is_ok());
    }

    #[test]
    fn conservation_proof_single_input_single_output() {
        // Simple 1-to-1 transfer.
        let r_in = test_scalar(60);
        let r_out = test_scalar(61);
        let value = 999u64;

        let inputs = vec![ValueCommitment::commit(value, &r_in)];
        let outputs = vec![ValueCommitment::commit(value, &r_out)];
        let excess = r_in - r_out;

        let proof = prove_conservation(&inputs, &outputs, &excess, b"1-to-1");
        assert!(verify_conservation(&inputs, &outputs, &proof, b"1-to-1").is_ok());
    }

    #[test]
    fn committed_note_construction() {
        let owner = [0xAA; 32];
        let blinding = test_scalar(70);
        let note_randomness = [0xBB; 32];
        let creation_nonce = [0xCC; 32];

        let opening = CommittedNoteOpening::new(
            owner,
            1000,
            42, // asset_type
            blinding,
            note_randomness,
            creation_nonce,
        );

        let note = CommittedNote::from_opening(&opening);
        assert_eq!(note.asset_type, 42);
        // Commitment should be non-zero.
        assert_ne!(note.note_commitment, [0u8; 32]);
        // Value commitment should equal commit_with_asset(1000, blinding, 42).
        let expected_vc = ValueCommitment::commit_with_asset(1000, &blinding, 42);
        assert_eq!(note.value_commitment.point, expected_vc.point);
    }

    // ─── Range proof tests ───────────────────────────────────────────────────

    #[test]
    fn range_proof_valid_zero() {
        let blinding = test_scalar(80);
        let value = 0u64;
        let commitment = ValueCommitment::commit(value, &blinding);
        let proof = BulletproofRangeProof::prove_range(value, &blinding);
        assert!(proof.verify_range(&commitment).is_ok());
    }

    #[test]
    fn range_proof_valid_one() {
        let blinding = test_scalar(81);
        let value = 1u64;
        let commitment = ValueCommitment::commit(value, &blinding);
        let proof = BulletproofRangeProof::prove_range(value, &blinding);
        assert!(proof.verify_range(&commitment).is_ok());
    }

    #[test]
    fn range_proof_valid_max() {
        let blinding = test_scalar(82);
        let value = u64::MAX;
        let commitment = ValueCommitment::commit(value, &blinding);
        let proof = BulletproofRangeProof::prove_range(value, &blinding);
        assert!(proof.verify_range(&commitment).is_ok());
    }

    #[test]
    fn range_proof_valid_large_value() {
        let blinding = test_scalar(83);
        let value = 1_000_000_000u64; // 1 billion
        let commitment = ValueCommitment::commit(value, &blinding);
        let proof = BulletproofRangeProof::prove_range(value, &blinding);
        assert!(proof.verify_range(&commitment).is_ok());
    }

    #[test]
    fn range_proof_wrong_commitment_fails() {
        // Prove for one value, verify against a different commitment.
        let blinding1 = test_scalar(84);
        let blinding2 = test_scalar(85);
        let commitment_wrong = ValueCommitment::commit(999, &blinding2);
        let proof = BulletproofRangeProof::prove_range(42, &blinding1);
        assert_eq!(
            proof.verify_range(&commitment_wrong),
            Err(RangeProofError::VerificationFailed)
        );
    }

    #[test]
    fn range_proof_wrong_value_commitment_fails() {
        // Prove for value=100 but verify against commitment to value=200 (same blinding).
        let blinding = test_scalar(86);
        let proof = BulletproofRangeProof::prove_range(100, &blinding);
        let wrong_commitment = ValueCommitment::commit(200, &blinding);
        assert_eq!(
            proof.verify_range(&wrong_commitment),
            Err(RangeProofError::VerificationFailed)
        );
    }

    #[test]
    fn range_proof_trait_impl() {
        // Test via the trait interface.
        let blinding = test_scalar(87);
        let value = 12345u64;
        let commitment = ValueCommitment::commit(value, &blinding);
        let proof =
            <BulletproofRangeProof as RangeProofTrait>::prove(value, &blinding, &commitment);
        assert!(<BulletproofRangeProof as RangeProofTrait>::verify(&proof, &commitment).is_ok());
    }

    #[test]
    fn range_proof_batch_verify() {
        let values = [100u64, 200, 300];
        let blindings: Vec<Scalar> = (0..3).map(|i| test_scalar(90 + i)).collect();
        let commitments: Vec<ValueCommitment> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, b)| ValueCommitment::commit(v, b))
            .collect();
        let proofs: Vec<BulletproofRangeProof> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, b)| BulletproofRangeProof::prove_range(v, b))
            .collect();

        assert!(BulletproofRangeProof::batch_verify(&proofs, &commitments).is_ok());
    }

    #[test]
    fn range_proof_batch_verify_length_mismatch() {
        let blinding = test_scalar(93);
        let commitment = ValueCommitment::commit(10, &blinding);
        let proof = BulletproofRangeProof::prove_range(10, &blinding);

        // More proofs than commitments.
        assert_eq!(
            BulletproofRangeProof::batch_verify(&[proof.clone(), proof], &[commitment]),
            Err(RangeProofError::LengthMismatch)
        );
    }

    // ─── Full conservation proof with range proofs ───────────────────────────

    #[test]
    fn full_conservation_valid_transaction() {
        // 2 inputs (300, 500) -> 2 outputs (450, 350). Total 800 = 800.
        let r_in1 = test_scalar(100);
        let r_in2 = test_scalar(101);
        let r_out1 = test_scalar(102);
        let r_out2 = test_scalar(103);

        let inputs = vec![
            ValueCommitment::commit(300, &r_in1),
            ValueCommitment::commit(500, &r_in2),
        ];
        let output_values = [450u64, 350];
        let output_blindings = [r_out1, r_out2];
        let outputs: Vec<ValueCommitment> = output_values
            .iter()
            .zip(output_blindings.iter())
            .map(|(&v, b)| ValueCommitment::commit(v, b))
            .collect();

        let excess_blinding = (r_in1 + r_in2) - (r_out1 + r_out2);

        let proof = prove_conservation_with_range(
            &inputs,
            &outputs,
            &output_values,
            &output_blindings,
            &excess_blinding,
            b"full-test-1",
        );

        assert!(verify_conservation_with_range(&inputs, &outputs, &proof, b"full-test-1").is_ok());
    }

    #[test]
    fn full_conservation_negative_value_attack_fails() {
        // Attack scenario: attacker tries to inflate by using a "negative" value.
        //
        // Honest: input 100 -> output 100 (no inflation).
        // Attack: input 100 -> output (100 + 1_000_000) and output (-1_000_000 mod l).
        //
        // The conservation equation would pass because the values sum correctly
        // in the scalar field. But the range proof on the "negative" output will fail
        // because the attacker cannot produce a valid 64-bit range proof for a value
        // that is actually (l - 1_000_000) when interpreted as a scalar.
        //
        // We simulate this by attempting to prove with a value that, when committed,
        // would look negative. Since we cannot actually call prove_range with a "negative"
        // u64, we instead show that a forged proof cannot verify:
        // Commit to a value using the scalar field directly (bypassing u64).
        let r_in = test_scalar(110);
        let r_out_legit = test_scalar(111);
        let r_out_attack = test_scalar(112);

        let input_value = 100u64;
        let inflated_value = 1_000_100u64; // more than input!

        let inputs = vec![ValueCommitment::commit(input_value, &r_in)];

        // The "legitimate" output gets the inflated value.
        let output_legit = ValueCommitment::commit(inflated_value, &r_out_legit);

        // The "attack" output must commit to a negative value so that
        // sum(outputs) = sum(inputs). The "negative" value in the scalar field:
        // negative_scalar = Scalar::from(input_value) - Scalar::from(inflated_value)
        //                  = -(inflated_value - input_value) mod l
        // This is NOT representable as a u64.
        let negative_scalar = Scalar::from(input_value) - Scalar::from(inflated_value);
        let output_attack = ValueCommitment {
            point: negative_scalar * value_generator() + r_out_attack * randomness_generator(),
        };

        let outputs = vec![output_legit.clone(), output_attack.clone()];

        // The excess should be zero-value (conservation holds in scalar field).
        let excess_blinding = r_in - (r_out_legit + r_out_attack);

        // Conservation proof alone would pass:
        let conservation_proof =
            prove_conservation(&inputs, &outputs, &excess_blinding, b"attack-tx");
        assert!(
            verify_conservation(&inputs, &outputs, &conservation_proof, b"attack-tx").is_ok(),
            "conservation alone passes (this is the vulnerability without range proofs)"
        );

        // But the attacker cannot produce a valid range proof for the attack output.
        // They can produce a range proof for the legit output:
        let legit_range_proof = BulletproofRangeProof::prove_range(inflated_value, &r_out_legit);
        assert!(legit_range_proof.verify_range(&output_legit).is_ok());

        // For the attack output, any proof the attacker might try will fail.
        // We simulate by using the legit proof against the attack commitment:
        assert_eq!(
            legit_range_proof.verify_range(&output_attack),
            Err(RangeProofError::VerificationFailed)
        );

        // And the full conservation proof with mismatched range proofs would also fail:
        let full_proof = FullConservationProof {
            conservation: conservation_proof,
            output_range_proofs: vec![legit_range_proof.clone(), legit_range_proof],
        };
        let result = verify_conservation_with_range(&inputs, &outputs, &full_proof, b"attack-tx");
        assert!(
            result.is_err(),
            "full conservation with range proofs rejects the attack"
        );
        match result {
            Err(FullConservationError::RangeProofFailed {
                output_index: 1, ..
            }) => {}
            other => panic!("expected RangeProofFailed at index 1, got {:?}", other),
        }
    }

    // ─── Byte-friendly helper tests ──────────────────────────────────────────

    #[test]
    fn commit_bytes_matches_scalar_commit() {
        // commit_bytes(value, blinding_bytes) must equal the compressed bytes of
        // ValueCommitment::commit(value, Scalar::from_bytes_mod_order(blinding)).
        let blinding = [7u8; 32];
        let scalar = Scalar::from_bytes_mod_order(blinding);
        let expected = ValueCommitment::commit(12345, &scalar).to_bytes().0;
        let got = commit_bytes(12345, &blinding);
        assert_eq!(got, expected);
        // And it must decompress back to a valid Ristretto point.
        assert!(ValueCommitment::from_bytes(&ValueCommitmentBytes(got)).is_some());
    }

    #[test]
    fn prove_conservation_bytes_roundtrip_balanced() {
        // 1000 input == 700 transfer + 300 change. Real generate -> verify.
        let inputs = [(1000u64, [1u8; 32])];
        let outputs = [(700u64, [2u8; 32]), (300u64, [3u8; 32])];
        let msg = b"roundtrip-balanced";

        let out = prove_conservation_bytes(&inputs, &outputs, msg);
        assert_eq!(out.input_commitments.len(), 1);
        assert_eq!(out.output_commitments.len(), 2);

        // Reconstruct ValueCommitments from the returned bytes and verify.
        let in_vcs: Vec<ValueCommitment> = out
            .input_commitments
            .iter()
            .map(|b| ValueCommitment::from_bytes(&ValueCommitmentBytes(*b)).unwrap())
            .collect();
        let out_vcs: Vec<ValueCommitment> = out
            .output_commitments
            .iter()
            .map(|b| ValueCommitment::from_bytes(&ValueCommitmentBytes(*b)).unwrap())
            .collect();

        assert!(
            verify_conservation(&in_vcs, &out_vcs, &out.proof, msg).is_ok(),
            "balanced byte-roundtrip proof must verify"
        );
    }

    #[test]
    fn prove_conservation_bytes_non_conserving_fails() {
        // Adversarial: 1000 input but outputs sum to 1100 (inflation). The
        // excess point has a nonzero V-component, so the Schnorr proof must NOT
        // verify even though excess_blinding is computed honestly.
        let inputs = [(1000u64, [1u8; 32])];
        let outputs = [(700u64, [2u8; 32]), (400u64, [3u8; 32])]; // 1100 != 1000
        let msg = b"non-conserving";

        let out = prove_conservation_bytes(&inputs, &outputs, msg);
        let in_vcs: Vec<ValueCommitment> = out
            .input_commitments
            .iter()
            .map(|b| ValueCommitment::from_bytes(&ValueCommitmentBytes(*b)).unwrap())
            .collect();
        let out_vcs: Vec<ValueCommitment> = out
            .output_commitments
            .iter()
            .map(|b| ValueCommitment::from_bytes(&ValueCommitmentBytes(*b)).unwrap())
            .collect();

        assert_eq!(
            verify_conservation(&in_vcs, &out_vcs, &out.proof, msg),
            Err(ConservationError::SignatureInvalid),
            "non-conserving (inflating) byte-roundtrip proof must fail closed"
        );
    }

    #[test]
    fn full_conservation_range_proof_count_mismatch() {
        let r_in = test_scalar(120);
        let r_out = test_scalar(121);

        let inputs = vec![ValueCommitment::commit(50, &r_in)];
        let outputs = vec![ValueCommitment::commit(50, &r_out)];
        let excess = r_in - r_out;

        let conservation = prove_conservation(&inputs, &outputs, &excess, b"mismatch");

        // Provide no range proofs (should be 1).
        let full_proof = FullConservationProof {
            conservation,
            output_range_proofs: vec![],
        };

        assert_eq!(
            verify_conservation_with_range(&inputs, &outputs, &full_proof, b"mismatch"),
            Err(FullConservationError::RangeProofCountMismatch {
                expected: 1,
                got: 0
            })
        );
    }
}
