//! FROST (threshold-Schnorr) quorum certificates — the ADDITIVE alternative to
//! the BLS path in [`crate::threshold`], per `docs/FROST-MIGRATION.md`.
//!
//! The Lean spec is `metatheory/Dregg2/Crypto/Frost.lean`
//! (`frost_cert_verifies_under_group_key`): a t-of-n FROST certificate IS a
//! single ordinary Schnorr signature `(R, z)` verified by the single-signer
//! verifier `z·g = R + e·pk` under the federation's GROUP public key —
//! constant-size regardless of committee size, resting only on the
//! discrete-log carrier (the same ed25519 curve every vote signature already
//! uses), with NO pairing and NO trusted KZG setup.
//!
//! # What lives here (additive stage — BLS is untouched)
//!
//! * [`FrostQC`] — the certificate: exactly one 64-byte ed25519-shaped Schnorr
//!   signature `(R ‖ z)`. Compare `threshold::ThresholdQC` (BLS aggregate +
//!   SNARK proof, arkworks-serialized, ~4x larger and pairing-verified).
//! * [`verify_frost_quorum`] — the group-key verify: RFC 8032 ed25519
//!   `verify_strict` under the group [`PublicKey`]. This is byte-for-byte the
//!   verifier a FROST(Ed25519, SHA-512) signing ceremony (RFC 9591) targets,
//!   so a later cutover to a vetted `frost-ed25519` signing stack changes
//!   NOTHING on the verify side.
//! * [`QuorumScheme`] — the scheme selector over the opaque
//!   `dregg_types::ThresholdQC` bytes carried in `AttestedRoot.threshold_qc` /
//!   wire messages, so a verifier holding either a BLS committee or a FROST
//!   group key dispatches without the carried types changing shape.
//! * [`FrostTestDealer`] / [`frost_sign`] — a TRUSTED-DEALER Shamir keygen and
//!   a single-ceremony signing helper that realizes the Lean theorem's exact
//!   algebra (Lagrange-combined partial responses `z_i = k_i + e·λ_i·x_i`).
//! * [`HybridQC`] / [`verify_hybrid_quorum`] — the HYBRID certificate: the
//!   FROST aggregate AND per-signer FIPS 204 ML-DSA-65 signatures, accepted
//!   only when BOTH halves verify (the Lean `hybridVerify = classical ∧ pq`),
//!   so the quorum survives a quantum adversary that breaks the discrete-log
//!   half (`hybrid_survives_classical_break`). Additive and staged behind
//!   [`QuorumScheme::Hybrid`], not wired into live consensus.
//! * [`HermineHybridQC`] / [`verify_hermine_hybrid`] — the COMPACT-PQ hybrid:
//!   the ed25519 vote quorum AND ONE `crypto_hermine` threshold certificate
//!   (the Raccoon-based lattice FROST-analog), so the post-quantum half is a
//!   single committee-INDEPENDENT object instead of [`HybridQC`]'s `t × ~3.3 KiB`
//!   ML-DSA concatenation. The Lean spec is `Dregg2.Crypto.HermineHybrid`
//!   (`hermine_hybrid_survives_classical_break`, quantum-safety reducing to
//!   MSIS). STAGED REFERENCE ONLY behind [`QuorumScheme::HermineHybrid`]:
//!   crypto-hermine is pre-audit (toy challenge hash, no formal ROS argument),
//!   so the ML-DSA [`QuorumScheme::HybridVotes`] path stays the deployable one —
//!   this wires the compact-PQ STRUCTURE and its size win, not a deployment.
//!
//! # Production-signing boundary (read before wiring signers)
//!
//! [`frost_sign`] omits RFC 9591's per-signer binding factors (the two-nonce
//! `ρ` mechanism that defeats the Drijvers/ROS concurrent-session attack) and
//! [`FrostTestDealer`] centralizes the group secret in a dealer. Both are fit
//! for tests, differentials against the Lean spec, and single-ceremony
//! fixtures — NOT for live concurrent signing. The migration plan's signing
//! stage adopts the vetted `frost-ed25519` crate (Zcash Foundation, audited)
//! for nonce generation/aggregation and ports `crate::dkg`'s JF-DKG to the
//! edwards group for dealerless keygen; the verify side below is already the
//! final one.

use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha512};

use dregg_types::{PublicKey, Signature};

// The COMPACT post-quantum half (`HermineHybridQC`). crypto-hermine is a lattice
// THRESHOLD signature, so its certificate is ONE object under the group key —
// committee-INDEPENDENT — unlike ML-DSA's per-signer Vec. STAGED reference only.
use crypto_hermine::{
    HermineSignature, Matrix, N as HERMINE_N, Poly as HerminePoly, PolyVec, Q as HERMINE_Q,
    verify_hermine,
};

/// Size in bytes of a serialized [`FrostQC`]: one Schnorr signature `(R ‖ z)`.
pub const FROST_QC_BYTES: usize = 64;

// =============================================================================
// FrostQC — the certificate
// =============================================================================

/// A FROST quorum certificate: ONE ordinary Schnorr signature under the
/// federation's group public key.
///
/// Constant-size for any committee size and any signing subset — the verifier
/// cannot even tell which t-subset signed (`frost_cert_verifies_under_group_key`
/// has no dependence on `t`, `n`, or `parts`). Threshold enforcement is a
/// SIGNING-side fact: fewer than `t` Shamir shares cannot Lagrange-reconstruct
/// the group secret's response, so no sub-threshold subset can produce a
/// verifying certificate (see `sub_threshold_subset_cannot_forge` below).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrostQC {
    /// The Schnorr signature `(R ‖ z)`: 32-byte compressed nonce point,
    /// 32-byte response scalar — the ed25519 wire shape.
    pub signature: Signature,
}

impl FrostQC {
    /// Serialize: exactly the 64 signature bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.signature.0.to_vec()
    }

    /// Deserialize from exactly [`FROST_QC_BYTES`] bytes.
    ///
    /// A BLS `threshold::ThresholdQC` serialization is larger (aggregate +
    /// SNARK proof), so the two schemes' opaque bytes cannot be confused by
    /// length alone; [`QuorumScheme`] still dispatches explicitly.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let arr: [u8; FROST_QC_BYTES] = bytes.try_into().ok()?;
        Some(Self {
            signature: Signature(arr),
        })
    }
}

// =============================================================================
// The group-key verify — the Lean `SchnorrVerifies` relation
// =============================================================================

/// Verify a FROST quorum certificate under the federation's group public key.
///
/// This is the single-signer Schnorr verifier the Lean spec reuses verbatim
/// (`SchnorrVerifies g pk R e z ↔ z·g = R + e·pk`), instantiated at ed25519:
/// `e = SHA-512(R ‖ A ‖ M) mod ℓ` and the check is `z·B = R + e·A`, exactly
/// RFC 8032 — via `verify_strict` (no cofactor slack, R and A must be
/// canonical), so a certificate that verifies here verifies as a plain
/// ed25519 signature everywhere else too.
pub fn verify_frost_quorum(group_key: &PublicKey, message: &[u8], qc: &FrostQC) -> bool {
    let Ok(vk) = ed25519_dalek::VerifyingKey::from_bytes(&group_key.0) else {
        return false;
    };
    let sig = ed25519_dalek::Signature::from_bytes(&qc.signature.0);
    vk.verify_strict(message, &sig).is_ok()
}

// =============================================================================
// QuorumScheme — the additive selector over opaque QC bytes
// =============================================================================

/// Which threshold-signature scheme a quorum certificate's opaque bytes carry.
///
/// The transition seam: `AttestedRoot.threshold_qc`, the wire
/// `AttestedRoot{,Push}` messages, and `persist`'s `StoredAttestedRoot` all
/// carry `dregg_types::ThresholdQC(Vec<u8>)` — scheme-opaque bytes. During the
/// migration BOTH schemes are valid; a verifier holds whichever context it has
/// and dispatches here. BLS verification is delegated unchanged to
/// [`crate::threshold::FederationCommittee::verify`].
pub enum QuorumScheme<'a> {
    /// The incumbent weighted-threshold BLS path (`hints`, pairing + KZG).
    Bls(&'a crate::threshold::FederationCommittee),
    /// The FROST path: everything the verifier needs is ONE 32-byte group key.
    Frost {
        /// The federation's group public key (Shamir secret in the exponent).
        group_key: PublicKey,
    },
    /// The HYBRID path: the FROST group key AND the committee's ML-DSA-65
    /// public keys. A certificate is a quorum only if BOTH halves verify —
    /// the classical aggregate under `group_key` and ≥ `threshold` distinct
    /// ML-DSA signatures under `ml_dsa_pubkeys` (the PQ half re-imposes the
    /// threshold explicitly, since ML-DSA has no threshold aggregation).
    Hybrid {
        /// The federation's group public key (the classical half).
        group_key: PublicKey,
        /// One ML-DSA-65 public key per committee member, member `i` at
        /// position `i` (the post-quantum half).
        ml_dsa_pubkeys: &'a [MlDsaPublicKey],
        /// Minimum count of distinct, valid ML-DSA signatures required.
        threshold: usize,
    },
    /// The LIVE-consensus hybrid path (`HybridPq`): the classical half is the
    /// EXISTING per-member ed25519 votes quorum (no FROST, no DKG), the PQ
    /// half is per-member ML-DSA-65 signatures over the same vote message.
    /// The opaque bytes carry a [`crate::types::HybridQuorumCertificate`].
    HybridVotes {
        /// The committee's ed25519 member keys, member `i` at position `i`
        /// (the same table the votes quorum verifies against today).
        members: &'a [PublicKey],
        /// One ML-DSA-65 public key per committee member, member `i` at
        /// position `i` (the post-quantum half).
        ml_dsa_pubkeys: &'a [MlDsaPublicKey],
    },
    /// The COMPACT-PQ hybrid path (`HermineHybrid`, STAGED reference): the
    /// classical half is the ed25519 vote quorum (as [`Self::HybridVotes`]), and
    /// the PQ half is ONE Hermine threshold certificate under the federation's
    /// Hermine group key — committee-INDEPENDENT, vs the `t × ~3.3 KiB` ML-DSA
    /// concatenation. The opaque bytes carry a [`HermineHybridQC`].
    ///
    /// Default-off reference: crypto-hermine is pre-audit; [`Self::HybridVotes`]
    /// stays the deployable post-quantum path.
    HermineHybrid {
        /// The committee's ed25519 member keys, member `i` at position `i`.
        members: &'a [PublicKey],
        /// The Hermine public matrix `A` (the shared CRS the group key is `A·s`).
        hermine_a: &'a Matrix,
        /// The federation's Hermine group public key `t = A·s`.
        hermine_group_key: &'a PolyVec,
        /// Minimum count of distinct, valid ed25519 votes required (the Hermine
        /// half's own threshold is enforced cryptographically at its verifier).
        threshold: usize,
    },
}

impl QuorumScheme<'_> {
    /// Verify opaque quorum-certificate bytes (as carried in
    /// `AttestedRoot.threshold_qc` and the wire messages) against `message`
    /// under this scheme.
    pub fn verify_opaque_qc(&self, qc_bytes: &[u8], message: &[u8]) -> bool {
        match self {
            QuorumScheme::Bls(committee) => {
                match crate::threshold::ThresholdQC::from_bytes(qc_bytes) {
                    Some(qc) => committee.verify(&qc, message).is_ok(),
                    None => false,
                }
            }
            QuorumScheme::Frost { group_key } => match FrostQC::from_bytes(qc_bytes) {
                Some(qc) => verify_frost_quorum(group_key, message, &qc),
                None => false,
            },
            QuorumScheme::Hybrid {
                group_key,
                ml_dsa_pubkeys,
                threshold,
            } => match HybridQC::from_bytes(qc_bytes) {
                Some(qc) => {
                    verify_hybrid_quorum(group_key, ml_dsa_pubkeys, message, &qc, *threshold)
                }
                None => false,
            },
            QuorumScheme::HybridVotes {
                members,
                ml_dsa_pubkeys,
            } => match crate::types::HybridQuorumCertificate::from_bytes(qc_bytes) {
                Some(hqc) => {
                    // Bind the certificate to the caller's expected message:
                    // the vote message the QC's own coordinates derive must be
                    // exactly the message being attested.
                    let derived = crate::types::QuorumCertificate::vote_message(
                        &hqc.qc.block_hash,
                        hqc.qc.height,
                        hqc.qc.view,
                    );
                    derived == message && hqc.verify_with_keys(members, ml_dsa_pubkeys)
                }
                None => false,
            },
            QuorumScheme::HermineHybrid {
                members,
                hermine_a,
                hermine_group_key,
                threshold,
            } => match HermineHybridQC::from_bytes(qc_bytes) {
                Some(qc) => verify_hermine_hybrid(
                    members,
                    hermine_a,
                    hermine_group_key,
                    message,
                    &qc,
                    *threshold,
                ),
                None => false,
            },
        }
    }
}

// =============================================================================
// Trusted-dealer keygen + single-ceremony signing (the Lean theorem's algebra)
// =============================================================================

/// One member's Shamir share of the group secret, dealt by [`FrostTestDealer`].
#[derive(Clone)]
pub struct FrostShare {
    /// 1-based Shamir evaluation index (x-coordinate; 0 is the group secret).
    pub index: u64,
    /// The share scalar `f(index)`.
    share: Scalar,
}

impl FrostShare {
    /// This member's share verification key `x_i·B` (for future
    /// partial-signature audit; unused by the certificate verifier).
    pub fn share_public(&self) -> PublicKey {
        PublicKey(EdwardsPoint::mul_base(&self.share).compress().to_bytes())
    }
}

/// Trusted-dealer Shamir keygen over the ed25519 scalar field.
///
/// The dealer transiently knows the group secret — exactly the property the
/// production DKG stage removes (port of `crate::dkg`'s JF-DKG, where
/// `f(0) = Σ f_i(0)` never exists in one place). Fit for tests and fixtures.
pub struct FrostTestDealer {
    /// The group public key `A = f(0)·B`.
    pub group_key: PublicKey,
    /// The signing threshold `t` (shares needed to reconstruct at 0).
    pub threshold: u64,
    /// All dealt shares, index `i+1` at position `i`.
    pub shares: Vec<FrostShare>,
}

impl FrostTestDealer {
    /// Deal an `n`-member committee with threshold `t` from caller-supplied
    /// polynomial-coefficient entropy (64 wide bytes per coefficient).
    ///
    /// Deterministic in `coeff_seed` for reproducible fixtures; pass OS
    /// entropy (`getrandom::fill`) for non-fixture use.
    pub fn deal(n: u64, t: u64, coeff_seed: &[[u8; 64]]) -> Option<Self> {
        if t == 0 || t > n || (coeff_seed.len() as u64) < t {
            return None;
        }
        // f(x) = a_0 + a_1 x + … + a_{t-1} x^{t-1}
        let coeffs: Vec<Scalar> = coeff_seed[..t as usize]
            .iter()
            .map(Scalar::from_bytes_mod_order_wide)
            .collect();
        let eval = |x: Scalar| -> Scalar {
            // Horner
            coeffs.iter().rev().fold(Scalar::ZERO, |acc, c| acc * x + c)
        };
        let group_secret = coeffs[0];
        let group_key = PublicKey(EdwardsPoint::mul_base(&group_secret).compress().to_bytes());
        let shares = (1..=n)
            .map(|i| FrostShare {
                index: i,
                share: eval(Scalar::from(i)),
            })
            .collect();
        Some(Self {
            group_key,
            threshold: t,
            shares,
        })
    }

    /// Deal from OS entropy.
    pub fn deal_random(n: u64, t: u64) -> Option<Self> {
        let mut seeds = vec![[0u8; 64]; t as usize];
        for s in seeds.iter_mut() {
            getrandom::fill(s).expect("OS entropy unavailable");
        }
        Self::deal(n, t, &seeds)
    }
}

/// The Lagrange coefficient at 0 for participant `i` over the index set `parts`.
fn lagrange_at_zero(i: u64, parts: &[u64]) -> Scalar {
    let xi = Scalar::from(i);
    let mut num = Scalar::ONE;
    let mut den = Scalar::ONE;
    for &j in parts {
        if j == i {
            continue;
        }
        let xj = Scalar::from(j);
        num *= xj; // (0 - x_j) products; signs cancel between num and den
        den *= xj - xi;
    }
    num * den.invert()
}

/// The ed25519 challenge `e = SHA-512(R ‖ A ‖ M) mod ℓ`.
fn ed25519_challenge(r_compressed: &[u8; 32], group_key: &PublicKey, message: &[u8]) -> Scalar {
    let mut h = Sha512::new();
    h.update(r_compressed);
    h.update(group_key.0);
    h.update(message);
    Scalar::from_bytes_mod_order_wide(&h.finalize().into())
}

/// Produce a FROST quorum certificate from a signing subset — the Lean
/// theorem's algebra, executably.
///
/// Each participant `i ∈ parts` contributes nonce `k_i` (from
/// `nonce_seed[idx]`) with commitment `R_i = k_i·B`; the ceremony forms
/// `R = Σ R_i`, the ed25519 challenge `e = H(R ‖ A ‖ M)`, partial responses
/// `z_i = k_i + e·(λ_i·x_i)`, and the certificate `(R, z = Σ z_i)` — which
/// [`verify_frost_quorum`] accepts iff `parts` carries ≥ t genuine shares
/// (`frost_cert_verifies_under_group_key` with `hrecon` from Shamir).
///
/// SINGLE-CEREMONY ONLY: no RFC 9591 binding factors — see the module doc.
/// `nonce_seed` must be fresh, independent entropy per ceremony (nonce reuse
/// leaks shares, as for any Schnorr).
pub fn frost_sign(
    group_key: &PublicKey,
    signers: &[&FrostShare],
    nonce_seed: &[[u8; 64]],
    message: &[u8],
) -> Option<FrostQC> {
    if signers.is_empty() || nonce_seed.len() < signers.len() {
        return None;
    }
    let parts: Vec<u64> = signers.iter().map(|s| s.index).collect();
    // Distinct indices only (a duplicated signer is a caller bug, not a quorum).
    {
        let mut seen = std::collections::HashSet::new();
        if !parts.iter().all(|i| seen.insert(*i)) {
            return None;
        }
    }

    // Round 1: nonces + commitments.
    let nonces: Vec<Scalar> = nonce_seed[..signers.len()]
        .iter()
        .map(Scalar::from_bytes_mod_order_wide)
        .collect();
    let r_point: EdwardsPoint = nonces.iter().map(EdwardsPoint::mul_base).sum();
    let r_compressed = r_point.compress().to_bytes();

    // Challenge under the GROUP key.
    let e = ed25519_challenge(&r_compressed, group_key, message);

    // Round 2: Lagrange-weighted partial responses, summed.
    let z: Scalar = signers
        .iter()
        .zip(nonces.iter())
        .map(|(s, k)| k + e * (lagrange_at_zero(s.index, &parts) * s.share))
        .sum();

    let mut sig = [0u8; 64];
    sig[..32].copy_from_slice(&r_compressed);
    sig[32..].copy_from_slice(z.as_bytes());
    Some(FrostQC {
        signature: Signature(sig),
    })
}

/// Sign with fresh OS entropy for the nonces.
pub fn frost_sign_random(
    group_key: &PublicKey,
    signers: &[&FrostShare],
    message: &[u8],
) -> Option<FrostQC> {
    let mut seeds = vec![[0u8; 64]; signers.len()];
    for s in seeds.iter_mut() {
        getrandom::fill(s).expect("OS entropy unavailable");
    }
    frost_sign(group_key, signers, &seeds, message)
}

// =============================================================================
// HYBRID quorum certificates — FROST/ed25519 AND FIPS 204 ML-DSA-65
// =============================================================================

/// Domain-separation context for the ML-DSA half of a hybrid QC (FIPS 204
/// `ctx`, bound into every signature). Sign and verify must agree on it.
pub const HYBRID_PQ_CTX: &[u8] = b"dregg-hybrid-qc-v1";

/// An ML-DSA-65 public key, as its FIPS 204 serialized bytes
/// ([`dregg_pq::ML_DSA_PK_LEN`] = 1952). Validated (`try_from_bytes`) at verify
/// time; an undecodable key rejects any certificate that names it.
#[derive(Clone, PartialEq, Eq)]
pub struct MlDsaPublicKey(pub [u8; dregg_pq::ML_DSA_PK_LEN]);

impl std::fmt::Debug for MlDsaPublicKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // 1952 bytes of key material is noise in a debug dump; show a prefix.
        write!(f, "MlDsaPublicKey({}..)", hex::encode(&self.0[..8]))
    }
}

impl MlDsaPublicKey {
    /// Verify an ML-DSA-65 signature over `message` under [`HYBRID_PQ_CTX`]
    /// (the domain-separation context every hybrid-quorum signature binds).
    ///
    /// `false` on wrong-length signature bytes or an undecodable key.
    pub fn verify(&self, message: &[u8], sig_bytes: &[u8]) -> bool {
        // The other entry from this crate into `dregg-pq` — see `MlDsaSigningKey::from_seed`.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        dregg_pq::ml_dsa_verify(&self.0, HYBRID_PQ_CTX, message, sig_bytes)
    }
}

/// An ML-DSA-65 signing key held by one committee member, for producing the
/// PQ half of a hybrid quorum. A thin newtype over the shared
/// [`dregg_pq::MlDsaKey`] primitive; every signature it produces is bound to
/// [`HYBRID_PQ_CTX`].
#[derive(Clone)]
pub struct MlDsaSigningKey(dregg_pq::MlDsaKey);

impl std::fmt::Debug for MlDsaSigningKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("MlDsaSigningKey(..)")
    }
}

impl MlDsaSigningKey {
    /// Deterministic keypair from a 32-byte seed `ξ` (`keygen_from_seed`) —
    /// for reproducible fixtures, exactly like [`HybridTestDealer::deal`].
    pub fn from_seed(xi: &[u8; 32]) -> (MlDsaPublicKey, Self) {
        // `dregg-federation` is a light leaf: it cannot link the Lean archive from
        // `[dependencies]`, so with no verified core installed `dregg-pq` refuses this derivation
        // with an uncatchable `process::abort()` — which is what this crate's lib-test binary did.
        // The dev-only `dregg-pq-testkit` links the archive and installs the cores; this and
        // `MlDsaPublicKey::verify` above are the two entries from this crate into `dregg-pq`, so
        // the lib-test binary is covered by these two lines.
        //
        // `#[cfg(test)]` because the shipped crate stays archive-free — a node installs the same
        // cores at startup.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        let key = dregg_pq::MlDsaKey::from_ed25519_seed(xi);
        let pk = MlDsaPublicKey(
            key.public_bytes()
                .try_into()
                .expect("ML-DSA-65 public key is ML_DSA_PK_LEN bytes"),
        );
        (pk, Self(key))
    }

    /// Sign `message` under [`HYBRID_PQ_CTX`] (hedged from OS entropy).
    pub fn sign(&self, message: &[u8]) -> Option<Vec<u8>> {
        self.0.try_sign(HYBRID_PQ_CTX, message)
    }
}

/// A HYBRID quorum certificate: the classical FROST aggregate PLUS one
/// ML-DSA-65 signature per participating signer.
///
/// The Lean `hybridVerify = classical ∧ pq`: [`verify_hybrid_quorum`] accepts
/// only when BOTH halves verify, so forging a hybrid quorum requires breaking
/// ed25519 discrete log AND module-lattice SIS/LWE simultaneously
/// (`hybrid_survives_classical_break`). The PQ half carries explicit
/// per-signer signatures — ML-DSA has no threshold aggregation — so unlike
/// [`FrostQC`] the certificate size grows with the signing subset
/// (~3.3 KiB per signer) and the verifier CAN see which subset signed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HybridQC {
    /// The classical half: the FROST Schnorr aggregate under the group key.
    pub frost: FrostQC,
    /// The post-quantum half: `(committee position, ML-DSA-65 signature
    /// bytes)` per participating signer. Positions are 0-based into the
    /// verifier's `ml_dsa_pubkeys` slice.
    pub pq_sigs: Vec<(usize, Vec<u8>)>,
}

impl HybridQC {
    /// Serialize to the opaque-bytes convention (`dregg_types::ThresholdQC`):
    /// `frost(64) ‖ count(u32 LE) ‖ [index(u32 LE) ‖ sig_len(u32 LE) ‖ sig]*`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = self.frost.to_bytes();
        out.extend_from_slice(&(self.pq_sigs.len() as u32).to_le_bytes());
        for (index, sig) in &self.pq_sigs {
            out.extend_from_slice(&(*index as u32).to_le_bytes());
            out.extend_from_slice(&(sig.len() as u32).to_le_bytes());
            out.extend_from_slice(sig);
        }
        out
    }

    /// Deserialize; `None` on any framing violation (short header, short
    /// entry, trailing bytes).
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let frost = FrostQC::from_bytes(bytes.get(..FROST_QC_BYTES)?)?;
        let mut rest = bytes.get(FROST_QC_BYTES..)?;
        let take_u32 = |rest: &mut &[u8]| -> Option<u32> {
            let (head, tail) = rest.split_at_checked(4)?;
            *rest = tail;
            Some(u32::from_le_bytes(head.try_into().ok()?))
        };
        let count = take_u32(&mut rest)?;
        // `count` is attacker-controlled: cap the preallocation by what the
        // remaining bytes could possibly frame (≥ 8 bytes per entry).
        let mut pq_sigs = Vec::with_capacity((count as usize).min(rest.len() / 8));
        for _ in 0..count {
            let index = take_u32(&mut rest)? as usize;
            let sig_len = take_u32(&mut rest)? as usize;
            let (sig, tail) = rest.split_at_checked(sig_len)?;
            rest = tail;
            pq_sigs.push((index, sig.to_vec()));
        }
        if !rest.is_empty() {
            return None;
        }
        Some(Self { frost, pq_sigs })
    }
}

/// Verify a hybrid quorum certificate: the Lean `hybridVerify = classical ∧ pq`.
///
/// Accepts iff BOTH:
/// * (classical) [`verify_frost_quorum`] accepts `qc.frost` under `group_key`;
/// * (post-quantum) `ml_dsa_pubkeys` is pairwise DISTINCT (one PQ authority
///   cannot occupy two committee slots), `qc.pq_sigs` carries at least
///   `threshold` entries, EVERY entry names a distinct in-range committee
///   position, and EVERY entry's signature ML-DSA-65-verifies over `message`
///   (with [`HYBRID_PQ_CTX`]) against that position's key in `ml_dsa_pubkeys`.
///
/// STRICT on the PQ half: any invalid, duplicate, or out-of-range entry
/// rejects the WHOLE certificate (not merely "doesn't count") — a valid
/// quorum has no reason to carry junk, and refusing it kills malleability
/// slop. `threshold == 0` is refused outright: it would make the PQ half
/// vacuous and the "hybrid" a plain FROST cert in disguise.
pub fn verify_hybrid_quorum(
    group_key: &PublicKey,
    ml_dsa_pubkeys: &[MlDsaPublicKey],
    message: &[u8],
    qc: &HybridQC,
    threshold: usize,
) -> bool {
    // Classical half.
    if !verify_frost_quorum(group_key, message, &qc.frost) {
        return false;
    }
    // Post-quantum half.
    verify_pq_quorum_half(ml_dsa_pubkeys, message, &qc.pq_sigs, threshold)
}

/// Verify the POST-QUANTUM half of a hybrid quorum on its own: at least
/// `threshold` entries, EVERY entry naming a distinct in-range committee
/// position, and EVERY entry's signature ML-DSA-65-verifying over `message`
/// (with [`HYBRID_PQ_CTX`]) against that position's key.
///
/// The enrolled roster `ml_dsa_pubkeys` must ALSO be pairwise DISTINCT: one
/// PQ authority cannot occupy multiple committee slots. Checked over the WHOLE
/// roster — including slots absent from this certificate's subset — so a
/// threshold-1 subset cannot make a duplicate enrollment valid. The same
/// distinct-roster contract [`crate::receipt::verify_hybrid_quorum_sigs`]
/// enforces for the receipt / checkpoint / cross-fed carrier.
///
/// This is the exact PQ leg of [`verify_hybrid_quorum`], factored so BOTH
/// classical carriers can share it: the FROST aggregate ([`HybridQC`]) and
/// the ed25519 per-member votes quorum
/// ([`crate::types::HybridQuorumCertificate`], the live-consensus wiring).
/// Same strictness: any invalid, duplicate, or out-of-range entry rejects
/// the WHOLE set, a duplicate enrolled roster is refused outright, and
/// `threshold == 0` (a vacuous PQ half) is refused.
pub fn verify_pq_quorum_half(
    ml_dsa_pubkeys: &[MlDsaPublicKey],
    message: &[u8],
    pq_sigs: &[(usize, Vec<u8>)],
    threshold: usize,
) -> bool {
    if threshold == 0 {
        return false;
    }
    // The enrolled ML-DSA roster must be pairwise DISTINCT: distinct classical
    // slots cannot share ONE enrolled PQ authority. Check the WHOLE roster
    // (not merely the subset this certificate names), so a threshold-1 subset
    // cannot make a duplicate enrollment valid — the same distinct-roster
    // contract `receipt::verify_hybrid_quorum_sigs` enforces.
    if ml_dsa_pubkeys
        .iter()
        .enumerate()
        .any(|(i, key)| ml_dsa_pubkeys[..i].contains(key))
    {
        return false;
    }
    let mut seen = std::collections::HashSet::new();
    for (index, sig_bytes) in pq_sigs {
        let Some(pk_bytes) = ml_dsa_pubkeys.get(*index) else {
            return false;
        };
        if !seen.insert(*index) {
            return false;
        }
        if !pk_bytes.verify(message, sig_bytes) {
            return false;
        }
    }
    pq_sigs.len() >= threshold
}

/// Trusted-dealer keygen for the HYBRID committee: a [`FrostTestDealer`]
/// Shamir sharing PLUS an independent ML-DSA-65 keypair per member (member
/// `i` holds FROST share index `i+1` and PQ keypair position `i`).
///
/// Same fitness boundary as [`FrostTestDealer`]: tests, differentials, and
/// single-ceremony fixtures — the production stage deals FROST shares by DKG
/// and has each member generate its own ML-DSA keypair locally (nothing about
/// the PQ half needs a dealer at all; keys here are dealt only so fixtures
/// are one call).
pub struct HybridTestDealer {
    /// The classical half's dealer (group key, threshold, Shamir shares).
    pub frost: FrostTestDealer,
    /// Each member's ML-DSA-65 public key, member `i` at position `i` —
    /// exactly the slice [`verify_hybrid_quorum`] takes.
    pub ml_dsa_pubkeys: Vec<MlDsaPublicKey>,
    /// Each member's ML-DSA-65 signing key (dealer-held; test-only).
    ml_dsa_keys: Vec<MlDsaSigningKey>,
}

impl HybridTestDealer {
    /// Deal an `n`-member hybrid committee with threshold `t`:
    /// `coeff_seed` feeds the Shamir polynomial (as [`FrostTestDealer::deal`]),
    /// `pq_seed` feeds FIPS 204 `keygen_from_seed` (one 32-byte `ξ` per
    /// member). Deterministic in both seeds for reproducible fixtures.
    pub fn deal(n: u64, t: u64, coeff_seed: &[[u8; 64]], pq_seed: &[[u8; 32]]) -> Option<Self> {
        if (pq_seed.len() as u64) < n {
            return None;
        }
        let frost = FrostTestDealer::deal(n, t, coeff_seed)?;
        let mut ml_dsa_pubkeys = Vec::with_capacity(n as usize);
        let mut ml_dsa_keys = Vec::with_capacity(n as usize);
        for xi in &pq_seed[..n as usize] {
            let (pk, sk) = MlDsaSigningKey::from_seed(xi);
            ml_dsa_pubkeys.push(pk);
            ml_dsa_keys.push(sk);
        }
        Some(Self {
            frost,
            ml_dsa_pubkeys,
            ml_dsa_keys,
        })
    }

    /// Deal from OS entropy.
    pub fn deal_random(n: u64, t: u64) -> Option<Self> {
        let mut coeff_seed = vec![[0u8; 64]; t as usize];
        for s in coeff_seed.iter_mut() {
            getrandom::fill(s).expect("OS entropy unavailable");
        }
        let mut pq_seed = vec![[0u8; 32]; n as usize];
        for s in pq_seed.iter_mut() {
            getrandom::fill(s).expect("OS entropy unavailable");
        }
        Self::deal(n, t, &coeff_seed, &pq_seed)
    }
}

/// Produce a HYBRID quorum certificate: one FROST ceremony over the signing
/// subset PLUS each signer's individual ML-DSA-65 signature over the same
/// `message` (under [`HYBRID_PQ_CTX`]).
///
/// `signer_positions` are 0-based committee positions (FROST share `p+1`,
/// PQ keypair `p`). Same single-ceremony boundary as [`frost_sign`], and
/// `nonce_seed` has the same freshness obligation; the ML-DSA half signs
/// hedged from OS entropy (FIPS 204 `try_sign`).
pub fn hybrid_sign(
    dealer: &HybridTestDealer,
    signer_positions: &[usize],
    nonce_seed: &[[u8; 64]],
    message: &[u8],
) -> Option<HybridQC> {
    let signers: Vec<&FrostShare> = signer_positions
        .iter()
        .map(|&p| dealer.frost.shares.get(p))
        .collect::<Option<_>>()?;
    let frost = frost_sign(&dealer.frost.group_key, &signers, nonce_seed, message)?;
    let mut pq_sigs = Vec::with_capacity(signer_positions.len());
    for &p in signer_positions {
        let sig = dealer.ml_dsa_keys.get(p)?.sign(message)?;
        pq_sigs.push((p, sig));
    }
    Some(HybridQC { frost, pq_sigs })
}

// =============================================================================
// HERMINE HYBRID — the COMPACT post-quantum half (STAGED reference)
// =============================================================================
//
// `HybridQC` above pays for its quantum safety by weight: the PQ half is one
// FIPS 204 ML-DSA-65 signature (~3.3 KiB) PER signer, so a `t`-of-`n` quorum
// carries `t × 3.3 KiB` of lattice signatures and the verifier can see which
// subset signed. That is the price of ML-DSA having NO threshold aggregation.
//
// `HermineHybridQC` collapses that half. crypto-hermine is a lattice THRESHOLD
// signature (the Raccoon-based FROST-analog, IACR ePrint 2026/419): a t-of-n
// quorum is ONE certificate `(w, c, z)` verified under the federation's Hermine
// GROUP key — committee-INDEPENDENT in size, exactly as `FrostQC` is on the
// classical side. So the PQ half becomes a single ~few-KiB object regardless of
// committee size, and (as with FROST) the verifier cannot tell which subset
// signed. The Lean spec is `Dregg2.Crypto.HermineHybrid`
// (`hermine_hybrid_survives_classical_break`): the hybrid stays quantum-safe by
// reducing to module-SIS at Hermine's verifier, the `hybridVerify = classical ∧
// pq` shape.
//
// ── STAGED-REFERENCE BOUNDARY (read before wiring) ──────────────────────────
// This wires the compact-PQ STRUCTURE — the mechanism, the size collapse, and
// the Lean-backed security shape — NOT a production deployment. crypto-hermine
// is PRE-AUDIT: a toy (non-cryptographic) challenge hash, no formal ROS-hardness
// argument for the lattice instantiation, reference sampling. The ML-DSA
// `HybridVotes` path stays the DEPLOYABLE post-quantum quorum; `HermineHybrid` is
// the compact upgrade to promote once crypto-hermine earns external audit. It is
// exposed behind `QuorumScheme::HermineHybrid`, default-off, wired into NO live
// consensus path.

/// Bytes per serialized Hermine coefficient. Every `R_q` coefficient is
/// `< q = 8380417 < 2²³`, so three bytes are exact (and canonical: `from_bytes`
/// reduces mod `q` defensively).
const HERMINE_COEFF_BYTES: usize = 3;

/// Serialized size of one Hermine `R_q` element (a `Poly`): `N` packed
/// coefficients.
const HERMINE_POLY_BYTES: usize = HERMINE_N * HERMINE_COEFF_BYTES;

/// A HYBRID quorum certificate whose post-quantum half is ONE Hermine threshold
/// certificate — the COMPACT counterpart of [`HybridQC`].
///
/// * `votes` — the classical half: the EXISTING per-member ed25519 vote quorum
///   (`(committee position, signature)` pairs), the same shape live consensus
///   already gathers. No FROST aggregation here; the classical half is the
///   plain vote set, exactly as [`QuorumScheme::HybridVotes`] carries it.
/// * `hermine_cert` — the post-quantum half: a SINGLE
///   [`crypto_hermine::HermineSignature`] `(w, c, z)` under the federation's
///   Hermine group key. Committee-INDEPENDENT — its size is fixed by the lattice
///   parameters (matrix rank `k × ℓ`), NOT by how many signers contributed
///   (contrast [`HybridQC::pq_sigs`], a `Vec` that grows `~3.3 KiB` per signer).
///
/// The Hermine half's THRESHOLD is enforced cryptographically on the signing
/// side (fewer than `t` shares cannot Lagrange-reconstruct the group secret, so
/// no sub-threshold subset produces a cert that verifies under the group key) —
/// exactly like [`FrostQC`]. [`verify_hermine_hybrid`]'s `threshold` argument
/// governs only the CLASSICAL ed25519 vote count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HermineHybridQC {
    /// The classical half: ed25519 vote quorum, `(committee position, sig)`.
    pub votes: Vec<(usize, Signature)>,
    /// The post-quantum half: ONE Hermine threshold certificate under the
    /// group key (committee-independent size).
    pub hermine_cert: HermineSignature,
}

/// Pack one Hermine `Poly` (its `N` coefficients, three bytes each).
fn hermine_poly_to_bytes(p: &HerminePoly, out: &mut Vec<u8>) {
    for &c in &p.coeffs {
        out.extend_from_slice(&c.to_le_bytes()[..HERMINE_COEFF_BYTES]);
    }
}

/// Read one packed Hermine `Poly`; `None` if fewer than [`HERMINE_POLY_BYTES`]
/// remain. Coefficients are reduced mod `q` (canonicalizing any junk input).
fn hermine_poly_from_bytes(rest: &mut &[u8]) -> Option<HerminePoly> {
    let mut coeffs = [0u64; HERMINE_N];
    for c in coeffs.iter_mut() {
        let (head, tail) = rest.split_at_checked(HERMINE_COEFF_BYTES)?;
        *rest = tail;
        let mut buf = [0u8; 8];
        buf[..HERMINE_COEFF_BYTES].copy_from_slice(head);
        *c = u64::from_le_bytes(buf) % HERMINE_Q;
    }
    Some(HerminePoly { coeffs })
}

/// Pack a Hermine `PolyVec`: length prefix `u32 LE`, then each element.
fn hermine_vec_to_bytes(v: &PolyVec, out: &mut Vec<u8>) {
    out.extend_from_slice(&(v.len() as u32).to_le_bytes());
    for p in &v.0 {
        hermine_poly_to_bytes(p, out);
    }
}

/// Read a length-prefixed Hermine `PolyVec`.
fn hermine_vec_from_bytes(rest: &mut &[u8]) -> Option<PolyVec> {
    let (head, tail) = rest.split_at_checked(4)?;
    *rest = tail;
    let len = u32::from_le_bytes(head.try_into().ok()?) as usize;
    // `len` is attacker-controlled: cap the preallocation by what could frame.
    let mut polys = Vec::with_capacity(len.min(rest.len() / HERMINE_POLY_BYTES));
    for _ in 0..len {
        polys.push(hermine_poly_from_bytes(rest)?);
    }
    Some(PolyVec(polys))
}

/// Serialize a [`HermineSignature`] `(w, c, z)` to the compact packed form.
/// This is the POST-QUANTUM half's on-wire size — committee-independent.
pub fn hermine_cert_to_bytes(cert: &HermineSignature) -> Vec<u8> {
    let mut out = Vec::new();
    hermine_vec_to_bytes(&cert.w, &mut out);
    hermine_poly_to_bytes(&cert.c, &mut out);
    hermine_vec_to_bytes(&cert.z, &mut out);
    out
}

/// Deserialize a [`HermineSignature`] from [`hermine_cert_to_bytes`]; leaves
/// `rest` positioned after the certificate. `None` on any framing violation.
fn hermine_cert_from_bytes(rest: &mut &[u8]) -> Option<HermineSignature> {
    let w = hermine_vec_from_bytes(rest)?;
    let c = hermine_poly_from_bytes(rest)?;
    let z = hermine_vec_from_bytes(rest)?;
    Some(HermineSignature { w, c, z })
}

impl HermineHybridQC {
    /// Serialize to the opaque-bytes convention (`dregg_types::ThresholdQC`):
    /// `votes_count(u32 LE) ‖ [pos(u32 LE) ‖ sig(64)]* ‖ hermine_cert`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.votes.len() as u32).to_le_bytes());
        for (pos, sig) in &self.votes {
            out.extend_from_slice(&(*pos as u32).to_le_bytes());
            out.extend_from_slice(&sig.0);
        }
        out.extend_from_slice(&hermine_cert_to_bytes(&self.hermine_cert));
        out
    }

    /// Deserialize; `None` on any framing violation (short header/entry,
    /// truncated certificate, trailing bytes).
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut rest = bytes;
        let take_u32 = |rest: &mut &[u8]| -> Option<u32> {
            let (head, tail) = rest.split_at_checked(4)?;
            *rest = tail;
            Some(u32::from_le_bytes(head.try_into().ok()?))
        };
        let count = take_u32(&mut rest)?;
        // `count` is attacker-controlled: cap the preallocation by what the
        // remaining bytes could frame (≥ 68 bytes per vote entry).
        let mut votes = Vec::with_capacity((count as usize).min(rest.len() / 68));
        for _ in 0..count {
            let pos = take_u32(&mut rest)? as usize;
            let (sig, tail) = rest.split_at_checked(64)?;
            rest = tail;
            votes.push((pos, Signature(sig.try_into().ok()?)));
        }
        let hermine_cert = hermine_cert_from_bytes(&mut rest)?;
        if !rest.is_empty() {
            return None;
        }
        Some(Self {
            votes,
            hermine_cert,
        })
    }

    /// The byte size of the POST-QUANTUM half alone (the single Hermine cert).
    /// Committee-INDEPENDENT: this is the compactness win to compare against
    /// [`HybridQC`]'s `t × ~3.3 KiB` ML-DSA concatenation.
    pub fn pq_half_bytes(&self) -> usize {
        hermine_cert_to_bytes(&self.hermine_cert).len()
    }
}

/// Verify a [`HermineHybridQC`] — the Lean `hybridVerify = classical ∧ pq` at
/// Hermine's verifier (`Dregg2.Crypto.HermineHybrid`).
///
/// Accepts iff BOTH:
/// * **(a) classical** — `qc.votes` carries at least `threshold` entries, EVERY
///   entry names a distinct in-range committee position, and EVERY entry's
///   ed25519 signature verifies over `message` against that position's key in
///   `committee_ed25519`;
/// * **(b) post-quantum** — [`crypto_hermine::verify_hermine`] accepts
///   `qc.hermine_cert` over `message` under the Hermine group key
///   `(hermine_a, hermine_group_key)`.
///
/// STRICT on the classical half exactly as [`verify_pq_quorum_half`] is on the
/// ML-DSA side: any invalid, duplicate, or out-of-range vote rejects the WHOLE
/// certificate, and `threshold == 0` (a vacuous classical half) is refused.
///
/// The `threshold` argument bounds ONLY the ed25519 vote count; the Hermine
/// half's threshold is enforced cryptographically inside `verify_hermine` (a
/// sub-`t` share subset cannot reconstruct a cert that verifies under the group
/// key — the same signing-side guarantee `FrostQC` rests on).
pub fn verify_hermine_hybrid(
    committee_ed25519: &[PublicKey],
    hermine_a: &Matrix,
    hermine_group_key: &PolyVec,
    message: &[u8],
    qc: &HermineHybridQC,
    threshold: usize,
) -> bool {
    // (a) classical half — the ed25519 vote quorum.
    if threshold == 0 {
        return false;
    }
    let mut seen = std::collections::HashSet::new();
    for (pos, sig) in &qc.votes {
        let Some(pk) = committee_ed25519.get(*pos) else {
            return false;
        };
        if !seen.insert(*pos) {
            return false;
        }
        if !pk.verify(message, sig) {
            return false;
        }
    }
    if qc.votes.len() < threshold {
        return false;
    }
    // (b) post-quantum half — the ONE Hermine threshold certificate.
    verify_hermine(hermine_a, hermine_group_key, message, &qc.hermine_cert)
}

/// Decompress a `CompressedEdwardsY` public key — used by tests to sanity-check
/// dealt keys are canonical points.
#[cfg(test)]
fn decompress_pk(pk: &PublicKey) -> Option<EdwardsPoint> {
    curve25519_dalek::edwards::CompressedEdwardsY(pk.0).decompress()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn seeds(n: usize, tag: u8) -> Vec<[u8; 64]> {
        (0..n)
            .map(|i| {
                let mut s = [0u8; 64];
                s[0] = tag;
                s[1] = i as u8;
                s[2] = 0x5a;
                s
            })
            .collect()
    }

    fn dealer_4_of_3() -> FrostTestDealer {
        FrostTestDealer::deal(4, 3, &seeds(3, 1)).unwrap()
    }

    #[test]
    fn frost_qc_signs_and_verifies_under_group_key() {
        let d = dealer_4_of_3();
        assert!(decompress_pk(&d.group_key).is_some());
        let message = b"dregg-federation-vote-v1:frost";
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 2), message).unwrap();
        assert!(verify_frost_quorum(&d.group_key, message, &qc));
    }

    #[test]
    fn wrong_message_fails() {
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 3), b"correct").unwrap();
        assert!(!verify_frost_quorum(&d.group_key, b"wrong", &qc));
    }

    #[test]
    fn sub_threshold_subset_cannot_forge() {
        // 2 shares of a t=3 sharing Lagrange-interpolate a DIFFERENT degree-1
        // polynomial's value at 0, not the group secret: the cert must fail.
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = d.shares[0..2].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(2, 4), b"m").unwrap();
        assert!(!verify_frost_quorum(&d.group_key, b"m", &qc));
    }

    #[test]
    fn any_t_subset_verifies_and_certificate_is_subset_independent_in_size() {
        let d = dealer_4_of_3();
        let message = b"subset independence";
        let s013: Vec<&FrostShare> = [0, 1, 3].iter().map(|&i| &d.shares[i]).collect();
        let s123: Vec<&FrostShare> = [1, 2, 3].iter().map(|&i| &d.shares[i]).collect();
        let all: Vec<&FrostShare> = d.shares.iter().collect();
        let qc_a = frost_sign(&d.group_key, &s013, &seeds(3, 5), message).unwrap();
        let qc_b = frost_sign(&d.group_key, &s123, &seeds(3, 6), message).unwrap();
        let qc_c = frost_sign(&d.group_key, &all, &seeds(4, 7), message).unwrap();
        for qc in [&qc_a, &qc_b, &qc_c] {
            assert!(verify_frost_quorum(&d.group_key, message, qc));
            assert_eq!(qc.to_bytes().len(), FROST_QC_BYTES);
        }
        // Different ceremonies, different certs — but the verifier can't tell
        // which subset signed.
        assert_ne!(qc_a, qc_b);
    }

    #[test]
    fn frost_qc_is_a_plain_ed25519_signature() {
        // The dregg_types verifier path (used everywhere for vote sigs)
        // accepts the FROST certificate as-is under the group key.
        let d = dealer_4_of_3();
        let message = b"plain ed25519 compatibility";
        let signers: Vec<&FrostShare> = d.shares[1..4].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 8), message).unwrap();
        assert!(d.group_key.verify(message, &qc.signature));
    }

    #[test]
    fn serialization_round_trips() {
        let d = dealer_4_of_3();
        let message = b"round trip";
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 9), message).unwrap();
        let qc2 = FrostQC::from_bytes(&qc.to_bytes()).unwrap();
        assert_eq!(qc, qc2);
        assert!(verify_frost_quorum(&d.group_key, message, &qc2));
        assert!(FrostQC::from_bytes(&[0u8; 63]).is_none());
        assert!(FrostQC::from_bytes(&[0u8; 65]).is_none());
    }

    #[test]
    fn scheme_selector_dispatches_frost_and_rejects_cross_scheme_bytes() {
        let d = dealer_4_of_3();
        let message = b"selector";
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 10), message).unwrap();
        let opaque = dregg_types::ThresholdQC(qc.to_bytes());

        let scheme = QuorumScheme::Frost {
            group_key: d.group_key,
        };
        assert!(scheme.verify_opaque_qc(&opaque.0, message));
        assert!(!scheme.verify_opaque_qc(&opaque.0, b"other message"));

        // BLS-shaped bytes (wrong length / garbage) under the Frost arm: reject.
        assert!(!scheme.verify_opaque_qc(&[0xAB; 48], message));
    }

    #[test]
    fn scheme_selector_bls_arm_still_verifies_bls() {
        // Both schemes valid side by side: the SAME opaque-bytes seam
        // dispatches to the incumbent BLS committee verify unchanged.
        let (committee, members) = crate::threshold::generate_test_committee(4, 3).unwrap();
        let message = b"bls via selector";
        let shares: Vec<(usize, crate::threshold::PartialSignature)> = members[0..3]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, message)))
            .collect();
        let bls_qc = committee.aggregate(&shares, message).unwrap();
        let opaque = dregg_types::ThresholdQC(bls_qc.to_bytes());

        let scheme = QuorumScheme::Bls(&committee);
        assert!(scheme.verify_opaque_qc(&opaque.0, message));
        assert!(!scheme.verify_opaque_qc(&opaque.0, b"tampered"));

        // FROST bytes under the BLS arm: reject.
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let fqc = frost_sign(&d.group_key, &signers, &seeds(3, 11), message).unwrap();
        assert!(!scheme.verify_opaque_qc(&fqc.to_bytes(), message));
    }

    #[test]
    fn nonce_seed_shorter_than_signers_is_refused() {
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        assert!(frost_sign(&d.group_key, &signers, &seeds(2, 12), b"m").is_none());
    }

    #[test]
    fn duplicate_signer_is_refused() {
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = vec![&d.shares[0], &d.shares[0], &d.shares[1]];
        assert!(frost_sign(&d.group_key, &signers, &seeds(3, 13), b"m").is_none());
    }

    // =========================================================================
    // HYBRID (FROST + ML-DSA-65) tests
    // =========================================================================

    fn pq_seeds(n: usize, tag: u8) -> Vec<[u8; 32]> {
        (0..n)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = tag;
                s[1] = i as u8;
                s[2] = 0xa5;
                s
            })
            .collect()
    }

    fn hybrid_dealer_4_of_3() -> HybridTestDealer {
        HybridTestDealer::deal(4, 3, &seeds(3, 20), &pq_seeds(4, 21)).unwrap()
    }

    /// The simulated QUANTUM ADVERSARY: solve the group key's discrete log
    /// (stood in for by Lagrange-reconstructing the secret from `t` shares —
    /// the test is omniscient so it can realize exactly what Shor's would
    /// yield: the group secret scalar) and single-signer Schnorr-sign any
    /// message of the attacker's choosing. The output PASSES
    /// [`verify_frost_quorum`] — a genuine break of the classical half.
    fn quantum_break_forge_frost(d: &FrostTestDealer, message: &[u8]) -> FrostQC {
        let t = d.threshold as usize;
        let parts: Vec<u64> = d.shares[..t].iter().map(|s| s.index).collect();
        let group_secret: Scalar = d.shares[..t]
            .iter()
            .map(|s| lagrange_at_zero(s.index, &parts) * s.share)
            .sum();
        let k = Scalar::from_bytes_mod_order_wide(&{
            let mut s = [0u8; 64];
            s[0] = 0xfe;
            s
        });
        let r_compressed = EdwardsPoint::mul_base(&k).compress().to_bytes();
        let e = ed25519_challenge(&r_compressed, &d.group_key, message);
        let z = k + e * group_secret;
        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(&r_compressed);
        sig[32..].copy_from_slice(z.as_bytes());
        FrostQC {
            signature: Signature(sig),
        }
    }

    #[test]
    fn hybrid_honest_qc_verifies_both_halves() {
        let d = hybrid_dealer_4_of_3();
        let message = b"dregg-federation-vote-v1:hybrid";
        let qc = hybrid_sign(&d, &[0, 1, 2], &seeds(3, 22), message).unwrap();
        // The classical half alone verifies…
        assert!(verify_frost_quorum(&d.frost.group_key, message, &qc.frost));
        // …and so does the whole hybrid certificate.
        assert!(verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &qc,
            3
        ));
        // Neither half accepts a different message.
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            b"other",
            &qc,
            3
        ));
    }

    #[test]
    fn hybrid_corrupted_frost_half_is_rejected() {
        let d = hybrid_dealer_4_of_3();
        let message = b"corrupt the classical half";
        let mut qc = hybrid_sign(&d, &[1, 2, 3], &seeds(3, 23), message).unwrap();
        qc.frost.signature.0[40] ^= 0x01; // flip one bit of z
        assert!(!verify_frost_quorum(&d.frost.group_key, message, &qc.frost));
        // The PQ half is untouched and honest — the QC must STILL be rejected.
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &qc,
            3
        ));
    }

    #[test]
    fn hybrid_corrupted_or_missing_ml_dsa_sig_is_rejected() {
        let d = hybrid_dealer_4_of_3();
        let message = b"corrupt the pq half";
        let qc = hybrid_sign(&d, &[0, 1, 3], &seeds(3, 24), message).unwrap();

        // Corrupted: one flipped byte in one ML-DSA signature.
        let mut corrupted = qc.clone();
        corrupted.pq_sigs[1].1[100] ^= 0x01;
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &corrupted,
            3
        ));

        // Missing: one signature dropped leaves 2 < threshold 3.
        let mut missing = qc.clone();
        missing.pq_sigs.remove(2);
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &missing,
            3
        ));

        // Wrong-length signature bytes.
        let mut truncated = qc;
        truncated.pq_sigs[0]
            .1
            .truncate(dregg_pq::ML_DSA_SIG_LEN - 1);
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &truncated,
            3
        ));
    }

    #[test]
    fn hybrid_survives_classical_break() {
        // THE QUANTUM-SAFETY TEST (the Lean `hybrid_survives_classical_break`):
        // an adversary who fully breaks ed25519 forges a VALID FROST half on a
        // malicious message and grafts on the only ML-DSA signatures in
        // existence — honest ones over the honest message. The PQ half catches
        // the substitution and the hybrid certificate is REJECTED.
        let d = hybrid_dealer_4_of_3();
        let honest_msg = b"honest state root";
        let malicious_msg = b"attacker's state root";
        let honest_qc = hybrid_sign(&d, &[0, 1, 2], &seeds(3, 25), honest_msg).unwrap();

        let forged_frost = quantum_break_forge_frost(&d.frost, malicious_msg);
        // The classical break is GENUINE: the forged half verifies under the
        // group key on the attacker's message.
        assert!(verify_frost_quorum(
            &d.frost.group_key,
            malicious_msg,
            &forged_frost
        ));

        let forged_qc = HybridQC {
            frost: forged_frost,
            pq_sigs: honest_qc.pq_sigs.clone(),
        };
        // …but the hybrid verifier still refuses it: no ML-DSA signature over
        // the malicious message exists.
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            malicious_msg,
            &forged_qc,
            3
        ));
    }

    #[test]
    fn hybrid_sub_threshold_pq_count_is_rejected() {
        let d = hybrid_dealer_4_of_3();
        let message = b"sub-threshold pq";
        let qc = hybrid_sign(&d, &[0, 1, 2], &seeds(3, 26), message).unwrap();
        // Keep only 2 of the 3 (all still individually VALID) — below t=3.
        let mut sub = qc.clone();
        sub.pq_sigs.truncate(2);
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &sub,
            3
        ));
        // A duplicate cannot pad the count back up.
        let mut padded = sub.clone();
        padded.pq_sigs.push(padded.pq_sigs[0].clone());
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &padded,
            3
        ));
        // Nor can an out-of-range index.
        let mut oob = sub;
        oob.pq_sigs.push((7, vec![0u8; dregg_pq::ML_DSA_SIG_LEN]));
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &oob,
            3
        ));
        // And threshold 0 (a vacuous PQ half) is refused outright.
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &qc,
            0
        ));
    }

    /// The enrolled ML-DSA roster must be pairwise DISTINCT: one PQ authority
    /// cannot occupy multiple committee slots. This is the distinct-roster
    /// contract `receipt::verify_hybrid_quorum_sigs` enforces, applied at the
    /// SHARED PQ-half seam BOTH hybrid carriers route through (the FROST
    /// `verify_hybrid_quorum` and the ed25519 `HybridQuorumCertificate`). The
    /// check covers the WHOLE roster — not just this certificate's subset — so
    /// a threshold-1 subset cannot make a duplicate enrollment valid.
    #[test]
    fn hybrid_duplicate_enrolled_pq_roster_is_refused() {
        let (p0, sk0) = MlDsaSigningKey::from_seed(&[0xA3; 32]);
        let (p1, sk1) = MlDsaSigningKey::from_seed(&[0xA4; 32]);
        let message = b"duplicate enrolled PQ roster";
        let sig0 = sk0.sign(message).expect("ML-DSA signs");

        // Control: an honest DISTINCT roster verifies at threshold 2.
        let distinct = vec![p0.clone(), p1.clone()];
        let honest = vec![(0usize, sig0.clone()), (1usize, sk1.sign(message).unwrap())];
        assert!(verify_pq_quorum_half(&distinct, message, &honest, 2));

        // A DUPLICATE enrolled roster refuses at threshold 2 even though the
        // reused signature sits at two DISTINCT positions under two distinct
        // (here, one) classical halves…
        let dup = vec![p0.clone(), p0.clone()];
        let reused = vec![(0usize, sig0.clone()), (1usize, sig0.clone())];
        assert!(
            !verify_pq_quorum_half(&dup, message, &reused, 2),
            "a duplicate enrolled ML-DSA key must not fill two PQ positions (t=2)"
        );
        // …and at threshold 1: the WHOLE roster is checked, so a one-entry
        // subset cannot make the duplicate enrollment valid.
        assert!(
            !verify_pq_quorum_half(&dup, message, &reused[..1], 1),
            "a duplicate enrolled roster refuses even at threshold 1"
        );
    }

    /// The FROST-carried hybrid verifier routes its PQ half through the same
    /// shared seam: a GENUINE classical aggregate cannot rescue a duplicated
    /// enrolled roster.
    #[test]
    fn hybrid_frost_carrier_refuses_duplicate_enrolled_roster() {
        let d = hybrid_dealer_4_of_3();
        let message = b"frost carrier, duplicate roster";
        let qc = hybrid_sign(&d, &[0, 1, 2], &seeds(3, 29), message).unwrap();
        // The classical half is genuine.
        assert!(verify_frost_quorum(&d.frost.group_key, message, &qc.frost));
        // One ML-DSA key (member 0's), signing once, placed at THREE positions.
        let one = d.ml_dsa_keys[0].sign(message).expect("ML-DSA signs");
        let aliased = HybridQC {
            frost: qc.frost.clone(),
            pq_sigs: vec![(0, one.clone()), (1, one.clone()), (2, one)],
        };
        // A roster that enrols that ONE key at all three of those positions.
        let mut dup_roster = d.ml_dsa_pubkeys.clone();
        dup_roster[1] = dup_roster[0].clone();
        dup_roster[2] = dup_roster[0].clone();
        assert!(
            !verify_hybrid_quorum(&d.frost.group_key, &dup_roster, message, &aliased, 3),
            "a duplicated enrolled roster must refuse the hybrid quorum"
        );
        // The honest distinct roster still verifies the honest certificate.
        assert!(verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &qc,
            3
        ));
    }

    #[test]
    fn hybrid_serialization_round_trips_and_selector_dispatches() {
        let d = hybrid_dealer_4_of_3();
        let message = b"hybrid selector";
        let qc = hybrid_sign(&d, &[1, 2, 3], &seeds(3, 27), message).unwrap();

        // Opaque-bytes round trip.
        let bytes = qc.to_bytes();
        let qc2 = HybridQC::from_bytes(&bytes).unwrap();
        assert_eq!(qc, qc2);

        // Framing violations reject.
        assert!(HybridQC::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(HybridQC::from_bytes(&trailing).is_none());
        assert!(HybridQC::from_bytes(&[0u8; 63]).is_none());

        // The scheme selector dispatches the hybrid arm over the same
        // opaque-bytes seam as BLS and FROST.
        let opaque = dregg_types::ThresholdQC(bytes);
        let scheme = QuorumScheme::Hybrid {
            group_key: d.frost.group_key,
            ml_dsa_pubkeys: &d.ml_dsa_pubkeys,
            threshold: 3,
        };
        assert!(scheme.verify_opaque_qc(&opaque.0, message));
        assert!(!scheme.verify_opaque_qc(&opaque.0, b"other message"));
        // A bare FROST cert's bytes are NOT a hybrid cert.
        let fqc = frost_sign(
            &d.frost.group_key,
            &d.frost.shares[0..3].iter().collect::<Vec<_>>(),
            &seeds(3, 28),
            message,
        )
        .unwrap();
        assert!(!scheme.verify_opaque_qc(&fqc.to_bytes(), message));
    }

    // =========================================================================
    // HERMINE HYBRID (ed25519 votes + ONE Hermine threshold cert) tests
    // =========================================================================
    //
    // The COMPACT-PQ structure: the post-quantum half is a SINGLE Hermine
    // threshold certificate (committee-independent), not ML-DSA's per-signer
    // Vec. STAGED reference — crypto-hermine is pre-audit.

    use crypto_hermine::{HermineShare, HermineTestDealer, hermine_sign};

    /// The Hermine lattice parameters used by these tests: `k = 2`, `ℓ = 3`.
    /// The certificate size is fixed by THESE, independent of committee size.
    const HERMINE_ROWS: usize = 2;
    const HERMINE_COLS: usize = 3;

    /// Build an `n`-member ed25519 committee (deterministic keys) and the
    /// signing keys behind it.
    fn ed25519_committee(n: usize) -> (Vec<dregg_types::SigningKey>, Vec<PublicKey>) {
        let mut sks = Vec::with_capacity(n);
        let mut pks = Vec::with_capacity(n);
        for i in 0..n {
            let mut seed = [0u8; 32];
            seed[0] = 0x7e;
            seed[1] = i as u8;
            let sk = dregg_types::SigningKey::from_bytes(&seed);
            pks.push(sk.public_key());
            sks.push(sk);
        }
        (sks, pks)
    }

    /// Produce a HermineHybridQC: `t` ed25519 votes over `message` from the
    /// first `t` members PLUS one Hermine threshold cert from the first `t`
    /// Hermine shares (via the production-shaped binding-factor ceremony).
    fn hermine_hybrid_qc(
        sks: &[dregg_types::SigningKey],
        dealer: &HermineTestDealer,
        t: usize,
        mask_seed: u64,
        message: &[u8],
    ) -> HermineHybridQC {
        let votes: Vec<(usize, Signature)> = (0..t)
            .map(|i| (i, dregg_types::sign(&sks[i], message)))
            .collect();
        let signers: Vec<&HermineShare> = dealer.shares[0..t].iter().collect();
        let hermine_cert =
            hermine_sign(&dealer.a, &dealer.group_key, &signers, mask_seed, message).unwrap();
        HermineHybridQC {
            votes,
            hermine_cert,
        }
    }

    #[test]
    fn hermine_hybrid_honest_qc_verifies_both_halves() {
        let n = 4;
        let t = 3;
        let (sks, pks) = ed25519_committee(n);
        let d =
            HermineTestDealer::deal(HERMINE_ROWS, HERMINE_COLS, n as u64, t as u64, 0xABCD_0001)
                .unwrap();
        let message = b"dregg-federation-vote-v1:hermine-hybrid";
        let qc = hermine_hybrid_qc(&sks, &d, t, 0x5151, message);

        // Both halves accept the honest certificate.
        assert!(verify_hermine_hybrid(
            &pks,
            &d.a,
            &d.group_key,
            message,
            &qc,
            t
        ));
        // The Hermine half alone verifies (the classical/pq split is real).
        assert!(verify_hermine(
            &d.a,
            &d.group_key,
            message,
            &qc.hermine_cert
        ));
        // Neither half accepts a different message.
        assert!(!verify_hermine_hybrid(
            &pks,
            &d.a,
            &d.group_key,
            b"other message",
            &qc,
            t
        ));
    }

    #[test]
    fn hermine_hybrid_forged_pq_is_rejected() {
        // THE PQ TEETH: a valid ed25519 quorum cannot carry a bad Hermine cert.
        let n = 4;
        let t = 3;
        let (sks, pks) = ed25519_committee(n);
        let d =
            HermineTestDealer::deal(HERMINE_ROWS, HERMINE_COLS, n as u64, t as u64, 0xABCD_0002)
                .unwrap();
        let message = b"dregg-federation-vote-v1:hermine-hybrid-forge";
        let qc = hermine_hybrid_qc(&sks, &d, t, 0x6262, message);

        // Tamper the Hermine response `z` (one coefficient) — the cert no longer
        // satisfies `A·z = w + c·t`.
        let mut tampered = qc.clone();
        tampered.hermine_cert.z.0[0] = tampered.hermine_cert.z.0[0].add(&HerminePoly::constant(1));
        assert!(!verify_hermine(
            &d.a,
            &d.group_key,
            message,
            &tampered.hermine_cert
        ));
        // The ed25519 votes are untouched and honest — yet the whole QC is
        // REJECTED (the Lean `classical ∧ pq`).
        assert!(!verify_hermine_hybrid(
            &pks,
            &d.a,
            &d.group_key,
            message,
            &tampered,
            t
        ));

        // A sub-threshold Hermine signer set cannot forge a verifying cert
        // either: 2 of a t=3 sharing reconstruct the wrong secret.
        let sub_signers: Vec<&HermineShare> = d.shares[0..2].iter().collect();
        let bad_cert = hermine_sign(&d.a, &d.group_key, &sub_signers, 0x7070, message).unwrap();
        let sub_qc = HermineHybridQC {
            votes: qc.votes.clone(),
            hermine_cert: bad_cert,
        };
        assert!(!verify_hermine_hybrid(
            &pks,
            &d.a,
            &d.group_key,
            message,
            &sub_qc,
            t
        ));
    }

    #[test]
    fn hermine_hybrid_sub_threshold_ed25519_is_rejected() {
        let n = 4;
        let t = 3;
        let (sks, pks) = ed25519_committee(n);
        let d =
            HermineTestDealer::deal(HERMINE_ROWS, HERMINE_COLS, n as u64, t as u64, 0xABCD_0003)
                .unwrap();
        let message = b"dregg-federation-vote-v1:hermine-hybrid-subthreshold";
        // A perfectly valid Hermine cert, but only 2 ed25519 votes below t = 3.
        let mut qc = hermine_hybrid_qc(&sks, &d, t, 0x8383, message);
        qc.votes.truncate(2);
        assert!(verify_hermine(
            &d.a,
            &d.group_key,
            message,
            &qc.hermine_cert
        ));
        assert!(!verify_hermine_hybrid(
            &pks,
            &d.a,
            &d.group_key,
            message,
            &qc,
            t
        ));
        // A duplicate vote cannot pad the count back to threshold.
        let mut padded = qc.clone();
        padded.votes.push(padded.votes[0]);
        assert!(!verify_hermine_hybrid(
            &pks,
            &d.a,
            &d.group_key,
            message,
            &padded,
            t
        ));
        // An out-of-range committee position is rejected outright.
        let mut oob = qc.clone();
        oob.votes.push((99, dregg_types::sign(&sks[0], message)));
        assert!(!verify_hermine_hybrid(
            &pks,
            &d.a,
            &d.group_key,
            message,
            &oob,
            t
        ));
        // And threshold 0 (a vacuous classical half) is refused.
        let full = hermine_hybrid_qc(&sks, &d, t, 0x8484, message);
        assert!(!verify_hermine_hybrid(
            &pks,
            &d.a,
            &d.group_key,
            message,
            &full,
            0
        ));
    }

    #[test]
    fn hermine_hybrid_serialization_round_trips_and_selector_dispatches() {
        let n = 4;
        let t = 3;
        let (sks, pks) = ed25519_committee(n);
        let d =
            HermineTestDealer::deal(HERMINE_ROWS, HERMINE_COLS, n as u64, t as u64, 0xABCD_0004)
                .unwrap();
        let message = b"hermine hybrid selector";
        let qc = hermine_hybrid_qc(&sks, &d, t, 0x9595, message);

        // Opaque-bytes round trip.
        let bytes = qc.to_bytes();
        let qc2 = HermineHybridQC::from_bytes(&bytes).unwrap();
        assert_eq!(qc, qc2);

        // Framing violations reject.
        assert!(HermineHybridQC::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(HermineHybridQC::from_bytes(&trailing).is_none());

        // The scheme selector dispatches the HermineHybrid arm over the same
        // opaque-bytes seam as BLS / FROST / Hybrid / HybridVotes.
        let opaque = dregg_types::ThresholdQC(bytes);
        let scheme = QuorumScheme::HermineHybrid {
            members: &pks,
            hermine_a: &d.a,
            hermine_group_key: &d.group_key,
            threshold: t,
        };
        assert!(scheme.verify_opaque_qc(&opaque.0, message));
        assert!(!scheme.verify_opaque_qc(&opaque.0, b"other message"));
        // A bare FROST cert's bytes are not a HermineHybrid cert.
        assert!(!scheme.verify_opaque_qc(&[0xAB; 64], message));
    }

    #[test]
    fn hermine_hybrid_pq_half_is_compact_and_committee_independent() {
        // THE COMPACTNESS WIN. crypto-hermine is a THRESHOLD scheme, so the PQ
        // half is ONE cert regardless of committee size — vs ML-DSA's `t` × one
        // ~3.3 KiB signature per signer.
        let (sks, pks) = ed25519_committee(8);

        // The Hermine PQ half at t = 3 …
        let d3 = HermineTestDealer::deal(HERMINE_ROWS, HERMINE_COLS, 8, 3, 0xABCD_0005).unwrap();
        let qc3 = hermine_hybrid_qc(&sks, &d3, 3, 0xA1A1, b"m");
        let hermine_pq = qc3.pq_half_bytes();

        // … and at t = 6 (double the signing subset): IDENTICAL byte size.
        let d6 = HermineTestDealer::deal(HERMINE_ROWS, HERMINE_COLS, 8, 6, 0xABCD_0006).unwrap();
        let qc6 = hermine_hybrid_qc(&sks, &d6, 6, 0xA2A2, b"m");
        assert_eq!(
            qc6.pq_half_bytes(),
            hermine_pq,
            "Hermine PQ half must be committee-independent"
        );
        let _ = &pks;

        // The ML-DSA HybridQC PQ half GROWS with the signing subset: one ML-DSA-65
        // signature (~3.3 KiB) per signer.
        let hd = HybridTestDealer::deal(8, 6, &seeds(6, 40), &pq_seeds(8, 41)).unwrap();
        let ml_dsa_qc_t3 = hybrid_sign(&hd, &[0, 1, 2], &seeds(3, 42), b"m").unwrap();
        let ml_dsa_qc_t6 = hybrid_sign(&hd, &[0, 1, 2, 3, 4, 5], &seeds(6, 43), b"m").unwrap();
        let ml_dsa_pq_t3: usize = ml_dsa_qc_t3.pq_sigs.iter().map(|(_, s)| s.len()).sum();
        let ml_dsa_pq_t6: usize = ml_dsa_qc_t6.pq_sigs.iter().map(|(_, s)| s.len()).sum();

        // The collapse: ONE Hermine cert < the t-signer ML-DSA concatenation,
        // and the gap only widens with committee size.
        println!(
            "PQ-half bytes — Hermine (any t): {hermine_pq}  |  ML-DSA t=3: {ml_dsa_pq_t3}  ML-DSA t=6: {ml_dsa_pq_t6}"
        );
        assert!(
            hermine_pq < ml_dsa_pq_t3,
            "one Hermine cert ({hermine_pq}) must beat t=3 ML-DSA ({ml_dsa_pq_t3})"
        );
        assert!(
            ml_dsa_pq_t6 > ml_dsa_pq_t3,
            "ML-DSA half grows with the subset"
        );
        assert!(
            ml_dsa_pq_t6 > 3 * hermine_pq,
            "at t=6 the ML-DSA half ({ml_dsa_pq_t6}) dwarfs the fixed Hermine cert ({hermine_pq})"
        );
        // Sanity on the fixed Hermine size: (k + 1 + ℓ) packed R_q elements plus
        // two u32 length prefixes (w and z; the challenge c is a bare Poly).
        let expected = (HERMINE_ROWS + 1 + HERMINE_COLS) * HERMINE_POLY_BYTES + 2 * 4;
        assert_eq!(hermine_pq, expected);
    }
}
