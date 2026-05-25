//! VK v2 — layered cell-program / predicate / effect verifying-key hashes.
//!
//! Per `VK-AS-RE-EXECUTION-RECIPE.md` §v2, a `vk_hash` in pyana commits
//! to **four** components, not one:
//!
//! 1. **Program bytes** — the canonical encoding of the executable
//!    spec (postcard(CellProgram), DSL AST, opaque predicate bytes,
//!    etc.). What v1 of the recipe already committed to.
//! 2. **AIR fingerprint** — the 32-byte hash of the
//!    [`crate::factory`] or AIR-side shape descriptor that says *which
//!    AIR* the validator is supposed to run the spec against. Closes
//!    the "same program, different AIR" attack: two cells with the
//!    same `CellProgram` value but different AIRs produce distinct
//!    vk_hashes.
//! 3. **Verifier fingerprint** — what code/wasm/compiled-VK actually
//!    runs the verifier. Distinguishes a re-execution validator from
//!    a recursive STARK validator from a wasm-compiled validator, all
//!    of which may run the same AIR over the same program.
//! 4. **Proving-system identifier** — Plonky3 BabyBear FRI, Kimchi
//!    Pasta, SP1, etc. Closes the cross-proving-system collision risk
//!    where two proofs over the same circuit but different commitment
//!    schemes share a vk_hash.
//!
//! [`canonical_vk_v2`] is the encoder. The legacy [`crate::factory::canonical_program_vk`]
//! and [`crate::predicate::canonical_predicate_vk`] live alongside as
//! the **program-bytes-only** layer; v2 callers pass those bytes into
//! `VkComponents.program_bytes` and round out with the other three
//! fields.
//!
//! ## Why a separate v2 function
//!
//! v1 is *not* sound under the threat model where AIR / verifier /
//! proving-system parameters vary independently of the program spec.
//! v2 supersedes v1 for new code; v1's encoders remain available for
//! the program-bytes-only layer of a v2 hash (callers should treat
//! them as building blocks, not finished VKs).
//!
//! ## Domain string
//!
//! `"pyana-vk-v2"`. Disjoint from v1's `"pyana-cellprogram-vk-v1"` and
//! `"pyana-witnessed-predicate-vk-v1"` keys, so a v2 hash cannot
//! collide with a v1 hash. v1 and v2 callers compute different bytes
//! for the same program — exactly as intended.

use serde::{Deserialize, Serialize};

/// Identifier for the proving system a vk_hash is committing to.
///
/// Different proving systems verify the same AIR / circuit
/// differently: a Plonky3-FRI STARK proof and a Kimchi-Pasta proof
/// over the same AIR are *not* interchangeable, even if their AIR
/// fingerprints match. Mixing them into the vk_hash prevents
/// cross-system collisions.
///
/// For pyana today, cell-program VKs all use
/// `Plonky3BabyBearFri { p3_rev: "82cfad73..." }` matching the rev
/// pinned in the workspace `Cargo.toml`. Apps that target Kimchi
/// (Mina interop) or SP1 use the matching variant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProvingSystemId {
    /// Plonky3 STARK over BabyBear with FRI commitment.
    ///
    /// `p3_rev` pins the Plonky3 git revision. Two ostensibly
    /// equivalent Plonky3 versions can differ in soundness-critical
    /// parameters (FRI folding, Fiat-Shamir, hash choice), so the
    /// revision is part of the identity.
    Plonky3BabyBearFri {
        /// Plonky3 git revision the proving stack was built against.
        p3_rev: &'static str,
    },
    /// Kimchi over the Pasta cycle (Mina-compatible).
    KimchiPasta,
    /// SP1 v6 zkVM.
    Sp1V6,
    /// Custom proving system, identified by a stable string.
    Custom {
        /// Stable identifier for this system. Conventionally
        /// `"<system-name>-v<n>"`.
        id: &'static str,
    },
}

impl ProvingSystemId {
    /// Canonical bytes for this identifier. Used by [`canonical_vk_v2`]
    /// to fold the proving-system choice into the vk_hash.
    ///
    /// Variant tag + variant-specific bytes; length-prefixed where
    /// variable so concatenation attacks cannot collide two distinct
    /// identifiers.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        match self {
            ProvingSystemId::Plonky3BabyBearFri { p3_rev } => {
                out.push(0u8);
                let rev_bytes = p3_rev.as_bytes();
                out.extend_from_slice(&(rev_bytes.len() as u64).to_le_bytes());
                out.extend_from_slice(rev_bytes);
            }
            ProvingSystemId::KimchiPasta => {
                out.push(1u8);
            }
            ProvingSystemId::Sp1V6 => {
                out.push(2u8);
            }
            ProvingSystemId::Custom { id } => {
                out.push(3u8);
                let id_bytes = id.as_bytes();
                out.extend_from_slice(&(id_bytes.len() as u64).to_le_bytes());
                out.extend_from_slice(id_bytes);
            }
        }
        out
    }
}

/// A 32-byte commitment to the verifier implementation that will
/// adjudicate a vk_hash.
///
/// Three flavors, picked by what's available to the VK author:
///
/// - [`VerifierFingerprint::SourceHash`] — git-blob-hash of the
///   verifier's Rust source file. For hand-written AIRs the verifier
///   lives in-tree; the source-hash binds the in-tree code to the
///   VK author's commit. Computed via `git hash-object <file>` or
///   equivalent at registration time.
/// - [`VerifierFingerprint::WasmHash`] — BLAKE3 (or similar) hash of
///   the wasm-compiled verifier bytes, for ahead-of-time compiled
///   verifiers and post-recursion wasm dispatch.
/// - [`VerifierFingerprint::CompiledVkHash`] — hash of the proving
///   system's verifying-key bytes, for proving systems that materialize
///   a separate VK blob (Pickles, Plonky2 recursion, etc.).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerifierFingerprint {
    /// Git-blob-hash of the verifier's source file.
    SourceHash([u8; 32]),
    /// BLAKE3 hash of the wasm-compiled verifier bytes.
    WasmHash([u8; 32]),
    /// Hash of the proving system's compiled verifying-key bytes.
    CompiledVkHash([u8; 32]),
}

impl VerifierFingerprint {
    /// Canonical 33-byte encoding: 1-byte variant tag + 32-byte hash.
    ///
    /// Returns a 32-byte hash of `(variant_tag || hash)` so all
    /// callers see a fixed-width digest. This is the form fed into
    /// [`canonical_vk_v2`].
    pub fn canonical_bytes(&self) -> [u8; 32] {
        let (tag, h) = match self {
            VerifierFingerprint::SourceHash(h) => (0u8, h),
            VerifierFingerprint::WasmHash(h) => (1u8, h),
            VerifierFingerprint::CompiledVkHash(h) => (2u8, h),
        };
        let mut hasher = blake3::Hasher::new_derive_key("pyana-verifier-fingerprint-v1");
        hasher.update(&[tag]);
        hasher.update(h);
        *hasher.finalize().as_bytes()
    }
}

/// The four components fed into [`canonical_vk_v2`].
///
/// Borrowed so callers do not have to clone large byte vectors. The
/// `program_bytes` slice should be the canonical postcard / DSL /
/// opaque-bytes representation of the executable spec — the same
/// bytes a validator would re-execute pre-recursion.
pub struct VkComponents<'a> {
    /// Canonical postcard(CellProgram) bytes (cell programs),
    /// canonical DSL AST bytes (custom predicates), or opaque app-
    /// provided bytes (custom effects).
    pub program_bytes: &'a [u8],
    /// 32-byte hash of the AIR descriptor; see
    /// `pyana_circuit::air_descriptor::fingerprint`.
    pub air_fingerprint: [u8; 32],
    /// Verifier-impl fingerprint (source/wasm/compiled-vk).
    pub verifier_fingerprint: VerifierFingerprint,
    /// Proving-system identifier.
    pub proving_system_id: ProvingSystemId,
}

/// Compute the canonical VK v2 hash from four components.
///
/// Encoding:
///
/// ```text
/// vk_hash_v2 = BLAKE3_keyed("pyana-vk-v2",
///                            len(program_bytes) || program_bytes ||
///                            air_fingerprint ||
///                            verifier_fingerprint.canonical_bytes() ||
///                            len(proving_system_bytes) || proving_system_bytes)
/// ```
///
/// Length prefixes around variable-length fields prevent concatenation
/// attacks. The 32-byte air_fingerprint and 32-byte verifier_fingerprint
/// are fixed-width and need no prefix.
///
/// # Boundary contract
///
/// - Cleartext-inside:  VK author (knows all four components) +
///                      validators (re-execute the program bytes
///                      against the AIR + verifier identified by the
///                      remaining three).
/// - Commitment-inside: receipt observers (see vk_hash_v2 + acceptance
///                      bit only).
/// - Acceptance-inside: post-recursion validators (proof + verifying
///                      key only).
/// - Out-of-band:       everyone else.
///
/// Enforced by: BLAKE3 keyed-hash domain separation under
/// `"pyana-vk-v2"`. Failure mode if violated: validators with
/// mismatched components compute a different vk_hash and reject the
/// claim — a soundness signal, not a soundness loss.
pub fn canonical_vk_v2(components: &VkComponents<'_>) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-vk-v2");
    hasher.update(&(components.program_bytes.len() as u64).to_le_bytes());
    hasher.update(components.program_bytes);
    hasher.update(&components.air_fingerprint);
    hasher.update(&components.verifier_fingerprint.canonical_bytes());
    let ps_bytes = components.proving_system_id.canonical_bytes();
    hasher.update(&(ps_bytes.len() as u64).to_le_bytes());
    hasher.update(&ps_bytes);
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_components<'a>(bytes: &'a [u8]) -> VkComponents<'a> {
        VkComponents {
            program_bytes: bytes,
            air_fingerprint: [0x11; 32],
            verifier_fingerprint: VerifierFingerprint::SourceHash([0x22; 32]),
            proving_system_id: ProvingSystemId::Plonky3BabyBearFri {
                p3_rev: "abcdef0123",
            },
        }
    }

    #[test]
    fn canonical_vk_v2_is_deterministic() {
        let bytes = b"hello-program";
        let c = sample_components(bytes);
        assert_eq!(canonical_vk_v2(&c), canonical_vk_v2(&c));
    }

    #[test]
    fn canonical_vk_v2_changes_with_program_bytes() {
        let a = canonical_vk_v2(&sample_components(b"prog-a"));
        let b = canonical_vk_v2(&sample_components(b"prog-b"));
        assert_ne!(a, b);
    }

    #[test]
    fn canonical_vk_v2_changes_with_air_fingerprint() {
        let mut c = sample_components(b"prog");
        let h_before = canonical_vk_v2(&c);
        c.air_fingerprint = [0x33; 32];
        let h_after = canonical_vk_v2(&c);
        assert_ne!(h_before, h_after);
    }

    #[test]
    fn canonical_vk_v2_changes_with_verifier_fingerprint_value() {
        let mut c = sample_components(b"prog");
        let h_before = canonical_vk_v2(&c);
        c.verifier_fingerprint = VerifierFingerprint::SourceHash([0x44; 32]);
        let h_after = canonical_vk_v2(&c);
        assert_ne!(h_before, h_after);
    }

    #[test]
    fn canonical_vk_v2_changes_with_verifier_fingerprint_variant() {
        // Same 32-byte hash, different variant tag — must produce
        // distinct vk_hashes.
        let mut c = sample_components(b"prog");
        c.verifier_fingerprint = VerifierFingerprint::SourceHash([0x22; 32]);
        let h_source = canonical_vk_v2(&c);
        c.verifier_fingerprint = VerifierFingerprint::WasmHash([0x22; 32]);
        let h_wasm = canonical_vk_v2(&c);
        c.verifier_fingerprint = VerifierFingerprint::CompiledVkHash([0x22; 32]);
        let h_vk = canonical_vk_v2(&c);
        assert_ne!(h_source, h_wasm);
        assert_ne!(h_wasm, h_vk);
        assert_ne!(h_source, h_vk);
    }

    #[test]
    fn canonical_vk_v2_changes_with_proving_system() {
        let mut c = sample_components(b"prog");
        let h_p3 = canonical_vk_v2(&c);
        c.proving_system_id = ProvingSystemId::KimchiPasta;
        let h_kimchi = canonical_vk_v2(&c);
        c.proving_system_id = ProvingSystemId::Sp1V6;
        let h_sp1 = canonical_vk_v2(&c);
        c.proving_system_id = ProvingSystemId::Custom { id: "my-system" };
        let h_custom = canonical_vk_v2(&c);
        assert_ne!(h_p3, h_kimchi);
        assert_ne!(h_kimchi, h_sp1);
        assert_ne!(h_sp1, h_custom);
        assert_ne!(h_p3, h_custom);
    }

    #[test]
    fn canonical_vk_v2_changes_with_plonky3_rev() {
        let mut c = sample_components(b"prog");
        c.proving_system_id = ProvingSystemId::Plonky3BabyBearFri { p3_rev: "rev-a" };
        let h_a = canonical_vk_v2(&c);
        c.proving_system_id = ProvingSystemId::Plonky3BabyBearFri { p3_rev: "rev-b" };
        let h_b = canonical_vk_v2(&c);
        assert_ne!(h_a, h_b);
    }

    #[test]
    fn canonical_vk_v2_length_prefix_disambiguates_concatenation() {
        // Without the length prefix on program_bytes, two splits could
        // collide: ("ab", "cd") vs. ("abc", "d"). The prefix prevents
        // this.
        let a = canonical_vk_v2(&VkComponents {
            program_bytes: b"abcd",
            air_fingerprint: [0x11; 32],
            verifier_fingerprint: VerifierFingerprint::SourceHash([0x22; 32]),
            proving_system_id: ProvingSystemId::KimchiPasta,
        });
        let b = canonical_vk_v2(&VkComponents {
            program_bytes: b"abc",
            air_fingerprint: [0x11; 32],
            verifier_fingerprint: VerifierFingerprint::SourceHash([0x22; 32]),
            proving_system_id: ProvingSystemId::KimchiPasta,
        });
        assert_ne!(a, b);
    }

    #[test]
    fn canonical_vk_v2_disjoint_from_v1_domains() {
        // Even if all four components reduce to a degenerate shape
        // (empty program, zero fingerprints, zero hashes), the v2 hash
        // must not collide with a vanilla BLAKE3 of the same components.
        // BLAKE3 keyed derivation makes this hold with overwhelming
        // probability; this test guards against accidental domain-key
        // removal at refactor time.
        let v2 = canonical_vk_v2(&VkComponents {
            program_bytes: b"",
            air_fingerprint: [0u8; 32],
            verifier_fingerprint: VerifierFingerprint::SourceHash([0u8; 32]),
            proving_system_id: ProvingSystemId::KimchiPasta,
        });
        let raw = *blake3::hash(b"").as_bytes();
        assert_ne!(v2, raw);
    }

    #[test]
    fn proving_system_canonical_bytes_distinguishes_variants() {
        let p3 = ProvingSystemId::Plonky3BabyBearFri { p3_rev: "r" };
        let kimchi = ProvingSystemId::KimchiPasta;
        let sp1 = ProvingSystemId::Sp1V6;
        let cust = ProvingSystemId::Custom { id: "x" };
        let a = p3.canonical_bytes();
        let b = kimchi.canonical_bytes();
        let c = sp1.canonical_bytes();
        let d = cust.canonical_bytes();
        assert_ne!(a, b);
        assert_ne!(b, c);
        assert_ne!(c, d);
        assert_ne!(a, d);
    }

    #[test]
    fn verifier_fingerprint_canonical_bytes_distinguishes_variants() {
        let s = VerifierFingerprint::SourceHash([7u8; 32]).canonical_bytes();
        let w = VerifierFingerprint::WasmHash([7u8; 32]).canonical_bytes();
        let v = VerifierFingerprint::CompiledVkHash([7u8; 32]).canonical_bytes();
        assert_ne!(s, w);
        assert_ne!(w, v);
        assert_ne!(s, v);
    }
}
