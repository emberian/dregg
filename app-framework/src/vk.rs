//! VK v2 wrappers — layered canonical VK hashes for app authors.
//!
//! Per `VK-AS-RE-EXECUTION-RECIPE.md` §v2, a `child_program_vk` (and
//! any other `[u8; 32]` VK identifier in pyana) commits to four
//! components:
//!
//! 1. **Program bytes** — `postcard(CellProgram)`.
//! 2. **AIR fingerprint** — for cell programs, the fingerprint of
//!    [`pyana_circuit::effect_vm::AIR_DESCRIPTOR`].
//! 3. **Verifier fingerprint** — for cell programs, a stable identifier
//!    of the in-tree Effect VM verifier. The app-framework pins this
//!    to a fixed sentinel until per-AIR source-hash plumbing lands.
//! 4. **Proving system** — Plonky3 + BabyBear + FRI, pinned to the
//!    workspace's plonky3 git rev.
//!
//! [`canonical_program_vk`] hides the four-tuple behind the same one-
//! argument shape `canonical_program_vk(program)` that starbridge-apps
//! already use. The cell-crate's program-bytes-only encoder
//! ([`pyana_cell::canonical_program_vk`]) is re-exported here as
//! [`canonical_program_bytes_hash`] for callers that want the bottom-
//! layer hash directly.
//!
//! ## Effect VM verifier fingerprint
//!
//! The Effect VM verifier is hand-written Rust in
//! `circuit::effect_vm`. Until we wire git-blob-hash discovery into
//! the build, the fingerprint is a fixed sentinel keyed by the AIR
//! identifier: `BLAKE3_keyed("pyana-effect-vm-verifier-v1", b"effect_vm_air_v1")`.
//! Any change to the verifier's externally visible behavior should
//! advance the keyed-derive domain to `-v2` so the fingerprint
//! changes; app authors who pin VK constants pick up the new hash
//! automatically.
//!
//! ## Proving-system pin
//!
//! [`DEFAULT_PROVING_SYSTEM`] is `Plonky3BabyBearFri { p3_rev: …}`. The
//! `p3_rev` string is the abbreviated git rev pinned in the workspace
//! `Cargo.toml`. Bumping plonky3 advances this constant and
//! cascades into every v2 VK hash — by design, since the new prover
//! may produce different proofs.

use pyana_cell::{
    CellProgram, ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2,
};
use pyana_circuit::air_descriptor::fingerprint as air_fingerprint_of;
use pyana_circuit::effect_vm::AIR_DESCRIPTOR as EFFECT_VM_AIR_DESCRIPTOR;

/// Plonky3 git revision pinned in the workspace `Cargo.toml`.
///
/// Folded into the proving-system identifier in [`DEFAULT_PROVING_SYSTEM`]
/// so any plonky3 bump produces fresh vk_hashes.
pub const PLONKY3_PINNED_REV: &str = "82cfad73";

/// The proving system every pyana cell-program VK commits to (v2).
pub const DEFAULT_PROVING_SYSTEM: ProvingSystemId = ProvingSystemId::Plonky3BabyBearFri {
    p3_rev: PLONKY3_PINNED_REV,
};

/// Compute the Effect VM AIR's fingerprint.
///
/// Returns the BLAKE3-keyed hash of
/// `pyana_circuit::effect_vm::AIR_DESCRIPTOR` under the domain
/// `"pyana-air-fingerprint-v1"`. Stable across runs of the same
/// pyana commit; changes if and only if the Effect VM AIR's shape
/// (column count, PI layout, constraint counts, max degree) changes.
pub fn effect_vm_air_fingerprint() -> [u8; 32] {
    air_fingerprint_of(&EFFECT_VM_AIR_DESCRIPTOR)
}

/// Compute the Effect VM verifier's fingerprint (v1 sentinel form).
///
/// Until git-blob-hash discovery is wired in, the fingerprint is a
/// deterministic sentinel: BLAKE3-keyed under
/// `"pyana-effect-vm-verifier-v1"` over the AIR identifier bytes.
/// This is a [`VerifierFingerprint::SourceHash`] in flavor — the
/// verifier source is in-tree at `circuit/src/effect_vm.rs` and the
/// sentinel commits to "this version of the Effect VM verifier."
pub fn effect_vm_verifier_fingerprint() -> VerifierFingerprint {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-effect-vm-verifier-v1");
    hasher.update(EFFECT_VM_AIR_DESCRIPTOR.air_id.as_bytes());
    VerifierFingerprint::SourceHash(*hasher.finalize().as_bytes())
}

/// Compute the canonical v2 vk_hash for a [`CellProgram`].
///
/// This is the **v2** layered hash. Pre-v2, `canonical_program_vk(program)`
/// returned the program-bytes-only hash (now exposed as
/// [`canonical_program_bytes_hash`]). v2 callers, including every
/// starbridge-app's `*_child_program_vk()` function, use this entry
/// point — it commits to program bytes + Effect VM AIR fingerprint +
/// Effect VM verifier fingerprint + Plonky3-BabyBear-FRI proving
/// system in one move.
///
/// # Migration
///
/// Greenfield: the v2 hash for any given program is *different* from
/// the v1 hash for the same program. Apps that previously pinned
/// `NAME_CHILD_PROGRAM_VK = canonical_program_vk(&name_cell_program())`
/// will see the constant's value change on this bump. Document the
/// new hash in the app's README; consumers who pin to the old hash
/// must update.
pub fn canonical_program_vk(program: &CellProgram) -> [u8; 32] {
    let program_bytes = pyana_cell::factory::canonical_program_bytes(program);
    canonical_vk_v2(&VkComponents {
        program_bytes: &program_bytes,
        air_fingerprint: effect_vm_air_fingerprint(),
        verifier_fingerprint: effect_vm_verifier_fingerprint(),
        proving_system_id: DEFAULT_PROVING_SYSTEM,
    })
}

/// Compute the program-bytes-only hash for a [`CellProgram`]. This is
/// the bottom layer of v2 — what the cell crate's
/// [`pyana_cell::canonical_program_vk`] returns. Exposed here for
/// callers that want both the v1 and v2 forms (e.g., to print both in
/// an app's inspector output during migration).
pub fn canonical_program_bytes_hash(program: &CellProgram) -> [u8; 32] {
    pyana_cell::canonical_program_vk(program)
}

/// Compute the canonical v2 vk_hash for a custom predicate.
///
/// Mirrors [`canonical_program_vk`] but for the predicate-side
/// authoring layer (DSL ASTs, opaque app bytes). Commits to the
/// supplied `predicate_bytes` + Effect VM AIR + Effect VM verifier +
/// Plonky3-BabyBear-FRI proving system.
pub fn canonical_predicate_vk(predicate_bytes: &[u8]) -> [u8; 32] {
    canonical_vk_v2(&VkComponents {
        program_bytes: predicate_bytes,
        air_fingerprint: effect_vm_air_fingerprint(),
        verifier_fingerprint: effect_vm_verifier_fingerprint(),
        proving_system_id: DEFAULT_PROVING_SYSTEM,
    })
}

/// Validate that a [`pyana_cell::FactoryDescriptor`]'s `child_program_vk`
/// is the v2 canonical hash of the supplied program under the
/// Effect VM AIR + verifier + Plonky3 proving system.
///
/// Thin wrapper around
/// [`pyana_cell::FactoryDescriptor::validate_child_vk_canonical_v2`]
/// that fills in the four components for the common cell-program
/// case. Apps that want to validate against a different AIR /
/// verifier / proving-system should call the cell-crate method
/// directly.
pub fn validate_child_vk_canonical(
    descriptor: &pyana_cell::FactoryDescriptor,
    program: &CellProgram,
) -> Result<(), pyana_cell::FactoryError> {
    descriptor.validate_child_vk_canonical_v2(
        program,
        effect_vm_air_fingerprint(),
        effect_vm_verifier_fingerprint(),
        DEFAULT_PROVING_SYSTEM,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_cell::CellProgram;

    #[test]
    fn canonical_program_vk_v2_is_deterministic() {
        let p = CellProgram::None;
        assert_eq!(canonical_program_vk(&p), canonical_program_vk(&p));
    }

    #[test]
    fn canonical_program_vk_v2_changes_with_program() {
        let p1 = CellProgram::None;
        let p2 = CellProgram::Cases(vec![]);
        assert_ne!(canonical_program_vk(&p1), canonical_program_vk(&p2));
    }

    #[test]
    fn canonical_program_vk_v2_distinct_from_v1_bytes_hash() {
        // The whole point of v2: the layered hash differs from the
        // program-bytes-only hash for the same program.
        let p = CellProgram::None;
        assert_ne!(canonical_program_vk(&p), canonical_program_bytes_hash(&p));
    }

    #[test]
    fn effect_vm_air_fingerprint_is_stable() {
        let a = effect_vm_air_fingerprint();
        let b = effect_vm_air_fingerprint();
        assert_eq!(a, b);
        assert_ne!(a, [0u8; 32]);
    }

    #[test]
    fn effect_vm_verifier_fingerprint_is_stable() {
        let a = effect_vm_verifier_fingerprint();
        let b = effect_vm_verifier_fingerprint();
        assert_eq!(a, b);
    }

    #[test]
    fn canonical_predicate_vk_v2_is_deterministic() {
        let bytes = b"some-dsl";
        assert_eq!(canonical_predicate_vk(bytes), canonical_predicate_vk(bytes));
    }

    #[test]
    fn canonical_predicate_vk_v2_changes_with_input() {
        let a = canonical_predicate_vk(b"predicate-a");
        let b = canonical_predicate_vk(b"predicate-b");
        assert_ne!(a, b);
    }
}
