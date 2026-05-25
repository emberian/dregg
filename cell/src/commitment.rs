//! Canonical state-commitment for a `Cell`.
//!
//! ## Background (audit P0-2)
//!
//! Prior to this module, the codebase had **three** disjoint state-commitment
//! schemes with no cross-binding:
//!
//! 1. `Cell::state_commitment()` — BLAKE3, `pyana-cell-state-v1` derive key,
//!    committed to a **subset** of state (no visibility, no commitments, no
//!    delegation/program/proved_state).
//! 2. `Ledger::hash_cell()` — BLAKE3, `pyana-cell:merkle-leaf v2` derive key,
//!    committed to a **superset** (all of `state_commitment` plus visibility,
//!    commitments, delegation_epoch, proved_state, program, delegate, delegation).
//! 3. `circuit::CellState::compute_commitment()` — Poseidon2 over BabyBear,
//!    committed to **only** `(balance, nonce, fields[0..8], capability_root)`,
//!    omitting identity, permissions, VK, etc.
//!
//! The trust gap: a sovereign cell's circuit-side identity had no binding
//! to its permissions or verification key. Two cells with identical
//! `(balance, nonce, fields, cap_root)` but completely different `Permissions`
//! produced the same circuit-side commitment.
//!
//! ## Resolution
//!
//! All authority-bearing state goes through a **single** canonical commitment
//! function: [`compute_canonical_state_commitment`]. Both `Cell::state_commitment`
//! and `Ledger::hash_cell` are now thin wrappers calling this function, so they
//! produce **identical bytes** for the same state.
//!
//! For the circuit (Poseidon2) side, the field shape is incompatible with the
//! BLAKE3 scheme. The right binding is to use this function's output as a
//! BabyBear public input on the circuit side — i.e. the STARK's `state_commit`
//! public input must be derived from the canonical commitment, not invented
//! independently. See [`canonical_to_babybear_pi`] for the bytes-to-felts
//! adapter.
//!
//! REVIEW[circuit-fix-coordination]: The circuit's `CellState::compute_commitment`
//! (in `circuit/src/effect_vm.rs`) still commits to a strict subset. To close
//! P0-2 fully, the circuit AIR's state_commit boundary public input should be
//! constrained to equal the BabyBear-field encoding of the canonical commitment.
//! A coordinating change in `circuit/` should introduce a
//! `bind_to_canonical_commitment(canonical_bytes)` adapter that asserts equality
//! between the Poseidon2 inner commitment and `canonical_to_babybear_pi(bytes)`,
//! or replace the Poseidon2 commitment with the canonical scheme entirely.

use crate::capability::CapabilitySet;
use crate::cell::Cell;
use crate::delegation::DelegatedRef;
#[cfg(test)]
use crate::id::CellId;
use crate::permissions::{AuthRequired, Permissions};
use crate::state::{CellState, FieldVisibility};

/// Domain-separation context for the canonical state commitment.
///
/// **Versioning policy:** any change to this module's hash shape MUST bump the
/// version suffix. Downstream Merkle leaves, sovereign commitments, and
/// circuit public inputs derive their domain separation transitively from this
/// context — bumping it cleanly invalidates stale commitments rather than
/// allowing silent cross-version collisions.
pub const CANONICAL_COMMITMENT_CONTEXT: &str = "pyana-cell:canonical-state-commitment v1";

/// Domain-separation context for the canonical capability-set root.
pub const CANONICAL_CAP_ROOT_CONTEXT: &str = "pyana-cell:canonical-capability-root v1";

/// Compute the canonical commitment for a single `AuthRequired` value.
#[inline]
fn auth_byte(auth: &AuthRequired) -> u8 {
    match auth {
        AuthRequired::None => 0,
        AuthRequired::Signature => 1,
        AuthRequired::Proof => 2,
        AuthRequired::Either => 3,
        AuthRequired::Impossible => 4,
        // Custom authorizers are identified by their vk_hash; encode as 5
        // so they are distinguished from the standard tiers in the
        // commitment. The full vk_hash is committed separately in the
        // permissions-commitment chain; the byte here just marks the tier.
        AuthRequired::Custom { .. } => 5,
    }
}

/// Compute the canonical commitment for a single `FieldVisibility` value.
#[inline]
fn visibility_byte(vis: FieldVisibility) -> u8 {
    match vis {
        FieldVisibility::Public => 0,
        FieldVisibility::Committed => 1,
        FieldVisibility::SelectivelyDisclosable => 2,
    }
}

/// Compute the canonical 32-byte commitment to a `Cell`'s full authority-bearing
/// state.
///
/// This is the **single** source of truth for "what bytes commit to this cell."
/// It is used by:
///
/// - `Cell::state_commitment()` — sovereign-witness verification
/// - `Ledger::hash_cell()` — Merkle leaf in the federation tree
/// - (planned) Poseidon2 binding for the STARK public input
///
/// All authority-relevant state is included. Omitting any field would allow an
/// attacker to present two distinct authority-bearing states with the same
/// commitment.
pub fn compute_canonical_state_commitment(cell: &Cell) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CANONICAL_COMMITMENT_CONTEXT);

    // ---- Identity ----
    hasher.update(cell.id.as_bytes());
    hasher.update(&cell.public_key);
    hasher.update(&cell.token_id);

    // ---- Mode ----
    let mode_byte: u8 = match cell.mode {
        crate::cell::CellMode::Hosted => 0,
        crate::cell::CellMode::Sovereign => 1,
    };
    hasher.update(&[mode_byte]);

    // ---- Core state ----
    hash_cell_state_into(&mut hasher, &cell.state);

    // ---- Permissions ----
    hash_permissions_into(&mut hasher, &cell.permissions);

    // ---- Verification key ----
    match &cell.verification_key {
        Some(vk) => {
            hasher.update(&[1u8]);
            hasher.update(&vk.hash);
        }
        None => {
            hasher.update(&[0u8]);
        }
    }

    // ---- Capabilities (full canonical root) ----
    let cap_root = compute_canonical_capability_root(&cell.capabilities);
    hasher.update(&cap_root);

    // ---- Delegate ----
    match &cell.delegate {
        Some(d) => {
            hasher.update(&[1u8]);
            hasher.update(d.as_bytes());
        }
        None => {
            hasher.update(&[0u8]);
        }
    }

    // ---- Delegation snapshot ----
    match &cell.delegation {
        Some(deleg) => {
            hasher.update(&[1u8]);
            hash_delegation_into(&mut hasher, deleg);
        }
        None => {
            hasher.update(&[0u8]);
        }
    }

    // ---- Program ----
    hash_program_into(&mut hasher, &cell.program);

    *hasher.finalize().as_bytes()
}

/// Hash the inner `CellState` (no domain separator — used as a sub-hasher).
fn hash_cell_state_into(hasher: &mut blake3::Hasher, state: &CellState) {
    hasher.update(&state.nonce.to_le_bytes());
    hasher.update(&state.balance.to_le_bytes());
    for field in &state.fields {
        hasher.update(field);
    }
    for vis in &state.field_visibility {
        hasher.update(&[visibility_byte(*vis)]);
    }
    for commit in &state.commitments {
        match commit {
            Some(h) => {
                hasher.update(&[1u8]);
                hasher.update(h);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
    }
    hasher.update(&[state.proved_state as u8]);
    hasher.update(&state.delegation_epoch.to_le_bytes());
    // Stage 1: CapTP-prep committed roots (`DESIGN-captp-integration.md` §4).
    // These are part of authority-bearing state because they gate enliven /
    // drop-ref / handoff operations.
    hasher.update(&state.swiss_table_root);
    hasher.update(&state.refcount_table_root);
}

fn hash_permissions_into(hasher: &mut blake3::Hasher, perms: &Permissions) {
    hasher.update(&[
        auth_byte(&perms.send),
        auth_byte(&perms.receive),
        auth_byte(&perms.set_state),
        auth_byte(&perms.set_permissions),
        auth_byte(&perms.set_verification_key),
        auth_byte(&perms.increment_nonce),
        auth_byte(&perms.delegate),
        auth_byte(&perms.access),
    ]);
}

fn hash_delegation_into(hasher: &mut blake3::Hasher, deleg: &DelegatedRef) {
    hasher.update(deleg.source.as_bytes());
    hasher.update(&deleg.delegation_epoch.to_le_bytes());
    hasher.update(&deleg.refreshed_at.to_le_bytes());
    hasher.update(&deleg.max_staleness.to_le_bytes());
    // Snapshot: full canonical leaf-hash so that (target, slot) + permissions +
    // breadstuff + expires_at + allowed_effects are all committed. (Audit P2-4
    // flagged that the old `hash_cell` was lossy here.)
    let cap_count = deleg.snapshot.len() as u64;
    hasher.update(&cap_count.to_le_bytes());
    for cap in &deleg.snapshot {
        hash_capability_ref_into(hasher, cap);
    }
}

fn hash_capability_ref_into(hasher: &mut blake3::Hasher, cap: &crate::capability::CapabilityRef) {
    hasher.update(cap.target.as_bytes());
    hasher.update(&cap.slot.to_le_bytes());
    hasher.update(&[auth_byte(&cap.permissions)]);
    match &cap.breadstuff {
        Some(bs) => {
            hasher.update(&[1u8]);
            hasher.update(bs);
        }
        None => {
            hasher.update(&[0u8]);
        }
    }
    match cap.expires_at {
        Some(h) => {
            hasher.update(&[1u8]);
            hasher.update(&h.to_le_bytes());
        }
        None => {
            hasher.update(&[0u8]);
        }
    }
    match cap.allowed_effects {
        Some(mask) => {
            hasher.update(&[1u8]);
            hasher.update(&mask.to_le_bytes());
        }
        None => {
            hasher.update(&[0u8]);
        }
    }
}

fn hash_program_into(hasher: &mut blake3::Hasher, program: &crate::program::CellProgram) {
    use crate::program::CellProgram;
    match program {
        CellProgram::None => {
            hasher.update(&[0u8]);
        }
        CellProgram::Predicate(constraints) => {
            hasher.update(&[1u8]);
            let serialized = postcard::to_allocvec(constraints).unwrap_or_default();
            hasher.update(&(serialized.len() as u64).to_le_bytes());
            hasher.update(&serialized);
        }
        CellProgram::Circuit { circuit_hash } => {
            hasher.update(&[2u8]);
            hasher.update(circuit_hash);
        }
        CellProgram::Cases(cases) => {
            hasher.update(&[3u8]);
            let serialized = postcard::to_allocvec(cases).unwrap_or_default();
            hasher.update(&(serialized.len() as u64).to_le_bytes());
            hasher.update(&serialized);
        }
    }
}

/// Compute the canonical 32-byte root of a `CapabilitySet`.
///
/// This is what the circuit's `capability_root` BabyBear element *should* be
/// derived from (audit P0-3 — currently uncomputed in the cell crate). All
/// authority-relevant fields of every `CapabilityRef` are included.
pub fn compute_canonical_capability_root(caps: &CapabilitySet) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CANONICAL_CAP_ROOT_CONTEXT);
    let cap_count = caps.len() as u64;
    hasher.update(&cap_count.to_le_bytes());
    for cap in caps.iter() {
        hash_capability_ref_into(&mut hasher, cap);
    }
    *hasher.finalize().as_bytes()
}

/// Convert a 32-byte canonical commitment into 8 BabyBear-shaped felts
/// (encoded as little-endian u32 truncated to 30 bits to fit BabyBear range).
///
/// The output is the binding input that a Poseidon2-based circuit can absorb
/// to tie its state_commit public input back to the canonical scheme. The
/// 30-bit truncation is intentional — BabyBear's modulus is 2^31 − 2^27 + 1,
/// and 30-bit limbs guarantee a unique encoding without modular reduction
/// collisions.
///
/// Returns `[u32; 8]` representing the 8 felts. The circuit side should
/// constrain its declared state_commit equal to a fixed Poseidon2 hash of
/// these 8 felts in some agreed-upon shape.
///
/// REVIEW[circuit-fix-coordination]: this function defines the *contract*
/// only — actual binding requires the circuit to absorb these 8 felts and
/// emit a constrained equality to its own state_commit. Coordination needed
/// with circuit-fix agent. See module-level docs.
pub fn canonical_to_babybear_pi(canonical: &[u8; 32]) -> [u32; 8] {
    let mut out = [0u32; 8];
    for i in 0..8 {
        let lo = canonical[i * 4] as u32;
        let mid1 = canonical[i * 4 + 1] as u32;
        let mid2 = canonical[i * 4 + 2] as u32;
        let hi = canonical[i * 4 + 3] as u32;
        // Pack 30 bits: 8+8+8+6 = 30
        out[i] = lo | (mid1 << 8) | (mid2 << 16) | ((hi & 0x3F) << 24);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cell::Cell;

    fn test_key(b: u8) -> [u8; 32] {
        let mut k = [0u8; 32];
        k[0] = b;
        k
    }

    fn test_token(b: u8) -> [u8; 32] {
        let mut t = [0u8; 32];
        t[1] = b;
        t
    }

    /// Adversarial test (audit P0-2 remediation): assert that the three
    /// commitment derivations all agree byte-for-byte.
    ///
    /// - `compute_canonical_state_commitment(&cell)` — the source of truth
    /// - `cell.state_commitment()` — wrapper
    /// - `Ledger::hash_cell_canonical(&cell)` — the Merkle leaf hash, also
    ///   the wrapper
    #[test]
    fn three_commitments_agree_byte_for_byte() {
        let cell = Cell::new(test_key(7), test_token(11));

        let canonical = compute_canonical_state_commitment(&cell);
        let from_state_commitment = cell.state_commitment();
        let from_hash_cell = crate::ledger::Ledger::hash_cell_canonical(&cell);

        assert_eq!(
            canonical, from_state_commitment,
            "Cell::state_commitment must equal canonical"
        );
        assert_eq!(
            canonical, from_hash_cell,
            "Ledger::hash_cell must equal canonical"
        );
        assert_eq!(
            from_state_commitment, from_hash_cell,
            "state_commitment and hash_cell must be identical"
        );
    }

    /// Adversarial test (audit P0-2): mutating *any* authority-bearing byte
    /// in the cell state must change the canonical commitment (and therefore
    /// all three derivations).
    #[test]
    fn mutating_state_changes_all_three_commitments() {
        let mut cell = Cell::new(test_key(7), test_token(11));
        let before = compute_canonical_state_commitment(&cell);
        let sc_before = cell.state_commitment();
        let hc_before = crate::ledger::Ledger::hash_cell_canonical(&cell);

        // Mutate balance through the legitimate accessor.
        assert!(cell.state.apply_balance_change(1234));

        let after = compute_canonical_state_commitment(&cell);
        let sc_after = cell.state_commitment();
        let hc_after = crate::ledger::Ledger::hash_cell_canonical(&cell);

        assert_ne!(before, after);
        assert_ne!(sc_before, sc_after);
        assert_ne!(hc_before, hc_after);

        // All three still agree on the new state.
        assert_eq!(after, sc_after);
        assert_eq!(after, hc_after);
    }

    /// Adversarial test: changing the **permissions** must alter the
    /// canonical commitment. Previously, the circuit-side Poseidon2
    /// commitment did NOT cover permissions, so two cells with different
    /// permissions but identical (balance, nonce, fields) collided. The
    /// canonical commitment closes this on the cell-crate side.
    #[test]
    fn changing_permissions_changes_commitment() {
        let mut cell1 = Cell::new(test_key(7), test_token(11));
        let mut cell2 = Cell::new(test_key(7), test_token(11));

        let c1 = compute_canonical_state_commitment(&cell1);
        let c2 = compute_canonical_state_commitment(&cell2);
        assert_eq!(c1, c2, "identical cells must agree");

        // Now change cell2's permissions.
        cell2.permissions = Permissions::zkapp();

        let c1b = compute_canonical_state_commitment(&cell1);
        let c2b = compute_canonical_state_commitment(&cell2);
        assert_eq!(c1, c1b, "cell1 unchanged");
        assert_ne!(c2, c2b, "cell2 permissions change must propagate");
        assert_ne!(c1b, c2b, "cells differ after permission change");

        // No mutation on cell1.
        let _ = &mut cell1;
    }

    /// Adversarial test: changing the verification key must alter the
    /// canonical commitment.
    #[test]
    fn changing_vk_changes_commitment() {
        let mut cell = Cell::new(test_key(7), test_token(11));
        let before = compute_canonical_state_commitment(&cell);
        cell.verification_key = Some(crate::cell::VerificationKey::new(b"new-vk".to_vec()));
        let after = compute_canonical_state_commitment(&cell);
        assert_ne!(before, after);
    }

    /// Canonical capability root must change with any capability addition.
    #[test]
    fn capability_root_changes_on_grant() {
        let mut caps = CapabilitySet::new();
        let before = compute_canonical_capability_root(&caps);
        caps.grant(
            CellId::derive_raw(&test_key(1), &test_token(1)),
            AuthRequired::Signature,
        );
        let after = compute_canonical_capability_root(&caps);
        assert_ne!(before, after);
    }

    /// canonical_to_babybear_pi: same input → same output (deterministic).
    #[test]
    fn canonical_to_babybear_pi_deterministic() {
        let bytes = [42u8; 32];
        let a = canonical_to_babybear_pi(&bytes);
        let b = canonical_to_babybear_pi(&bytes);
        assert_eq!(a, b);
    }

    /// canonical_to_babybear_pi: different inputs → different outputs.
    #[test]
    fn canonical_to_babybear_pi_distinguishes() {
        let mut a = [0u8; 32];
        let mut b = [0u8; 32];
        b[0] = 1;
        assert_ne!(canonical_to_babybear_pi(&a), canonical_to_babybear_pi(&b));

        // High bit (within the 6-bit hi part of a limb) also distinguishes.
        a[3] = 0x20;
        b[3] = 0x10;
        assert_ne!(canonical_to_babybear_pi(&a), canonical_to_babybear_pi(&b));
    }

    /// All output felts must fit within BabyBear's representable range
    /// (< 2^31). Our 30-bit packing should produce values < 2^30.
    #[test]
    fn canonical_to_babybear_pi_in_range() {
        let bytes = [0xFFu8; 32];
        let pi = canonical_to_babybear_pi(&bytes);
        for &felt in &pi {
            assert!(felt < (1u32 << 30), "felt {felt} exceeds 30-bit range");
        }
    }
}
