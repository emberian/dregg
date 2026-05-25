//! AIR shape descriptors and fingerprints (VK v2 lane).
//!
//! Per `VK-AS-RE-EXECUTION-RECIPE.md` §v2, a `vk_hash` for a cell program
//! commits to four components — program bytes, AIR shape, verifier impl,
//! proving system. This module is the home of the **AIR shape** layer.
//!
//! An [`AirDescriptor`] is a static description of a hand-written AIR's
//! externally visible shape: how many trace columns it uses, what its
//! public-input layout looks like, how many algebraic constraints it
//! carries, and what maximum polynomial degree they reach. The
//! [`fingerprint`] function compresses this description into a 32-byte
//! hash under the domain `"pyana-air-fingerprint-v1"` — the value that
//! goes into [`crate::vk_v2::VkComponents::air_fingerprint`] when
//! computing a cell-program VK that should bind to a *specific* AIR.
//!
//! ## Why this matters
//!
//! Pre-v2, `canonical_program_vk(program)` returned `BLAKE3(domain ||
//! postcard(program))` — committing only to the program spec. If two
//! cells ran the same `CellProgram` against different AIRs (say, the
//! Effect VM AIR vs. a note-spending AIR with a different column layout
//! and PI shape), they would share a vk_hash. A validator could not
//! tell them apart from the VK alone, which is the wrong story:
//! re-execution against the wrong AIR is a soundness failure.
//!
//! v2 fixes this by mixing the AIR fingerprint into the vk_hash. Each
//! hand-written AIR module exports `pub const AIR_DESCRIPTOR:
//! AirDescriptor` that captures its shape; callers (cell-program VK
//! computation, custom-effect registration, custom-predicate
//! registration) pass the descriptor's fingerprint as one of the four
//! components.
//!
//! ## Adding a new AIR
//!
//! When you add a hand-written AIR, add a `pub const AIR_DESCRIPTOR:
//! AirDescriptor` at the bottom of the AIR's module. The descriptor
//! should be `const`-evaluable so the fingerprint can be computed at
//! callsite time without runtime overhead.
//!
//! The `source_hash` field is optional. If you compute the git-blob
//! hash of the AIR's source file and pin it here, you get an even
//! tighter binding: a validator can confirm the AIR source they hold
//! matches what the VK author committed to. Leave it `None` for
//! hand-written AIRs that the platform reserves and ships in-tree (the
//! source is the canonical bytes; the binding is implicit). Set it for
//! app-provided AIRs where source distribution matters.

/// A description of one public-input slot in an AIR's PI vector.
///
/// `name` is a human-readable identifier for diagnostics; `offset` and
/// `length_in_felts` describe the BabyBear field-element range the slot
/// occupies in the PI vector. Two AIRs with the same column count but
/// different PI layouts (e.g., reordered slots, different lengths) get
/// distinct fingerprints because the slot list is part of the hash.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PiSlot {
    /// Human-readable slot name. Hashed as UTF-8 bytes; case-sensitive.
    pub name: &'static str,
    /// Index of the first felt of this slot in the AIR's PI vector.
    pub offset: usize,
    /// Number of consecutive felts this slot occupies.
    pub length_in_felts: usize,
}

/// A static descriptor of a hand-written AIR's externally visible shape.
///
/// Used to compute [`fingerprint`] — the 32-byte AIR-shape commitment
/// that goes into VK v2's layered vk_hash. Two AIRs with the same
/// descriptor produce the same fingerprint; any field difference
/// produces a different fingerprint.
///
/// Each hand-written AIR module exports a `pub const AIR_DESCRIPTOR:
/// AirDescriptor` so callers can derive the fingerprint at any time
/// without depending on the AIR's runtime types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AirDescriptor {
    /// Stable identifier for this AIR. Conventionally
    /// `"<name>_air_v<n>"`, e.g., `"effect_vm_air_v1"`. Two AIRs that
    /// have the same shape but model different domains MUST have
    /// distinct `air_id` values; otherwise a vk_hash misbinding is
    /// possible.
    pub air_id: &'static str,
    /// Number of trace columns the AIR uses.
    pub column_count: usize,
    /// Layout of the public-input vector. Ordered by `offset`.
    pub public_input_layout: &'static [PiSlot],
    /// Total number of polynomial constraints the AIR enforces (each
    /// summed into the random-linear combination during evaluation).
    pub constraint_polynomial_count: usize,
    /// Number of boundary constraints (row-pinned algebraic equalities).
    pub boundary_constraint_count: usize,
    /// Maximum polynomial degree of any single constraint. Drives
    /// quotient-polynomial dimensioning.
    pub max_degree: usize,
    /// Optional git-blob-hash of the AIR's source file. When `Some`,
    /// validators can confirm the AIR source they hold corresponds to
    /// the descriptor's claim; when `None`, the AIR is in-tree and the
    /// `air_id` is the canonical identifier.
    pub source_hash: Option<[u8; 32]>,
}

/// Compute the 32-byte fingerprint of an [`AirDescriptor`].
///
/// Domain-keyed under `"pyana-air-fingerprint-v1"` so AIR fingerprints
/// cannot collide with cell-program VK hashes, custom-predicate VK
/// hashes, or any other `[u8; 32]` identifier in pyana.
///
/// The encoding is canonical: every field is fed into the hasher with
/// an explicit length prefix where the field has variable size, so
/// concatenation attacks cannot collide two different descriptors.
pub fn fingerprint(d: &AirDescriptor) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-air-fingerprint-v1");
    let id_bytes = d.air_id.as_bytes();
    hasher.update(&(id_bytes.len() as u64).to_le_bytes());
    hasher.update(id_bytes);
    hasher.update(&(d.column_count as u64).to_le_bytes());
    hasher.update(&(d.public_input_layout.len() as u64).to_le_bytes());
    for slot in d.public_input_layout {
        let name_bytes = slot.name.as_bytes();
        hasher.update(&(name_bytes.len() as u64).to_le_bytes());
        hasher.update(name_bytes);
        hasher.update(&(slot.offset as u64).to_le_bytes());
        hasher.update(&(slot.length_in_felts as u64).to_le_bytes());
    }
    hasher.update(&(d.constraint_polynomial_count as u64).to_le_bytes());
    hasher.update(&(d.boundary_constraint_count as u64).to_le_bytes());
    hasher.update(&(d.max_degree as u64).to_le_bytes());
    match &d.source_hash {
        Some(h) => {
            hasher.update(&[1u8]);
            hasher.update(h);
        }
        None => {
            hasher.update(&[0u8]);
        }
    }
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_descriptor() -> AirDescriptor {
        AirDescriptor {
            air_id: "test_air_v1",
            column_count: 8,
            public_input_layout: &[
                PiSlot {
                    name: "alpha",
                    offset: 0,
                    length_in_felts: 4,
                },
                PiSlot {
                    name: "beta",
                    offset: 4,
                    length_in_felts: 2,
                },
            ],
            constraint_polynomial_count: 11,
            boundary_constraint_count: 3,
            max_degree: 4,
            source_hash: None,
        }
    }

    #[test]
    fn fingerprint_is_deterministic() {
        let d = sample_descriptor();
        assert_eq!(fingerprint(&d), fingerprint(&d));
    }

    #[test]
    fn fingerprint_changes_with_air_id() {
        let a = sample_descriptor();
        let b = AirDescriptor {
            air_id: "other_air_v1",
            ..a
        };
        assert_ne!(fingerprint(&a), fingerprint(&b));
    }

    #[test]
    fn fingerprint_changes_with_column_count() {
        let a = sample_descriptor();
        let b = AirDescriptor {
            column_count: 9,
            ..a
        };
        assert_ne!(fingerprint(&a), fingerprint(&b));
    }

    #[test]
    fn fingerprint_changes_with_pi_layout_offset() {
        let a = sample_descriptor();
        let alt: &'static [PiSlot] = &[
            PiSlot {
                name: "alpha",
                offset: 1,
                length_in_felts: 4,
            },
            PiSlot {
                name: "beta",
                offset: 5,
                length_in_felts: 2,
            },
        ];
        let b = AirDescriptor {
            public_input_layout: alt,
            ..a
        };
        assert_ne!(fingerprint(&a), fingerprint(&b));
    }

    #[test]
    fn fingerprint_changes_with_pi_layout_name() {
        let a = sample_descriptor();
        let alt: &'static [PiSlot] = &[
            PiSlot {
                name: "gamma",
                offset: 0,
                length_in_felts: 4,
            },
            PiSlot {
                name: "beta",
                offset: 4,
                length_in_felts: 2,
            },
        ];
        let b = AirDescriptor {
            public_input_layout: alt,
            ..a
        };
        assert_ne!(fingerprint(&a), fingerprint(&b));
    }

    #[test]
    fn fingerprint_changes_with_constraint_counts() {
        let a = sample_descriptor();
        let b = AirDescriptor {
            constraint_polynomial_count: a.constraint_polynomial_count + 1,
            ..a
        };
        let c = AirDescriptor {
            boundary_constraint_count: a.boundary_constraint_count + 1,
            ..a
        };
        assert_ne!(fingerprint(&a), fingerprint(&b));
        assert_ne!(fingerprint(&a), fingerprint(&c));
    }

    #[test]
    fn fingerprint_changes_with_max_degree() {
        let a = sample_descriptor();
        let b = AirDescriptor {
            max_degree: a.max_degree + 1,
            ..a
        };
        assert_ne!(fingerprint(&a), fingerprint(&b));
    }

    #[test]
    fn fingerprint_distinguishes_some_vs_none_source_hash() {
        let a = sample_descriptor();
        let b = AirDescriptor {
            source_hash: Some([0u8; 32]),
            ..a
        };
        assert_ne!(fingerprint(&a), fingerprint(&b));
    }

    #[test]
    fn in_tree_air_descriptors_have_distinct_fingerprints() {
        // The three hand-written AIRs in the tree must produce distinct
        // fingerprints. If they collided, a vk_hash bound to one AIR
        // would mistakenly accept proofs under another.
        let effect_vm = fingerprint(&crate::effect_vm::AIR_DESCRIPTOR);
        #[allow(deprecated)]
        let note_spending = fingerprint(&crate::note_spending_air::AIR_DESCRIPTOR);
        let bridge_action = fingerprint(&crate::bridge_action_air::AIR_DESCRIPTOR);
        assert_ne!(effect_vm, note_spending);
        assert_ne!(note_spending, bridge_action);
        assert_ne!(effect_vm, bridge_action);
        // Each fingerprint is also non-zero (BLAKE3 of any input is
        // non-zero w.h.p.).
        assert_ne!(effect_vm, [0u8; 32]);
        assert_ne!(note_spending, [0u8; 32]);
        assert_ne!(bridge_action, [0u8; 32]);
    }

    #[test]
    fn pi_layout_length_prefix_disambiguates_concatenation() {
        // Two descriptors whose slot lists concatenate to the same byte
        // string should still fingerprint distinctly, because the
        // layout-length prefix differs.
        let one_slot: &'static [PiSlot] = &[PiSlot {
            name: "ab",
            offset: 0,
            length_in_felts: 2,
        }];
        let two_slots: &'static [PiSlot] = &[
            PiSlot {
                name: "a",
                offset: 0,
                length_in_felts: 1,
            },
            PiSlot {
                name: "b",
                offset: 1,
                length_in_felts: 1,
            },
        ];
        let a = AirDescriptor {
            public_input_layout: one_slot,
            ..sample_descriptor()
        };
        let b = AirDescriptor {
            public_input_layout: two_slots,
            ..sample_descriptor()
        };
        assert_ne!(fingerprint(&a), fingerprint(&b));
    }
}
