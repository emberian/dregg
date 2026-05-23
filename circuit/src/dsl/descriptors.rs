//! Standard DSL circuit descriptors for pyana proof generation and verification.
//!
//! This module provides factory functions for all production DSL circuits:
//! - [`merkle_poseidon2_descriptor`] / [`merkle_poseidon2_circuit`]
//! - [`blinded_merkle_poseidon2_descriptor`] / [`blinded_merkle_poseidon2_circuit`]
//! - [`non_revocation_descriptor`] / [`non_revocation_circuit`]
//! - [`derivation_descriptor`] / [`derivation_circuit`]
//!
//! These replace the old hand-written AIRs (`MerklePoseidon2StarkAir`,
//! `BlindedMerklePoseidon2StarkAir`, `NonRevocationAir`, `DerivationAir`) which
//! are now DEPRECATED.

use crate::field::{BABYBEAR_P, BabyBear};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// AIR name constants (canonical, versioned)
// ============================================================================

/// AIR name for Effect VM proofs (sovereign transitions).
pub const EFFECT_VM_AIR_NAME: &str = "pyana-effect-vm-v1";

/// AIR name for standard Merkle Poseidon2 membership proofs.
pub const MERKLE_POSEIDON2_AIR_NAME: &str = "pyana-merkle-poseidon2-v1";

/// AIR name for blinded (ring) Merkle membership proofs.
pub const BLINDED_MERKLE_AIR_NAME: &str = "pyana-blinded-merkle-v1";

/// AIR name for non-revocation proofs.
pub const NON_REVOCATION_AIR_NAME: &str = "pyana-non-revocation-v1";

/// AIR name for derivation proofs.
pub const DERIVATION_AIR_NAME: &str = "pyana-derivation-v1";

// ============================================================================
// Merkle Poseidon2
// ============================================================================

/// Column layout for Merkle Poseidon2.
pub mod merkle_col {
    pub const CURRENT: usize = 0;
    pub const SIB0: usize = 1;
    pub const SIB1: usize = 2;
    pub const SIB2: usize = 3;
    pub const POSITION: usize = 4;
    pub const PARENT: usize = 5;
    // Blinded variant only:
    pub const BLINDING: usize = 6;
    pub const BLINDED: usize = 7;
}

pub const MERKLE_P2_WIDTH: usize = 6;
pub const BLINDED_MERKLE_P2_WIDTH: usize = 8;
pub const MERKLE_PUBLIC_INPUT_COUNT: usize = 2;

/// Build a 4-ary Merkle membership `CircuitDescriptor` using Poseidon2 (hash_fact).
///
/// Proves: "I know a leaf and a path such that hashing up the tree yields the claimed root."
///
/// Public inputs: [leaf_hash, root]
pub fn merkle_poseidon2_descriptor() -> CircuitDescriptor {
    let p = BABYBEAR_P;
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    let mut constraints = Vec::new();

    // C1: Position validity -- pos*(pos-1)*(pos-2)*(pos-3) == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                ],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                ],
            },
            PolyTerm {
                coeff: pos_11,
                col_indices: vec![merkle_col::POSITION, merkle_col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![merkle_col::POSITION],
            },
        ],
    });

    // C2: Parent hash binding
    constraints.push(ConstraintExpr::Hash {
        output_col: merkle_col::PARENT,
        input_cols: vec![
            merkle_col::CURRENT,
            merkle_col::SIB0,
            merkle_col::SIB1,
            merkle_col::SIB2,
            merkle_col::POSITION,
        ],
    });

    // C3: Chain continuity
    constraints.push(ConstraintExpr::Transition {
        next_col: merkle_col::CURRENT,
        local_col: merkle_col::PARENT,
    });

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: merkle_col::CURRENT,
            pi_index: 0,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: merkle_col::PARENT,
            pi_index: 1,
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "current".into(),
            index: merkle_col::CURRENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "sib0".into(),
            index: merkle_col::SIB0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib1".into(),
            index: merkle_col::SIB1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib2".into(),
            index: merkle_col::SIB2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "position".into(),
            index: merkle_col::POSITION,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "parent".into(),
            index: merkle_col::PARENT,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: MERKLE_POSEIDON2_AIR_NAME.into(),
        trace_width: MERKLE_P2_WIDTH,
        max_degree: 5,
        columns,
        constraints,
        boundaries,
        public_input_count: MERKLE_PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a `DslCircuit` for standard Merkle Poseidon2 membership.
pub fn merkle_poseidon2_circuit() -> DslCircuit {
    DslCircuit::new(merkle_poseidon2_descriptor())
}

/// Build a blinded 4-ary Merkle membership `CircuitDescriptor` using Poseidon2.
///
/// Proves: "I know a leaf in this tree" WITHOUT revealing which leaf.
/// Public inputs: [blinded_leaf, root]
pub fn blinded_merkle_poseidon2_descriptor() -> CircuitDescriptor {
    let p = BABYBEAR_P;
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    let mut constraints = Vec::new();

    // C1: Position validity
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                ],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                ],
            },
            PolyTerm {
                coeff: pos_11,
                col_indices: vec![merkle_col::POSITION, merkle_col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![merkle_col::POSITION],
            },
        ],
    });

    // C2: Parent hash binding
    constraints.push(ConstraintExpr::Hash {
        output_col: merkle_col::PARENT,
        input_cols: vec![
            merkle_col::CURRENT,
            merkle_col::SIB0,
            merkle_col::SIB1,
            merkle_col::SIB2,
            merkle_col::POSITION,
        ],
    });

    // C3: Chain continuity
    constraints.push(ConstraintExpr::Transition {
        next_col: merkle_col::CURRENT,
        local_col: merkle_col::PARENT,
    });

    // C4: Blinding hash binding
    constraints.push(ConstraintExpr::Hash {
        output_col: merkle_col::BLINDED,
        input_cols: vec![merkle_col::CURRENT, merkle_col::BLINDING],
    });

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: merkle_col::BLINDED,
            pi_index: 0,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: merkle_col::PARENT,
            pi_index: 1,
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "current".into(),
            index: merkle_col::CURRENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "sib0".into(),
            index: merkle_col::SIB0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib1".into(),
            index: merkle_col::SIB1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib2".into(),
            index: merkle_col::SIB2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "position".into(),
            index: merkle_col::POSITION,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "parent".into(),
            index: merkle_col::PARENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "blinding".into(),
            index: merkle_col::BLINDING,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "blinded".into(),
            index: merkle_col::BLINDED,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: BLINDED_MERKLE_AIR_NAME.into(),
        trace_width: BLINDED_MERKLE_P2_WIDTH,
        max_degree: 5,
        columns,
        constraints,
        boundaries,
        public_input_count: MERKLE_PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a `DslCircuit` for blinded Merkle Poseidon2 membership (ring membership).
pub fn blinded_merkle_poseidon2_circuit() -> DslCircuit {
    DslCircuit::new(blinded_merkle_poseidon2_descriptor())
}

// ============================================================================
// Non-Revocation
// ============================================================================

/// Tree depth for the DSL non-revocation Merkle tree (binary, 16 leaves).
pub const NON_REVOCATION_TREE_DEPTH: usize = 4;

/// Number of bits for the ordering range check (30-bit, sound for BabyBear).
pub const NON_REVOCATION_ORDERING_BITS: usize = 30;

/// Trace width for the non-revocation DSL circuit.
pub const NON_REVOCATION_TRACE_WIDTH: usize = 70;

/// (p-1)/2 for BabyBear, used in ordering range checks.
const HALF_P_MINUS_1: u32 = 1006632959;

/// Column indices for the non-revocation DSL circuit.
pub mod non_rev_col {
    use super::NON_REVOCATION_ORDERING_BITS;

    pub const COL_0: usize = 0;
    pub const COL_1: usize = 1;
    pub const COL_2: usize = 2;
    pub const COL_3: usize = 3;
    pub const COL_4: usize = 4;

    pub const DIFF_LEFT: usize = 5;
    pub const DIFF_LEFT_BITS_START: usize = 6;
    pub const DIFF_RIGHT: usize = DIFF_LEFT_BITS_START + NON_REVOCATION_ORDERING_BITS; // 36
    pub const DIFF_RIGHT_BITS_START: usize = DIFF_RIGHT + 1; // 37

    pub const IS_CONTROL: usize = DIFF_RIGHT_BITS_START + NON_REVOCATION_ORDERING_BITS; // 67
    pub const IS_MERKLE_LEFT: usize = IS_CONTROL + 1; // 68
    pub const IS_MERKLE_RIGHT: usize = IS_MERKLE_LEFT + 1; // 69

    #[inline]
    pub const fn diff_left_bit(i: usize) -> usize {
        DIFF_LEFT_BITS_START + i
    }

    #[inline]
    pub const fn diff_right_bit(i: usize) -> usize {
        DIFF_RIGHT_BITS_START + i
    }
}

/// Build the non-revocation `CircuitDescriptor`.
///
/// Proves: "My credential is NOT in the revocation tree" via sorted-tree
/// non-membership with 30-bit ordering range checks.
///
/// Public inputs: [revocation_root]
pub fn non_revocation_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1-C3: Row type selectors are binary
    constraints.push(ConstraintExpr::Binary {
        col: non_rev_col::IS_CONTROL,
    });
    constraints.push(ConstraintExpr::Binary {
        col: non_rev_col::IS_MERKLE_LEFT,
    });
    constraints.push(ConstraintExpr::Binary {
        col: non_rev_col::IS_MERKLE_RIGHT,
    });

    // C4: direction_bit is binary (gated by Merkle selectors)
    constraints.push(ConstraintExpr::Gated {
        selector_col: non_rev_col::IS_MERKLE_LEFT,
        inner: Box::new(ConstraintExpr::Binary {
            col: non_rev_col::COL_3,
        }),
    });
    constraints.push(ConstraintExpr::Gated {
        selector_col: non_rev_col::IS_MERKLE_RIGHT,
        inner: Box::new(ConstraintExpr::Binary {
            col: non_rev_col::COL_3,
        }),
    });

    // C5: Hash binding for Merkle rows
    constraints.push(ConstraintExpr::Gated {
        selector_col: non_rev_col::IS_MERKLE_LEFT,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: non_rev_col::COL_2,
            input_cols: vec![non_rev_col::COL_0, non_rev_col::COL_1],
        }),
    });
    constraints.push(ConstraintExpr::Gated {
        selector_col: non_rev_col::IS_MERKLE_RIGHT,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: non_rev_col::COL_2,
            input_cols: vec![non_rev_col::COL_0, non_rev_col::COL_1],
        }),
    });

    // C6: Ordering diff_left consistency
    constraints.push(ConstraintExpr::Gated {
        selector_col: non_rev_col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![non_rev_col::DIFF_LEFT],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![non_rev_col::COL_0],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![non_rev_col::COL_1],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![],
                },
            ],
        }),
    });

    // C7: Ordering diff_right consistency
    constraints.push(ConstraintExpr::Gated {
        selector_col: non_rev_col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![non_rev_col::DIFF_RIGHT],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![non_rev_col::COL_2],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![non_rev_col::COL_0],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![],
                },
            ],
        }),
    });

    // C8: diff_left bits are binary
    for i in 0..NON_REVOCATION_ORDERING_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: non_rev_col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Binary {
                col: non_rev_col::diff_left_bit(i),
            }),
        });
    }

    // C9: diff_right bits are binary
    for i in 0..NON_REVOCATION_ORDERING_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: non_rev_col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Binary {
                col: non_rev_col::diff_right_bit(i),
            }),
        });
    }

    // C10: diff_left range check reconstruction
    {
        let mut terms = Vec::new();
        let mut power_of_two = BabyBear::ONE;
        for i in 0..NON_REVOCATION_ORDERING_BITS {
            terms.push(PolyTerm {
                coeff: power_of_two,
                col_indices: vec![non_rev_col::diff_left_bit(i)],
            });
            power_of_two = power_of_two + power_of_two;
        }
        terms.push(PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![non_rev_col::DIFF_LEFT],
        });
        terms.push(PolyTerm {
            coeff: -BabyBear::new(HALF_P_MINUS_1),
            col_indices: vec![],
        });
        constraints.push(ConstraintExpr::Gated {
            selector_col: non_rev_col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Polynomial { terms }),
        });
    }

    // C11: diff_right range check reconstruction
    {
        let mut terms = Vec::new();
        let mut power_of_two = BabyBear::ONE;
        for i in 0..NON_REVOCATION_ORDERING_BITS {
            terms.push(PolyTerm {
                coeff: power_of_two,
                col_indices: vec![non_rev_col::diff_right_bit(i)],
            });
            power_of_two = power_of_two + power_of_two;
        }
        terms.push(PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![non_rev_col::DIFF_RIGHT],
        });
        terms.push(PolyTerm {
            coeff: -BabyBear::new(HALF_P_MINUS_1),
            col_indices: vec![],
        });
        constraints.push(ConstraintExpr::Gated {
            selector_col: non_rev_col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Polynomial { terms }),
        });
    }

    // C12: Adjacency constraint
    constraints.push(ConstraintExpr::Gated {
        selector_col: non_rev_col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![non_rev_col::COL_4],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![non_rev_col::COL_3],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![],
                },
            ],
        }),
    });

    // Boundary constraints
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::Index(NON_REVOCATION_TREE_DEPTH),
            col: non_rev_col::COL_2,
            pi_index: 0,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Index(2 * NON_REVOCATION_TREE_DEPTH),
            col: non_rev_col::COL_2,
            pi_index: 0,
        },
    ];

    // Column definitions
    let columns = vec![
        ColumnDef {
            name: "col0_ancestor_or_current".into(),
            index: non_rev_col::COL_0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "col1_left_or_sibling".into(),
            index: non_rev_col::COL_1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "col2_right_or_parent".into(),
            index: non_rev_col::COL_2,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "col3_leftpos_or_dir".into(),
            index: non_rev_col::COL_3,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "col4_rightpos".into(),
            index: non_rev_col::COL_4,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff_left".into(),
            index: non_rev_col::DIFF_LEFT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff_right".into(),
            index: non_rev_col::DIFF_RIGHT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "is_control".into(),
            index: non_rev_col::IS_CONTROL,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "is_merkle_left".into(),
            index: non_rev_col::IS_MERKLE_LEFT,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "is_merkle_right".into(),
            index: non_rev_col::IS_MERKLE_RIGHT,
            kind: ColumnKind::Binary,
        },
    ];

    CircuitDescriptor {
        name: NON_REVOCATION_AIR_NAME.into(),
        trace_width: NON_REVOCATION_TRACE_WIDTH,
        max_degree: 3,
        columns,
        constraints,
        boundaries,
        public_input_count: 1,
        lookup_tables: vec![],
    }
}

/// Create a `DslCircuit` for non-revocation proofs.
pub fn non_revocation_circuit() -> DslCircuit {
    DslCircuit::new(non_revocation_descriptor())
}

// ============================================================================
// Derivation
// ============================================================================

/// Auxiliary column indices for C2 (ConditionalNonzero) inverse columns.
pub use crate::dsl::derivation::BODY_HASH_INV_START as DERIVATION_BODY_HASH_INV_START;

/// Extended trace width including auxiliary inverse columns for C2.
pub use crate::dsl::derivation::EXTENDED_TRACE_WIDTH as DERIVATION_EXTENDED_TRACE_WIDTH;

/// Build the derivation AIR as a `CircuitDescriptor`.
///
/// Encodes constraints C1-C28 with 379 columns (371 standard + 8 inverse auxiliary).
/// This delegates to [`crate::dsl::derivation::derivation_circuit_descriptor()`] which
/// contains the correct, fully-specified 28-constraint implementation.
///
/// Public inputs: [state_root, derived_hash, not_after, org_id, budget]
pub fn derivation_descriptor() -> CircuitDescriptor {
    crate::dsl::derivation::derivation_circuit_descriptor()
}

/// Create a `DslCircuit` for derivation proofs.
pub fn derivation_circuit() -> DslCircuit {
    crate::dsl::derivation::derivation_dsl_circuit()
}

/// AIR name for DSL base predicate proofs.
pub const PREDICATE_DSL_AIR_NAME: &str = "pyana-predicate-dsl-v2";

/// AIR name for DSL relational predicate proofs.
pub const RELATIONAL_PREDICATE_DSL_AIR_NAME: &str = "pyana-relational-predicate-dsl-v2";

/// AIR name for DSL compound predicate proofs.
pub const COMPOUND_PREDICATE_DSL_AIR_NAME: &str = "pyana-compound-predicate-dsl-v2";

/// Returns `true` if the given AIR name matches any of the standard DSL circuits.
///
/// Used by verifiers to determine if a proof can be verified through the unified
/// DSL verification path.
pub fn is_known_dsl_air(air_name: &str) -> bool {
    matches!(
        air_name,
        EFFECT_VM_AIR_NAME
            | MERKLE_POSEIDON2_AIR_NAME
            | BLINDED_MERKLE_AIR_NAME
            | NON_REVOCATION_AIR_NAME
            | DERIVATION_AIR_NAME
            | PREDICATE_DSL_AIR_NAME
            | RELATIONAL_PREDICATE_DSL_AIR_NAME
            | COMPOUND_PREDICATE_DSL_AIR_NAME
    )
}

/// Get the appropriate `DslCircuit` for a given AIR name, or `None` if unrecognized.
///
/// This is the single dispatch point for verifying standard proofs. All standard
/// proof types (membership, blinded membership, non-revocation, derivation, predicates)
/// are handled here. Effect VM uses its own `EffectVmAir` directly.
pub fn circuit_for_air_name(air_name: &str) -> Option<DslCircuit> {
    match air_name {
        MERKLE_POSEIDON2_AIR_NAME => Some(merkle_poseidon2_circuit()),
        BLINDED_MERKLE_AIR_NAME => Some(blinded_merkle_poseidon2_circuit()),
        NON_REVOCATION_AIR_NAME => Some(non_revocation_circuit()),
        DERIVATION_AIR_NAME => Some(derivation_circuit()),
        PREDICATE_DSL_AIR_NAME => Some(DslCircuit::new(
            crate::dsl::predicates::predicate_descriptor(),
        )),
        RELATIONAL_PREDICATE_DSL_AIR_NAME => Some(DslCircuit::new(
            crate::dsl::predicates::relational_predicate_descriptor(),
        )),
        COMPOUND_PREDICATE_DSL_AIR_NAME => {
            Some(crate::dsl::predicates::compound_predicate_dsl_circuit())
        }
        _ => None,
    }
}
