//! Production non-revocation proving via DSL circuit.
//!
//! This module provides the canonical implementation for non-revocation proofs:
//! - [`DslRevocationTree`] — sorted binary Merkle tree (hash_fact-based)
//! - [`prove_non_revocation_dsl`] — generate a STARK proof of non-membership
//! - [`verify_non_revocation_dsl`] — verify a STARK non-membership proof
//! - [`revocation_hash_to_field`] — convert 32-byte revocation hash to BabyBear
//!
//! Supersedes the old `pyana_circuit::non_revocation_air` (4-ary, hand-written AIR)
//! and the test-only `pyana_dsl_tests::non_revocation_dsl`.

use crate::field::BabyBear;
use crate::poseidon2::{hash_fact, hash_many};
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Constants
// ============================================================================

/// Tree depth for the DSL non-revocation Merkle tree.
/// Binary tree of depth 4 supports 16 leaves.
pub const TREE_DEPTH: usize = 4;

/// Alias for external consumers that used `REVOCATION_TREE_DEPTH`.
pub const REVOCATION_TREE_DEPTH: usize = TREE_DEPTH;

/// Number of bits for the ordering range check.
///
/// BabyBear p = 2013265921, (p-1)/2 = 1006632960 < 2^30 = 1073741824.
/// To prove diff < (p-1)/2 (which implies canonical ordering), we prove that
/// `(p-1)/2 - diff` fits in 30 bits. If diff >= (p-1)/2, the subtraction
/// wraps to a value > 2^30 that cannot be decomposed into 30 bits.
/// Using fewer bits (e.g., 16) is UNSOUND: a malicious prover can craft
/// values that pass the 16-bit check but violate the ordering property.
pub const ORDERING_BITS: usize = 30;

/// Trace width for the non-revocation DSL circuit.
/// 5 shared + 1 diff_left + 30 diff_left_bits + 1 diff_right + 30 diff_right_bits + 3 selectors
/// + 1 sentinel selector = 71
pub const TRACE_WIDTH: usize = 71;

/// (p-1)/2 for BabyBear, used in ordering range checks.
pub const HALF_P_MINUS_1: u32 = 1006632959;

/// Sentinel min value (0) for the sorted tree.
pub const SENTINEL_MIN: BabyBear = BabyBear::ZERO;

/// Sentinel max value (p-1) for the sorted tree.
pub const SENTINEL_MAX: BabyBear = BabyBear(2013265920);

// ============================================================================
// Column layout
// ============================================================================

/// Column indices for the non-revocation DSL circuit.
pub mod col {
    use super::ORDERING_BITS;

    // Shared columns (used differently on control vs Merkle rows)
    pub const COL_0: usize = 0; // ancestor_hash (control) / current (Merkle)
    pub const COL_1: usize = 1; // left_neighbor (control) / sibling (Merkle)
    pub const COL_2: usize = 2; // right_neighbor (control) / parent (Merkle)
    pub const COL_3: usize = 3; // left_position (control) / direction_bit (Merkle)
    pub const COL_4: usize = 4; // right_position (control)

    // Ordering columns (control row only)
    pub const DIFF_LEFT: usize = 5;
    pub const DIFF_LEFT_BITS_START: usize = 6;
    pub const DIFF_RIGHT: usize = DIFF_LEFT_BITS_START + ORDERING_BITS; // 36
    pub const DIFF_RIGHT_BITS_START: usize = DIFF_RIGHT + 1; // 37

    // Row type selectors
    pub const IS_CONTROL: usize = DIFF_RIGHT_BITS_START + ORDERING_BITS; // 67
    pub const IS_MERKLE_LEFT: usize = IS_CONTROL + 1; // 68
    pub const IS_MERKLE_RIGHT: usize = IS_MERKLE_LEFT + 1; // 69
    pub const RIGHT_IS_SENTINEL: usize = IS_MERKLE_RIGHT + 1; // 70

    #[inline]
    pub const fn diff_left_bit(i: usize) -> usize {
        DIFF_LEFT_BITS_START + i
    }

    #[inline]
    pub const fn diff_right_bit(i: usize) -> usize {
        DIFF_RIGHT_BITS_START + i
    }
}

/// Public input indices.
pub mod pi {
    pub const REVOCATION_ROOT: usize = 0;
}

// ============================================================================
// Circuit descriptor
// ============================================================================

/// Build the non-revocation CircuitDescriptor.
///
/// Encodes constraints C1-C12 for sorted-tree non-membership with 30-bit
/// ordering range checks and binary Merkle path authentication.
pub fn non_revocation_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1-C3: Row type selectors are binary
    constraints.push(ConstraintExpr::Binary {
        col: col::IS_CONTROL,
    });
    constraints.push(ConstraintExpr::Binary {
        col: col::IS_MERKLE_LEFT,
    });
    constraints.push(ConstraintExpr::Binary {
        col: col::IS_MERKLE_RIGHT,
    });
    constraints.push(ConstraintExpr::Binary {
        col: col::RIGHT_IS_SENTINEL,
    });

    // C4: direction_bit (col 3) is binary on Merkle rows
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_LEFT,
        inner: Box::new(ConstraintExpr::Binary { col: col::COL_3 }),
    });
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_RIGHT,
        inner: Box::new(ConstraintExpr::Binary { col: col::COL_3 }),
    });

    // C5: Hash binding for Merkle rows: col2 = hash_fact(col0, [col1])
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_LEFT,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::COL_2,
            input_cols: vec![col::COL_0, col::COL_1],
        }),
    });
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_RIGHT,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::COL_2,
            input_cols: vec![col::COL_0, col::COL_1],
        }),
    });

    // C6: Ordering diff_left consistency (control row):
    // diff_left == ancestor_hash - left_neighbor - 1
    // => col5 - col0 + col1 + 1 == 0
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::DIFF_LEFT],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::COL_0],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::COL_1],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![],
                }, // constant +1
            ],
        }),
    });

    // C7: Ordering diff_right consistency (control row, unless the upper
    // neighbor is the max sentinel):
    // diff_right == right_neighbor - ancestor_hash - 1
    // => col_DIFF_RIGHT - col2 + col0 + 1 == 0
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::InvertedGated {
            selector_col: col::RIGHT_IS_SENTINEL,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![col::DIFF_RIGHT],
                    },
                    PolyTerm {
                        coeff: -BabyBear::ONE,
                        col_indices: vec![col::COL_2],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![col::COL_0],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![],
                    }, // constant +1
                ],
            }),
        }),
    });

    // C7b: A disabled right-gap check is allowed only for the canonical max sentinel.
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::RIGHT_IS_SENTINEL, col::COL_2],
                },
                PolyTerm {
                    coeff: -SENTINEL_MAX,
                    col_indices: vec![col::RIGHT_IS_SENTINEL],
                },
            ],
        }),
    });

    // C8: diff_left bits are binary (gated by is_control)
    for i in 0..ORDERING_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Binary {
                col: col::diff_left_bit(i),
            }),
        });
    }

    // C9: diff_right bits are binary (gated by is_control)
    for i in 0..ORDERING_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Binary {
                col: col::diff_right_bit(i),
            }),
        });
    }

    // C10: diff_left range check reconstruction (gated by is_control):
    // sum(diff_left_bits[i] * 2^i) == HALF_P_MINUS_1 - diff_left
    // => sum(bits[i] * 2^i) + diff_left - HALF_P_MINUS_1 == 0
    {
        let mut terms = Vec::new();
        let mut power_of_two = BabyBear::ONE;
        for i in 0..ORDERING_BITS {
            terms.push(PolyTerm {
                coeff: power_of_two,
                col_indices: vec![col::diff_left_bit(i)],
            });
            power_of_two = power_of_two + power_of_two;
        }
        terms.push(PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![col::DIFF_LEFT],
        });
        terms.push(PolyTerm {
            coeff: -BabyBear::new(HALF_P_MINUS_1),
            col_indices: vec![],
        });
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Polynomial { terms }),
        });
    }

    // C11: diff_right range check reconstruction (gated by is_control):
    // sum(diff_right_bits[i] * 2^i) == HALF_P_MINUS_1 - diff_right
    // => sum(bits[i] * 2^i) + diff_right - HALF_P_MINUS_1 == 0
    {
        let mut terms = Vec::new();
        let mut power_of_two = BabyBear::ONE;
        for i in 0..ORDERING_BITS {
            terms.push(PolyTerm {
                coeff: power_of_two,
                col_indices: vec![col::diff_right_bit(i)],
            });
            power_of_two = power_of_two + power_of_two;
        }
        terms.push(PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![col::DIFF_RIGHT],
        });
        terms.push(PolyTerm {
            coeff: -BabyBear::new(HALF_P_MINUS_1),
            col_indices: vec![],
        });
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::InvertedGated {
                selector_col: col::RIGHT_IS_SENTINEL,
                inner: Box::new(ConstraintExpr::Polynomial { terms }),
            }),
        });
    }

    // C12: Adjacency constraint (control row): right_position - left_position - 1 == 0
    // col4 - col3 - 1 == 0
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::COL_4],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::COL_3],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![],
                }, // constant -1
            ],
        }),
    });

    // Boundary constraints: bind revocation_root to Merkle path tops.
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::Index(TREE_DEPTH),
            col: col::COL_2,
            pi_index: pi::REVOCATION_ROOT,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Index(2 * TREE_DEPTH),
            col: col::COL_2,
            pi_index: pi::REVOCATION_ROOT,
        },
    ];

    // Column definitions
    let columns = vec![
        ColumnDef {
            name: "col0_ancestor_or_current".into(),
            index: col::COL_0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "col1_left_or_sibling".into(),
            index: col::COL_1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "col2_right_or_parent".into(),
            index: col::COL_2,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "col3_leftpos_or_dir".into(),
            index: col::COL_3,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "col4_rightpos".into(),
            index: col::COL_4,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff_left".into(),
            index: col::DIFF_LEFT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff_right".into(),
            index: col::DIFF_RIGHT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "is_control".into(),
            index: col::IS_CONTROL,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "is_merkle_left".into(),
            index: col::IS_MERKLE_LEFT,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "is_merkle_right".into(),
            index: col::IS_MERKLE_RIGHT,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "right_is_sentinel".into(),
            index: col::RIGHT_IS_SENTINEL,
            kind: ColumnKind::Binary,
        },
    ];

    CircuitDescriptor {
        name: "pyana-non-revocation-dsl-v1".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 3, // Gated(Binary) is degree 3: selector * col * (col - 1)
        columns,
        constraints,
        boundaries,
        public_input_count: 1, // [revocation_root]
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the non-revocation descriptor.
pub fn non_revocation_dsl_circuit() -> DslCircuit {
    DslCircuit::new(non_revocation_circuit_descriptor())
}

// ============================================================================
// Sorted binary Merkle tree (hash_fact-based)
// ============================================================================

/// A sorted revocation tree using binary Merkle with hash_fact.
///
/// Leaves are sorted BabyBear field elements. The tree is padded to 2^TREE_DEPTH leaves.
/// Internal nodes are computed as: parent = hash_fact(left_child, [right_child]).
#[derive(Clone, Debug)]
pub struct DslRevocationTree {
    /// All levels of the tree. levels[0] = leaves (padded), levels[depth] = [root].
    levels: Vec<Vec<BabyBear>>,
    /// The sorted leaves (including sentinels, before padding).
    sorted_leaves: Vec<BabyBear>,
    /// Tree depth.
    depth: usize,
}

impl DslRevocationTree {
    /// Build a new sorted revocation tree from revocation hashes.
    pub fn new(mut hashes: Vec<BabyBear>, depth: usize) -> Self {
        // Add sentinels
        hashes.push(SENTINEL_MIN);
        hashes.push(SENTINEL_MAX);
        hashes.sort_by_key(|h| h.0);
        hashes.dedup();

        let capacity = 1usize << depth;
        let mut leaves = hashes.clone();
        leaves.resize(capacity, BabyBear::ZERO);

        // Build tree levels bottom-up
        let mut levels = vec![leaves];
        for _ in 0..depth {
            let prev = levels.last().unwrap();
            let mut next_level = Vec::with_capacity(prev.len() / 2);
            for chunk in prev.chunks(2) {
                next_level.push(hash_fact(chunk[0], &[chunk[1]]));
            }
            levels.push(next_level);
        }

        Self {
            levels,
            sorted_leaves: hashes,
            depth,
        }
    }

    /// Get the Merkle root.
    pub fn root(&self) -> BabyBear {
        self.levels[self.depth][0]
    }

    /// Check if a hash is in the revocation set (excluding sentinels).
    pub fn contains(&self, hash: &BabyBear) -> bool {
        if *hash == SENTINEL_MIN || *hash == SENTINEL_MAX {
            return false;
        }
        self.sorted_leaves
            .binary_search_by_key(&hash.0, |h| h.0)
            .is_ok()
    }

    /// Number of sorted leaves (including sentinels).
    pub fn num_leaves(&self) -> usize {
        self.sorted_leaves.len()
    }

    /// Number of actual revoked entries (excluding sentinels).
    pub fn num_revoked(&self) -> usize {
        self.sorted_leaves
            .iter()
            .filter(|h| **h != SENTINEL_MIN && **h != SENTINEL_MAX)
            .count()
    }

    /// Whether the tree has no revoked entries.
    pub fn is_empty(&self) -> bool {
        self.num_revoked() == 0
    }

    /// Generate a Merkle membership proof for a leaf at the given position.
    ///
    /// Returns (siblings, directions) where:
    /// - siblings[i] = the sibling at level i
    /// - directions[i] = 0 if current is left child, 1 if right child
    pub fn prove_membership(&self, position: usize) -> Option<(Vec<BabyBear>, Vec<u8>)> {
        let capacity = 1usize << self.depth;
        if position >= capacity {
            return None;
        }

        let mut siblings = Vec::with_capacity(self.depth);
        let mut directions = Vec::with_capacity(self.depth);
        let mut idx = position;

        for level in 0..self.depth {
            let sibling_idx = idx ^ 1; // flip last bit to get sibling
            siblings.push(self.levels[level][sibling_idx]);
            directions.push((idx & 1) as u8); // 0 if left, 1 if right
            idx >>= 1;
        }

        Some((siblings, directions))
    }

    /// Generate a non-membership witness for a hash NOT in the tree.
    ///
    /// Returns None if the hash IS in the tree.
    pub fn prove_non_membership(&self, hash: &BabyBear) -> Option<NonMembershipWitnessDsl> {
        if *hash == SENTINEL_MIN || *hash == SENTINEL_MAX {
            return None;
        }

        match self.sorted_leaves.binary_search_by_key(&hash.0, |h| h.0) {
            Ok(_) => None, // IS in the tree
            Err(idx) => {
                assert!(idx > 0 && idx < self.sorted_leaves.len());
                let left_pos = idx - 1;
                let right_pos = idx;
                let left_val = self.sorted_leaves[left_pos];
                let right_val = self.sorted_leaves[right_pos];

                let (left_siblings, left_directions) = self.prove_membership(left_pos)?;
                let (right_siblings, right_directions) = self.prove_membership(right_pos)?;

                Some(NonMembershipWitnessDsl {
                    ancestor_hash: *hash,
                    left_neighbor: left_val,
                    right_neighbor: right_val,
                    left_siblings,
                    left_directions,
                    right_siblings,
                    right_directions,
                    left_tree_position: left_pos,
                    right_tree_position: right_pos,
                })
            }
        }
    }
}

/// Non-membership witness for the DSL circuit.
#[derive(Clone, Debug)]
pub struct NonMembershipWitnessDsl {
    pub ancestor_hash: BabyBear,
    pub left_neighbor: BabyBear,
    pub right_neighbor: BabyBear,
    pub left_siblings: Vec<BabyBear>,
    pub left_directions: Vec<u8>,
    pub right_siblings: Vec<BabyBear>,
    pub right_directions: Vec<u8>,
    pub left_tree_position: usize,
    pub right_tree_position: usize,
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate the execution trace for a non-membership proof.
///
/// Returns (trace, public_inputs) where trace is padded to power of 2.
pub fn generate_non_revocation_trace(
    witness: &NonMembershipWitnessDsl,
    revocation_root: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let rows_needed = 1 + 2 * TREE_DEPTH; // 1 control + TREE_DEPTH left + TREE_DEPTH right = 9
    let total_rows = rows_needed.next_power_of_two().max(16); // padded to power of 2

    let mut trace = Vec::with_capacity(total_rows);

    // --- Control row (row 0) ---
    let mut control = vec![BabyBear::ZERO; TRACE_WIDTH];
    control[col::COL_0] = witness.ancestor_hash;
    control[col::COL_1] = witness.left_neighbor;
    control[col::COL_2] = witness.right_neighbor;
    control[col::COL_3] = BabyBear::new(witness.left_tree_position as u32);
    control[col::COL_4] = BabyBear::new(witness.right_tree_position as u32);

    // Ordering witness: diff_left = ancestor_hash - left_neighbor - 1
    let diff_left = witness.ancestor_hash - witness.left_neighbor - BabyBear::ONE;
    control[col::DIFF_LEFT] = diff_left;
    let diff_left_u32 = diff_left.as_u32();
    if diff_left_u32 <= HALF_P_MINUS_1 {
        let check_val = HALF_P_MINUS_1 - diff_left_u32;
        for i in 0..ORDERING_BITS {
            control[col::diff_left_bit(i)] = BabyBear::new((check_val >> i) & 1);
        }
    }

    // Ordering witness: diff_right = right_neighbor - ancestor_hash - 1.
    // The max sentinel is the one legal upper-tail case where the canonical
    // integer gap may exceed the half-field range bound; the sentinel selector
    // disables only the right-gap reconstruction/range check for that row.
    if witness.right_neighbor == SENTINEL_MAX {
        control[col::RIGHT_IS_SENTINEL] = BabyBear::ONE;
    } else {
        let diff_right = witness.right_neighbor - witness.ancestor_hash - BabyBear::ONE;
        control[col::DIFF_RIGHT] = diff_right;
        let diff_right_u32 = diff_right.as_u32();
        if diff_right_u32 <= HALF_P_MINUS_1 {
            let check_val = HALF_P_MINUS_1 - diff_right_u32;
            for i in 0..ORDERING_BITS {
                control[col::diff_right_bit(i)] = BabyBear::new((check_val >> i) & 1);
            }
        }
    }

    control[col::IS_CONTROL] = BabyBear::ONE;
    control[col::IS_MERKLE_LEFT] = BabyBear::ZERO;
    control[col::IS_MERKLE_RIGHT] = BabyBear::ZERO;
    trace.push(control);

    // --- Left Merkle rows (rows 1..=TREE_DEPTH) ---
    let mut current = witness.left_neighbor;
    for level in 0..TREE_DEPTH {
        let sibling = witness.left_siblings[level];
        let dir = witness.left_directions[level];

        // Arrange col0, col1 so that hash_fact(col0, [col1]) = parent
        let (left_child, right_child) = if dir == 0 {
            (current, sibling)
        } else {
            (sibling, current)
        };
        let parent = hash_fact(left_child, &[right_child]);

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        row[col::COL_0] = left_child;
        row[col::COL_1] = right_child;
        row[col::COL_2] = parent;
        row[col::COL_3] = BabyBear::new(dir as u32);
        row[col::IS_CONTROL] = BabyBear::ZERO;
        row[col::IS_MERKLE_LEFT] = BabyBear::ONE;
        row[col::IS_MERKLE_RIGHT] = BabyBear::ZERO;
        trace.push(row);

        current = parent;
    }

    // --- Right Merkle rows (rows TREE_DEPTH+1..=2*TREE_DEPTH) ---
    current = witness.right_neighbor;
    for level in 0..TREE_DEPTH {
        let sibling = witness.right_siblings[level];
        let dir = witness.right_directions[level];

        let (left_child, right_child) = if dir == 0 {
            (current, sibling)
        } else {
            (sibling, current)
        };
        let parent = hash_fact(left_child, &[right_child]);

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        row[col::COL_0] = left_child;
        row[col::COL_1] = right_child;
        row[col::COL_2] = parent;
        row[col::COL_3] = BabyBear::new(dir as u32);
        row[col::IS_CONTROL] = BabyBear::ZERO;
        row[col::IS_MERKLE_LEFT] = BabyBear::ZERO;
        row[col::IS_MERKLE_RIGHT] = BabyBear::ONE;
        trace.push(row);

        current = parent;
    }

    // --- Padding rows (inactive) ---
    while trace.len() < total_rows {
        let row = vec![BabyBear::ZERO; TRACE_WIDTH];
        // All selectors are zero, so no constraints fire on padding rows
        trace.push(row);
    }

    let public_inputs = vec![revocation_root];
    (trace, public_inputs)
}

// ============================================================================
// Production prove / verify API
// ============================================================================

/// Generate a STARK proof that `item_hash` is NOT in the given revocation tree.
///
/// Returns `Err` if the item IS in the tree (cannot prove non-membership).
pub fn prove_non_revocation_dsl(
    tree: &DslRevocationTree,
    item_hash: BabyBear,
) -> Result<StarkProof, String> {
    let witness = tree
        .prove_non_membership(&item_hash)
        .ok_or_else(|| "item is in the revocation tree (revoked)".to_string())?;

    let root = tree.root();
    let (trace, public_inputs) = generate_non_revocation_trace(&witness, root);
    let circuit = non_revocation_dsl_circuit();
    Ok(stark::prove(&circuit, &trace, &public_inputs))
}

/// Verify a STARK non-revocation proof against the given root and item hash.
///
/// The verifier only needs the revocation root (committed by the federation)
/// and the proof. The item identity remains private.
pub fn verify_non_revocation_dsl(
    proof: &StarkProof,
    root: BabyBear,
    _item_hash: BabyBear,
) -> Result<(), String> {
    let circuit = non_revocation_dsl_circuit();
    let public_inputs = vec![root];
    stark::verify(&circuit, proof, &public_inputs)
}

// ============================================================================
// Utility functions
// ============================================================================

/// Convert a 32-byte revocation hash (from `DerivationTree::revocation_hash`) to a BabyBear
/// field element suitable for the sorted revocation tree.
///
/// Uses Poseidon2 to compress the 32 bytes into a single field element,
/// matching the approach used in `commit::poseidon2_tree::commitment_to_field`.
pub fn revocation_hash_to_field(hash: &[u8; 32]) -> BabyBear {
    let elements = BabyBear::encode_hash(hash);
    hash_many(&elements)
}
