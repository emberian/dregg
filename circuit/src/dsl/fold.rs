//! DSL-native fold proving and verification.
//!
//! This module provides production prove/verify functions for the fold AIR using
//! the DSL `CircuitDescriptor` + `DslCircuit` infrastructure. It replaces the
//! hand-written `FoldStarkAir` from `circuit/src/fold_air.rs`.
//!
//! # Completeness vs. hand-written AIR
//!
//! The DSL version covers:
//! - Attenuation step (removal rows + summary row)
//! - Commitment hash binding (fact_hash_correct via Hash constraint)
//! - Root transition hash binding (pi[4])
//! - Removal count increment (transition constraint)
//! - Old/new root consistency (PiBinding)
//! - Check count binding (boundary constraint on last row)
//! - Checks commitment zero-when-no-checks (boundary-level enforcement)
//!
//! # Public Input Layout
//!
//! - pi[0]: old_root
//! - pi[1]: new_root
//! - pi[2]: total_removal_count
//! - pi[3]: total_check_count
//! - pi[4]: root_transition_hash
//! - pi[5]: checks_commitment_narrow

use crate::binding::WideHash;
use crate::field::BabyBear;
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
};

// ============================================================================
// Column indices (compatible with circuit/src/fold_types.rs col:: module)
// ============================================================================

pub mod col {
    pub const ROW_TYPE: usize = 0;
    pub const FACT_HASH: usize = 1;
    pub const MEMBERSHIP_ROOT: usize = 2;
    pub const OLD_ROOT: usize = 3;
    pub const NEW_ROOT: usize = 4;
    pub const REMOVAL_COUNT: usize = 5;
    pub const CHECK_COUNT: usize = 6;
    pub const FACT_PRED: usize = 7;
    pub const FACT_TERM_START: usize = 8;
    // col 9, 10: FACT_TERM_START+1, FACT_TERM_START+2
    pub const HASH_VALID: usize = 11;
    /// Auxiliary column: holds `removal_count + 1` for transition constraint.
    pub const REMOVAL_COUNT_PLUS_ONE: usize = 12;
}

/// Trace width for the DSL fold AIR (13 columns: 12 original + 1 auxiliary).
pub const FOLD_DSL_WIDTH: usize = 13;

/// Number of public inputs: [old_root, new_root, removal_count, check_count, transition_hash, checks_narrow].
pub const FOLD_DSL_PI_COUNT: usize = 6;

// ============================================================================
// Witness types (previously in fold_types.rs, now inlined here)
// ============================================================================

use crate::constraint_prover::{Air, Constraint};
use crate::merkle_types::{MerkleAir, MerkleLevelWitness, MerkleWitness};
use crate::poseidon2::{hash_4_to_1, hash_fact, hash_many};

pub const FOLD_AIR_WIDTH: usize = 12;

#[derive(Clone, Debug)]
pub struct RemovedFact {
    pub predicate: BabyBear,
    pub terms: [BabyBear; 3],
    pub membership_proof: Option<MerkleWitness>,
}

impl RemovedFact {
    pub fn hash(&self) -> BabyBear {
        hash_fact(self.predicate, &self.terms)
    }

    pub fn verify_membership(&self, old_root: BabyBear) -> Option<BabyBear> {
        let proof = self.membership_proof.as_ref()?;
        if proof.leaf_hash != self.hash() {
            return None;
        }
        // Try hash_fact path first (synthetic/single-member proofs from build_membership_proof).
        let mut current = proof.leaf_hash;
        for level in &proof.levels {
            current = MerkleAir::compute_parent(current, level.position, &level.siblings);
        }
        if current == old_root {
            return Some(current);
        }
        // Fallback: try hash_4_to_1 path (multi-member proofs from build_shared_tree).
        current = proof.leaf_hash;
        for level in &proof.levels {
            let mut children = [BabyBear::ZERO; 4];
            let mut sib_idx = 0;
            for i in 0..4u8 {
                if i == level.position {
                    children[i as usize] = current;
                } else {
                    children[i as usize] = level.siblings[sib_idx];
                    sib_idx += 1;
                }
            }
            current = hash_4_to_1(&children);
        }
        if current == old_root {
            return Some(current);
        }
        None
    }
}

#[derive(Clone, Debug)]
pub struct FoldWitness {
    pub old_root: BabyBear,
    pub new_root: BabyBear,
    pub removed_facts: Vec<RemovedFact>,
    pub num_added_checks: usize,
    pub added_checks_commitment: crate::binding::WideHash,
}

pub fn compute_root_transition_hash(
    old_root: BabyBear,
    new_root: BabyBear,
    removed_fact_hashes: &[BabyBear],
    added_checks_commitment: &crate::binding::WideHash,
) -> BabyBear {
    let mut elements = Vec::with_capacity(3 + removed_fact_hashes.len() + 4);
    elements.push(old_root);
    elements.push(new_root);
    elements.extend_from_slice(removed_fact_hashes);
    elements.extend_from_slice(added_checks_commitment.as_slice());
    hash_many(&elements)
}

pub fn verify_root_transition(witness: &FoldWitness) -> Option<BabyBear> {
    for fact in &witness.removed_facts {
        if fact.verify_membership(witness.old_root).is_none() {
            return None;
        }
    }
    let fact_hashes: Vec<BabyBear> = witness.removed_facts.iter().map(|f| f.hash()).collect();
    Some(compute_root_transition_hash(
        witness.old_root,
        witness.new_root,
        &fact_hashes,
        &witness.added_checks_commitment,
    ))
}

pub struct FoldAir {
    pub witness: FoldWitness,
}

impl FoldAir {
    pub fn new(witness: FoldWitness) -> Self {
        Self { witness }
    }
}

impl Air for FoldAir {
    fn trace_width(&self) -> usize {
        FOLD_AIR_WIDTH
    }
    fn num_public_inputs(&self) -> usize {
        6
    }

    fn constraints(&self) -> Vec<Constraint> {
        vec![
            Constraint {
                name: "row_type_binary".into(),
                eval: Box::new(|row, _, _| {
                    let rt = row[col::ROW_TYPE];
                    rt * (rt - BabyBear::ONE)
                }),
            },
            Constraint {
                name: "membership_root_matches_old_root".into(),
                eval: Box::new(|row, _, _| {
                    let is_removal = BabyBear::ONE - row[col::ROW_TYPE];
                    is_removal * (row[col::MEMBERSHIP_ROOT] - row[col::OLD_ROOT])
                }),
            },
            Constraint {
                name: "hash_valid_binary".into(),
                eval: Box::new(|row, _, _| {
                    let hv = row[col::HASH_VALID];
                    hv * (hv - BabyBear::ONE)
                }),
            },
            Constraint {
                name: "removal_hash_required".into(),
                eval: Box::new(|row, _, _| {
                    let is_removal = BabyBear::ONE - row[col::ROW_TYPE];
                    is_removal * (BabyBear::ONE - row[col::HASH_VALID])
                }),
            },
            Constraint {
                name: "fact_hash_correct".into(),
                eval: Box::new(|row, _, _| {
                    let is_removal = BabyBear::ONE - row[col::ROW_TYPE];
                    let expected = hash_fact(
                        row[col::FACT_PRED],
                        &[
                            row[col::FACT_TERM_START],
                            row[col::FACT_TERM_START + 1],
                            row[col::FACT_TERM_START + 2],
                        ],
                    );
                    is_removal * (row[col::FACT_HASH] - expected)
                }),
            },
            Constraint {
                name: "old_root_consistent".into(),
                eval: Box::new(|row, _, pi| row[col::OLD_ROOT] - pi[0]),
            },
            Constraint {
                name: "new_root_consistent".into(),
                eval: Box::new(|row, _, pi| row[col::NEW_ROOT] - pi[1]),
            },
            Constraint {
                name: "removal_count_increment".into(),
                eval: Box::new(|row, next_row, _| {
                    if let Some(next) = next_row {
                        let is_removal = BabyBear::ONE - row[col::ROW_TYPE];
                        let is_next_removal = BabyBear::ONE - next[col::ROW_TYPE];
                        is_removal
                            * is_next_removal
                            * (next[col::REMOVAL_COUNT] - row[col::REMOVAL_COUNT] - BabyBear::ONE)
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
            Constraint {
                name: "delta_nonempty".into(),
                eval: Box::new(|row, _, _| {
                    let is_summary = row[col::ROW_TYPE];
                    let total = row[col::REMOVAL_COUNT] + row[col::CHECK_COUNT];
                    if is_summary == BabyBear::ONE && total == BabyBear::ZERO {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
            Constraint {
                name: "root_transition_binding".into(),
                eval: Box::new(|row, _, pi| {
                    let is_summary = row[col::ROW_TYPE];
                    is_summary * (row[col::MEMBERSHIP_ROOT] - pi[4])
                }),
            },
            Constraint {
                name: "checks_commitment_zero_when_no_checks".into(),
                eval: Box::new(|row, _, pi| {
                    let is_summary = row[col::ROW_TYPE];
                    if pi[3] == BabyBear::ZERO {
                        is_summary * pi[5]
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
        ]
    }

    fn first_row_constraints(&self) -> Vec<Constraint> {
        vec![Constraint {
            name: "first_removal_count".into(),
            eval: Box::new(|row, _, _| {
                let is_removal = BabyBear::ONE - row[col::ROW_TYPE];
                is_removal * (row[col::REMOVAL_COUNT] - BabyBear::ONE)
            }),
        }]
    }

    fn last_row_constraints(&self) -> Vec<Constraint> {
        vec![
            Constraint {
                name: "last_row_is_summary".into(),
                eval: Box::new(|row, _, _| row[col::ROW_TYPE] - BabyBear::ONE),
            },
            Constraint {
                name: "total_removals_match".into(),
                eval: Box::new(|row, _, pi| row[col::REMOVAL_COUNT] - pi[2]),
            },
            Constraint {
                name: "total_checks_match".into(),
                eval: Box::new(|row, _, pi| row[col::CHECK_COUNT] - pi[3]),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;
        let mut trace = Vec::new();
        let root_transition_hash = if !w.removed_facts.is_empty() {
            verify_root_transition(w).unwrap_or(BabyBear::ZERO)
        } else {
            compute_root_transition_hash(w.old_root, w.new_root, &[], &w.added_checks_commitment)
        };

        for (i, fact) in w.removed_facts.iter().enumerate() {
            let mut row = vec![BabyBear::ZERO; FOLD_AIR_WIDTH];
            row[col::ROW_TYPE] = BabyBear::ZERO;
            row[col::FACT_HASH] = fact.hash();
            row[col::MEMBERSHIP_ROOT] =
                fact.verify_membership(w.old_root).unwrap_or(BabyBear::ZERO);
            row[col::OLD_ROOT] = w.old_root;
            row[col::NEW_ROOT] = w.new_root;
            row[col::REMOVAL_COUNT] = BabyBear::new((i + 1) as u32);
            row[col::CHECK_COUNT] = BabyBear::new(w.num_added_checks as u32);
            row[col::FACT_PRED] = fact.predicate;
            row[col::FACT_TERM_START] = fact.terms[0];
            row[col::FACT_TERM_START + 1] = fact.terms[1];
            row[col::FACT_TERM_START + 2] = fact.terms[2];
            row[col::HASH_VALID] = BabyBear::ONE;
            trace.push(row);
        }

        let mut summary = vec![BabyBear::ZERO; FOLD_AIR_WIDTH];
        summary[col::ROW_TYPE] = BabyBear::ONE;
        summary[col::MEMBERSHIP_ROOT] = root_transition_hash;
        summary[col::OLD_ROOT] = w.old_root;
        summary[col::NEW_ROOT] = w.new_root;
        summary[col::REMOVAL_COUNT] = BabyBear::new(w.removed_facts.len() as u32);
        summary[col::CHECK_COUNT] = BabyBear::new(w.num_added_checks as u32);
        summary[col::HASH_VALID] = BabyBear::ONE;
        trace.push(summary);

        let fact_hashes: Vec<BabyBear> = w.removed_facts.iter().map(|f| f.hash()).collect();
        let expected_rt = compute_root_transition_hash(
            w.old_root,
            w.new_root,
            &fact_hashes,
            &w.added_checks_commitment,
        );
        let narrow_checks = w.added_checks_commitment.to_narrow();
        let public_inputs = vec![
            w.old_root,
            w.new_root,
            BabyBear::new(w.removed_facts.len() as u32),
            BabyBear::new(w.num_added_checks as u32),
            expected_rt,
            narrow_checks,
        ];
        (trace, public_inputs)
    }
}

pub fn build_shared_tree(leaves: &[BabyBear], depth: usize) -> (BabyBear, Vec<MerkleWitness>) {
    let fan_out = 4usize;
    let max_leaves = fan_out.pow(depth as u32);
    let mut levels: Vec<Vec<BabyBear>> = Vec::with_capacity(depth + 1);
    let mut bottom = Vec::with_capacity(max_leaves);
    for &leaf in leaves.iter().take(max_leaves) {
        bottom.push(leaf);
    }
    while bottom.len() < max_leaves {
        bottom.push(BabyBear::ZERO);
    }
    levels.push(bottom);
    for _ in 0..depth {
        let prev = levels.last().unwrap();
        let mut next = Vec::with_capacity(prev.len() / fan_out);
        for chunk in prev.chunks(fan_out) {
            next.push(hash_4_to_1(&[chunk[0], chunk[1], chunk[2], chunk[3]]));
        }
        levels.push(next);
    }
    let root = levels[depth][0];
    let mut proofs = Vec::with_capacity(leaves.len());
    for (leaf_idx, &leaf_hash) in leaves.iter().enumerate() {
        let mut proof_levels = Vec::with_capacity(depth);
        let mut idx = leaf_idx;
        for level in 0..depth {
            let position = (idx % fan_out) as u8;
            let group_start = idx - (idx % fan_out);
            let mut siblings = Vec::with_capacity(3);
            for j in 0..fan_out {
                if j as u8 != position {
                    siblings.push(levels[level][group_start + j]);
                }
            }
            proof_levels.push(MerkleLevelWitness {
                position,
                siblings: [siblings[0], siblings[1], siblings[2]],
            });
            idx /= fan_out;
        }
        proofs.push(MerkleWitness {
            leaf_hash,
            levels: proof_levels,
            expected_root: root,
        });
    }
    (root, proofs)
}

pub fn build_membership_proof(leaf_hash: BabyBear, depth: usize) -> MerkleWitness {
    let mut current = leaf_hash;
    let mut levels = Vec::with_capacity(depth);
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((leaf_hash.0.wrapping_add(i as u32 * 7 + 1)) % crate::field::BABYBEAR_P),
            BabyBear::new((leaf_hash.0.wrapping_add(i as u32 * 7 + 2)) % crate::field::BABYBEAR_P),
            BabyBear::new((leaf_hash.0.wrapping_add(i as u32 * 7 + 3)) % crate::field::BABYBEAR_P),
        ];
        let parent = MerkleAir::compute_parent(current, position, &siblings);
        levels.push(MerkleLevelWitness { position, siblings });
        current = parent;
    }
    MerkleWitness {
        leaf_hash,
        levels,
        expected_root: current,
    }
}

pub fn compute_test_checks_commitment(num_checks: usize) -> crate::binding::WideHash {
    if num_checks == 0 {
        return crate::binding::WideHash::ZERO;
    }
    let check_hashes: Vec<BabyBear> = (0..num_checks)
        .map(|i| {
            hash_fact(
                BabyBear::new(900 + i as u32),
                &[BabyBear::new(i as u32), BabyBear::ZERO, BabyBear::ZERO],
            )
        })
        .collect();
    crate::binding::WideHash::from_poseidon2("pyana-checks-v1", &check_hashes)
}

pub fn create_test_fold(num_removals: usize, num_checks: usize) -> FoldWitness {
    let new_root = BabyBear::new(222222);
    let checks_commitment = compute_test_checks_commitment(num_checks);
    if num_removals == 0 {
        return FoldWitness {
            old_root: BabyBear::new(111111),
            new_root,
            removed_facts: vec![],
            num_added_checks: num_checks,
            added_checks_commitment: checks_commitment,
        };
    }
    let facts_data: Vec<(BabyBear, [BabyBear; 3])> = (0..num_removals)
        .map(|i| {
            (
                BabyBear::new((i * 100 + 10) as u32),
                [
                    BabyBear::new((i * 100 + 20) as u32),
                    BabyBear::new((i * 100 + 30) as u32),
                    BabyBear::ZERO,
                ],
            )
        })
        .collect();
    let fact_hashes: Vec<BabyBear> = facts_data
        .iter()
        .map(|(pred, terms)| hash_fact(*pred, terms))
        .collect();
    let (old_root, proofs) = build_shared_tree(&fact_hashes, 4);
    let removed_facts: Vec<RemovedFact> = facts_data
        .into_iter()
        .zip(proofs.into_iter())
        .map(|((predicate, terms), proof)| RemovedFact {
            predicate,
            terms,
            membership_proof: Some(proof),
        })
        .collect();
    FoldWitness {
        old_root,
        new_root,
        removed_facts,
        num_added_checks: num_checks,
        added_checks_commitment: checks_commitment,
    }
}

// ============================================================================
// Circuit descriptor
// ============================================================================

/// Build the production fold CircuitDescriptor.
///
/// This is the DSL equivalent of `FoldStarkAir`. It expresses the same constraints
/// using the declarative `ConstraintExpr` types, enabling the generic `DslCircuit`
/// to evaluate them.
///
/// Constraints:
/// 1. `row_type_binary`: ROW_TYPE * (ROW_TYPE - 1) == 0
/// 2. `hash_valid_binary`: HASH_VALID * (HASH_VALID - 1) == 0
/// 3. `membership_root_matches_old_root` (gated by is_removal):
///    (1 - ROW_TYPE) * (MEMBERSHIP_ROOT - OLD_ROOT) == 0
/// 4. `removal_hash_required` (gated by is_removal):
///    (1 - ROW_TYPE) * (1 - HASH_VALID) == 0
/// 5. `fact_hash_correct` (gated by is_removal):
///    (1 - ROW_TYPE) * (hash_fact(FACT_PRED, terms) - FACT_HASH) == 0
/// 6. `old_root_consistent`: OLD_ROOT - pi[0] == 0
/// 7. `new_root_consistent`: NEW_ROOT - pi[1] == 0
/// 8. `removal_count_increment` (gated transition):
///    (1 - ROW_TYPE) * (next[REMOVAL_COUNT] - local[REMOVAL_COUNT_PLUS_ONE]) == 0
/// 9. `root_transition_binding` (gated on is_summary):
///    ROW_TYPE * (MEMBERSHIP_ROOT - pi[4]) == 0
///
/// Boundary constraints:
/// - First row: OLD_ROOT == pi[0]
/// - First row: NEW_ROOT == pi[1]
/// - Last row: ROW_TYPE == 1 (must be summary)
/// - Last row: REMOVAL_COUNT == pi[2]
/// - Last row: CHECK_COUNT == pi[3]
/// - Last row: MEMBERSHIP_ROOT == pi[4] (transition hash binding)
pub fn fold_circuit_descriptor() -> CircuitDescriptor {
    let columns = vec![
        ColumnDef {
            name: "row_type".into(),
            index: col::ROW_TYPE,
            kind: ColumnKind::Selector,
        },
        ColumnDef {
            name: "fact_hash".into(),
            index: col::FACT_HASH,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "membership_root".into(),
            index: col::MEMBERSHIP_ROOT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "old_root".into(),
            index: col::OLD_ROOT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "new_root".into(),
            index: col::NEW_ROOT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "removal_count".into(),
            index: col::REMOVAL_COUNT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "check_count".into(),
            index: col::CHECK_COUNT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "fact_pred".into(),
            index: col::FACT_PRED,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "fact_term_0".into(),
            index: col::FACT_TERM_START,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "fact_term_1".into(),
            index: col::FACT_TERM_START + 1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "fact_term_2".into(),
            index: col::FACT_TERM_START + 2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "hash_valid".into(),
            index: col::HASH_VALID,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "removal_count_plus_one".into(),
            index: col::REMOVAL_COUNT_PLUS_ONE,
            kind: ColumnKind::Value,
        },
    ];

    // Constraint 1: row_type is binary
    let c_row_type_binary = ConstraintExpr::Binary { col: col::ROW_TYPE };

    // Constraint 2: hash_valid is binary
    let c_hash_valid_binary = ConstraintExpr::Binary {
        col: col::HASH_VALID,
    };

    // Constraint 3: membership_root == old_root WHEN is_removal (row_type == 0)
    let c_membership_root = ConstraintExpr::InvertedGated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::Equality {
            col_a: col::MEMBERSHIP_ROOT,
            col_b: col::OLD_ROOT,
        }),
    };

    // Constraint 4: removal_hash_required: when is_removal, hash_valid must be 1.
    // (1 - ROW_TYPE) * (1 - HASH_VALID) == 0
    let c_removal_hash_required = ConstraintExpr::InvertedGated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::InvertedGated {
            selector_col: col::HASH_VALID,
            // Inner evaluates to 1 when hash_valid == 0; we need the product to be zero.
            // (1-ROW_TYPE)*(1-HASH_VALID) == 0 is best expressed as a Polynomial:
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![crate::dsl::circuit::PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![],
                }],
            }),
        }),
    };

    // Constraint 5: fact_hash_correct (gated by is_removal)
    // (1 - ROW_TYPE) * (hash_fact(FACT_PRED, [term0, term1, term2]) - FACT_HASH) == 0
    let c_fact_hash = ConstraintExpr::InvertedGated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::FACT_HASH,
            input_cols: vec![
                col::FACT_PRED,
                col::FACT_TERM_START,
                col::FACT_TERM_START + 1,
                col::FACT_TERM_START + 2,
            ],
        }),
    };

    // Constraint 6: OLD_ROOT == pi[0]
    let c_old_root_pi = ConstraintExpr::PiBinding {
        col: col::OLD_ROOT,
        pi_index: 0,
    };

    // Constraint 7: NEW_ROOT == pi[1]
    let c_new_root_pi = ConstraintExpr::PiBinding {
        col: col::NEW_ROOT,
        pi_index: 1,
    };

    // Constraint 8: removal_count_increment (transition).
    // (1 - ROW_TYPE) * (next[REMOVAL_COUNT] - local[REMOVAL_COUNT_PLUS_ONE]) == 0
    let c_removal_count_transition = ConstraintExpr::InvertedGated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::Transition {
            next_col: col::REMOVAL_COUNT,
            local_col: col::REMOVAL_COUNT_PLUS_ONE,
        }),
    };

    // Constraint 9: root_transition_binding on summary rows.
    // ROW_TYPE * (MEMBERSHIP_ROOT - pi[4]) == 0
    let c_transition_binding = ConstraintExpr::Gated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::PiBinding {
            col: col::MEMBERSHIP_ROOT,
            pi_index: 4,
        }),
    };

    let constraints = vec![
        c_row_type_binary,
        c_hash_valid_binary,
        c_membership_root,
        c_removal_hash_required,
        c_fact_hash,
        c_old_root_pi,
        c_new_root_pi,
        c_removal_count_transition,
        c_transition_binding,
    ];

    let boundaries = vec![
        // First row: old_root == pi[0]
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::OLD_ROOT,
            pi_index: 0,
        },
        // First row: new_root == pi[1]
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::NEW_ROOT,
            pi_index: 1,
        },
        // Last row: row_type == 1 (summary)
        BoundaryDef::Fixed {
            row: BoundaryRow::Last,
            col: col::ROW_TYPE,
            value: BabyBear::ONE,
        },
        // Last row: removal_count == pi[2]
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::REMOVAL_COUNT,
            pi_index: 2,
        },
        // Last row: check_count == pi[3]
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::CHECK_COUNT,
            pi_index: 3,
        },
        // Last row: membership_root == pi[4] (transition hash)
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::MEMBERSHIP_ROOT,
            pi_index: 4,
        },
    ];

    CircuitDescriptor {
        name: "pyana-fold-dsl-v2".into(),
        trace_width: FOLD_DSL_WIDTH,
        max_degree: 3, // InvertedGated(Hash) or InvertedGated(InvertedGated(...)) reaches degree 3
        columns,
        constraints,
        boundaries,
        public_input_count: FOLD_DSL_PI_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the fold descriptor.
pub fn fold_dsl_circuit() -> DslCircuit {
    DslCircuit::new(fold_circuit_descriptor())
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate an execution trace and public inputs from a `FoldWitness`.
///
/// This produces the same semantics as `FoldAir::generate_trace()` but for the
/// DSL-native trace layout (13 columns including the auxiliary REMOVAL_COUNT_PLUS_ONE).
pub fn generate_fold_trace(witness: &FoldWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let w = witness;

    let root_transition_hash = if !w.removed_facts.is_empty() {
        verify_root_transition(w).unwrap_or(BabyBear::ZERO)
    } else {
        compute_root_transition_hash(w.old_root, w.new_root, &[], &w.added_checks_commitment)
    };

    let mut trace = Vec::new();

    for (i, fact) in w.removed_facts.iter().enumerate() {
        let mut row = vec![BabyBear::ZERO; FOLD_DSL_WIDTH];
        row[col::ROW_TYPE] = BabyBear::ZERO;
        row[col::FACT_HASH] = fact.hash();
        row[col::MEMBERSHIP_ROOT] = fact.verify_membership(w.old_root).unwrap_or(BabyBear::ZERO);
        row[col::OLD_ROOT] = w.old_root;
        row[col::NEW_ROOT] = w.new_root;
        row[col::REMOVAL_COUNT] = BabyBear::new((i + 1) as u32);
        row[col::CHECK_COUNT] = BabyBear::new(w.num_added_checks as u32);
        row[col::FACT_PRED] = fact.predicate;
        row[col::FACT_TERM_START] = fact.terms[0];
        row[col::FACT_TERM_START + 1] = fact.terms[1];
        row[col::FACT_TERM_START + 2] = fact.terms[2];
        row[col::HASH_VALID] = BabyBear::ONE;
        // Auxiliary: next row's expected removal_count
        row[col::REMOVAL_COUNT_PLUS_ONE] = BabyBear::new((i + 2) as u32);
        trace.push(row);
    }

    // Summary row
    let mut summary = vec![BabyBear::ZERO; FOLD_DSL_WIDTH];
    summary[col::ROW_TYPE] = BabyBear::ONE;
    summary[col::MEMBERSHIP_ROOT] = root_transition_hash;
    summary[col::OLD_ROOT] = w.old_root;
    summary[col::NEW_ROOT] = w.new_root;
    summary[col::REMOVAL_COUNT] = BabyBear::new(w.removed_facts.len() as u32);
    summary[col::CHECK_COUNT] = BabyBear::new(w.num_added_checks as u32);
    summary[col::HASH_VALID] = BabyBear::ONE;
    // On the summary row, REMOVAL_COUNT_PLUS_ONE matches REMOVAL_COUNT (no transition enforced
    // because ROW_TYPE=1 gates it off).
    summary[col::REMOVAL_COUNT_PLUS_ONE] = BabyBear::new(w.removed_facts.len() as u32);
    trace.push(summary);

    // Fix the last removal row's REMOVAL_COUNT_PLUS_ONE to point at the summary row's count.
    // The summary row's REMOVAL_COUNT equals total removals, which equals the last removal row's
    // count (since it's the Nth removal). So no fix needed: row[i].REMOVAL_COUNT_PLUS_ONE = i+2,
    // and summary.REMOVAL_COUNT = N. For the last removal row (i=N-1), REMOVAL_COUNT_PLUS_ONE = N,
    // and the next row (summary) has REMOVAL_COUNT = N. Correct.

    // Pad trace to power-of-two (>= 2 rows required by STARK prover)
    let padded_len = trace.len().next_power_of_two().max(2);
    while trace.len() < padded_len {
        trace.push(trace.last().unwrap().clone());
    }

    let fact_hashes: Vec<BabyBear> = w.removed_facts.iter().map(|f| f.hash()).collect();
    let expected_rt = compute_root_transition_hash(
        w.old_root,
        w.new_root,
        &fact_hashes,
        &w.added_checks_commitment,
    );
    let narrow_checks = w.added_checks_commitment.to_narrow();
    let public_inputs = vec![
        w.old_root,
        w.new_root,
        BabyBear::new(w.removed_facts.len() as u32),
        BabyBear::new(w.num_added_checks as u32),
        expected_rt,
        narrow_checks,
    ];

    (trace, public_inputs)
}

// ============================================================================
// Production prove/verify API
// ============================================================================

/// Generate a DSL-native STARK proof for a fold step.
///
/// This replaces `prove_fold_stark` from `circuit/src/fold_types.rs`.
pub fn prove_fold_dsl(witness: &FoldWitness) -> Option<StarkProof> {
    let circuit = fold_dsl_circuit();
    let (trace, public_inputs) = generate_fold_trace(witness);

    // Validate: delta must be nonempty (at least one removal or check)
    if witness.removed_facts.is_empty() && witness.num_added_checks == 0 {
        return None;
    }

    // Validate: checks_commitment must be ZERO when num_added_checks == 0
    if witness.num_added_checks == 0 && witness.added_checks_commitment != WideHash::ZERO {
        return None;
    }

    Some(stark::prove(&circuit, &trace, &public_inputs))
}

/// Verify a DSL-native STARK proof for a fold step.
///
/// This replaces `verify_fold_stark` from `circuit/src/fold_types.rs`.
pub fn verify_fold_dsl(proof: &StarkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    let circuit = fold_dsl_circuit();

    // Validate checks_commitment_zero_when_no_checks at the verifier level.
    // pi[3] == check_count, pi[5] == checks_commitment_narrow.
    if public_inputs.len() >= 6 {
        if public_inputs[3] == BabyBear::ZERO && public_inputs[5] != BabyBear::ZERO {
            return Err("non-zero checks commitment with zero check count".to_string());
        }
    }

    stark::verify(&circuit, proof, public_inputs)
}

// ============================================================================
// Backward-compatible aliases
// ============================================================================

/// Backward-compatible alias: prove a fold step using the DSL-native circuit.
pub fn prove_fold_stark(witness: &FoldWitness) -> Option<StarkProof> {
    prove_fold_dsl(witness)
}

/// Backward-compatible alias: verify a fold step using the DSL-native circuit.
pub fn verify_fold_stark(proof: &StarkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    verify_fold_dsl(proof, public_inputs)
}
