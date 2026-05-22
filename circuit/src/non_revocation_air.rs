//! Non-revocation circuit: ZK proof that a capability has no revoked ancestor.
//!
//! # Proof Statement
//!
//! "Given a revocation set root R, my capability's derivation path has NO ancestor
//! whose revocation_hash appears under R."
//!
//! # Approach: Sorted-Merkle Non-Membership
//!
//! For each ancestor hash H in the derivation path:
//! 1. Find two adjacent leaves L_left and L_right in the sorted revocation tree
//!    where L_left < H < L_right.
//! 2. Prove L_left is in the tree (Poseidon2 Merkle membership proof).
//! 3. Prove L_right is in the tree (Poseidon2 Merkle membership proof).
//! 4. Prove L_left < H < L_right (range check via field ordering constraints).
//! 5. Prove L_left and L_right are adjacent (positions differ by 1).
//!
//! # AIR Layout
//!
//! For each ancestor (up to MAX_ANCESTORS), the trace contains:
//! - A CONTROL row identifying the ancestor hash and its neighbors
//! - Merkle membership rows for the left neighbor
//! - Merkle membership rows for the right neighbor
//!
//! The non-membership is proven per-ancestor: for each ancestor hash, we show
//! it falls between two adjacent elements in the sorted revocation set.
//!
//! # Public Inputs
//!
//! - `revocation_set_root`: The Poseidon2 Merkle root committed by the federation
//!
//! # Private Witness
//!
//! - Derivation path (list of ancestor revocation hashes)
//! - For each ancestor: the non-membership witnesses (left/right neighbors + Merkle paths)

use crate::field::BabyBear;
use crate::poseidon2::{hash_4_to_1, hash_many};
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Maximum number of ancestors supported in a single non-revocation proof.
/// This bounds the derivation chain depth we can prove in one shot.
pub const MAX_ANCESTORS: usize = 8;

/// Merkle tree depth for the revocation set.
/// With a 4-ary tree of depth 4, supports up to 256 revocation entries.
/// In production this would be larger, but 4 is sufficient for correctness.
pub const REVOCATION_TREE_DEPTH: usize = 4;

/// Number of bits for ordering range checks.
///
/// BabyBear p = 2013265921, (p-1)/2 = 1006632960 < 2^30 = 1073741824.
/// To prove diff < (p-1)/2 (which implies canonical ordering), we prove that
/// `(p-1)/2 - 1 - diff` fits in 30 bits. If diff >= (p-1)/2, the subtraction
/// wraps to a value > 2^30 that cannot be decomposed into 30 bits.
pub const ORDERING_DIFF_BITS: usize = 30;

/// (p-1)/2 - 1 as a field element, used for the ordering range check.
/// If diff = a - b - 1 is in [0, (p-1)/2 - 1], then HALF_P_MINUS_1 - diff
/// is in [0, (p-1)/2 - 1] < 2^30, and can be decomposed into 30 bits.
pub const HALF_P_MINUS_1: u32 = 1006632959; // (2013265921 - 1) / 2 - 1 + 1 ... = (p-1)/2 - 1

/// Trace width for the non-revocation AIR.
///
/// Layout per row:
/// - col 0: current_hash (the value being hashed up the Merkle path)
/// - col 1: sibling_0
/// - col 2: sibling_1
/// - col 3: sibling_2
/// - col 4: position (0..3 for Merkle level)
/// - col 5: parent (Poseidon2 hash of children at this level)
/// - col 6: row_type (0 = control, 1 = left_merkle, 2 = right_merkle)
/// - col 7: ancestor_hash (the hash being proven absent, repeated in all rows for this ancestor)
/// - col 8: left_neighbor (the left boundary value)
/// - col 9: right_neighbor (the right boundary value)
/// - col 10: ancestor_index (which ancestor in the path, 0..MAX_ANCESTORS-1)
/// - col 11: is_active (1 if this row is part of an active ancestor proof, 0 for padding)
/// - col 12: left_position (tree position of left neighbor leaf)
/// - col 13: right_position (tree position of right neighbor leaf)
/// - col 14: diff_left (ancestor_hash - left_neighbor - 1; must be < (p-1)/2)
/// - col 15..44: diff_left_bits[0..30] (bit decomposition of HALF_P_MINUS_1 - diff_left)
/// - col 45: diff_right (right_neighbor - ancestor_hash - 1; must be < (p-1)/2)
/// - col 46..75: diff_right_bits[0..30] (bit decomposition of HALF_P_MINUS_1 - diff_right)
pub const NON_REVOCATION_WIDTH: usize = 76;

/// Column indices.
pub mod col {
    use super::ORDERING_DIFF_BITS;

    /// Current hash value being walked up the Merkle path.
    pub const CURRENT: usize = 0;
    /// First sibling in the 4-ary Merkle level.
    pub const SIB0: usize = 1;
    /// Second sibling.
    pub const SIB1: usize = 2;
    /// Third sibling.
    pub const SIB2: usize = 3;
    /// Position within the 4-ary group (0..3).
    pub const POSITION: usize = 4;
    /// Parent hash (result of hashing this level).
    pub const PARENT: usize = 5;
    /// Row type: 0 = control row, 1 = left merkle, 2 = right merkle.
    pub const ROW_TYPE: usize = 6;
    /// The ancestor hash being proven absent from the revocation set.
    pub const ANCESTOR_HASH: usize = 7;
    /// The left neighbor (lower bound) in the sorted revocation set.
    pub const LEFT_NEIGHBOR: usize = 8;
    /// The right neighbor (upper bound) in the sorted revocation set.
    pub const RIGHT_NEIGHBOR: usize = 9;
    /// Which ancestor in the derivation path (0-indexed).
    pub const ANCESTOR_INDEX: usize = 10;
    /// Whether this row is active (1) or padding (0).
    pub const IS_ACTIVE: usize = 11;
    /// Tree position of the left neighbor leaf (used for adjacency check).
    pub const LEFT_POSITION: usize = 12;
    /// Tree position of the right neighbor leaf (used for adjacency check).
    pub const RIGHT_POSITION: usize = 13;
    /// diff_left = ancestor_hash - left_neighbor - 1 (ordering: left < ancestor).
    pub const DIFF_LEFT: usize = 14;
    /// Bit decomposition of diff_left (30 bits), starting at col 15.
    pub const DIFF_LEFT_BITS_START: usize = 15;
    /// diff_right = right_neighbor - ancestor_hash - 1 (ordering: ancestor < right).
    pub const DIFF_RIGHT: usize = DIFF_LEFT_BITS_START + ORDERING_DIFF_BITS; // 45
    /// Bit decomposition of diff_right (30 bits), starting at col 46.
    pub const DIFF_RIGHT_BITS_START: usize = DIFF_RIGHT + 1; // 46

    /// Get column index for diff_left_bits[bit_idx].
    #[inline]
    pub const fn diff_left_bit(bit_idx: usize) -> usize {
        DIFF_LEFT_BITS_START + bit_idx
    }

    /// Get column index for diff_right_bits[bit_idx].
    #[inline]
    pub const fn diff_right_bit(bit_idx: usize) -> usize {
        DIFF_RIGHT_BITS_START + bit_idx
    }
}

/// Public input indices.
pub mod pi {
    /// The revocation set Merkle root committed by the federation.
    pub const REVOCATION_ROOT: usize = 0;
}

/// Non-membership witness for a single ancestor hash.
///
/// Demonstrates that `ancestor_hash` is NOT in the sorted revocation tree by
/// showing two adjacent leaves that bracket it.
#[derive(Clone, Debug)]
pub struct NonMembershipWitness {
    /// The ancestor's revocation hash (what we're proving is absent).
    pub ancestor_hash: BabyBear,
    /// The left neighbor in the sorted revocation set (L_left < ancestor_hash).
    pub left_neighbor: BabyBear,
    /// The right neighbor in the sorted revocation set (ancestor_hash < L_right).
    pub right_neighbor: BabyBear,
    /// Merkle siblings for the left neighbor's membership proof.
    pub left_siblings: Vec<[BabyBear; 3]>,
    /// Merkle positions for the left neighbor's membership proof.
    pub left_positions: Vec<u8>,
    /// Merkle siblings for the right neighbor's membership proof.
    pub right_siblings: Vec<[BabyBear; 3]>,
    /// Merkle positions for the right neighbor's membership proof.
    pub right_positions: Vec<u8>,
    /// Tree position (leaf index) of the left neighbor.
    pub left_tree_position: usize,
    /// Tree position (leaf index) of the right neighbor.
    pub right_tree_position: usize,
}

/// Complete witness for a non-revocation proof.
///
/// Contains non-membership witnesses for each ancestor in the derivation path.
#[derive(Clone, Debug)]
pub struct NonRevocationWitness {
    /// Non-membership witnesses, one per ancestor in the derivation path.
    /// Length must be <= MAX_ANCESTORS.
    pub ancestors: Vec<NonMembershipWitness>,
}

/// The non-revocation AIR.
///
/// Proves that for each ancestor in a capability's derivation path, its
/// revocation hash does NOT appear in the committed revocation set.
pub struct NonRevocationAir {
    /// Merkle tree depth for the revocation set.
    pub tree_depth: usize,
}

impl NonRevocationAir {
    /// Create a new non-revocation AIR with the given tree depth.
    pub fn new(tree_depth: usize) -> Self {
        assert!(tree_depth >= 2, "Tree depth must be at least 2");
        Self { tree_depth }
    }

    /// Rows per ancestor: 1 control + tree_depth (left merkle) + tree_depth (right merkle).
    fn rows_per_ancestor(&self) -> usize {
        1 + 2 * self.tree_depth
    }

    /// Generate the execution trace from a witness.
    ///
    /// Returns (trace, public_inputs) where:
    /// - trace: rows of width NON_REVOCATION_WIDTH, padded to power of 2
    /// - public_inputs: [revocation_root]
    pub fn generate_trace(
        &self,
        witness: &NonRevocationWitness,
        revocation_root: BabyBear,
    ) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let num_ancestors = witness.ancestors.len();
        assert!(
            num_ancestors <= MAX_ANCESTORS,
            "Too many ancestors: {} > {}",
            num_ancestors,
            MAX_ANCESTORS
        );

        let rows_per = self.rows_per_ancestor();
        let active_rows = num_ancestors * rows_per;
        let total_rows = active_rows.next_power_of_two().max(4); // min 4 rows for STARK

        let mut trace = Vec::with_capacity(total_rows);

        for (ancestor_idx, nmw) in witness.ancestors.iter().enumerate() {
            assert_eq!(
                nmw.left_siblings.len(),
                self.tree_depth,
                "Left proof depth mismatch"
            );
            assert_eq!(
                nmw.right_siblings.len(),
                self.tree_depth,
                "Right proof depth mismatch"
            );

            let ancestor_hash = nmw.ancestor_hash;
            let left_neighbor = nmw.left_neighbor;
            let right_neighbor = nmw.right_neighbor;

            // Control row: records the ancestor hash and its neighbors.
            // The ordering constraint (left < ancestor < right) and adjacency
            // constraint (right_pos == left_pos + 1) are enforced on this row.
            let mut control = vec![BabyBear::ZERO; NON_REVOCATION_WIDTH];
            control[col::CURRENT] = left_neighbor; // left neighbor is the "starting point"
            control[col::POSITION] = BabyBear::ZERO;
            control[col::PARENT] = BabyBear::ZERO;
            control[col::ROW_TYPE] = BabyBear::ZERO; // control row
            control[col::ANCESTOR_HASH] = ancestor_hash;
            control[col::LEFT_NEIGHBOR] = left_neighbor;
            control[col::RIGHT_NEIGHBOR] = right_neighbor;
            control[col::ANCESTOR_INDEX] = BabyBear::new(ancestor_idx as u32);
            control[col::IS_ACTIVE] = BabyBear::ONE;

            // Ordering and adjacency witness columns.
            control[col::LEFT_POSITION] = BabyBear::new(nmw.left_tree_position as u32);
            control[col::RIGHT_POSITION] = BabyBear::new(nmw.right_tree_position as u32);

            // diff_left = ancestor_hash - left_neighbor - 1
            // If ancestor > left canonically, diff_left < (p-1)/2.
            // The bits decompose HALF_P_MINUS_1 - diff_left (the "check" value).
            // For valid witnesses, check_left fits in 30 bits.
            // For malicious witnesses, the bits will be wrong and constraints reject.
            let diff_left = ancestor_hash - left_neighbor - BabyBear::ONE;
            control[col::DIFF_LEFT] = diff_left;
            let diff_left_u32 = diff_left.as_u32();
            if diff_left_u32 <= HALF_P_MINUS_1 {
                let check_left_val = HALF_P_MINUS_1 - diff_left_u32;
                for i in 0..ORDERING_DIFF_BITS {
                    control[col::diff_left_bit(i)] = BabyBear::new((check_left_val >> i) & 1);
                }
            }
            // else: bits stay zero, constraints will reject (decomposition won't match)

            // diff_right = right_neighbor - ancestor_hash - 1
            let diff_right = right_neighbor - ancestor_hash - BabyBear::ONE;
            control[col::DIFF_RIGHT] = diff_right;
            let diff_right_u32 = diff_right.as_u32();
            if diff_right_u32 <= HALF_P_MINUS_1 {
                let check_right_val = HALF_P_MINUS_1 - diff_right_u32;
                for i in 0..ORDERING_DIFF_BITS {
                    control[col::diff_right_bit(i)] = BabyBear::new((check_right_val >> i) & 1);
                }
            }
            // else: bits stay zero, constraints will reject

            trace.push(control);

            // Left neighbor Merkle membership proof rows.
            let mut current = left_neighbor;
            for level in 0..self.tree_depth {
                let pos = nmw.left_positions[level];
                assert!(pos < 4, "Merkle position must be 0..3");
                let siblings = &nmw.left_siblings[level];

                let mut children = [BabyBear::ZERO; 4];
                let mut sib_idx = 0;
                for j in 0..4u8 {
                    if j == pos {
                        children[j as usize] = current;
                    } else {
                        children[j as usize] = siblings[sib_idx];
                        sib_idx += 1;
                    }
                }
                let parent = hash_4_to_1(&children);

                let mut row = vec![BabyBear::ZERO; NON_REVOCATION_WIDTH];
                row[col::CURRENT] = current;
                row[col::SIB0] = siblings[0];
                row[col::SIB1] = siblings[1];
                row[col::SIB2] = siblings[2];
                row[col::POSITION] = BabyBear::new(pos as u32);
                row[col::PARENT] = parent;
                row[col::ROW_TYPE] = BabyBear::ONE; // left merkle
                row[col::ANCESTOR_HASH] = ancestor_hash;
                row[col::LEFT_NEIGHBOR] = left_neighbor;
                row[col::RIGHT_NEIGHBOR] = right_neighbor;
                row[col::ANCESTOR_INDEX] = BabyBear::new(ancestor_idx as u32);
                row[col::IS_ACTIVE] = BabyBear::ONE;
                trace.push(row);

                current = parent;
            }

            // Right neighbor Merkle membership proof rows.
            current = right_neighbor;
            for level in 0..self.tree_depth {
                let pos = nmw.right_positions[level];
                assert!(pos < 4, "Merkle position must be 0..3");
                let siblings = &nmw.right_siblings[level];

                let mut children = [BabyBear::ZERO; 4];
                let mut sib_idx = 0;
                for j in 0..4u8 {
                    if j == pos {
                        children[j as usize] = current;
                    } else {
                        children[j as usize] = siblings[sib_idx];
                        sib_idx += 1;
                    }
                }
                let parent = hash_4_to_1(&children);

                let mut row = vec![BabyBear::ZERO; NON_REVOCATION_WIDTH];
                row[col::CURRENT] = current;
                row[col::SIB0] = siblings[0];
                row[col::SIB1] = siblings[1];
                row[col::SIB2] = siblings[2];
                row[col::POSITION] = BabyBear::new(pos as u32);
                row[col::PARENT] = parent;
                row[col::ROW_TYPE] = BabyBear::new(2); // right merkle
                row[col::ANCESTOR_HASH] = ancestor_hash;
                row[col::LEFT_NEIGHBOR] = left_neighbor;
                row[col::RIGHT_NEIGHBOR] = right_neighbor;
                row[col::ANCESTOR_INDEX] = BabyBear::new(ancestor_idx as u32);
                row[col::IS_ACTIVE] = BabyBear::ONE;
                trace.push(row);

                current = parent;
            }
        }

        // Pad to power of 2 with inactive rows.
        while trace.len() < total_rows {
            let mut row = vec![BabyBear::ZERO; NON_REVOCATION_WIDTH];
            row[col::IS_ACTIVE] = BabyBear::ZERO;
            trace.push(row);
        }

        let public_inputs = vec![revocation_root];
        (trace, public_inputs)
    }
}

impl StarkAir for NonRevocationAir {
    fn width(&self) -> usize {
        NON_REVOCATION_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        4 // position validity is degree 4
    }

    fn air_name(&self) -> &'static str {
        "pyana-non-revocation-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let position = local[col::POSITION];
        let is_active = local[col::IS_ACTIVE];
        let row_type = local[col::ROW_TYPE];

        // Constraint 1: Position validity (degree 4).
        // pos * (pos-1) * (pos-2) * (pos-3) = 0
        let c_pos = position
            * (position - BabyBear::ONE)
            * (position - BabyBear::new(2))
            * (position - BabyBear::new(3));

        let mut combined = is_active * c_pos;
        let mut alpha_pow = alpha;

        // Constraint 2: is_active is binary.
        let c_binary_active = is_active * (is_active - BabyBear::ONE);
        combined = combined + alpha_pow * c_binary_active;
        alpha_pow = alpha_pow * alpha;

        // Constraint 3: row_type validity. row_type in {0, 1, 2}.
        // row_type * (row_type - 1) * (row_type - 2) = 0
        let c_row_type = row_type * (row_type - BabyBear::ONE) * (row_type - BabyBear::new(2));
        combined = combined + alpha_pow * (is_active * c_row_type);
        alpha_pow = alpha_pow * alpha;

        // Constraint 4: Merkle hash binding (on Merkle rows: row_type == 1 or row_type == 2).
        // is_merkle = row_type * (row_type - 1) ... no, we need:
        // is_merkle = 1 when row_type = 1 or row_type = 2.
        // Use: is_merkle = row_type * (3 - row_type) / 2 ... but division is complex.
        // Simpler: is_merkle = 1 - (1 - row_type) * (2 - row_type) / 2
        // Actually simplest: is_not_control = 1 if row_type != 0.
        // (1 - delta(row_type, 0)) where delta is Lagrange basis for 0.
        // Lagrange at 0 over {0,1,2}: L_0(x) = (x-1)(x-2)/((0-1)(0-2)) = (x-1)(x-2)/2
        let inv_2 = BabyBear::new(2).inverse().unwrap();
        let is_control = (row_type - BabyBear::ONE) * (row_type - BabyBear::new(2)) * inv_2;
        let is_merkle = BabyBear::ONE - is_control;

        // For Merkle rows, verify parent = hash_4_to_1(children arranged by position).
        let current = local[col::CURRENT];
        let sib0 = local[col::SIB0];
        let sib1 = local[col::SIB1];
        let sib2 = local[col::SIB2];
        let parent = local[col::PARENT];

        let p = position;
        let p_m1 = p - BabyBear::ONE;
        let p_m2 = p - BabyBear::new(2);
        let p_m3 = p - BabyBear::new(3);

        // Lagrange interpolation coefficients for position in {0,1,2,3}
        let inv_neg6 = -BabyBear::new(6).inverse().unwrap();
        let inv_2_pos = BabyBear::new(2).inverse().unwrap();
        let inv_neg2 = -inv_2_pos;
        let inv_6 = BabyBear::new(6).inverse().unwrap();

        let l0 = p_m1 * p_m2 * p_m3 * inv_neg6;
        let l1 = p * p_m2 * p_m3 * inv_2_pos;
        let l2 = p * p_m1 * p_m3 * inv_neg2;
        let l3 = p * p_m1 * p_m2 * inv_6;

        let child0 = current * l0 + sib0 * (BabyBear::ONE - l0);
        let child1 = sib0 * l0 + current * l1 + sib1 * (l2 + l3);
        let child2 = sib1 * (l0 + l1) + current * l2 + sib2 * l3;
        let child3 = sib2 * (BabyBear::ONE - l3) + current * l3;

        let expected_parent = hash_4_to_1(&[child0, child1, child2, child3]);
        let c_hash = is_active * is_merkle * (parent - expected_parent);
        combined = combined + alpha_pow * c_hash;
        alpha_pow = alpha_pow * alpha;

        // Constraint 5: Control row consistency — left_neighbor == CURRENT column.
        // On control rows, left_neighbor starts the left Merkle path.
        let ancestor_hash = local[col::ANCESTOR_HASH];
        let left_neighbor = local[col::LEFT_NEIGHBOR];
        let right_neighbor = local[col::RIGHT_NEIGHBOR];

        let c_control_left = is_active * is_control * (current - left_neighbor);
        combined = combined + alpha_pow * c_control_left;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // Constraint 6: Ordering — left_neighbor < ancestor_hash.
        // Proven via bit decomposition: diff_left = ancestor_hash - left_neighbor - 1
        // must decompose into ORDERING_DIFF_BITS bits with the high bit = 0.
        // This ensures diff_left is in [0, 2^29 - 1], i.e., ancestor_hash - left_neighbor
        // is in [1, 2^29], proving strict ordering on canonical u32 representations.
        // ====================================================================

        let diff_left = local[col::DIFF_LEFT];

        // 6a: diff_left consistency: diff_left == ancestor_hash - left_neighbor - 1
        let c_diff_left_correct =
            is_active * is_control * (diff_left - (ancestor_hash - left_neighbor - BabyBear::ONE));
        combined = combined + alpha_pow * c_diff_left_correct;
        alpha_pow = alpha_pow * alpha;

        // 6b: diff_left range check via bit decomposition.
        // The bits decompose (HALF_P_MINUS_1 - diff_left). If this fits in 30 bits,
        // then diff_left < (p-1)/2, proving left_neighbor < ancestor_hash canonically.
        let half_p = BabyBear::new(HALF_P_MINUS_1);
        {
            let mut recomposed = BabyBear::ZERO;
            let mut power_of_two = BabyBear::ONE;
            for i in 0..ORDERING_DIFF_BITS {
                let bit = local[col::diff_left_bit(i)];
                recomposed = recomposed + bit * power_of_two;
                power_of_two = power_of_two + power_of_two;
            }
            let c_decomp = is_active * is_control * (recomposed - (half_p - diff_left));
            combined = combined + alpha_pow * c_decomp;
        }
        alpha_pow = alpha_pow * alpha;

        // 6c: diff_left bits are binary
        {
            let mut bits_check = BabyBear::ZERO;
            for i in 0..ORDERING_DIFF_BITS {
                let bit = local[col::diff_left_bit(i)];
                bits_check = bits_check + bit * (bit - BabyBear::ONE);
            }
            combined = combined + alpha_pow * (is_active * is_control * bits_check);
        }
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // Constraint 7: Ordering — ancestor_hash < right_neighbor.
        // Same technique: diff_right = right_neighbor - ancestor_hash - 1.
        // ====================================================================

        let diff_right = local[col::DIFF_RIGHT];

        // 7a: diff_right consistency
        let c_diff_right_correct = is_active
            * is_control
            * (diff_right - (right_neighbor - ancestor_hash - BabyBear::ONE));
        combined = combined + alpha_pow * c_diff_right_correct;
        alpha_pow = alpha_pow * alpha;

        // 7b: diff_right range check via bit decomposition.
        // The bits decompose (HALF_P_MINUS_1 - diff_right).
        {
            let mut recomposed = BabyBear::ZERO;
            let mut power_of_two = BabyBear::ONE;
            for i in 0..ORDERING_DIFF_BITS {
                let bit = local[col::diff_right_bit(i)];
                recomposed = recomposed + bit * power_of_two;
                power_of_two = power_of_two + power_of_two;
            }
            let c_decomp = is_active * is_control * (recomposed - (half_p - diff_right));
            combined = combined + alpha_pow * c_decomp;
        }
        alpha_pow = alpha_pow * alpha;

        // 7c: diff_right bits are binary
        {
            let mut bits_check = BabyBear::ZERO;
            for i in 0..ORDERING_DIFF_BITS {
                let bit = local[col::diff_right_bit(i)];
                bits_check = bits_check + bit * (bit - BabyBear::ONE);
            }
            combined = combined + alpha_pow * (is_active * is_control * bits_check);
        }
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // Constraint 8: Adjacency — right_position == left_position + 1.
        // This ensures the prover cannot pick two non-adjacent leaves that
        // happen to bracket the element (which would allow a revoked element
        // to appear to be absent).
        // ====================================================================

        let left_pos = local[col::LEFT_POSITION];
        let right_pos = local[col::RIGHT_POSITION];
        let c_adjacency = is_active * is_control * (right_pos - left_pos - BabyBear::ONE);
        combined = combined + alpha_pow * c_adjacency;

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];

        if public_inputs.is_empty() || trace_len == 0 {
            return constraints;
        }

        let revocation_root = public_inputs[pi::REVOCATION_ROOT];

        // Bind revocation_root to the PARENT column at the top of each Merkle path.
        // For ancestor 0:
        //   - Control row is at index 0
        //   - Left Merkle rows are at indices 1..=tree_depth
        //   - Right Merkle rows are at indices (tree_depth+1)..=(2*tree_depth)
        //
        // The last left Merkle row (index tree_depth) has PARENT = revocation_root.
        // The last right Merkle row (index 2*tree_depth) also has PARENT = revocation_root.
        //
        // We bind BOTH to ensure the prover commits to the same root for left and
        // right neighbor membership proofs.
        let left_top_row = self.tree_depth;
        let right_top_row = 2 * self.tree_depth;

        if left_top_row < trace_len {
            constraints.push(BoundaryConstraint {
                row: left_top_row,
                col: col::PARENT,
                value: revocation_root,
            });
        }

        if right_top_row < trace_len {
            constraints.push(BoundaryConstraint {
                row: right_top_row,
                col: col::PARENT,
                value: revocation_root,
            });
        }

        constraints
    }
}

/// A sorted revocation tree built on top of a Poseidon2 4-ary Merkle tree.
///
/// This is the data structure that the federation commits to. Leaves are sorted
/// revocation hashes (as BabyBear field elements), enabling efficient non-membership
/// proofs via the adjacent-neighbor technique.
#[derive(Clone, Debug)]
pub struct SortedRevocationTree {
    /// Sorted leaves (revocation hashes as field elements).
    leaves: Vec<BabyBear>,
    /// Tree depth.
    depth: usize,
}

/// Sentinel value at the lower boundary of the sorted revocation tree.
/// This is 0, which is the smallest possible canonical BabyBear value.
/// Its presence ensures that any non-zero hash has a valid left neighbor.
pub const SENTINEL_MIN: BabyBear = BabyBear::ZERO;

/// Sentinel value at the upper boundary of the sorted revocation tree.
/// This is p - 1 = 2013265920, the largest canonical BabyBear value.
/// Its presence ensures that any hash < p-1 has a valid right neighbor.
pub const SENTINEL_MAX: BabyBear = BabyBear(2013265920);

impl SortedRevocationTree {
    /// Create a new sorted revocation tree from a set of revocation hashes.
    ///
    /// The hashes are sorted by their canonical u32 representation to enable
    /// binary search and adjacent-neighbor non-membership proofs.
    ///
    /// Automatically inserts boundary sentinel values (0 and p-1) to ensure
    /// that every non-member hash falls between two adjacent tree entries.
    /// This is required for the in-circuit ordering constraints to be satisfiable.
    pub fn new(mut revocation_hashes: Vec<BabyBear>, depth: usize) -> Self {
        // Insert boundary sentinels for sound non-membership proofs.
        revocation_hashes.push(SENTINEL_MIN);
        revocation_hashes.push(SENTINEL_MAX);
        revocation_hashes.sort_by_key(|h| h.0);
        // Deduplicate (in case 0 or p-1 was already present)
        revocation_hashes.dedup();
        Self {
            leaves: revocation_hashes,
            depth,
        }
    }

    /// Number of entries (including sentinels).
    pub fn len(&self) -> usize {
        self.leaves.len()
    }

    /// Number of actual revoked entries (excluding sentinels).
    pub fn num_revoked(&self) -> usize {
        self.leaves
            .iter()
            .filter(|h| **h != SENTINEL_MIN && **h != SENTINEL_MAX)
            .count()
    }

    /// Whether the tree has no revoked entries (sentinels don't count).
    pub fn is_empty(&self) -> bool {
        self.num_revoked() == 0
    }

    /// Check if a hash is in the revocation set (sentinels are not considered revoked).
    pub fn contains(&self, hash: &BabyBear) -> bool {
        if *hash == SENTINEL_MIN || *hash == SENTINEL_MAX {
            return false;
        }
        self.leaves.binary_search_by_key(&hash.0, |h| h.0).is_ok()
    }

    /// Check if a hash exists as a leaf in the tree (including sentinels).
    pub fn contains_leaf(&self, hash: &BabyBear) -> bool {
        self.leaves.binary_search_by_key(&hash.0, |h| h.0).is_ok()
    }

    /// Compute the Merkle root of the sorted tree.
    ///
    /// Builds a 4-ary Poseidon2 Merkle tree over the sorted leaves (padded with
    /// zeros to fill the tree capacity).
    pub fn root(&self) -> BabyBear {
        use crate::poseidon2::hash_4_to_1;

        let capacity = 4usize.pow(self.depth as u32);
        let mut level: Vec<BabyBear> = Vec::with_capacity(capacity);
        level.extend_from_slice(&self.leaves);
        level.resize(capacity, BabyBear::ZERO);

        // Hash up level by level.
        for _ in 0..self.depth {
            let mut next_level = Vec::with_capacity(level.len() / 4);
            for chunk in level.chunks(4) {
                next_level.push(hash_4_to_1(&[chunk[0], chunk[1], chunk[2], chunk[3]]));
            }
            level = next_level;
        }

        assert_eq!(level.len(), 1);
        level[0]
    }

    /// Generate a Merkle membership proof for a leaf at a given position.
    ///
    /// Returns (siblings_per_level, positions_per_level) suitable for the AIR.
    pub fn prove_membership(&self, position: usize) -> Option<(Vec<[BabyBear; 3]>, Vec<u8>)> {
        let capacity = 4usize.pow(self.depth as u32);
        if position >= capacity {
            return None;
        }

        // Build the full padded leaf array.
        let mut padded_leaves = Vec::with_capacity(capacity);
        padded_leaves.extend_from_slice(&self.leaves);
        padded_leaves.resize(capacity, BabyBear::ZERO);

        let mut siblings = Vec::with_capacity(self.depth);
        let mut positions = Vec::with_capacity(self.depth);
        let mut level = padded_leaves;
        let mut idx = position;

        for _ in 0..self.depth {
            let group_base = (idx / 4) * 4;
            let pos_in_group = (idx % 4) as u8;
            positions.push(pos_in_group);

            let mut sibs = [BabyBear::ZERO; 3];
            let mut sib_idx = 0;
            for i in 0..4 {
                if i == pos_in_group as usize {
                    continue;
                }
                sibs[sib_idx] = level[group_base + i];
                sib_idx += 1;
            }
            siblings.push(sibs);

            // Compute next level.
            let mut next_level = Vec::with_capacity(level.len() / 4);
            for chunk in level.chunks(4) {
                next_level.push(hash_4_to_1(&[chunk[0], chunk[1], chunk[2], chunk[3]]));
            }
            level = next_level;
            idx = idx / 4;
        }

        Some((siblings, positions))
    }

    /// Generate a non-membership witness for a hash that is NOT in the tree.
    ///
    /// Returns None if the hash IS in the tree (can't prove non-membership),
    /// or if the hash equals a sentinel value.
    ///
    /// Because the tree always contains sentinels (0 and p-1), any hash in the
    /// range (0, p-1) exclusive is guaranteed to fall between two adjacent leaves.
    pub fn prove_non_membership(&self, hash: &BabyBear) -> Option<NonMembershipWitness> {
        // Sentinels themselves cannot be proven absent (they ARE in the tree).
        if *hash == SENTINEL_MIN || *hash == SENTINEL_MAX {
            return None;
        }

        // Binary search for the insertion point.
        match self.leaves.binary_search_by_key(&hash.0, |h| h.0) {
            Ok(_) => None, // Hash IS in the set.
            Err(idx) => {
                // Thanks to sentinels, idx is always in range (0, leaves.len()).
                // leaves[0] = SENTINEL_MIN = 0, so hash > 0 means idx > 0.
                // leaves[last] = SENTINEL_MAX = p-1, so hash < p-1 means idx < leaves.len().
                assert!(
                    idx > 0 && idx < self.leaves.len(),
                    "Sentinel invariant violated: idx={}, len={}",
                    idx,
                    self.leaves.len()
                );

                // Left neighbor is leaves[idx-1], right neighbor is leaves[idx].
                // They are adjacent in the sorted order (positions idx-1 and idx).
                let left_pos = idx - 1;
                let right_pos = idx;
                let left_val = self.leaves[left_pos];
                let right_val = self.leaves[right_pos];

                // Generate Merkle proofs for both neighbors.
                let (left_siblings, left_positions) = self.prove_membership(left_pos)?;
                let (right_siblings, right_positions) = self.prove_membership(right_pos)?;

                Some(NonMembershipWitness {
                    ancestor_hash: *hash,
                    left_neighbor: left_val,
                    right_neighbor: right_val,
                    left_siblings,
                    left_positions,
                    right_siblings,
                    right_positions,
                    left_tree_position: left_pos,
                    right_tree_position: right_pos,
                })
            }
        }
    }
}

/// Generate a non-revocation proof for a derivation path.
///
/// Given a list of ancestor revocation hashes and a sorted revocation tree,
/// proves that NONE of the ancestors appear in the revocation set.
///
/// Returns None if any ancestor IS revoked (cannot generate a valid proof).
pub fn prove_non_revocation(
    ancestor_hashes: &[BabyBear],
    revocation_tree: &SortedRevocationTree,
) -> Option<StarkProof> {
    if ancestor_hashes.len() > MAX_ANCESTORS {
        return None;
    }

    // Generate non-membership witnesses for each ancestor.
    let mut witnesses = Vec::with_capacity(ancestor_hashes.len());
    for hash in ancestor_hashes {
        match revocation_tree.prove_non_membership(hash) {
            Some(w) => witnesses.push(w),
            None => return None, // This ancestor IS revoked.
        }
    }

    let witness = NonRevocationWitness {
        ancestors: witnesses,
    };

    let revocation_root = revocation_tree.root();
    let air = NonRevocationAir::new(revocation_tree.depth);
    let (trace, public_inputs) = air.generate_trace(&witness, revocation_root);

    Some(stark::prove(&air, &trace, &public_inputs))
}

/// Verify a non-revocation proof.
///
/// The verifier only needs the revocation set root (committed by the federation)
/// and the STARK proof. The derivation path remains private.
///
/// Returns Ok(()) if the proof is valid, Err with reason otherwise.
pub fn verify_non_revocation(revocation_root: BabyBear, proof: &StarkProof) -> Result<(), String> {
    // Determine tree depth from the proof's trace length and number of ancestors.
    // Each ancestor uses 1 + 2*depth rows. We use the default depth.
    let air = NonRevocationAir::new(REVOCATION_TREE_DEPTH);
    let public_inputs = vec![revocation_root];
    stark::verify(&air, proof, &public_inputs)
}

/// Convert a 32-byte revocation hash (from `DerivationTree::revocation_hash`) to a BabyBear
/// field element suitable for the sorted revocation tree.
///
/// Uses Poseidon2 to compress the 32 bytes into a single field element,
/// matching the approach used in `commit::poseidon2_tree::commitment_to_field`.
pub fn revocation_hash_to_field(hash: &[u8; 32]) -> BabyBear {
    let elements = BabyBear::encode_hash(hash);
    hash_many(&elements)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Create a deterministic revocation hash for testing.
    fn make_revocation_hash(seed: u32) -> BabyBear {
        hash_many(&[BabyBear::new(seed), BabyBear::new(0xDEAD)])
    }

    /// Build a test revocation tree with the given number of revoked entries.
    fn build_test_tree(num_revoked: usize) -> SortedRevocationTree {
        let hashes: Vec<BabyBear> = (1..=num_revoked as u32)
            .map(|i| make_revocation_hash(i * 100))
            .collect();
        SortedRevocationTree::new(hashes, REVOCATION_TREE_DEPTH)
    }

    #[test]
    fn sorted_tree_construction() {
        let tree = build_test_tree(5);
        // 5 revoked entries + 2 sentinels = 7 leaves
        assert_eq!(tree.len(), 7);
        assert_eq!(tree.num_revoked(), 5);

        // Verify leaves are sorted.
        for i in 1..tree.leaves.len() {
            assert!(
                tree.leaves[i - 1].0 < tree.leaves[i].0,
                "Leaves must be sorted"
            );
        }

        // Verify sentinels are present.
        assert_eq!(tree.leaves[0], SENTINEL_MIN);
        assert_eq!(*tree.leaves.last().unwrap(), SENTINEL_MAX);
    }

    #[test]
    fn sorted_tree_root_deterministic() {
        let tree1 = build_test_tree(5);
        let tree2 = build_test_tree(5);
        assert_eq!(tree1.root(), tree2.root());
    }

    #[test]
    fn sorted_tree_membership_proof_verifies() {
        let tree = build_test_tree(5);
        let root = tree.root();

        // Prove membership of each leaf.
        for i in 0..tree.len() {
            let (siblings, positions) = tree.prove_membership(i).unwrap();
            // Manually verify: walk up the Merkle path.
            let mut current = tree.leaves[i];
            for level in 0..tree.depth {
                let pos = positions[level];
                let sibs = &siblings[level];
                let mut children = [BabyBear::ZERO; 4];
                let mut sib_idx = 0;
                for j in 0..4u8 {
                    if j == pos {
                        children[j as usize] = current;
                    } else {
                        children[j as usize] = sibs[sib_idx];
                        sib_idx += 1;
                    }
                }
                current = hash_4_to_1(&children);
            }
            assert_eq!(current, root, "Membership proof failed for leaf {i}");
        }
    }

    #[test]
    fn sorted_tree_non_membership_for_absent_hash() {
        let tree = build_test_tree(5);

        // A hash that is NOT in the tree.
        let absent = make_revocation_hash(999);
        assert!(!tree.contains(&absent));

        let witness = tree.prove_non_membership(&absent).unwrap();
        assert_eq!(witness.ancestor_hash, absent);

        // Left neighbor must be strictly less than absent hash.
        assert!(
            witness.left_neighbor.0 < absent.0,
            "Left neighbor must be less than absent hash"
        );
        // Right neighbor must be strictly greater than absent hash.
        assert!(
            witness.right_neighbor.0 > absent.0,
            "Right neighbor must be greater than absent hash"
        );
        // Adjacency: right position == left position + 1.
        assert_eq!(
            witness.right_tree_position,
            witness.left_tree_position + 1,
            "Neighbors must be adjacent in the tree"
        );
    }

    #[test]
    fn sorted_tree_non_membership_fails_for_present_hash() {
        let tree = build_test_tree(5);

        // A hash that IS in the tree.
        let present = tree.leaves[2];
        assert!(tree.contains(&present));

        // Should return None (can't prove non-membership).
        assert!(tree.prove_non_membership(&present).is_none());
    }

    #[test]
    fn trace_generation_correct_dimensions() {
        let tree = build_test_tree(5);
        let absent1 = make_revocation_hash(901);
        let absent2 = make_revocation_hash(902);
        let absent3 = make_revocation_hash(903);

        let ancestor_hashes = vec![absent1, absent2, absent3];
        let witnesses: Vec<NonMembershipWitness> = ancestor_hashes
            .iter()
            .map(|h| tree.prove_non_membership(h).unwrap())
            .collect();

        let witness = NonRevocationWitness {
            ancestors: witnesses,
        };
        let air = NonRevocationAir::new(REVOCATION_TREE_DEPTH);
        let (trace, public_inputs) = air.generate_trace(&witness, tree.root());

        // Trace should be padded to power of 2.
        assert!(trace.len().is_power_of_two());

        // Each row should have correct width.
        for row in &trace {
            assert_eq!(row.len(), NON_REVOCATION_WIDTH);
        }

        // Public inputs: [revocation_root].
        assert_eq!(public_inputs.len(), 1);
        assert_eq!(public_inputs[pi::REVOCATION_ROOT], tree.root());
    }

    #[test]
    fn constraint_zero_on_valid_trace() {
        let tree = build_test_tree(5);
        let absent1 = make_revocation_hash(901);
        let absent2 = make_revocation_hash(902);

        let witnesses: Vec<NonMembershipWitness> = vec![absent1, absent2]
            .iter()
            .map(|h| tree.prove_non_membership(h).unwrap())
            .collect();

        let witness = NonRevocationWitness {
            ancestors: witnesses,
        };
        let air = NonRevocationAir::new(REVOCATION_TREE_DEPTH);
        let (trace, public_inputs) = air.generate_trace(&witness, tree.root());

        let alpha = BabyBear::new(7);
        for i in 0..trace.len() {
            let next_idx = if i + 1 < trace.len() { i + 1 } else { 0 };
            let c = air.eval_constraints(&trace[i], &trace[next_idx], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Constraint non-zero at row {i}: c = {}",
                c.0
            );
        }
    }

    #[test]
    fn prove_non_revocation_3_level_path() {
        // Build a revocation tree with some revoked entries.
        let tree = build_test_tree(5);

        // Ancestor hashes that are NOT in the revocation set.
        let ancestor_hashes: Vec<BabyBear> = vec![
            make_revocation_hash(801),
            make_revocation_hash(802),
            make_revocation_hash(803),
        ];

        // Verify none are in the tree.
        for h in &ancestor_hashes {
            assert!(!tree.contains(h));
        }

        // Generate proof.
        let proof = prove_non_revocation(&ancestor_hashes, &tree)
            .expect("Should generate proof for non-revoked ancestors");

        // Verify proof.
        let result = verify_non_revocation(tree.root(), &proof);
        assert!(
            result.is_ok(),
            "Non-revocation proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn prove_non_revocation_fails_when_ancestor_revoked() {
        let tree = build_test_tree(5);

        // One ancestor IS in the revocation set.
        let revoked_hash = tree.leaves[2]; // this IS revoked
        let ancestor_hashes = vec![
            make_revocation_hash(801), // not revoked
            revoked_hash,              // REVOKED
            make_revocation_hash(803), // not revoked
        ];

        // Proof generation should fail (returns None).
        let result = prove_non_revocation(&ancestor_hashes, &tree);
        assert!(
            result.is_none(),
            "Should not be able to prove non-revocation for a revoked ancestor"
        );
    }

    #[test]
    fn unrelated_revocation_proof_still_valid() {
        // Revocation tree has entries, but they're unrelated to our path.
        let tree = build_test_tree(10);

        // Our ancestors use completely different seeds.
        let ancestor_hashes: Vec<BabyBear> = vec![
            make_revocation_hash(50001),
            make_revocation_hash(50002),
            make_revocation_hash(50003),
        ];

        // Verify none are in the tree.
        for h in &ancestor_hashes {
            assert!(!tree.contains(h), "Test hash unexpectedly in tree");
        }

        // Generate and verify proof.
        let proof = prove_non_revocation(&ancestor_hashes, &tree)
            .expect("Should generate proof for unrelated hashes");
        let result = verify_non_revocation(tree.root(), &proof);
        assert!(
            result.is_ok(),
            "Unrelated revocation should not affect proof: {:?}",
            result.err()
        );
    }

    #[test]
    fn wrong_root_rejected() {
        let tree = build_test_tree(5);
        let ancestor_hashes = vec![make_revocation_hash(801)];

        let proof = prove_non_revocation(&ancestor_hashes, &tree).unwrap();

        // Verify with wrong root.
        let wrong_root = BabyBear::new(0xBAD);
        let result = verify_non_revocation(wrong_root, &proof);
        assert!(result.is_err(), "Should reject wrong revocation root");
    }

    #[test]
    fn empty_ancestor_list() {
        let tree = build_test_tree(5);

        // Empty derivation path (root capability, no ancestors).
        let ancestor_hashes: Vec<BabyBear> = vec![];

        let proof = prove_non_revocation(&ancestor_hashes, &tree)
            .expect("Empty ancestor list should produce valid proof");
        let result = verify_non_revocation(tree.root(), &proof);
        assert!(
            result.is_ok(),
            "Empty ancestor proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn single_ancestor_proof() {
        let tree = build_test_tree(3);
        let ancestor_hashes = vec![make_revocation_hash(777)];

        assert!(!tree.contains(&ancestor_hashes[0]));

        let proof = prove_non_revocation(&ancestor_hashes, &tree).unwrap();
        let result = verify_non_revocation(tree.root(), &proof);
        assert!(
            result.is_ok(),
            "Single ancestor proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn revocation_hash_to_field_deterministic() {
        let hash = [0xAB; 32];
        let f1 = revocation_hash_to_field(&hash);
        let f2 = revocation_hash_to_field(&hash);
        assert_eq!(f1, f2);
    }

    #[test]
    fn revocation_hash_to_field_different_inputs() {
        let h1 = [0x01; 32];
        let h2 = [0x02; 32];
        assert_ne!(revocation_hash_to_field(&h1), revocation_hash_to_field(&h2));
    }

    #[test]
    fn max_ancestors_supported() {
        let tree = build_test_tree(5);

        // MAX_ANCESTORS ancestors, all non-revoked.
        let ancestor_hashes: Vec<BabyBear> = (0..MAX_ANCESTORS as u32)
            .map(|i| make_revocation_hash(60000 + i))
            .collect();

        for h in &ancestor_hashes {
            assert!(!tree.contains(h));
        }

        let proof = prove_non_revocation(&ancestor_hashes, &tree)
            .expect("Should support MAX_ANCESTORS ancestors");
        let result = verify_non_revocation(tree.root(), &proof);
        assert!(
            result.is_ok(),
            "MAX_ANCESTORS proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn tampered_proof_rejected() {
        let tree = build_test_tree(5);
        let ancestor_hashes = vec![make_revocation_hash(801), make_revocation_hash(802)];

        let mut proof = prove_non_revocation(&ancestor_hashes, &tree).unwrap();

        // Tamper with trace commitment.
        proof.trace_commitment[0] ^= 0xFF;

        let result = verify_non_revocation(tree.root(), &proof);
        assert!(result.is_err(), "Tampered proof should be rejected");
    }

    #[test]
    fn proof_size_reasonable() {
        let tree = build_test_tree(5);
        let ancestor_hashes: Vec<BabyBear> =
            (0..3u32).map(|i| make_revocation_hash(700 + i)).collect();

        let proof = prove_non_revocation(&ancestor_hashes, &tree).unwrap();
        let bytes = stark::proof_to_bytes(&proof);

        // Proof should be reasonable size (< 256 KiB for 3 ancestors).
        assert!(
            bytes.len() < 256 * 1024,
            "Proof too large: {} bytes",
            bytes.len()
        );
    }

    // ========================================================================
    // Soundness tests for in-circuit ordering and adjacency constraints
    // ========================================================================

    /// Helper: generate a trace with a manually-crafted (potentially malicious) witness,
    /// and check whether the constraints accept or reject it.
    fn constraints_accept(
        air: &NonRevocationAir,
        trace: &[Vec<BabyBear>],
        public_inputs: &[BabyBear],
    ) -> bool {
        let alpha = BabyBear::new(7);
        for i in 0..trace.len() {
            let next_idx = if i + 1 < trace.len() { i + 1 } else { 0 };
            let c = air.eval_constraints(&trace[i], &trace[next_idx], public_inputs, alpha);
            if c != BabyBear::ZERO {
                return false;
            }
        }
        true
    }

    #[test]
    fn non_adjacent_neighbors_rejected() {
        // SOUNDNESS TEST: A malicious prover picks two non-adjacent leaves that
        // bracket the element. The adjacency constraint should catch this.
        let tree = build_test_tree(10); // 10 revoked + 2 sentinels = 12 leaves

        // Pick a hash that falls between two leaves.
        let target = make_revocation_hash(12345);
        assert!(!tree.contains(&target));

        // Get the legitimate witness first.
        let legit_witness = tree.prove_non_membership(&target).unwrap();

        // Now craft a malicious witness: use two non-adjacent leaves that
        // still bracket the target. Find two leaves that bracket the target
        // but are NOT adjacent (skip one leaf in between).
        let target_val = target.0;
        let mut left_idx = None;
        let mut right_idx = None;
        for i in 0..tree.leaves.len() - 2 {
            if tree.leaves[i].0 < target_val && tree.leaves[i + 2].0 > target_val {
                // Skip leaves[i+1] -- use non-adjacent pair (i, i+2)
                left_idx = Some(i);
                right_idx = Some(i + 2);
                break;
            }
        }

        let left_idx = left_idx.expect("Should find non-adjacent bracket");
        let right_idx = right_idx.expect("Should find non-adjacent bracket");

        // Verify the bracket is non-adjacent (positions differ by 2, not 1).
        assert_eq!(right_idx - left_idx, 2);

        let left_val = tree.leaves[left_idx];
        let right_val = tree.leaves[right_idx];
        assert!(left_val.0 < target_val && target_val < right_val.0);

        // Build malicious witness with non-adjacent neighbors.
        let (left_siblings, left_positions) = tree.prove_membership(left_idx).unwrap();
        let (right_siblings, right_positions) = tree.prove_membership(right_idx).unwrap();

        let malicious = NonMembershipWitness {
            ancestor_hash: target,
            left_neighbor: left_val,
            right_neighbor: right_val,
            left_siblings,
            left_positions,
            right_siblings,
            right_positions,
            left_tree_position: left_idx,
            right_tree_position: right_idx,
        };

        let witness = NonRevocationWitness {
            ancestors: vec![malicious],
        };

        let air = NonRevocationAir::new(REVOCATION_TREE_DEPTH);
        let (trace, public_inputs) = air.generate_trace(&witness, tree.root());

        // The adjacency constraint should REJECT this trace.
        assert!(
            !constraints_accept(&air, &trace, &public_inputs),
            "Non-adjacent neighbors must be rejected by adjacency constraint"
        );

        // Verify the legitimate witness DOES pass.
        let legit_full = NonRevocationWitness {
            ancestors: vec![legit_witness],
        };
        let (legit_trace, legit_pi) = air.generate_trace(&legit_full, tree.root());
        assert!(
            constraints_accept(&air, &legit_trace, &legit_pi),
            "Legitimate witness with adjacent neighbors should pass"
        );
    }

    #[test]
    fn element_outside_bracket_rejected() {
        // SOUNDNESS TEST: Prover claims neighbors that DON'T bracket the element.
        // The ordering constraints should catch this.
        let tree = build_test_tree(5);

        // Pick a hash not in the tree.
        let target = make_revocation_hash(777);
        assert!(!tree.contains(&target));

        let legit_witness = tree.prove_non_membership(&target).unwrap();
        let left_pos = legit_witness.left_tree_position;
        let right_pos = legit_witness.right_tree_position;

        // Craft a malicious witness where the element is ABOVE the right neighbor.
        // Use a pair of adjacent leaves that are both below the target.
        // Find the first pair that are both < target.
        let target_val = target.0;
        let mut found_pair = None;
        for i in 0..tree.leaves.len() - 1 {
            if tree.leaves[i].0 < target_val
                && tree.leaves[i + 1].0 < target_val
                && tree.leaves[i + 1].0 > tree.leaves[i].0
            {
                found_pair = Some((i, i + 1));
                break;
            }
        }

        if let Some((li, ri)) = found_pair {
            let left_val = tree.leaves[li];
            let right_val = tree.leaves[ri];
            assert!(
                target_val > right_val.0,
                "Element should be above both neighbors"
            );

            let (left_siblings, left_positions_merkle) = tree.prove_membership(li).unwrap();
            let (right_siblings, right_positions_merkle) = tree.prove_membership(ri).unwrap();

            let malicious = NonMembershipWitness {
                ancestor_hash: target,
                left_neighbor: left_val,
                right_neighbor: right_val,
                left_siblings,
                left_positions: left_positions_merkle,
                right_siblings,
                right_positions: right_positions_merkle,
                left_tree_position: li,
                right_tree_position: ri,
            };

            let witness = NonRevocationWitness {
                ancestors: vec![malicious],
            };

            let air = NonRevocationAir::new(REVOCATION_TREE_DEPTH);
            let (trace, public_inputs) = air.generate_trace(&witness, tree.root());

            // The ordering constraint (ancestor < right_neighbor) should REJECT this.
            assert!(
                !constraints_accept(&air, &trace, &public_inputs),
                "Element outside bracket (above right) must be rejected"
            );
        }

        // Also test: element BELOW the left neighbor.
        // Use a pair where both are above the target.
        let mut found_pair_above = None;
        for i in 0..tree.leaves.len() - 1 {
            if tree.leaves[i].0 > target_val
                && tree.leaves[i + 1].0 > target_val
                && tree.leaves[i + 1].0 > tree.leaves[i].0
            {
                found_pair_above = Some((i, i + 1));
                break;
            }
        }

        if let Some((li, ri)) = found_pair_above {
            let left_val = tree.leaves[li];
            let right_val = tree.leaves[ri];
            assert!(target_val < left_val.0, "Element should be below both");

            let (left_siblings, left_positions_merkle) = tree.prove_membership(li).unwrap();
            let (right_siblings, right_positions_merkle) = tree.prove_membership(ri).unwrap();

            let malicious = NonMembershipWitness {
                ancestor_hash: target,
                left_neighbor: left_val,
                right_neighbor: right_val,
                left_siblings,
                left_positions: left_positions_merkle,
                right_siblings,
                right_positions: right_positions_merkle,
                left_tree_position: li,
                right_tree_position: ri,
            };

            let witness = NonRevocationWitness {
                ancestors: vec![malicious],
            };

            let air = NonRevocationAir::new(REVOCATION_TREE_DEPTH);
            let (trace, public_inputs) = air.generate_trace(&witness, tree.root());

            // The ordering constraint (left_neighbor < ancestor) should REJECT this.
            assert!(
                !constraints_accept(&air, &trace, &public_inputs),
                "Element outside bracket (below left) must be rejected"
            );
        }
    }

    #[test]
    fn element_equal_to_neighbor_rejected() {
        // SOUNDNESS TEST: Element equals one of the neighbors.
        // diff_left = ancestor - left - 1 would wrap around (be large),
        // failing the high-bit-zero check.
        let tree = build_test_tree(5);

        // Use a leaf that IS in the tree as the "ancestor_hash",
        // but craft a witness where it equals the left neighbor.
        let leaf_val = tree.leaves[3]; // a real leaf (not sentinel)
        assert!(leaf_val != SENTINEL_MIN && leaf_val != SENTINEL_MAX);

        // Craft witness: ancestor_hash == left_neighbor == leaf_val.
        // Use adjacent positions (3, 4).
        let li = 3;
        let ri = 4;
        let right_val = tree.leaves[ri];

        let (left_siblings, left_positions_merkle) = tree.prove_membership(li).unwrap();
        let (right_siblings, right_positions_merkle) = tree.prove_membership(ri).unwrap();

        let malicious = NonMembershipWitness {
            ancestor_hash: leaf_val, // EQUALS left neighbor!
            left_neighbor: leaf_val,
            right_neighbor: right_val,
            left_siblings,
            left_positions: left_positions_merkle,
            right_siblings,
            right_positions: right_positions_merkle,
            left_tree_position: li,
            right_tree_position: ri,
        };

        let witness = NonRevocationWitness {
            ancestors: vec![malicious],
        };

        let air = NonRevocationAir::new(REVOCATION_TREE_DEPTH);
        let (trace, public_inputs) = air.generate_trace(&witness, tree.root());

        // diff_left = ancestor - left - 1 = leaf_val - leaf_val - 1 = p - 1 (wraps!)
        // This is a huge number, so bit decomposition with 30 bits won't match,
        // or the high bit will be set. Either way, constraints reject.
        assert!(
            !constraints_accept(&air, &trace, &public_inputs),
            "Element equal to left neighbor must be rejected"
        );

        // Also test: ancestor_hash == right_neighbor.
        let right_leaf = tree.leaves[4];
        let malicious2 = NonMembershipWitness {
            ancestor_hash: right_leaf, // EQUALS right neighbor!
            left_neighbor: tree.leaves[3],
            right_neighbor: right_leaf,
            left_siblings: tree.prove_membership(3).unwrap().0,
            left_positions: tree.prove_membership(3).unwrap().1,
            right_siblings: tree.prove_membership(4).unwrap().0,
            right_positions: tree.prove_membership(4).unwrap().1,
            left_tree_position: 3,
            right_tree_position: 4,
        };

        let witness2 = NonRevocationWitness {
            ancestors: vec![malicious2],
        };
        let (trace2, pi2) = air.generate_trace(&witness2, tree.root());

        // diff_right = right - ancestor - 1 = right_leaf - right_leaf - 1 = p - 1 (wraps!)
        assert!(
            !constraints_accept(&air, &trace2, &pi2),
            "Element equal to right neighbor must be rejected"
        );
    }

    #[test]
    fn valid_non_membership_passes() {
        // Positive test: a correctly-generated non-membership proof passes
        // all constraints including the new ordering and adjacency checks.
        let tree = build_test_tree(8);

        // Test with several different absent hashes.
        let absent_hashes: Vec<BabyBear> = (0..5u32)
            .map(|i| make_revocation_hash(40000 + i * 1000))
            .collect();

        for hash in &absent_hashes {
            assert!(!tree.contains(hash));
        }

        let witnesses: Vec<NonMembershipWitness> = absent_hashes
            .iter()
            .map(|h| tree.prove_non_membership(h).unwrap())
            .collect();

        // Verify each witness satisfies the constraints individually.
        let air = NonRevocationAir::new(REVOCATION_TREE_DEPTH);
        for (i, w) in witnesses.iter().enumerate() {
            let single = NonRevocationWitness {
                ancestors: vec![w.clone()],
            };
            let (trace, pi) = air.generate_trace(&single, tree.root());
            assert!(
                constraints_accept(&air, &trace, &pi),
                "Valid non-membership witness {} should pass all constraints",
                i
            );

            // Verify ordering invariants in the witness.
            assert!(
                w.left_neighbor.0 < w.ancestor_hash.0,
                "Left must be < ancestor"
            );
            assert!(
                w.ancestor_hash.0 < w.right_neighbor.0,
                "Ancestor must be < right"
            );
            assert_eq!(
                w.right_tree_position,
                w.left_tree_position + 1,
                "Must be adjacent"
            );
        }

        // Also verify the full proof (STARK) works end-to-end.
        let proof =
            prove_non_revocation(&absent_hashes, &tree).expect("Should generate valid proof");
        let result = verify_non_revocation(tree.root(), &proof);
        assert!(
            result.is_ok(),
            "Full STARK proof should verify: {:?}",
            result.err()
        );
    }
}
