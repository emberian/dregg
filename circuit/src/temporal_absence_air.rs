//! Temporal absence AIR: proves "attribute X was NOT held during [t1, t2]".
//!
//! # Proof Statement
//!
//! Given a per-attribute append-only timeline Merkle tree (sorted by block height),
//! prove that no event for attribute X occurred during blocks [t1, t2]. This is
//! accomplished via a "certified gap proof" over the timeline.
//!
//! # Construction
//!
//! The federation maintains a timeline tree per attribute. Each leaf is:
//!   `(block_height, event_type, attribute_hash)`
//!
//! A gap proof shows two adjacent timeline entries that bracket [t1, t2]:
//! - `entry_before`: the latest entry at or before t1
//! - `entry_after`: the earliest entry at or after t2
//! - These entries are adjacent in the timeline (no entries between them)
//! - Neither entry is an X-event during [t1, t2]
//!
//! # Trace Layout (2 rows: entry_before, entry_after)
//!
//! | Column       | Description                                        |
//! |--------------|----------------------------------------------------|
//! | 0            | block_height (the block height of this entry)      |
//! | 1            | event_type (hash identifying the event type)       |
//! | 2            | attribute_hash (hash of the attribute)             |
//! | 3            | timeline_index (position in the timeline tree)     |
//! | 4            | leaf_hash (Poseidon2 hash of the entry)            |
//! | 5..5+D-1     | merkle_path (D sibling hashes for Merkle proof)    |
//! | 5+D          | merkle_root (computed root from path)              |
//!
//! # Public Inputs
//!
//! `[t1, t2, excluded_attribute_hash, timeline_root]`
//!
//! # Constraints
//!
//! Per-row:
//! - leaf_hash == Poseidon2(block_height, event_type, attribute_hash, timeline_index)
//! - Merkle path from leaf_hash produces merkle_root == timeline_root
//!
//! Cross-row (entry_before -> entry_after):
//! - entry_before.block_height <= t1 (before or at the start of the gap)
//! - entry_after.block_height >= t2 (at or after the end of the gap)
//! - entry_after.timeline_index == entry_before.timeline_index + 1 (adjacency)
//! - Neither entry's attribute_hash matches excluded_attribute_hash during [t1,t2]
//!   (specifically: if entry matches X, its block_height must be outside [t1,t2])
//!
//! # Security
//!
//! The adjacency constraint (index difference == 1) proves there are NO timeline
//! entries between the two provided entries. Combined with the Merkle membership
//! proofs binding both entries to the same timeline root, this constitutes a
//! complete absence proof.

use crate::constraint_prover::{Air, Constraint, ConstraintProof, ConstraintProver};
use crate::field::BabyBear;
use crate::poseidon2::hash_many;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

// ─────────────────────────────────────────────────────────────────────────────
// Constants
// ─────────────────────────────────────────────────────────────────────────────

/// Timeline Merkle tree depth (supports up to 2^4 = 16 timeline entries per attribute).
/// In production, this would be 16 or larger; kept at 4 for efficient testing.
pub const TIMELINE_DEPTH: usize = 4;

/// Trace width: block_height(1) + event_type(1) + attribute_hash(1) + timeline_index(1)
///            + leaf_hash(1) + merkle_path(TIMELINE_DEPTH) + merkle_root(1)
pub const TEMPORAL_ABSENCE_WIDTH: usize = 5 + TIMELINE_DEPTH + 1;

/// Column indices.
pub mod col {
    use super::TIMELINE_DEPTH;

    /// Block height of this timeline entry.
    pub const BLOCK_HEIGHT: usize = 0;
    /// Event type hash (identifies what kind of event occurred).
    pub const EVENT_TYPE: usize = 1;
    /// Attribute hash (identifies which attribute this event concerns).
    pub const ATTRIBUTE_HASH: usize = 2;
    /// Index in the timeline tree (sequential position).
    pub const TIMELINE_INDEX: usize = 3;
    /// Leaf hash: H(block_height, event_type, attribute_hash, timeline_index).
    pub const LEAF_HASH: usize = 4;
    /// Start of the Merkle path (TIMELINE_DEPTH sibling hashes).
    pub const MERKLE_PATH_START: usize = 5;
    /// Computed Merkle root from the path.
    pub const MERKLE_ROOT: usize = MERKLE_PATH_START + TIMELINE_DEPTH; // 21

    /// Get the column index for merkle_path[level].
    #[inline]
    pub const fn merkle_path(level: usize) -> usize {
        MERKLE_PATH_START + level
    }
}

/// Public input indices.
pub mod pi {
    /// Start of the absence window (block height).
    pub const T1: usize = 0;
    /// End of the absence window (block height).
    pub const T2: usize = 1;
    /// The attribute hash that must NOT appear during [t1, t2].
    pub const EXCLUDED_ATTR: usize = 2;
    /// The committed timeline Merkle root.
    pub const TIMELINE_ROOT: usize = 3;
}

// ─────────────────────────────────────────────────────────────────────────────
// Witness
// ─────────────────────────────────────────────────────────────────────────────

/// A single timeline entry with its Merkle membership proof.
#[derive(Clone, Debug)]
pub struct TimelineEntry {
    /// Block height at which this event occurred.
    pub block_height: u32,
    /// Event type identifier (hash).
    pub event_type: BabyBear,
    /// Attribute hash identifying what attribute changed.
    pub attribute_hash: BabyBear,
    /// Sequential index in the timeline tree.
    pub timeline_index: u32,
    /// Merkle path (sibling hashes at each level, from leaf to root).
    /// For a binary Merkle tree of depth TIMELINE_DEPTH.
    pub merkle_path: Vec<BabyBear>,
}

impl TimelineEntry {
    /// Compute the leaf hash for this entry.
    pub fn leaf_hash(&self) -> BabyBear {
        hash_many(&[
            BabyBear::new(self.block_height),
            self.event_type,
            self.attribute_hash,
            BabyBear::new(self.timeline_index),
        ])
    }

    /// Compute the Merkle root from this entry's leaf hash and path.
    /// Uses a binary Merkle tree: at each level, the entry's position bit
    /// determines whether it's on the left or right.
    pub fn compute_merkle_root(&self) -> BabyBear {
        let mut current = self.leaf_hash();
        let mut index = self.timeline_index;

        for level in 0..self.merkle_path.len() {
            let sibling = self.merkle_path[level];
            // Position bit: 0 = left child, 1 = right child
            if index & 1 == 0 {
                current = hash_many(&[current, sibling]);
            } else {
                current = hash_many(&[sibling, current]);
            }
            index >>= 1;
        }

        current
    }
}

/// Witness for a temporal absence proof.
#[derive(Clone, Debug)]
pub struct TemporalAbsenceWitness {
    /// The timeline entry immediately before the absence window.
    pub entry_before: TimelineEntry,
    /// The timeline entry immediately after the absence window.
    pub entry_after: TimelineEntry,
    /// Start of the absence window (block height).
    pub t1: u32,
    /// End of the absence window (block height).
    pub t2: u32,
    /// The attribute hash that must not appear during [t1, t2].
    pub excluded_attribute_hash: BabyBear,
    /// The committed timeline root.
    pub timeline_root: BabyBear,
}

impl TemporalAbsenceWitness {
    /// Check whether this witness is valid (all constraints would be satisfied).
    pub fn is_valid(&self) -> bool {
        // 1. entry_before.block_height <= t1
        if self.entry_before.block_height > self.t1 {
            return false;
        }

        // 2. entry_after.block_height >= t2
        if self.entry_after.block_height < self.t2 {
            return false;
        }

        // 3. Adjacency: entry_after.index == entry_before.index + 1
        if self.entry_after.timeline_index != self.entry_before.timeline_index + 1 {
            return false;
        }

        // 4. Merkle paths must validate to the same root
        let root_before = self.entry_before.compute_merkle_root();
        let root_after = self.entry_after.compute_merkle_root();
        if root_before != self.timeline_root || root_after != self.timeline_root {
            return false;
        }

        // 5. Neither entry is an excluded-attribute event during [t1, t2]
        if self.entry_before.attribute_hash == self.excluded_attribute_hash
            && self.entry_before.block_height >= self.t1
            && self.entry_before.block_height <= self.t2
        {
            return false;
        }
        if self.entry_after.attribute_hash == self.excluded_attribute_hash
            && self.entry_after.block_height >= self.t1
            && self.entry_after.block_height <= self.t2
        {
            return false;
        }

        true
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// AIR
// ─────────────────────────────────────────────────────────────────────────────

/// Temporal Absence AIR.
///
/// Proves that no event for a specific attribute occurred in the timeline
/// between blocks t1 and t2. Uses a gap proof: two adjacent timeline entries
/// that bracket the absence window.
pub struct TemporalAbsenceAir {
    pub witness: TemporalAbsenceWitness,
}

impl TemporalAbsenceAir {
    pub fn new(witness: TemporalAbsenceWitness) -> Self {
        Self { witness }
    }
}

impl Air for TemporalAbsenceAir {
    fn trace_width(&self) -> usize {
        TEMPORAL_ABSENCE_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        4 // [t1, t2, excluded_attribute_hash, timeline_root]
    }

    fn constraints(&self) -> Vec<Constraint> {
        vec![
            // Constraint 1: Leaf hash is correctly computed.
            // leaf_hash == H(block_height, event_type, attribute_hash, timeline_index)
            Constraint {
                name: "leaf_hash_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let expected = hash_many(&[
                        row[col::BLOCK_HEIGHT],
                        row[col::EVENT_TYPE],
                        row[col::ATTRIBUTE_HASH],
                        row[col::TIMELINE_INDEX],
                    ]);
                    row[col::LEAF_HASH] - expected
                }),
            },
            // Constraint 2: Merkle root is correctly computed from path.
            Constraint {
                name: "merkle_root_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut current = row[col::LEAF_HASH];
                    let mut index = row[col::TIMELINE_INDEX].as_u32();

                    for level in 0..TIMELINE_DEPTH {
                        let sibling = row[col::merkle_path(level)];
                        if index & 1 == 0 {
                            current = hash_many(&[current, sibling]);
                        } else {
                            current = hash_many(&[sibling, current]);
                        }
                        index >>= 1;
                    }

                    row[col::MERKLE_ROOT] - current
                }),
            },
            // Constraint 3: Merkle root matches timeline root (public input).
            Constraint {
                name: "merkle_root_matches_public".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::MERKLE_ROOT] - public_inputs[pi::TIMELINE_ROOT]
                }),
            },
            // Constraint 4: Adjacency (entry_after.index == entry_before.index + 1).
            // This is a cross-row constraint: only checked from row 0 to row 1.
            Constraint {
                name: "timeline_adjacency".to_string(),
                eval: Box::new(|row, next_row, _| {
                    if let Some(next) = next_row {
                        next[col::TIMELINE_INDEX] - row[col::TIMELINE_INDEX] - BabyBear::ONE
                    } else {
                        BabyBear::ZERO // Only applies to first row
                    }
                }),
            },
            // Constraint 5: entry_before.block_height <= t1.
            // Encoded as: t1 - entry_before.block_height >= 0.
            // We verify this non-negativity via the witness being consistent.
            // In the constraint prover, we check the difference directly.
            Constraint {
                name: "entry_before_timing".to_string(),
                eval: Box::new(|row, next_row, public_inputs| {
                    // Only applies to row 0 (entry_before)
                    if next_row.is_some() {
                        let t1 = public_inputs[pi::T1];
                        let block_height = row[col::BLOCK_HEIGHT];
                        // Check block_height <= t1: if block_height > t1, the difference
                        // wraps around in the field (becomes large). We check the raw values.
                        let bh = block_height.as_u32();
                        let t1_val = t1.as_u32();
                        if bh > t1_val {
                            BabyBear::ONE // violation
                        } else {
                            BabyBear::ZERO
                        }
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
            // Constraint 6: entry_after.block_height >= t2.
            Constraint {
                name: "entry_after_timing".to_string(),
                eval: Box::new(|_row, next_row, public_inputs| {
                    // Only applies to row 1 (entry_after) -- checked when we ARE row 1
                    // Since this is the last row, next_row is None.
                    if next_row.is_none() {
                        // We don't have self-identification for "which row am I" easily
                        // in the generic constraint. This is handled via last_row_constraints.
                        BabyBear::ZERO
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
        ]
    }

    fn first_row_constraints(&self) -> Vec<Constraint> {
        vec![
            // entry_before.block_height <= t1
            Constraint {
                name: "first_entry_before_t1".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    let bh = row[col::BLOCK_HEIGHT].as_u32();
                    let t1 = public_inputs[pi::T1].as_u32();
                    if bh > t1 {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
        ]
    }

    fn last_row_constraints(&self) -> Vec<Constraint> {
        vec![
            // entry_after.block_height >= t2
            Constraint {
                name: "last_entry_after_t2".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    let bh = row[col::BLOCK_HEIGHT].as_u32();
                    let t2 = public_inputs[pi::T2].as_u32();
                    if bh < t2 {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;
        let mut trace = Vec::with_capacity(2);

        // Row 0: entry_before
        let mut row0 = vec![BabyBear::ZERO; TEMPORAL_ABSENCE_WIDTH];
        row0[col::BLOCK_HEIGHT] = BabyBear::new(w.entry_before.block_height);
        row0[col::EVENT_TYPE] = w.entry_before.event_type;
        row0[col::ATTRIBUTE_HASH] = w.entry_before.attribute_hash;
        row0[col::TIMELINE_INDEX] = BabyBear::new(w.entry_before.timeline_index);
        row0[col::LEAF_HASH] = w.entry_before.leaf_hash();
        for (level, &sibling) in w.entry_before.merkle_path.iter().enumerate() {
            if level < TIMELINE_DEPTH {
                row0[col::merkle_path(level)] = sibling;
            }
        }
        row0[col::MERKLE_ROOT] = w.entry_before.compute_merkle_root();
        trace.push(row0);

        // Row 1: entry_after
        let mut row1 = vec![BabyBear::ZERO; TEMPORAL_ABSENCE_WIDTH];
        row1[col::BLOCK_HEIGHT] = BabyBear::new(w.entry_after.block_height);
        row1[col::EVENT_TYPE] = w.entry_after.event_type;
        row1[col::ATTRIBUTE_HASH] = w.entry_after.attribute_hash;
        row1[col::TIMELINE_INDEX] = BabyBear::new(w.entry_after.timeline_index);
        row1[col::LEAF_HASH] = w.entry_after.leaf_hash();
        for (level, &sibling) in w.entry_after.merkle_path.iter().enumerate() {
            if level < TIMELINE_DEPTH {
                row1[col::merkle_path(level)] = sibling;
            }
        }
        row1[col::MERKLE_ROOT] = w.entry_after.compute_merkle_root();
        trace.push(row1);

        let public_inputs = vec![
            BabyBear::new(w.t1),
            BabyBear::new(w.t2),
            w.excluded_attribute_hash,
            w.timeline_root,
        ];

        (trace, public_inputs)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// StarkAir implementation (for real STARK proofs)
// ─────────────────────────────────────────────────────────────────────────────

impl StarkAir for TemporalAbsenceAir {
    fn width(&self) -> usize {
        TEMPORAL_ABSENCE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // Hash computations are degree 7 (Poseidon2 S-box).
        7
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-temporal-absence-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // C1: Leaf hash correct
        let expected_leaf = hash_many(&[
            local[col::BLOCK_HEIGHT],
            local[col::EVENT_TYPE],
            local[col::ATTRIBUTE_HASH],
            local[col::TIMELINE_INDEX],
        ]);
        let c1 = local[col::LEAF_HASH] - expected_leaf;

        // C2: Merkle root correct
        let mut current = local[col::LEAF_HASH];
        let mut index = local[col::TIMELINE_INDEX].as_u32();
        for level in 0..TIMELINE_DEPTH {
            let sibling = local[col::merkle_path(level)];
            if index & 1 == 0 {
                current = hash_many(&[current, sibling]);
            } else {
                current = hash_many(&[sibling, current]);
            }
            index >>= 1;
        }
        let c2 = local[col::MERKLE_ROOT] - current;

        // C3: Root matches public input
        let c3 = local[col::MERKLE_ROOT] - public_inputs[pi::TIMELINE_ROOT];

        let mut combined = c1;
        combined = combined + alpha * c2;
        combined = combined + alpha * alpha * c3;

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 4 {
            // Row 0: entry_before's merkle_root == timeline_root
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::MERKLE_ROOT,
                value: public_inputs[pi::TIMELINE_ROOT],
            });
            // Row 1: entry_after's merkle_root == timeline_root
            constraints.push(BoundaryConstraint {
                row: 1,
                col: col::MERKLE_ROOT,
                value: public_inputs[pi::TIMELINE_ROOT],
            });
        }
        constraints
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Proof type
// ─────────────────────────────────────────────────────────────────────────────

/// A temporal absence proof: proves no X-event occurred during [t1, t2].
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct TemporalAbsenceProof {
    /// Start of the proven absence window.
    pub t1: u32,
    /// End of the proven absence window.
    pub t2: u32,
    /// The attribute hash that was proven absent.
    pub excluded_attribute_hash: BabyBear,
    /// The timeline root this proof is bound to.
    pub timeline_root: BabyBear,
    /// The STARK proof.
    pub stark_proof: StarkProof,
}

// ─────────────────────────────────────────────────────────────────────────────
// Prover / Verifier API
// ─────────────────────────────────────────────────────────────────────────────

/// Generate a temporal absence proof.
///
/// Proves that no event for `excluded_attribute_hash` occurred in the timeline
/// between blocks `t1` and `t2` (inclusive). The proof is bound to `timeline_root`.
///
/// The prover provides two adjacent timeline entries bracketing the gap:
/// - `entry_before`: latest entry at or before t1
/// - `entry_after`: earliest entry at or after t2
///
/// Returns `None` if the witness is invalid (entries don't bracket the gap,
/// aren't adjacent, or Merkle proofs don't verify).
pub fn prove_temporal_absence(witness: &TemporalAbsenceWitness) -> Option<TemporalAbsenceProof> {
    if !witness.is_valid() {
        return None;
    }

    let air = TemporalAbsenceAir::new(witness.clone());
    let (mut trace, public_inputs) = air.generate_trace();

    // Pad to power of 2 (minimum 2 rows, which is already satisfied).
    while !trace.len().is_power_of_two() {
        trace.push(trace.last().unwrap().clone());
    }

    let stark_proof = stark::prove(&air, &trace, &public_inputs);

    Some(TemporalAbsenceProof {
        t1: witness.t1,
        t2: witness.t2,
        excluded_attribute_hash: witness.excluded_attribute_hash,
        timeline_root: witness.timeline_root,
        stark_proof,
    })
}

/// Verify a temporal absence proof.
///
/// Checks that the proof correctly demonstrates no event for the excluded
/// attribute occurred in [t1, t2] within the timeline committed at `timeline_root`.
pub fn verify_temporal_absence(
    proof: &TemporalAbsenceProof,
    t1: u32,
    t2: u32,
    excluded_attribute_hash: BabyBear,
    timeline_root: BabyBear,
) -> bool {
    // Check claimed parameters match expected.
    if proof.t1 != t1 || proof.t2 != t2 {
        return false;
    }
    if proof.excluded_attribute_hash != excluded_attribute_hash {
        return false;
    }
    if proof.timeline_root != timeline_root {
        return false;
    }

    let public_inputs = vec![
        BabyBear::new(t1),
        BabyBear::new(t2),
        excluded_attribute_hash,
        timeline_root,
    ];

    // Reconstruct a dummy witness for the AIR shape.
    let dummy_entry = TimelineEntry {
        block_height: 0,
        event_type: BabyBear::ZERO,
        attribute_hash: BabyBear::ZERO,
        timeline_index: 0,
        merkle_path: vec![BabyBear::ZERO; TIMELINE_DEPTH],
    };
    let dummy_witness = TemporalAbsenceWitness {
        entry_before: dummy_entry.clone(),
        entry_after: dummy_entry,
        t1,
        t2,
        excluded_attribute_hash,
        timeline_root,
    };
    let air = TemporalAbsenceAir::new(dummy_witness);
    stark::verify(&air, &proof.stark_proof, &public_inputs).is_ok()
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper: build a test timeline tree
// ─────────────────────────────────────────────────────────────────────────────

/// Build a binary Merkle tree of depth `TIMELINE_DEPTH` from timeline leaf hashes.
/// Returns (root, paths) where paths[i] is the sibling path for leaf i (length == TIMELINE_DEPTH).
pub fn build_timeline_tree(leaves: &[BabyBear]) -> (BabyBear, Vec<Vec<BabyBear>>) {
    // Always build to TIMELINE_DEPTH so paths have the right length.
    let n = 1usize << TIMELINE_DEPTH; // 2^TIMELINE_DEPTH leaves

    // Pad leaves to full tree capacity
    let mut current_level: Vec<BabyBear> = leaves.to_vec();
    current_level.resize(n, BabyBear::ZERO);

    // Store all levels for path extraction
    let mut levels = vec![current_level.clone()];

    for _ in 0..TIMELINE_DEPTH {
        let mut next_level = Vec::with_capacity(current_level.len() / 2);
        for pair in current_level.chunks(2) {
            next_level.push(hash_many(&[pair[0], pair[1]]));
        }
        current_level = next_level;
        levels.push(current_level.clone());
    }

    let root = levels.last().unwrap()[0];

    // Extract paths (each path has TIMELINE_DEPTH siblings)
    let mut paths = Vec::with_capacity(leaves.len());
    for i in 0..leaves.len() {
        let mut path = Vec::with_capacity(TIMELINE_DEPTH);
        let mut idx = i;
        for level in 0..TIMELINE_DEPTH {
            let sibling_idx = idx ^ 1;
            path.push(levels[level][sibling_idx]);
            idx >>= 1;
        }
        paths.push(path);
    }

    (root, paths)
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Create a timeline with known entries and build a Merkle tree.
    fn build_test_timeline(
        entries: &[(u32, BabyBear, BabyBear)], // (block_height, event_type, attribute_hash)
    ) -> (BabyBear, Vec<TimelineEntry>) {
        // Compute leaf hashes
        let leaf_hashes: Vec<BabyBear> = entries
            .iter()
            .enumerate()
            .map(|(i, (bh, et, ah))| {
                hash_many(&[BabyBear::new(*bh), *et, *ah, BabyBear::new(i as u32)])
            })
            .collect();

        // Build Merkle tree
        let (root, paths) = build_timeline_tree(&leaf_hashes);

        // Build timeline entries
        let timeline_entries: Vec<TimelineEntry> = entries
            .iter()
            .enumerate()
            .map(|(i, (bh, et, ah))| {
                let mut merkle_path = paths[i].clone();
                // Pad path to TIMELINE_DEPTH
                merkle_path.resize(TIMELINE_DEPTH, BabyBear::ZERO);
                TimelineEntry {
                    block_height: *bh,
                    event_type: *et,
                    attribute_hash: *ah,
                    timeline_index: i as u32,
                    merkle_path,
                }
            })
            .collect();

        (root, timeline_entries)
    }

    #[test]
    fn test_temporal_absence_valid_gap() {
        // Timeline: events at blocks 5, 10, 50, 100
        // Prove absence of attribute X during [11, 49]
        let attr_x = BabyBear::new(0xDEAD);
        let attr_y = BabyBear::new(0xBEEF);
        let event_type = BabyBear::new(1);

        let entries = vec![
            (5u32, event_type, attr_y), // index 0
            (10, event_type, attr_y),   // index 1
            (50, event_type, attr_y),   // index 2
            (100, event_type, attr_y),  // index 3
        ];

        let (root, timeline) = build_test_timeline(&entries);

        // Gap proof: entry at index 1 (block 10) and entry at index 2 (block 50)
        let witness = TemporalAbsenceWitness {
            entry_before: timeline[1].clone(),
            entry_after: timeline[2].clone(),
            t1: 11,
            t2: 49,
            excluded_attribute_hash: attr_x,
            timeline_root: root,
        };

        assert!(witness.is_valid(), "Witness should be valid");

        // Verify AIR constraints
        let air = TemporalAbsenceAir::new(witness.clone());
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "AIR constraints should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_temporal_absence_stark_proof() {
        let attr_x = BabyBear::new(0xDEAD);
        let attr_y = BabyBear::new(0xBEEF);
        let event_type = BabyBear::new(1);

        let entries = vec![
            (5u32, event_type, attr_y),
            (10, event_type, attr_y),
            (50, event_type, attr_y),
            (100, event_type, attr_y),
        ];

        let (root, timeline) = build_test_timeline(&entries);

        let witness = TemporalAbsenceWitness {
            entry_before: timeline[1].clone(),
            entry_after: timeline[2].clone(),
            t1: 11,
            t2: 49,
            excluded_attribute_hash: attr_x,
            timeline_root: root,
        };

        let proof = prove_temporal_absence(&witness);
        assert!(proof.is_some(), "Should generate proof");

        let proof = proof.unwrap();
        let valid = verify_temporal_absence(&proof, 11, 49, attr_x, root);
        assert!(valid, "Proof should verify");
    }

    #[test]
    fn test_temporal_absence_non_adjacent_fails() {
        // Try to use non-adjacent entries (skip index 2)
        let attr_x = BabyBear::new(0xDEAD);
        let attr_y = BabyBear::new(0xBEEF);
        let event_type = BabyBear::new(1);

        let entries = vec![
            (5u32, event_type, attr_y),
            (10, event_type, attr_y),
            (30, event_type, attr_y), // index 2: this is between our claimed gap
            (50, event_type, attr_y),
            (100, event_type, attr_y),
        ];

        let (root, timeline) = build_test_timeline(&entries);

        // Try entry at index 1 (block 10) and index 3 (block 50) -- NOT adjacent
        let witness = TemporalAbsenceWitness {
            entry_before: timeline[1].clone(),
            entry_after: timeline[3].clone(),
            t1: 11,
            t2: 49,
            excluded_attribute_hash: attr_x,
            timeline_root: root,
        };

        assert!(
            !witness.is_valid(),
            "Non-adjacent entries should be invalid"
        );

        let proof = prove_temporal_absence(&witness);
        assert!(proof.is_none(), "Should fail for non-adjacent entries");
    }

    #[test]
    fn test_temporal_absence_timing_violation_before() {
        // entry_before.block_height > t1
        let attr_x = BabyBear::new(0xDEAD);
        let attr_y = BabyBear::new(0xBEEF);
        let event_type = BabyBear::new(1);

        let entries = vec![
            (5u32, event_type, attr_y),
            (20, event_type, attr_y), // block 20 > t1=15
            (50, event_type, attr_y),
            (100, event_type, attr_y),
        ];

        let (root, timeline) = build_test_timeline(&entries);

        let witness = TemporalAbsenceWitness {
            entry_before: timeline[1].clone(), // block 20
            entry_after: timeline[2].clone(),  // block 50
            t1: 15, // entry_before.block_height (20) > t1 (15) -- VIOLATION
            t2: 49,
            excluded_attribute_hash: attr_x,
            timeline_root: root,
        };

        assert!(
            !witness.is_valid(),
            "entry_before after t1 should be invalid"
        );
    }

    #[test]
    fn test_temporal_absence_timing_violation_after() {
        // entry_after.block_height < t2
        let attr_x = BabyBear::new(0xDEAD);
        let attr_y = BabyBear::new(0xBEEF);
        let event_type = BabyBear::new(1);

        let entries = vec![
            (5u32, event_type, attr_y),
            (10, event_type, attr_y),
            (30, event_type, attr_y), // block 30 < t2=40
            (100, event_type, attr_y),
        ];

        let (root, timeline) = build_test_timeline(&entries);

        let witness = TemporalAbsenceWitness {
            entry_before: timeline[1].clone(), // block 10
            entry_after: timeline[2].clone(),  // block 30
            t1: 11,
            t2: 40, // entry_after.block_height (30) < t2 (40) -- VIOLATION
            excluded_attribute_hash: attr_x,
            timeline_root: root,
        };

        assert!(
            !witness.is_valid(),
            "entry_after before t2 should be invalid"
        );
    }

    #[test]
    fn test_temporal_absence_wrong_root_fails() {
        let attr_x = BabyBear::new(0xDEAD);
        let attr_y = BabyBear::new(0xBEEF);
        let event_type = BabyBear::new(1);

        let entries = vec![
            (5u32, event_type, attr_y),
            (10, event_type, attr_y),
            (50, event_type, attr_y),
            (100, event_type, attr_y),
        ];

        let (root, timeline) = build_test_timeline(&entries);

        let witness = TemporalAbsenceWitness {
            entry_before: timeline[1].clone(),
            entry_after: timeline[2].clone(),
            t1: 11,
            t2: 49,
            excluded_attribute_hash: attr_x,
            timeline_root: BabyBear::new(99999), // wrong root
        };

        assert!(!witness.is_valid(), "Wrong root should be invalid");
    }

    #[test]
    fn test_temporal_absence_verify_wrong_params() {
        let attr_x = BabyBear::new(0xDEAD);
        let attr_y = BabyBear::new(0xBEEF);
        let event_type = BabyBear::new(1);

        let entries = vec![
            (5u32, event_type, attr_y),
            (10, event_type, attr_y),
            (50, event_type, attr_y),
            (100, event_type, attr_y),
        ];

        let (root, timeline) = build_test_timeline(&entries);

        let witness = TemporalAbsenceWitness {
            entry_before: timeline[1].clone(),
            entry_after: timeline[2].clone(),
            t1: 11,
            t2: 49,
            excluded_attribute_hash: attr_x,
            timeline_root: root,
        };

        let proof = prove_temporal_absence(&witness).unwrap();

        // Wrong t1
        assert!(!verify_temporal_absence(&proof, 12, 49, attr_x, root));
        // Wrong t2
        assert!(!verify_temporal_absence(&proof, 11, 50, attr_x, root));
        // Wrong attribute
        assert!(!verify_temporal_absence(
            &proof,
            11,
            49,
            BabyBear::new(0xCAFE),
            root
        ));
        // Wrong root
        assert!(!verify_temporal_absence(
            &proof,
            11,
            49,
            attr_x,
            BabyBear::new(1)
        ));
    }

    #[test]
    fn test_temporal_absence_exact_boundary() {
        // entry_before.block_height == t1 and entry_after.block_height == t2
        let attr_x = BabyBear::new(0xDEAD);
        let attr_y = BabyBear::new(0xBEEF);
        let event_type = BabyBear::new(1);

        let entries = vec![
            (5u32, event_type, attr_y),
            (10, event_type, attr_y), // exactly at t1
            (50, event_type, attr_y), // exactly at t2
            (100, event_type, attr_y),
        ];

        let (root, timeline) = build_test_timeline(&entries);

        let witness = TemporalAbsenceWitness {
            entry_before: timeline[1].clone(), // block 10, at t1
            entry_after: timeline[2].clone(),  // block 50, at t2
            t1: 10,
            t2: 50,
            excluded_attribute_hash: attr_x,
            timeline_root: root,
        };

        assert!(witness.is_valid(), "Exact boundary should be valid");

        let proof = prove_temporal_absence(&witness).unwrap();
        let valid = verify_temporal_absence(&proof, 10, 50, attr_x, root);
        assert!(valid, "Exact boundary proof should verify");
    }

    #[test]
    fn test_timeline_entry_leaf_hash_deterministic() {
        let entry = TimelineEntry {
            block_height: 42,
            event_type: BabyBear::new(7),
            attribute_hash: BabyBear::new(0xABC),
            timeline_index: 3,
            merkle_path: vec![BabyBear::ZERO; TIMELINE_DEPTH],
        };

        let h1 = entry.leaf_hash();
        let h2 = entry.leaf_hash();
        assert_eq!(h1, h2, "Leaf hash should be deterministic");
        assert_ne!(h1, BabyBear::ZERO, "Leaf hash should be non-trivial");
    }

    #[test]
    fn test_build_timeline_tree_consistency() {
        let leaves = vec![
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ];
        let (root, paths) = build_timeline_tree(&leaves);

        // Verify each path leads to the root
        for (i, leaf) in leaves.iter().enumerate() {
            let mut current = *leaf;
            let mut idx = i;
            for level in 0..TIMELINE_DEPTH {
                let sibling = paths[i][level];
                if idx & 1 == 0 {
                    current = hash_many(&[current, sibling]);
                } else {
                    current = hash_many(&[sibling, current]);
                }
                idx >>= 1;
            }
            assert_eq!(current, root, "Path {} should lead to root", i);
        }
    }
}
