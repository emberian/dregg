//! Sorted-set **neighbor adjacency** STARK — the Golden-Vision lift that closes
//! the Silver-Sound non-membership forge.
//!
//! # The forge this closes
//!
//! `dregg_cell::predicate::SortedNeighborNonMembershipVerifier` (and the
//! `CredentialSetMembershipVerifier` non-revocation leg) prove a candidate's
//! *absence* from a sorted set by exhibiting two neighbor leaves
//! `lower < candidate < upper` plus a commitment-keyed `adjacency_tag`. That
//! tag binds `(commitment, lower, upper)` but **not** the claim that `lower`
//! and `upper` are actually *adjacent leaves under the committed Merkle root*.
//! An attacker who knows the (public) set commitment can therefore pick
//! `lower = 0x00…`, `upper = 0xFF…`, recompute a valid `adjacency_tag`, and
//! "prove" non-membership for *any* candidate — the documented Silver gap
//! (`AIR-SOUNDNESS-AUDIT.md` finding #2; `predicate.rs`
//! `audit_silver_golden_gap_commitment_knower_can_still_forge_wide_bracket`).
//!
//! # What this AIR proves
//!
//! Given a binary Poseidon2 Merkle tree (sorted leaves, leaf `i` is the `i`-th
//! smallest), this AIR proves, in zero knowledge of the paths:
//!
//! 1. `leaf_lower` is the leaf at index `idx_lower` under `root`
//!    (a full Merkle authentication path).
//! 2. `leaf_upper` is the leaf at index `idx_upper` under the **same** `root`.
//! 3. the indices `idx_lower`, `idx_upper` are reconstructed *inside the
//!    circuit* from each path's direction bits, so they cannot be lied about.
//!
//! [`verify_adjacency`] then enforces `idx_upper == idx_lower + 1` against the
//! circuit-bound index public inputs — the leaves are provably **consecutive**.
//! Because no set member can lie strictly between two consecutive leaves,
//! `lower < candidate < upper` becomes a *sound* non-membership witness, and a
//! forger can no longer invent wide-bracket sentinels.
//!
//! # Index reconstruction without `next`-arithmetic
//!
//! The DSL's only cross-row primitive is [`ConstraintExpr::Transition`]
//! (`next[a] == local[b]`, a pure copy). To reconstruct
//! `idx = Σ_level dir_level · 2^level` we therefore split each accumulation
//! step into a *same-row* polynomial (which the DSL supports at degree ≤ 3)
//! plus a `Transition` copy:
//!
//! - `pow` doubling: same-row `pow2 = 2·pow`, then `Transition(next.pow ←
//!   local.pow2)`.
//! - index step: same-row `idx_out = idx_in + dir·pow`, then
//!   `Transition(next.idx_in ← local.idx_out)`.
//!
//! Row 0 anchors (`pow=1`, `idx_in=0`) and the full indices (`idx_out` at the
//! last row) are bound with *boundary* constraints, which are checked
//! independently of the transition divisor (see the soundness note below).
//!
//! # Trace layout (two parallel paths, one tree level per row)
//!
//! | col | name              | meaning                                          |
//! |-----|-------------------|--------------------------------------------------|
//! | 0   | l_cur             | lower running hash (row 0 = `leaf_lower`)         |
//! | 1   | l_sib             | lower sibling at this level                       |
//! | 2   | l_dir             | lower direction bit (1 ⇒ l_cur is right child)    |
//! | 3   | l_left            | ordered left  = (1-l_dir)·l_cur + l_dir·l_sib     |
//! | 4   | l_right           | ordered right = (1-l_dir)·l_sib + l_dir·l_cur     |
//! | 5   | l_par             | parent = hash_2_to_1(l_left, l_right)             |
//! | 6   | l_idx_in          | index accumulated *before* this level             |
//! | 7   | l_idx_out         | index accumulated *including* this level          |
//! | 8…15| u_*               | (mirror of cols 0..8 for the upper path)          |
//! | 16  | pow               | 2^level for this row (row 0 = 1)                  |
//! | 17  | pow2              | 2·pow (helper feeding next row's pow)             |
//!
//! # Public inputs
//!
//! `[root, leaf_lower, leaf_upper, idx_lower, idx_upper]` (see [`adj_pi`]).
//!
//! # Soundness note (last-row transition gap)
//!
//! Per the STARK transition-vanishing convention (`stark.rs` §"Transition
//! Constraint Evaluation"), *every* constraint — even pure-`local` ones — is
//! enforced on rows `0..n-2` and **not** on the last row. We therefore require
//! the trace depth to be a power of two so the last trace row is a *real*
//! Merkle level, and anchor every must-hold-at-last value (`l_par`/`u_par` =
//! root, `l_idx_out`/`u_idx_out` = indices) with explicit *boundary*
//! constraints. The `idx_out` boundary binds the in-circuit reconstructed
//! index, so a prover cannot bind a tampered index PI.

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};
use crate::field::BabyBear;
use crate::poseidon2::hash_2_to_1;
use crate::stark::{self, StarkProof};

/// AIR name (versioned). A future re-layout bumps the `-v1` suffix so proofs
/// for distinct layouts can never be cross-verified.
pub const ADJACENCY_AIR_NAME: &str = "dregg-membership-adjacency-v1";

/// Column layout for the neighbor-adjacency AIR.
pub mod adj_col {
    // Lower path
    pub const L_CUR: usize = 0;
    pub const L_SIB: usize = 1;
    pub const L_DIR: usize = 2;
    pub const L_LEFT: usize = 3;
    pub const L_RIGHT: usize = 4;
    pub const L_PAR: usize = 5;
    pub const L_IDX_IN: usize = 6;
    pub const L_IDX_OUT: usize = 7;
    // Upper path (mirror of lower, +8)
    pub const U_CUR: usize = 8;
    pub const U_SIB: usize = 9;
    pub const U_DIR: usize = 10;
    pub const U_LEFT: usize = 11;
    pub const U_RIGHT: usize = 12;
    pub const U_PAR: usize = 13;
    pub const U_IDX_IN: usize = 14;
    pub const U_IDX_OUT: usize = 15;
    // Shared power-of-two accumulator
    pub const POW: usize = 16;
    pub const POW2: usize = 17;
}

/// Trace width.
pub const ADJ_WIDTH: usize = 18;

/// Public-input indices.
pub mod adj_pi {
    pub const ROOT: usize = 0;
    pub const LEAF_LOWER: usize = 1;
    pub const LEAF_UPPER: usize = 2;
    pub const IDX_LOWER: usize = 3;
    pub const IDX_UPPER: usize = 4;
}

/// Number of public inputs.
pub const ADJ_PUBLIC_INPUT_COUNT: usize = 5;

// ────────────────────────────────────────────────────────────────────────
// Descriptor
// ────────────────────────────────────────────────────────────────────────

/// Build the neighbor-adjacency `CircuitDescriptor`.
pub fn adjacency_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // Per-path constraints: dir binary, child ordering, parent hash, chain
    // continuity, index accumulation step.
    for (cur, sib, dir, left, right, par, idx_in, idx_out) in [
        (
            adj_col::L_CUR,
            adj_col::L_SIB,
            adj_col::L_DIR,
            adj_col::L_LEFT,
            adj_col::L_RIGHT,
            adj_col::L_PAR,
            adj_col::L_IDX_IN,
            adj_col::L_IDX_OUT,
        ),
        (
            adj_col::U_CUR,
            adj_col::U_SIB,
            adj_col::U_DIR,
            adj_col::U_LEFT,
            adj_col::U_RIGHT,
            adj_col::U_PAR,
            adj_col::U_IDX_IN,
            adj_col::U_IDX_OUT,
        ),
    ] {
        // dir ∈ {0,1}
        constraints.push(ConstraintExpr::Binary { col: dir });

        // left == (1-dir)*cur + dir*sib  ⇔  left - cur - dir*sib + dir*cur == 0
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![left],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![cur],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![dir, sib],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![dir, cur],
                },
            ],
        });

        // right == (1-dir)*sib + dir*cur  ⇔  right - sib - dir*cur + dir*sib == 0
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![right],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![sib],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![dir, cur],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![dir, sib],
                },
            ],
        });

        // par == hash_2_to_1(left, right)
        constraints.push(ConstraintExpr::Hash2to1 {
            output_col: par,
            input_col_a: left,
            input_col_b: right,
        });

        // chain continuity: next.cur == local.par
        constraints.push(ConstraintExpr::Transition {
            next_col: cur,
            local_col: par,
        });

        // index step: idx_out == idx_in + dir*pow  (same-row, degree 2)
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![idx_out],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![idx_in],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![dir, adj_col::POW],
                },
            ],
        });

        // index carry: next.idx_in == local.idx_out
        constraints.push(ConstraintExpr::Transition {
            next_col: idx_in,
            local_col: idx_out,
        });
    }

    // pow2 == 2*pow  (same-row helper)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![adj_col::POW2],
            },
            PolyTerm {
                coeff: -BabyBear::new(2),
                col_indices: vec![adj_col::POW],
            },
        ],
    });

    // pow doubling carry: next.pow == local.pow2
    constraints.push(ConstraintExpr::Transition {
        next_col: adj_col::POW,
        local_col: adj_col::POW2,
    });

    // Boundaries.
    let boundaries = vec![
        // Leaves at row 0.
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: adj_col::L_CUR,
            pi_index: adj_pi::LEAF_LOWER,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: adj_col::U_CUR,
            pi_index: adj_pi::LEAF_UPPER,
        },
        // Root at the last row (both paths agree).
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: adj_col::L_PAR,
            pi_index: adj_pi::ROOT,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: adj_col::U_PAR,
            pi_index: adj_pi::ROOT,
        },
        // Full reconstructed indices at the last row.
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: adj_col::L_IDX_OUT,
            pi_index: adj_pi::IDX_LOWER,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: adj_col::U_IDX_OUT,
            pi_index: adj_pi::IDX_UPPER,
        },
        // Anchor accumulators at row 0: pow=1, idx_in=0 (both paths).
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: adj_col::POW,
            value: BabyBear::ONE,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: adj_col::L_IDX_IN,
            value: BabyBear::ZERO,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: adj_col::U_IDX_IN,
            value: BabyBear::ZERO,
        },
    ];

    let columns = vec![
        col("l_cur", adj_col::L_CUR, ColumnKind::Hash),
        col("l_sib", adj_col::L_SIB, ColumnKind::Value),
        col("l_dir", adj_col::L_DIR, ColumnKind::Binary),
        col("l_left", adj_col::L_LEFT, ColumnKind::Value),
        col("l_right", adj_col::L_RIGHT, ColumnKind::Value),
        col("l_par", adj_col::L_PAR, ColumnKind::Hash),
        col("l_idx_in", adj_col::L_IDX_IN, ColumnKind::Value),
        col("l_idx_out", adj_col::L_IDX_OUT, ColumnKind::Value),
        col("u_cur", adj_col::U_CUR, ColumnKind::Hash),
        col("u_sib", adj_col::U_SIB, ColumnKind::Value),
        col("u_dir", adj_col::U_DIR, ColumnKind::Binary),
        col("u_left", adj_col::U_LEFT, ColumnKind::Value),
        col("u_right", adj_col::U_RIGHT, ColumnKind::Value),
        col("u_par", adj_col::U_PAR, ColumnKind::Hash),
        col("u_idx_in", adj_col::U_IDX_IN, ColumnKind::Value),
        col("u_idx_out", adj_col::U_IDX_OUT, ColumnKind::Value),
        col("pow", adj_col::POW, ColumnKind::Value),
        col("pow2", adj_col::POW2, ColumnKind::Value),
    ];

    CircuitDescriptor {
        name: ADJACENCY_AIR_NAME.into(),
        trace_width: ADJ_WIDTH,
        max_degree: 3,
        columns,
        constraints,
        boundaries,
        public_input_count: ADJ_PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

fn col(name: &str, index: usize, kind: ColumnKind) -> ColumnDef {
    ColumnDef {
        name: name.into(),
        index,
        kind,
    }
}

/// Build the `DslCircuit` for the neighbor-adjacency AIR.
pub fn adjacency_circuit() -> DslCircuit {
    DslCircuit::new(adjacency_descriptor())
}

// ────────────────────────────────────────────────────────────────────────
// Witness / prover
// ────────────────────────────────────────────────────────────────────────

/// A single Merkle authentication step for a binary tree.
///
/// `dir == false` ⇒ the running hash is the **left** child (`parent =
/// hash(cur, sibling)`); `dir == true` ⇒ the running hash is the **right**
/// child (`parent = hash(sibling, cur)`). The bit at level `level` adds
/// `dir << level` to the reconstructed leaf index.
#[derive(Clone, Copy, Debug)]
pub struct AdjStep {
    pub sibling: BabyBear,
    pub dir: bool,
}

/// Compute the root and the reconstructed leaf index implied by a path.
fn walk(leaf: BabyBear, path: &[AdjStep]) -> (BabyBear, u64) {
    let mut cur = leaf;
    let mut idx: u64 = 0;
    for (level, step) in path.iter().enumerate() {
        let (left, right) = if step.dir {
            (step.sibling, cur)
        } else {
            (cur, step.sibling)
        };
        cur = hash_2_to_1(left, right);
        if step.dir {
            idx |= 1u64 << level;
        }
    }
    (cur, idx)
}

/// Errors produced while building or proving an adjacency witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdjacencyError {
    /// The two paths have different depths.
    DepthMismatch { lower: usize, upper: usize },
    /// Depth must be a power of two ≥ 2 (so the last trace row is a real
    /// Merkle level whose parent is the committed root).
    BadDepth { depth: usize },
    /// The two paths reach different roots.
    RootMismatch,
    /// The reconstructed indices are not consecutive (`upper != lower + 1`).
    NotConsecutive { idx_lower: u64, idx_upper: u64 },
    /// STARK verification failed.
    StarkRejected(String),
    /// A public input did not match the proof's bound value.
    PublicInputMismatch(String),
}

impl core::fmt::Display for AdjacencyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::DepthMismatch { lower, upper } => {
                write!(f, "path depth mismatch: lower={lower}, upper={upper}")
            }
            Self::BadDepth { depth } => {
                write!(f, "path depth {depth} must be a power of two ≥ 2")
            }
            Self::RootMismatch => write!(f, "lower and upper paths reach different roots"),
            Self::NotConsecutive {
                idx_lower,
                idx_upper,
            } => write!(
                f,
                "leaves are not consecutive: idx_lower={idx_lower}, idx_upper={idx_upper} \
                 (require idx_upper == idx_lower + 1)"
            ),
            Self::StarkRejected(e) => write!(f, "adjacency STARK rejected: {e}"),
            Self::PublicInputMismatch(e) => write!(f, "adjacency public-input mismatch: {e}"),
        }
    }
}

impl std::error::Error for AdjacencyError {}

/// Generate the adjacency trace + public inputs for two consecutive leaves.
///
/// Returns `(trace, public_inputs)` where `public_inputs` follows [`adj_pi`].
/// Validates power-of-two equal depth, equal roots, and consecutiveness
/// *before* emitting — a dishonest witness fails here, not silently.
pub fn generate_adjacency_trace(
    leaf_lower: BabyBear,
    lower_path: &[AdjStep],
    leaf_upper: BabyBear,
    upper_path: &[AdjStep],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), AdjacencyError> {
    let depth = lower_path.len();
    if depth != upper_path.len() {
        return Err(AdjacencyError::DepthMismatch {
            lower: depth,
            upper: upper_path.len(),
        });
    }
    // Require power-of-two depth ≥ 2 so the last trace row is a real Merkle
    // level (no padding row can move `*_par[last]` off the committed root).
    if depth < 2 || !depth.is_power_of_two() {
        return Err(AdjacencyError::BadDepth { depth });
    }

    let (root_l, idx_lower) = walk(leaf_lower, lower_path);
    let (root_u, idx_upper) = walk(leaf_upper, upper_path);
    if root_l != root_u {
        return Err(AdjacencyError::RootMismatch);
    }
    if idx_upper != idx_lower + 1 {
        return Err(AdjacencyError::NotConsecutive {
            idx_lower,
            idx_upper,
        });
    }

    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(depth);
    let mut l_cur = leaf_lower;
    let mut u_cur = leaf_upper;
    let mut pow = BabyBear::ONE;
    let mut l_idx_in = BabyBear::ZERO;
    let mut u_idx_in = BabyBear::ZERO;

    for level in 0..depth {
        let ls = lower_path[level];
        let us = upper_path[level];

        let l_dir = bit(ls.dir);
        let (l_left, l_right) = if ls.dir {
            (ls.sibling, l_cur)
        } else {
            (l_cur, ls.sibling)
        };
        let l_par = hash_2_to_1(l_left, l_right);
        let l_idx_out = l_idx_in + l_dir * pow;

        let u_dir = bit(us.dir);
        let (u_left, u_right) = if us.dir {
            (us.sibling, u_cur)
        } else {
            (u_cur, us.sibling)
        };
        let u_par = hash_2_to_1(u_left, u_right);
        let u_idx_out = u_idx_in + u_dir * pow;

        let pow2 = pow + pow;

        let mut row = vec![BabyBear::ZERO; ADJ_WIDTH];
        row[adj_col::L_CUR] = l_cur;
        row[adj_col::L_SIB] = ls.sibling;
        row[adj_col::L_DIR] = l_dir;
        row[adj_col::L_LEFT] = l_left;
        row[adj_col::L_RIGHT] = l_right;
        row[adj_col::L_PAR] = l_par;
        row[adj_col::L_IDX_IN] = l_idx_in;
        row[adj_col::L_IDX_OUT] = l_idx_out;
        row[adj_col::U_CUR] = u_cur;
        row[adj_col::U_SIB] = us.sibling;
        row[adj_col::U_DIR] = u_dir;
        row[adj_col::U_LEFT] = u_left;
        row[adj_col::U_RIGHT] = u_right;
        row[adj_col::U_PAR] = u_par;
        row[adj_col::U_IDX_IN] = u_idx_in;
        row[adj_col::U_IDX_OUT] = u_idx_out;
        row[adj_col::POW] = pow;
        row[adj_col::POW2] = pow2;
        trace.push(row);

        l_cur = l_par;
        u_cur = u_par;
        l_idx_in = l_idx_out;
        u_idx_in = u_idx_out;
        pow = pow2;
    }

    // `depth` is already a power of two ≥ 2, so the trace length is correct and
    // the last row is the real root level — no padding needed.
    debug_assert!(trace.len().is_power_of_two());

    let root = root_l;
    let public_inputs = vec![
        root,
        leaf_lower,
        leaf_upper,
        BabyBear::from_u64(idx_lower),
        BabyBear::from_u64(idx_upper),
    ];
    Ok((trace, public_inputs))
}

#[inline]
fn bit(b: bool) -> BabyBear {
    if b { BabyBear::ONE } else { BabyBear::ZERO }
}

/// Prove that `leaf_lower` and `leaf_upper` are consecutive leaves under a
/// shared binary Poseidon2 Merkle root.
///
/// `lower_path` / `upper_path` are leaf→root authentication paths of **equal,
/// power-of-two depth ≥ 2**. Returns a [`StarkProof`] plus the public inputs
/// the verifier must use.
pub fn prove_adjacency(
    leaf_lower: BabyBear,
    lower_path: &[AdjStep],
    leaf_upper: BabyBear,
    upper_path: &[AdjStep],
) -> Result<(StarkProof, Vec<BabyBear>), AdjacencyError> {
    let (trace, public_inputs) =
        generate_adjacency_trace(leaf_lower, lower_path, leaf_upper, upper_path)?;
    let circuit = adjacency_circuit();
    let proof = stark::prove(&circuit, &trace, &public_inputs);
    Ok((proof, public_inputs))
}

/// Verify an adjacency proof against the committed root and neighbor leaves.
///
/// Checks, in order:
/// 1. the supplied public inputs bind `root`, `leaf_lower`, `leaf_upper`;
/// 2. `idx_upper == idx_lower + 1` (**consecutiveness** — the teeth that close
///    the wide-bracket forge: the verifier refuses any proof whose indices are
///    not adjacent, so `lower`/`upper` cannot be arbitrary set sentinels);
/// 3. the STARK itself verifies (each leaf authenticates to `root`; the
///    `idx_out` boundary binds the in-circuit reconstructed indices to PIs).
pub fn verify_adjacency(
    proof: &StarkProof,
    root: BabyBear,
    leaf_lower: BabyBear,
    leaf_upper: BabyBear,
    public_inputs: &[BabyBear],
) -> Result<(), AdjacencyError> {
    if public_inputs.len() != ADJ_PUBLIC_INPUT_COUNT {
        return Err(AdjacencyError::PublicInputMismatch(format!(
            "expected {ADJ_PUBLIC_INPUT_COUNT} public inputs, got {}",
            public_inputs.len()
        )));
    }
    if public_inputs[adj_pi::ROOT] != root {
        return Err(AdjacencyError::PublicInputMismatch(
            "root public input does not match the committed set root".into(),
        ));
    }
    if public_inputs[adj_pi::LEAF_LOWER] != leaf_lower {
        return Err(AdjacencyError::PublicInputMismatch(
            "leaf_lower public input does not match the witness lower neighbor".into(),
        ));
    }
    if public_inputs[adj_pi::LEAF_UPPER] != leaf_upper {
        return Err(AdjacencyError::PublicInputMismatch(
            "leaf_upper public input does not match the witness upper neighbor".into(),
        ));
    }

    // Consecutiveness: idx_upper - idx_lower == 1 (mod p). Indices are honest
    // small integers reconstructed in-circuit (Σ dir·2^level), so the field
    // difference is exactly 1 for a genuine adjacent pair and anything else
    // otherwise.
    let idx_lower = public_inputs[adj_pi::IDX_LOWER];
    let idx_upper = public_inputs[adj_pi::IDX_UPPER];
    if idx_upper - idx_lower != BabyBear::ONE {
        return Err(AdjacencyError::NotConsecutive {
            idx_lower: idx_lower.as_u32() as u64,
            idx_upper: idx_upper.as_u32() as u64,
        });
    }

    let circuit = adjacency_circuit();
    stark::verify(&circuit, proof, public_inputs).map_err(AdjacencyError::StarkRejected)
}

// ────────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a depth-`D` binary tree over `leaves` (length 2^D) and return all
    /// levels (level 0 = leaves, last = [root]).
    fn build_tree(leaves: &[BabyBear]) -> Vec<Vec<BabyBear>> {
        assert!(leaves.len().is_power_of_two());
        let mut levels = vec![leaves.to_vec()];
        while levels.last().unwrap().len() > 1 {
            let cur = levels.last().unwrap();
            let mut next = Vec::with_capacity(cur.len() / 2);
            for pair in cur.chunks(2) {
                next.push(hash_2_to_1(pair[0], pair[1]));
            }
            levels.push(next);
        }
        levels
    }

    fn auth_path(levels: &[Vec<BabyBear>], mut index: usize) -> Vec<AdjStep> {
        let depth = levels.len() - 1;
        let mut path = Vec::with_capacity(depth);
        for level in &levels[..depth] {
            let is_right = index & 1 == 1;
            let sibling = if is_right {
                level[index - 1]
            } else {
                level[index + 1]
            };
            path.push(AdjStep {
                sibling,
                dir: is_right,
            });
            index >>= 1;
        }
        path
    }

    fn sample_leaves(n: usize) -> Vec<BabyBear> {
        (0..n).map(|i| BabyBear::new((i as u32 + 1) * 10)).collect()
    }

    #[test]
    fn honest_consecutive_pair_verifies() {
        // 16 leaves => depth 4 (a power of two, as the AIR requires).
        let leaves = sample_leaves(16);
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];

        let lp = auth_path(&levels, 5);
        let up = auth_path(&levels, 6);
        let (proof, pi) = prove_adjacency(leaves[5], &lp, leaves[6], &up).unwrap();

        verify_adjacency(&proof, root, leaves[5], leaves[6], &pi)
            .expect("honest consecutive pair must verify");
        assert_eq!(pi[adj_pi::IDX_LOWER], BabyBear::new(5));
        assert_eq!(pi[adj_pi::IDX_UPPER], BabyBear::new(6));
    }

    #[test]
    fn honest_consecutive_pair_index_zero_one() {
        let leaves = sample_leaves(4); // depth 2 (power of two)
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];
        let lp = auth_path(&levels, 0);
        let up = auth_path(&levels, 1);
        let (proof, pi) = prove_adjacency(leaves[0], &lp, leaves[1], &up).unwrap();
        verify_adjacency(&proof, root, leaves[0], leaves[1], &pi).unwrap();
        assert_eq!(pi[adj_pi::IDX_LOWER], BabyBear::new(0));
        assert_eq!(pi[adj_pi::IDX_UPPER], BabyBear::new(1));
    }

    /// THE FORGE (fail-before/pass-after): an attacker who knows the public
    /// root picks wide-bracket sentinels lower=leaf[0], upper=leaf[15] that are
    /// NOT consecutive. Even with genuine Merkle paths for both, the in-circuit
    /// index reconstruction yields 0 and 15 — `generate_adjacency_trace`
    /// refuses to build the trace, so no forged proof can be produced.
    #[test]
    fn forge_nonconsecutive_wide_bracket_is_rejected() {
        let leaves = sample_leaves(16);
        let levels = build_tree(&leaves);

        let lp = auth_path(&levels, 0);
        let up = auth_path(&levels, 15);
        let err = prove_adjacency(leaves[0], &lp, leaves[15], &up).unwrap_err();
        assert!(
            matches!(err, AdjacencyError::NotConsecutive { .. }),
            "wide-bracket non-consecutive forge must be refused at witness time; got {err:?}"
        );
    }

    /// A forger reuses an HONEST consecutive proof but lies to the verifier
    /// about which leaves it attests — the public-input binding rejects.
    #[test]
    fn forge_wrong_leaf_binding_is_rejected() {
        let leaves = sample_leaves(16);
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];
        let lp = auth_path(&levels, 5);
        let up = auth_path(&levels, 6);
        let (proof, pi) = prove_adjacency(leaves[5], &lp, leaves[6], &up).unwrap();

        let err = verify_adjacency(&proof, root, leaves[9], leaves[6], &pi).unwrap_err();
        assert!(matches!(err, AdjacencyError::PublicInputMismatch(_)));
    }

    /// A forger tampers the index PIs to keep a fake "consecutive" difference;
    /// the STARK boundary binding of the in-circuit reconstructed indices
    /// rejects (the bound trace values are still 5 and 6).
    #[test]
    fn forge_tampered_index_pi_is_rejected() {
        let leaves = sample_leaves(16);
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];

        let lp = auth_path(&levels, 5);
        let up = auth_path(&levels, 6);
        let (proof, mut pi) = prove_adjacency(leaves[5], &lp, leaves[6], &up).unwrap();

        // Bump both indices by 1 — still differ by 1 (passes consecutiveness),
        // but no longer match the trace's reconstructed 5 and 6.
        pi[adj_pi::IDX_LOWER] = BabyBear::new(6);
        pi[adj_pi::IDX_UPPER] = BabyBear::new(7);
        let err = verify_adjacency(&proof, root, leaves[5], leaves[6], &pi).unwrap_err();
        assert!(
            matches!(err, AdjacencyError::StarkRejected(_)),
            "tampered index PIs must fail the STARK boundary binding; got {err:?}"
        );
    }

    /// Two index-adjacent leaves that authenticate to DIFFERENT roots cannot be
    /// combined: witness generation rejects the root mismatch.
    #[test]
    fn forge_different_roots_is_rejected() {
        let leaves_a = sample_leaves(4);
        let mut leaves_b = sample_leaves(4);
        leaves_b[0] = BabyBear::new(999);
        let levels_a = build_tree(&leaves_a);
        let levels_b = build_tree(&leaves_b);

        let lp = auth_path(&levels_a, 0);
        let up = auth_path(&levels_b, 1);
        let err = prove_adjacency(leaves_a[0], &lp, leaves_b[1], &up).unwrap_err();
        assert!(matches!(err, AdjacencyError::RootMismatch));
    }

    #[test]
    fn wrong_root_at_verify_is_rejected() {
        let leaves = sample_leaves(4);
        let levels = build_tree(&leaves);
        let lp = auth_path(&levels, 0);
        let up = auth_path(&levels, 1);
        let (proof, pi) = prove_adjacency(leaves[0], &lp, leaves[1], &up).unwrap();
        let err =
            verify_adjacency(&proof, BabyBear::new(12345), leaves[0], leaves[1], &pi).unwrap_err();
        assert!(matches!(err, AdjacencyError::PublicInputMismatch(_)));
    }

    #[test]
    fn non_power_of_two_depth_is_rejected() {
        // 8 leaves => depth 3 (not a power of two) must be refused.
        let leaves = sample_leaves(8);
        let levels = build_tree(&leaves);
        let lp = auth_path(&levels, 2);
        let up = auth_path(&levels, 3);
        let err = prove_adjacency(leaves[2], &lp, leaves[3], &up).unwrap_err();
        assert!(matches!(err, AdjacencyError::BadDepth { depth: 3 }));
    }
}
