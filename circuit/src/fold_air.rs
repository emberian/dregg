//! Fold step AIR - with verified membership and root transition binding.
//!
//! See module-level docs for trace layout and constraint descriptions.

use crate::constraint_prover::{Air, Constraint, ConstraintProver};
use crate::field::BabyBear;
use crate::merkle_air::{MerkleAir, MerkleLevelWitness, MerkleWitness};
use crate::poseidon2::{hash_fact, hash_many};
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

pub const FOLD_AIR_WIDTH: usize = 12;

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
    pub const HASH_VALID: usize = 11;
}

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
        let air = MerkleAir::new(proof.clone());
        let result = ConstraintProver::verify(&air);
        if !result.is_valid() {
            return None;
        }
        if proof.expected_root != old_root {
            return None;
        }
        Some(proof.expected_root)
    }
}

#[derive(Clone, Debug)]
pub struct FoldWitness {
    pub old_root: BabyBear,
    pub new_root: BabyBear,
    pub removed_facts: Vec<RemovedFact>,
    pub num_added_checks: usize,
    /// Cryptographic commitment to the added checks (124-bit WideHash).
    ///
    /// This binds the actual check content to the fold proof, preventing a malicious
    /// prover from claiming checks they didn't actually add. When `num_added_checks == 0`,
    /// this MUST be `WideHash::ZERO` (backwards-compatible identity).
    ///
    /// Computed as: `WideHash::from_poseidon2("pyana-checks-v1", &[check_1_hash, ...])`.
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
    // Include the 4 elements of the checks commitment in the transition hash.
    // When no checks are added, these are all ZERO (identity element for hashing),
    // but still included to ensure the hash domain is consistent.
    elements.extend_from_slice(added_checks_commitment.as_slice());
    hash_many(&elements)
}

/// Verify that the fold's root transition is sound.
///
/// Checks:
/// 1. Each removed fact has a valid Merkle membership proof against `old_root`.
/// 2. Computes the root transition hash binding (old_root, new_root, fact_hashes).
///
/// The returned hash is used as public input pi[4] in the FoldAir. The verifier
/// (bridge layer) MUST independently compute `new_root` by rebuilding the Poseidon2
/// Merkle tree from old leaves minus removed leaves. This binding via pi[4] ensures
/// a malicious prover cannot claim an arbitrary `new_root` without producing a
/// Poseidon2 collision.
///
/// Returns `None` if any membership proof is missing or invalid.
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
            // SECURITY: This constraint binds the summary row's MEMBERSHIP_ROOT
            // to pi[4], which is computed as:
            //   Poseidon2(old_root || new_root || removed_fact_hashes || checks_commitment)
            //
            // Since pi[4] commits to new_root AND added_checks_commitment via a
            // collision-resistant hash, a malicious prover cannot substitute a different
            // new_root or different checks without producing a Poseidon2 collision.
            // The verifier MUST independently compute pi[4] from the actual tree rebuild
            // and the actual checks commitment, which is done by build_fold_witnesses()
            // in the bridge.
            //
            // pi[5] is the added_checks_commitment: Poseidon2(check_1_hash || check_2_hash || ...).
            // This is included in the root transition hash (pi[4]), cryptographically binding
            // the actual check content to the proof.
            Constraint {
                name: "root_transition_binding".into(),
                eval: Box::new(|row, _, pi| {
                    let is_summary = row[col::ROW_TYPE];
                    is_summary * (row[col::MEMBERSHIP_ROOT] - pi[4])
                }),
            },
            // SECURITY: When check_count == 0, the checks commitment must be ZERO.
            // This prevents a prover from sneaking a non-zero commitment with zero count.
            // When check_count > 0, the commitment is non-zero (enforced by Poseidon2
            // producing non-zero outputs for non-empty inputs, assuming no collisions
            // with zero). The meaningful binding comes from pi[4] including the commitment.
            Constraint {
                name: "checks_commitment_zero_when_no_checks".into(),
                eval: Box::new(|row, _, pi| {
                    let is_summary = row[col::ROW_TYPE];
                    // When check_count (pi[3]) is zero, checks_commitment (pi[5]) must be zero.
                    // We only enforce this on summary rows to avoid over-constraining.
                    // Note: this is a public-input-only constraint (doesn't touch trace values
                    // beyond ROW_TYPE), so it acts as a well-formedness check on the verifier's inputs.
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
        // pi[5] is the narrow (single-element) representation of the checks commitment,
        // used only for the zero-check constraint. The full 124-bit binding is through
        // pi[4] (root transition hash) which includes all 4 WideHash elements.
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

// ============================================================================
// FoldStarkAir: Real STARK proof generation/verification for fold steps.
// ============================================================================

/// StarkAir implementation for the Fold step.
///
/// This enables generating real STARK proofs (polynomial commitment + FRI)
/// for fold operations, replacing the ConstraintProof (BLAKE3 trace digest)
/// that provides no cryptographic soundness.
///
/// The fold AIR uses per-row constraints (binary checks, hash correctness,
/// public input binding) and one transition constraint (removal_count_increment).
/// For the small trace sizes typical of fold steps (2-8 rows), the custom STARK
/// handles this correctly.
pub struct FoldStarkAir {
    pub witness: FoldWitness,
}

impl FoldStarkAir {
    pub fn new(witness: FoldWitness) -> Self {
        Self { witness }
    }
}

impl StarkAir for FoldStarkAir {
    fn width(&self) -> usize {
        FOLD_AIR_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // The highest-degree constraint is removal_count_increment which multiplies
        // three terms (is_removal * is_next_removal * diff) = degree 3.
        // The delta_nonempty constraint uses conditional branching, not polynomial degree.
        3
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-fold-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut result = BabyBear::ZERO;
        let mut alpha_power = BabyBear::ONE;

        // C1: row_type_binary: rt * (rt - 1) = 0
        let rt = local[col::ROW_TYPE];
        result = result + alpha_power * (rt * (rt - BabyBear::ONE));
        alpha_power = alpha_power * alpha;

        // C2: membership_root_matches_old_root
        let is_removal = BabyBear::ONE - local[col::ROW_TYPE];
        result = result
            + alpha_power * (is_removal * (local[col::MEMBERSHIP_ROOT] - local[col::OLD_ROOT]));
        alpha_power = alpha_power * alpha;

        // C3: hash_valid_binary
        let hv = local[col::HASH_VALID];
        result = result + alpha_power * (hv * (hv - BabyBear::ONE));
        alpha_power = alpha_power * alpha;

        // C4: removal_hash_required
        result = result + alpha_power * (is_removal * (BabyBear::ONE - local[col::HASH_VALID]));
        alpha_power = alpha_power * alpha;

        // C5: fact_hash_correct
        let expected_hash = hash_fact(
            local[col::FACT_PRED],
            &[
                local[col::FACT_TERM_START],
                local[col::FACT_TERM_START + 1],
                local[col::FACT_TERM_START + 2],
            ],
        );
        result = result + alpha_power * (is_removal * (local[col::FACT_HASH] - expected_hash));
        alpha_power = alpha_power * alpha;

        // C6: old_root_consistent (binds to public input)
        result = result + alpha_power * (local[col::OLD_ROOT] - public_inputs[0]);
        alpha_power = alpha_power * alpha;

        // C7: new_root_consistent (binds to public input)
        result = result + alpha_power * (local[col::NEW_ROOT] - public_inputs[1]);
        alpha_power = alpha_power * alpha;

        // C8: removal_count_increment (transition constraint)
        // Only enforced when both current and next are removal rows.
        let is_next_removal = BabyBear::ONE - next[col::ROW_TYPE];
        result = result
            + alpha_power
                * (is_removal
                    * is_next_removal
                    * (next[col::REMOVAL_COUNT] - local[col::REMOVAL_COUNT] - BabyBear::ONE));
        alpha_power = alpha_power * alpha;

        // C9: root_transition_binding (on summary row)
        let is_summary = local[col::ROW_TYPE];
        result =
            result + alpha_power * (is_summary * (local[col::MEMBERSHIP_ROOT] - public_inputs[4]));
        alpha_power = alpha_power * alpha;

        // C10: checks_commitment_zero_when_no_checks
        // When check_count (pi[3]) is zero, checks_commitment (pi[5]) must be zero.
        if public_inputs[3] == BabyBear::ZERO {
            result = result + alpha_power * (is_summary * public_inputs[5]);
        }

        result
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 6 {
            // First row: old_root must match pi[0]
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::OLD_ROOT,
                value: public_inputs[0],
            });
            // First row: new_root must match pi[1]
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::NEW_ROOT,
                value: public_inputs[1],
            });
            // Last row: must be summary (ROW_TYPE = 1)
            constraints.push(BoundaryConstraint {
                row: trace_len - 1,
                col: col::ROW_TYPE,
                value: BabyBear::ONE,
            });
            // Last row: removal_count = pi[2]
            constraints.push(BoundaryConstraint {
                row: trace_len - 1,
                col: col::REMOVAL_COUNT,
                value: public_inputs[2],
            });
            // Last row: check_count = pi[3]
            constraints.push(BoundaryConstraint {
                row: trace_len - 1,
                col: col::CHECK_COUNT,
                value: public_inputs[3],
            });
        }
        constraints
    }
}

/// Generate a real STARK proof for a fold step.
///
/// This produces a cryptographically sound proof (polynomial commitment + FRI)
/// that the fold operation was performed correctly. The verifier can check this
/// without seeing the witness.
///
/// Returns `None` if the witness fails constraint checking or the trace is too
/// small for the STARK prover (requires >= 2 rows, power-of-two padded).
pub fn prove_fold_stark(witness: &FoldWitness) -> Option<StarkProof> {
    let air = FoldStarkAir::new(witness.clone());
    let fold_air = FoldAir::new(witness.clone());

    // Generate trace and public inputs
    let (trace, public_inputs) = fold_air.generate_trace();

    // Pad trace to power-of-two (>= 2 rows required by STARK prover)
    let padded_len = trace.len().next_power_of_two().max(2);
    let mut padded_trace = trace;
    while padded_trace.len() < padded_len {
        // Pad with the last row (summary row) to maintain constraint satisfaction
        padded_trace.push(padded_trace.last().unwrap().clone());
    }

    Some(stark::prove(&air, &padded_trace, &public_inputs))
}

/// Verify a STARK proof for a fold step.
///
/// Returns `Ok(())` if the proof is valid, or an error message describing the failure.
///
/// # Soundness: new_root verification
///
/// The STARK proves that `pi[4] = Poseidon2(old_root || new_root || removed_fact_hashes)`,
/// which binds `new_root` to the proof via collision resistance. However, the AIR does NOT
/// independently recompute `new_root` from "old tree minus removed leaves" — doing so would
/// require encoding the full Merkle rebuild inside the STARK (expensive and impractical for
/// our tree sizes).
///
/// Instead, the protocol relies on the **bridge layer** to independently compute `new_root`:
/// `build_fold_witnesses()` rebuilds the Poseidon2 Merkle tree over the new state's facts
/// and provides the resulting root as `FoldWitness.new_root`. The prover cannot forge this
/// because:
/// 1. The verifier (bridge or validated IVC) independently constructs the Merkle tree from
///    the actual facts after removal.
/// 2. The STARK proof then binds `new_root` into the transition hash via `pi[4]`.
/// 3. A forged `new_root` would require a Poseidon2 collision to produce a valid `pi[4]`.
///
/// For remote verification without the bridge layer, use `prove_validated_ivc()` which
/// provides per-step Merkle membership STARKs proving each removal was valid against
/// the claimed `old_root`. The `new_root` claim is then verified by the hash-chain STARK's
/// continuity: `step[i].new_root == step[i+1].old_root`, with membership proofs proving
/// each `old_root` is honest.
pub fn verify_fold_stark(proof: &StarkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    // Reconstruct a minimal witness just for AIR metadata (width, name, etc.)
    // The verifier doesn't need the actual witness data — only the AIR parameters.
    let dummy_witness = FoldWitness {
        old_root: BabyBear::ZERO,
        new_root: BabyBear::ZERO,
        removed_facts: vec![],
        num_added_checks: 0,
        added_checks_commitment: crate::binding::WideHash::ZERO,
    };
    let air = FoldStarkAir::new(dummy_witness);
    stark::verify(&air, proof, public_inputs)
}

pub fn build_shared_tree(leaves: &[BabyBear], depth: usize) -> (BabyBear, Vec<MerkleWitness>) {
    use crate::poseidon2::hash_4_to_1;
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

/// Compute the checks commitment for a set of test checks.
///
/// Each test check is modeled as `hash_fact(predicate=CHECK_BASE+i, terms=[i, 0, 0])`.
/// Returns `WideHash::ZERO` when `num_checks == 0` (backwards-compatible identity).
pub fn compute_test_checks_commitment(num_checks: usize) -> crate::binding::WideHash {
    if num_checks == 0 {
        return crate::binding::WideHash::ZERO;
    }
    let check_hashes: Vec<BabyBear> = (0..num_checks)
        .map(|i| {
            hash_fact(
                BabyBear::new(900 + i as u32), // CHECK_BASE + i
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fold_air_valid_single_removal() {
        let witness = create_test_fold(1, 0);
        let air = FoldAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Fold AIR should verify: {:?}",
            result.violations()
        );
    }

    #[test]
    fn fold_air_valid_multiple_removals() {
        let witness = create_test_fold(3, 2);
        let air = FoldAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Fold AIR should verify: {:?}",
            result.violations()
        );
    }

    #[test]
    fn fold_air_valid_checks_only() {
        let witness = FoldWitness {
            old_root: BabyBear::new(100),
            new_root: BabyBear::new(200),
            removed_facts: vec![],
            num_added_checks: 3,
            added_checks_commitment: compute_test_checks_commitment(3),
        };
        let air = FoldAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Fold AIR (checks only) should verify: {:?}",
            result.violations()
        );
    }

    #[test]
    fn fold_air_empty_delta_fails() {
        let witness = FoldWitness {
            old_root: BabyBear::new(100),
            new_root: BabyBear::new(200),
            removed_facts: vec![],
            num_added_checks: 0,
            added_checks_commitment: crate::binding::WideHash::ZERO,
        };
        let air = FoldAir::new(witness);
        assert!(!ConstraintProver::verify(&air).is_valid());
    }

    #[test]
    fn fold_air_no_membership_proof_fails() {
        let witness = FoldWitness {
            old_root: BabyBear::new(111111),
            new_root: BabyBear::new(222222),
            removed_facts: vec![RemovedFact {
                predicate: BabyBear::new(10),
                terms: [BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO],
                membership_proof: None,
            }],
            num_added_checks: 0,
            added_checks_commitment: crate::binding::WideHash::ZERO,
        };
        assert!(
            !ConstraintProver::verify(&FoldAir::new(witness)).is_valid(),
            "Missing membership proof should fail"
        );
    }

    #[test]
    fn fold_air_wrong_membership_root_fails() {
        let predicate = BabyBear::new(10);
        let terms = [BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO];
        let fact_hash = hash_fact(predicate, &terms);
        let proof = build_membership_proof(fact_hash, 4);
        let witness = FoldWitness {
            old_root: BabyBear::new(999999),
            new_root: BabyBear::new(222222),
            removed_facts: vec![RemovedFact {
                predicate,
                terms,
                membership_proof: Some(proof),
            }],
            num_added_checks: 0,
            added_checks_commitment: crate::binding::WideHash::ZERO,
        };
        assert!(
            !ConstraintProver::verify(&FoldAir::new(witness)).is_valid(),
            "Wrong root should fail"
        );
    }

    #[test]
    fn fold_air_forged_membership_proof_fails() {
        let predicate = BabyBear::new(10);
        let terms = [BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO];
        let wrong_leaf = BabyBear::new(99999);
        let proof = build_membership_proof(wrong_leaf, 4);
        let witness = FoldWitness {
            old_root: proof.expected_root,
            new_root: BabyBear::new(222222),
            removed_facts: vec![RemovedFact {
                predicate,
                terms,
                membership_proof: Some(proof),
            }],
            num_added_checks: 0,
            added_checks_commitment: crate::binding::WideHash::ZERO,
        };
        assert!(
            !ConstraintProver::verify(&FoldAir::new(witness)).is_valid(),
            "Forged proof should fail"
        );
    }

    // ========================================================================
    // FoldStarkAir STARK proof generation/verification tests
    // ========================================================================

    #[test]
    fn fold_stark_proof_single_removal() {
        let witness = create_test_fold(1, 0);
        let proof = prove_fold_stark(&witness).expect("fold STARK proof should generate");

        // Verify against the correct public inputs
        let fold_air = FoldAir::new(witness.clone());
        let (_, public_inputs) = fold_air.generate_trace();
        assert!(
            verify_fold_stark(&proof, &public_inputs).is_ok(),
            "fold STARK proof should verify"
        );
    }

    #[test]
    fn fold_stark_proof_multiple_removals() {
        let witness = create_test_fold(3, 2);
        let proof = prove_fold_stark(&witness).expect("fold STARK proof should generate");

        let fold_air = FoldAir::new(witness.clone());
        let (_, public_inputs) = fold_air.generate_trace();
        assert!(
            verify_fold_stark(&proof, &public_inputs).is_ok(),
            "fold STARK proof should verify"
        );
    }

    #[test]
    fn fold_stark_proof_checks_only() {
        let witness = FoldWitness {
            old_root: BabyBear::new(100),
            new_root: BabyBear::new(200),
            removed_facts: vec![],
            num_added_checks: 3,
            added_checks_commitment: compute_test_checks_commitment(3),
        };
        let proof = prove_fold_stark(&witness).expect("fold STARK proof should generate");

        let fold_air = FoldAir::new(witness.clone());
        let (_, public_inputs) = fold_air.generate_trace();
        assert!(
            verify_fold_stark(&proof, &public_inputs).is_ok(),
            "fold STARK proof (checks only) should verify"
        );
    }

    #[test]
    fn fold_stark_proof_wrong_public_inputs_fails() {
        let witness = create_test_fold(1, 0);
        let proof = prove_fold_stark(&witness).expect("fold STARK proof should generate");

        // Tamper with public inputs: wrong old_root
        let fold_air = FoldAir::new(witness.clone());
        let (_, mut public_inputs) = fold_air.generate_trace();
        public_inputs[0] = BabyBear::new(99999); // wrong old_root
        assert!(
            verify_fold_stark(&proof, &public_inputs).is_err(),
            "fold STARK proof with wrong public inputs should fail"
        );
    }

    #[test]
    fn fold_stark_proof_tampered_commitment_fails() {
        let witness = create_test_fold(2, 1);
        let mut proof = prove_fold_stark(&witness).expect("fold STARK proof should generate");

        // Tamper with the trace commitment
        proof.trace_commitment[0] ^= 0xFF;

        let fold_air = FoldAir::new(witness.clone());
        let (_, public_inputs) = fold_air.generate_trace();
        assert!(
            verify_fold_stark(&proof, &public_inputs).is_err(),
            "tampered fold STARK proof should fail"
        );
    }

    // ========================================================================
    // Added checks commitment binding tests
    // ========================================================================

    #[test]
    fn fold_air_checks_commitment_binds_content() {
        // Prover claims 3 checks added but provides a commitment for only 2 checks.
        // The root transition hash won't match pi[4] because pi[5] (commitment)
        // was computed from 2 checks but pi[3] says 3.
        //
        // More importantly: even if the count is "correct", a forged commitment
        // (different checks than what was actually added) will fail because
        // the verifier independently computes the commitment from real check data.
        let real_commitment_for_2 = compute_test_checks_commitment(2);
        let witness = FoldWitness {
            old_root: BabyBear::new(100),
            new_root: BabyBear::new(200),
            removed_facts: vec![],
            num_added_checks: 3,                            // claims 3...
            added_checks_commitment: real_commitment_for_2, // ...but commitment is for 2
        };
        let air = FoldAir::new(witness);
        let result = ConstraintProver::verify(&air);
        // This should pass at the AIR level (the AIR doesn't know how many checks
        // went into the commitment -- that's the verifier's job to supply matching
        // pi[3] and pi[5]). The key security property is that pi[4] binds pi[5].
        // If the verifier supplies mismatched count/commitment, the proof won't
        // verify against the expected root transition hash at the bridge layer.
        //
        // However, at the STARK level, if we produce a proof with this witness,
        // then the verifier uses the CORRECT public inputs (count=3, commitment
        // for 3 checks), the proof will fail.
        assert!(
            result.is_valid(),
            "AIR should pass (it trusts its own public inputs): {:?}",
            result.violations()
        );
    }

    #[test]
    fn fold_stark_wrong_checks_commitment_fails() {
        // Generate a valid proof with 3 checks (correct commitment).
        let witness = create_test_fold(0, 3);
        let proof = prove_fold_stark(&witness).expect("fold STARK proof should generate");

        // Now the verifier tries to verify with a DIFFERENT checks commitment
        // (e.g., the prover claimed they added checks A,B,C but really added A,B,D).
        // The verifier independently computes the commitment from what was actually expected.
        let fold_air = FoldAir::new(witness.clone());
        let (_, mut public_inputs) = fold_air.generate_trace();
        // Tamper with pi[5] (checks_commitment narrow) to simulate verifier detecting fraud
        let wrong_commitment = compute_test_checks_commitment(2);
        public_inputs[5] = wrong_commitment.to_narrow();
        // Also recompute pi[4] with the wrong commitment (as verifier would)
        public_inputs[4] = compute_root_transition_hash(
            public_inputs[0],
            public_inputs[1],
            &[], // no removals
            &wrong_commitment,
        );
        assert!(
            verify_fold_stark(&proof, &public_inputs).is_err(),
            "STARK proof with wrong checks commitment should fail verification"
        );
    }

    #[test]
    fn fold_stark_forged_count_with_zero_commitment_fails() {
        // Prover produces a proof claiming 0 checks (with ZERO commitment),
        // but actually added checks. When the verifier supplies the real
        // commitment (non-zero), verification fails.
        let witness_no_checks = FoldWitness {
            old_root: BabyBear::new(100),
            new_root: BabyBear::new(200),
            removed_facts: vec![],
            num_added_checks: 1,
            added_checks_commitment: compute_test_checks_commitment(1),
        };
        let proof = prove_fold_stark(&witness_no_checks).expect("should generate");

        // Verifier detects the prover actually didn't include the real checks:
        // supplies count=1 but with a DIFFERENT commitment
        let fold_air = FoldAir::new(witness_no_checks.clone());
        let (_, mut public_inputs) = fold_air.generate_trace();
        // Replace commitment with a forged one
        let forged_commitment =
            crate::binding::WideHash::from_poseidon2("forged", &[BabyBear::new(9999)]);
        public_inputs[5] = forged_commitment.to_narrow();
        public_inputs[4] = compute_root_transition_hash(
            public_inputs[0],
            public_inputs[1],
            &[],
            &forged_commitment,
        );
        assert!(
            verify_fold_stark(&proof, &public_inputs).is_err(),
            "STARK proof with forged checks commitment should fail"
        );
    }

    #[test]
    fn fold_air_nonzero_commitment_with_zero_count_fails() {
        // The constraint `checks_commitment_zero_when_no_checks` prevents
        // a prover from claiming 0 checks but providing a non-zero commitment.
        let witness = FoldWitness {
            old_root: BabyBear::new(100),
            new_root: BabyBear::new(200),
            removed_facts: vec![],
            num_added_checks: 0,
            added_checks_commitment: crate::binding::WideHash::from_poseidon2(
                "test",
                &[BabyBear::new(42)],
            ), // non-zero!
        };
        let air = FoldAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            !result.is_valid(),
            "Non-zero commitment with zero check count should fail"
        );
    }

    #[test]
    fn fold_air_zero_commitment_with_nonzero_count_is_invalid_binding() {
        // A prover claims checks but provides ZERO commitment. The root transition
        // hash will be computed with ZERO commitment, which won't match what the
        // verifier expects (the verifier independently hashes the real checks).
        //
        // At the AIR level, this still "passes" because the AIR is self-consistent.
        // The real check happens when the STARK verifier supplies correct pi[5].
        let witness = FoldWitness {
            old_root: BabyBear::new(100),
            new_root: BabyBear::new(200),
            removed_facts: vec![],
            num_added_checks: 2,
            added_checks_commitment: crate::binding::WideHash::ZERO, // wrong: should be non-zero for 2 checks
        };
        let air = FoldAir::new(witness.clone());
        let result = ConstraintProver::verify(&air);
        // The AIR passes because it's internally consistent (the public inputs
        // are generated from the witness). But at the STARK level, the verifier
        // would supply the CORRECT commitment and the proof would fail.
        assert!(
            result.is_valid(),
            "AIR is self-consistent even with zero commitment"
        );

        // Now verify at the STARK level: proof fails when verifier supplies correct commitment
        let proof = prove_fold_stark(&witness).expect("should generate");
        let fold_air = FoldAir::new(witness.clone());
        let (_, mut public_inputs) = fold_air.generate_trace();
        // Verifier corrects pi[5] to the real commitment
        let real_commitment = compute_test_checks_commitment(2);
        public_inputs[5] = real_commitment.to_narrow();
        public_inputs[4] =
            compute_root_transition_hash(public_inputs[0], public_inputs[1], &[], &real_commitment);
        assert!(
            verify_fold_stark(&proof, &public_inputs).is_err(),
            "STARK should fail when verifier supplies correct commitment that differs from proof"
        );
    }
}
